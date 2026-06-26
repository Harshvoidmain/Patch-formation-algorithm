// ============================================================================
// simple_patch_formation.cpp
//
// Simplified C++ implementation of the Patch Tiling Algorithm
// Reference: Kotwal, A.V. (2025). Sci. Rep. 15, 34549.
//
// This program simulates particle hit data on concentric cylindrical layers,
// groups them into superpoints, and runs a raster-scanning patch tiling
// algorithm to cover all allowed particle trajectories without leaving gaps.
// ============================================================================

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <random>
#include <cmath>
#include <string>

using namespace std;

// ============================================================================
// CONSTANTS
// ============================================================================
static const int    L        = 5;                             // Number of detector layers
static const double R[L]     = {5.0, 10.0, 15.0, 20.0, 25.0};  // Radial positions of layers (cm)
static const int    N        = 16;                            // Hits per superpoint (resolution constraint)
static const double Z0_MAX   = 15.0;                          // Half-width of the beam collision region (z0)
static const double ZL_MAX   = 50.0;                          // Outer layer half-length (zL)
static const double Z1_FIELD = 22.0;                          // Field of view boundary in innermost layer (z1)

// Simulated hit configuration representing realistic event density
static const int    N_HITS[L] = {70, 62, 55, 47, 40};          // Hit budget per layer (decreases outwards)
static const int    N_TRACKS   = 15;                           // Number of simulated charged particle tracks

// Algorithm tuning parameters
static const int    BS_ITER   = 30;                            // Binary search iterations for overlap optimization
static const double OVL_TOL   = 0.02;                          // Target overlap margin between patches (200 micrometers)
static const double FALLBACK  = 0.5;                           // Small step size fallback if a patch is empty (cm)

// ============================================================================
// GEOMETRY UTILITIES
// ============================================================================
struct Vec2 { double x, y; };                                  // 2D coordinate in parameter space (x = z1, y = zL)
using Poly = vector<Vec2>;                                     // Polygon represented as a sequence of vertices

// Sutherland-Hodgman clipping algorithm: clips polygon 'p' against half-plane: a*x + b*y <= c
Poly clip_hp(Poly p, double a, double b, double c) {
    Poly res;
    int n = (int)p.size();
    for (int i = 0; i < n; i++) {
        double xi = p[i].x, yi = p[i].y;
        double xj = p[(i+1)%n].x, yj = p[(i+1)%n].y;
        
        // Signed distances from the clipping boundary line
        double di = a*xi + b*yi - c;
        double dj = a*xj + b*yj - c;
        
        // If vertex i is inside or on the boundary, keep it
        if (di <= 1e-9) res.push_back({xi, yi});
        
        // If the edge intersects the boundary line, compute and add the intersection point
        if ((di < -1e-9 && dj > 1e-9) || (di > 1e-9 && dj < -1e-9)) {
            double t = di / (di - dj);
            res.push_back({xi + t*(xj-xi), yi + t*(yj-yi)});
        }
    }
    return res;
}

// Computes the area of a polygon using the Shoelace formula (2D Cross Product)
double poly_area(const Poly& p) {
    if (p.size() < 3) return 0.0;
    double a = 0.0;
    for (size_t i = 0; i < p.size(); i++) {
        a += p[i].x * p[(i+1)%p.size()].y - p[(i+1)%p.size()].x * p[i].y;
    }
    return 0.5 * fabs(a);
}

// Computes the intersection of polygon A and polygon B by clipping A against B's half-planes
Poly poly_intersect(const Poly& A, const Poly& B) {
    Poly res = A;
    for (size_t i = 0; i < B.size(); i++) {
        double x1 = B[i].x, y1 = B[i].y;
        double x2 = B[(i+1)%B.size()].x, y2 = B[(i+1)%B.size()].y;
        double a = y1 - y2;
        double b = x2 - x1;
        double c = x2*y1 - x1*y2;
        res = clip_hp(res, a, b, c);
        if (res.empty()) return res;
    }
    return res;
}

// Helper utilities to retrieve bounding box limits
double px_min(const Poly& p){ double m=p[0].x; for(auto&v:p) m=min(m,v.x); return m; }
double px_max(const Poly& p){ double m=p[0].x; for(auto&v:p) m=max(m,v.x); return m; }
double py_min(const Poly& p){ double m=p[0].y; for(auto&v:p) m=min(m,v.y); return m; }
double py_max(const Poly& p){ double m=p[0].y; for(auto&v:p) m=max(m,v.y); return m; }

// Determines if a polygon is rectangular (within a small tolerance)
bool is_rect(const Poly& p, double tol = 5e-3) {
    if ((int)p.size() < 4) return false;
    double bb = (px_max(p)-px_min(p)) * (py_max(p)-py_min(p)); // Bounding box area
    return bb < 1e-8 || fabs(poly_area(p) - bb) < tol*bb + tol; // Compare area to bounding box
}

// Determines if the union of polygon A and B is rectangular
bool union_rect(const Poly& A, const Poly& B, double tol = 5e-3) {
    double bb = (max(px_max(A),px_max(B)) - min(px_min(A),px_min(B))) * 
                (max(py_max(A),py_max(B)) - min(py_min(A),py_min(B)));
    double u_area = poly_area(A) + poly_area(B) - poly_area(poly_intersect(A, B));
    return bb < 1e-8 || fabs(u_area - bb) < tol*bb + tol;
}

// Computes the 2D bounding box of two polygons
Poly bbox2(const Poly& A, const Poly& B) {
    double x1=min(px_min(A),px_min(B)), x2=max(px_max(A),px_max(B));
    double y1=min(py_min(A),py_min(B)), y2=max(py_max(A),py_max(B));
    return {{x1,y1},{x2,y1},{x2,y2},{x1,y2}};
}

// ============================================================================
// PARAMETER SPACE FORMULAS
// ============================================================================
// Fractional radial distance of layer l from layer 0 to layer L-1
inline double alpha_l(int l) { return (R[l] - R[0]) / (R[L-1] - R[0]); }

// Linear interpolation of coordinate z at layer l given inner layer z1 and outer layer zL
inline double z_at(int l, double z1, double zL) { return (1.0 - alpha_l(l))*z1 + alpha_l(l)*zL; }

// ============================================================================
// DATA TYPES
// ============================================================================
struct Hit { double z; bool is_track; };                       // A particle collision measurement
struct SP  { int layer; double z_min, z_max; };                // A superpoint: a sliding window of N hits
enum class PT { SEED, COMP, TERT };                            // Patch types: Seed, Complementary, Tertiary

struct Patch {
    SP   sp[L];                                                // Selected superpoints on all L layers
    Poly poly;                                                 // Valid parameter space region polygon
    PT   type;                                                 // Patch type classification
    int  spatch_id;                                            // ID of the parent superpatch grouping
    int  col_idx;                                              // Raster scan column index
    int  row_idx;                                              // Raster scan row index inside column
    bool is_rectangular;                                       // True if the patch polygon forms a rectangle
};

struct Corner {
    double z1;                                                 // innermost coordinate (horizontal parameter)
    double zL;                                                 // outermost coordinate (vertical parameter)
};

struct Superpatch {
    vector<Patch> patches;                                     // A superpatch contains 1, 2, or 3 overlapping patches
    Corner d_corner;                                           // Lower-left boundary corner of the superpatch
};

struct WedgeResult {
    vector<Patch> patches;                                     // All patches covering the entire wedge
    int n_superpatches = 0;                                    // Counter for generated superpatches
};

static vector<Hit> hits[L];                                    // Hit collections for all layers
static vector<SP>  sps[L];                                     // Superpoint list for all layers

// ============================================================================
// EVENT SIMULATION
// ============================================================================
// Generates random tracks and noise to simulate hit data in a detector wedge
void gen_hits(unsigned seed_val) {
    mt19937 gen(seed_val);
    uniform_real_distribution<double> d0(-Z0_MAX, Z0_MAX), dL(-ZL_MAX, ZL_MAX);
    normal_distribution<double> smear(0.0, 0.005);             // 50 micrometer sensor resolution smearing

    for (int l = 0; l < L; l++) hits[l].clear();

    // 1. Generate core hits belonging to clean particle tracks
    for (int t = 0; t < N_TRACKS; t++) {
        double z0 = d0(gen), zLt = dL(gen);                    // Track endpoints
        for (int l = 0; l < L; l++)
            hits[l].push_back({z0 + (zLt - z0) / R[L-1] * R[l] + smear(gen), true});
    }

    // 2. Generate random noise hits to reach the per-layer budget
    for (int l = 0; l < L; l++) {
        int noise_n = N_HITS[l] - (int)hits[l].size();
        double span = 2.0 * ZL_MAX * 1.1;
        for (int i = 0; i < noise_n; i++)
            hits[l].push_back({-ZL_MAX*1.1 + (i / max(1.0, (double)(noise_n-1))) * span + smear(gen), false});
        // Sort hits by z-position for sliding window superpoint grouping
        sort(hits[l].begin(), hits[l].end(), [](const Hit& a, const Hit& b){ return a.z < b.z; });
    }
}

// Forms superpoints by running a sliding window of size N over sorted hits
void form_sps() {
    for (int l = 0; l < L; l++) {
        sps[l].clear();
        for (int i = 0; i + N <= (int)hits[l].size(); i++)
            sps[l].push_back({l, hits[l][i].z, hits[l][i+N-1].z});
    }
}

// Right-Justified selector: finds the first superpoint whose upper edge covers/exceeds the target
SP rj(int l, double z_tgt) {
    int best = (int)sps[l].size() - 1;
    for (int i = 0; i < (int)sps[l].size(); i++) {
        if (sps[l][i].z_max >= z_tgt - 1e-9) {
            best = i;
            break;
        }
    }
    return sps[l][best];
}

// Left-Justified selector: finds the first superpoint whose lower edge covers/reaches the target
SP lj(int l, double z_tgt) {
    int best = (int)sps[l].size() - 1;
    for (int i = (int)sps[l].size()-1; i >= 0; i--) {
        if (sps[l][i].z_min >= z_tgt - 1e-9) {
            best = i;
        } else {
            // Also check if this superpoint's coverage window overlaps/contains the target
            if (sps[l][i].z_max >= z_tgt - 1e-9) {
                best = i;
            }
            break;
        }
    }
    return sps[l][best];
}

// Computes the intersection polygon in (z1, zL) space for the L superpoints
Poly compute_poly(const SP sp[L]) {
    Poly p = {{-300,-300},{300,-300},{300,300},{-300,300}}; // Initialize with large bounding box
    for (int l = 0; l < L; l++) {
        // Clip against upper boundary of superpoint in layer l
        p = clip_hp(p,  (1.0 - alpha_l(l)),  alpha_l(l),  sp[l].z_max);  if (p.empty()) return p;
        // Clip against lower boundary of superpoint in layer l
        p = clip_hp(p, -(1.0 - alpha_l(l)), -alpha_l(l), -sp[l].z_min);  if (p.empty()) return p;
    }
    return p;
}

// ============================================================================
// ALGORITHM WORKFLOW IMPLEMENTATION
// ============================================================================

// Creates a SEED patch: right-justified from the current column-top corner
Patch make_seed_patch(Corner b_corner) {
    Patch seed;
    seed.type = PT::SEED;
    for (int l = 0; l < L; l++) {
        seed.sp[l] = rj(l, z_at(l, b_corner.z1, b_corner.zL));
    }
    seed.poly = compute_poly(seed.sp);
    seed.is_rectangular = seed.poly.empty() ? false : is_rect(seed.poly);
    return seed;
}

// Retrieves the initial bottom-left corner of the seed patch to place the complementary patch
Corner get_initial_c_corner(const Patch& seed) {
    return { seed.sp[0].z_min, py_min(seed.poly) };
}

// Creates a COMP patch: left-justified to the specified complementary corner target
Patch make_complementary_patch(Corner c_corner, const Patch& seed) {
    Patch comp;
    comp.type = PT::COMP;
    comp.sp[0] = seed.sp[0]; // Anchored on the innermost layer of the seed patch
    for (int l = 1; l < L; l++) {
        comp.sp[l] = lj(l, z_at(l, c_corner.z1, c_corner.zL));
    }
    comp.poly = compute_poly(comp.sp);
    comp.is_rectangular = false;
    return comp;
}

// Computes the algebraic overlap margin between the bottom of the SEED and the top of the COMP patch
double compute_overlap(const Patch& seed, const Patch& comp) {
    double zc_L_seed = -1e9, zd_L_seed = -1e9;
    for (int l = 1; l < L; l++) {
        zc_L_seed = max(zc_L_seed, (seed.sp[l].z_min - (1.0 - alpha_l(l)) * seed.sp[0].z_min) / alpha_l(l));
        zd_L_seed = max(zd_L_seed, (seed.sp[l].z_min - (1.0 - alpha_l(l)) * seed.sp[0].z_max) / alpha_l(l));
    }
    double za_L_comp = 1e9, zb_L_comp = 1e9;
    for (int l = 1; l < L; l++) {
        za_L_comp = min(za_L_comp, (comp.sp[l].z_max - (1.0 - alpha_l(l)) * seed.sp[0].z_min) / alpha_l(l));
        zb_L_comp = min(zb_L_comp, (comp.sp[l].z_max - (1.0 - alpha_l(l)) * seed.sp[0].z_max) / alpha_l(l));
    }
    return min(za_L_comp - zc_L_seed, zb_L_comp - zd_L_seed);
}

// Creates a TERT patch: right-justified helper to bridge SEED and COMP
Patch make_tertiary_patch(Corner tert_b, const Patch& seed) {
    Patch tert;
    tert.type = PT::TERT;
    tert.sp[L-1] = seed.sp[L-1]; // Anchored on the outermost layer
    for (int l = 0; l < L-1; l++) {
        tert.sp[l] = rj(l, z_at(l, tert_b.z1, tert_b.zL));
    }
    tert.poly = compute_poly(tert.sp);
    tert.is_rectangular = false;
    return tert;
}

// Calculates the worst-case (largest) gap between TERT and COMP/SEED. Gap <= 0.0 means perfect cover.
double compute_tert_gap(const Patch& seed, const Patch& comp, const Patch& tert) {
    double max_gap = -1e9;
    for (int l = 0; l < L-1; l++) {
        double req_z = max(comp.sp[l].z_min, seed.sp[l].z_min); // Must overlap with whichever starts furthest right
        max_gap = max(max_gap, req_z - tert.sp[l].z_max);
    }
    return max_gap;
}

// Computes the bottom boundary limit and determines the target starting position for the next row
Corner get_next_b_corner(const Patch& seed, const Patch& comp, double current_zL) {
    const SP* bot_sp = !comp.poly.empty() ? comp.sp : seed.sp;
    double y_min_left = -1e9;
    double y_min_right = -1e9;
    for (int l = 1; l < L; l++) {
        y_min_left = max(y_min_left, (bot_sp[l].z_min - (1.0 - alpha_l(l)) * seed.sp[0].z_min) / alpha_l(l));
        y_min_right = max(y_min_right, (bot_sp[l].z_min - (1.0 - alpha_l(l)) * seed.sp[0].z_max) / alpha_l(l));
    }
    double spatch_bottom = max(y_min_left, y_min_right); // max_bottom logic prevents row-transition gaps
    double next_zL = spatch_bottom + 0.4;                // 0.4 cm safety buffer overlap
    double next_val = (next_zL >= current_zL - 1e-6) ? current_zL - FALLBACK : next_zL;
    return { spatch_bottom, next_val };
}

// Core Tiling Algorithm (Flowchart Fig. 2 / Pseudocode implementation)
WedgeResult run_algorithm(unsigned seed_val) {
    gen_hits(seed_val);
    form_sps();

    WedgeResult res;
    int spatch_id = 0, col_iter = 0;
    vector<double> prev_col_lefts;
    double col_left_edge = Z1_FIELD;

    Corner b_corner = { Z1_FIELD, ZL_MAX }; // Start at the top-right corner of the wedge field

    // 1. Column Progression Loop (Right to Left)
    while (col_left_edge > -Z1_FIELD - 1.5 - 1e-3 && col_iter < 100) {
        col_iter++;
        vector<double> current_col_lefts;

        // Reset starting corners for the column
        b_corner.z1 = (col_iter == 1) ? Z1_FIELD : prev_col_lefts[0];
        b_corner.zL = min(ZL_MAX, 5.0 * b_corner.z1 + 60.0);

        int row_iter = 0, row_iter_su = 0;
        col_left_edge = 999.0;

        // 2. Row Progression Loop (Top to Bottom within Column)
        while (b_corner.zL > -ZL_MAX - 5.0 - 1e-3 && row_iter < 100) {
            row_iter++;

            // Shift column right-boundary depending on previous column left-justify bounds
            double right_z1 = (col_iter == 1) ? Z1_FIELD :
                              (row_iter_su < (int)prev_col_lefts.size() ? prev_col_lefts[row_iter_su] : prev_col_lefts.back());
            b_corner.z1 = right_z1;

            // Step I: Make SEED Patch
            Patch seed = make_seed_patch(b_corner);
            if (seed.poly.empty()) {
                b_corner.zL -= FALLBACK;
                continue;
            }

            spatch_id++; row_iter_su++;
            
            Superpatch superpatch;
            Patch comp;
            bool has_comp = false;
            bool has_tert = false;

            if (seed.is_rectangular) {
                // Seed alone forms a perfect rectangular superpatch (simple case)
                superpatch.patches = { seed };
                Corner next_corners = get_next_b_corner(seed, comp, b_corner.zL);
                superpatch.d_corner = { seed.sp[0].z_min, next_corners.zL };
            } else {
                // Seed is triangular -> need Complementary patch to square it off
                Corner c_corner = get_initial_c_corner(seed);

                // Overlap optimization binary search loop (Step II)
                double lo = c_corner.zL - 35.0, hi = c_corner.zL + 5.0, best_c_zL = c_corner.zL, min_pos_delta = 1e9;
                bool comp_found_valid = false;

                for (int bs = 0; bs < BS_ITER; bs++) {
                    c_corner.zL = 0.5 * (lo + hi);
                    comp = make_complementary_patch(c_corner, seed);
                    if (comp.poly.empty()) { lo = c_corner.zL; continue; }

                    double delta = compute_overlap(seed, comp);
                    if (delta >= 0.0 && delta < min_pos_delta) {
                        min_pos_delta = delta;
                        best_c_zL = c_corner.zL;
                        comp_found_valid = true;
                    }
                    if (delta > OVL_TOL) hi = c_corner.zL;      // Over-lapping too much -> step down
                    else if (delta < 0.0) lo = c_corner.zL;     // Gap detected -> step up
                    else {
                        best_c_zL = c_corner.zL;
                        comp_found_valid = true;
                        break;
                    }
                }
                if (comp_found_valid) c_corner.zL = best_c_zL;
                comp = make_complementary_patch(c_corner, seed);
                has_comp = !comp.poly.empty();

                // Check if union of seed & complementary is rectangular
                bool superpatch_is_rectangular = has_comp ? union_rect(seed.poly, comp.poly) : seed.is_rectangular;
                
                // Step III: Make Tertiary patch if union is still triangular (gap exists)
                Patch tert;
                if (!superpatch_is_rectangular && has_comp) {
                    Corner tert_b = { px_max(comp.poly), py_min(comp.poly) };
                    double tb_lo = px_min(comp.poly) - 20.0, tb_hi = px_max(seed.poly) + 20.0, best_tb_z1 = tert_b.z1;
                    bool tert_found_valid = false;

                    for (int bs = 0; bs < BS_ITER; bs++) {
                        tert_b.z1 = 0.5 * (tb_lo + tb_hi);
                        tert = make_tertiary_patch(tert_b, seed);
                        if (tert.poly.empty()) { tb_hi = tert_b.z1; continue; }

                        double max_gap = compute_tert_gap(seed, comp, tert);
                        if (max_gap <= 0.0) {
                            superpatch_is_rectangular = true;
                            has_tert = true;
                            best_tb_z1 = tert_b.z1;
                            tb_hi = tert_b.z1; // Shift horizontally to find minimal size
                            tert_found_valid = true;
                        } else {
                            tb_lo = tert_b.z1;
                        }
                    }
                    if (tert_found_valid || has_tert) {
                        tert_b.z1 = best_tb_z1;
                        tert = make_tertiary_patch(tert_b, seed);
                        has_tert = !tert.poly.empty();
                    }
                }

                // Construct superpatch group
                superpatch.patches.push_back(seed);
                if (has_comp) superpatch.patches.push_back(comp);
                if (has_tert) superpatch.patches.push_back(tert);

                // Compute boundary coordinates for next row progression
                Corner next_corners = get_next_b_corner(seed, comp, b_corner.zL);
                superpatch.d_corner = { next_corners.z1, next_corners.zL };
            }

            // Save generated patches to the final result collection
            for (auto& p : superpatch.patches) {
                p.spatch_id = spatch_id;
                p.col_idx = col_iter;
                p.row_idx = row_iter_su - 1;
                res.patches.push_back(p);
            }

            current_col_lefts.push_back(seed.sp[0].z_min);
            col_left_edge = min(col_left_edge, seed.sp[0].z_min);

            b_corner = superpatch.d_corner; // Advance b_corner down to the next row
        }
        prev_col_lefts = current_col_lefts; // Store column boundary to anchor next column scan
    }
    return res;
}

// ============================================================================
// VISUALIZATION & OUTPUT
// ============================================================================
// Custom type-based color scheme matching requirements
string get_patch_color(int col_idx, int row_idx, PT type) {
    if (type == PT::SEED) return "#3B82F6"; // Slate Blue for Seeds
    if (type == PT::COMP) return "#F43F5E"; // Coral Rose for Complementary
    return "#10B981";                       // Emerald Teal for Tertiary helpers
}

// Exports the generated wedge cover result into a single vector SVG file
void export_svg(const WedgeResult& wr, const string& filename) {
    const int W = 400, H = 750;                               // SVG Canvas size
    const double ML = 60, MR = 30, MT = 30, MB = 60;          // Margins left, right, top, bottom
    
    ofstream out(filename);
    out << "<svg viewBox=\"0 0 " << W << " " << H << "\" xmlns=\"http://www.w3.org/2000/svg\">\n";
    out << "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n";
    
    // Mapping functions to scale coordinates (z1 from [-22, 22] and zL from [-50, 50]) to SVG pixels
    auto mapping_x = [&](double z1) { return ML + (z1 - (-22.0)) / 44.0 * (W - ML - MR); };
    auto mapping_y = [&](double zL) { return MT + (50.0 - zL) / 100.0 * (H - MT - MB); };
    
    // Draw background grid lines
    out << "<g stroke=\"#ddd\" stroke-width=\"0.5\" stroke-dasharray=\"2 2\">\n";
    for (double zL = -40; zL <= 40; zL += 20)
        out << "<line x1=\"" << ML << "\" y1=\"" << mapping_y(zL) << "\" x2=\"" << W - MR << "\" y2=\"" << mapping_y(zL) << "\"/>\n";
    for (double z1 = -20; z1 <= 20; z1 += 5)
        out << "<line x1=\"" << mapping_x(z1) << "\" y1=\"" << MT << "\" x2=\"" << mapping_x(z1) << "\" y2=\"" << H - MB << "\"/>\n";
    out << "</g>\n";
    
    // Draw all calculated patch polygons
    for (const auto& p : wr.patches) {
        if (p.poly.empty()) continue;
        out << "<polygon points=\"";
        for (const auto& v : p.poly) out << mapping_x(v.x) << "," << mapping_y(v.y) << " ";
        out << "\" fill=\"" << get_patch_color(p.col_idx, p.row_idx, p.type) << "\" fill-opacity=\"0.85\" stroke=\"none\"/>\n";
    }
    
    // Draw slanted field boundaries representing the luminous region
    out << "<g stroke=\"black\" stroke-width=\"1.5\">\n";
    out << "<line x1=\"" << mapping_x(-22.0) << "\" y1=\"" << mapping_y(-50.0) << "\" x2=\"" << mapping_x(-2.0) << "\" y2=\"" << mapping_y(50.0) << "\"/>\n";
    out << "<line x1=\"" << mapping_x(2.0) << "\" y1=\"" << mapping_y(-50.0) << "\" x2=\"" << mapping_x(22.0) << "\" y2=\"" << mapping_y(50.0) << "\"/>\n";
    out << "</g>\n";
    
    // Draw primary axes lines
    out << "<g stroke=\"black\" stroke-width=\"1\">\n";
    out << "<line x1=\"" << ML << "\" y1=\"" << H - MB << "\" x2=\"" << W - MR << "\" y2=\"" << H - MB << "\"/>\n";
    out << "<line x1=\"" << ML << "\" y1=\"" << MT << "\" x2=\"" << ML << "\" y2=\"" << H - MB << "\"/>\n";
    out << "</g>\n";
    
    // Draw horizontal ticks and labels
    out << "<g font-family=\"sans-serif\" font-size=\"10\" text-anchor=\"middle\">\n";
    for (double z1 = -20; z1 <= 20; z1 += 10) {
        out << "<text x=\"" << mapping_x(z1) << "\" y=\"" << H - MB + 15 << "\">" << (int)z1 << "</text>\n";
        out << "<line x1=\"" << mapping_x(z1) << "\" y1=\"" << H - MB << "\" x2=\"" << mapping_x(z1) << "\" y2=\"" << H - MB + 4 << "\" stroke=\"black\"/>\n";
    }
    out << "<text x=\"" << (ML + W - MR)/2.0 << "\" y=\"" << H - MB + 35 << "\" font-weight=\"bold\">z1 (cm)</text>\n";
    out << "</g>\n";
    
    // Draw vertical ticks and labels
    out << "<g font-family=\"sans-serif\" font-size=\"10\" text-anchor=\"end\">\n";
    for (double zL = -40; zL <= 40; zL += 20) {
        out << "<text x=\"" << ML - 8 << "\" y=\"" << mapping_y(zL) + 4 << "\">" << (int)zL << "</text>\n";
        out << "<line x1=\"" << ML - 4 << "\" y1=\"" << mapping_y(zL) << "\" x2=\"" << ML << "\" y2=\"" << mapping_y(zL) << "\" stroke=\"black\"/>\n";
    }
    out << "<text x=\"" << ML - 25 << "\" y=\"" << (MT + H - MB)/2.0 << "\" transform=\"rotate(-90," << ML - 25 << "," << (MT + H - MB)/2.0 << ")\" font-weight=\"bold\" text-anchor=\"middle\">z_L (cm)</text>\n";
    out << "</g>\n";
    
    out << "</svg>\n";
}

int main() {
    unsigned test_seed = 42;
    WedgeResult wr = run_algorithm(test_seed);
    export_svg(wr, "simple_cover.svg");
    cout << "Wedge cover generated successfully: simple_cover.svg" << endl;
    return 0;
}
