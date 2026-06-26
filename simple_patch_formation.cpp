// ============================================================
// simple_patch_formation.cpp
//
// Simplified C++ implementation of the Patch Tiling Algorithm
// Reference: Kotwal, A.V. (2025). Sci. Rep. 15, 34549.
//
// Outputs a single-panel SVG: simple_cover.svg
// matching the exact layout and colors of the target image.
// ============================================================

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <random>
#include <cmath>
#include <string>

using namespace std;

// ============================================================
// CONSTANTS
// ============================================================
static const int    L        = 5;
static const double R[L]     = {5.0, 10.0, 15.0, 20.0, 25.0};  // Layer radii (cm)
static const int    N        = 16;                             // Hits per superpoint
static const double Z0_MAX   = 15.0;                           // Beam-spot half-width (cm)
static const double ZL_MAX   = 50.0;                           // Outer layer half-length (cm)
static const double Z1_FIELD = 22.0;

static const int    N_HITS[L] = {70, 62, 55, 47, 40};          // Hit counts per layer
static const int    N_TRACKS   = 15;                           // Simulated tracks

static const int    BS_ITER   = 30;                            // Binary search iterations
static const double OVL_TOL   = 0.02;                          // Overlap tolerance (cm)
static const double FALLBACK  = 0.5;                           // Step size fallback (cm)

// ============================================================
// GEOMETRY
// ============================================================
struct Vec2 { double x, y; };
using Poly = vector<Vec2>;

// Sutherland-Hodgman polygon clipping against half-plane a*x + b*y <= c
Poly clip_hp(Poly p, double a, double b, double c) {
    Poly res;
    int n = (int)p.size();
    for (int i = 0; i < n; i++) {
        double xi = p[i].x, yi = p[i].y;
        double xj = p[(i+1)%n].x, yj = p[(i+1)%n].y;
        double di = a*xi + b*yi - c;
        double dj = a*xj + b*yj - c;
        if (di <= 1e-9) res.push_back({xi, yi});
        if ((di < -1e-9 && dj > 1e-9) || (di > 1e-9 && dj < -1e-9)) {
            double t = di / (di - dj);
            res.push_back({xi + t*(xj-xi), yi + t*(yj-yi)});
        }
    }
    return res;
}

// Intersects two polygons
Poly poly_intersect(Poly A, const Poly& B) {
    int n = (int)B.size();
    for (int i = 0; i < n && !A.empty(); i++) {
        double a = -(B[(i+1)%n].y - B[i].y);
        double b = B[(i+1)%n].x - B[i].x;
        A = clip_hp(A, a, b, a*B[i].x + b*B[i].y);
    }
    return A;
}

double poly_area(const Poly& p) {
    double a = 0; int n = (int)p.size();
    for (int i = 0; i < n; i++) a += p[i].x*p[(i+1)%n].y - p[(i+1)%n].x*p[i].y;
    return 0.5*fabs(a);
}

double px_min(const Poly& p){double m=p[0].x; for(auto&v:p)m=min(m,v.x); return m;}
double px_max(const Poly& p){double m=p[0].x; for(auto&v:p)m=max(m,v.x); return m;}
double py_min(const Poly& p){double m=p[0].y; for(auto&v:p)m=min(m,v.y); return m;}
double py_max(const Poly& p){double m=p[0].y; for(auto&v:p)m=max(m,v.y); return m;}

// Checks if the area of polygon is close to its bounding box area
bool is_rect(const Poly& p, double tol = 5e-3) {
    if ((int)p.size() < 4) return false;
    double bb = (px_max(p)-px_min(p)) * (py_max(p)-py_min(p));
    return bb < 1e-8 || fabs(poly_area(p) - bb) < tol*bb + tol;
}

// Checks if A union B is rectangular
bool union_rect(const Poly& A, const Poly& B, double tol = 5e-3) {
    double bb = (max(px_max(A),px_max(B)) - min(px_min(A),px_min(B))) * (max(py_max(A),py_max(B)) - min(py_min(A),py_min(B)));
    return bb < 1e-8 || fabs(poly_area(A) + poly_area(B) - poly_area(poly_intersect(A, B)) - bb) < tol*bb + tol;
}

// Checks if A union B union C is rectangular
bool union3_rect(const Poly& A, const Poly& B, const Poly& C, double tol = 5e-3) {
    double bb = (max({px_max(A),px_max(B),px_max(C)}) - min({px_min(A),px_min(B),px_min(C)}))
              * (max({py_max(A),py_max(B),py_max(C)}) - min({py_min(A),py_min(B),py_min(C)}));
    if (bb < 1e-8) return true;
    double iAB  = poly_area(poly_intersect(A, B)), iAC = poly_area(poly_intersect(A, C)), iBC = poly_area(poly_intersect(B, C));
    double iABC = poly_area(poly_intersect(poly_intersect(A, B), C));
    return fabs(poly_area(A)+poly_area(B)+poly_area(C) - iAB - iAC - iBC + iABC - bb) < tol*bb + tol;
}

Poly bbox2(const Poly& A, const Poly& B) {
    double x1=min(px_min(A),px_min(B)), x2=max(px_max(A),px_max(B));
    double y1=min(py_min(A),py_min(B)), y2=max(py_max(A),py_max(B));
    return {{x1,y1},{x2,y1},{x2,y2},{x1,y2}};
}

Poly bbox3(const Poly& A, const Poly& B, const Poly& C) {
    double x1=min({px_min(A),px_min(B),px_min(C)}), x2=max({px_max(A),px_max(B),px_max(C)});
    double y1=min({py_min(A),py_min(B),py_min(C)}), y2=max({py_max(A),py_max(B),py_max(C)});
    return {{x1,y1},{x2,y1},{x2,y2},{x1,y2}};
}

// Retrieves the min/max coordinates of the polygon at the vertical boundary lines
void get_vertical_boundary_y(const Poly& p, double x_val, double& y_min, double& y_max) {
    y_min = 1e9; y_max = -1e9;
    for (auto& v : p) {
        if (fabs(v.x - x_val) < 1e-4) {
            y_min = min(y_min, v.y); y_max = max(y_max, v.y);
        }
    }
}

// ============================================================
// PARAMETER SPACE FORMULAS
// ============================================================
inline double alpha_l(int l) { return (R[l] - R[0]) / (R[L-1] - R[0]); }
inline double z_at(int l, double z1, double zL) { return (1.0 - alpha_l(l))*z1 + alpha_l(l)*zL; }

// ============================================================
// DATA TYPES
// ============================================================
struct Hit { double z; bool is_track; };
struct SP  { int layer; double z_min, z_max; };
enum class PT { SEED, COMP, TERT };

struct Patch {
    SP   sp[L];
    Poly poly;
    PT   type;
    int  spatch_id;
    int  col_idx;
    int  row_idx;
};

struct WedgeResult {
    vector<Patch> patches;
    int n_superpatches = 0;
};

static vector<Hit> hits[L];
static vector<SP>  sps[L];

// ============================================================
// SIMULATION & ALGORITHM
// ============================================================
void gen_hits(unsigned seed_val) {
    mt19937 gen(seed_val);
    uniform_real_distribution<double> d0(-Z0_MAX, Z0_MAX), dL(-ZL_MAX, ZL_MAX);
    normal_distribution<double> smear(0.0, 0.005); // Pixel resolution

    for (int l = 0; l < L; l++) hits[l].clear();

    for (int t = 0; t < N_TRACKS; t++) {
        double z0 = d0(gen), zLt = dL(gen);
        for (int l = 0; l < L; l++)
            hits[l].push_back({z0 + (zLt - z0) / R[L-1] * R[l] + smear(gen), true});
    }

    for (int l = 0; l < L; l++) {
        int noise_n = N_HITS[l] - (int)hits[l].size();
        double span = 2.0 * ZL_MAX * 1.1;
        for (int i = 0; i < noise_n; i++)
            hits[l].push_back({-ZL_MAX*1.1 + (i / max(1.0, (double)(noise_n-1))) * span + smear(gen), false});
        sort(hits[l].begin(), hits[l].end(), [](const Hit& a, const Hit& b){ return a.z < b.z; });
    }
}

void form_sps() {
    for (int l = 0; l < L; l++) {
        sps[l].clear();
        for (int i = 0; i + N <= (int)hits[l].size(); i++)
            sps[l].push_back({l, hits[l][i].z, hits[l][i+N-1].z});
    }
}

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

SP lj(int l, double z_tgt) {
    int best = (int)sps[l].size() - 1;
    for (int i = (int)sps[l].size()-1; i >= 0; i--) {
        if (sps[l][i].z_min >= z_tgt - 1e-9) {
            best = i;
        } else {
            if (sps[l][i].z_max >= z_tgt - 1e-9) {
                best = i;
            }
            break;
        }
    }
    return sps[l][best];
}

Poly compute_poly(const SP sp[L]) {
    Poly p = {{-300,-300},{300,-300},{300,300},{-300,300}};
    for (int l = 0; l < L; l++) {
        p = clip_hp(p,  (1.0 - alpha_l(l)),  alpha_l(l),  sp[l].z_max);  if (p.empty()) return p;
        p = clip_hp(p, -(1.0 - alpha_l(l)), -alpha_l(l), -sp[l].z_min);  if (p.empty()) return p;
    }
    return p;
}

void build_seed(double z1_b, double zL_b, SP out[L]) {
    for (int l = 0; l < L; l++) out[l] = rj(l, z_at(l, z1_b, zL_b));
}

void build_comp(const SP seed[L], double z1_c, double zL_c, SP out[L]) {
    out[0] = seed[0];
    for (int l = 1; l < L; l++) out[l] = lj(l, z_at(l, z1_c, zL_c));
}

void build_tert(const SP seed[L], double z1_tb, double zL_tb, SP out[L]) {
    out[L-1] = seed[L-1];
    for (int l = 0; l < L-1; l++) out[l] = rj(l, z_at(l, z1_tb, zL_tb));
}

// // Runs the dynamic cover generation (Flowchart Fig. 2)
WedgeResult run_algorithm(unsigned seed_val) {
    gen_hits(seed_val);
    form_sps();

    WedgeResult res;
    int sp_id = 0, col_iter = 0;
    vector<double> prev_col_lefts;
    vector<double> prev_col_bottoms;
    double col_left_edge = Z1_FIELD;

    while (col_left_edge > -Z1_FIELD - 1.5 - 1e-3 && col_iter < 100) {
        col_iter++;
        vector<double> current_col_lefts;
        vector<double> current_col_bottoms;

        double right_z1_start = (col_iter == 1) ? Z1_FIELD : prev_col_lefts[0];
        double row_zL = min(ZL_MAX, 5.0 * right_z1_start + 60.0);
        int row_iter = 0, row_iter_su = 0;
        col_left_edge = 999.0;

        while (row_zL > -ZL_MAX - 5.0 - 1e-3 && row_iter < 100) {
            row_iter++;

            double right_z1 = (col_iter == 1) ? Z1_FIELD :
                              (row_iter_su < (int)prev_col_lefts.size() ? prev_col_lefts[row_iter_su] : prev_col_lefts.back());

            // 1. Seed Patch
            SP seed_sp[L];
            build_seed(right_z1, row_zL, seed_sp);
            Poly seed_poly = compute_poly(seed_sp);
            if (seed_poly.empty()) { row_zL -= FALLBACK; continue; }

            sp_id++; row_iter_su++;

            double spatch_left = seed_sp[0].z_min;
            double c_z1 = seed_sp[0].z_min, c_zL = py_min(seed_poly);
            double zc_L_seed = -1e9, zd_L_seed = -1e9;
            for (int l = 1; l < L; l++) {
                zc_L_seed = max(zc_L_seed, (seed_sp[l].z_min - (1.0 - alpha_l(l)) * seed_sp[0].z_min) / alpha_l(l));
                zd_L_seed = max(zd_L_seed, (seed_sp[l].z_min - (1.0 - alpha_l(l)) * seed_sp[0].z_max) / alpha_l(l));
            }
 
            // 2. Complementary Patch (Binary Search)
            SP comp_sp[L]; Poly comp_poly;
            {
                double lo = zc_L_seed - 35.0, hi = zc_L_seed + 5.0, best_c_zL = c_zL, min_pos_delta = 1e9;
                bool found_valid = false;
                for (int bs = 0; bs < BS_ITER; bs++) {
                    c_zL = 0.5*(lo + hi);
                    build_comp(seed_sp, c_z1, c_zL, comp_sp);
                    comp_poly = compute_poly(comp_sp);
                    if (comp_poly.empty()) { lo = c_zL; continue; }
 
                    double za_L_comp = 1e9, zb_L_comp = 1e9;
                    for (int l = 1; l < L; l++) {
                        za_L_comp = min(za_L_comp, (comp_sp[l].z_max - (1.0 - alpha_l(l)) * seed_sp[0].z_min) / alpha_l(l));
                        zb_L_comp = min(zb_L_comp, (comp_sp[l].z_max - (1.0 - alpha_l(l)) * seed_sp[0].z_max) / alpha_l(l));
                    }
 
                    double delta = min(za_L_comp - zc_L_seed, zb_L_comp - zd_L_seed);
                    if (delta >= 0.0 && delta < min_pos_delta) {
                        min_pos_delta = delta; best_c_zL = c_zL; found_valid = true;
                    }
                    if (delta > OVL_TOL) hi = c_zL; else if (delta < 0.0) lo = c_zL; else {
                        best_c_zL = c_zL; found_valid = true; break;
                    }
                }
                if (found_valid) c_zL = best_c_zL;
                build_comp(seed_sp, c_z1, c_zL, comp_sp);
                comp_poly = compute_poly(comp_sp);
            }
 
            // 3. Tertiary Patch (Conditional)
            bool sp_rect = !comp_poly.empty() ? union_rect(seed_poly, comp_poly) : is_rect(seed_poly);
            SP tert_sp[L]; Poly tert_poly; bool has_tert = false;
            if (!comp_poly.empty()) spatch_left = min(spatch_left, comp_sp[0].z_min);
 
            if (!sp_rect && !comp_poly.empty()) {
                double tb_z1 = px_max(comp_poly), tb_zL = py_min(comp_poly);
                double tb_lo = px_min(comp_poly) - 20.0, tb_hi = px_max(seed_poly) + 20.0, best_tb_z1 = tb_z1;
                bool tert_found_valid = false;
 
                for (int bs = 0; bs < BS_ITER; bs++) {
                    tb_z1 = 0.5*(tb_lo + tb_hi);
                    build_tert(seed_sp, tb_z1, tb_zL, tert_sp);
                    tert_poly = compute_poly(tert_sp);
                    if (tert_poly.empty()) { tb_hi = tb_z1; continue; }
 
                    double max_gap = -1e9;
                    for (int l = 0; l < L-1; l++) {
                        double req_z = max(comp_sp[l].z_min, seed_sp[l].z_min);
                        max_gap = max(max_gap, req_z - tert_sp[l].z_max);
                    }
 
                    if (max_gap <= 0.0) {
                        sp_rect = true; has_tert = true; best_tb_z1 = tb_z1; tert_found_valid = true;
                        tb_hi = tb_z1;
                    } else {
                        tb_lo = tb_z1;
                    }
                }
 
                if (tert_found_valid) {
                    tb_z1 = best_tb_z1;
                    build_tert(seed_sp, tb_z1, tb_zL, tert_sp);
                    tert_poly = compute_poly(tert_sp);
                    has_tert = !tert_poly.empty();
                }
                if (has_tert && !tert_poly.empty()) spatch_left = min(spatch_left, tert_sp[0].z_min);
            }
 
            // 4. Freeze & Store
            Poly sp_poly = bbox2(seed_poly, !comp_poly.empty() ? comp_poly : seed_poly);
  
            res.patches.push_back({ {seed_sp[0]}, seed_poly, PT::SEED, sp_id, col_iter, row_iter_su - 1 });
            for(int l=0; l<L; l++) res.patches.back().sp[l] = seed_sp[l];
            if (!comp_poly.empty()) {
                res.patches.push_back({ {comp_sp[0]}, comp_poly, PT::COMP, sp_id, col_iter, row_iter_su - 1 });
                for(int l=0; l<L; l++) res.patches.back().sp[l] = comp_sp[l];
            }
            if (has_tert && !tert_poly.empty()) {
                res.patches.push_back({ {tert_sp[0]}, tert_poly, PT::TERT, sp_id, col_iter, row_iter_su - 1 });
                for(int l=0; l<L; l++) res.patches.back().sp[l] = tert_sp[l];
            }
  
            current_col_lefts.push_back(seed_sp[0].z_min);
            double y_min_left = -1e9;
            double y_min_right = -1e9;
            {
                const SP* bot_sp = !comp_poly.empty() ? comp_sp : seed_sp;
                for (int l = 1; l < L; l++) {
                    y_min_left = max(y_min_left, (bot_sp[l].z_min - (1.0 - alpha_l(l)) * seed_sp[0].z_min) / alpha_l(l));
                    y_min_right = max(y_min_right, (bot_sp[l].z_min - (1.0 - alpha_l(l)) * seed_sp[0].z_max) / alpha_l(l));
                }
            }
            double spatch_bottom = max(y_min_left, y_min_right);
            current_col_bottoms.push_back(spatch_bottom);
            col_left_edge = min(col_left_edge, seed_sp[0].z_min);
 
            if (spatch_bottom <= -ZL_MAX + 1e-3) {
                break; // Stop row iteration since the entire column width reached the bottom of the field
            }
 
            double next_zL = spatch_bottom + 0.4;
            row_zL = (next_zL >= row_zL - 1e-6) ? row_zL - FALLBACK : next_zL;
        }
        prev_col_lefts = current_col_lefts;
        prev_col_bottoms = current_col_bottoms;
    }
    return res;
}

// ============================================================
// VISUALIZATION
// ============================================================
string get_patch_color(int col_idx, int row_idx, PT type) {
    if (col_idx == 1) { // Rightmost column
        if (row_idx == 0) {
            if (type == PT::SEED) return "#0D47A1"; // Blue
            if (type == PT::COMP) return "#C62828"; // Red
            return "#4A148C";                       // Purple (tert)
        }
        return "#2E7D32"; // Green for bottom rows
    } else if (col_idx == 2) { // Middle column
        if (row_idx == 0) return "#0097A7"; // Cyan
        if (row_idx == 1) return "#C2185B"; // Magenta
        return "#9E9D24";                   // Yellow/Olive
    } else { // Leftmost column (col_idx >= 3)
        if (row_idx == 0) return "#000000"; // Black
        if (row_idx == 1) return "#D84315"; // Orange
        return "#4A148C";                   // Dark Purple
    }
}

void export_svg(const WedgeResult& wr, const string& filename) {
    const int W = 400, H = 750;
    const double ML = 60, MR = 30, MT = 30, MB = 60;
    double pw = W - ML - MR, ph = H - MT - MB;

    auto to_x = [&](double z1) { return ML + (z1 - (-22.0)) / (22.0 - (-22.0)) * pw; };
    auto to_y = [&](double zL) { return MT + ph - (zL - (-50.0)) / (50.0 - (-50.0)) * ph; };

    ofstream out(filename);
    out << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
        << "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" << W << "\" height=\"" << H << "\" viewBox=\"0 0 " << W << " " << H << "\">\n"
        << "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n"
        << "<defs>\n"
        << "  <clipPath id=\"plot_clip\"><rect x=\"" << ML << "\" y=\"" << MT << "\" width=\"" << pw << "\" height=\"" << ph << "\"/></clipPath>\n"
        << "  <clipPath id=\"luminous_clip\">\n"
        << "    <polygon points=\"" 
        << to_x(-22.0) << "," << to_y(-50.0) << " " 
        << to_x(2.0) << "," << to_y(-50.0) << " " 
        << to_x(22.0) << "," << to_y(50.0) << " " 
        << to_x(-2.0) << "," << to_y(50.0) << "\"/>\n"
        << "  </clipPath>\n"
        << "</defs>\n";

    // 1. Grid
    for (int v : {-20, -10, 0, 10, 20})
        out << "<line x1=\"" << to_x(v) << "\" y1=\"" << MT << "\" x2=\"" << to_x(v) << "\" y2=\"" << MT+ph << "\" stroke=\"#e0e0e0\" stroke-width=\"0.6\"/>\n";
    for (int v : {-40, -20, 0, 20, 40})
        out << "<line x1=\"" << ML << "\" y1=\"" << to_y(v) << "\" x2=\"" << ML+pw << "\" y2=\"" << to_y(v) << "\" stroke=\"#e0e0e0\" stroke-width=\"0.6\"/>\n";

    // 2. Patches
    out << "<g clip-path=\"url(#plot_clip)\">\n";
    for (auto& p : wr.patches) {
        if (p.poly.empty()) continue;
        out << "<polygon points=\"";
        for (auto& v : p.poly) out << to_x(v.x) << "," << to_y(v.y) << " ";
        out << "\" fill=\"" << get_patch_color(p.col_idx, p.row_idx, p.type) << "\" fill-opacity=\"0.85\" stroke=\"none\"/>\n";
    }
    // Luminous Region Boundaries
    out << "<line x1=\"" << to_x(-22.0) << "\" y1=\"" << to_y(-50.0) << "\" x2=\"" << to_x(-2.0) << "\" y2=\"" << to_y(50.0) << "\" stroke=\"black\" stroke-width=\"1.2\"/>\n"
        << "<line x1=\"" << to_x(2.0) << "\" y1=\"" << to_y(-50.0) << "\" x2=\"" << to_x(22.0) << "\" y2=\"" << to_y(50.0) << "\" stroke=\"black\" stroke-width=\"1.2\"/>\n"
        << "</g>\n";

    // 3. Border & Ticks
    out << "<rect x=\"" << ML << "\" y=\"" << MT << "\" width=\"" << pw << "\" height=\"" << ph << "\" fill=\"none\" stroke=\"#333333\" stroke-width=\"1.0\"/>\n"
        << "<g font-family=\"sans-serif\" font-size=\"10\" fill=\"#333333\">\n";
    for (int v : {-20, -10, 0, 10, 20}) {
        out << "<line x1=\"" << to_x(v) << "\" y1=\"" << MT+ph << "\" x2=\"" << to_x(v) << "\" y2=\"" << MT+ph+4 << "\" stroke=\"#333333\" stroke-width=\"0.8\"/>\n"
            << "<text x=\"" << to_x(v) << "\" y=\"" << MT+ph+16 << "\" text-anchor=\"middle\">" << v << "</text>\n";
    }
    for (int v : {-40, -20, 0, 20, 40}) {
        out << "<line x1=\"" << ML-4 << "\" y1=\"" << to_y(v) << "\" x2=\"" << ML << "\" y2=\"" << to_y(v) << "\" stroke=\"#333333\" stroke-width=\"0.8\"/>\n"
            << "<text x=\"" << ML-6 << "\" y=\"" << to_y(v)+3 << "\" text-anchor=\"end\">" << v << "</text>\n";
    }
    // Labels
    out << "<text x=\"" << ML + pw/2 << "\" y=\"" << H - 15 << "\" text-anchor=\"middle\" font-size=\"14\" font-style=\"italic\">z1 (cm)</text>\n"
        << "<text transform=\"rotate(-90," << 18 << "," << MT + ph/2 << ")\" x=\"" << 18 << "\" y=\"" << MT + ph/2 + 4 << "\" text-anchor=\"middle\" font-size=\"14\" font-style=\"italic\">z_L (cm)</text>\n"
        << "</g>\n</svg>\n";
}

// ============================================================
// MAIN
// ============================================================
int main() {
    WedgeResult wr = run_algorithm(42);
    export_svg(wr, "simple_cover.svg");
    cout << "Wedge cover generated successfully: simple_cover.svg" << endl;
    return 0;
}
