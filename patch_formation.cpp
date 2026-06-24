// ============================================================
// patch_formation.cpp
//
// C++ Implementation of the Patch Formation Algorithm
// Reference: Kotwal, A.V. (2025). Sci. Rep. 15, 34549.
//   "Block segmentation in feature space for realtime object
//    detection in high granularity images"
//   DOI: https://doi.org/10.1038/s41598-025-17888-0
//
// Flowchart : Fig. 2  - exact implementation
// Output    : patches_fig4.svg   (6-panel view, Fig. 4 style)
//             metrics_fig6.svg   (performance histograms, Fig. 6 style)
//
// Compile   : g++ -O2 -std=c++17 -o patch_formation patch_formation.cpp
//             cl  /EHsc /O2 patch_formation.cpp
// Run       : ./patch_formation   (or .\patch_formation.exe on Windows)
// ============================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <algorithm>
#include <numeric>
#include <random>
#include <cmath>
#include <string>
#include <iomanip>
#include <functional>
#include <cassert>

using namespace std;

// ============================================================
// CONSTANTS  (Kotwal 2025)
// ============================================================
static const int    L        = 5;
static const double R[L]     = {5.0, 10.0, 15.0, 20.0, 25.0};  // cm
static const int    N        = 16;      // hits per superpoint (2^4)
static const double Z0_MAX   = 15.0;   // luminous region half-width (cm)
static const double ZL_MAX   = 50.0;   // sensor acceptance half-length (cm)
// z1 at the top-right corner of the field:
//   track from z0=+15 to zL=+50 has z1 = 15 + (50-15)/25*5 = 22
static const double Z1_FIELD = 22.0;

// Hit simulation matching paper's average counts per layer (from innermost to outermost)
static const int    N_HITS[L] = {70, 62, 55, 47, 40};
static const int    N_TRACKS   = 15;

// Binary search parameters
static const int    BS_ITER   = 6;     // max binary-search iterations
static const double OVL_TOL   = 0.02; // optimal-overlap tolerance (cm)
static const double FALLBACK  = 0.5;  // fallback column/row step (cm)

// ============================================================
// 2-D GEOMETRY  (convex polygon in parameter space)
// ============================================================
struct Vec2 { double x, y; };
using Poly = vector<Vec2>;

// -- Sutherland-Hodgman: clip polygon against half-plane a*x + b*y <= c
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

// -- Polygon intersection via Sutherland-Hodgman
Poly poly_intersect(Poly A, const Poly& B) {
    int n = (int)B.size();
    for (int i = 0; i < n && !A.empty(); i++) {
        double x1 = B[i].x,        y1 = B[i].y;
        double x2 = B[(i+1)%n].x,  y2 = B[(i+1)%n].y;
        double a = -(y2-y1), b = (x2-x1), c = a*x1 + b*y1;
        A = clip_hp(A, a, b, c);
    }
    return A;
}

// -- Geometric queries
double poly_area(const Poly& p) {
    double a = 0; int n = (int)p.size();
    for (int i = 0; i < n; i++) {
        int j = (i+1)%n;
        a += p[i].x*p[j].y - p[j].x*p[i].y;
    }
    return 0.5*fabs(a);
}
double px_min(const Poly& p){double m=p[0].x;for(auto&v:p)m=min(m,v.x);return m;}
double px_max(const Poly& p){double m=p[0].x;for(auto&v:p)m=max(m,v.x);return m;}
double py_min(const Poly& p){double m=p[0].y;for(auto&v:p)m=min(m,v.y);return m;}
double py_max(const Poly& p){double m=p[0].y;for(auto&v:p)m=max(m,v.y);return m;}

// Is polygon area ≈ its bounding-box area?
bool is_rect(const Poly& p, double tol = 5e-3) {
    if ((int)p.size() < 4) return false;
    double bb = (px_max(p)-px_min(p)) * (py_max(p)-py_min(p));
    if (bb < 1e-8) return true;
    return fabs(poly_area(p) - bb) < tol*bb + tol;
}

// Is A ∪ B rectangular?
bool union_rect(const Poly& A, const Poly& B, double tol = 5e-3) {
    double bb_w = max(px_max(A),px_max(B)) - min(px_min(A),px_min(B));
    double bb_h = max(py_max(A),py_max(B)) - min(py_min(A),py_min(B));
    double bb   = bb_w * bb_h;
    if (bb < 1e-8) return true;
    double inter = poly_area(poly_intersect(A, B));
    double ua    = poly_area(A) + poly_area(B) - inter;
    return fabs(ua - bb) < tol*bb + tol;
}

// Is A ∪ B ∪ C rectangular?
bool union3_rect(const Poly& A, const Poly& B, const Poly& C, double tol = 5e-3) {
    double bb = (max({px_max(A),px_max(B),px_max(C)}) - min({px_min(A),px_min(B),px_min(C)}))
              * (max({py_max(A),py_max(B),py_max(C)}) - min({py_min(A),py_min(B),py_min(C)}));
    if (bb < 1e-8) return true;
    double iAB  = poly_area(poly_intersect(A, B));
    double iAC  = poly_area(poly_intersect(A, C));
    double iBC  = poly_area(poly_intersect(B, C));
    double iABC = poly_area(poly_intersect(poly_intersect(A, B), C));
    double ua   = poly_area(A)+poly_area(B)+poly_area(C) - iAB - iAC - iBC + iABC;
    return fabs(ua - bb) < tol*bb + tol;
}

// Bounding box of two/three polygons (as a Poly)
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

// Point-in-polygon test (ray casting)
bool point_in_poly(double x, double y, const Poly& p) {
    bool inside = false;
    int n = (int)p.size();
    for (int i = 0, j = n-1; i < n; j = i++) {
        double xi=p[i].x, yi=p[i].y, xj=p[j].x, yj=p[j].y;
        if (((yi>y)!=(yj>y)) && (x < (xj-xi)*(y-yi)/(yj-yi)+xi))
            inside = !inside;
    }
    return inside;
}

// Get y-endpoints (min, max) of polygon p at x_val (vertical boundary)
void get_vertical_boundary_y(const Poly& p, double x_val, double& y_min, double& y_max) {
    y_min = 1e9;
    y_max = -1e9;
    for (auto& v : p) {
        if (fabs(v.x - x_val) < 1e-4) {
            y_min = min(y_min, v.y);
            y_max = max(y_max, v.y);
        }
    }
}

// ============================================================
// PARAMETER SPACE  (Eq. 1 of the paper)
// z_l = (1-α_l)·z1  +  α_l·z_L,   α_l = (r_l-r_1)/(r_L-r_1)
// ============================================================
inline double alpha_l(int l) {
    return (R[l] - R[0]) / (R[L-1] - R[0]);
}
inline double z_at(int l, double z1, double zL) {
    double a = alpha_l(l);
    return (1.0 - a)*z1 + a*zL;
}

// ============================================================
// DATA TYPES
// ============================================================
struct Hit { double z; bool is_track; };

struct SP {   // superpoint: N adjacent hits on one layer
    int    layer;
    double z_min, z_max;
};

enum class PT { SEED, COMP, TERT };

struct Patch {
    SP   sp[L];   // one superpoint per layer
    Poly poly;    // polygon in (z1, zL) parameter space
    PT   type;
    int  spatch_id;
};

struct WedgeResult {
    vector<Patch> patches;
    int n_seed = 0, n_comp = 0, n_tert = 0;
    int n_superpatches = 0;
    vector<int> nTP;   // trial patches attempted per superpatch
    vector<int> nP;    // patches in final superpatch
    vector<pair<double, double>> true_tracks; // z0, zLt
};

// ============================================================
// GLOBAL HIT / SUPERPOINT STORAGE  (per wedge)
// ============================================================
static vector<Hit> hits[L];
static vector<SP>  sps[L];
static vector<pair<double, double>> current_tracks;

// ============================================================
// STEP 1 — SIMULATE HITS
// ============================================================
void gen_hits(unsigned seed_val) {
    mt19937 gen(seed_val);
    uniform_real_distribution<double> d0(-Z0_MAX, Z0_MAX);
    uniform_real_distribution<double> dL(-ZL_MAX, ZL_MAX);
    normal_distribution<double> smear(0.0, 0.005);  // pixel resolution

    current_tracks.clear();

    for (int l = 0; l < L; l++) hits[l].clear();

    // Signal tracks: straight lines through all layers
    for (int t = 0; t < N_TRACKS; t++) {
        double z0 = d0(gen), zLt = dL(gen);
        current_tracks.push_back({z0, zLt});
        for (int l = 0; l < L; l++) {
            double z = z0 + (zLt - z0) / R[L-1] * R[l] + smear(gen);
            hits[l].push_back({z, true});
        }
    }

    // Noise: quasi-uniform spacing
    for (int l = 0; l < L; l++) {
        int noise_n = N_HITS[l] - (int)hits[l].size();
        double span = 2.0 * ZL_MAX * 1.1;
        for (int i = 0; i < noise_n; i++) {
            double z = -ZL_MAX*1.1 + (i / max(1.0, (double)(noise_n-1))) * span
                       + smear(gen);
            hits[l].push_back({z, false});
        }
        sort(hits[l].begin(), hits[l].end(),
             [](const Hit& a, const Hit& b){ return a.z < b.z; });
    }
}

// ============================================================
// STEP 2 — FORM SUPERPOINTS  (sliding window of N hits)
// ============================================================
void form_sps() {
    for (int l = 0; l < L; l++) {
        sps[l].clear();
        int sz = (int)hits[l].size();
        for (int i = 0; i + N <= sz; i++)
            sps[l].push_back({l, hits[l][i].z, hits[l][i+N-1].z});
    }
}

// ============================================================
// SUPERPOINT SELECTION
// ============================================================
// Right-justified: largest i with sps[l][i].z_max <= z_tgt
SP rj(int l, double z_tgt) {
    int best = 0;
    for (int i = 0; i < (int)sps[l].size(); i++)
        if (sps[l][i].z_max <= z_tgt + 1e-9) best = i; else break;
    return sps[l][best];
}

// Left-justified: smallest i with sps[l][i].z_min >= z_tgt
SP lj(int l, double z_tgt) {
    int best = (int)sps[l].size() - 1;
    for (int i = (int)sps[l].size()-1; i >= 0; i--)
        if (sps[l][i].z_min >= z_tgt - 1e-9) best = i; else break;
    return sps[l][best];
}

// ============================================================
// PATCH POLYGON: clip BIG box by each layer's strip constraint
// ============================================================
Poly compute_poly(const SP sp[L]) {
    Poly p = {{-300,-300},{300,-300},{300,300},{-300,300}};
    for (int l = 0; l < L; l++) {
        double a = 1.0 - alpha_l(l);
        double b = alpha_l(l);
        // upper bound: (1-a)*z1 + a*zL <= sp.z_max
        p = clip_hp(p,  a,  b,  sp[l].z_max);  if (p.empty()) return p;
        // lower bound: (1-a)*z1 + a*zL >= sp.z_min
        p = clip_hp(p, -a, -b, -sp[l].z_min);  if (p.empty()) return p;
    }
    return p;
}

// ============================================================
// PATCH BUILDERS
// ============================================================
// Seed: right-justify all L layers to b-corner (z1_b, zL_b)
void build_seed(double z1_b, double zL_b, SP out[L]) {
    for (int l = 0; l < L; l++)
        out[l] = rj(l, z_at(l, z1_b, zL_b));
}

// Complementary: S1 = seed_sp[0]; layers l>1 left-justified to (z1_c, zL_c)
void build_comp(const SP seed[L], double z1_c, double zL_c, SP out[L]) {
    out[0] = seed[0];
    for (int l = 1; l < L; l++)
        out[l] = lj(l, z_at(l, z1_c, zL_c));
}

// Tertiary: SL = seed_sp[L-1]; layers l<L-1 right-justified to (z1_tb, zL_tb)
void build_tert(const SP seed[L], double z1_tb, double zL_tb, SP out[L]) {
    out[L-1] = seed[L-1];
    for (int l = 0; l < L-1; l++)
        out[l] = rj(l, z_at(l, z1_tb, zL_tb));
}

// ============================================================
// CORE ALGORITHM  —  Fig. 2 Flowchart (Kotwal 2025)
// ============================================================
WedgeResult run_algorithm(unsigned seed_val) {
    gen_hits(seed_val);
    form_sps();

    WedgeResult res;
    res.true_tracks = current_tracks;
    int sp_id    = 0;
    int col_iter = 0;

    // Starting b-corner: top-right corner of the field
    double col_z1 = Z1_FIELD + 1.5;

    while (col_z1 > -Z1_FIELD - 1.5 - 1e-3 && col_iter < 5000) {
        col_iter++;
        double row_zL      = ZL_MAX + 5.0;
        double col_left_z1 = +999.0;   // leftmost z1 edge of this column
        int    row_iter    = 0;
        double column_S1_z_min = col_z1;

        while (row_zL > -ZL_MAX - 5.0 - 1e-3 && row_iter < 5000) {
            row_iter++;
            sp_id++;
            int n_trial = 0;

            // ── MAKE SEED PATCH (right-justified to b-corner) ──
            SP seed_sp[L];
            build_seed(col_z1, row_zL, seed_sp);
            Poly seed_poly = compute_poly(seed_sp);
            if (seed_poly.empty()) { row_zL -= FALLBACK; continue; }
            n_trial++;
            column_S1_z_min = seed_sp[0].z_min;

            double sx1 = px_min(seed_poly), sy1 = py_min(seed_poly);
            double sx2 = px_max(seed_poly), sy2 = py_max(seed_poly);
            if (sx1 < col_left_z1) col_left_z1 = sx1;
 
            // ── GET INITIAL C-CORNER = bottom-left of seed polygon ──
            double c_z1 = seed_sp[0].z_min; // left vertical boundary
            double c_zL = sy1;
 
            // Get vertical boundary y endpoints of the seed patch
            double zc_L_seed, zd_L_seed;
            {
                double dummy1, dummy2;
                get_vertical_boundary_y(seed_poly, seed_sp[0].z_min, zc_L_seed, dummy1);
                get_vertical_boundary_y(seed_poly, seed_sp[0].z_max, zd_L_seed, dummy2);
            }
 
            // ── MAKE COMPLEMENTARY PATCH (binary search on c_zL) ──
            //    Target: min(delta_ac, delta_bd) is the smallest positive value
            SP   comp_sp[L];
            Poly comp_poly;
            {
                double lo = zc_L_seed - 35.0, hi = zc_L_seed + 5.0;
                double best_c_zL = c_zL;
                double min_pos_delta = 1e9;
                bool found_valid = false;

                for (int bs = 0; bs < BS_ITER; bs++) {
                    n_trial++;
                    c_zL = 0.5*(lo + hi);
                    build_comp(seed_sp, c_z1, c_zL, comp_sp);
                    comp_poly = compute_poly(comp_sp);
                    if (comp_poly.empty()) { lo = c_zL; continue; }
 
                    double za_L_comp, zb_L_comp;
                    double dummy1, dummy2;
                    get_vertical_boundary_y(comp_poly, seed_sp[0].z_min, dummy1, za_L_comp);
                    get_vertical_boundary_y(comp_poly, seed_sp[0].z_max, dummy2, zb_L_comp);
 
                    if (za_L_comp < -1e8 || zb_L_comp < -1e8) {
                        lo = c_zL; // treat as empty
                        continue;
                    }
 
                    double delta_ac = za_L_comp - zc_L_seed;
                    double delta_bd = zb_L_comp - zd_L_seed;
                    double delta = min(delta_ac, delta_bd);
 
                    if (seed_val == 42 && col_iter == 1 && row_iter == 1) {
                        cout << "  BS iter " << bs << ": lo=" << lo << ", hi=" << hi << ", c_zL=" << c_zL
                             << ", delta_ac=" << delta_ac << ", delta_bd=" << delta_bd << ", delta=" << delta << "\n";
                    }
 
                    if (delta >= 0.0 && delta < min_pos_delta) {
                        min_pos_delta = delta;
                        best_c_zL = c_zL;
                        found_valid = true;
                    }
 
                    if      (delta >  OVL_TOL) hi = c_zL;   // positive → adjust down
                    else if (delta <  0.0)     lo = c_zL;   // negative → adjust up
                    else {
                        best_c_zL = c_zL;
                        found_valid = true;
                        break;                             // optimal → freeze comp
                    }
                }
                if (found_valid) {
                    c_zL = best_c_zL;
                }
                build_comp(seed_sp, c_z1, c_zL, comp_sp);
                comp_poly = compute_poly(comp_sp);
            }

            // ── COMPUTE OVERLAP OF SEED AND COMPLEMENTARY ──
            // superpatch = union of seed + comp
            bool sp_rect = false;
            SP   tert_sp[L];
            Poly tert_poly;
            bool has_tert = false;

            if (!comp_poly.empty()) {
                if (px_min(comp_poly) < col_left_z1) col_left_z1 = px_min(comp_poly);
                sp_rect = union_rect(seed_poly, comp_poly);
            } else {
                sp_rect = is_rect(seed_poly);
            }

            // ── SUPERPATCH NOT RECTANGULAR → MAKE TERTIARY PATCH ──
            if (!sp_rect && !comp_poly.empty()) {
                // Tertiary b-corner: starts at right edge of comp, its bottom
                double tb_z1 = px_max(comp_poly);
                double tb_zL = py_min(comp_poly);

                // Binary search on tb_z1 until seed ∪ comp ∪ tert = rectangle
                // Gap between tert.x_max and comp.x_min:
                //   if gap > 0: tert is too narrow → decrease tb_z1
                //   if gap < 0: tert is too wide  → increase tb_z1
                double tb_lo = px_min(comp_poly) - 2.0;
                double tb_hi = sx2 + 3.0;
                double best_tb_z1 = tb_z1;
                double min_pos_gap = 1e9;
                bool tert_found_valid = false;

                for (int bs = 0; bs < BS_ITER; bs++) {
                    n_trial++;
                    tb_z1 = 0.5*(tb_lo + tb_hi);
                    build_tert(seed_sp, tb_z1, tb_zL, tert_sp);
                    tert_poly = compute_poly(tert_sp);
                    if (tert_poly.empty()) { tb_hi = tb_z1; continue; }

                    if (union3_rect(seed_poly, comp_poly, tert_poly)) {
                        sp_rect  = true;
                        has_tert = true;
                        best_tb_z1 = tb_z1;
                        tert_found_valid = true;
                        break;
                    }
                    // Adjust tertiary b-corner
                    double gap = px_min(comp_poly) - px_max(tert_poly);
                    if (gap >= 0.0 && gap < min_pos_gap) {
                        min_pos_gap = gap;
                        best_tb_z1 = tb_z1;
                        tert_found_valid = true;
                    }
                    if (gap > OVL_TOL)  tb_lo = tb_z1;  // tert too narrow → go right
                    else                tb_hi = tb_z1;  // tert too wide   → go left
                }

                if (!sp_rect) {
                    if (tert_found_valid) {
                        tb_z1 = best_tb_z1;
                    }
                    // Best-effort: use last/best tert
                    build_tert(seed_sp, tb_z1, tb_zL, tert_sp);
                    tert_poly = compute_poly(tert_sp);
                    has_tert  = !tert_poly.empty();
                }

                if (has_tert && !tert_poly.empty())
                    if (px_min(tert_poly) < col_left_z1)
                        col_left_z1 = px_min(tert_poly);
            }

            // ── FREEZE SUPERPATCH ────────────────────────────────
            Poly sp_poly;
            if (has_tert && !tert_poly.empty())
                sp_poly = bbox3(seed_poly, comp_poly, tert_poly);
            else if (!comp_poly.empty())
                sp_poly = bbox2(seed_poly, comp_poly);
            else
                sp_poly = seed_poly;

            // ── STORE PATCHES ────────────────────────────────────
            int np = 0;
            {
                Patch ps;
                ps.type = PT::SEED; ps.spatch_id = sp_id;
                for (int l = 0; l < L; l++) ps.sp[l] = seed_sp[l];
                ps.poly = seed_poly;
                res.patches.push_back(ps);
                res.n_seed++; np++;
            }
            if (!comp_poly.empty()) {
                Patch pc;
                pc.type = PT::COMP; pc.spatch_id = sp_id;
                for (int l = 0; l < L; l++) pc.sp[l] = comp_sp[l];
                pc.poly = comp_poly;
                res.patches.push_back(pc);
                res.n_comp++; np++;
            }
            if (has_tert && !tert_poly.empty()) {
                Patch pt;
                pt.type = PT::TERT; pt.spatch_id = sp_id;
                for (int l = 0; l < L; l++) pt.sp[l] = tert_sp[l];
                pt.poly = tert_poly;
                res.patches.push_back(pt);
                res.n_tert++; np++;
            }
            res.nTP.push_back(n_trial);
            res.nP.push_back(np);

            // ── B-CORNER OF NEXT SEED = D-CORNER OF SUPERPATCH ──
            // (column tiling: move down in zL)
            double next_zL = py_min(sp_poly);
            if (next_zL >= row_zL - 1e-6) next_zL = row_zL - FALLBACK;
            row_zL = next_zL;
        }

        // ── COLUMN COMPLETE: start next column at new b-corner ──
        if (column_S1_z_min >= col_z1 - 1e-6) col_z1 -= FALLBACK;
        else                                  col_z1  = column_S1_z_min;
    }

    res.n_superpatches = sp_id;
    return res;
}

// ============================================================
// COMPUTE ACCEPTANCE EFFICIENCY (for Fig. 6 bottom-right)
// Returns (1 - ε) × 10^6 (ppm) for each z0 bin
// ============================================================
struct AcceptPoint { double z0; bool accepted; };

vector<AcceptPoint> compute_acceptance(const vector<WedgeResult>& results) {
    vector<AcceptPoint> pts;
    ofstream csv("tracks.csv");
    csv << "z0,zL,z1,accepted\n";

    for (auto& wr : results) {
        for (auto& trk : wr.true_tracks) {
            double z0 = trk.first;
            double zLt = trk.second;
            // Map to parameter space
            double z1 = z0 + (zLt - z0) / R[L-1] * R[0];
            double zL = zLt;

            bool acc = false;
            for (auto& p : wr.patches) {
                if (!p.poly.empty() && point_in_poly(z1, zL, p.poly)) {
                    acc = true; break;
                }
            }
            pts.push_back({z0, acc});
            csv << z0 << "," << zL << "," << z1 << "," << (acc ? 1 : 0) << "\n";
        }
    }
    return pts;
}

// ============================================================
// SVG UTILITIES
// ============================================================
struct SVGCtx {
    ofstream out;
    int width, height;

    SVGCtx(const string& fname, int w, int h) : out(fname), width(w), height(h) {
        out << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
            << "<svg xmlns=\"http://www.w3.org/2000/svg\" "
            << "width=\"" << w << "\" height=\"" << h << "\" "
            << "viewBox=\"0 0 " << w << " " << h << "\">\n"
            << "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n";
    }
    ~SVGCtx() { out << "</svg>\n"; }

    void text(double x, double y, const string& s, int fs = 10,
              const string& anchor = "middle",
              const string& fill   = "black",
              const string& style  = "") {
        out << "<text x=\"" << x << "\" y=\"" << y
            << "\" text-anchor=\"" << anchor << "\" font-size=\"" << fs
            << "\" fill=\"" << fill << "\"";
        if (!style.empty()) out << " " << style;
        out << ">" << s << "</text>\n";
    }

    void line(double x1, double y1, double x2, double y2,
              const string& stroke = "black", double sw = 1.0,
              const string& dash = "") {
        out << "<line x1=\"" << x1 << "\" y1=\"" << y1
            << "\" x2=\"" << x2 << "\" y2=\"" << y2
            << "\" stroke=\"" << stroke << "\" stroke-width=\"" << sw << "\"";
        if (!dash.empty()) out << " stroke-dasharray=\"" << dash << "\"";
        out << "/>\n";
    }

    void rect(double x, double y, double w, double h,
              const string& fill = "none", const string& stroke = "black",
              double sw = 1.0) {
        out << "<rect x=\"" << x << "\" y=\"" << y
            << "\" width=\"" << w << "\" height=\"" << h
            << "\" fill=\"" << fill << "\" stroke=\"" << stroke
            << "\" stroke-width=\"" << sw << "\"/>\n";
    }

    void poly(const vector<pair<double,double>>& pts,
              const string& fill, double opacity = 0.7,
              const string& stroke = "white", double sw = 0.4) {
        out << "<polygon points=\"";
        for (auto& [x, y] : pts) out << x << "," << y << " ";
        out << "\" fill=\"" << fill << "\" fill-opacity=\"" << opacity
            << "\" stroke=\"" << stroke << "\" stroke-width=\"" << sw << "\"/>\n";
    }

    void clip_def(const string& id, double x, double y, double w, double h) {
        out << "<defs><clipPath id=\"" << id << "\">"
            << "<rect x=\"" << x << "\" y=\"" << y
            << "\" width=\"" << w << "\" height=\"" << h << "\"/>"
            << "</clipPath></defs>\n";
    }

    void begin_group(const string& clip_id = "", const string& attrs = "") {
        out << "<g";
        if (!clip_id.empty()) out << " clip-path=\"url(#" << clip_id << ")\"";
        if (!attrs.empty())   out << " " << attrs;
        out << ">\n";
    }
    void end_group() { out << "</g>\n"; }
};

// ── 30 distinct colors for superpatches (matching Fig. 4 vibrancy) ──
static const char* COLORS[] = {
    "#E53935","#3949AB","#43A047","#F57C00","#8E24AA",
    "#00ACC1","#E91E63","#00897B","#FDD835","#6D4C41",
    "#1E88E5","#FB8C00","#D81B60","#039BE5","#7CB342",
    "#F4511E","#3949AB","#00BCD4","#C0CA33","#8D6E63",
    "#26A69A","#EF5350","#5C6BC0","#66BB6A","#FF7043",
    "#AB47BC","#29B6F6","#9CCC65","#FFCA28","#26C6DA"
};
static const int N_COLORS = 30;

// ── Coordinate transform: (z1,zL) → SVG (x,y) ──
struct CoordMap {
    double ox, oy, pw, ph;  // origin + plot size in SVG
    double z1_min, z1_max, zL_min, zL_max;

    double x(double z1) const {
        return ox + (z1 - z1_min) / (z1_max - z1_min) * pw;
    }
    double y(double zL) const {
        return oy + ph - (zL - zL_min) / (zL_max - zL_min) * ph;
    }
};

// ============================================================
// DRAW ONE PARAMETER-SPACE PANEL  (Fig. 4 style)
// ============================================================
void draw_param_panel(SVGCtx& svg, const WedgeResult& wr,
                      double ox, double oy, int panel_idx,
                      bool show_y_labels, bool show_x_labels) {
    const double PW = 180, PH = 220;  // plot data area
    const double ML = 35, MR = 10, MT = 15, MB = 30;

    double px = ox + ML, py = oy + MT;
    CoordMap cm{px, py, PW, PH, -25.0, 25.0, -55.0, 55.0};

    // Clip definition
    string cid = "cp" + to_string(panel_idx);
    svg.clip_def(cid, px, py, PW, PH);

    // Background
    svg.rect(px, py, PW, PH, "#fafafa", "#bbb", 0.5);

    // Grid lines
    for (int v : {-20,-10,0,10,20}) {
        svg.line(cm.x(v), py, cm.x(v), py+PH, "#ddd", 0.4);
    }
    for (int v : {-40,-20,0,20,40}) {
        svg.line(px, cm.y(v), px+PW, cm.y(v), "#ddd", 0.4);
    }

    // Draw patches (clipped)
    svg.begin_group(cid);
    for (auto& p : wr.patches) {
        if (p.poly.empty()) continue;
        string col = COLORS[p.spatch_id % N_COLORS];
        vector<pair<double,double>> pts;
        for (auto& v : p.poly) pts.push_back({cm.x(v.x), cm.y(v.y)});
        svg.poly(pts, col, 0.75, "white", 0.3);
    }

    // Field boundary lines: z0 = +15 and z0 = -15
    // At z0=c: z1 = c + (zL-c)/R[L-1]*R[0]  i.e., z1 = 0.8*c + 0.2*zL
    for (double z0 : {+15.0, -15.0}) {
        // At zL = -55: z1 = z0 + (-55-z0)/25*5 = z0 - 11 - 0.2*z0 = 0.8*z0 - 11
        double z1a = 0.8*z0 + 0.2*(-55.0);
        double z1b = 0.8*z0 + 0.2*(+55.0);
        svg.line(cm.x(z1a), cm.y(-55.0), cm.x(z1b), cm.y(55.0), "black", 1.2);
    }
    svg.end_group();

    // Axes border
    svg.rect(px, py, PW, PH, "none", "#555", 0.8);

    // X axis ticks and labels
    for (int v : {-20,-10,0,10,20}) {
        double ax = cm.x(v);
        svg.line(ax, py+PH, ax, py+PH+4, "#555", 0.7);
        if (show_x_labels)
            svg.text(ax, py+PH+14, to_string(v), 8);
    }
    if (show_x_labels)
        svg.text(px+PW/2, py+PH+26, "z1 (cm)", 9, "middle", "#333",
                 "font-style=\"italic\"");

    // Y axis ticks and labels
    for (int v : {-40,-20,0,20,40}) {
        double ay = cm.y(v);
        svg.line(px-4, ay, px, ay, "#555", 0.7);
        if (show_y_labels)
            svg.text(px-6, ay+3, to_string(v), 8, "end");
    }
    if (show_y_labels) {
        // Rotated label
        svg.out << "<text transform=\"rotate(-90," << ox+10 << "," << py+PH/2
                << ")\" x=\"" << ox+10 << "\" y=\"" << py+PH/2+4
                << "\" text-anchor=\"middle\" font-size=\"9\" fill=\"#333\""
                << " font-style=\"italic\">z_L (cm)</text>\n";
    }

    // Panel info
    int ntot = (int)wr.patches.size();
    int nsp  = wr.n_superpatches;
    svg.text(px+PW-2, py+12,
             "SP=" + to_string(nsp) + " P=" + to_string(ntot),
             7, "end", "#333");
}

// ============================================================
// DRAW HISTOGRAM (for Fig. 6)
// ============================================================
void draw_histogram(SVGCtx& svg, const vector<int>& data,
                    double ox, double oy, double pw, double ph,
                    const string& xlabel, const string& ylabel,
                    const string& fill_color,
                    double& out_mean, double& out_sigma) {
    if (data.empty()) return;

    int vmin = *min_element(data.begin(), data.end());
    int vmax = *max_element(data.begin(), data.end());
    int nbins = min(30, vmax - vmin + 1);
    double bw = (double)(vmax - vmin + 1) / nbins;

    vector<int> counts(nbins, 0);
    for (int v : data) {
        int b = min((int)((v - vmin) / bw), nbins-1);
        counts[b]++;
    }

    int cmax = *max_element(counts.begin(), counts.end());
    double mean = 0, sq = 0;
    for (int v : data) { mean += v; sq += (double)v*v; }
    mean /= data.size();
    double var = sq/data.size() - mean*mean;
    double sigma = sqrt(max(0.0, var));
    out_mean  = mean;
    out_sigma = sigma;

    const double ML2 = 40, MR2 = 10, MT2 = 15, MB2 = 30;
    double px = ox+ML2, py = oy+MT2, pw2 = pw-ML2-MR2, ph2 = ph-MT2-MB2;

    // Background
    svg.rect(px, py, pw2, ph2, "#fafafa", "#bbb", 0.5);

    // Bars
    double bar_w = pw2 / nbins;
    for (int b = 0; b < nbins; b++) {
        if (counts[b] == 0) continue;
        double bh = (double)counts[b] / cmax * ph2;
        double bx = px + b * bar_w;
        double by = py + ph2 - bh;
        svg.rect(bx+0.5, by, bar_w-1.0, bh, fill_color, "#fff", 0.3);
    }

    // Axes
    svg.rect(px, py, pw2, ph2, "none", "#555", 0.8);

    // X ticks
    int tick_step = max(1, (vmax - vmin) / 5);
    for (int v = vmin; v <= vmax; v += tick_step) {
        double tx2 = px + (v - vmin) / (double)(vmax - vmin + 1) * pw2;
        svg.line(tx2, py+ph2, tx2, py+ph2+4, "#555", 0.7);
        svg.text(tx2, py+ph2+14, to_string(v), 8);
    }
    svg.text(px+pw2/2, py+ph2+26, xlabel, 9, "middle", "#333",
             "font-style=\"italic\"");

    // Y ticks
    for (int i = 0; i <= 4; i++) {
        int yv = (int)(cmax * i / 4.0);
        double ty2 = py + ph2 - (double)yv / cmax * ph2;
        svg.line(px-4, ty2, px, ty2, "#555", 0.7);
        svg.text(px-6, ty2+3, to_string(yv), 8, "end");
    }
    svg.text(ox+10, py+ph2/2, ylabel, 9, "middle", "#333",
             "font-style=\"italic\" transform=\"rotate(-90," +
             to_string((int)(ox+10)) + "," + to_string((int)(py+ph2/2)) + ")\"");

    // Legend box with mean/sigma
    ostringstream leg;
    leg << fixed << setprecision(1) << "mu=" << mean << ", sigma=" << sigma;
    svg.rect(px+pw2-100, py+5, 96, 22, "#e0e8ff", "#4488cc", 1.0);
    svg.text(px+pw2-52, py+20, leg.str(), 8, "middle", "#333");
}

// ============================================================
// FIG. 4 — 6-panel parameter space views
// ============================================================
void generate_fig4(const vector<WedgeResult>& results) {
    const int NR = 2, NC = 3;
    const double PANEL_W = 225+5, PANEL_H = 265+5;
    const double GAP_X = 5, GAP_Y = 5;
    const double OUTER_L = 10, OUTER_T = 40, OUTER_R = 10, OUTER_B = 20;

    double total_w = OUTER_L + NC*PANEL_W + (NC-1)*GAP_X + OUTER_R;
    double total_h = OUTER_T + NR*PANEL_H + (NR-1)*GAP_Y + OUTER_B;

    SVGCtx svg("patches_fig4.svg", (int)total_w, (int)total_h);

    // Title
    svg.text(total_w/2, 25,
             "Patch Formation - Parameter Space (z1, zL)  -  Kotwal 2025 Sci. Rep. 15, 34549",
             12, "middle", "#222");

    for (int r = 0; r < NR; r++) {
        for (int c = 0; c < NC; c++) {
            int idx = r*NC + c;
            if (idx >= (int)results.size()) break;

            double ox = OUTER_L + c*(PANEL_W + GAP_X);
            double oy = OUTER_T + r*(PANEL_H + GAP_Y);

            draw_param_panel(svg, results[idx], ox, oy, idx,
                             c == 0,   // y-labels on leftmost column
                             r == NR-1); // x-labels on bottom row
        }
    }

    cout << "  Saved: patches_fig4.svg\n";
}

// ============================================================
// FIG. 6 — Performance metrics histograms + acceptance
// ============================================================
void generate_fig6(const vector<WedgeResult>& all_results,
                   const vector<AcceptPoint>& accept_pts) {
    const double SW = 820, SH = 600;
    SVGCtx svg("metrics_fig6.svg", (int)SW, (int)SH);

    svg.text(SW/2, 22,
             "Performance Metrics  ·  Kotwal 2025 Sci. Rep. 15, 34549",
             13, "middle", "#222");

    // Aggregate nTP and nP across all wedges (per wedge sum)
    vector<int> all_nTP, all_nP;
    for (auto& wr : all_results) {
        int sum_nTP = 0;
        for (int v : wr.nTP) sum_nTP += v;
        all_nTP.push_back(sum_nTP);
        all_nP.push_back((int)wr.patches.size());
    }

    const double HW = 360, HH = 240;
    double mean_tp, sig_tp, mean_p, sig_p;

    // Top-left: nTP histogram
    draw_histogram(svg, all_nTP, 20, 40, HW, HH,
                   "n_{TP}", "number of covers",
                   "#3498DB", mean_tp, sig_tp);
    svg.text(20+HW/2, 38, "Trial Patches per Cover (n_{TP})", 10,
             "middle", "#444");

    // Top-right: nP histogram
    draw_histogram(svg, all_nP, SW/2+20, 40, HW, HH,
                   "n_P", "number of covers",
                   "#3498DB", mean_p, sig_p);
    svg.text(SW/2+20+HW/2, 38, "Patches per Cover (n_P)", 10,
             "middle", "#444");

    // Bottom: Acceptance loss (1-ε) in ppm vs z0
    // Bin accept_pts by z0
    {
        const int NBINS = 60;
        double z0_lo = -Z0_MAX, z0_hi = Z0_MAX;
        double bw = (z0_hi - z0_lo) / NBINS;
        vector<int>    bin_n(NBINS, 0);
        vector<int>    bin_ok(NBINS, 0);
        for (auto& ap : accept_pts) {
            int b = (int)((ap.z0 - z0_lo) / bw);
            b = max(0, min(NBINS-1, b));
            bin_n[b]++;
            if (ap.accepted) bin_ok[b]++;
        }

        const double PX = 60, PY = 360, PW2 = 680, PH2 = 200;
        svg.text(PX+PW2/2, PY-10, "Acceptance Loss (1-epsilon) vs z0", 10,
                 "middle", "#444");
        svg.rect(PX, PY, PW2, PH2, "#fafafa", "#bbb", 0.5);

        // Grid
        for (int zv : {-10,-5,0,5,10}) {
            double gx = PX + (zv - z0_lo) / (z0_hi - z0_lo) * PW2;
            svg.line(gx, PY, gx, PY+PH2, "#ddd", 0.4);
        }

        // ppm values
        double ppm_max = 0;
        vector<double> ppm(NBINS, 0.0);
        for (int b = 0; b < NBINS; b++) {
            if (bin_n[b] > 0)
                ppm[b] = (1.0 - (double)bin_ok[b]/bin_n[b]) * 1e6;
            ppm_max = max(ppm_max, ppm[b]);
        }
        ppm_max = max(ppm_max, 1.0);

        // Y grid + ticks
        for (int i = 0; i <= 4; i++) {
            double yv = ppm_max * i / 4.0;
            double gy = PY + PH2 - yv / ppm_max * PH2;
            svg.line(PX-4, gy, PX, gy, "#555", 0.7);
            ostringstream ss; ss << fixed << setprecision(1) << yv;
            svg.text(PX-6, gy+3, ss.str(), 8, "end");
            svg.line(PX, gy, PX+PW2, gy, "#eee", 0.4);
        }

        // Draw acceptance loss curve
        svg.out << "<polyline points=\"";
        for (int b = 0; b < NBINS; b++) {
            double bx = PX + (b + 0.5) * PW2 / NBINS;
            double by = PY + PH2 - ppm[b] / ppm_max * PH2;
            svg.out << bx << "," << by << " ";
        }
        svg.out << "\" fill=\"none\" stroke=\"#C0392B\" stroke-width=\"1.3\"/>\n";

        // Dot at each bin center
        for (int b = 0; b < NBINS; b++) {
            double bx = PX + (b + 0.5) * PW2 / NBINS;
            double by = PY + PH2 - ppm[b] / ppm_max * PH2;
            svg.out << "<circle cx=\"" << bx << "\" cy=\"" << by
                    << "\" r=\"2\" fill=\"#C0392B\"/>\n";
        }

        // Compute inclusive mean ppm
        double total_miss = 0, total_n = 0;
        for (auto& ap : accept_pts) { if (!ap.accepted) total_miss++; total_n++; }
        double incl_ppm = (total_miss / total_n) * 1e6;

        // Label
        ostringstream lbl;
        lbl << fixed << setprecision(0) << "<1-epsilon> = " << incl_ppm << " ppm";
        svg.rect(PX+PW2-140, PY+8, 132, 20, "#fff0f0", "#C0392B", 1.0);
        svg.text(PX+PW2-74, PY+22, lbl.str(), 9, "middle", "#C0392B");

        // Axes
        svg.rect(PX, PY, PW2, PH2, "none", "#555", 0.8);

        for (int zv : {-15,-10,-5,0,5,10,15}) {
            double tx2 = PX + (zv - z0_lo) / (z0_hi - z0_lo) * PW2;
            svg.line(tx2, PY+PH2, tx2, PY+PH2+4, "#555", 0.7);
            svg.text(tx2, PY+PH2+14, to_string(zv), 8);
        }
        svg.text(PX+PW2/2, PY+PH2+27, "z0 (cm)", 10, "middle", "#333",
                 "font-style=\"italic\"");

        svg.text(PX-35, PY+PH2/2,
                 "(1-epsilon) (ppm)", 9, "middle", "#333",
                 "font-style=\"italic\" transform=\"rotate(-90," +
                 to_string((int)(PX-35)) + "," + to_string((int)(PY+PH2/2)) + ")\"");
    }

    cout << "  Saved: metrics_fig6.svg\n";
}

// ============================================================
// PRINT CONSOLE SUMMARY
// ============================================================
void print_summary(const WedgeResult& wr, unsigned seed_val) {
    cout << "\n  Wedge seed=" << seed_val << ":\n";
    cout << "    Superpatches : " << wr.n_superpatches << "\n";
    cout << "    Seed patches : " << wr.n_seed << "\n";
    cout << "    Comp patches : " << wr.n_comp << "\n";
    cout << "    Tert patches : " << wr.n_tert << "\n";
    cout << "    Total patches: " << wr.patches.size() << "\n";
    for (int i = 0; i < (int)wr.patches.size(); i++) {
        auto& p = wr.patches[i];
        cout << "    Patch " << i << " (" << (p.type == PT::SEED ? "SEED" : p.type == PT::COMP ? "COMP" : "TERT") << "): size=" << p.poly.size() << "\n";
        for (auto& v : p.poly) {
            cout << "      (" << v.x << ", " << v.y << ")\n";
        }
    }

    double min_z1 = 999.0, max_z1 = -999.0;
    double min_zL = 999.0, max_zL = -999.0;
    for (auto& p : wr.patches) {
        if (p.poly.empty()) continue;
        min_z1 = min(min_z1, px_min(p.poly));
        max_z1 = max(max_z1, px_max(p.poly));
        min_zL = min(min_zL, py_min(p.poly));
        max_zL = max(max_zL, py_max(p.poly));
    }
    cout << "    z1 range     : [" << min_z1 << ", " << max_z1 << "]\n";
    cout << "    zL range     : [" << min_zL << ", " << max_zL << "]\n";

    if (!wr.nTP.empty()) {
        double mTP = 0, mP = 0;
        for (int v : wr.nTP) mTP += v;
        for (int v : wr.nP)  mP  += v;
        mTP /= wr.nTP.size(); mP /= wr.nP.size();
        cout << "    <nTP>        : " << fixed << setprecision(1) << mTP << "\n";
        cout << "    <nP>         : " << fixed << setprecision(1) << mP  << "\n";
    }
}

// ============================================================
// MAIN
// ============================================================
int main() {
    cout << "============================================\n";
    cout << "  Patch Formation Algorithm  (Kotwal 2025)\n";
    cout << "  Sci. Rep. 15, 34549\n";
    cout << "============================================\n";
    cout << "  L=" << L << " layers | N=" << N << " hits/superpoint\n";
    cout << "  |z0|<" << Z0_MAX << " cm | |zL|<" << ZL_MAX << " cm\n\n";

    // ── Run on 6 wedges for Fig. 4 ───────────────────────────
    cout << "Step 1: Running algorithm on 6 wedges (Fig. 4 panels)...\n";
    vector<WedgeResult> fig4_results;
    unsigned seeds6[] = {42, 137, 271, 512, 1024, 2048};
    for (int i = 0; i < 6; i++) {
        WedgeResult wr = run_algorithm(seeds6[i]);
        print_summary(wr, seeds6[i]);
        fig4_results.push_back(wr);
    }

    // ── Run on N_STAT wedges for Fig. 6 statistics ───────────
    const int N_STAT = 100;  // increase to 6400 for paper-scale statistics
    cout << "\nStep 2: Running on " << N_STAT
         << " wedges for performance statistics...\n";

    vector<WedgeResult> stat_results;
    stat_results.reserve(N_STAT);
    for (int i = 0; i < N_STAT; i++) {
        stat_results.push_back(run_algorithm((unsigned)(i * 37 + 7)));
        if ((i+1) % 25 == 0)
            cout << "  Progress: " << i+1 << "/" << N_STAT << "\n";
    }

    // Aggregate statistics per wedge (per cover) to match paper Fig. 6
    vector<int> all_nTP, all_nP;
    for (auto& wr : stat_results) {
        int sum_nTP = 0;
        for (int v : wr.nTP) sum_nTP += v;
        all_nTP.push_back(sum_nTP);
        all_nP.push_back((int)wr.patches.size());
    }
    {
        double mTP=0, mP=0, sTP=0, sP=0;
        for (int v : all_nTP) mTP += v;
        for (int v : all_nP)  mP  += v;
        mTP /= all_nTP.size(); mP /= all_nP.size();
        for (int v : all_nTP) sTP += (v-mTP)*(v-mTP);
        for (int v : all_nP)  sP  += (v-mP)*(v-mP);
        sTP = sqrt(sTP/all_nTP.size()); sP = sqrt(sP/all_nP.size());
        cout << "\n  Statistics over " << N_STAT << " wedges:\n";
        cout << "    nTP:  mu=" << fixed << setprecision(1) << mTP
             << "  sigma=" << sTP << "\n";
        cout << "    nP:   mu=" << mP << "  sigma=" << sP << "\n";
    }

    // ── Compute acceptance efficiency for Fig. 6 bottom ──────
    cout << "\nStep 3: Computing acceptance efficiency...\n";
    auto accept_pts = compute_acceptance(stat_results);
    {
        int miss = 0;
        for (auto& ap : accept_pts) if (!ap.accepted) miss++;
        double ppm = accept_pts.empty() ? 0.0 : (double)miss / accept_pts.size() * 1e6;
        cout << "  Acceptance loss: " << fixed << setprecision(1)
             << ppm << " ppm\n";
    }

    // ── Generate SVG outputs ──────────────────────────────────
    cout << "\nStep 4: Generating SVG infographics...\n";
    generate_fig4(fig4_results);
    generate_fig6(stat_results, accept_pts);

    cout << "\nDone. Output files:\n";
    cout << "  patches_fig4.svg   (parameter space, 6 panels — open in browser)\n";
    cout << "  metrics_fig6.svg   (performance metrics — open in browser)\n";
    cout << "============================================\n";
    return 0;
}
