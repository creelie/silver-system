// bipprop BASE [opt=val ...] : is the CNF BASE.cnf, an encoding of "G is biplanar", satisfiable?
// BASE.lits has a header 'n k' and k lines 'lit l a b': the literal lit is true iff the edge ab
// is drawn in layer l. CaDiCaL solves BASE.cnf with an external propagator: whenever the edges
// assigned to a layer contain a subdivision of K5 or K3,3 (Boyer-Myrvold test of Boost), it adds
// the clause "not all of these edges in this layer". Every such clause is written to BASE.kur
// (DIMACS), so that BASE.cnf with BASE.kur can be refuted again with a proof. Options opt=val
// are passed to CaDiCaL.
#include "cadical.hpp"
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/boyer_myrvold_planar_test.hpp>
#include <boost/graph/is_kuratowski_subgraph.hpp>
#include <chrono>
#include <cstdio>
#include <deque>
#include <map>
#include <fstream>
#include <iostream>
#include <vector>
using namespace boost;
typedef adjacency_list<vecS, vecS, undirectedS, property<vertex_index_t, int>,
                       property<edge_index_t, int>> Graph;

static int n, k, nv;
static std::vector<int> ll, ea, eb, lv;  // per entry: literal, layer, endpoints

struct Prop : CaDiCaL::ExternalPropagator {
  std::vector<int> val, trail;
  std::vector<size_t> lim;
  bool dirty[2] = {true, true}, edirty[2] = {true, true};
  int eager = 0; long nprop = 0; size_t rpos = 0;
  std::deque<std::vector<int>> props;  // propagated literal followed by its reason clause
  std::map<int, std::vector<int>> reason;
  std::deque<std::vector<int>> pending;
  std::vector<int> cur; size_t curpos = 0; bool emitting = false;
  FILE *log;
  long checks = 0, nkur = 0, kurlen = 0;
  std::vector<std::vector<int>> occ;  // var -> entries
  Prop(const char *path) : val(nv + 1, 0), occ(nv + 1) {
    log = fopen(path, "w");
    for (int i = 0; i < k; i++) occ[abs(ll[i])].push_back(i);
  }
  void notify_assignment(const std::vector<int> &lits) override {
    for (int l : lits) { int v = abs(l); if (v > nv || val[v]) continue;
      val[v] = l > 0 ? 1 : -1; trail.push_back(v);
      for (int i : occ[v]) dirty[lv[i]] = edirty[lv[i]] = true; }
  }
  void notify_new_decision_level() override { lim.push_back(trail.size()); }
  void notify_backtrack(size_t lev) override {
    if (lev >= lim.size()) return;
    size_t keep = lim[lev];
    while (trail.size() > keep) { val[trail.back()] = 0; trail.pop_back(); }
    lim.resize(lev);
    props.clear(); edirty[0] = edirty[1] = true;
  }
  static bool planar(const std::vector<int> &ents) {
    Graph h(n);
    for (int i : ents) add_edge(ea[i], eb[i], h);
    return boyer_myrvold_planarity_test(h);
  }
  // a subdivision of K5 or K3,3 among the edges of the entries ents (empty if they are planar)
  std::vector<int> kuratowski(const std::vector<int> &ents) {
    checks++;
    if (ents.size() < 9) return {};
    Graph g(n);
    for (int v : ents) add_edge(ea[v], eb[v], g);
    auto ei = get(edge_index, g); int c = 0;
    graph_traits<Graph>::edge_iterator a, b;
    for (tie(a, b) = edges(g); a != b; ++a) { put(ei, *a, c++); }
    std::vector<graph_traits<Graph>::edge_descriptor> kur;
    if (boyer_myrvold_planarity_test(boyer_myrvold_params::graph = g,
                                     boyer_myrvold_params::kuratowski_subgraph = std::back_inserter(kur)))
      return {};
    // Boost's Kuratowski subgraph may carry extra edges: delete edges greedily while the rest stays
    // non-planar, which leaves a subdivision of K5 or K3,3.
    std::vector<int> sub;
    for (auto &e : kur) {
      int x = source(e, g), y = target(e, g); if (x > y) std::swap(x, y);
      for (int i : ents) if (ea[i] == x && eb[i] == y) { sub.push_back(i); break; }
    }
    for (size_t j = 0; j < sub.size();) {
      std::vector<int> rest;
      for (size_t t = 0; t < sub.size(); t++) if (t != j) rest.push_back(sub[t]);
      if (!planar(rest)) sub = rest; else j++;
    }
    return sub;
  }
  std::vector<int> record(const std::vector<int> &sub) {
    std::vector<int> cl;
    for (int i : sub) cl.push_back(-ll[i]);
    nkur++; kurlen += cl.size();
    for (int lit : cl) fprintf(log, "%d ", lit);
    fprintf(log, "0\n");
    return cl;
  }
  std::vector<int> layer(int l, const std::vector<int> &sgn) {
    std::vector<int> es;  // entries of layer l whose literal is true
    for (int i = 0; i < k; i++)
      if (lv[i] == l && sgn[abs(ll[i])] == (ll[i] > 0 ? 1 : -1)) es.push_back(i);
    return es;
  }
  // returns true if layer l of the assignment sgn is planar; otherwise queues a clause
  bool test(int l, const std::vector<int> &sgn) {
    auto sub = kuratowski(layer(l, sgn));
    if (sub.empty()) return true;
    pending.push_back(record(sub));
    return false;
  }
  // eager mode: an unassigned literal whose edge would make its layer non-planar is set false,
  // with the Kuratowski clause as its reason
  void scan(int l) {
    auto es = layer(l, val);
    if (!kuratowski(es).empty()) return;  // a conflict clause will follow
    for (int i = 0; i < k; i++) {
      if (lv[i] != l || val[abs(ll[i])] != 0) continue;
      es.push_back(i);
      auto sub = kuratowski(es);
      es.pop_back();
      if (!sub.empty()) props.push_back(record(sub)), props.back().insert(props.back().begin(), -ll[i]);
    }
  }
  bool cb_check_found_model(const std::vector<int> &model) override {
    std::vector<int> s(nv + 1, 0);
    for (int lit : model) if (abs(lit) <= nv) s[abs(lit)] = lit > 0 ? 1 : -1;
    bool ok = true;
    for (int l = 0; l < 2; l++) ok &= test(l, s);
    return ok;
  }
  bool cb_has_external_clause(bool &forget) override {
    forget = false;
    if (pending.empty())
      for (int l = 0; l < 2; l++) if (dirty[l]) { dirty[l] = false; test(l, val); }
    return !pending.empty();
  }
  int cb_add_external_clause_lit() override {
    if (!emitting) { cur = pending.front(); pending.pop_front(); curpos = 0; emitting = true; }
    if (curpos < cur.size()) return cur[curpos++];
    emitting = false; return 0;
  }
  int cb_decide() override { return 0; }
  int cb_propagate() override {
    if (!eager) return 0;
    if (props.empty())
      for (int l = 0; l < 2; l++) if (edirty[l]) { edirty[l] = false; scan(l); }
    while (!props.empty()) {
      auto r = props.front(); props.pop_front();
      int lit = r[0]; r.erase(r.begin());
      if (val[abs(lit)] != 0) continue;
      reason[lit] = r; nprop++; return lit;
    }
    return 0;
  }
  int cb_add_reason_clause_lit(int plit) override {
    auto &cl = reason[plit];
    if (rpos < cl.size()) return cl[rpos++];
    rpos = 0; return 0;
  }
};

int main(int argc, char **argv) {
  std::string base = argv[1];
  { std::ifstream f(base + ".lits"); f >> n >> k; ll.resize(k); lv.resize(k); ea.resize(k); eb.resize(k);
    nv = 0;
    for (int i = 0; i < k; i++) { f >> ll[i] >> lv[i] >> ea[i] >> eb[i];
      if (ea[i] > eb[i]) std::swap(ea[i], eb[i]); nv = std::max(nv, abs(ll[i])); } }
  CaDiCaL::Solver s;
  int eager = 0;
  for (int i = 2; i < argc; i++) { std::string o = argv[i]; auto p = o.find('=');
    if (p == std::string::npos) continue;
    if (o.substr(0, p) == "eager") eager = atoi(o.substr(p + 1).c_str());
    else s.set(o.substr(0, p).c_str(), atoi(o.substr(p + 1).c_str())); }
  int vars; bool strict = false;
  const char *err = s.read_dimacs((base + ".cnf").c_str(), vars, strict);
  if (err) { std::cerr << err << "\n"; return 1; }
  Prop P((base + ".kur").c_str());
  P.eager = eager;
  s.connect_external_propagator(&P);
  for (int i = 0; i < k; i++) s.add_observed_var(abs(ll[i]));
  auto t0 = std::chrono::steady_clock::now();
  int r = s.solve();
  double t = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  fclose(P.log);
  printf("%s %s time %.1f kuratowski %ld avglen %.1f checks %ld propagated %ld\n", base.c_str(),
         r == 10 ? "SAT" : r == 20 ? "UNSAT" : "UNKNOWN", t, P.nkur,
         P.nkur ? (double)P.kurlen / P.nkur : 0.0, P.checks, P.nprop);
  if (r == 10)
    for (int l = 0; l < 2; l++) { printf("L%d", l);
      for (int i = 0; i < k; i++) if (lv[i] == l && s.val(ll[i]) > 0) printf(" %d-%d", ea[i], eb[i]);
      printf("\n"); }
  s.disconnect_external_propagator();
  return r == 10 ? 10 : r == 20 ? 20 : 0;
}
