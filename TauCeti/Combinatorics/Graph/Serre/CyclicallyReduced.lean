/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Core
public import TauCeti.Combinatorics.Graph.Serre.Degree
public import TauCeti.Combinatorics.Graph.Serre.Dist

import TauCeti.Data.List.Chain

/-!
# Cyclically reduced closed paths in a Serre graph

A closed path is cyclically reduced when traversing it twice is reduced: it has no backtracking,
also not from its last dart to its first. The darts on such paths, and the vertices at which a
nonempty one is based, form the part of a graph that does not depend on a base vertex: in a
preconnected graph the based core at any of these vertices consists of exactly these darts and
vertices, whereas the based core at another vertex also contains a path leading to them.

The main results are:

* `SerreGraph.mem_cyclicDarts_of_isReduced`: a reduced path between two vertices lying on
  cyclically reduced closed paths only uses darts on cyclically reduced closed paths;
* `SerreGraph.Preconnected.coreDarts_eq_cyclicDarts` and
  `SerreGraph.Preconnected.coreVertices_eq_cyclicVertices`: the based core at such a vertex;
* `SerreGraph.cyclicVertices_eq_empty_iff`: there is no such vertex exactly in acyclic graphs;
* `SerreGraph.IsCore.mem_cyclicVertices_of_ne`: the base vertex of a core lies on a cyclically
  reduced closed path as soon as two distinct darts leave it.
* `SerreGraph.IsCore.cyclicDarts_eq_univ` and `SerreGraph.IsCore.cyclicVertices_eq_univ`: a core
  whose base vertex lies on a cyclically reduced closed path consists of such paths;
* `SerreGraph.Path.IsCyclicallyReduced.mem_coreDarts`: a cyclically reduced closed path whose
  base vertex is reachable from `v` lies in the based core at `v`;
* `SerreGraph.mem_cyclicDarts_core_iff` and `SerreGraph.mem_cyclicVertices_core_iff`: passing to
  a based core does not change the darts and vertices on cyclically reduced closed paths;
* `SerreGraph.IsCore.notMem_cyclicDarts_iff` and `SerreGraph.IsCore.notMem_cyclicVertices_iff`:
  in a core that is not acyclic, the darts and vertices on no cyclically reduced closed path are
  those of a path hanging from the base vertex, which meets the cyclically reduced closed paths
  only at its end. Such a reduced path exists by `SerreGraph.Preconnected.exists_isReduced_path`.

This is the graph-theoretic content of the type of a core graph, obtained from a based core by
deleting the path that hangs from the base vertex: for a core graph with at least one dart, the
type consists of the darts and vertices on cyclically reduced closed paths. The type of the
one-vertex graph is that vertex, which lies on no nonempty cyclically reduced closed path.

Kapovich and Myasnikov describe the hanging path by the degrees of its vertices
(`SerreGraph.degree`): when the base vertex has degree one, it is the unique shortest path to the
first vertex of degree at least three, and its internal vertices have degree two. The two
descriptions agree:

* `SerreGraph.IsCore.degree_le_two`, `SerreGraph.IsCore.two_le_degree` and
  `SerreGraph.IsCore.degree_eq_two`: in a core, a vertex on no cyclically reduced closed path has
  degree at most two, and every vertex other than the base vertex has degree at least two;
* `SerreGraph.three_le_degree_tgt_of_notMem_cyclicDarts`: a vertex on a cyclically reduced closed
  path entered by a dart on no such path has degree at least three;
* `SerreGraph.IsCore.two_le_degree_iff_mem_cyclicVertices` and
  `SerreGraph.IsCore.degree_eq_zero_iff_isAcyclic`: the base vertex of a core has degree at least
  two exactly when it lies on a cyclically reduced closed path, and degree zero exactly when the
  core is acyclic;
* `SerreGraph.IsCore.notMem_cyclicDarts_iff_of_three_le_degree`: when the base vertex has degree
  at most one, the darts on no cyclically reduced closed path are the darts of any path from the
  base vertex to the first vertex of degree at least three, and their reverses;
* `SerreGraph.IsCore.existsUnique_three_le_degree`: when the base vertex has degree one, the end
  of the hanging path is the unique vertex of degree at least three joined to the base vertex by a
  unique shortest path whose internal vertices have degree two.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Lemma 3.7, and Section 7, Definition 7.3, Remark 7.4 and Lemma 7.5.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

/-- A closed path is cyclically reduced when its square is reduced: no dart is followed by its
reverse, also not cyclically from the last dart to the first. -/
def Path.IsCyclicallyReduced {a : Γ.V} (p : Γ.Path a a) : Prop :=
  Path.IsReduced Γ (p.comp p)

theorem Path.isCyclicallyReduced_iff {a : Γ.V} (p : Γ.Path a a) :
    Path.IsCyclicallyReduced Γ p ↔ Path.IsReduced Γ (p.comp p) := Iff.rfl

/-- Cyclic reducedness is the chain condition on the doubled dart list. -/
theorem Path.isCyclicallyReduced_iff_isChain {a : Γ.V} (p : Γ.Path a a) :
    Path.IsCyclicallyReduced Γ p ↔
      (Path.darts Γ p ++ Path.darts Γ p).IsChain fun e f => f ≠ Γ.rev e := by
  rw [Path.isCyclicallyReduced_iff, Path.isReduced_iff_isChain, Path.darts_comp]

/-- A cyclically reduced closed path is reduced. -/
theorem Path.IsCyclicallyReduced.isReduced {a : Γ.V} {p : Γ.Path a a}
    (hp : Path.IsCyclicallyReduced Γ p) : Path.IsReduced Γ p :=
  Path.IsReduced.of_comp_left Γ hp

@[simp] theorem Path.isCyclicallyReduced_nil (a : Γ.V) :
    Path.IsCyclicallyReduced Γ (Quiver.Path.nil : Γ.Path a a) :=
  Path.isReduced_nil Γ a

/-- Reversing a closed path preserves cyclic reducedness. -/
@[simp] theorem Path.isCyclicallyReduced_reverse {a : Γ.V} (p : Γ.Path a a) :
    Path.IsCyclicallyReduced Γ p.reverse ↔ Path.IsCyclicallyReduced Γ p := by
  rw [Path.isCyclicallyReduced_iff, Path.isCyclicallyReduced_iff, ← Quiver.Path.reverse_comp,
    Path.isReduced_reverse]

/-- A morphism injective on darts preserves and reflects cyclically reduced closed paths. -/
theorem Hom.isCyclicallyReduced_mapPath_iff {Δ : SerreGraph} (f : Γ.Hom Δ)
    (hf : Function.Injective f.mapE) {a : Γ.V} (p : Γ.Path a a) :
    Path.IsCyclicallyReduced Δ (f.toPrefunctor.mapPath p) ↔ Path.IsCyclicallyReduced Γ p := by
  rw [Path.isCyclicallyReduced_iff, Path.isCyclicallyReduced_iff, ← Prefunctor.mapPath_comp,
    Hom.isReduced_mapPath_iff Γ f hf]

/-- A cyclically reduced closed path can be restarted at any of its darts: the rotated path is
cyclically reduced, begins with that dart, and traverses the same darts. -/
theorem Path.IsCyclicallyReduced.exists_rotate {a : Γ.V} {p : Γ.Path a a}
    (hp : Path.IsCyclicallyReduced Γ p) {e : Γ.E} (he : e ∈ Path.darts Γ p) :
    ∃ p' : Γ.Path (Γ.src e) (Γ.src e), Path.IsCyclicallyReduced Γ p' ∧
      (Path.darts Γ p').head? = some e ∧ ∀ f, f ∈ Path.darts Γ p' ↔ f ∈ Path.darts Γ p := by
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  refine ⟨((Γ.dart e).toPath.comp r).comp q, ?_, by simp, fun f => by simp; tauto⟩
  rw [Path.isCyclicallyReduced_iff_isChain] at hp ⊢
  have h := List.isRotated_append (l := Path.darts Γ q) (l' := e :: Path.darts Γ r)
  simpa using h.isChain_append_self_iff.1 (by simpa using hp)

/-- A cyclically reduced closed path can be restarted, possibly after reversing it, at the
initial vertex of any dart that it traverses in one of the two directions. -/
private theorem Path.IsCyclicallyReduced.exists_rotate_or_reverse {a : Γ.V} {c : Γ.Path a a}
    (hc : Path.IsCyclicallyReduced Γ c) {d : Γ.E}
    (h : d ∈ Path.darts Γ c ∨ Γ.rev d ∈ Path.darts Γ c) :
    ∃ c₁ : Γ.Path (Γ.src d) (Γ.src d), Path.IsCyclicallyReduced Γ c₁ ∧ Path.darts Γ c₁ ≠ [] ∧
      ∀ e ∈ Path.darts Γ c, e ∈ Path.darts Γ c₁ ∨ Γ.rev e ∈ Path.darts Γ c₁ := by
  rcases h with h | h
  · obtain ⟨c₁, h1, h2, h3⟩ := hc.exists_rotate Γ h
    exact ⟨c₁, h1, fun h0 => by simp [h0] at h2, fun e he => Or.inl ((h3 e).mpr he)⟩
  · obtain ⟨c₁, h1, h2, h3⟩ := ((Path.isCyclicallyReduced_reverse Γ c).mpr hc).exists_rotate
      Γ (e := d) (by simpa using ⟨Γ.rev d, h, Γ.rev_rev d⟩)
    exact ⟨c₁, h1, fun h0 => by simp [h0] at h2,
      fun e he => Or.inr ((h3 _).mpr (by simpa using ⟨e, he, rfl⟩))⟩

/-- A reduced closed path that is not cyclically reduced ends with the reverse of its first
dart. -/
private theorem Path.IsReduced.exists_getLast?_rev_mem_head? {a : Γ.V} {p : Γ.Path a a}
    (hp : Path.IsReduced Γ p) (hc : ¬ Path.IsCyclicallyReduced Γ p) :
    ∃ e ∈ (Path.darts Γ p).getLast?, Γ.rev e ∈ (Path.darts Γ p).head? := by
  rw [Path.isCyclicallyReduced_iff, Path.isReduced_comp_iff] at hc
  simp only [hp, true_and, not_forall, not_not] at hc
  obtain ⟨e, he, f, hf, rfl⟩ := hc
  exact ⟨e, he, hf⟩

/-- The darts lying on a cyclically reduced closed path. -/
def cyclicDarts : Set Γ.E :=
  {e | ∃ (a : Γ.V) (p : Γ.Path a a), Path.IsCyclicallyReduced Γ p ∧ e ∈ Path.darts Γ p}

theorem mem_cyclicDarts_iff (e : Γ.E) :
    e ∈ Γ.cyclicDarts ↔
      ∃ (a : Γ.V) (p : Γ.Path a a), Path.IsCyclicallyReduced Γ p ∧ e ∈ Path.darts Γ p :=
  Iff.rfl

/-- The darts on cyclically reduced closed paths are closed under reversal. -/
@[simp] theorem rev_mem_cyclicDarts_iff (e : Γ.E) :
    Γ.rev e ∈ Γ.cyclicDarts ↔ e ∈ Γ.cyclicDarts := by
  suffices h : ∀ e ∈ Γ.cyclicDarts, Γ.rev e ∈ Γ.cyclicDarts from
    ⟨fun he => by simpa using h (Γ.rev e) he, h e⟩
  rintro e ⟨a, p, hp, he⟩
  exact ⟨a, p.reverse, (Path.isCyclicallyReduced_reverse Γ p).mpr hp, by simpa using ⟨e, he, rfl⟩⟩

/-- The vertices at which a nonempty cyclically reduced closed path is based. -/
def cyclicVertices : Set Γ.V :=
  {a | ∃ p : Γ.Path a a, 0 < p.length ∧ Path.IsCyclicallyReduced Γ p}

theorem mem_cyclicVertices_iff (a : Γ.V) :
    a ∈ Γ.cyclicVertices ↔ ∃ p : Γ.Path a a, 0 < p.length ∧ Path.IsCyclicallyReduced Γ p :=
  Iff.rfl

/-- The vertices carrying a nonempty cyclically reduced closed path are the initial vertices of
the darts on such paths. -/
theorem mem_cyclicVertices_iff_exists_src (a : Γ.V) :
    a ∈ Γ.cyclicVertices ↔ ∃ e ∈ Γ.cyclicDarts, Γ.src e = a := by
  constructor
  · rintro ⟨p, h0, hp⟩
    obtain ⟨e, l, hl⟩ := List.exists_cons_of_ne_nil (Path.darts_ne_nil Γ h0)
    exact ⟨e, ⟨a, p, hp, by simp [hl]⟩, Path.src_eq_of_mem_head?_darts Γ p (by simp [hl])⟩
  · rintro ⟨e, ⟨b, p, hp, he⟩, rfl⟩
    obtain ⟨p', hp', hhead, -⟩ := hp.exists_rotate Γ he
    refine ⟨p', ?_, hp'⟩
    rw [← Path.length_darts, List.length_pos_iff]
    rintro h
    simp [h] at hhead

theorem src_mem_cyclicVertices {e : Γ.E} (he : e ∈ Γ.cyclicDarts) :
    Γ.src e ∈ Γ.cyclicVertices :=
  (Γ.mem_cyclicVertices_iff_exists_src _).mpr ⟨e, he, rfl⟩

theorem tgt_mem_cyclicVertices {e : Γ.E} (he : e ∈ Γ.cyclicDarts) :
    Γ.tgt e ∈ Γ.cyclicVertices := by
  simpa only [Γ.src_rev] using Γ.src_mem_cyclicVertices ((Γ.rev_mem_cyclicDarts_iff e).mpr he)

/-- A morphism injective on darts sends vertices on cyclically reduced closed paths to such
vertices. -/
theorem Hom.map_mem_cyclicVertices {Δ : SerreGraph} (f : Γ.Hom Δ)
    (hf : Function.Injective f.mapE) {a : Γ.V} (ha : a ∈ Γ.cyclicVertices) :
    f.mapV a ∈ Δ.cyclicVertices := by
  obtain ⟨p, h0, hp⟩ := ha
  exact ⟨f.toPrefunctor.mapPath p, h0.trans_eq (Prefunctor.length_mapPath f.toPrefunctor p).symm,
    (f.isCyclicallyReduced_mapPath_iff Γ hf p).mpr hp⟩

/-- A morphism injective on darts sends darts on cyclically reduced closed paths to such darts. -/
theorem Hom.map_mem_cyclicDarts {Δ : SerreGraph} (f : Γ.Hom Δ)
    (hf : Function.Injective f.mapE) {e : Γ.E} (he : e ∈ Γ.cyclicDarts) :
    f.mapE e ∈ Δ.cyclicDarts := by
  obtain ⟨a, p, hp, he⟩ := he
  exact ⟨_, f.toPrefunctor.mapPath p, (f.isCyclicallyReduced_mapPath_iff Γ hf p).mpr hp,
    by rw [Hom.darts_mapPath]; exact List.mem_map_of_mem he⟩

/-- Conjugating a nonempty cyclically reduced closed path by a reduced path whose last dart it
traverses in neither direction gives a reduced closed path. -/
private theorem Path.IsCyclicallyReduced.isReduced_conj_cons {u : Γ.V} {d : Γ.E}
    (q : Γ.Path u (Γ.src d)) (hq : Path.IsReduced Γ (q.cons ⟨d, rfl, rfl⟩))
    {c : Γ.Path (Γ.tgt d) (Γ.tgt d)} (hc : Path.IsCyclicallyReduced Γ c)
    (hc0 : Path.darts Γ c ≠ []) (h : d ∉ Path.darts Γ c ∧ Γ.rev d ∉ Path.darts Γ c) :
    Path.IsReduced Γ (((q.cons ⟨d, rfl, rfl⟩).comp c).comp (q.cons ⟨d, rfl, rfl⟩).reverse) := by
  rw [Path.isReduced_comp_iff, Path.isReduced_comp_iff, Path.isReduced_reverse]
  refine ⟨⟨hq, hc.isReduced, fun e he f hf hfe => ?_⟩, hq, fun e he f hf hfe => ?_⟩
  · have hde : d = e := by simpa using he
    subst hde
    exact h.2 (hfe ▸ List.mem_of_mem_head? hf)
  · have hdf : Γ.rev d = f := by simpa using hf
    have hde : d = e := Γ.rev_injective (hdf.trans hfe)
    subst hde
    rw [Path.darts_comp, List.getLast?_append_of_ne_nil _ hc0] at he
    exact h.1 (List.mem_of_mem_getLast? he)

/-- A reduced path ending on a cyclically reduced closed path `c` splits into a prefix and a
suffix running along cyclically reduced closed paths, such that conjugating a rotation of
`c` or of its reverse by the prefix is a reduced closed path. -/
private theorem exists_isReduced_comp_comp_reverse {u a : Γ.V} (q : Γ.Path u a)
    (hq : Path.IsReduced Γ q) (c : Γ.Path a a) (hc : Path.IsCyclicallyReduced Γ c)
    (hc0 : Path.darts Γ c ≠ []) :
    ∃ (b : Γ.V) (q' : Γ.Path u b) (r : Γ.Path b a) (c' : Γ.Path b b),
      q = q'.comp r ∧ (∀ e ∈ Path.darts Γ r, e ∈ Γ.cyclicDarts) ∧
        Path.IsCyclicallyReduced Γ c' ∧ Path.darts Γ c' ≠ [] ∧
        (∀ e ∈ Path.darts Γ c, e ∈ Path.darts Γ c' ∨ Γ.rev e ∈ Path.darts Γ c') ∧
        Path.IsReduced Γ ((q'.comp c').comp q'.reverse) := by
  induction q with
  | nil =>
    exact ⟨_, .nil, .nil, c, rfl, by simp, hc, hc0, fun e he => Or.inl he,
      by simpa using hc.isReduced⟩
  | cons q d ih =>
    obtain ⟨d, rfl, rfl⟩ := d
    by_cases h : d ∈ Path.darts Γ c ∨ Γ.rev d ∈ Path.darts Γ c
    · -- The last dart of `q` runs along `c`: restart `c` at its initial vertex and shorten `q`.
      have hd : d ∈ Γ.cyclicDarts := by
        rcases h with h | h
        · exact ⟨_, c, hc, h⟩
        · exact (Γ.rev_mem_cyclicDarts_iff d).mp ⟨_, c, hc, h⟩
      obtain ⟨c₁, hc₁, hc₁0, hcc₁⟩ := hc.exists_rotate_or_reverse Γ h
      obtain ⟨b, q', r, c', rfl, hr, hc', hc'0, hcc', hred⟩ := ih (hq.of_cons Γ) c₁ hc₁ hc₁0
      refine ⟨b, q', r.cons ⟨d, rfl, rfl⟩, c', rfl, ?_, hc', hc'0, fun e he => ?_, hred⟩
      · intro e he
        rcases (by simpa using he : e ∈ Path.darts Γ r ∨ e = d) with he | rfl
        · exact hr e he
        · exact hd
      · rcases hcc₁ e he with h1 | h1
        · exact hcc' e h1
        · simpa [or_comm] using hcc' _ h1
    · -- Otherwise there is no backtracking where `q` meets `c`.
      exact ⟨_, q.cons ⟨d, rfl, rfl⟩, .nil, c, rfl, by simp, hc, hc0, fun e he => Or.inl he,
        hc.isReduced_conj_cons Γ q hq hc0 (not_or.mp h)⟩

/-- A reduced path between two vertices on cyclically reduced closed paths only traverses darts
lying on cyclically reduced closed paths. -/
theorem mem_cyclicDarts_of_isReduced {a b : Γ.V} (ha : a ∈ Γ.cyclicVertices)
    (hb : b ∈ Γ.cyclicVertices) {q : Γ.Path a b} (hq : Path.IsReduced Γ q) {e : Γ.E}
    (he : e ∈ Path.darts Γ q) : e ∈ Γ.cyclicDarts := by
  obtain ⟨ca, ha0, hca⟩ := ha
  obtain ⟨cb, hb0, hcb⟩ := hb
  -- Shorten `q` at its end, then the reverse of the remaining prefix at the other end.
  obtain ⟨b', q', r, cb', rfl, hr, -, _, -, h1⟩ :=
    Γ.exists_isReduced_comp_comp_reverse q hq cb hcb (Path.darts_ne_nil Γ hb0)
  rcases List.mem_append.mp (by simpa using he) with he | he
  swap
  · exact hr e he
  obtain ⟨a', q'', r', ca', hq'', hr', -, hca'0, -, h2⟩ :=
    Γ.exists_isReduced_comp_comp_reverse q'.reverse
      ((Path.isReduced_reverse Γ q').mpr ((h1.of_comp_left Γ).of_comp_left Γ)) ca hca
      (Path.darts_ne_nil Γ ha0)
  have hdr : Path.darts Γ q'.reverse = Path.darts Γ q'' ++ Path.darts Γ r' := by
    rw [hq'', Path.darts_comp]
  have hd : Path.darts Γ q' = (Path.darts Γ r').reverse.map Γ.rev ++
      (Path.darts Γ q'').reverse.map Γ.rev := by
    have h := Path.darts_reverse Γ q'.reverse
    rw [Quiver.Path.reverse_reverse, hdr] at h
    simpa using h
  rw [← Γ.rev_mem_cyclicDarts_iff]
  rcases List.mem_append.mp
      (hdr ▸ (by simpa using ⟨e, he, rfl⟩ : Γ.rev e ∈ Path.darts Γ q'.reverse))
      with he' | he'
  swap
  · exact hr' _ he'
  -- What is left of `q` joins two cyclically reduced closed paths without backtracking, and
  -- going around both along it is cyclically reduced.
  refine ⟨_, ((q''.comp ca').comp q''.reverse).comp cb', ?_, by simp [he']⟩
  rw [Path.isReduced_iff_isChain] at h1 h2
  rw [Path.isCyclicallyReduced_iff_isChain]
  simp only [Path.darts_comp, hdr, hd] at h1
  simp only [Path.darts_comp, Path.darts_reverse] at h2 ⊢
  exact h2.append_self_of_overlap
    (h1.infix ⟨(Path.darts Γ r').reverse.map Γ.rev, Path.darts Γ r', by simp⟩)
    (List.ne_nil_of_mem he') (by simpa using List.ne_nil_of_mem he')

/-- A nonempty reduced path with equal endpoints forces a cyclically reduced closed path:
either it is one, or removing its first and last darts leaves a shorter one. -/
private theorem cyclicVertices_nonempty_aux (n : ℕ) : ∀ {a b : Γ.V} (p : Γ.Path a b), a = b →
    Path.IsReduced Γ p → p.length = n → 0 < n → Γ.cyclicVertices.Nonempty := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b p hab hp hn h0
  subst hab
  by_cases hc : Path.IsCyclicallyReduced Γ p
  · exact ⟨a, p, by omega, hc⟩
  obtain ⟨e, he, hf⟩ := hp.exists_getLast?_rev_mem_head? Γ hc
  have ha : Γ.tgt e = a := Path.tgt_eq_of_mem_getLast?_darts Γ p he
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p (List.mem_of_mem_getLast? he)
  simp only [Quiver.Path.length_comp, Quiver.Path.length_cons] at hn
  rcases Nat.eq_zero_or_pos r.length with hr | hr
  swap
  · exact ih r.length (by omega) r ha (hp.of_comp_right Γ) rfl hr
  have hr' : Path.darts Γ r = [] := List.eq_nil_of_length_eq_zero (by rw [Path.length_darts, hr])
  simp only [Path.darts_comp, Path.darts_cons, dart_val, hr', List.append_nil] at hf
  have hq : Γ.rev e ∈ Path.darts Γ q := by
    have hf' : (Path.darts Γ q ++ [e]).head? = some (Γ.rev e) := hf
    cases h : Path.darts Γ q with
    | nil =>
      rw [h] at hf'
      exact absurd (Option.some.inj hf').symm (Γ.rev_ne e)
    | cons x l =>
      rw [h] at hf'
      exact Option.some.inj hf' ▸ List.mem_cons_self
  obtain ⟨q₁, r₁, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ q hq
  have hp' := hp.of_comp_left Γ
  simp only [Quiver.Path.length_comp, Quiver.Path.length_cons] at hn
  rcases Nat.eq_zero_or_pos r₁.length with hr₁ | hr₁
  swap
  · exact ih r₁.length (by omega) r₁ (Γ.tgt_rev e) ((hp'.of_cons Γ).of_comp_right Γ) rfl hr₁
  -- The dart `e` cannot directly follow its reverse.
  have hr₁' : Path.darts Γ r₁ = [] :=
    List.eq_nil_of_length_eq_zero (by rw [Path.length_darts, hr₁])
  rw [Path.isReduced_iff_isChain] at hp'
  simp only [Path.darts_cons, Path.darts_comp, dart_val, hr₁', List.append_nil,
    List.append_assoc, List.cons_append, List.nil_append] at hp'
  have := List.isChain_pair.mp hp'.right_of_append
  simp at this

/-- A nonempty reduced closed path forces a nonempty cyclically reduced closed path. -/
theorem cyclicVertices_nonempty_of_isReduced {a : Γ.V} (p : Γ.Path a a)
    (hp : Path.IsReduced Γ p) (h0 : 0 < p.length) : Γ.cyclicVertices.Nonempty :=
  Γ.cyclicVertices_nonempty_aux p.length p rfl hp rfl h0

/-- A graph has no nonempty cyclically reduced closed path exactly when it is acyclic. -/
theorem cyclicVertices_eq_empty_iff : Γ.cyclicVertices = ∅ ↔ Γ.IsAcyclic := by
  rw [isAcyclic_iff]
  constructor
  · intro h a p hp
    by_contra hne
    have h0 : 0 < p.length :=
      Nat.pos_of_ne_zero fun h0 => hne (Quiver.Path.eq_nil_of_length_zero p h0)
    exact (Γ.cyclicVertices_nonempty_of_isReduced p hp h0).ne_empty h
  · intro h
    refine Set.eq_empty_of_forall_notMem fun a ⟨p, h0, hp⟩ => ?_
    rw [h a p hp.isReduced] at h0
    simp at h0

variable {Γ}

/-- The darts of a cyclically reduced closed path whose base vertex can be reached from `v` lie
in the based core at `v`. -/
theorem Path.IsCyclicallyReduced.mem_coreDarts {v a : Γ.V} {c : Γ.Path a a}
    (hc : Path.IsCyclicallyReduced Γ c) (q : Γ.Path v a) {e : Γ.E} (he : e ∈ Path.darts Γ c) :
    e ∈ Γ.coreDarts v := by
  obtain ⟨b, q', r, c', -, -, -, -, hcc', hred⟩ :=
    Γ.exists_isReduced_comp_comp_reverse (Path.reduce Γ q) (Path.isReduced_reduce Γ q) c hc
      (List.ne_nil_of_mem he)
  have key : ∀ f ∈ Path.darts Γ c', f ∈ Γ.coreDarts v := fun f hf =>
    (Γ.mem_coreDarts_iff v f).mpr ⟨_, hred, by simp [hf]⟩
  rcases hcc' e he with h1 | h1
  · exact key e h1
  · exact (Γ.rev_mem_coreDarts_iff v e).mp (key _ h1)

/-- A cyclically reduced closed path based at a vertex of a based core is a cyclically reduced
closed path of the core. -/
private theorem Path.IsCyclicallyReduced.exists_core_path {v : Γ.V} {a : (Γ.core v).V}
    {c : Γ.Path a.1 a.1} (hc : Path.IsCyclicallyReduced Γ c) :
    ∃ q : (Γ.core v).Path a a, Path.IsCyclicallyReduced (Γ.core v) q ∧
      (Γ.coreInclusion v).toPrefunctor.mapPath q = c := by
  obtain ⟨q₀⟩ := Γ.core_reachable v a
  obtain ⟨q, rfl⟩ : ∃ q : (Γ.core v).Path a a, _ := Γ.exists_subgraph_path _ _ _ _ c
    (fun e he => hc.mem_coreDarts ((Γ.coreInclusion v).toPrefunctor.mapPath q₀) he) a.2 a.2
  exact ⟨q, ((Γ.coreInclusion v).isCyclicallyReduced_mapPath_iff _
    (Γ.subgraphInclusion_mapE_injective _ _ _ _) q).mp hc, rfl⟩

/-- A vertex of a based core lies on a cyclically reduced closed path of the core exactly when it
does so in the ambient graph. -/
theorem mem_cyclicVertices_core_iff (v : Γ.V) (a : (Γ.core v).V) :
    a ∈ (Γ.core v).cyclicVertices ↔ a.1 ∈ Γ.cyclicVertices := by
  refine ⟨(Γ.coreInclusion v).map_mem_cyclicVertices _
    (Γ.subgraphInclusion_mapE_injective _ _ _ _), ?_⟩
  rintro ⟨c, h0, hc⟩
  obtain ⟨q, hq, rfl⟩ := hc.exists_core_path
  exact ⟨q, h0.trans_eq (Prefunctor.length_mapPath _ q), hq⟩

/-- A dart of a based core lies on a cyclically reduced closed path of the core exactly when it
does so in the ambient graph. -/
theorem mem_cyclicDarts_core_iff (v : Γ.V) (e : (Γ.core v).E) :
    e ∈ (Γ.core v).cyclicDarts ↔ e.1 ∈ Γ.cyclicDarts := by
  refine ⟨(Γ.coreInclusion v).map_mem_cyclicDarts _
    (Γ.subgraphInclusion_mapE_injective _ _ _ _), ?_⟩
  rintro ⟨a, c, hc, he⟩
  -- Restart the closed path at `e`, whose initial vertex lies in the core.
  obtain ⟨c', hc', -, hcc'⟩ := hc.exists_rotate Γ he
  obtain ⟨q, hq, rfl⟩ := hc'.exists_core_path (a := (Γ.core v).src e)
  refine ⟨_, q, hq, ?_⟩
  have hd := Hom.darts_mapPath (Γ.core v) (Γ.coreInclusion v) q
  obtain ⟨f, hf, hfe⟩ :=
    List.mem_map.mp (Eq.mp (congrArg (fun l => e.1 ∈ l) hd) ((hcc' e.1).mpr he))
  exact Subtype.ext hfe ▸ hf

/-- In a preconnected graph every dart on a cyclically reduced closed path lies in the based
core at every vertex. -/
theorem Preconnected.cyclicDarts_subset_coreDarts (h : Γ.Preconnected) (v : Γ.V) :
    Γ.cyclicDarts ⊆ Γ.coreDarts v := by
  rintro e ⟨a, c, hc, he⟩
  obtain ⟨q⟩ := (Γ.preconnected_iff.mp h) v a
  exact hc.mem_coreDarts q he

/-- In a preconnected graph the based core at a vertex on a cyclically reduced closed path
consists of the darts on cyclically reduced closed paths. -/
theorem Preconnected.coreDarts_eq_cyclicDarts (h : Γ.Preconnected) {a : Γ.V}
    (ha : a ∈ Γ.cyclicVertices) : Γ.coreDarts a = Γ.cyclicDarts :=
  Set.Subset.antisymm (fun e he => by
    obtain ⟨p, hp, he⟩ := (Γ.mem_coreDarts_iff a e).mp he
    exact Γ.mem_cyclicDarts_of_isReduced ha ha hp he) (h.cyclicDarts_subset_coreDarts a)

/-- In a preconnected graph the vertices of the based core at a vertex on a cyclically reduced
closed path are the vertices on such paths. -/
theorem Preconnected.coreVertices_eq_cyclicVertices (h : Γ.Preconnected) {a : Γ.V}
    (ha : a ∈ Γ.cyclicVertices) : Γ.coreVertices a = Γ.cyclicVertices := by
  ext b
  rw [mem_coreVertices_iff, h.coreDarts_eq_cyclicDarts ha, mem_cyclicVertices_iff_exists_src]
  exact ⟨fun hb => hb.elim (fun hba => hba ▸ (Γ.mem_cyclicVertices_iff_exists_src a).mp ha) id,
    Or.inr⟩

/-- In a preconnected graph every vertex on a cyclically reduced closed path lies in the based
core at every vertex. -/
theorem Preconnected.cyclicVertices_subset_coreVertices (h : Γ.Preconnected) (v : Γ.V) :
    Γ.cyclicVertices ⊆ Γ.coreVertices v := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (Γ.mem_cyclicVertices_iff_exists_src a).mp ha
  exact Γ.src_mem_coreVertices v (h.cyclicDarts_subset_coreDarts v he)

/-- A preconnected graph is acyclic exactly when its based cores are. -/
theorem Preconnected.isAcyclic_core_iff (h : Γ.Preconnected) (v : Γ.V) :
    (Γ.core v).IsAcyclic ↔ Γ.IsAcyclic := by
  rw [← cyclicVertices_eq_empty_iff, ← cyclicVertices_eq_empty_iff,
    Set.eq_empty_iff_forall_notMem, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun hc a ha => hc ⟨a, h.cyclicVertices_subset_coreVertices v ha⟩
    ((Γ.mem_cyclicVertices_core_iff v _).mpr ha),
    fun hc a ha => hc a.1 ((Γ.mem_cyclicVertices_core_iff v a).mp ha)⟩

/-- An acyclic graph has no dart on a cyclically reduced closed path. -/
theorem IsAcyclic.cyclicDarts_eq_empty (h : Γ.IsAcyclic) : Γ.cyclicDarts = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ he =>
    (Γ.cyclicVertices_eq_empty_iff.mpr h ▸ Γ.src_mem_cyclicVertices he : _ ∈ (∅ : Set Γ.V))

/-- If the base vertex of a core lies on a cyclically reduced closed path, so does every dart. -/
theorem IsCore.cyclicDarts_eq_univ {v : Γ.V} (hΓ : Γ.IsCore v) (hv : v ∈ Γ.cyclicVertices) :
    Γ.cyclicDarts = Set.univ := by
  rw [← (Γ.connected_iff.mp hΓ.connected).2.coreDarts_eq_cyclicDarts hv]
  exact Set.eq_univ_of_forall fun e => (Γ.mem_coreDarts_iff v e).mpr (((Γ.isCore_iff v).mp hΓ).2 e)

/-- If the base vertex of a core lies on a cyclically reduced closed path, so does every
vertex. -/
theorem IsCore.cyclicVertices_eq_univ {v : Γ.V} (hΓ : Γ.IsCore v) (hv : v ∈ Γ.cyclicVertices) :
    Γ.cyclicVertices = Set.univ := by
  refine Set.eq_univ_of_forall fun a => ?_
  obtain ⟨p⟩ := ((Γ.isCore_iff v).mp hΓ).1 a
  cases p with
  | nil => exact hv
  | cons p e =>
    have he : e.1 ∈ Γ.cyclicDarts := hΓ.cyclicDarts_eq_univ hv ▸ Set.mem_univ e.1
    exact e.2.2 ▸ Γ.tgt_mem_cyclicVertices he

/-- An acyclic core has no darts: each dart would lie on a nonempty reduced loop. -/
theorem IsCore.isEmpty_of_isAcyclic {v : Γ.V} (hΓ : Γ.IsCore v) (h : Γ.IsAcyclic) :
    IsEmpty Γ.E := by
  refine ⟨fun e => ?_⟩
  obtain ⟨p, hp, he⟩ := ((Γ.isCore_iff v).mp hΓ).2 e
  rw [Γ.isAcyclic_iff.mp h v p hp] at he
  simp at he

/-- An acyclic core consists of its base vertex alone. -/
theorem IsCore.eq_of_isAcyclic {v : Γ.V} (hΓ : Γ.IsCore v) (h : Γ.IsAcyclic) (a : Γ.V) :
    a = v := by
  obtain ⟨p⟩ := ((Γ.isCore_iff v).mp hΓ).1 a
  cases p with
  | nil => rfl
  | cons _ e => exact (hΓ.isEmpty_of_isAcyclic h).elim e.1

/-- If the base vertex of a core is on no cyclically reduced closed path, each dart leaving it
begins a reduced closed path at the base that returns along the reverse of that dart. -/
private theorem IsCore.exists_isReduced_head?_getLast? {v : Γ.V} (hΓ : Γ.IsCore v)
    (hv : v ∉ Γ.cyclicVertices) {e : Γ.E} (he : Γ.src e = v) :
    ∃ p : Γ.Path v v, Path.IsReduced Γ p ∧ (Path.darts Γ p).head? = some e ∧
      (Path.darts Γ p).getLast? = some (Γ.rev e) := by
  subst he
  obtain ⟨p, hp, he⟩ := ((Γ.isCore_iff _).mp hΓ).2 e
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  have hred : Path.IsReduced Γ ((Γ.dart e).toPath.comp r) := by
    rw [Path.isReduced_iff_isChain] at hp ⊢
    exact hp.suffix ⟨Path.darts Γ q, by simp⟩
  refine ⟨_, hred, by simp, ?_⟩
  -- The closed path is not cyclically reduced, so its last dart reverses its first.
  obtain ⟨g, hg, hf⟩ := hred.exists_getLast?_rev_mem_head? Γ fun hc =>
    hv ⟨_, by simp [Quiver.Path.length_comp], hc⟩
  obtain rfl : e = Γ.rev g := by simpa [eq_comm] using hf
  simpa using hg

/-- The base vertex of a core lies on a cyclically reduced closed path as soon as two distinct
darts leave it. -/
theorem IsCore.mem_cyclicVertices_of_ne {v : Γ.V} (hΓ : Γ.IsCore v) {e f : Γ.E}
    (he : Γ.src e = v) (hf : Γ.src f = v) (hef : e ≠ f) : v ∈ Γ.cyclicVertices := by
  by_contra hv
  obtain ⟨p, hp, hp1, hp2⟩ := hΓ.exists_isReduced_head?_getLast? hv he
  obtain ⟨q, hq, hq1, hq2⟩ := hΓ.exists_isReduced_head?_getLast? hv hf
  have hp0 : Path.darts Γ p ≠ [] := fun h => by simp [h] at hp1
  have hq0 : Path.darts Γ q ≠ [] := fun h => by simp [h] at hq1
  -- Leaving along `e` and then along `f` gives a cyclically reduced closed path at the base.
  refine hv ⟨p.comp q, ?_, ?_⟩
  · rw [← Path.length_darts, Path.darts_comp, List.length_append]
    exact Nat.add_pos_left (List.length_pos_iff.mpr hp0) _
  · have hpq : Path.IsReduced Γ (p.comp q) := by
      refine (Path.isReduced_comp_iff Γ p q).mpr ⟨hp, hq, fun x hx y hy => ?_⟩
      obtain rfl : Γ.rev e = x := by simpa [hp2] using hx
      obtain rfl : f = y := by simpa [hq1] using hy
      simpa using hef.symm
    refine (Path.isReduced_comp_iff Γ _ _).mpr ⟨hpq, hpq, fun x hx y hy => ?_⟩
    rw [Path.darts_comp, List.getLast?_append_of_ne_nil _ hq0, hq2] at hx
    rw [Path.darts_comp, List.head?_append_of_ne_nil _ hp0, hp1] at hy
    obtain rfl : Γ.rev f = x := by simpa using hx
    obtain rfl : e = y := by simpa using hy
    simpa using hef

/-! ### The hanging path of a core -/

/-- Let `p` be a path from the base vertex of a core to a vertex on a cyclically reduced closed
path, all of whose darts start at vertices on no such path: the path hanging from the base vertex.
The darts on no cyclically reduced closed path are exactly the darts of `p` and their reverses. -/
theorem IsCore.notMem_cyclicDarts_iff {v w : Γ.V} (hΓ : Γ.IsCore v) {p : Γ.Path v w}
    (hw : w ∈ Γ.cyclicVertices) (hp : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) (e : Γ.E) :
    e ∉ Γ.cyclicDarts ↔ e ∈ Path.darts Γ p ∨ Γ.rev e ∈ Path.darts Γ p := by
  refine ⟨fun he => ?_, ?_⟩
  · have hcore : e ∈ Γ.coreDarts v := (Γ.mem_coreDarts_iff v e).mpr (((Γ.isCore_iff v).mp hΓ).2 e)
    rcases Γ.mem_coreDarts_or_mem_darts p.reverse hcore with h | h | h
    · rw [(Γ.connected_iff.mp hΓ.connected).2.coreDarts_eq_cyclicDarts hw] at h
      exact absurd h he
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ Path.darts Γ p, Γ.rev a = e := by simpa using h
      exact Or.inr (by simpa using ha)
    · obtain ⟨a, ha, hae⟩ : ∃ a ∈ Path.darts Γ p, Γ.rev a = Γ.rev e := by simpa using h
      exact Or.inl (Γ.rev_injective hae ▸ ha)
  · rintro (h | h) hc
    · exact hp e h (Γ.src_mem_cyclicVertices hc)
    · exact hp _ h (Γ.src_mem_cyclicVertices ((Γ.rev_mem_cyclicDarts_iff e).mpr hc))

/-- Let `p` be a path from the base vertex of a core to a vertex on a cyclically reduced closed
path, all of whose darts start at vertices on no such path: the path hanging from the base vertex.
The vertices on no cyclically reduced closed path are exactly the vertices of `p` other than its
end, that is, the origins of its darts. -/
theorem IsCore.notMem_cyclicVertices_iff {v w : Γ.V} (hΓ : Γ.IsCore v) {p : Γ.Path v w}
    (hw : w ∈ Γ.cyclicVertices) (hp : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) (a : Γ.V) :
    a ∉ Γ.cyclicVertices ↔ ∃ e ∈ Path.darts Γ p, Γ.src e = a := by
  refine ⟨fun ha => ?_, fun ⟨e, he, hea⟩ => hea ▸ hp e he⟩
  -- Every vertex of `p` other than its end is the origin of a dart of `p`.
  have key : ∀ {b} (r : Γ.Path b w), (∀ e ∈ Path.darts Γ r, e ∈ Path.darts Γ p) → b ≠ w →
      ∃ e ∈ Path.darts Γ p, Γ.src e = b := fun r hr hb => by
    obtain ⟨e, l, hl⟩ := List.exists_cons_of_ne_nil (Path.darts_ne_nil Γ
      (Nat.pos_of_ne_zero fun h0 => hb (r.eq_of_length_zero h0)))
    exact ⟨e, hr e (by simp [hl]), Path.src_eq_of_mem_head?_darts Γ r (by simp [hl])⟩
  have hne : a ≠ w := fun h => ha (h ▸ hw)
  obtain ⟨q⟩ := ((Γ.isCore_iff v).mp hΓ).1 a
  cases q with
  | nil => exact key p (fun _ => id) hne
  | cons q f =>
    obtain ⟨g, -, rfl⟩ := f
    have hg : Γ.rev g ∉ Γ.cyclicDarts := fun h => ha (by simpa using Γ.src_mem_cyclicVertices h)
    rcases (IsCore.notMem_cyclicDarts_iff hΓ hw hp _).mp hg with h | h
    · exact ⟨_, h, Γ.src_rev g⟩
    · obtain ⟨q', r, hpr⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p (by simpa using h)
      exact key r (fun e he => by simp [hpr, he]) hne

/-! ### Degrees along the hanging path -/

/-- A vertex on a nonempty cyclically reduced closed path has two distinct outgoing darts on
cyclically reduced closed paths: the first dart of such a path and the reverse of its last. -/
private theorem exists_cyclicDarts_ne {a : Γ.V} (ha : a ∈ Γ.cyclicVertices) :
    ∃ x y, x ∈ Γ.cyclicDarts ∧ y ∈ Γ.cyclicDarts ∧ Γ.src x = a ∧ Γ.src y = a ∧ x ≠ y := by
  obtain ⟨p, h0, hp⟩ := ha
  have hne := Path.darts_ne_nil Γ h0
  have hx : (Path.darts Γ p).head hne ∈ (Path.darts Γ p).head? := by
    simp [List.head?_eq_some_head hne]
  have hz : (Path.darts Γ p).getLast hne ∈ (Path.darts Γ p).getLast? := by
    simp [List.getLast?_eq_some_getLast hne]
  refine ⟨_, Γ.rev ((Path.darts Γ p).getLast hne), ⟨a, p, hp, List.head_mem hne⟩,
    (Γ.rev_mem_cyclicDarts_iff _).mpr ⟨a, p, hp, List.getLast_mem hne⟩,
    Path.src_eq_of_mem_head?_darts Γ p hx, ?_, ?_⟩
  · rw [src_rev]
    exact Path.tgt_eq_of_mem_getLast?_darts Γ p hz
  · -- Going around `p` twice, its last dart is not followed by its reverse.
    exact ((Path.isReduced_comp_iff Γ p p).mp hp).2.2 _ hz _ hx

/-- A vertex on a nonempty cyclically reduced closed path has degree at least two. -/
theorem two_le_degree_of_mem_cyclicVertices {a : Γ.V} (ha : a ∈ Γ.cyclicVertices) :
    2 ≤ Γ.degree a := by
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ := exists_cyclicDarts_ne ha
  exact two_le_degree_iff.mpr ⟨x, y, hx, hy, hxy⟩

/-- A vertex on a nonempty cyclically reduced closed path that is reached by a dart on no such
path has degree at least three. -/
theorem three_le_degree_tgt_of_notMem_cyclicDarts {e : Γ.E} (he : e ∉ Γ.cyclicDarts)
    (h : Γ.tgt e ∈ Γ.cyclicVertices) : 3 ≤ Γ.degree (Γ.tgt e) := by
  obtain ⟨x, y, hxC, hyC, hx, hy, hxy⟩ := exists_cyclicDarts_ne h
  have he' : Γ.rev e ∉ Γ.cyclicDarts := by rwa [rev_mem_cyclicDarts_iff]
  exact three_le_degree_iff.mpr ⟨x, y, Γ.rev e, hx, hy, Γ.src_rev e, hxy,
    fun h => he' (h ▸ hxC), fun h => he' (h ▸ hyC)⟩

/-- At a vertex on no cyclically reduced closed path, at most one dart of the based core at that
vertex leaves it. -/
private theorem eq_of_mem_coreDarts {a : Γ.V} (ha : a ∉ Γ.cyclicVertices) {x y : Γ.E}
    (hx : x ∈ Γ.coreDarts a) (hy : y ∈ Γ.coreDarts a) (hxa : Γ.src x = a) (hya : Γ.src y = a) :
    x = y := by
  by_contra hxy
  refine ha ((mem_cyclicVertices_core_iff a (Γ.coreBase a)).mp ?_)
  exact (Γ.core_isCore a).mem_cyclicVertices_of_ne (e := ⟨x, hx⟩) (f := ⟨y, hy⟩)
    (Subtype.ext hxa) (Subtype.ext hya) fun h => hxy (congrArg Subtype.val h)

/-- In a core, a vertex on no cyclically reduced closed path has degree at most two. -/
theorem IsCore.degree_le_two {v a : Γ.V} (hΓ : Γ.IsCore v) (ha : a ∉ Γ.cyclicVertices) :
    Γ.degree a ≤ 2 := by
  obtain ⟨p⟩ := ((Γ.isCore_iff v).mp hΓ).1 a
  obtain ⟨r, hr⟩ := exists_length_eq_dist ⟨p.reverse⟩
  -- A dart leaving `a` lies in the core at `a` or is the first dart of a shortest path to `v`.
  have key : ∀ x, Γ.src x = a → x ∈ Γ.coreDarts a ∨ x ∈ (Path.darts Γ r).head? := fun x hxa =>
    (Γ.mem_coreDarts_or_mem_darts r
      ((Γ.mem_coreDarts_iff v x).mpr (((Γ.isCore_iff v).mp hΓ).2 x))).imp_right fun h =>
        h.elim (Path.mem_head?_darts_of_length_le_dist hr.le · hxa) fun h =>
          (Path.tgt_ne_of_length_le_dist hr.le h (by rw [tgt_rev, hxa])).elim
  by_contra h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    three_le_degree_iff.mp (Order.add_one_le_of_lt (not_le.mp h))
  rcases key x hx with hx' | hx' <;> rcases key y hy with hy' | hy' <;>
    rcases key z hz with hz' | hz'
  all_goals first
    | exact hxy (eq_of_mem_coreDarts ha hx' hy' hx hy)
    | exact hxz (eq_of_mem_coreDarts ha hx' hz' hx hz)
    | exact hyz (eq_of_mem_coreDarts ha hy' hz' hy hz)
    | exact hxy (Option.mem_unique hx' hy')
    | exact hxz (Option.mem_unique hx' hz')
    | exact hyz (Option.mem_unique hy' hz')

/-- In a core, a vertex of degree at least three lies on a cyclically reduced closed path. -/
theorem IsCore.mem_cyclicVertices_of_three_le_degree {v a : Γ.V} (hΓ : Γ.IsCore v)
    (ha : 3 ≤ Γ.degree a) : a ∈ Γ.cyclicVertices := by
  by_contra h
  exact absurd (ha.trans (hΓ.degree_le_two h)) (by decide)

/-- In a core, every vertex other than the base vertex has degree at least two. -/
theorem IsCore.two_le_degree {v a : Γ.V} (hΓ : Γ.IsCore v) (ha : a ≠ v) : 2 ≤ Γ.degree a := by
  obtain ⟨p⟩ := ((Γ.isCore_iff v).mp hΓ).1 a
  cases p with
  | nil => exact absurd rfl ha
  | cons p g =>
    obtain ⟨g, -, rfl⟩ := g
    obtain ⟨f, hf, hfg⟩ := IsCore.exists_outgoing_ne Γ v hΓ (Γ.rev g) (by simpa using ha)
    exact two_le_degree_iff.mpr ⟨f, Γ.rev g, by simpa using hf, by simp, hfg⟩

/-- In a core, a vertex other than the base vertex on no cyclically reduced closed path has
degree two. -/
theorem IsCore.degree_eq_two {v a : Γ.V} (hΓ : Γ.IsCore v) (ha : a ∉ Γ.cyclicVertices)
    (hav : a ≠ v) : Γ.degree a = 2 :=
  (hΓ.degree_le_two ha).antisymm (hΓ.two_le_degree hav)

/-- The base vertex of a core has degree at least two exactly when it lies on a cyclically
reduced closed path. -/
theorem IsCore.two_le_degree_iff_mem_cyclicVertices {v : Γ.V} (hΓ : Γ.IsCore v) :
    2 ≤ Γ.degree v ↔ v ∈ Γ.cyclicVertices := by
  refine ⟨fun h => ?_, two_le_degree_of_mem_cyclicVertices⟩
  obtain ⟨e, f, he, hf, hef⟩ := two_le_degree_iff.mp h
  exact hΓ.mem_cyclicVertices_of_ne he hf hef

/-- The base vertex of a core has degree zero exactly when the core is acyclic, that is, when it
is the base vertex alone. -/
theorem IsCore.degree_eq_zero_iff_isAcyclic {v : Γ.V} (hΓ : Γ.IsCore v) :
    Γ.degree v = 0 ↔ Γ.IsAcyclic := by
  refine ⟨fun h => ?_, fun h => degree_eq_zero_iff.mpr fun e =>
    (hΓ.isEmpty_of_isAcyclic h).elim e⟩
  -- Each dart lies on a reduced closed path at `v`, whose first dart would leave `v`.
  have hE : IsEmpty Γ.E := ⟨fun e => by
    obtain ⟨p, -, he⟩ := ((Γ.isCore_iff v).mp hΓ).2 e
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (List.isSome_head?.mpr (List.ne_nil_of_mem he))
    exact degree_eq_zero_iff.mp h x (Path.src_eq_of_mem_head?_darts Γ p hx)⟩
  refine Γ.isAcyclic_iff.mpr fun u p _ => ?_
  cases p with
  | nil => rfl
  | cons _ e => exact isEmptyElim e.1

/-- A path starting at a vertex on no cyclically reduced closed path, which leaves only from
vertices of degree at most two after its start, never leaves from a vertex on a cyclically
reduced closed path: it could only enter such a vertex through a dart on no such path, and the
vertex would then have degree at least three. -/
theorem src_notMem_cyclicVertices_of_degree_le_two {v w : Γ.V} {q : Γ.Path v w}
    (hv : v ∉ Γ.cyclicVertices) (hq : ∀ e ∈ Path.darts Γ q, Γ.src e ≠ v → Γ.degree (Γ.src e) ≤ 2)
    {e : Γ.E} (he : e ∈ Path.darts Γ q) : Γ.src e ∉ Γ.cyclicVertices := by
  induction q generalizing e with
  | nil => simp at he
  | cons q f ih =>
    have ih' : ∀ e ∈ Path.darts Γ q, Γ.src e ∉ Γ.cyclicVertices := fun e he =>
      ih (fun e' he' => hq e' (by simp [he'])) he
    rcases (by simpa using he : e ∈ Path.darts Γ q ∨ e = f.1) with he | rfl
    · exact ih' e he
    cases q with
    | nil => simpa [f.2.1] using hv
    | cons q g =>
      intro hf
      have hg : g.1 ∉ Γ.cyclicDarts := fun h => ih' g.1 (by simp) (Γ.src_mem_cyclicVertices h)
      have h3 := three_le_degree_tgt_of_notMem_cyclicDarts hg (by rwa [g.2.2, ← f.2.1])
      rw [g.2.2, ← f.2.1] at h3
      exact absurd (h3.trans (hq f.1 (by simp) fun h => hv (h ▸ hf))) (by decide)

/-- **The hanging path in terms of degrees.** Let the base vertex of a core have degree at most
one, and let `q` be a path from it to the first vertex of degree at least three: every vertex
that `q` leaves, other than the base vertex, has degree at most two. The darts on no cyclically
reduced closed path are exactly the darts of `q` and their reverses. -/
theorem IsCore.notMem_cyclicDarts_iff_of_three_le_degree {v w : Γ.V} (hΓ : Γ.IsCore v)
    (hv : Γ.degree v ≤ 1) {q : Γ.Path v w}
    (hq : ∀ e ∈ Path.darts Γ q, Γ.src e ≠ v → Γ.degree (Γ.src e) ≤ 2) (hw : 3 ≤ Γ.degree w)
    (e : Γ.E) : e ∉ Γ.cyclicDarts ↔ e ∈ Path.darts Γ q ∨ Γ.rev e ∈ Path.darts Γ q := by
  have hvC : v ∉ Γ.cyclicVertices := fun h =>
    absurd ((hΓ.two_le_degree_iff_mem_cyclicVertices.mpr h).trans hv) (by decide)
  exact hΓ.notMem_cyclicDarts_iff (hΓ.mem_cyclicVertices_of_three_le_degree hw)
    (fun _ he => src_notMem_cyclicVertices_of_degree_le_two hvC hq he) e

/-- In a core that is not acyclic, a shortest path from the base vertex to a nearest vertex on a
cyclically reduced closed path leaves only from vertices on no such path. -/
private theorem IsCore.exists_hanging_geodesic {v : Γ.V} (hΓ : Γ.IsCore v) (h : ¬ Γ.IsAcyclic) :
    ∃ w ∈ Γ.cyclicVertices, ∃ p : Γ.Path v w, p.length = Γ.dist v w ∧
      ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices := by
  obtain ⟨w, hw, hmin⟩ := exists_forall_dist_le
    (Set.nonempty_iff_ne_empty.mpr (mt Γ.cyclicVertices_eq_empty_iff.mp h)) v
  obtain ⟨p, hp⟩ := exists_length_eq_dist (((Γ.isCore_iff v).mp hΓ).1 w)
  exact ⟨w, hw, p, hp, fun e he => Path.src_notMem_of_forall_dist_le hmin hp.le he⟩

/-- A path from a vertex on no cyclically reduced closed path to a vertex on one, leaving only
from vertices on no such path, ends at a vertex of degree at least three. -/
private theorem three_le_degree_of_forall_src_notMem {v w : Γ.V} (p : Γ.Path v w)
    (hv : v ∉ Γ.cyclicVertices) (hw : w ∈ Γ.cyclicVertices)
    (hp : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) : 3 ≤ Γ.degree w := by
  cases p with
  | nil => exact absurd hw hv
  | cons p g =>
    have hg : g.1 ∉ Γ.cyclicDarts := fun h => hp g.1 (by simp) (Γ.src_mem_cyclicVertices h)
    simpa [g.2.2] using three_le_degree_tgt_of_notMem_cyclicDarts hg (by rwa [g.2.2])

/-- A dart of a path leaving only from vertices on no cyclically reduced closed path that ends at
a vertex on such a path is the last dart of the path. -/
private theorem tgt_eq_of_mem_darts {v w : Γ.V} {p : Γ.Path v w}
    (hp : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) {g : Γ.E} (hg : g ∈ Path.darts Γ p)
    (hgC : Γ.tgt g ∈ Γ.cyclicVertices) : Γ.tgt g = w := by
  obtain ⟨p₁, p₂, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p hg
  rcases Nat.eq_zero_or_pos p₂.length with h0 | h0
  · exact p₂.eq_of_length_zero h0
  obtain ⟨c, f, p₃, -, rfl⟩ :=
    p₂.eq_toPath_comp_of_length_eq_succ (Nat.succ_pred_eq_of_pos h0).symm
  exact (hp f.1 (by simp) (by rwa [f.2.1])).elim

/-- In a core, two darts leaving a vertex `b` on no cyclically reduced closed path coincide if
neither reverses the last dart of a path from the base vertex to `b`. -/
private theorem IsCore.eq_of_src_eq {v b : Γ.V} (hΓ : Γ.IsCore v) (hb : b ∉ Γ.cyclicVertices)
    (q : Γ.Path v b) {e f : Γ.E} (he : Γ.src e = b) (hf : Γ.src f = b)
    (hqe : ∀ g ∈ (Path.darts Γ q).getLast?, e ≠ Γ.rev g)
    (hqf : ∀ g ∈ (Path.darts Γ q).getLast?, f ≠ Γ.rev g) : e = f := by
  cases q with
  | nil =>
    have h1 : Γ.degree v ≤ 1 := Order.le_of_lt_add_one (lt_of_not_ge
      (mt hΓ.two_le_degree_iff_mem_cyclicVertices.mp hb))
    exact degree_le_one_iff.mp h1 _ _ he hf
  | cons q g =>
    -- Otherwise `e`, `f` and the reverse of the last dart `g` are three darts leaving `b`.
    by_contra hne
    exact hb (hΓ.mem_cyclicVertices_of_three_le_degree (three_le_degree_iff.mpr ⟨e, f,
      Γ.rev g.1, he, hf, by simpa using g.2.2, hne, hqe g.1 (by simp), hqf g.1 (by simp)⟩))

/-- Let `p` be a reduced path from the base vertex of a core, leaving only from vertices on no
cyclically reduced closed path. Every reduced path from the base vertex is an initial piece of
`p` or extends `p`: at the vertices that `p` leaves, of degree at most two, a reduced path has no
choice. -/
private theorem IsCore.prefix_or_prefix {v w : Γ.V} (hΓ : Γ.IsCore v) {p : Γ.Path v w}
    (hp : Path.IsReduced Γ p) (hpC : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) {a : Γ.V}
    {q : Γ.Path v a} (hq : Path.IsReduced Γ q) :
    (∃ s : Γ.Path a w, p = q.comp s) ∨ ∃ s : Γ.Path w a, q = p.comp s := by
  induction q with
  | nil => exact Or.inl ⟨p, (Quiver.Path.nil_comp p).symm⟩
  | @cons b d q e ih =>
    rcases ih (hq.of_cons Γ) with ⟨s, rfl⟩ | ⟨s, rfl⟩
    swap
    · exact Or.inr ⟨s.cons e, rfl⟩
    rcases Nat.eq_zero_or_pos s.length with h0 | h0
    · obtain rfl := s.eq_of_length_zero h0
      obtain rfl := Quiver.Path.eq_nil_of_length_zero s h0
      exact Or.inr ⟨e.toPath, rfl⟩
    -- The next darts `e` of `q` and `f` of `p` leave `b`, on no cyclically reduced closed path.
    obtain ⟨c, f, s', -, rfl⟩ :=
      s.eq_toPath_comp_of_length_eq_succ (Nat.succ_pred_eq_of_pos h0).symm
    have hef : e.1 = f.1 := hΓ.eq_of_src_eq (by simpa [f.2.1] using hpC f.1 (by simp)) q e.2.1
      f.2.1 (fun g hg => ((Path.isReduced_comp_iff Γ q e.toPath).mp hq).2.2 g hg e.1 (by simp))
      fun g hg => ((Path.isReduced_comp_iff Γ _ _).mp hp).2.2 g hg f.1 (by simp)
    obtain ⟨e, he, rfl⟩ := e
    obtain ⟨f, hf, rfl⟩ := f
    obtain rfl : e = f := hef
    exact Or.inl ⟨s', by rw [← Quiver.Path.comp_assoc]; rfl⟩

/-- In a core whose base vertex is on no cyclically reduced closed path, two paths from the base
vertex to vertices on such paths, leaving only from vertices on no such path, have the same end. -/
private theorem IsCore.eq_of_forall_src_notMem {v w w' : Γ.V} (hΓ : Γ.IsCore v)
    (hv : v ∉ Γ.cyclicVertices) {p : Γ.Path v w} (hw : w ∈ Γ.cyclicVertices)
    (hp : ∀ e ∈ Path.darts Γ p, Γ.src e ∉ Γ.cyclicVertices) (q : Γ.Path v w')
    (hw' : w' ∈ Γ.cyclicVertices) (hq : ∀ e ∈ Path.darts Γ q, Γ.src e ∉ Γ.cyclicVertices) :
    w' = w := by
  -- The last dart of `q` is on no cyclically reduced closed path, so it is the last dart of `p`.
  cases q with
  | nil => exact absurd hw' hv
  | cons q g =>
    have hg : g.1 ∉ Γ.cyclicDarts := fun h => hq g.1 (by simp) (Γ.src_mem_cyclicVertices h)
    rcases (hΓ.notMem_cyclicDarts_iff hw hp g.1).mp hg with h | h
    · rw [← g.2.2]
      exact tgt_eq_of_mem_darts hp h (by rwa [g.2.2])
    · exact (hp _ h (by rwa [src_rev, g.2.2])).elim

/-- **The end of the hanging path.** If the base vertex `v` of a core has degree one, there is a
unique vertex `w` such that there is a unique shortest path from `v` to `w`, every vertex of this
path other than `v` and `w` has degree two, and `w` has degree at least three. -/
theorem IsCore.existsUnique_three_le_degree {v : Γ.V} (hΓ : Γ.IsCore v) (hv : Γ.degree v = 1) :
    ∃! w : Γ.V, (∃! p : Γ.Path v w, p.length = Γ.dist v w) ∧
      (∀ p : Γ.Path v w, p.length = Γ.dist v w →
        ∀ e ∈ Path.darts Γ p, Γ.src e ≠ v → Γ.degree (Γ.src e) = 2) ∧ 3 ≤ Γ.degree w := by
  have hvC : v ∉ Γ.cyclicVertices := fun h =>
    absurd (hΓ.two_le_degree_iff_mem_cyclicVertices.mpr h) (by rw [hv]; decide)
  have hac : ¬ Γ.IsAcyclic := fun h =>
    one_ne_zero (hv.symm.trans (hΓ.degree_eq_zero_iff_isAcyclic.mpr h))
  obtain ⟨w, hw, p, hp, hpC⟩ := hΓ.exists_hanging_geodesic hac
  -- Every shortest path from `v` to `w` is `p`: one of them extends the other by a closed path.
  have huniq : ∀ q : Γ.Path v w, q.length = Γ.dist v w → q = p := fun q hq => by
    rcases hΓ.prefix_or_prefix (Path.isReduced_of_length_le_dist hp.le) hpC
        (Path.isReduced_of_length_le_dist hq.le) with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [Quiver.Path.length_comp] at hp
      rw [Quiver.Path.eq_nil_of_length_zero s (by lia), Quiver.Path.comp_nil]
    · rw [Quiver.Path.length_comp] at hq
      rw [Quiver.Path.eq_nil_of_length_zero s (by lia), Quiver.Path.comp_nil]
  refine ⟨w, ⟨⟨p, hp, huniq⟩, fun q hq e he hev => ?_,
    three_le_degree_of_forall_src_notMem p hvC hw hpC⟩, ?_⟩
  · rw [huniq q hq] at he
    exact hΓ.degree_eq_two (hpC e he) hev
  rintro w' ⟨⟨q, hq, -⟩, hint, h3⟩
  exact hΓ.eq_of_forall_src_notMem hvC hw hpC q (hΓ.mem_cyclicVertices_of_three_le_degree h3)
    fun e he => src_notMem_cyclicVertices_of_degree_le_two hvC
      (fun e he hev => (hint q hq e he hev).le) he

/-- A rose petal is cyclically reduced: going around it twice does not backtrack. -/
theorem rosePetal_isCyclicallyReduced {α : Type*} (a : α) :
    Path.IsCyclicallyReduced (rose α) (rosePetal a) :=
  (Path.isCyclicallyReduced_iff (rose α) (rosePetal a)).mpr <| rosePetal_eq_toPath a ▸
    (Path.isReduced_cons_cons (rose α) .nil _ _).mpr ⟨Path.isReduced_toPath _ _, by simp [rose]⟩

/-- The vertex of a rose with at least one petal lies on a cyclically reduced closed path. -/
theorem rose_cyclicVertices {α : Type*} [Nonempty α] : (rose α).cyclicVertices = Set.univ := by
  refine Set.eq_univ_of_forall ?_
  rintro ⟨⟩
  exact ⟨rosePetal (Classical.arbitrary α), by rw [rosePetal_length]; exact Nat.one_pos,
    rosePetal_isCyclicallyReduced _⟩

end TauCeti.SerreGraph
