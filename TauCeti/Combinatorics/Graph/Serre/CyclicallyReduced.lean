/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Core
public import TauCeti.Combinatorics.Graph.Serre.Tree
public import TauCeti.Combinatorics.Quiver.Prefunctor

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
  a based core does not change the darts and vertices on cyclically reduced closed paths.

This is the graph-theoretic content of the type of a core graph, obtained from a based core by
deleting the path that hangs from the base vertex: for a core graph with at least one dart, the
type consists of the darts and vertices on cyclically reduced closed paths. The type of the
one-vertex graph is that vertex, which lies on no nonempty cyclically reduced closed path.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 7, Definition 7.3 and Remark 7.4.
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
  obtain ⟨q, rfl⟩ := Γ.exists_core_path v c
    (fun e he => hc.mem_coreDarts ((Γ.coreInclusion v).toPrefunctor.mapPath q₀) he) a.2 a.2
  exact ⟨q, ((Γ.coreInclusion v).isCyclicallyReduced_mapPath_iff _ Subtype.val_injective q).mp hc,
    rfl⟩

/-- A vertex of a based core lies on a cyclically reduced closed path of the core exactly when it
does so in the ambient graph. -/
theorem mem_cyclicVertices_core_iff (v : Γ.V) (a : (Γ.core v).V) :
    a ∈ (Γ.core v).cyclicVertices ↔ a.1 ∈ Γ.cyclicVertices := by
  refine ⟨(Γ.coreInclusion v).map_mem_cyclicVertices _ Subtype.val_injective, ?_⟩
  rintro ⟨c, h0, hc⟩
  obtain ⟨q, hq, rfl⟩ := hc.exists_core_path
  exact ⟨q, h0.trans_eq (Prefunctor.length_mapPath _ q), hq⟩

/-- A dart of a based core lies on a cyclically reduced closed path of the core exactly when it
does so in the ambient graph. -/
theorem mem_cyclicDarts_core_iff (v : Γ.V) (e : (Γ.core v).E) :
    e ∈ (Γ.core v).cyclicDarts ↔ e.1 ∈ Γ.cyclicDarts := by
  refine ⟨(Γ.coreInclusion v).map_mem_cyclicDarts _ Subtype.val_injective, ?_⟩
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
