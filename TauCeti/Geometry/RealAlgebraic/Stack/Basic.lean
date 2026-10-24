/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.Topology.Connected.Prod

/-!
# Sections and sectors of a stack

A finite family of functions `θ₀ < θ₁ < … < θₖ₋₁` on a base `X` cuts the cylinder `X × α` into a
*stack*: the `k` *sections*, which are the graphs of the `θᵢ`, and the `k + 1` open *sectors*
between consecutive graphs, the lowest and highest sectors being unbounded. These are the cells
built over a base cell when a cylindrical algebraic decomposition is lifted by one dimension.

This file develops the stack geometry for arbitrary functions, independently of the polynomials
whose roots they will be. Sector `j` is defined as the set of points lying above exactly the first
`j` sections. When the functions are ordered pointwise this is the region between section `j - 1`
and section `j`, and the sections and sectors partition the cylinder. For continuous, strictly
ordered functions on a connected base, each sector carries a continuous section, so every part
projects onto the whole base, and every section and sector of a real stack is connected. Finally
`TauCeti.cylinder` places the cylinder over a subset `S` of the coordinate space inside the
coordinate space of one more dimension, with the distinguished coordinate first; it is a
topological embedding, so connectedness of stack cells transfers to their ambient images, the
cells `TauCeti.stackCells` of the stack in the ambient space.

## Main declarations

* `TauCeti.sectionSet`, `TauCeti.sectorSet`: the sections and sectors of a stack.
* `TauCeti.mem_sectorSet_iff_of_monotone`: for ordered functions, a sector is cut out by the two
  adjacent sections.
* `TauCeti.iUnion_sectionSet_union_iUnion_sectorSet`, `TauCeti.pairwise_disjoint_sectionSet`,
  `TauCeti.pairwise_disjoint_sectorSet`, `TauCeti.disjoint_sectionSet_sectorSet`: the sections and
  sectors partition the cylinder.
* `TauCeti.sectionSet_nonempty`, `TauCeti.sectorSet_nonempty`: over a nonempty base, every section
  and every sector of a strictly ordered stack is nonempty.
* `TauCeti.sectorSet_castSucc_succ_eq_image`, `TauCeti.sectorSet_zero_eq_image`,
  `TauCeti.sectorSet_last_eq_image`: a bounded sector is the image of `X × (0, 1)`, and the lowest
  and highest sectors are the images of `X × (-∞, 0)` and `X × (0, ∞)`, under explicit maps that
  are continuous whenever the functions of the stack are, for a topological ring `α` (continuous
  addition suffices for the two unbounded sectors).
* `TauCeti.exists_continuous_forall_mem_sectorSet`: every sector of a continuous strictly ordered
  stack contains the graph of a continuous function.
* `TauCeti.isConnected_sectionSet`, `TauCeti.isConnected_sectorSet`: over a connected base, the
  sections and sectors of a continuous strictly ordered real stack are connected.
* `TauCeti.cylinder`, `TauCeti.isEmbedding_cylinder`: the ambient cylinder embedding.
* `TauCeti.stackCells`: the ambient sections and sectors of a stack over a subset of `α ^ n`.
* `TauCeti.image_cylinder_sectionSet_comp`, `TauCeti.image_cylinder_sectorSet_comp`,
  `TauCeti.stackCells_comp`: ambient stack cells pull back along arbitrary base maps.
* `TauCeti.stackCells_inclusion`: restricting a stack to a subset of its base cuts each ambient
  cell down to the part lying over that subset.
* `TauCeti.sUnion_stackCells`, `TauCeti.pairwiseDisjoint_stackCells`,
  `TauCeti.isConnected_of_mem_stackCells`: the ambient cells of a stack partition the cylinder
  over its base, and over a connected base they are connected.
* `TauCeti.ordConnected_setOf_cons_mem_of_mem_stackCells`: every ambient cell meets each line
  parallel to the distinguished axis in an order-connected set.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Function Set Topology

namespace TauCeti

variable {X Y α : Type*} {k : ℕ}

/-! ### Sections and sectors -/

section Order

/-- The `i`-th section of the stack defined by `θ`: the graph `Function.graph (θ i)` of `θ i`
in the cylinder `X × α`. -/
def sectionSet (θ : Fin k → X → α) (i : Fin k) : Set (X × α) :=
  (θ i).graph

@[simp]
theorem mem_sectionSet {θ : Fin k → X → α} {i : Fin k} {z : X × α} :
    z ∈ sectionSet θ i ↔ θ i z.1 = z.2 :=
  Iff.rfl

/-- A section is the range of the graph map of its function. -/
theorem sectionSet_eq_range (θ : Fin k → X → α) (i : Fin k) :
    sectionSet θ i = range fun x ↦ (x, θ i x) := by
  ext ⟨x, t⟩
  simp

/-- Sections pull back along a change of base. -/
theorem sectionSet_comp (θ : Fin k → X → α) (f : Y → X) (i : Fin k) :
    sectionSet (fun i ↦ θ i ∘ f) i = Prod.map f id ⁻¹' sectionSet θ i :=
  (rfl)

/-- Each section lies over the whole base. -/
@[simp]
theorem fst_image_sectionSet (θ : Fin k → X → α) (i : Fin k) :
    Prod.fst '' sectionSet θ i = univ :=
  eq_univ_of_forall fun x ↦ ⟨(x, θ i x), rfl, rfl⟩

/-- Over a nonempty base, every section is nonempty. -/
@[simp]
theorem sectionSet_nonempty [Nonempty X] (θ : Fin k → X → α) (i : Fin k) :
    (sectionSet θ i).Nonempty := by
  rw [← image_nonempty (f := Prod.fst), fst_image_sectionSet]
  exact univ_nonempty

/-- Distinct sections of a stack whose functions are pointwise injective in the index are
disjoint. -/
theorem pairwise_disjoint_sectionSet {θ : Fin k → X → α}
    (hθ : ∀ x, Injective fun i ↦ θ i x) : Pairwise (Disjoint on sectionSet θ) := by
  refine fun i i' hii' ↦ disjoint_left.2 fun z hz hz' ↦ hii' (hθ z.1 ?_)
  simp only [mem_sectionSet] at hz hz'
  exact hz.trans hz'.symm

variable [LinearOrder α] {θ : Fin k → X → α}

/-- The `j`-th sector of the stack defined by `θ`, for `j ≤ k`: the points of `X × α` lying
strictly above the first `j` sections and strictly below the others. When there are no sections
the only sector is the whole cylinder. -/
def sectorSet (θ : Fin k → X → α) (j : Fin (k + 1)) : Set (X × α) :=
  {z | (∀ i : Fin k, i.castSucc < j → θ i z.1 < z.2) ∧
    ∀ i : Fin k, j ≤ i.castSucc → z.2 < θ i z.1}

@[simp]
theorem mem_sectorSet {j : Fin (k + 1)} {z : X × α} :
    z ∈ sectorSet θ j ↔ (∀ i : Fin k, i.castSucc < j → θ i z.1 < z.2) ∧
      ∀ i : Fin k, j ≤ i.castSucc → z.2 < θ i z.1 :=
  Iff.rfl

/-- A stack with no sections has the whole cylinder as its unique sector. -/
@[simp]
theorem sectorSet_fin_zero (θ : Fin 0 → X → α) (j : Fin 1) : sectorSet θ j = univ := by
  ext z
  simp

/-- Sectors pull back along a change of base. -/
theorem sectorSet_comp (θ : Fin k → X → α) (f : Y → X) (j : Fin (k + 1)) :
    sectorSet (fun i ↦ θ i ∘ f) j = Prod.map f id ⁻¹' sectorSet θ j :=
  (rfl)

/-- Each fibre of a sector is order-connected: it is an open interval of `α`, possibly
unbounded. -/
theorem ordConnected_preimage_mk_sectorSet (θ : Fin k → X → α) (j : Fin (k + 1)) (x : X) :
    (Prod.mk x ⁻¹' sectorSet θ j).OrdConnected :=
  ⟨fun _ ha _ hb _ ht ↦ ⟨fun i hi ↦ (ha.1 i hi).trans_le ht.1,
    fun i hi ↦ ht.2.trans_lt (hb.2 i hi)⟩⟩

/-- For pointwise monotone `θ`, a point lies in sector `j` exactly when it is above section
`j - 1` (if `0 < j`) and below section `j` (if `j < k`). -/
theorem mem_sectorSet_iff_of_monotone (hθ : ∀ x, Monotone fun i ↦ θ i x) {j : Fin (k + 1)}
    {z : X × α} :
    z ∈ sectorSet θ j ↔ (∀ i : Fin k, i.succ = j → θ i z.1 < z.2) ∧
      ∀ i : Fin k, i.castSucc = j → z.2 < θ i z.1 := by
  refine ⟨fun h ↦ ⟨fun i hi ↦ h.1 i (hi ▸ Fin.castSucc_lt_succ), fun i hi ↦ h.2 i hi.ge⟩,
    fun h ↦ ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩⟩
  · -- The section just below sector `j` lies above section `i`.
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.ne_zero_of_lt hi)
    exact (hθ z.1 (Fin.castSucc_lt_succ_iff.1 hi)).trans_lt (h.1 j' rfl)
  · -- The section just above sector `j` lies below section `i`.
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 (hi.trans_lt (Fin.castSucc_lt_last i)).ne
    exact (h.2 j' rfl).trans_le (hθ z.1 (Fin.castSucc_le_castSucc_iff.1 hi))

/-- For pointwise monotone `θ`, the lowest sector lies below the lowest section. -/
theorem sectorSet_zero {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ 0 = {z | z.2 < θ 0 z.1} := by
  ext z
  rw [mem_sectorSet_iff_of_monotone hθ]
  exact ⟨fun h ↦ h.2 0 rfl, fun h ↦ ⟨fun i hi ↦ absurd hi (Fin.succ_ne_zero i),
    fun i hi ↦ by rwa [Fin.castSucc_eq_zero_iff.1 hi]⟩⟩

/-- For pointwise monotone `θ`, the highest sector lies above the highest section. -/
theorem sectorSet_last {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ (Fin.last (k + 1)) = {z | θ (Fin.last k) z.1 < z.2} := by
  ext z
  rw [mem_sectorSet_iff_of_monotone hθ]
  exact ⟨fun h ↦ h.1 _ (Fin.succ_last k), fun h ↦ ⟨fun i hi ↦ by rwa [Fin.succ_eq_last_succ.1 hi],
    fun i hi ↦ absurd hi (Fin.castSucc_ne_last i)⟩⟩

/-- For pointwise monotone `θ`, a bounded sector lies between two consecutive sections. -/
theorem sectorSet_castSucc_succ {θ : Fin (k + 1) → X → α} (hθ : ∀ x, Monotone fun i ↦ θ i x)
    (i : Fin k) :
    sectorSet θ i.castSucc.succ = {z | θ i.castSucc z.1 < z.2 ∧ z.2 < θ i.succ z.1} := by
  ext z
  rw [mem_sectorSet_iff_of_monotone hθ]
  refine ⟨fun h ↦ ⟨h.1 _ rfl, h.2 _ (Fin.succ_castSucc i).symm⟩,
    fun h ↦ ⟨fun i' hi ↦ ?_, fun i' hi ↦ ?_⟩⟩
  · rw [Fin.succ_inj.1 hi]
    exact h.1
  · rw [Fin.castSucc_inj.1 (hi.trans (Fin.succ_castSucc i))]
    exact h.2

/-- Distinct sectors of a stack are disjoint. -/
theorem pairwise_disjoint_sectorSet (θ : Fin k → X → α) :
    Pairwise (Disjoint on sectorSet θ) := by
  -- The section with the index of the lower sector separates the two sectors.
  suffices ∀ j j' : Fin (k + 1), j < j' → Disjoint (sectorSet θ j) (sectorSet θ j') from
    fun j j' h ↦ h.lt_or_gt.elim (this j j') fun h' ↦ (this j' j h').symm
  refine fun j j' hjj' ↦ disjoint_left.2 fun z hz hz' ↦ ?_
  let i : Fin k := ⟨j, by omega⟩
  exact (hz.2 i le_rfl).not_gt (hz'.1 i hjj')

/-- A section and a sector of a stack are disjoint. -/
theorem disjoint_sectionSet_sectorSet (θ : Fin k → X → α) (i : Fin k) (j : Fin (k + 1)) :
    Disjoint (sectionSet θ i) (sectorSet θ j) := by
  refine disjoint_left.2 fun z hz hz' ↦ ?_
  rw [mem_sectionSet] at hz
  rcases lt_or_ge i.castSucc j with h | h
  · exact (hz'.1 i h).ne hz
  · exact (hz'.2 i h).ne' hz

/-- For pointwise monotone `θ`, the sections and sectors cover the cylinder. -/
theorem iUnion_sectionSet_union_iUnion_sectorSet (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    (⋃ i, sectionSet θ i) ∪ ⋃ j, sectorSet θ j = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases hsec : ∃ i, θ i z.1 = z.2
  · obtain ⟨i, hi⟩ := hsec
    exact Or.inl (mem_iUnion.2 ⟨i, hi⟩)
  simp only [not_exists] at hsec
  refine Or.inr (mem_iUnion.2 ?_)
  by_cases habove : ∃ i, z.2 < θ i z.1
  · -- `z` lies in the sector just below the lowest section above it.
    have hne : (Finset.univ.filter fun i ↦ z.2 < θ i z.1).Nonempty := by
      obtain ⟨i, hi⟩ := habove
      exact ⟨i, by simpa using hi⟩
    let i₀ := (Finset.univ.filter fun i ↦ z.2 < θ i z.1).min' hne
    have hi₀ : z.2 < θ i₀ z.1 := by simpa using Finset.min'_mem _ hne
    refine ⟨i₀.castSucc, fun i hi ↦ ?_, fun i hi ↦ hi₀.trans_le (hθ z.1 (by simpa using hi))⟩
    refine lt_of_le_of_ne (not_lt.1 fun h ↦ ?_) (hsec i)
    exact (Fin.castSucc_lt_castSucc_iff.1 hi).not_ge
      (Finset.min'_le _ _ (by simpa using h))
  · -- `z` lies above every section.
    simp only [not_exists, not_lt] at habove
    exact ⟨Fin.last k, fun i _ ↦ lt_of_le_of_ne (habove i) (hsec i),
      fun i hi ↦ absurd hi (not_le.2 (Fin.castSucc_lt_last i))⟩

/-- For pointwise strictly monotone `θ` with values in a densely ordered type without endpoints,
each sector lies over the whole base. -/
theorem fst_image_sectorSet [Nonempty α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    Prod.fst '' sectorSet θ j = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  suffices ∃ t, (x, t) ∈ sectorSet θ j by
    obtain ⟨t, ht⟩ := this
    exact ⟨(x, t), ht, rfl⟩
  cases k with
  | zero => simp
  | succ k =>
    have hm : ∀ x, Monotone fun i ↦ θ i x := fun x ↦ (hθ x).monotone
    cases j using Fin.cases with
    | zero =>
      obtain ⟨t, ht⟩ := exists_lt (θ 0 x)
      exact ⟨t, by rw [sectorSet_zero hm]; exact ht⟩
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        obtain ⟨t, ht⟩ := exists_gt (θ (Fin.last k) x)
        exact ⟨t, by rw [Fin.succ_last, sectorSet_last hm]; exact ht⟩
      | cast i =>
        obtain ⟨t, ht⟩ := exists_between (hθ x i.castSucc_lt_succ)
        exact ⟨t, by rw [sectorSet_castSucc_succ hm]; exact ht⟩

/-- Over a nonempty base, every sector of a pointwise strictly monotone stack with values in a
densely ordered type without endpoints is nonempty. -/
theorem sectorSet_nonempty [Nonempty X] [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    (sectorSet θ j).Nonempty := by
  rw [← image_nonempty (f := Prod.fst), fst_image_sectorSet hθ j]
  exact univ_nonempty

/-! ### Parametrizations of the sectors -/

/-- For pointwise strictly monotone `θ` with values in an ordered field, the bounded sector between
sections `i` and `i + 1` is the image of `X × (0, 1)` under the map sending `(x, s)` to the point
`AffineMap.lineMap (θ i x) (θ (i + 1) x) s` of the fibre over `x`. When `α` is a topological ring,
`Continuous.lineMap` shows that this map is continuous whenever the functions of the stack are. -/
theorem sectorSet_castSucc_succ_eq_image [Field α] [IsStrictOrderedRing α]
    {θ : Fin (k + 1) → X → α} (hθ : ∀ x, StrictMono fun i ↦ θ i x) (i : Fin k) :
    sectorSet θ i.castSucc.succ =
      (fun z : X × α ↦ (z.1, AffineMap.lineMap (θ i.castSucc z.1) (θ i.succ z.1) z.2)) ''
        (univ ×ˢ Ioo 0 1) := by
  ext ⟨x, t⟩
  -- Each fibre is an open interval, which is the open segment between its endpoints.
  have h : t ∈ Ioo (θ i.castSucc x) (θ i.succ x) ↔
      t ∈ AffineMap.lineMap (θ i.castSucc x) (θ i.succ x) '' Ioo (0 : α) 1 := by
    rw [← openSegment_eq_image_lineMap, openSegment_eq_Ioo (hθ x i.castSucc_lt_succ)]
  rw [sectorSet_castSucc_succ fun x ↦ (hθ x).monotone, mem_ofPred_eq, ← mem_Ioo, h]
  simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
  exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

/-- For pointwise monotone `θ` with values in an ordered additive group, the lowest sector is the
image of `X × (-∞, 0)` under the map translating the height `s` by `θ 0 x`. When addition on `α`
is continuous, this map is continuous whenever `θ 0` is. -/
theorem sectorSet_zero_eq_image [AddCommGroup α] [IsOrderedAddMonoid α] {θ : Fin (k + 1) → X → α}
    (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ 0 = (fun z : X × α ↦ (z.1, θ 0 z.1 + z.2)) '' (univ ×ˢ Iio 0) := by
  ext ⟨x, t⟩
  have h : t ∈ Iio (θ 0 x) ↔ t ∈ (θ 0 x + ·) '' Iio 0 := by
    rw [image_const_add_Iio, add_zero]
  rw [sectorSet_zero hθ, mem_ofPred_eq, ← mem_Iio, h]
  simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
  exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

/-- For pointwise monotone `θ` with values in an ordered additive group, the highest sector is the
image of `X × (0, ∞)` under the map translating the height `s` by `θ k x`. When addition on `α`
is continuous, this map is continuous whenever `θ k` is. -/
theorem sectorSet_last_eq_image [AddCommGroup α] [IsOrderedAddMonoid α] {θ : Fin (k + 1) → X → α}
    (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    sectorSet θ (Fin.last (k + 1)) =
      (fun z : X × α ↦ (z.1, θ (Fin.last k) z.1 + z.2)) '' (univ ×ˢ Ioi 0) := by
  ext ⟨x, t⟩
  have h : t ∈ Ioi (θ (Fin.last k) x) ↔ t ∈ (θ (Fin.last k) x + ·) '' Ioi 0 := by
    rw [image_const_add_Ioi, add_zero]
  rw [sectorSet_last hθ, mem_ofPred_eq, ← mem_Ioi, h]
  simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, Prod.mk.injEq]
  exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨x, s, hs, rfl, h⟩, fun ⟨_, s, hs, rfl, h⟩ ↦ ⟨s, hs, h⟩⟩

end Order

section Topology

variable [TopologicalSpace X] {θ : Fin k → X → α}

/-- A sector bounded by finitely many continuous functions is open in the cylinder.
The functions need not be ordered. -/
theorem isOpen_sectorSet [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    (hc : ∀ i, Continuous (θ i)) (j : Fin (k + 1)) : IsOpen (sectorSet θ j) := by
  simp only [sectorSet, ofPred_and, ofPred_forall]
  refine (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_)
  · exact isOpen_lt ((hc i).comp continuous_fst) continuous_snd
  · exact isOpen_lt continuous_snd ((hc i).comp continuous_fst)

/-- Over a preconnected base, the section of a continuous function is preconnected. -/
theorem isPreconnected_sectionSet [TopologicalSpace α] [PreconnectedSpace X] {i : Fin k}
    (hθ : Continuous (θ i)) : IsPreconnected (sectionSet θ i) := by
  rw [sectionSet_eq_range]
  exact isPreconnected_range (by fun_prop)

/-- Over a connected base, the section of a continuous function is connected. -/
theorem isConnected_sectionSet [TopologicalSpace α] [ConnectedSpace X] {i : Fin k}
    (hθ : Continuous (θ i)) : IsConnected (sectionSet θ i) := by
  rw [sectionSet_eq_range]
  exact isConnected_range (by fun_prop)

/-- Every sector of a stack of continuous, pointwise strictly ordered functions with values in
an ordered semitopological field contains the graph of a continuous function. -/
theorem exists_continuous_forall_mem_sectorSet [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [IsSemitopologicalRing α] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    ∃ σ : X → α, Continuous σ ∧ ∀ x, (x, σ x) ∈ sectorSet θ j := by
  cases k with
  | zero => exact ⟨fun _ ↦ 0, continuous_const, by simp⟩
  | succ k =>
    have hm : ∀ x, Monotone fun i ↦ θ i x := fun x ↦ (hθ x).monotone
    cases j using Fin.cases with
    | zero =>
      refine ⟨fun x ↦ θ 0 x - 1, by fun_prop, fun x ↦ ?_⟩
      simp [sectorSet_zero hm]
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        refine ⟨fun x ↦ θ (Fin.last k) x + 1, by fun_prop, fun x ↦ ?_⟩
        rw [Fin.succ_last, sectorSet_last hm]
        simp
      | cast i =>
        refine ⟨fun x ↦ (θ i.castSucc x + θ i.succ x) / 2, by fun_prop, fun x ↦ ?_⟩
        have h := hθ x i.castSucc_lt_succ
        rw [sectorSet_castSucc_succ hm, mem_ofPred_eq]
        constructor <;> linarith

variable {θ : Fin k → X → ℝ}

/-- Over a preconnected base, each sector of a stack of continuous, pointwise strictly ordered
real functions is preconnected. -/
theorem isPreconnected_sectorSet [PreconnectedSpace X] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    IsPreconnected (sectorSet θ j) := by
  obtain ⟨σ, hσ, hσj⟩ := exists_continuous_forall_mem_sectorSet hc hθ j
  exact isPreconnected_of_isPreconnected_preimage_prodMk hσ hσj fun x ↦
    (ordConnected_preimage_mk_sectorSet θ j x).isPreconnected

/-- Over a connected base, each sector of a stack of continuous, pointwise strictly ordered real
functions is connected. -/
theorem isConnected_sectorSet [ConnectedSpace X] (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    IsConnected (sectorSet θ j) :=
  ⟨sectorSet_nonempty hθ j, isPreconnected_sectorSet hc hθ j⟩

end Topology

/-! ### The ambient cylinder -/

section Cylinder

variable {n : ℕ}

/-- The cylinder `S × α` over a set `S` of points of `α ^ n`, placed in `α ^ (n + 1)` with the
distinguished coordinate first. -/
def cylinder (S : Set (Fin n → α)) (z : S × α) : Fin (n + 1) → α :=
  Fin.cons z.2 z.1.val

variable {S : Set (Fin n → α)}

theorem cylinder_def (z : S × α) : cylinder S z = Fin.cons z.2 z.1.val :=
  (rfl)

@[simp]
theorem cylinder_apply_zero (z : S × α) : cylinder S z 0 = z.2 :=
  (rfl)

@[simp]
theorem cylinder_apply_succ (z : S × α) (i : Fin n) : cylinder S z i.succ = z.1.val i :=
  (rfl)

@[simp]
theorem tail_cylinder (z : S × α) : Fin.tail (cylinder S z) = z.1.val :=
  (rfl)

/-- Distinct points of the cylinder over `S` have distinct ambient images. -/
theorem cylinder_injective : Injective (cylinder S) := by
  intro z z' h
  have h₀ := congr_fun h 0
  have h₁ := congrArg Fin.tail h
  simp only [cylinder_apply_zero, tail_cylinder] at h₀ h₁
  exact Prod.ext (Subtype.ext h₁) h₀

/-- A point lies in the image of a subset `A` of the cylinder over `S` exactly when its last `n`
coordinates lie in `S` and, together with its distinguished coordinate, give a point of `A`. -/
theorem mem_image_cylinder {A : Set (S × α)} {y : Fin (n + 1) → α} :
    y ∈ cylinder S '' A ↔ ∃ h : Fin.tail y ∈ S, (⟨Fin.tail y, h⟩, y 0) ∈ A := by
  refine ⟨?_, fun ⟨h, hA⟩ ↦ ⟨_, hA, Fin.cons_self_tail y⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact ⟨z.1.2, hz⟩

/-- Forgetting the distinguished coordinate of the image of a subset `A` of the cylinder over `S`
gives the projection of `A` to `S`, as a subset of `α ^ n`. -/
theorem image_tail_image_cylinder (A : Set (S × α)) :
    Fin.tail '' (cylinder S '' A) = Subtype.val '' (Prod.fst '' A) := by
  simp only [image_image, tail_cylinder]

/-- The cylinder over `S` fills exactly the points whose last `n` coordinates lie in `S`. -/
theorem range_cylinder : range (cylinder S) = {y : Fin (n + 1) → α | Fin.tail y ∈ S} := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨(⟨Fin.tail y, hy⟩, y 0), Fin.cons_self_tail y⟩⟩
  rintro ⟨z, rfl⟩
  simp

variable [TopologicalSpace α]

/-- The cylinder map is continuous. -/
@[fun_prop]
theorem continuous_cylinder : Continuous (cylinder S) := by
  unfold cylinder
  fun_prop

/-- The cylinder over `S` is a topological embedding into `α ^ (n + 1)`. -/
theorem isEmbedding_cylinder : IsEmbedding (cylinder S) := by
  refine .of_comp continuous_cylinder (g := fun y ↦ (Fin.tail y, y 0)) (by fun_prop) ?_
  exact IsEmbedding.subtypeVal.prodMap .id

end Cylinder

/-! ### Stacks in the ambient space -/

section Ambient

variable {n : ℕ}

section Order

variable [LinearOrder α] {C : Set (Fin n → α)} {θ : Fin k → C → α}

/-- The cells of the stack over `C ⊆ α ^ n` defined by `θ`, as subsets of `α ^ (n + 1)`: the
images under `TauCeti.cylinder` of its `k` sections and its `k + 1` sectors. -/
def stackCells (C : Set (Fin n → α)) (θ : Fin k → C → α) : Set (Set (Fin (n + 1) → α)) :=
  range (fun i ↦ cylinder C '' sectionSet θ i) ∪ range fun j ↦ cylinder C '' sectorSet θ j

@[simp]
theorem mem_stackCells {E : Set (Fin (n + 1) → α)} :
    E ∈ stackCells C θ ↔
      (∃ i, cylinder C '' sectionSet θ i = E) ∨ ∃ j, cylinder C '' sectorSet θ j = E :=
  Iff.rfl

theorem image_cylinder_sectionSet_mem_stackCells (i : Fin k) :
    cylinder C '' sectionSet θ i ∈ stackCells C θ :=
  Or.inl ⟨i, rfl⟩

theorem image_cylinder_sectorSet_mem_stackCells (j : Fin (k + 1)) :
    cylinder C '' sectorSet θ j ∈ stackCells C θ :=
  Or.inr ⟨j, rfl⟩

/-- A stack has finitely many cells. -/
theorem finite_stackCells (C : Set (Fin n → α)) (θ : Fin k → C → α) :
    (stackCells C θ).Finite :=
  (finite_range _).union (finite_range _)

section Map

variable {m : ℕ} (θ : Fin k → C → α) (f : (Fin m → α) → Fin n → α)

omit [LinearOrder α] in
/-- Pullback of an ambient section along a base map. The height coordinate is unchanged. -/
theorem image_cylinder_sectionSet_comp (i : Fin k) :
    cylinder (f ⁻¹' C) '' sectionSet (fun i x ↦ θ i ⟨f x.1, x.2⟩) i =
      (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' (cylinder C '' sectionSet θ i) := by
  ext y
  simp only [mem_image_cylinder, mem_sectionSet, mem_preimage, Fin.tail_cons, Fin.cons_zero]

/-- Pullback of an ambient sector along a base map, including either unbounded sector. -/
theorem image_cylinder_sectorSet_comp (j : Fin (k + 1)) :
    cylinder (f ⁻¹' C) '' sectorSet (fun i x ↦ θ i ⟨f x.1, x.2⟩) j =
      (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' (cylinder C '' sectorSet θ j) := by
  ext y
  simp only [mem_image_cylinder, mem_sectorSet, mem_preimage, Fin.tail_cons, Fin.cons_zero]

/-- The cells of a pulled-back stack are precisely the inverse images of the original cells.
This holds even when the base map is not injective or surjective. -/
theorem stackCells_comp :
    stackCells (f ⁻¹' C) (fun i x ↦ θ i ⟨f x.1, x.2⟩) =
      (fun E ↦ (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' E) '' stackCells C θ := by
  ext E
  simp only [mem_stackCells, mem_image]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨_, Or.inl ⟨i, rfl⟩, (image_cylinder_sectionSet_comp θ f i).symm⟩
    · exact ⟨_, Or.inr ⟨j, rfl⟩, (image_cylinder_sectorSet_comp θ f j).symm⟩
  · rintro ⟨E, (⟨i, rfl⟩ | ⟨j, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, image_cylinder_sectionSet_comp θ f i⟩
    · exact Or.inr ⟨j, image_cylinder_sectorSet_comp θ f j⟩

end Map

section Restrict

variable {D : Set (Fin n → α)} (h : D ⊆ C)

omit [LinearOrder α] in
/-- Restricting the base of the cylinder from `C` to a subset `D` cuts the image of a subset of
the cylinder over `C` down to the points lying over `D`. -/
theorem image_cylinder_preimage_inclusion (A : Set (C × α)) :
    cylinder D '' (Prod.map (inclusion h) id ⁻¹' A) = cylinder C '' A ∩ Fin.tail ⁻¹' D := by
  ext y
  simp only [mem_image_cylinder, mem_inter_iff, mem_preimage, Prod.map_apply, inclusion_mk,
    id_eq]
  exact ⟨fun ⟨hD, hA⟩ ↦ ⟨⟨h hD, hA⟩, hD⟩, fun ⟨⟨_, hA⟩, hD⟩ ↦ ⟨hD, hA⟩⟩

variable (θ : Fin k → C → α)

omit [LinearOrder α] in
/-- A section of a stack restricted to a smaller base `D` is the part of the original section
lying over `D`. -/
theorem image_cylinder_sectionSet_inclusion (i : Fin k) :
    cylinder D '' sectionSet (fun i ↦ θ i ∘ inclusion h) i =
      cylinder C '' sectionSet θ i ∩ Fin.tail ⁻¹' D := by
  rw [sectionSet_comp, image_cylinder_preimage_inclusion]

/-- A sector of a stack restricted to a smaller base `D` is the part of the original sector lying
over `D`, including either unbounded sector. -/
theorem image_cylinder_sectorSet_inclusion (j : Fin (k + 1)) :
    cylinder D '' sectorSet (fun i ↦ θ i ∘ inclusion h) j =
      cylinder C '' sectorSet θ j ∩ Fin.tail ⁻¹' D := by
  rw [sectorSet_comp, image_cylinder_preimage_inclusion]

/-- The cells of a stack restricted to a smaller base `D` are the parts of the original cells
lying over `D`. -/
theorem stackCells_inclusion :
    stackCells D (fun i ↦ θ i ∘ inclusion h) = (· ∩ Fin.tail ⁻¹' D) '' stackCells C θ := by
  ext E
  simp only [mem_stackCells, mem_image]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨_, Or.inl ⟨i, rfl⟩, (image_cylinder_sectionSet_inclusion h θ i).symm⟩
    · exact ⟨_, Or.inr ⟨j, rfl⟩, (image_cylinder_sectorSet_inclusion h θ j).symm⟩
  · rintro ⟨E, (⟨i, rfl⟩ | ⟨j, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, image_cylinder_sectionSet_inclusion h θ i⟩
    · exact Or.inr ⟨j, image_cylinder_sectorSet_inclusion h θ j⟩

end Restrict

/-- For pointwise strictly monotone `θ` with values in a densely ordered type without endpoints,
every cell of the stack over `C` lies over the whole of `C`. -/
theorem image_tail_of_mem_stackCells [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] (hθ : ∀ x, StrictMono fun i ↦ θ i x) {E : Set (Fin (n + 1) → α)}
    (hE : E ∈ stackCells C θ) : Fin.tail '' E = C := by
  rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [image_tail_image_cylinder]
  · rw [fst_image_sectionSet, Subtype.coe_image_univ]
  · rw [fst_image_sectorSet hθ, Subtype.coe_image_univ]

/-- If over each set in `𝒟` a pointwise strictly ordered stack is chosen, with values in a
densely ordered type without endpoints, then the projections of all the cells of these stacks are
exactly the sets in `𝒟`. -/
theorem image_image_tail_iUnion_stackCells [Nonempty α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] {𝒟 : Set (Set (Fin n → α))} {k : Set (Fin n → α) → ℕ}
    {θ : ∀ C : Set (Fin n → α), Fin (k C) → C → α}
    (hθ : ∀ C ∈ 𝒟, ∀ x, StrictMono fun i ↦ θ C i x) :
    image Fin.tail '' ⋃ C ∈ 𝒟, stackCells C (θ C) = 𝒟 := by
  ext D
  simp only [mem_image, mem_iUnion₂]
  constructor
  · rintro ⟨E, ⟨C, hC, hE⟩, rfl⟩
    rwa [image_tail_of_mem_stackCells (hθ C hC) hE]
  · intro hD
    exact ⟨_, ⟨D, hD, image_cylinder_sectorSet_mem_stackCells 0⟩,
      image_tail_of_mem_stackCells (hθ D hD) (image_cylinder_sectorSet_mem_stackCells 0)⟩

/-- For pointwise monotone `θ`, the cells of the stack over `C` cover the cylinder over `C`. -/
theorem sUnion_stackCells (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    ⋃₀ stackCells C θ = Fin.tail ⁻¹' C := by
  ext y
  refine ⟨fun ⟨E, hE, hy⟩ ↦ ?_, fun h ↦ ?_⟩
  · rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> exact (mem_image_cylinder.1 hy).1
  · -- The point of the cylinder over `C` above `y` lies in a section or a sector.
    have hz : ((⟨Fin.tail y, h⟩, y 0) : C × α) ∈ (⋃ i, sectionSet θ i) ∪ ⋃ j, sectorSet θ j := by
      rw [iUnion_sectionSet_union_iUnion_sectorSet hθ]
      exact mem_univ _
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hz
      exact ⟨_, image_cylinder_sectionSet_mem_stackCells i, mem_image_cylinder.2 ⟨h, hi⟩⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hz
      exact ⟨_, image_cylinder_sectorSet_mem_stackCells j, mem_image_cylinder.2 ⟨h, hj⟩⟩

/-- For pointwise injective `θ`, distinct cells of the stack over `C` are disjoint. -/
theorem pairwiseDisjoint_stackCells (hθ : ∀ x, Injective fun i ↦ θ i x) :
    (stackCells C θ).PairwiseDisjoint id := by
  rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩) _ (⟨i', rfl⟩ | ⟨j', rfl⟩) hne <;>
    rw [onFun, id, id, disjoint_image_iff cylinder_injective]
  · exact pairwise_disjoint_sectionSet hθ fun h ↦ hne (h ▸ rfl)
  · exact disjoint_sectionSet_sectorSet θ i j'
  · exact (disjoint_sectionSet_sectorSet θ i' j).symm
  · exact pairwise_disjoint_sectorSet θ fun h ↦ hne (h ▸ rfl)

/-- Every cell of a stack meets each line parallel to the distinguished axis in an
order-connected set: a point or nothing for a section, an open interval for a sector. -/
theorem ordConnected_setOf_cons_mem_of_mem_stackCells {E : Set (Fin (n + 1) → α)}
    (hE : E ∈ stackCells C θ) (x : Fin n → α) : {t | Fin.cons t x ∈ E}.OrdConnected := by
  -- Over `x ∈ C` the slice of `cylinder C '' A` is the fibre of `A` over `x`, else it is empty.
  have key {A : Set (C × α)} (hA : ∀ x, (Prod.mk x ⁻¹' A).OrdConnected) :
      {t | Fin.cons t x ∈ cylinder C '' A}.OrdConnected := by
    by_cases hx : x ∈ C
    · convert hA ⟨x, hx⟩ using 1
      ext t
      simp only [mem_ofPred_eq, mem_preimage, mem_image_cylinder, Fin.tail_cons, Fin.cons_zero]
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hx, h⟩⟩
    · convert ordConnected_empty (α := α) using 1
      ext t
      simp only [mem_ofPred_eq, mem_image_cylinder, Fin.tail_cons, mem_empty_iff_false,
        iff_false]
      exact fun ⟨h, _⟩ ↦ hx h
  rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · refine key fun x ↦ ?_
    convert ordConnected_singleton (a := θ i x) using 1
    ext t
    simp [mem_sectionSet, eq_comm]
  · exact key (ordConnected_preimage_mk_sectorSet θ j)

end Order

/-- For continuous, pointwise strictly monotone real `θ` over a connected base, every cell of the
stack is connected. -/
theorem isConnected_of_mem_stackCells {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}
    (hC : IsConnected C) (hc : ∀ i, Continuous (θ i)) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) : IsConnected E := by
  have := isConnected_iff_connectedSpace.1 hC
  rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact (isConnected_sectionSet (hc i)).image _ continuous_cylinder.continuousOn
  · exact (isConnected_sectorSet hc hθ j).image _ continuous_cylinder.continuousOn

end Ambient

end TauCeti
