/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
topological embedding, so connectedness of stack cells transfers to their ambient images.

## Main declarations

* `TauCeti.sectionSet`, `TauCeti.sectorSet`: the sections and sectors of a stack.
* `TauCeti.mem_sectorSet_iff_of_monotone`: for ordered functions, a sector is cut out by the two
  adjacent sections.
* `TauCeti.iUnion_sectionSet_union_iUnion_sectorSet`, `TauCeti.pairwise_disjoint_sectionSet`,
  `TauCeti.pairwise_disjoint_sectorSet`, `TauCeti.disjoint_sectionSet_sectorSet`: the sections and
  sectors partition the cylinder.
* `TauCeti.exists_continuous_forall_mem_sectorSet`: every sector of a continuous strictly ordered
  stack contains the graph of a continuous function.
* `TauCeti.isConnected_sectionSet`, `TauCeti.isConnected_sectorSet`: over a connected base, the
  sections and sectors of a continuous strictly ordered real stack are connected.
* `TauCeti.cylinder`, `TauCeti.isEmbedding_cylinder`: the ambient cylinder embedding.

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

end Order

section Topology

variable [TopologicalSpace X] {θ : Fin k → X → α}

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
an ordered topological field contains the graph of a continuous function. -/
theorem exists_continuous_forall_mem_sectorSet [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [IsTopologicalRing α] (hc : ∀ i, Continuous (θ i))
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
    IsConnected (sectorSet θ j) := by
  obtain ⟨x⟩ := ‹ConnectedSpace X›.toNonempty
  obtain ⟨σ, -, hσj⟩ := exists_continuous_forall_mem_sectorSet hc hθ j
  exact ⟨⟨_, hσj x⟩, isPreconnected_sectorSet hc hθ j⟩

end Topology

/-! ### The ambient cylinder -/

section Cylinder

variable {n : ℕ}

/-- The cylinder `S × α` over a set `S` of points of `α ^ n`, placed in `α ^ (n + 1)` with the
distinguished coordinate first. -/
def cylinder (S : Set (Fin n → α)) (z : S × α) : Fin (n + 1) → α :=
  Fin.cons z.2 z.1.val

variable {S : Set (Fin n → α)}

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

end TauCeti
