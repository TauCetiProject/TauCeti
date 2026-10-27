/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Embedding a vector bundle into a finite trivial bundle

A family of linear trivializations `e i` of a vector bundle `E`, together with scalar weights
`ρ i`, assembles into a fibrewise continuous linear map `E x →L[𝕜] (ι → F)`, namely
`v ↦ (ρ i x • e i v)ᵢ`. When each weight `ρ i` is continuous with topological support in the base
set of `e i`, the resulting map of total spaces is continuous. It is injective on the fibre over
any point of the base set of some `e i` at which `ρ i` is nonzero.

Applying this to a partition of unity subordinate to a finite cover by trivializations shows that,
over a normal base admitting such a cover, a vector bundle with model fibre `F` admits a continuous
bundle map into the trivial bundle with fibre `ι → F` which is linear and injective on every fibre.
Over a compact normal base (in particular a compact Hausdorff base) a finite cover always exists,
so every vector bundle with finite-dimensional model fibre admits such a map into a trivial bundle
`B × 𝕜ᴺ` for some `N`. This is the classical first step towards a complementary bundle
`E ⊕ E⊥ ≅ B × 𝕜ᴺ` over a compact Hausdorff base; see Atiyah, *K-theory*, §1.4, or Hatcher,
*Vector bundles and K-theory*, Proposition 1.4.

## Main definitions and results

* `TauCeti.weightedTrivializationMap`: the fibrewise map `v ↦ (ρ i x • e i v)ᵢ`.
* `TauCeti.continuous_weightedTrivializationMap`: it is continuous on the total space when each
  weight is continuous with topological support in the base set of its trivialization.
* `TauCeti.injective_weightedTrivializationMap`: it is injective on the fibre over a point of the
  base set of some `e i` at which `ρ i` is nonzero.
* `TauCeti.exists_continuous_injective_pi_of_iUnion_baseSet`: a finite cover by trivializations of
  a normal base gives a continuous fibrewise injective linear map into the trivial bundle with
  fibre `ι → F`.
* `TauCeti.exists_continuous_injective_fin_of_compactSpace`: over a compact normal base, every
  vector bundle with finite-dimensional model fibre admits a continuous fibrewise injective linear
  map into a trivial bundle `B × (Fin N → 𝕜)`.
-/

public section

open Bundle Set Function
open scoped Topology

namespace TauCeti

variable {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]

section Weighted

/-- The fibrewise continuous linear map `v ↦ (ρ i x • e i v)ᵢ` assembled from a family of linear
trivializations `e i` and scalar weights `ρ i`. Outside the base set of `e i`, the coordinate
`(e i).continuousLinearMapAt 𝕜 x` is zero. -/
noncomputable def weightedTrivializationMap (e : ι → Trivialization F (π F E))
    [∀ i, (e i).IsLinear 𝕜] (ρ : ι → B → 𝕜) (x : B) : E x →L[𝕜] (ι → F) :=
  ContinuousLinearMap.pi fun i ↦ ρ i x • (e i).continuousLinearMapAt 𝕜 x

variable (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear 𝕜] (ρ : ι → B → 𝕜)

@[simp]
theorem weightedTrivializationMap_apply (x : B) (v : E x) (i : ι) :
    weightedTrivializationMap e ρ x v i = ρ i x • (e i).continuousLinearMapAt 𝕜 x v :=
  (rfl)

/-- On the base set of `e i`, the `i`-th coordinate of `weightedTrivializationMap` is the weighted
fibre coordinate of the trivialization `e i`. -/
theorem weightedTrivializationMap_apply_of_mem {x : B} {i : ι} (hx : x ∈ (e i).baseSet)
    (v : E x) : weightedTrivializationMap e ρ x v i = ρ i x • (e i ⟨x, v⟩).2 := by
  rw [weightedTrivializationMap_apply, (e i).continuousLinearMapAt_apply_of_mem (R := 𝕜) hx]

/-- The map of total spaces induced by `weightedTrivializationMap` is continuous provided each
weight `ρ i` is continuous and has topological support inside the base set of `e i`. -/
theorem continuous_weightedTrivializationMap (hρ : ∀ i, Continuous (ρ i))
    (hsupp : ∀ i, tsupport (ρ i) ⊆ (e i).baseSet) :
    Continuous fun p : TotalSpace F E ↦ weightedTrivializationMap e ρ p.proj p.2 := by
  refine continuous_pi fun i ↦ continuous_of_tsupport fun p hp ↦ ?_
  have hpρ : p.proj ∈ tsupport (ρ i) :=
    tsupport_comp_subset_preimage (ρ i) (FiberBundle.continuous_proj F E)
      (tsupport_smul_subset_left _ _ hp)
  have hsource : (e i).source ∈ 𝓝 p :=
    (e i).open_source.mem_nhds ((e i).mem_source.2 (hsupp i hpρ))
  have hcont : ContinuousAt (fun q : TotalSpace F E ↦ ρ i q.proj • (e i q).2) p :=
    ((hρ i).continuousAt.comp (FiberBundle.continuous_proj F E).continuousAt).smul
      ((e i).continuousOn.continuousAt hsource).snd
  refine hcont.congr (Filter.eventuallyEq_of_mem hsource fun q hq ↦ ?_)
  exact (weightedTrivializationMap_apply_of_mem e ρ ((e i).mem_source.1 hq) q.2).symm

/-- `weightedTrivializationMap` is injective on the fibre over a point `x` of the base set of some
`e i` at which the weight `ρ i` does not vanish. -/
theorem injective_weightedTrivializationMap {x : B} {i : ι} (hxi : x ∈ (e i).baseSet)
    (hi : ρ i x ≠ 0) : Injective (weightedTrivializationMap e ρ x) := by
  intro v w hvw
  have h : (e i).continuousLinearMapAt 𝕜 x v = (e i).continuousLinearMapAt 𝕜 x w :=
    smul_right_injective F hi (congrFun hvw i)
  rw [← (e i).symmL_continuousLinearMapAt (R := 𝕜) hxi v, h,
    (e i).symmL_continuousLinearMapAt hxi w]

end Weighted

section Existence

variable [NormedAlgebra ℝ 𝕜]

/-- If the base sets of finitely many linear trivializations `e i` cover a normal base, then the
bundle admits a continuous fibrewise injective linear map into the trivial bundle with
fibre `ι → F`. -/
theorem exists_continuous_injective_pi_of_iUnion_baseSet [NormalSpace B] [Finite ι]
    (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear 𝕜]
    (hcover : ⋃ i, (e i).baseSet = univ) :
    ∃ j : ∀ x, E x →L[𝕜] (ι → F),
      Continuous (fun p : TotalSpace F E ↦ j p.proj p.2) ∧ ∀ x, Injective (j x) := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ
    (fun i ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (locallyFinite_of_finite _)
    hcover.ge
  let w : ι → B → 𝕜 := fun i x ↦ algebraMap ℝ 𝕜 (ρ i x)
  have hwsupp : ∀ i, tsupport (w i) ⊆ (e i).baseSet := fun i ↦
    (tsupport_comp_subset (map_zero (algebraMap ℝ 𝕜)) (ρ i)).trans (hρ i)
  refine ⟨weightedTrivializationMap e w,
    continuous_weightedTrivializationMap e w (fun i ↦ (continuous_algebraMap ℝ 𝕜).comp (ρ i).2)
      hwsupp, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
  have hwi : w i x ≠ 0 := (map_ne_zero (algebraMap ℝ 𝕜)).2 hi.ne'
  exact injective_weightedTrivializationMap e w (hwsupp i (subset_tsupport _ hwi)) hwi

/-- Over a compact normal base (for instance a compact Hausdorff base), every vector bundle with
finite-dimensional model fibre admits a continuous fibrewise injective linear map into the
trivial bundle `B × (Fin N → 𝕜)` for some `N`. -/
theorem exists_continuous_injective_fin_of_compactSpace [CompactSpace B] [NormalSpace B]
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F E] :
    ∃ (N : ℕ) (j : ∀ x, E x →L[𝕜] (Fin N → 𝕜)),
      Continuous (fun p : TotalSpace F E ↦ j p.proj p.2) ∧ ∀ x, Injective (j x) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : B ↦ (trivializationAt F E x).baseSet)
    (fun x ↦ (trivializationAt F E x).open_baseSet)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F E x⟩
  obtain ⟨j, hj, hinj⟩ := exists_continuous_injective_pi_of_iUnion_baseSet (𝕜 := 𝕜)
    (fun x : t ↦ trivializationAt F E x.1)
    (eq_univ_of_univ_subset fun x hx ↦ by simpa using ht hx)
  let L : (t → F) ≃L[𝕜] (Fin (Module.finrank 𝕜 (t → F)) → 𝕜) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact ⟨Module.finrank 𝕜 (t → F), fun x ↦ L.toContinuousLinearMap.comp (j x),
    L.continuous.comp hj, fun x ↦ L.injective.comp (hinj x)⟩

end Existence

end TauCeti
