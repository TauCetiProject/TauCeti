/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel
import TauCeti.Analysis.Calculus.Bilinear

/-!
# Morse–Bott data of the components of the weight-model moment map

Let `α : ι → StrongDual ℝ 𝔱` be the weights of the linear torus action on `ℂ^ι`, written in real
coordinates `z_i = q_i + i p_i`, with moment map `μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i`
(`TauCeti.weightMomentMap`). For `ξ ∈ 𝔱`, the component

`μ^ξ(q, p) = -½ Σ_i α_i(ξ) (q_i² + p_i²)`

is a quadratic function, so its Hessian is the same quadratic form

`v ↦ -Σ_i α_i(ξ) (v_{q,i}² + v_{p,i}²)`

at every point. This is a weighted sum of squares in which every weight `-α_i(ξ)` appears twice,
once for `q_i` and once for `p_i`. Sylvester's law of inertia then reads off its indices of inertia:

* the Morse index of `μ^ξ` is twice the number of `i` with `α_i(ξ) > 0`;
* the positive index of its Hessian (the coindex) is twice the number of `i` with `α_i(ξ) < 0`;
* the null space of its Hessian is the kernel of the generator `ξ_M`, the subspace of `z` with
  `z_i = 0` whenever `α_i(ξ) ≠ 0`, of dimension twice the number of `i` with `α_i(ξ) = 0`.

The critical points of `μ^ξ` are exactly the zeros of the generator `ξ_M`, so the critical set of
`μ^ξ` is that same linear subspace. Hence `μ^ξ` is a Morse–Bott function: at each critical point,
the null space of the Hessian is the tangent space of the critical set. Its index and coindex are
even. By the equivariant Darboux theorem the weight model is the local form of a Hamiltonian torus
action near a fixed point, so these are the local Morse–Bott data of the components of a torus
moment map there.

## Main results

* `TauCeti.hessianQuadraticForm_weightMomentMap_apply`: the Hessian of `μ^ξ`.
* `TauCeti.equivalent_hessianQuadraticForm_weightMomentMap_apply`: the Hessian is equivalent to the
  weighted sum of squares with each weight `-α_i(ξ)` repeated twice.
* `TauCeti.morseIndex_weightMomentMap_apply`: the Morse index is `2 #{i | 0 < α_i(ξ)}`.
* `TauCeti.sigPos_hessianQuadraticForm_weightMomentMap_apply`: the coindex is
  `2 #{i | α_i(ξ) < 0}`.
* `TauCeti.fderiv_weightMomentMap_apply_eq_zero_iff`: the critical points of `μ^ξ` are the zeros of
  the generator `ξ_M`.
* `TauCeti.radical_hessianQuadraticForm_weightMomentMap_apply`: the null space of the Hessian is
  the kernel of the generator `ξ_M`, that is the critical set.
* `TauCeti.finrank_ker_weightGenerator`: this subspace has dimension `2 #{i | α_i(ξ) = 0}`.

## References

* Victor Guillemin and Shlomo Sternberg, *Convexity properties of the moment mapping*, Invent.
  Math. 67 (1982), Section 2.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Section 27.
-/

public section

noncomputable section

namespace TauCeti

open QuadraticForm QuadraticMap

variable {ι : Type*} [Fintype ι] {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

/-- The coordinate `z ↦ q_i` of `ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`. -/
private abbrev coordFst (i : ι) : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The coordinate `z ↦ p_i` of `ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`. -/
private abbrev coordSnd (i : ι) : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ ↦ ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The component `μ^ξ` is the quadratic function `z ↦ B z z` of a continuous bilinear form. -/
private theorem weightMomentMap_apply_eq_bilinear (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱) :
    (fun y ↦ weightMomentMap α y ξ) = fun z ↦
      (∑ i, (-(1 / 2) * α i ξ) •
        ((coordFst i).smulRight (coordFst i) + (coordSnd i).smulRight (coordSnd i))) z z := by
  funext z
  simp only [weightMomentMap_apply, sum_apply, smul_apply,
    add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    PiLp.proj_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The Hessian of a component of the weight-model moment map.** At every point, the Hessian of
`μ^ξ` is `v ↦ -Σ_i α_i(ξ) (v_{q,i}² + v_{p,i}²)`. -/
theorem hessianQuadraticForm_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    hessianQuadraticForm (fun y ↦ weightMomentMap α y ξ) x v =
      -∑ i, α i ξ * (v.1 i ^ 2 + v.2 i ^ 2) := by
  rw [hessianQuadraticForm_apply, weightMomentMap_apply_eq_bilinear,
    ContinuousLinearMap.fderiv_fderiv_apply_self]
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', PiLp.proj_apply, smul_eq_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The real coordinates `(q, p) ↦ (q_i)_i ⊔ (p_i)_i` of `ℂ^ι`, indexed by `ι ⊕ ι`. -/
private def sumCoords :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ≃ₗ[ℝ] (ι ⊕ ι → ℝ) :=
  ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (ι → ℝ))).trans
    (LinearEquiv.sumArrowLequivProdArrow ι ι ℝ ℝ).symm

omit [Fintype ι] in
private theorem sumCoords_inl (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    sumCoords v (Sum.inl i) = v.1 i :=
  (rfl)

omit [Fintype ι] in
private theorem sumCoords_inr (v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    sumCoords v (Sum.inr i) = v.2 i :=
  (rfl)

/-- The isometry of the Hessian of `μ^ξ` with the doubled weighted sum of squares, given by the
real coordinates `(q_i)_i ⊔ (p_i)_i`. -/
private def hessianIsometryEquiv (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (hessianQuadraticForm (fun y ↦ weightMomentMap α y ξ) x).IsometryEquiv
      (weightedSumSquares ℝ (Sum.elim (fun i ↦ -α i ξ) fun i ↦ -α i ξ)) where
  __ := sumCoords
  map_app' v := by
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, weightedSumSquares_apply,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sumCoords_inl, sumCoords_inr, smul_eq_mul,
      hessianQuadraticForm_weightMomentMap_apply, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The Hessian of `μ^ξ` is a doubled weighted sum of squares.** In the real coordinates
`(q_i)_i ⊔ (p_i)_i`, indexed by `ι ⊕ ι`, the Hessian of `μ^ξ` at any point is the weighted sum of
squares in which the weight `-α_i(ξ)` is attached to both `q_i` and `p_i`. -/
theorem equivalent_hessianQuadraticForm_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (hessianQuadraticForm (fun y ↦ weightMomentMap α y ξ) x).Equivalent
      (weightedSumSquares ℝ (Sum.elim (fun i ↦ -α i ξ) fun i ↦ -α i ξ)) :=
  ⟨hessianIsometryEquiv α ξ x⟩

omit [Fintype ι] in
/-- A property of the doubled index set `ι ⊕ ι`, read off the same function on both copies of `ι`,
holds on twice as many indices as on `ι`. -/
private theorem ncard_setOf_sumElim [Finite ι] {β : Type*} (f : ι → β) (P : β → Prop) :
    {j : ι ⊕ ι | P (Sum.elim f f j)}.ncard = 2 * {i | P (f i)}.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Set.coe_ofPred, Set.coe_ofPred,
    Nat.card_congr Equiv.subtypeSum, Nat.card_sum, two_mul]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- **The Morse index of a component of the weight-model moment map.** At every point, the Morse
index of `μ^ξ` is twice the number of weights with `α_i(ξ) > 0`. -/
theorem morseIndex_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    morseIndex (fun y ↦ weightMomentMap α y ξ) x = 2 * {i | 0 < α i ξ}.ncard := by
  rw [morseIndex_def, sigNeg_of_equiv_weightedSumSquares
    (equivalent_hessianQuadraticForm_weightMomentMap_apply α ξ x),
    ncard_setOf_sumElim (fun i ↦ -α i ξ) (· < 0)]
  simp

/-- **The coindex of a component of the weight-model moment map.** At every point, the positive
index of inertia of the Hessian of `μ^ξ` is twice the number of weights with `α_i(ξ) < 0`. -/
theorem sigPos_hessianQuadraticForm_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    sigPos (hessianQuadraticForm (fun y ↦ weightMomentMap α y ξ) x) =
      2 * {i | α i ξ < 0}.ncard := by
  rw [sigPos_of_equiv_weightedSumSquares
    (equivalent_hessianQuadraticForm_weightMomentMap_apply α ξ x),
    ncard_setOf_sumElim (fun i ↦ -α i ξ) (0 < ·)]
  simp

/-- The kernel of the generator of the rotation by the angles `θ` is the subspace of `z` with
`z_i = q_i + i p_i = 0` whenever `θ_i ≠ 0`. -/
theorem mem_ker_weightGenerator_iff (θ : ι → ℝ) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.ker (weightGenerator θ).toLinearMap ↔
      ∀ i, θ i ≠ 0 → x.1 i = 0 ∧ x.2 i = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, weightGenerator_apply_eq_zero_iff]
  exact forall_congr' fun i ↦ by tauto

/-- In the real coordinates `(q_i)_i ⊔ (p_i)_i`, the kernel of the generator of the rotation by the
angles `θ` is spanned by the coordinates whose angle vanishes. -/
private theorem map_sumCoords_ker_weightGenerator (θ : ι → ℝ) :
    (LinearMap.ker (weightGenerator θ).toLinearMap).map sumCoords.toLinearMap =
      Pi.spanSubset ℝ {j | Sum.elim θ θ j = 0} := by
  ext u
  obtain ⟨v, rfl⟩ := sumCoords.surjective u
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_ker_weightGenerator_iff,
    Pi.mem_spanSubset_iff]
  constructor
  · rintro h (i | i) hi
    · exact (h i hi).1
    · exact (h i hi).2
  · exact fun h i hi ↦ ⟨h (Sum.inl i) hi, h (Sum.inr i) hi⟩

/-- **Critical points of a component of the weight-model moment map.** A point is critical for
`μ^ξ` exactly when the generator `ξ_M`, the rotation generator for the angles `α_i(ξ)`, vanishes
there. -/
theorem fderiv_weightMomentMap_apply_eq_zero_iff (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y ↦ weightMomentMap α y ξ) x = 0 ↔ weightGenerator (fun i ↦ α i ξ) x = 0 := by
  rw [← SymplecticForm.hamiltonianVectorField_eq_zero_iff stdSymplecticForm,
    hamiltonianVectorField_weightMomentMap]

/-- **The Morse–Bott property of a component of the weight-model moment map.** At every point,
the null space of the Hessian of `μ^ξ` is the kernel of the generator `ξ_M`. By
`TauCeti.fderiv_weightMomentMap_apply_eq_zero_iff` this kernel is the critical set of `μ^ξ`, so at
each critical point the null space of the Hessian is the tangent space of the critical set. -/
theorem radical_hessianQuadraticForm_weightMomentMap_apply (α : ι → StrongDual ℝ 𝔱) (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (hessianQuadraticForm (fun y ↦ weightMomentMap α y ξ) x).radical =
      LinearMap.ker (weightGenerator fun i ↦ α i ξ).toLinearMap := by
  refine Submodule.map_injective_of_injective (f := sumCoords.toLinearMap) sumCoords.injective ?_
  rw [map_sumCoords_ker_weightGenerator]
  -- The linear equivalence underlying `hessianIsometryEquiv` is `sumCoords`, by construction.
  have h := (hessianIsometryEquiv α ξ x).map_radical
  rw [radical_weightedSumSquares] at h
  refine h.trans (congrArg _ ?_)
  ext (i | i) <;> simp

/-- The kernel of the generator of the rotation by the angles `θ`, the fixed tangent directions,
has dimension twice the number of `i` with `θ_i = 0`. -/
theorem finrank_ker_weightGenerator (θ : ι → ℝ) :
    Module.finrank ℝ (LinearMap.ker (weightGenerator θ).toLinearMap) =
      2 * {i | θ i = 0}.ncard := by
  rw [← sumCoords.finrank_map_eq, map_sumCoords_ker_weightGenerator,
    Pi.dim_spanSubset, ncard_setOf_sumElim θ (· = 0)]

end TauCeti
