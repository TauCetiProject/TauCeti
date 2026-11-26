/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.GNS
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.InnerProductSpace.ConjOperator
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing

/-!
# The modular conjugation of a KMS state

For a β-KMS state `ω` of a point-norm continuous real action `α` on a possibly nonunital
C⋆-algebra `A`, the formula `J₀ [a] = [α_{iβ/2}(a⋆)]` on classes of entire analytic elements
extends uniquely to an antiunitary involution `J₀ : H_ω ≃ₗᵢ⋆[ℂ] H_ω`
(`TauCeti.CStarAction.IsKMSState.modularConjugation`). Conjugating bounded operators by `J₀` via
`LinearIsometryEquiv.conjOperator` (`T ↦ J₀ T J₀`) satisfies `J₀ M J₀ ⊆ M'` for
`M = ω.toPositiveLinearMap.gnsVonNeumannAlgebra`
(`TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_commutant`). In the unital
case, `J₀` fixes the cyclic GNS vector `Ω = [1]`
(`TauCeti.CStarAction.IsKMSState.modularConjugation_gnsVector`); the reverse inclusion
`J₀ M' J₀ ⊆ M` is proved in `TauCeti.Analysis.CStarAlgebra.Action.KMS.TomitaCommutation`.

## Main definitions

* `TauCeti.CStarAction.IsKMSState.modularConjugation`: the antiunitary involution `J₀` on `H_ω`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_toGNS`: `J₀ [a] = [α_{iβ/2}(a⋆)]`.
* `TauCeti.CStarAction.IsKMSState.inner_modularConjugation`: `⟪J₀ u, J₀ v⟫ = ⟪v, u⟫`.
* `TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_commutant`: `J₀ M J₀ ⊆ M'`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Section 5.3.1.
-/

public section

noncomputable section

open Complex ContinuousLinearMap PositiveLinearMap
open scoped ComplexConjugate ComplexOrder CStarAlgebra InnerProductSpace

namespace TauCeti.CStarAction

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-! ### Construction of the modular conjugation -/

/-- The classes of entire analytic elements are dense in the GNS Hilbert space. -/
theorem denseRange_toGNS_entireAnalytic (α : CStarAction (Multiplicative ℝ) A)
    (f : A →ₚ[ℂ] ℂ) : DenseRange (fun a : α.entireAnalytic => f.toGNS (a : A)) := by
  intro v
  have hrange : Set.range (fun a : α.entireAnalytic => f.toGNS (a : A)) =
      f.toGNS '' (α.entireAnalytic : Set A) := by ext w; simp
  rw [hrange]
  refine (closure_minimal ?_ isClosed_closure) (f.denseRange_toGNS v)
  calc Set.range f.toGNS = f.toGNS '' closure (α.entireAnalytic : Set A) := by
        rw [α.dense_entireAnalytic.closure_eq, Set.image_univ]
    _ ⊆ closure (f.toGNS '' (α.entireAnalytic : Set A)) :=
        image_closure_subset_closure_image f.toGNS.continuous

/-- The pre-modular conjugation `[a] ↦ [α_{iβ/2}(a⋆)]` on the entire analytic subalgebra. -/
private def preModularConjugation (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (f : A →ₚ[ℂ] ℂ) : α.entireAnalytic →ₛₗ[starRingEnd ℂ] f.GNS where
  toFun a := f.toGNS (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))
  map_add' a b := by
    have ha := mem_entireAnalytic.mp a.property; have hb := mem_entireAnalytic.mp b.property
    simp only [NonUnitalStarSubalgebra.coe_add, star_add, ha.star.entireExtension_add hb.star,
      map_add]
  map_smul' c a := by
    simp only [SetLike.val_smul, star_smul, entireExtension_smul, map_smul, RCLike.star_def]

/-- On entire analytic elements, `preModularConjugation` reverses inner products. -/
private theorem inner_preModularConjugation (hω : α.IsKMSState β ω) (a b : α.entireAnalytic) :
    ⟪preModularConjugation α β ω.toPositiveLinearMap a,
        preModularConjugation α β ω.toPositiveLinearMap b⟫_ℂ =
      ⟪ω.toPositiveLinearMap.toGNS (b : A), ω.toPositiveLinearMap.toGNS (a : A)⟫_ℂ := by
  have ha := mem_entireAnalytic.mp a.property; have hb := mem_entireAnalytic.mp b.property
  have hstar : star (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) =
      α.entireExtension (a : A) (-((β / 2 : ℝ) * I)) := by
    simp only [entireExtension_star, star_star, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_neg]
  have hshift : α.entireExtension (star (b : A)) ((β / 2 : ℝ) * I) =
      α.entireExtension (α.entireExtension (star (b : A)) (-((β / 2 : ℝ) * I))) (β * I) := by
    rw [entireExtension_entireExtension]; congr 1; push_cast; ring
  have hinv : ω (α.entireExtension (star (b : A) * (a : A)) (-((β / 2 : ℝ) * I))) =
      ω (star (b : A) * (a : A)) := by
    rcases eq_or_ne β 0 with rfl | hβ
    · simp [(hb.star.mul ha).entireExtension_apply_zero]
    · exact hω.apply_entireExtension hβ (hb.star.mul ha) _
  simp only [preModularConjugation, LinearMap.coe_mk, AddHom.coe_mk, toGNS_apply,
    UniformSpace.Completion.inner_coe, preGNS_inner_def, ofPreGNS_toPreGNS,
    PositiveContinuousLinearMap.coe_toPositiveLinearMap]
  rw [hstar, hshift,
    hω.apply_mul_entireExtension_mul_I _ (isEntireAnalytic_entireExtension α (star (b : A)) _),
    ← hb.star.entireExtension_mul ha, hinv]

/-- On entire analytic elements, `preModularConjugation` preserves GNS norms. -/
private theorem norm_preModularConjugation (hω : α.IsKMSState β ω) (a : α.entireAnalytic) :
    ‖preModularConjugation α β ω.toPositiveLinearMap a‖ =
      ‖ω.toPositiveLinearMap.toGNS (a : A)‖ := by
  have hsq : ‖preModularConjugation α β ω.toPositiveLinearMap a‖ ^ 2 =
      ‖ω.toPositiveLinearMap.toGNS (a : A)‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using
      congrArg Complex.re (inner_preModularConjugation hω a a)
  nlinarith [norm_nonneg (preModularConjugation α β ω.toPositiveLinearMap a),
    norm_nonneg (ω.toPositiveLinearMap.toGNS (a : A))]

/-- The conjugate-linear isometry extending `preModularConjugation` to `H_ω`. -/
private def modularConjugationIsometry (hω : α.IsKMSState β ω) :
    ω.toPositiveLinearMap.GNS →ₛₗᵢ[starRingEnd ℂ] ω.toPositiveLinearMap.GNS :=
  (preModularConjugation α β ω.toPositiveLinearMap).extendOfIsometry
    (e := ω.toPositiveLinearMap.toGNS.toLinearMap.comp α.entireAnalytic.toSubmodule.subtype)
    (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap) (norm_preModularConjugation hω)

private theorem modularConjugationIsometry_apply_toGNS (hω : α.IsKMSState β ω) {a : A}
    (ha : α.IsEntireAnalytic a) :
    modularConjugationIsometry hω (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (α.entireExtension (star a) ((β / 2 : ℝ) * I)) :=
  LinearMap.extendOfIsometry_eq _ _ _ (⟨a, mem_entireAnalytic.mpr ha⟩ : α.entireAnalytic)

private theorem modularConjugationIsometry_involutive (hω : α.IsKMSState β ω)
    (v : ω.toPositiveLinearMap.GNS) :
    modularConjugationIsometry hω (modularConjugationIsometry hω v) = v := by
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on v
    (isClosed_eq (by fun_prop) continuous_id) fun a => ?_
  have ha := mem_entireAnalytic.mp a.property
  rw [modularConjugationIsometry_apply_toGNS hω ha,
    modularConjugationIsometry_apply_toGNS hω (isEntireAnalytic_entireExtension α _ _)]
  simp only [entireExtension_star, star_star, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, entireExtension_entireExtension, neg_add_cancel, ha.entireExtension_apply_zero]

/-- The **modular conjugation** `J₀` of a β-KMS state `ω`: the unique antiunitary involution on
the GNS Hilbert space satisfying `J₀ [a] = [α_{iβ/2}(a⋆)]` for every entire analytic `a`. -/
def IsKMSState.modularConjugation (hω : α.IsKMSState β ω) :
    ω.toPositiveLinearMap.GNS ≃ₗᵢ⋆[ℂ] ω.toPositiveLinearMap.GNS where
  toLinearEquiv :=
    { toLinearMap := (modularConjugationIsometry hω).toLinearMap
      invFun := modularConjugationIsometry hω
      left_inv := modularConjugationIsometry_involutive hω
      right_inv := modularConjugationIsometry_involutive hω }
  norm_map' := (modularConjugationIsometry hω).norm_map

/-- On classes of entire analytic elements, `J₀ [a] = [α_{iβ/2}(a⋆)]`. -/
theorem IsKMSState.modularConjugation_apply_toGNS (hω : α.IsKMSState β ω) {a : A}
    (ha : α.IsEntireAnalytic a) :
    hω.modularConjugation (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (α.entireExtension (star a) ((β / 2 : ℝ) * I)) :=
  modularConjugationIsometry_apply_toGNS hω ha

/-- The modular conjugation is an involution: `J₀ (J₀ v) = v`. -/
@[simp] theorem IsKMSState.modularConjugation_modularConjugation (hω : α.IsKMSState β ω)
    (v : ω.toPositiveLinearMap.GNS) :
    hω.modularConjugation (hω.modularConjugation v) = v :=
  modularConjugationIsometry_involutive hω v

/-- The modular conjugation is its own inverse. -/
@[simp] theorem IsKMSState.modularConjugation_symm (hω : α.IsKMSState β ω) :
    hω.modularConjugation.symm = hω.modularConjugation := by
  ext v
  exact hω.modularConjugation.symm_apply_eq.mpr
    (hω.modularConjugation_modularConjugation v).symm

/-- **Antiunitarity of the modular conjugation:** `⟪J₀ u, J₀ v⟫ = ⟪v, u⟫`. -/
theorem IsKMSState.inner_modularConjugation (hω : α.IsKMSState β ω)
    (u v : ω.toPositiveLinearMap.GNS) :
    ⟪hω.modularConjugation u, hω.modularConjugation v⟫_ℂ = ⟪v, u⟫_ℂ := by
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun b => ?_
  rw [hω.modularConjugation_apply_toGNS (mem_entireAnalytic.mp a.property),
    hω.modularConjugation_apply_toGNS (mem_entireAnalytic.mp b.property)]
  exact inner_preModularConjugation hω a b

/-- Moving the modular conjugation across an inner product reverses the entries:
`⟪u, J₀ v⟫ = ⟪v, J₀ u⟫`. -/
theorem IsKMSState.inner_modularConjugation_right (hω : α.IsKMSState β ω)
    (u v : ω.toPositiveLinearMap.GNS) :
    ⟪u, hω.modularConjugation v⟫_ℂ = ⟪v, hω.modularConjugation u⟫_ℂ := by
  simpa using hω.inner_modularConjugation (hω.modularConjugation u) v

/-- Moving the modular conjugation across an inner product on the left:
`⟪J₀ u, v⟫ = ⟪J₀ v, u⟫`. -/
theorem IsKMSState.inner_modularConjugation_left (hω : α.IsKMSState β ω)
    (u v : ω.toPositiveLinearMap.GNS) :
    ⟪hω.modularConjugation u, v⟫_ℂ = ⟪hω.modularConjugation v, u⟫_ℂ := by
  simpa using hω.inner_modularConjugation u (hω.modularConjugation v)

/-- At `β = 0` (tracial states), the modular conjugation acts on every class by
`J₀ [a] = [a⋆]`. -/
theorem IsKMSState.modularConjugation_apply_toGNS_of_zero (hω : α.IsKMSState 0 ω) (a : A) :
    hω.modularConjugation (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (star a) := by
  refine congrFun (Continuous.ext_on α.dense_entireAnalytic
    (hω.modularConjugation.continuous.comp ω.toPositiveLinearMap.toGNS.continuous)
    (ω.toPositiveLinearMap.toGNS.continuous.comp continuous_star) fun b hb => ?_) a
  simpa [(mem_entireAnalytic.mp hb).star.entireExtension_apply_zero] using
    hω.modularConjugation_apply_toGNS (mem_entireAnalytic.mp hb)

/-- For `β ≠ 0`, the modular conjugation commutes with the GNS implementing unitary group. -/
theorem IsKMSState.modularConjugation_gnsImplementingGroup (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) (t : Multiplicative ℝ) (v : ω.toPositiveLinearMap.GNS) :
    hω.modularConjugation (α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t v) =
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t (hω.modularConjugation v) := by
  have hinv : ∀ s a, ω.toPositiveLinearMap (α s a) = ω.toPositiveLinearMap a :=
    fun s a => hω.apply_action hβ s a
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.property; set r : ℝ := Multiplicative.toAdd t
  rw [show t = Multiplicative.ofAdd r from (ofAdd_toAdd t).symm]
  have hU_toGNS (x : A) :
      α.gnsImplementingGroup hinv (.ofAdd r) (ω.toPositiveLinearMap.toGNS x) =
        ω.toPositiveLinearMap.toGNS (α (.ofAdd r) x) := by simp [toGNS_apply]
  rw [hU_toGNS, hω.modularConjugation_apply_toGNS (ha.apply r),
    hω.modularConjugation_apply_toGNS ha, hU_toGNS, ← map_star, entireExtension_action,
    ← entireExtension_add_ofReal, add_comm]

/-! ### Conjugation of bounded operators by `J₀` -/

/-- On classes of entire analytic elements, `J₀ π_ω(b) J₀` acts by right multiplication by
`α_{iβ/2}(b⋆)`. -/
theorem IsKMSState.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS
    (hω : α.IsKMSState β ω) {a b : A} (ha : α.IsEntireAnalytic a)
    (hb : α.IsEntireAnalytic b) :
    hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom b)
        (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (a * α.entireExtension (star b) ((β / 2 : ℝ) * I)) := by
  let f := ω.toPositiveLinearMap
  rw [LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm,
    hω.modularConjugation_apply_toGNS ha,
    show f.gnsNonUnitalStarAlgHom b (f.toGNS (α.entireExtension (star a) ((β / 2 : ℝ) * I))) =
      f.toGNS (b * α.entireExtension (star a) ((β / 2 : ℝ) * I)) by
      simp [toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe],
    hω.modularConjugation_apply_toGNS (hb.mul (isEntireAnalytic_entireExtension α _ _)),
    star_mul, entireExtension_star, star_star, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, (isEntireAnalytic_entireExtension α a _).entireExtension_mul hb.star,
    entireExtension_entireExtension, neg_add_cancel, ha.entireExtension_apply_zero]

/-- For every `b : A`, the operator `J₀ π_ω(b) J₀` lies in the commutant `M_ω'`. -/
theorem IsKMSState.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_mem_commutant
    (hω : α.IsKMSState β ω) (b : A) :
    hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom b) ∈
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant := by
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom
  have hcont_conj : Continuous fun x : A => hω.modularConjugation.conjOperator (ρ x) :=
    hω.modularConjugation.conjOperator.continuous.comp (map_continuous ρ)
  have hcomm_entire {b c : A} (hb : α.IsEntireAnalytic b) (hc : α.IsEntireAnalytic c) :
      ρ c * hω.modularConjugation.conjOperator (ρ b) =
        hω.modularConjugation.conjOperator (ρ b) * ρ c := by
    ext v; refine (denseRange_toGNS_entireAnalytic α f).induction_on v
      (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    have ha := mem_entireAnalytic.mp a.property
    have hρ (x y : A) : ρ x (f.toGNS y) = f.toGNS (x * y) := by
      simp [ρ, toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
    simp only [mul_apply_eq_comp]
    rw [hρ c (a : A),
      hω.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS ha hb,
      hω.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS (hc.mul ha) hb,
      hρ, mul_assoc]
  refine f.mem_gnsVonNeumannAlgebra_commutant_iff.mpr fun c => ?_
  have hfor_b {b : A} (hb : α.IsEntireAnalytic b) :
      ρ c * hω.modularConjugation.conjOperator (ρ b) =
        hω.modularConjugation.conjOperator (ρ b) * ρ c :=
    congrFun (Continuous.ext_on α.dense_entireAnalytic
      ((map_continuous ρ).mul continuous_const) (continuous_const.mul (map_continuous ρ))
      fun _ hx => hcomm_entire hb (mem_entireAnalytic.mp hx)) c
  exact congrFun (Continuous.ext_on α.dense_entireAnalytic
    (continuous_const.mul hcont_conj) (hcont_conj.mul continuous_const)
    fun _ hx => hfor_b (mem_entireAnalytic.mp hx)) b

/-- **Tomita commutation (`J₀ M J₀ ⊆ M'`).** Conjugating any operator in the GNS von Neumann
algebra `M_ω = π_ω(A)''` by the modular conjugation `J₀` yields an operator in `M_ω'`. -/
theorem IsKMSState.conjOperator_modularConjugation_mem_commutant (hω : α.IsKMSState β ω)
    {x : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hx : x ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra) :
    hω.modularConjugation.conjOperator x ∈
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant := by
  let f := ω.toPositiveLinearMap
  refine f.mem_gnsVonNeumannAlgebra_commutant_iff.mpr fun a => ?_
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp
    (hω.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_mem_commutant a) x hx
  have h := congrArg hω.modularConjugation.conjOperator hc
  have hinvol (T : f.GNS →L[ℂ] f.GNS) :
      hω.modularConjugation.conjOperator (hω.modularConjugation.conjOperator T) = T := by
    simpa only [LinearIsometryEquiv.conjOperator_symm, hω.modularConjugation_symm] using
      hω.modularConjugation.conjOperator.symm_apply_apply T
  rw [LinearIsometryEquiv.conjOperator_mul, LinearIsometryEquiv.conjOperator_mul, hinvol] at h
  exact h.symm

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- The modular conjugation fixes the canonical GNS vector `Ω = [1]`. -/
@[simp]
theorem IsKMSState.modularConjugation_gnsVector (hω : α.IsKMSState β ω) :
    hω.modularConjugation ω.toPositiveLinearMap.gnsVector = ω.toPositiveLinearMap.gnsVector := by
  simpa [gnsVector_def, toGNS_apply] using
    hω.modularConjugation_apply_toGNS (isEntireAnalytic_one α)

end Unital

end TauCeti.CStarAction
