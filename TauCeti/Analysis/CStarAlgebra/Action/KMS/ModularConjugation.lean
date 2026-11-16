/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.GNS
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
import TauCeti.RepresentationTheory.Continuous.Unitary.StronglyContinuous

/-!
# The modular conjugation of a KMS state and Tomita commutation

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`, and let `ω`
be a β-KMS state of `α` for some real `β`, with GNS Hilbert space `H_ω`, GNS representation `π_ω`,
and classes `[a]`. On the dense subspace of classes of entire analytic elements, the formula

`J₀ [a] = [α_{iβ/2}(a⋆)]`

defines a conjugate-linear isometry satisfying `⟪J₀ [a], J₀ [b]⟫ = ⟪[b], [a]⟫`, as a consequence
of the analytic KMS identity and complex-time invariance (or the trace property when `β = 0`).
It therefore extends uniquely to an antiunitary involution `J₀ : H_ω ≃ₗᵢ⋆[ℂ] H_ω`, defined here
as `TauCeti.CStarAction.IsKMSState.modularConjugation`.

Conjugating bounded operators by `J₀` gives the conjugate-linear isometric involution
`TauCeti.CStarAction.IsKMSState.conjModularConjugation`, `T ↦ J₀ T J₀`. On `π_ω(A)` it acts as
right multiplication on entire classes, so `J₀ π_ω(a) J₀` lies in the commutant `M' = π_ω(A)'`
and `J₀ M J₀ ⊆ M'` for the von Neumann algebra `M = π_ω(A)''`,
`TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_centralizer`.

When `A` is unital with cyclic GNS vector `Ω = [1]`, `J₀` fixes `Ω`, and conversely for every
`R ∈ M'`, the conjugate `J₀ R J₀` lies in `M = π_ω(A)''`,
`TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin`. For `β = 0`, `J₀ (R Ω) = R⋆ Ω`
holds directly for all `R ∈ M'`. For `β ≠ 0`, `ω` is invariant with strongly continuous
implementing unitary group `U_t` commuting with `J₀`; every `R ∈ M'` is approximated strongly by
operator-norm entire Gaussian smearings in `M'`, on which analytic continuation gives
`J₀ (S(0) Ω) = S(iβ/2)⋆ Ω` and hence commutation of `J₀ R J₀` with `M'`.

## Main definitions

* `TauCeti.CStarAction.IsKMSState.modularConjugation`: the antiunitary involution `J₀` on the
  GNS Hilbert space of a β-KMS state.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation`: conjugation `T ↦ J₀ T J₀` of bounded
  operators by `J₀`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_toGNS`: `J₀ [a] = [α_{iβ/2}(a⋆)]` for
  entire analytic `a`.
* `TauCeti.CStarAction.IsKMSState.inner_modularConjugation`: `⟪J₀ u, J₀ v⟫ = ⟪v, u⟫`.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_centralizer`: `J₀ M J₀ ⊆ M'`.
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin`: `J₀ M' J₀ ⊆ M` (unital).
* `TauCeti.CStarAction.IsKMSState.conjModularConjugation_mem_adjoin_iff`: `J₀ T J₀ ∈ M ↔ T ∈ M'`.
* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_zero` and
  `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_commute`: `J₀ (R Ω) = R⋆ Ω`
  for `R ∈ M'` when `β = 0` or when `R` commutes with the implementing unitary group.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Section 5.3.1 and Theorem 5.3.30.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory PositiveLinearMap Real Topology
open scoped ComplexConjugate ComplexOrder Convolution CStarAlgebra InnerProductSpace Pointwise

namespace TauCeti.CStarAction

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-! ### Construction of the modular conjugation -/

/-- The classes of entire analytic elements are dense in the GNS Hilbert space. -/
theorem denseRange_toGNS_entireAnalytic (α : CStarAction (Multiplicative ℝ) A)
    (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : α.entireAnalytic => f.toGNS (a : A)) := by
  intro v
  have hrange : Set.range (fun a : α.entireAnalytic => f.toGNS (a : A)) =
      f.toGNS '' (α.entireAnalytic : Set A) := by
    ext w
    simp
  rw [hrange]
  have hsub : Set.range f.toGNS ⊆ closure (f.toGNS '' (α.entireAnalytic : Set A)) := by
    calc
      Set.range f.toGNS = f.toGNS '' Set.univ := Set.image_univ.symm
      _ = f.toGNS '' closure (α.entireAnalytic : Set A) := by rw [α.dense_entireAnalytic.closure_eq]
      _ ⊆ closure (f.toGNS '' (α.entireAnalytic : Set A)) :=
        image_closure_subset_closure_image f.toGNS.continuous
  exact (closure_minimal hsub isClosed_closure) (f.denseRange_toGNS v)

/-- The pre-modular conjugation `[a] ↦ [α_{iβ/2}(a⋆)]` as a conjugate-linear map from the entire
analytic subalgebra into the GNS Hilbert space. -/
private def preModularConjugation (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (f : A →ₚ[ℂ] ℂ) : α.entireAnalytic →ₛₗ[starRingEnd ℂ] f.GNS where
  toFun a := f.toGNS (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))
  map_add' a b := by
    have ha := mem_entireAnalytic.mp a.2
    have hb := mem_entireAnalytic.mp b.2
    simp only [NonUnitalStarSubalgebra.coe_add, star_add, ha.star.entireExtension_add hb.star,
      map_add]
  map_smul' c a := by
    simp only [SetLike.val_smul, star_smul, entireExtension_smul, map_smul, RCLike.star_def]

/-- On entire analytic elements, `preModularConjugation` reverses inner products:
`⟪j₀ a, j₀ b⟫ = ⟪[b], [a]⟫`. -/
private theorem inner_preModularConjugation (hω : α.IsKMSState β ω) (a b : α.entireAnalytic) :
    ⟪preModularConjugation α β ω.toPositiveLinearMap a,
        preModularConjugation α β ω.toPositiveLinearMap b⟫_ℂ =
      ⟪ω.toPositiveLinearMap.toGNS (b : A), ω.toPositiveLinearMap.toGNS (a : A)⟫_ℂ := by
  have ha := mem_entireAnalytic.mp a.2
  have hb := mem_entireAnalytic.mp b.2
  have hstar : star (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) =
      α.entireExtension (a : A) (-((β / 2 : ℝ) * I)) := by
    rw [entireExtension_star, star_star]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hshift : α.entireExtension (star (b : A)) ((β / 2 : ℝ) * I) =
      α.entireExtension (α.entireExtension (star (b : A)) (-((β / 2 : ℝ) * I))) (β * I) := by
    rw [entireExtension_entireExtension]
    congr 1
    push_cast
    ring
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
    have h := congrArg Complex.re (inner_preModularConjugation hω a a)
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h
  nlinarith [norm_nonneg (preModularConjugation α β ω.toPositiveLinearMap a),
    norm_nonneg (ω.toPositiveLinearMap.toGNS (a : A))]

/-- The conjugate-linear isometry extending `preModularConjugation` to the GNS Hilbert space. -/
private def modularConjugationIsometry (hω : α.IsKMSState β ω) :
    ω.toPositiveLinearMap.GNS →ₛₗᵢ[starRingEnd ℂ] ω.toPositiveLinearMap.GNS :=
  (preModularConjugation α β ω.toPositiveLinearMap).extendOfIsometry
    (e := ω.toPositiveLinearMap.toGNS.toLinearMap.comp α.entireAnalytic.toSubmodule.subtype)
    (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap)
    (norm_preModularConjugation hω)

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
  have ha := mem_entireAnalytic.mp a.2
  rw [modularConjugationIsometry_apply_toGNS hω ha,
    modularConjugationIsometry_apply_toGNS hω (isEntireAnalytic_entireExtension α _ _)]
  congr 1
  have hstar : star (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) =
      α.entireExtension (a : A) (-((β / 2 : ℝ) * I)) := by
    rw [entireExtension_star, star_star]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hstar, entireExtension_entireExtension, neg_add_cancel, ha.entireExtension_apply_zero]

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

/-- The modular conjugation is its own inverse. -/
@[simp]
theorem IsKMSState.modularConjugation_symm (hω : α.IsKMSState β ω) :
    hω.modularConjugation.symm = hω.modularConjugation := by
  ext v
  rfl

/-- The modular conjugation is an involution: `J₀ (J₀ v) = v`. -/
@[simp]
theorem IsKMSState.modularConjugation_modularConjugation (hω : α.IsKMSState β ω)
    (v : ω.toPositiveLinearMap.GNS) :
    hω.modularConjugation (hω.modularConjugation v) = v :=
  modularConjugationIsometry_involutive hω v

/-- **Antiunitarity of the modular conjugation:** `⟪J₀ u, J₀ v⟫ = ⟪v, u⟫`. -/
theorem IsKMSState.inner_modularConjugation (hω : α.IsKMSState β ω)
    (u v : ω.toPositiveLinearMap.GNS) :
    ⟪hω.modularConjugation u, hω.modularConjugation v⟫_ℂ = ⟪v, u⟫_ℂ := by
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun b => ?_
  have ha := mem_entireAnalytic.mp a.2
  have hb := mem_entireAnalytic.mp b.2
  rw [hω.modularConjugation_apply_toGNS ha, hω.modularConjugation_apply_toGNS hb]
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

/-- At `β = 0` (tracial states), the modular conjugation acts on every class by `J₀ [a] = [a⋆]`.
-/
theorem IsKMSState.modularConjugation_apply_toGNS_of_zero (hω : α.IsKMSState 0 ω) (a : A) :
    hω.modularConjugation (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (star a) := by
  refine congrFun (Continuous.ext_on α.dense_entireAnalytic
    (hω.modularConjugation.continuous.comp ω.toPositiveLinearMap.toGNS.continuous)
    (ω.toPositiveLinearMap.toGNS.continuous.comp continuous_star) fun b hb => ?_) a
  have hb' := mem_entireAnalytic.mp hb
  simpa [hb'.star.entireExtension_apply_zero] using hω.modularConjugation_apply_toGNS hb'

/-- For `β ≠ 0`, the modular conjugation commutes with the GNS implementing unitary group. -/
theorem IsKMSState.modularConjugation_gnsImplementingGroup (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    (t : Multiplicative ℝ) (v : ω.toPositiveLinearMap.GNS) :
    hω.modularConjugation
        (α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t v) =
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t
        (hω.modularConjugation v) := by
  have hinv : ∀ s a, ω.toPositiveLinearMap (α s a) = ω.toPositiveLinearMap a :=
    fun s a => hω.apply_action hβ s a
  refine (denseRange_toGNS_entireAnalytic α ω.toPositiveLinearMap).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.2
  set r : ℝ := Multiplicative.toAdd t
  have ht : t = Multiplicative.ofAdd r := (ofAdd_toAdd t).symm
  rw [ht]
  have hta : α.IsEntireAnalytic (α (Multiplicative.ofAdd r) (a : A)) := ha.apply r
  have hU_toGNS (x : A) :
      α.gnsImplementingGroup hinv (.ofAdd r) (ω.toPositiveLinearMap.toGNS x) =
        ω.toPositiveLinearMap.toGNS (α (.ofAdd r) x) := by
    simp [toGNS_apply]
  rw [hU_toGNS, hω.modularConjugation_apply_toGNS hta, hω.modularConjugation_apply_toGNS ha,
    hU_toGNS]
  congr 1
  rw [← map_star, entireExtension_action, ← entireExtension_add_ofReal, add_comm]

/-! ### Conjugation of bounded operators by `J₀` -/

/-- Conjugation `T ↦ J₀ T J₀` of a bounded operator on `H_ω` by the modular conjugation `J₀`. -/
def IsKMSState.conjModularConjugation (hω : α.IsKMSState β ω)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS where
  toFun v := hω.modularConjugation (T (hω.modularConjugation v))
  map_add' u v := by simp
  map_smul' c v := by simp [map_smulₛₗ]
  cont := by fun_prop

/-- Evaluating `J₀ T J₀` on a vector `v`. -/
@[simp]
theorem IsKMSState.conjModularConjugation_apply (hω : α.IsKMSState β ω)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)
    (v : ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation T v = hω.modularConjugation (T (hω.modularConjugation v)) :=
  (rfl)

/-- Conjugation by `J₀` is an involution. -/
@[simp]
theorem IsKMSState.conjModularConjugation_conjModularConjugation (hω : α.IsKMSState β ω)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation (hω.conjModularConjugation T) = T := by
  ext v
  simp

/-- Conjugation by `J₀` fixes `1`. -/
@[simp]
theorem IsKMSState.conjModularConjugation_one (hω : α.IsKMSState β ω) :
    hω.conjModularConjugation 1 = 1 := by
  ext v
  simp

/-- Conjugation by `J₀` fixes `0`. -/
@[simp]
theorem IsKMSState.conjModularConjugation_zero (hω : α.IsKMSState β ω) :
    hω.conjModularConjugation 0 = 0 := by
  ext v
  simp

/-- Conjugation by `J₀` is additive. -/
@[simp]
theorem IsKMSState.conjModularConjugation_add (hω : α.IsKMSState β ω)
    (S T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation (S + T) =
      hω.conjModularConjugation S + hω.conjModularConjugation T := by
  ext v
  simp

/-- Conjugation by `J₀` is conjugate-linear. -/
@[simp]
theorem IsKMSState.conjModularConjugation_smul (hω : α.IsKMSState β ω) (c : ℂ)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation (c • T) = conj c • hω.conjModularConjugation T := by
  ext v
  simp [map_smulₛₗ]

/-- Conjugation by `J₀` is multiplicative. -/
@[simp]
theorem IsKMSState.conjModularConjugation_mul (hω : α.IsKMSState β ω)
    (S T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation (S * T) =
      hω.conjModularConjugation S * hω.conjModularConjugation T := by
  ext v
  simp

/-- Conjugation by `J₀` commutes with the operator adjoint. -/
@[simp]
theorem IsKMSState.conjModularConjugation_star (hω : α.IsKMSState β ω)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    hω.conjModularConjugation (star T) = star (hω.conjModularConjugation T) := by
  ext v
  refine ext_inner_left ℂ fun u => ?_
  simp only [conjModularConjugation_apply, star_eq_adjoint, adjoint_inner_right]
  rw [hω.inner_modularConjugation_right, adjoint_inner_left, hω.inner_modularConjugation_left]

/-- Conjugation by `J₀` preserves the operator norm. -/
@[simp]
theorem IsKMSState.norm_conjModularConjugation (hω : α.IsKMSState β ω)
    (T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
    ‖hω.conjModularConjugation T‖ = ‖T‖ := by
  have hle (S : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) :
      ‖hω.conjModularConjugation S‖ ≤ ‖S‖ :=
    opNorm_le_bound _ (norm_nonneg S) fun v => by
      simpa only [conjModularConjugation_apply, hω.modularConjugation.norm_map] using
        S.le_opNorm (hω.modularConjugation v)
  exact le_antisymm (hle T) (by simpa using hle (hω.conjModularConjugation T))

/-- On classes of entire analytic elements, `J₀ π_ω(b) J₀` acts by right multiplication by
`α_{iβ/2}(b⋆)`. -/
theorem IsKMSState.conjModularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS
    (hω : α.IsKMSState β ω) {a b : A} (ha : α.IsEntireAnalytic a) (hb : α.IsEntireAnalytic b) :
    hω.conjModularConjugation (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom b)
        (ω.toPositiveLinearMap.toGNS a) =
      ω.toPositiveLinearMap.toGNS (a * α.entireExtension (star b) ((β / 2 : ℝ) * I)) := by
  let f := ω.toPositiveLinearMap
  have hmul : α.IsEntireAnalytic (b * α.entireExtension (star a) ((β / 2 : ℝ) * I)) :=
    hb.mul (isEntireAnalytic_entireExtension α _ _)
  rw [conjModularConjugation_apply, hω.modularConjugation_apply_toGNS ha]
  have hρ : f.gnsNonUnitalStarAlgHom b (f.toGNS (α.entireExtension (star a) ((β / 2 : ℝ) * I))) =
      f.toGNS (b * α.entireExtension (star a) ((β / 2 : ℝ) * I)) := by
    simp [toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
  rw [hρ, hω.modularConjugation_apply_toGNS hmul]
  congr 1
  rw [star_mul, entireExtension_star, star_star]
  have hconj : conj ((β / 2 : ℝ) * I) = -((β / 2 : ℝ) * I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hconj, (isEntireAnalytic_entireExtension α a _).entireExtension_mul hb.star,
    entireExtension_entireExtension, neg_add_cancel, ha.entireExtension_apply_zero]

/-- For every `b : A`, the operator `J₀ π_ω(b) J₀` lies in the commutant `π_ω(A)'`. -/
theorem IsKMSState.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer
    (hω : α.IsKMSState β ω) (b : A) :
    hω.conjModularConjugation (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom b) ∈
      Set.centralizer (Set.range ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsNonUnitalStarAlgHom
  have hcont_conj : Continuous fun x : A => hω.conjModularConjugation (ρ x) := by
    refine Isometry.continuous (AddMonoidHomClass.isometry_of_norm
      ({ toFun := hω.conjModularConjugation
         map_zero' := hω.conjModularConjugation_zero
         map_add' := hω.conjModularConjugation_add } : (f.GNS →L[ℂ] f.GNS) →+ _)
      hω.norm_conjModularConjugation) |>.comp (map_continuous ρ)
  -- Check commutation first for entire analytic `b` and `c`, then extend by density.
  have hcomm_entire {b c : A} (hb : α.IsEntireAnalytic b) (hc : α.IsEntireAnalytic c) :
      ρ c * hω.conjModularConjugation (ρ b) = hω.conjModularConjugation (ρ b) * ρ c := by
    ext v
    refine (denseRange_toGNS_entireAnalytic α f).induction_on v
      (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    have ha := mem_entireAnalytic.mp a.2
    have hρ (x y : A) : ρ x (f.toGNS y) = f.toGNS (x * y) := by
      simp [ρ, toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
    have h1 := hω.conjModularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS ha hb
    have h2 := hω.conjModularConjugation_gnsNonUnitalStarAlgHom_apply_toGNS (hc.mul ha) hb
    simp only [mul_apply_eq_comp]
    rw [hρ c (a : A), h1, h2, hρ, mul_assoc]
  rintro _ ⟨c, rfl⟩
  have hfor_b {b : A} (hb : α.IsEntireAnalytic b) :
      ρ c * hω.conjModularConjugation (ρ b) = hω.conjModularConjugation (ρ b) * ρ c :=
    congrFun (Continuous.ext_on α.dense_entireAnalytic
      ((map_continuous ρ).mul continuous_const)
      (continuous_const.mul (map_continuous ρ))
      fun x hx => hcomm_entire hb (mem_entireAnalytic.mp hx)) c
  exact congrFun (Continuous.ext_on α.dense_entireAnalytic
    (continuous_const.mul hcont_conj) (hcont_conj.mul continuous_const)
    fun x hx => hfor_b (mem_entireAnalytic.mp hx)) b

/-- **Tomita commutation (`J₀ M J₀ ⊆ M'`).** Conjugating any operator in the von Neumann algebra
`π_ω(A)''` by the modular conjugation `J₀` yields an operator in the commutant `π_ω(A)'`. -/
theorem IsKMSState.conjModularConjugation_mem_centralizer (hω : α.IsKMSState β ω)
    {x : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hx : x ∈ VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom)) :
    hω.conjModularConjugation x ∈
      Set.centralizer (Set.range ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom) := by
  rw [← SetLike.mem_coe,
    ← NonUnitalStarAlgHom.coe_range ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset,
    NonUnitalStarAlgHom.coe_range] at hx
  rintro _ ⟨a, rfl⟩
  have hcomm := hx _ (hω.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer a)
  have h := congrArg hω.conjModularConjugation hcomm
  simpa using h

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- The modular conjugation fixes the canonical GNS vector `Ω = [1]`. -/
@[simp]
theorem IsKMSState.modularConjugation_gnsVector (hω : α.IsKMSState β ω) :
    hω.modularConjugation ω.toPositiveLinearMap.gnsVector = ω.toPositiveLinearMap.gnsVector := by
  have h := hω.modularConjugation_apply_toGNS (isEntireAnalytic_one α)
  simpa [gnsVector_def, toGNS_apply] using h

/-! ### The `β = 0` commutation theorem -/

/-- At `β = 0` (tracial states), `J₀ (R Ω) = R⋆ Ω` for every operator `R` in the commutant
`π_ω(A)'`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_zero (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  refine ext_inner_left ℂ fun u => ?_
  refine f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have hRstar : star R ∈ Set.centralizer (Set.range ρ) := by
    rintro _ ⟨x, rfl⟩
    have h := congrArg star (hR (ρ (star x)) ⟨star x, rfl⟩)
    simpa [star_mul, ← map_star] using h.symm
  have hcomm : ρ (star a) * star R = star R * ρ (star a) := hRstar _ ⟨star a, rfl⟩
  rw [hω.inner_modularConjugation_right, hω.modularConjugation_apply_toGNS_of_zero a]
  calc
    ⟪R f.gnsVector, f.toGNS (star a)⟫_ℂ
        = ⟪f.gnsVector, (star R) (ρ (star a) f.gnsVector)⟫_ℂ := by
          rw [star_eq_adjoint, adjoint_inner_right]
          simp [ρ, toGNS_apply]
    _ = ⟪f.gnsVector, ρ (star a) ((star R) f.gnsVector)⟫_ℂ := by
          simpa only [mul_apply_eq_comp] using congrArg (fun T => ⟪f.gnsVector, T f.gnsVector⟫_ℂ)
            hcomm.symm
    _ = ⟪f.toGNS a, (star R) f.gnsVector⟫_ℂ := by
          rw [map_star, star_eq_adjoint, adjoint_inner_right]
          simp [ρ, toGNS_apply]

/-- Tomita commutation at `β = 0`: `J₀ R J₀ ∈ π_ω(A)''` for every `R ∈ π_ω(A)'`. -/
private theorem conjModularConjugation_mem_adjoin_of_zero (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  have hrange : (f.gnsNonUnitalStarAlgHom.range : Set _) = Set.range f.gnsStarAlgHom :=
    NonUnitalStarAlgHom.coe_range f.gnsNonUnitalStarAlgHom
  rw [← SetLike.mem_coe, ← hrange,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset, hrange]
  intro R' hR'
  have hR'star : star R' ∈ Set.centralizer (Set.range ρ) := by
    rintro _ ⟨x, rfl⟩
    have h := congrArg star (hR' (ρ (star x)) ⟨star x, rfl⟩)
    simpa [star_mul, ← map_star] using h.symm
  ext v
  refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  let La := hω.conjModularConjugation (ρ a)
  have hLa : La ∈ Set.centralizer (Set.range ρ) :=
    hω.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer a
  have hprod : R * La * star R' ∈ Set.centralizer (Set.range ρ) := by
    intro S hS
    rw [mul_assoc, mul_assoc, ← mul_assoc S, hR S hS, mul_assoc R, ← mul_assoc S, hLa S hS,
      mul_assoc La, hR'star S hS]
    simp only [mul_assoc]
  have h1 : R' (f.toGNS a) = ρ a (R' f.gnsVector) := by
    have h := congrArg (fun T => T f.gnsVector) (hR' (ρ a) ⟨a, rfl⟩)
    simpa [ρ, mul_apply_eq_comp, toGNS_apply] using h.symm
  have h2 : hω.modularConjugation (R' (f.toGNS a)) = (La * star R') f.gnsVector := by
    rw [h1, mul_apply_eq_comp, ← hω.modularConjugation_apply_gnsVector_of_zero hR']
    simp [La, f]
  have h3 : (hω.conjModularConjugation R * R') (f.toGNS a) =
      hω.modularConjugation ((R * La * star R') f.gnsVector) := by
    simp only [mul_apply_eq_comp, hω.conjModularConjugation_apply, h2]
  rw [h3, hω.modularConjugation_apply_gnsVector_of_zero hprod]
  have h4 : star (R * La * star R') = R' * star La * star R := by
    simp [star_mul, mul_assoc]
  rw [h4]
  simp only [mul_apply_eq_comp]
  rw [← hω.modularConjugation_apply_gnsVector_of_zero hR]
  have hLa_star : star La = hω.conjModularConjugation (ρ (star a)) := by
    rw [← hω.conjModularConjugation_star, map_star]
  simp only [hLa_star, hω.conjModularConjugation_apply, hω.modularConjugation_modularConjugation]
  have hcommR : ρ (star a) (R f.gnsVector) = R (ρ (star a) f.gnsVector) := by
    simpa [mul_apply_eq_comp] using
      congrArg (fun T => T f.gnsVector) (hR (ρ (star a)) ⟨star a, rfl⟩)
  rw [hcommR]
  have hcls : ρ (star a) f.gnsVector = hω.modularConjugation (f.toGNS a) := by
    rw [hω.modularConjugation_apply_toGNS_of_zero a]
    simp [ρ, f, toGNS_apply]
  rw [hcls]

/-! ### Gaussian smearing of commutant operators and the `β ≠ 0` commutation theorem -/

section Nonzero

/-- Complex Gaussian kernel `(c / √π) * exp (-(c * (t - z))²)`. -/
private def smearKernel (c t : ℝ) (z : ℂ) : ℂ :=
  ((c : ℂ) / √π) * cexp (-((c : ℂ) * (t - z)) ^ 2)

/-- Complex derivative of `smearKernel c t` with respect to `z`. -/
private def smearKernelDeriv (c t : ℝ) (z : ℂ) : ℂ :=
  smearKernel c t z * (2 * (c : ℂ) ^ 2 * (t - z))

private theorem hasDerivAt_smearKernel (c t : ℝ) (z : ℂ) :
    HasDerivAt (smearKernel c t) (smearKernelDeriv c t z) z := by
  convert (Complex.hasDerivAt_cexp_neg_mul_sub_sq c t z).const_mul ((c : ℂ) / √π) using 1
  · funext w
    rfl
  · unfold smearKernelDeriv smearKernel
    ring

private theorem hasDerivAt_smearKernelDeriv (c t : ℝ) (z : ℂ) :
    HasDerivAt (smearKernelDeriv c t)
      (smearKernel c t z * (4 * (c : ℂ) ^ 4 * (t - z) ^ 2 - 2 * (c : ℂ) ^ 2)) z := by
  have h1 := hasDerivAt_smearKernel c t z
  have h2 : HasDerivAt (fun w : ℂ => 2 * (c : ℂ) ^ 2 * (t - w)) (-(2 * (c : ℂ) ^ 2)) z := by
    simpa using ((hasDerivAt_id z).const_sub (t : ℂ)).const_mul (2 * (c : ℂ) ^ 2)
  convert h1.mul h2 using 1
  · funext w
    rfl
  · unfold smearKernelDeriv
    ring

private theorem norm_smearKernel_le {c : ℝ} (t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖smearKernel c t z‖ ≤
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  rw [smearKernel, norm_mul, mul_assoc]
  gcongr
  exact Complex.norm_cexp_neg_mul_sub_sq_le c t hz

private theorem norm_smearKernelDeriv_le {c : ℝ} (t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖smearKernelDeriv c t z‖ ≤
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * (2 * c ^ 2) *
        ((|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2)) := by
  have hlin : ‖2 * (c : ℂ) ^ 2 * (t - z)‖ ≤ 2 * c ^ 2 * (|t| + D) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.norm_two]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    gcongr
  rw [smearKernelDeriv, norm_mul]
  calc
    ‖smearKernel c t z‖ * ‖2 * (c : ℂ) ^ 2 * (t - z)‖
        ≤ (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)) *
            (2 * c ^ 2 * (|t| + D)) :=
          mul_le_mul (norm_smearKernel_le t hz) hlin (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem integrable_norm_smearKernel {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Integrable fun t : ℝ => ‖smearKernel c t z‖ := by
  have hb : 0 < c ^ 2 / 2 := by positivity
  refine ((integrable_exp_neg_mul_sq hb).const_mul
    (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * ‖z‖ ^ 2))).mono'
    (Continuous.norm (by unfold smearKernel; fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_smearKernel_le t (le_refl ‖z‖)

private theorem integrable_norm_smearKernelDeriv {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Integrable fun t : ℝ => ‖smearKernelDeriv c t z‖ := by
  have hb : 0 < c ^ 2 / 2 := by positivity
  have hG : Integrable fun t : ℝ => (|t| + ‖z‖) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
    refine ((integrable_mul_exp_neg_mul_sq hb).norm.add
      ((integrable_exp_neg_mul_sq hb).const_mul ‖z‖)).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  refine (hG.const_mul (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * ‖z‖ ^ 2) * (2 * c ^ 2))).mono'
    (Continuous.norm (by unfold smearKernelDeriv smearKernel; fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_smearKernelDeriv_le t (le_refl ‖z‖)

private theorem smearKernel_taylor_bound {c : ℝ} (t : ℝ) {z₀ z : ℂ}
    (hz : z ∈ Metric.ball z₀ 1) :
    ‖smearKernel c t z - smearKernel c t z₀ - (z - z₀) * smearKernelDeriv c t z₀‖ ≤
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * (‖z₀‖ + 1) ^ 2) *
        (4 * c ^ 4 * (|t| + (‖z₀‖ + 1)) ^ 2 + 2 * c ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) *
        ‖z - z₀‖ ^ 2 := by
  set D := ‖z₀‖ + 1
  set r := ‖z - z₀‖
  set M := ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) *
    (4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)
  have hr : r < 1 := by simpa [r, Metric.mem_ball, dist_eq_norm] using hz
  have hsub : Metric.closedBall z₀ r ⊆ Metric.ball z₀ 1 :=
    Metric.closedBall_subset_ball hr
  have hD {w : ℂ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ D := by
    have hball : ‖w - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hsub hw
    calc
      ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖z₀‖ := by linarith
      _ = D := by ring
  -- Step 1: bound `‖k'(w) - k'(z₀)‖ ≤ M * r` on `closedBall z₀ r`.
  have hderiv2_le : ∀ w ∈ Metric.closedBall z₀ r, ‖deriv (smearKernelDeriv c t) w‖ ≤ M := by
    intro w hw
    rw [(hasDerivAt_smearKernelDeriv c t w).deriv, norm_mul]
    have hpoly : ‖4 * (c : ℂ) ^ 4 * (t - w) ^ 2 - 2 * (c : ℂ) ^ 2‖ ≤
        4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2 := by
      have htw : ‖(t : ℂ) - w‖ ≤ |t| + D := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact hD hw
      calc
        ‖4 * (c : ℂ) ^ 4 * (t - w) ^ 2 - 2 * (c : ℂ) ^ 2‖
            ≤ ‖4 * (c : ℂ) ^ 4 * (t - w) ^ 2‖ + ‖2 * (c : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = 4 * c ^ 4 * ‖(t : ℂ) - w‖ ^ 2 + 2 * c ^ 2 := by
          have hc4 : |c| ^ 4 = c ^ 4 := by
            have : (4 : ℕ) = 2 * 2 := rfl
            rw [this, pow_mul, pow_mul, sq_abs]
          simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hc4]
        _ ≤ 4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2 := by gcongr
    calc
      ‖smearKernel c t w‖ * ‖4 * (c : ℂ) ^ 4 * (t - w) ^ 2 - 2 * (c : ℂ) ^ 2‖
          ≤ (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)) *
              (4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2) :=
            mul_le_mul (norm_smearKernel_le t (hD hw)) hpoly (norm_nonneg _) (by positivity)
      _ = M := by ring
  have hk'_diff : ∀ w ∈ Metric.closedBall z₀ r,
      ‖smearKernelDeriv c t w - smearKernelDeriv c t z₀‖ ≤ M * r := by
    intro w hw
    have h := (convex_closedBall z₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (hasDerivAt_smearKernelDeriv c t x).differentiableAt) hderiv2_le
      (Metric.mem_closedBall_self (norm_nonneg _)) hw
    have hw_le : ‖w - z₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    exact h.trans (mul_le_mul_of_nonneg_left hw_le (by positivity))
  -- Step 2: apply the mean value inequality to `w ↦ k(w) - (w - z₀) * k'(z₀)`.
  let ψ : ℂ → ℂ := fun w => smearKernel c t w - (w - z₀) * smearKernelDeriv c t z₀
  have hψ_deriv (w : ℂ) : HasDerivAt ψ (smearKernelDeriv c t w - smearKernelDeriv c t z₀) w := by
    convert (hasDerivAt_smearKernel c t w).sub
      (((hasDerivAt_id w).sub_const z₀).mul_const (smearKernelDeriv c t z₀)) using 1
    · funext y
      simp [ψ]
    · ring
  have hz_mem : z ∈ Metric.closedBall z₀ r := by
    simp [r, Metric.mem_closedBall, dist_eq_norm]
  have hψ := (convex_closedBall z₀ r).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (hψ_deriv w).differentiableAt)
    (fun w hw => by rw [(hψ_deriv w).deriv]; exact hk'_diff w hw)
    (Metric.mem_closedBall_self (norm_nonneg _)) hz_mem
  simpa only [ψ, sub_self, zero_mul, sub_zero, sub_right_comm, sq, mul_assoc, r] using hψ

private theorem integrable_smearKernel_taylor_bound {c : ℝ} (hc : 0 < c) (D : ℝ) :
    Integrable fun t : ℝ =>
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) *
        (4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  have hb : 0 < c ^ 2 / 2 := by positivity
  have h0 : Integrable fun t : ℝ => rexp (-(c ^ 2 / 2) * t ^ 2) := integrable_exp_neg_mul_sq hb
  have h1 : Integrable fun t : ℝ => |t| * rexp (-(c ^ 2 / 2) * t ^ 2) := by
    refine (integrable_mul_exp_neg_mul_sq hb).norm.congr (ae_of_all _ fun t => ?_)
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h2 : Integrable fun t : ℝ => t ^ 2 * rexp (-(c ^ 2 / 2) * t ^ 2) := by
    refine (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).congr
      (ae_of_all _ fun t => ?_)
    simp
  have hcomb : Integrable fun t : ℝ =>
      (4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
    refine (((h2.const_mul (4 * c ^ 4)).add (h1.const_mul (8 * c ^ 4 * D))).add
      (h0.const_mul (4 * c ^ 4 * D ^ 2 + 2 * c ^ 2))).congr (ae_of_all _ fun t => ?_)
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    simp only [Pi.add_apply]
    rw [← hsq]
    ring
  simpa [mul_assoc] using hcomb.const_mul (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Orbit `t ↦ U_t (R (U_{-t} v))` of a vector under unitary conjugation by `U`. -/
private theorem continuous_unitaryConj_apply
    (U : ContRepresentation ℂ (Multiplicative ℝ) H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (v : H) :
    Continuous fun t : ℝ =>
      U (Multiplicative.ofAdd t) (R (U (Multiplicative.ofAdd (-t)) v)) := by
  have h1 : Continuous fun t : ℝ => U (Multiplicative.ofAdd (-t)) v := by
    have := (hU.continuous_inv_apply hcont v).comp continuous_ofAdd
    convert this using 1
    ext t
    rw [Function.comp_apply, ofAdd_neg]
  exact (hU.continuous_apply_prod hcont).comp
    (continuous_ofAdd.prodMk (R.continuous.comp h1))

private theorem integrable_kernel_smul_unitaryConj
    (U : ContRepresentation ℂ (Multiplicative ℝ) H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    {k : ℝ → ℂ} (hk_cont : Continuous k) (hk_int : Integrable fun t => ‖k t‖) (v : H) :
    Integrable fun t : ℝ =>
      k t • U (Multiplicative.ofAdd t) (R (U (Multiplicative.ofAdd (-t)) v)) := by
  refine (hk_int.mul_const (‖R‖ * ‖v‖)).mono'
    (hk_cont.smul (continuous_unitaryConj_apply U hU hcont R v)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_smul, hU.norm_map]
  calc
    ‖k t‖ * ‖R (U (.ofAdd (-t)) v)‖ ≤ ‖k t‖ * (‖R‖ * ‖U (.ofAdd (-t)) v‖) := by
      gcongr
      exact R.le_opNorm _
    _ = ‖k t‖ * (‖R‖ * ‖v‖) := by rw [hU.norm_map]

variable [CompleteSpace H]

/-- Strong Bochner integral operator `v ↦ ∫ t, k t • U_t R U_{-t} v`. -/
private def kernelSmearOp (U : ContRepresentation ℂ (Multiplicative ℝ) H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    (k : ℝ → ℂ) (hk_cont : Continuous k) (hk_int : Integrable fun t => ‖k t‖) :
    H →L[ℂ] H :=
  ({ toFun v := ∫ t : ℝ,
        k t • U (Multiplicative.ofAdd t) (R (U (Multiplicative.ofAdd (-t)) v))
     map_add' u v := by
       simp only [map_add, smul_add]
       exact integral_add
         (integrable_kernel_smul_unitaryConj U hU hcont R hk_cont hk_int u)
         (integrable_kernel_smul_unitaryConj U hU hcont R hk_cont hk_int v)
     map_smul' c v := by
       simp only [map_smul, smul_comm _ c, RingHom.id_apply]
       exact integral_smul c _ } : H →ₗ[ℂ] H).mkContinuous
    ((∫ t : ℝ, ‖k t‖) * ‖R‖) fun v => by
      refine (norm_integral_le_of_norm_le (hk_int.mul_const (‖R‖ * ‖v‖))
        (ae_of_all _ fun t => ?_)).trans_eq (by rw [integral_mul_const, mul_assoc])
      rw [norm_smul, hU.norm_map]
      calc
        ‖k t‖ * ‖R (U (.ofAdd (-t)) v)‖ ≤ ‖k t‖ * (‖R‖ * ‖U (.ofAdd (-t)) v‖) := by
          gcongr
          exact R.le_opNorm _
        _ = ‖k t‖ * (‖R‖ * ‖v‖) := by rw [hU.norm_map]

/-- Complex-time Gaussian smearing of an operator `R` under the unitary group `U`. -/
private def smearOp (U : ContRepresentation ℂ (Multiplicative ℝ) H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) (z : ℂ) :
    H →L[ℂ] H :=
  kernelSmearOp U hU hcont R (fun t => smearKernel c t z)
    (by unfold smearKernel; fun_prop) (integrable_norm_smearKernel hc z)

/-- The operator-norm derivative of `smearOp U hU hcont R hc`. -/
private def smearOpDeriv (U : ContRepresentation ℂ (Multiplicative ℝ) H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) (z : ℂ) :
    H →L[ℂ] H :=
  kernelSmearOp U hU hcont R (fun t => smearKernelDeriv c t z)
    (by unfold smearKernelDeriv smearKernel; fun_prop) (integrable_norm_smearKernelDeriv hc z)

/-- The Gaussian smearing `z ↦ smearOp R c z` is entire in the operator norm. -/
private theorem differentiable_smearOp (U : ContRepresentation ℂ (Multiplicative ℝ) H)
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ (smearOp U hU hcont R hc) := by
  intro z₀
  set D := ‖z₀‖ + 1
  set M : ℝ → ℝ := fun t =>
    ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) *
      (4 * c ^ 4 * (|t| + D) ^ 2 + 2 * c ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)
  have hMint : Integrable M := integrable_smearKernel_taylor_bound hc D
  set K := (∫ t, M t) * ‖R‖
  have : 0 ≤ K := mul_nonneg (integral_nonneg fun t => by positivity) (norm_nonneg R)
  have hquad : ∀ z ∈ Metric.ball z₀ 1,
      ‖smearOp U hU hcont R hc z - smearOp U hU hcont R hc z₀ -
        (z - z₀) • smearOpDeriv U hU hcont R hc z₀‖ ≤ K * ‖z - z₀‖ ^ 2 := by
    intro z hz
    refine opNorm_le_bound _ (by positivity) fun v => ?_
    have hint1 := integrable_kernel_smul_unitaryConj U hU hcont R
      (by unfold smearKernel; fun_prop) (integrable_norm_smearKernel hc z) v
    have hint2 := integrable_kernel_smul_unitaryConj U hU hcont R
      (by unfold smearKernel; fun_prop) (integrable_norm_smearKernel hc z₀) v
    have hint3 := integrable_kernel_smul_unitaryConj U hU hcont R
      (by unfold smearKernelDeriv smearKernel; fun_prop) (integrable_norm_smearKernelDeriv hc z₀) v
    have heq : (smearOp U hU hcont R hc z - smearOp U hU hcont R hc z₀ -
        (z - z₀) • smearOpDeriv U hU hcont R hc z₀) v =
        ∫ t : ℝ, (smearKernel c t z - smearKernel c t z₀ -
          (z - z₀) * smearKernelDeriv c t z₀) •
          U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
      have h1 : (fun t => (smearKernel c t z - smearKernel c t z₀ -
            (z - z₀) * smearKernelDeriv c t z₀) • U (.ofAdd t) (R (U (.ofAdd (-t)) v))) =
          fun t => (smearKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) -
            smearKernel c t z₀ • U (.ofAdd t) (R (U (.ofAdd (-t)) v))) -
            (z - z₀) • (smearKernelDeriv c t z₀ • U (.ofAdd t) (R (U (.ofAdd (-t)) v))) := by
        funext t
        rw [sub_smul, sub_smul, mul_smul]
      have hint12 : Integrable (fun t =>
          smearKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) -
            smearKernel c t z₀ • U (.ofAdd t) (R (U (.ofAdd (-t)) v))) := hint1.sub hint2
      have hint3' : Integrable (fun t =>
          (z - z₀) • smearKernelDeriv c t z₀ • U (.ofAdd t) (R (U (.ofAdd (-t)) v))) :=
        hint3.smul (z - z₀)
      symm
      rw [h1, integral_sub hint12 hint3', integral_sub hint1 hint2, integral_smul]
      rfl
    rw [heq]
    refine (norm_integral_le_of_norm_le (hMint.mul_const (‖z - z₀‖ ^ 2 * (‖R‖ * ‖v‖)))
      (ae_of_all _ fun t => ?_)).trans_eq (by rw [integral_mul_const]; ring)
    rw [norm_smul, hU.norm_map]
    calc
      ‖smearKernel c t z - smearKernel c t z₀ - (z - z₀) * smearKernelDeriv c t z₀‖ *
          ‖R (U (.ofAdd (-t)) v)‖
          ≤ (M t * ‖z - z₀‖ ^ 2) * (‖R‖ * ‖v‖) := by
            refine mul_le_mul (smearKernel_taylor_bound t hz) ?_ (norm_nonneg _) (by positivity)
            simpa only [hU.norm_map] using R.le_opNorm (U (.ofAdd (-t)) v)
      _ = M t * (‖z - z₀‖ ^ 2 * (‖R‖ * ‖v‖)) := by ring
  refine HasDerivAt.differentiableAt (f' := smearOpDeriv U hU hcont R hc z₀) ?_
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  refine Metric.eventually_nhds_iff.mpr ⟨min 1 (ε / (K + 1)), by positivity, fun z hz => ?_⟩
  have hball : z ∈ Metric.ball z₀ 1 :=
    Metric.mem_ball.mpr (hz.trans_le (min_le_left _ _))
  have hle : ‖z - z₀‖ ≤ ε / (K + 1) := by
    rw [← dist_eq_norm]
    exact (hz.trans_le (min_le_right _ _)).le
  calc
    ‖smearOp U hU hcont R hc z - smearOp U hU hcont R hc z₀ -
        (z - z₀) • smearOpDeriv U hU hcont R hc z₀‖
        ≤ K * ‖z - z₀‖ ^ 2 := hquad z hball
    _ = (K * ‖z - z₀‖) * ‖z - z₀‖ := by ring
    _ ≤ ε * ‖z - z₀‖ := by
      gcongr
      calc
        K * ‖z - z₀‖ ≤ K * (ε / (K + 1)) := by gcongr
        _ ≤ (K + 1) * (ε / (K + 1)) := by gcongr; linarith
        _ = ε := mul_div_cancel₀ ε (by positivity)

/-- At real time `s`, `smearOp R c s = U_s * smearOp R c 0 * U_{-s}`. -/
private theorem smearOp_ofReal (U : ContRepresentation ℂ (Multiplicative ℝ) H)
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    {c : ℝ} (hc : 0 < c) (s : ℝ) :
    smearOp U hU hcont R hc s =
      U (.ofAdd s) * smearOp U hU hcont R hc 0 * U (.ofAdd (-s)) := by
  ext v
  simp only [mul_apply_eq_comp, smearOp, kernelSmearOp, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [← (U (.ofAdd s)).integral_comp_comm
    (integrable_kernel_smul_unitaryConj U hU hcont R (by unfold smearKernel; fun_prop)
      (integrable_norm_smearKernel hc 0) (U (.ofAdd (-s)) v)),
    ← integral_add_right_eq_self _ s]
  congr 1 with u
  rw [map_smul]
  congr 1
  · simp only [smearKernel, sub_zero]
    push_cast
    ring_nf
  · have hm1 : U (.ofAdd s) * U (.ofAdd u) = U (.ofAdd (u + s)) := by
      rw [← map_mul, ← ofAdd_add, add_comm]
    have hm2 : U (.ofAdd (-u)) * U (.ofAdd (-s)) = U (.ofAdd (-(u + s))) := by
      rw [← map_mul, ← ofAdd_add, neg_add]
    calc
      U (.ofAdd (u + s)) (R (U (.ofAdd (-(u + s))) v))
          = (U (.ofAdd s) * U (.ofAdd u)) (R ((U (.ofAdd (-u)) * U (.ofAdd (-s))) v)) := by
            rw [hm1, hm2]
      _ = U (.ofAdd s) (U (.ofAdd u) (R (U (.ofAdd (-u)) (U (.ofAdd (-s)) v)))) := by
            simp only [mul_apply_eq_comp]

/-- At `z = 0`, `smearOp R c 0` converges strongly to `R` as `c → ∞`. -/
private theorem tendsto_smearOp_zero (U : ContRepresentation ℂ (Multiplicative ℝ) H)
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (v : H) :
    Tendsto (fun c : ℝ =>
      ∫ t : ℝ, gaussianDensity c t • U (.ofAdd t) (R (U (.ofAdd (-t)) v)))
      atTop (𝓝 (R v)) := by
  let g : ℝ → H := fun u => U (.ofAdd (-u)) (R (U (.ofAdd u) v))
  have hg : Continuous g :=
    (hU.continuous_apply_prod hcont).comp
      ((continuous_ofAdd.comp continuous_neg).prodMk
        (R.continuous.comp ((hcont v).comp continuous_ofAdd)))
  have hpow : Tendsto (fun c : ℝ => c ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : 2 ≠ 0)
  have htime : Tendsto (fun c : ℝ => 4 * c ^ 2) atTop atTop :=
    hpow.const_mul_atTop (by norm_num : 0 < (4 : ℝ))
  have ht₀ : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝 0) := by
    simpa only [one_div] using! htime.inv_tendsto_atTop
  have ht : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht₀, (eventually_gt_atTop 0).mono fun c hc =>
      Set.mem_Ioi.mpr (by positivity)⟩
  have hbdd : ∀ᵐ u : ℝ, ‖g u‖ ≤ ‖R‖ * ‖v‖ := ae_of_all _ fun u => by
    simp only [g, hU.norm_map]
    simpa only [hU.norm_map] using R.le_opNorm (U (.ofAdd u) v)
  have hlim := (tendsto_heatKernel_convolution hg.aestronglyMeasurable hbdd
    (x₀ := 0) hg.continuousAt).comp (ht.prodMk tendsto_const_nhds)
  have hg₀ : g 0 = R v := by simp [g]
  rw [hg₀] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
  have hvariance : 4 * π * (1 / (4 * c ^ 2)) = π / c ^ 2 := by field_simp
  have hexponent (t : ℝ) : -t ^ 2 / (4 * (1 / (4 * c ^ 2))) = -(c * t) ^ 2 := by field_simp
  have hkernel (t : ℝ) : heatKernel (1 / (4 * c ^ 2)) t = gaussianDensity c t := by
    rw [heatKernel_apply]
    simp only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs]
    rw [neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hvariance,
      Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le, hexponent, gaussianDensity_def]
    simp only [inv_div]
    ring
  simp only [Function.comp_apply, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    hkernel, g, neg_neg]

omit [CompleteSpace H] in
private theorem smearOp_zero_apply (U : ContRepresentation ℂ (Multiplicative ℝ) H)
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    {c : ℝ} (hc : 0 < c) (v : H) :
    smearOp U hU hcont R hc 0 v =
      ∫ t : ℝ, gaussianDensity c t • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  simp only [smearOp, kernelSmearOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1 with t
  rw [smearKernel, gaussianDensity_def, ← Complex.coe_smul]
  congr 1
  push_cast
  ring_nf

/-- An analytic family in the GNS commutant for `β ≠ 0`: an entire operator-valued function whose
values lie in `π_ω(A)'` and whose restriction to `ℝ` is conjugation by `U_t`. -/
private structure IsAnalyticCommutantFamily (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    (S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)) : Prop where
  differentiable : Differentiable ℂ S
  mem_centralizer (z : ℂ) :
    S z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)
  apply_ofReal (t : ℝ) :
    S t = α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) (.ofAdd t) * S 0 *
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) (.ofAdd (-t))

/-- Real time translation of an analytic commutant family conjugates at every complex time. -/
private theorem IsAnalyticCommutantFamily.add_ofReal {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) (w : ℂ) (t : ℝ) :
    S (w + t) =
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) (.ofAdd t) * S w *
        α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) (.ofAdd (-t)) := by
  let U := α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
  have h1 : Differentiable ℂ fun z : ℂ => S (z + t) :=
    hS.differentiable.comp (differentiable_id.add_const (t : ℂ))
  have h2 : Differentiable ℂ fun z : ℂ => U (.ofAdd t) * S z * U (.ofAdd (-t)) :=
    ((differentiable_const (U (.ofAdd t))).mul hS.differentiable).mul (differentiable_const _)
  refine congrFun (h1.eq_of_ofReal_eq h2 fun s => ?_) w
  rw [← Complex.ofReal_add, hS.apply_ofReal (s + t), hS.apply_ofReal s]
  have hm1 : U (.ofAdd (s + t)) = U (.ofAdd t) * U (.ofAdd s) := by
    rw [add_comm, ofAdd_add, map_mul]
  have hm2 : U (.ofAdd (-(s + t))) = U (.ofAdd (-s)) * U (.ofAdd (-t)) := by
    rw [neg_add, ofAdd_add, map_mul]
  dsimp only [U] at hm1 hm2 ⊢
  rw [hm1, hm2]
  simp only [mul_assoc]

/-- **Key identity for analytic commutant families:** `J₀ (S 0 Ω) = (S (iβ/2))⋆ Ω`. -/
private theorem IsAnalyticCommutantFamily.modularConjugation_apply_gnsVector
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) :
    hω.modularConjugation (S 0 ω.toPositiveLinearMap.gnsVector) =
      (star (S ((β / 2 : ℝ) * I))) ω.toPositiveLinearMap.gnsVector := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  have hinv : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
  let U := α.gnsImplementingGroup hinv
  have hU := α.isUnitary_gnsImplementingGroup hinv
  have hUΩ (r : ℝ) : U (.ofAdd r) f.gnsVector = f.gnsVector := by
    simp [U, gnsVector_def]
  have hstar_U (r : ℝ) : star (U (.ofAdd r)) = U (.ofAdd (-r)) := by
    rw [star_eq_adjoint, hU.adjoint_eq_inv, ofAdd_neg]
  let T : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z => star (S (conj z))
  have hT_diff : Differentiable ℂ T := fun z => by
    simpa [T, Function.comp_def] using (hS.differentiable (conj z)).star_conj
  refine ext_inner_left ℂ fun u => ?_
  refine (denseRange_toGNS_entireAnalytic α f).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.2
  -- Compare the two entire scalar functions `z ↦ ⟪[a], T z Ω⟫` and `z ↦ ⟪S 0 Ω, [α_{-z}(a⋆)]⟫`.
  let F : ℂ → ℂ := fun z => ⟪f.toGNS (a : A), T z f.gnsVector⟫_ℂ
  let G : ℂ → ℂ := fun z => ⟪S 0 f.gnsVector, f.toGNS (α.entireExtension (star (a : A)) (-z))⟫_ℂ
  have hF : Differentiable ℂ F :=
    ((innerSL ℂ (f.toGNS (a : A))).comp
      (ContinuousLinearMap.apply ℂ f.GNS f.gnsVector)).differentiable.comp hT_diff
  have hG : Differentiable ℂ G :=
    ((innerSL ℂ (S 0 f.gnsVector)).comp f.toGNS).differentiable.comp
      ((differentiable_entireExtension α (star (a : A))).comp differentiable_neg)
  have hFG : F = G := hF.eq_of_ofReal_eq hG fun t => by
    have hTt : T t = U (.ofAdd t) * star (S 0) * U (.ofAdd (-t)) := by
      dsimp only [U] at hstar_U ⊢
      simp only [T, Complex.conj_ofReal, hS.apply_ofReal t, star_mul, hstar_U, neg_neg, mul_assoc]
    have hcomm : ρ (α (.ofAdd (-t)) (a : A)) * S 0 = S 0 * ρ (α (.ofAdd (-t)) (a : A)) :=
      hS.mem_centralizer 0 _ ⟨_, rfl⟩
    simp only [F, G, hTt, mul_apply_eq_comp, hUΩ]
    have h1 : ⟪f.toGNS (a : A), U (.ofAdd t) ((star (S 0)) f.gnsVector)⟫_ℂ =
        ⟪U (.ofAdd (-t)) (f.toGNS (a : A)), (star (S 0)) f.gnsVector⟫_ℂ := by
      rw [← hstar_U t]
      exact (adjoint_inner_left (U (.ofAdd t)) _ _).symm
    rw [h1, star_eq_adjoint, adjoint_inner_right]
    have h2 : U (.ofAdd (-t)) (f.toGNS (a : A)) = ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector := by
      simp [U, ρ, toGNS_apply]
    rw [h2]
    have h3 : S 0 (ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector) =
        ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector) := by
      simpa [mul_apply_eq_comp] using congrArg (fun X => X f.gnsVector) hcomm.symm
    rw [h3]
    have h4 : ⟪ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector), f.gnsVector⟫_ℂ =
        ⟪S 0 f.gnsVector, ρ (star (α (.ofAdd (-t)) (a : A))) f.gnsVector⟫_ℂ := by
      rw [map_star, star_eq_adjoint, adjoint_inner_right]
    rw [h4]
    congr 1
    rw [← map_star (α (.ofAdd (-t))) (a : A), ← Complex.ofReal_neg,
      ha.star.entireExtension_ofReal (-t)]
    simp [ρ, toGNS_apply]
  have heval := congrFun hFG (-((β / 2 : ℝ) * I))
  have hconj : conj (-((β / 2 : ℝ) * I)) = (β / 2 : ℝ) * I := by
    rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  simp only [F, G, T, hconj, neg_neg] at heval
  rw [← hω.modularConjugation_apply_toGNS ha, hω.inner_modularConjugation_right] at heval
  exact heval.symm

/-- Product of two analytic commutant families. -/
private theorem IsAnalyticCommutantFamily.mul {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S₁ S₂ : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (h₁ : IsAnalyticCommutantFamily hω hβ S₁) (h₂ : IsAnalyticCommutantFamily hω hβ S₂) :
    IsAnalyticCommutantFamily hω hβ (fun z => S₁ z * S₂ z) where
  differentiable := h₁.differentiable.mul h₂.differentiable
  mem_centralizer z X hX := by
    rw [← mul_assoc, h₁.mem_centralizer z X hX, mul_assoc, h₂.mem_centralizer z X hX, ← mul_assoc]
  apply_ofReal t := by
    let U := α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
    have hcancel : U (.ofAdd (-t)) * U (.ofAdd t) = 1 := by
      rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
    rw [h₁.apply_ofReal t, h₂.apply_ofReal t]
    calc
      U (.ofAdd t) * S₁ 0 * U (.ofAdd (-t)) * (U (.ofAdd t) * S₂ 0 * U (.ofAdd (-t)))
          = U (.ofAdd t) * S₁ 0 * (U (.ofAdd (-t)) * U (.ofAdd t)) * S₂ 0 * U (.ofAdd (-t)) := by
            simp only [mul_assoc]
      _ = U (.ofAdd t) * (S₁ 0 * S₂ 0) * U (.ofAdd (-t)) := by
            rw [hcancel, mul_one]
            simp only [mul_assoc]

/-- Shifted adjoint `z ↦ (R'(conj z + iβ/2))⋆` of an analytic commutant family. -/
private theorem IsAnalyticCommutantFamily.shiftedStar {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR' : IsAnalyticCommutantFamily hω hβ R') :
    IsAnalyticCommutantFamily hω hβ (fun z => star (R' (conj z + (β / 2 : ℝ) * I))) where
  differentiable z := by
    have hW : Differentiable ℂ fun w : ℂ => R' (w + (β / 2 : ℝ) * I) :=
      hR'.differentiable.comp (differentiable_id.add_const _)
    simpa [Function.comp_def] using (hW (conj z)).star_conj
  mem_centralizer z := by
    rintro _ ⟨a, rfl⟩
    have h := congrArg star (hR'.mem_centralizer (conj z + (β / 2 : ℝ) * I) _ ⟨star a, rfl⟩)
    simpa [star_mul, ← map_star] using h.symm
  apply_ofReal t := by
    let U := α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
    have hU := α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
    have hstar_U (r : ℝ) : star (U (.ofAdd r)) = U (.ofAdd (-r)) := by
      rw [star_eq_adjoint, hU.adjoint_eq_inv, ofAdd_neg]
    have hshift := hR'.add_ofReal ((β / 2 : ℝ) * I) t
    dsimp only [U] at hstar_U
    rw [Complex.conj_ofReal, add_comm (t : ℂ), hshift, star_mul, star_mul, hstar_U, hstar_U,
      neg_neg, map_zero, zero_add]
    simp only [mul_assoc]

/-- The right-multiplication analytic commutant family `z ↦ J₀ π_ω(α_{conj z}(a)) J₀` for an
entire analytic element `a`. -/
private theorem isAnalyticCommutantFamily_rightMul (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {a : A} (ha : α.IsEntireAnalytic a) :
    IsAnalyticCommutantFamily hω hβ
      (fun z => hω.conjModularConjugation
        (ω.toPositiveLinearMap.gnsStarAlgHom (α.entireExtension a (conj z)))) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  have hinv : ∀ s x, f (α s x) = f x := fun s x => hω.apply_action hβ s x
  let U := α.gnsImplementingGroup hinv
  -- `T ↦ J₀ T⋆ J₀` is complex-linear and bounded, and `J₀ π(α_{conj z}(a)) J₀ = Φ (π (α_z(a⋆)))`.
  let Φ : (f.GNS →L[ℂ] f.GNS) →L[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    ({ toFun T := hω.conjModularConjugation (star T)
       map_add' S T := by simp
       map_smul' c T := by simp } : (f.GNS →L[ℂ] f.GNS) →ₗ[ℂ] _).mkContinuous 1
      fun T => le_of_eq (by
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [hω.norm_conjModularConjugation, star_eq_adjoint, LinearIsometryEquiv.norm_map,
          one_mul])
  let ρL : A →L[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    { toLinearMap := ρ.toLinearMap, cont := map_continuous ρ }
  refine ⟨?_, fun z => hω.conjModularConjugation_gnsNonUnitalStarAlgHom_mem_centralizer _,
    fun t => ?_⟩
  · have heq : (fun z : ℂ => hω.conjModularConjugation (ρ (α.entireExtension a (conj z)))) =
        fun z => Φ (ρL (α.entireExtension (star a) z)) := by
      have hΦ (T) : Φ T = hω.conjModularConjugation (star T) := rfl
      have hρL (x) : ρL x = ρ x := rfl
      ext z v
      have h : star (α.entireExtension (star a) z) = α.entireExtension a (conj z) := by
        rw [entireExtension_star, star_star]
      rw [hΦ, hρL, ← map_star, h]
    rw [heq]
    exact (Φ.comp ρL).differentiable.comp (differentiable_entireExtension α (star a))
  · rw [Complex.conj_ofReal, ha.entireExtension_ofReal t, map_zero, ha.entireExtension_apply_zero]
    have hcov : ρ (α (.ofAdd t) a) = U (.ofAdd t) * ρ a * U (.ofAdd (-t)) := by
      have h := (α.gnsCovariantRepresentation hinv).coefficient_action (.ofAdd t) a
      simpa [U, ρ, ofAdd_neg] using h
    have hUconj (r : ℝ) : hω.conjModularConjugation (U (.ofAdd r)) = U (.ofAdd r) := by
      ext v
      simp [U, hω.modularConjugation_gnsImplementingGroup hβ]
    rw [hcov, hω.conjModularConjugation_mul, hω.conjModularConjugation_mul, hUconj, hUconj]

/-- Gaussian smearing of a commutant operator `R ∈ π_ω(A)'` produces an analytic commutant family.
-/
private theorem isAnalyticCommutantFamily_smearOp (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom))
    {c : ℝ} (hc : 0 < c) :
    IsAnalyticCommutantFamily hω hβ
      (smearOp (α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a))
        (α.isUnitary_gnsImplementingGroup _)
        (α.continuous_gnsImplementingGroup_apply _) R hc) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  have hinv : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
  let U := α.gnsImplementingGroup hinv
  have hU := α.isUnitary_gnsImplementingGroup hinv
  have hcont := α.continuous_gnsImplementingGroup_apply hinv
  refine ⟨differentiable_smearOp U hU hcont R hc, ?_, smearOp_ofReal U hU hcont R hc⟩
  intro z
  rintro _ ⟨a, rfl⟩
  ext v
  simp only [mul_apply_eq_comp, smearOp, kernelSmearOp, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [← (ρ a).integral_comp_comm
    (integrable_kernel_smul_unitaryConj U hU hcont R (by unfold smearKernel; fun_prop)
      (integrable_norm_smearKernel hc z) v)]
  congr 1 with t
  rw [map_smul]
  congr 1
  have hcov (r : ℝ) (x : A) : U (.ofAdd r) * ρ x = ρ (α (.ofAdd r) x) * U (.ofAdd r) := by
    ext w
    simpa [U, ρ, mul_apply_eq_comp] using
      (α.gnsCovariantRepresentation hinv).covariance (.ofAdd r) x w
  have hcomm : ρ (α (.ofAdd (-t)) a) * R = R * ρ (α (.ofAdd (-t)) a) := hR _ ⟨_, rfl⟩
  have h1 : ρ a * U (.ofAdd t) = U (.ofAdd t) * ρ (α (.ofAdd (-t)) a) := by
    have := hcov t (α (.ofAdd (-t)) a)
    simpa [← CStarAction.mul_apply, ← ofAdd_add] using this.symm
  have h2 : U (.ofAdd (-t)) * ρ a = ρ (α (.ofAdd (-t)) a) * U (.ofAdd (-t)) := hcov (-t) a
  have htot : ρ a * (U (.ofAdd t) * R * U (.ofAdd (-t))) =
      (U (.ofAdd t) * R * U (.ofAdd (-t))) * ρ a := by
    calc
      ρ a * (U (.ofAdd t) * R * U (.ofAdd (-t)))
          = (ρ a * U (.ofAdd t)) * R * U (.ofAdd (-t)) := by simp only [mul_assoc]
      _ = U (.ofAdd t) * (ρ (α (.ofAdd (-t)) a) * R) * U (.ofAdd (-t)) := by
            rw [h1]; simp only [mul_assoc]
      _ = U (.ofAdd t) * R * (ρ (α (.ofAdd (-t)) a) * U (.ofAdd (-t))) := by
            rw [hcomm]; simp only [mul_assoc]
      _ = U (.ofAdd t) * R * U (.ofAdd (-t)) * ρ a := by
            rw [← h2]; simp only [mul_assoc]
  simpa [U, ρ, f, mul_apply_eq_comp] using congrArg (fun X => X v) htot

/-- For two analytic commutant families `R, R'`, `J₀ (R 0) J₀` commutes with `R' 0`. -/
private theorem commute_conjModularConjugation_of_isAnalyticCommutantFamily
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR : IsAnalyticCommutantFamily hω hβ R) (hR' : IsAnalyticCommutantFamily hω hβ R') :
    hω.conjModularConjugation (R 0) * R' 0 = R' 0 * hω.conjModularConjugation (R 0) := by
  let f := ω.toPositiveLinearMap
  let ρ := f.gnsStarAlgHom
  ext v
  refine (denseRange_toGNS_entireAnalytic α f).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.2
  let La : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z =>
    hω.conjModularConjugation (ρ (α.entireExtension (a : A) (conj z)))
  let S' : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z => star (R' (conj z + (β / 2 : ℝ) * I))
  have hLa : IsAnalyticCommutantFamily hω hβ La := isAnalyticCommutantFamily_rightMul hω hβ ha
  have hS' : IsAnalyticCommutantFamily hω hβ S' := hR'.shiftedStar
  have hS : IsAnalyticCommutantFamily hω hβ (fun z => R z * La z * S' z) :=
    (hR.mul hLa).mul hS'
  -- Evaluate `J₀ (S 0 Ω) = (S (iβ/2))⋆ Ω`.
  have hkey := hS.modularConjugation_apply_gnsVector
  -- Left-hand side equals `(J₀ (R 0) J₀) (R' 0 [a])`.
  have hlhs : hω.modularConjugation ((R 0 * La 0 * S' 0) f.gnsVector) =
      (hω.conjModularConjugation (R 0) * R' 0) (f.toGNS (a : A)) := by
    have hS'0 : S' 0 f.gnsVector = hω.modularConjugation (R' 0 f.gnsVector) := by
      simp only [S', map_zero, zero_add]
      exact hR'.modularConjugation_apply_gnsVector.symm
    have hLa0 : La 0 = hω.conjModularConjugation (ρ (a : A)) := by
      simp [La, ha.entireExtension_apply_zero]
    have hcommR' : ρ (a : A) (R' 0 f.gnsVector) = R' 0 (f.toGNS (a : A)) := by
      simpa [ρ, mul_apply_eq_comp, toGNS_apply] using
        congrArg (fun X => X f.gnsVector) (hR'.mem_centralizer 0 (ρ (a : A)) ⟨a, rfl⟩)
    simp only [mul_apply_eq_comp, hS'0, hLa0, hω.conjModularConjugation_apply,
      hω.modularConjugation_modularConjugation, hcommR']
  -- Right-hand side equals `R' 0 ((J₀ (R 0) J₀) [a])`.
  have hrhs : (star (R ((β / 2 : ℝ) * I) * La ((β / 2 : ℝ) * I) * S' ((β / 2 : ℝ) * I)))
      f.gnsVector = (R' 0 * hω.conjModularConjugation (R 0)) (f.toGNS (a : A)) := by
    have hS'val : star (S' ((β / 2 : ℝ) * I)) = R' 0 := by
      simp only [S', star_star]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_add_cancel]
    have hLaval : star (La ((β / 2 : ℝ) * I)) =
        hω.conjModularConjugation (ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))) := by
      simp only [La, ← hω.conjModularConjugation_star, ← map_star]
      congr 2
      rw [entireExtension_star]
    have hRval : (star (R ((β / 2 : ℝ) * I))) f.gnsVector =
        hω.modularConjugation (R 0 f.gnsVector) :=
      hR.modularConjugation_apply_gnsVector.symm
    have hcommR : ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) (R 0 f.gnsVector) =
        R 0 (hω.modularConjugation (f.toGNS (a : A))) := by
      rw [hω.modularConjugation_apply_toGNS ha]
      have h := hR.mem_centralizer 0
        (ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))) ⟨_, rfl⟩
      simpa [ρ, mul_apply_eq_comp, toGNS_apply] using congrArg (fun X => X f.gnsVector) h
    rw [star_mul, star_mul, hS'val, hLaval, mul_apply_eq_comp, mul_apply_eq_comp, hRval,
      hω.conjModularConjugation_apply, hω.modularConjugation_modularConjugation, hcommR]
    rfl
  rw [← hlhs, ← hrhs]
  exact hkey

/-- For `β ≠ 0`, any operator `R ∈ π_ω(A)'` commuting with the GNS implementing unitary group
satisfies `J₀ (R Ω) = R⋆ Ω`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_commute (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom))
    (hcomm : ∀ t : Multiplicative ℝ,
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t * R =
        R * α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector := by
  have hconst : IsAnalyticCommutantFamily hω hβ (fun _ => R) := by
    refine ⟨differentiable_const R, fun _ => hR, fun t => ?_⟩
    rw [hcomm (.ofAdd t), mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one,
      mul_one]
  exact hconst.modularConjugation_apply_gnsVector

/-- Tomita commutation for `β ≠ 0`: `J₀ R J₀ ∈ π_ω(A)''` for every `R ∈ π_ω(A)'`. -/
private theorem conjModularConjugation_mem_adjoin_of_ne_zero (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  let f := ω.toPositiveLinearMap
  have hinv : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
  let U := α.gnsImplementingGroup hinv
  have hU := α.isUnitary_gnsImplementingGroup hinv
  have hcont := α.continuous_gnsImplementingGroup_apply hinv
  have hrange : (f.gnsNonUnitalStarAlgHom.range : Set _) = Set.range f.gnsStarAlgHom :=
    NonUnitalStarAlgHom.coe_range f.gnsNonUnitalStarAlgHom
  rw [← SetLike.mem_coe, ← hrange,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset, hrange]
  intro R' hR'
  -- First pass `c' → ∞` for fixed `c > 0`, then `c → ∞`.
  have hsmear_tendsto (S : f.GNS →L[ℂ] f.GNS) (v : f.GNS) :
      Tendsto (fun c : ℝ =>
        ∫ t : ℝ, gaussianDensity c t • U (.ofAdd t) (S (U (.ofAdd (-t)) v)))
        atTop (𝓝 (S v)) :=
    tendsto_smearOp_zero U hU hcont S v
  have hstep1 {c : ℝ} (hc : 0 < c) :
      hω.conjModularConjugation (smearOp U hU hcont R hc 0) * R' =
        R' * hω.conjModularConjugation (smearOp U hU hcont R hc 0) := by
    ext v
    simp only [mul_apply_eq_comp]
    set T := hω.conjModularConjugation (smearOp U hU hcont R hc 0)
    have hlhs : Tendsto (fun c' : ℝ =>
        T (∫ t : ℝ, gaussianDensity c' t • U (.ofAdd t) (R' (U (.ofAdd (-t)) v))))
        atTop (𝓝 (T (R' v))) :=
      (T.continuous.tendsto _).comp (hsmear_tendsto R' v)
    have hrhs : Tendsto (fun c' : ℝ =>
        ∫ t : ℝ, gaussianDensity c' t • U (.ofAdd t) (R' (U (.ofAdd (-t)) (T v))))
        atTop (𝓝 (R' (T v))) :=
      hsmear_tendsto R' (T v)
    refine tendsto_nhds_unique (hlhs.congr' ((eventually_gt_atTop 0).mono fun c' hc' => ?_)) hrhs
    rw [← smearOp_zero_apply U hU hcont R' hc' v, ← smearOp_zero_apply U hU hcont R' hc' (T v)]
    have hcomm := commute_conjModularConjugation_of_isAnalyticCommutantFamily
      (isAnalyticCommutantFamily_smearOp hω hβ hR hc)
      (isAnalyticCommutantFamily_smearOp hω hβ hR' hc')
    simpa [T, mul_apply_eq_comp] using congrArg (fun X => X v) hcomm
  ext v
  simp only [mul_apply_eq_comp]
  have hlhs : Tendsto (fun c : ℝ =>
      hω.modularConjugation
        (∫ t : ℝ, gaussianDensity c t • U (.ofAdd t)
          (R (U (.ofAdd (-t)) (hω.modularConjugation (R' v))))))
      atTop (𝓝 (hω.conjModularConjugation R (R' v))) :=
    (hω.modularConjugation.continuous.tendsto _).comp
      (hsmear_tendsto R (hω.modularConjugation (R' v)))
  have hrhs : Tendsto (fun c : ℝ =>
      R' (hω.modularConjugation
        (∫ t : ℝ, gaussianDensity c t • U (.ofAdd t)
          (R (U (.ofAdd (-t)) (hω.modularConjugation v))))))
      atTop (𝓝 (R' (hω.conjModularConjugation R v))) :=
    ((R'.continuous.comp hω.modularConjugation.continuous).tendsto _).comp
      (hsmear_tendsto R (hω.modularConjugation v))
  refine (tendsto_nhds_unique
    (hlhs.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)) hrhs).symm
  rw [← smearOp_zero_apply U hU hcont R hc (hω.modularConjugation (R' v)),
    ← smearOp_zero_apply U hU hcont R hc (hω.modularConjugation v)]
  simpa [mul_apply_eq_comp, hω.conjModularConjugation_apply] using
    congrArg (fun X => X v) (hstep1 hc)

end Nonzero

/-! ### Tomita commutation for all `β` -/

/-- **Tomita commutation for KMS states (`J₀ M' J₀ ⊆ M`).** For every real `β` (including `β = 0`),
conjugating any operator in the commutant `π_ω(A)'` by the modular conjugation `J₀` yields an
operator in the von Neumann algebra `π_ω(A)''`. -/
theorem IsKMSState.conjModularConjugation_mem_adjoin (hω : α.IsKMSState β ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) :
    hω.conjModularConjugation R ∈
      VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · exact conjModularConjugation_mem_adjoin_of_zero hω hR
  · exact conjModularConjugation_mem_adjoin_of_ne_zero hω hβ hR

/-- Conjugation by `J₀` sends an operator into `π_ω(A)''` if and only if it lies in `π_ω(A)'`. -/
theorem IsKMSState.conjModularConjugation_mem_adjoin_iff (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.conjModularConjugation T ∈
        VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ↔
      T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) :=
  ⟨fun h => by
      have h' := hω.conjModularConjugation_mem_centralizer h
      rw [hω.conjModularConjugation_conjModularConjugation] at h'
      exact h',
    hω.conjModularConjugation_mem_adjoin⟩

/-- Conjugation by `J₀` sends an operator into `π_ω(A)'` if and only if it lies in `π_ω(A)''`. -/
theorem IsKMSState.conjModularConjugation_mem_centralizer_iff (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.conjModularConjugation T ∈
        Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ↔
      T ∈ VonNeumannAlgebra.adjoin (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) :=
  ⟨fun h => by simpa using hω.conjModularConjugation_mem_adjoin h,
    hω.conjModularConjugation_mem_centralizer⟩

end Unital

end TauCeti.CStarAction
