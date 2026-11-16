/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Scalar multiplication as a linear isometry equivalence and inverse operator norms

A commuting scalar `c` of norm `1` from a normed division ring acts on a seminormed `R`-module `M`
as a linear isometry equivalence `LinearIsometryEquiv.smulLeft c hc : M ≃ₗᵢ[R] M`; for example,
multiplication by `I : ℂ` on a complex normed space viewed as a real normed space.

More generally, multiplying any continuous linear map `f : M →L[𝕜] M₂` by any commuting scalar
`c` from a normed division ring scales the operator norm of its totalized inverse by `‖c‖⁻¹`:
`‖(c • f).inverse‖ = ‖c‖⁻¹ * ‖f.inverse‖` (`ContinuousLinearMap.norm_inverse_smul`), including
when `c = 0` or `f` is not invertible.

## Main declarations

* `LinearIsometryEquiv.smulLeft`: multiplication by a unit-norm commuting scalar as a linear
  isometry equivalence.
* `ContinuousLinearMap.norm_inverse_smul`: `‖(c • f).inverse‖ = ‖c‖⁻¹ * ‖f.inverse‖`.
-/

public section

namespace LinearIsometryEquiv

variable {R S M : Type*} [Semiring R] [NormedDivisionRing S]
  [SeminormedAddCommGroup M] [Module R M] [Module S M] [NormSMulClass S M]
  [SMulCommClass R S M]

/-- Multiplication by a unit-norm commuting scalar as a linear isometry equivalence `M ≃ₗᵢ[R] M`.
For example, multiplication by `I : ℂ` on a complex normed space viewed over `ℝ`. -/
def smulLeft (c : S) (hc : ‖c‖ = 1) : M ≃ₗᵢ[R] M where
  toFun x := c • x
  invFun x := c⁻¹ • x
  map_add' x y := smul_add c x y
  map_smul' r x := by rw [RingHom.id_apply, ← smul_comm]
  left_inv x := inv_smul_smul₀ (norm_ne_zero_iff.mp (hc ▸ one_ne_zero)) x
  right_inv x := smul_inv_smul₀ (norm_ne_zero_iff.mp (hc ▸ one_ne_zero)) x
  norm_map' x := by simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, norm_smul,
    hc, one_mul]

/-- Applying `LinearIsometryEquiv.smulLeft c hc` multiplies by `c`. -/
@[simp]
theorem smulLeft_apply (c : S) (hc : ‖c‖ = 1) (x : M) :
    smulLeft (R := R) c hc x = c • x :=
  (rfl)

/-- Applying the inverse of `LinearIsometryEquiv.smulLeft c hc` multiplies by `c⁻¹`. -/
theorem smulLeft_symm_apply (c : S) (hc : ‖c‖ = 1) (x : M) :
    (smulLeft (R := R) c hc).symm x = c⁻¹ • x :=
  (rfl)

/-- The inverse of `LinearIsometryEquiv.smulLeft c hc` is `LinearIsometryEquiv.smulLeft c⁻¹ _`. -/
@[simp]
theorem smulLeft_symm (c : S) (hc : ‖c‖ = 1) :
    (smulLeft (R := R) (M := M) c hc).symm = smulLeft c⁻¹ (by rw [norm_inv, hc, inv_one]) :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

end LinearIsometryEquiv

namespace ContinuousLinearMap

variable {𝕜 S M M₂ : Type*} [NontriviallyNormedField 𝕜] [NormedDivisionRing S]
  [SeminormedAddCommGroup M] [NormedSpace 𝕜 M]
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] [Module S M₂] [NormSMulClass S M₂]
  [SMulCommClass 𝕜 S M₂]

/-- Scaling a continuous linear map by a commuting scalar `c` scales the operator norm of its
totalized inverse by `‖c‖⁻¹`. This holds unconditionally, including when `c = 0` or `f` is not
invertible, without requiring `f` to be `S`-linear. -/
@[simp]
theorem norm_inverse_smul (c : S) (f : M →L[𝕜] M₂) :
    ‖(c • f).inverse‖ = ‖c‖⁻¹ * ‖f.inverse‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : (0 : S) • f = 0 := by ext; simp
    have hinv0 : (0 : M →L[𝕜] M₂).inverse = 0 := by
      by_cases h : (0 : M →L[𝕜] M₂).IsInvertible
      · obtain ⟨_, _⟩ := isInvertible_zero_iff.mp h
        exact Subsingleton.elim _ _
      · exact inverse_of_not_isInvertible h
    rw [h0, hinv0, norm_zero, norm_zero, inv_zero, zero_mul]
  · refine le_antisymm ?_ ?_
    · refine opNorm_le_bound _ (by positivity) fun y ↦ ?_
      rw [inverse_smul_apply hc]
      calc ‖f.inverse (c⁻¹ • y)‖
          ≤ ‖f.inverse‖ * ‖c⁻¹ • y‖ := f.inverse.le_opNorm _
        _ = ‖c‖⁻¹ * ‖f.inverse‖ * ‖y‖ := by rw [norm_smul, norm_inv]; ring
    · have hle : ‖f.inverse‖ ≤ ‖c‖ * ‖(c • f).inverse‖ := by
        refine opNorm_le_bound _ (by positivity) fun z ↦ ?_
        have hz : f.inverse z = (c • f).inverse (c • z) := by
          rw [inverse_smul_apply hc, inv_smul_smul₀ hc]
        rw [hz]
        calc ‖(c • f).inverse (c • z)‖
            ≤ ‖(c • f).inverse‖ * ‖c • z‖ := (c • f).inverse.le_opNorm _
          _ = ‖c‖ * ‖(c • f).inverse‖ * ‖z‖ := by rw [norm_smul]; ring
      exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hc)).mpr hle

end ContinuousLinearMap
