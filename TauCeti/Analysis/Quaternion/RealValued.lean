/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.QuotientDeriv
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# Quotient derivatives of real-valued quaternionic functions

A real-valued function `g : ℍ → ℝ`, viewed as the quaternion-valued function
`x ↦ (g x : ℍ)`, has a left or right quotient slope at `q` only in the degenerate way: the slope
is `0` and the real derivative of `g` at `q` vanishes. The reason is that the real derivative of
`x ↦ (g x : ℍ)` takes real values, whereas `h ↦ h * b` and `h ↦ b * h` reach the nonreal
quaternion `i` for every `b ≠ 0`.

In particular the four coordinate projections `x ↦ x.re`, `x ↦ x.imI`, `x ↦ x.imJ` and
`x ↦ x.imK`, whose real derivatives are nonzero real-linear functionals of rank one, have no
one-sided quotient slope at any point, although they are real-linear.

## Main results

* `TauCeti.hasLeftQuotientFDerivAt_coe_comp_iff` and its right counterpart: `x ↦ (g x : ℍ)` has
  slope `b` at `q` exactly when `b = 0` and `g` has real derivative `0` at `q`.
* `TauCeti.leftQuotientDifferentiableAt_coe_comp_iff` and its right counterpart: some slope
  exists exactly when the real derivative of `g` at `q` is `0`.
* `HasFDerivAt.not_leftQuotientDifferentiableAt_coe_comp`,
  `HasFDerivAt.not_hasLeftQuotientFDerivAt_coe_comp` and their right counterparts: a nonzero real
  derivative excludes every one-sided slope.
* `TauCeti.not_leftQuotientDifferentiableAt_re`, `TauCeti.not_hasLeftQuotientFDerivAt_re`, their
  right counterparts and the analogues for `imI`, `imJ` and `imK`: the coordinate projections have
  no one-sided slope at any point.

## References

* O. Dzagnidze, *On the differentiability of quaternion functions*, arXiv:1203.5619v1, §1, p. 2,
  for the one-sided quotient derivatives.
-/

public section

open scoped Quaternion

namespace TauCeti

variable {g : ℍ → ℝ} {q b : ℍ}

/-- A real-valued function `x ↦ (g x : ℍ)` has left slope `b` at `q` exactly when `b = 0` and the
real derivative of `g` at `q` is `0`. -/
theorem hasLeftQuotientFDerivAt_coe_comp_iff :
    HasLeftQuotientFDerivAt (fun x ↦ (g x : ℍ)) q b ↔ b = 0 ∧ HasFDerivAt g (0 : ℍ →L[ℝ] ℝ) q := by
  -- `Algebra.linearMap ℝ ℍ` is the coercion `ℝ → ℍ`, with left inverse the real part.
  have hre : Function.LeftInverse (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
      (Algebra.linearMap ℝ ℍ).toContinuousLinearMap := fun r ↦ by simp
  have hemb := Topology.IsEmbedding.of_leftInverse hre (map_continuous _) (map_continuous _)
  refine ⟨fun hb ↦ ?_, fun ⟨hb, hg⟩ ↦ ?_⟩
  · obtain rfl : b = 0 := by
      -- Otherwise the derivative value `(i * b⁻¹) * b = i` would be real.
      by_contra hb0
      have h := DFunLike.congr_fun (ContinuousLinearMap.comp_comp_eq_of_hasFDerivAt_comp_left _ _
        hre (k := g) hb.hasFDerivAt) (⟨0, 1, 0, 0⟩ * b⁻¹)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', mul_assoc, inv_mul_cancel₀ hb0, mul_one] at h
      simpa using congrArg QuaternionAlgebra.imI h
    refine ⟨rfl, (ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding _ hemb).mp ?_⟩
    simpa [Function.comp_def, hasLeftQuotientFDerivAt_iff_hasFDerivAt] using hb
  · simpa [Function.comp_def, hb, hasLeftQuotientFDerivAt_iff_hasFDerivAt] using
      (ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding _ hemb).mpr hg

/-- A real-valued function `x ↦ (g x : ℍ)` has right slope `b` at `q` exactly when `b = 0` and the
real derivative of `g` at `q` is `0`. -/
theorem hasRightQuotientFDerivAt_coe_comp_iff :
    HasRightQuotientFDerivAt (fun x ↦ (g x : ℍ)) q b ↔ b = 0 ∧ HasFDerivAt g (0 : ℍ →L[ℝ] ℝ) q := by
  -- `Algebra.linearMap ℝ ℍ` is the coercion `ℝ → ℍ`, with left inverse the real part.
  have hre : Function.LeftInverse (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
      (Algebra.linearMap ℝ ℍ).toContinuousLinearMap := fun r ↦ by simp
  have hemb := Topology.IsEmbedding.of_leftInverse hre (map_continuous _) (map_continuous _)
  refine ⟨fun hb ↦ ?_, fun ⟨hb, hg⟩ ↦ ?_⟩
  · obtain rfl : b = 0 := by
      -- Otherwise the derivative value `b * (b⁻¹ * i) = i` would be real.
      by_contra hb0
      have h := DFunLike.congr_fun (ContinuousLinearMap.comp_comp_eq_of_hasFDerivAt_comp_left _ _
        hre (k := g) hb.hasFDerivAt) (b⁻¹ * ⟨0, 1, 0, 0⟩)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', ← mul_assoc,
        mul_inv_cancel₀ hb0, one_mul] at h
      simpa using congrArg QuaternionAlgebra.imI h
    refine ⟨rfl, (ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding _ hemb).mp ?_⟩
    simpa [Function.comp_def, hasRightQuotientFDerivAt_iff_hasFDerivAt] using hb
  · simpa [Function.comp_def, hb, hasRightQuotientFDerivAt_iff_hasFDerivAt] using
      (ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding _ hemb).mpr hg

/-- A real-valued function `x ↦ (g x : ℍ)` is left quotient differentiable at `q` exactly when the
real derivative of `g` at `q` is `0`. -/
theorem leftQuotientDifferentiableAt_coe_comp_iff :
    LeftQuotientDifferentiableAt (fun x ↦ (g x : ℍ)) q ↔ HasFDerivAt g (0 : ℍ →L[ℝ] ℝ) q :=
  ⟨fun h ↦ (hasLeftQuotientFDerivAt_coe_comp_iff.mp h.hasLeftQuotientFDerivAt).2,
    fun hg ↦ (hasLeftQuotientFDerivAt_coe_comp_iff.mpr ⟨rfl, hg⟩).leftQuotientDifferentiableAt⟩

/-- A real-valued function `x ↦ (g x : ℍ)` is right quotient differentiable at `q` exactly when the
real derivative of `g` at `q` is `0`. -/
theorem rightQuotientDifferentiableAt_coe_comp_iff :
    RightQuotientDifferentiableAt (fun x ↦ (g x : ℍ)) q ↔ HasFDerivAt g (0 : ℍ →L[ℝ] ℝ) q :=
  ⟨fun h ↦ (hasRightQuotientFDerivAt_coe_comp_iff.mp h.hasRightQuotientFDerivAt).2,
    fun hg ↦ (hasRightQuotientFDerivAt_coe_comp_iff.mpr ⟨rfl, hg⟩).rightQuotientDifferentiableAt⟩

end TauCeti

/-- A real-valued function with a nonzero real derivative at `q` has no left quotient slope at
`q`. -/
theorem HasFDerivAt.not_leftQuotientDifferentiableAt_coe_comp {g : ℍ → ℝ} {g' : ℍ →L[ℝ] ℝ}
    {q : ℍ} (hg : HasFDerivAt g g' q) (hg' : g' ≠ 0) :
    ¬TauCeti.LeftQuotientDifferentiableAt (fun x ↦ (g x : ℍ)) q := fun h ↦
  hg' (hg.unique (TauCeti.leftQuotientDifferentiableAt_coe_comp_iff.mp h))

/-- A real-valued function with a nonzero real derivative at `q` has no right quotient slope at
`q`. -/
theorem HasFDerivAt.not_rightQuotientDifferentiableAt_coe_comp {g : ℍ → ℝ} {g' : ℍ →L[ℝ] ℝ}
    {q : ℍ} (hg : HasFDerivAt g g' q) (hg' : g' ≠ 0) :
    ¬TauCeti.RightQuotientDifferentiableAt (fun x ↦ (g x : ℍ)) q := fun h ↦
  hg' (hg.unique (TauCeti.rightQuotientDifferentiableAt_coe_comp_iff.mp h))

/-- A real-valued function with a nonzero real derivative at `q` has no left quotient slope `b` at
`q`. -/
theorem HasFDerivAt.not_hasLeftQuotientFDerivAt_coe_comp {g : ℍ → ℝ} {g' : ℍ →L[ℝ] ℝ}
    {q : ℍ} (hg : HasFDerivAt g g' q) (hg' : g' ≠ 0) (b : ℍ) :
    ¬TauCeti.HasLeftQuotientFDerivAt (fun x ↦ (g x : ℍ)) q b := fun h ↦
  hg.not_leftQuotientDifferentiableAt_coe_comp hg' h.leftQuotientDifferentiableAt

/-- A real-valued function with a nonzero real derivative at `q` has no right quotient slope `b`
at `q`. -/
theorem HasFDerivAt.not_hasRightQuotientFDerivAt_coe_comp {g : ℍ → ℝ} {g' : ℍ →L[ℝ] ℝ}
    {q : ℍ} (hg : HasFDerivAt g g' q) (hg' : g' ≠ 0) (b : ℍ) :
    ¬TauCeti.HasRightQuotientFDerivAt (fun x ↦ (g x : ℍ)) q b := fun h ↦
  hg.not_rightQuotientDifferentiableAt_coe_comp hg' h.rightQuotientDifferentiableAt

namespace TauCeti

/-! ### The coordinate projections -/

/-- A nonzero real-linear functional, viewed as a quaternion-valued map, has neither a left nor a
right quotient slope at any point. -/
private theorem not_quotientDifferentiableAt_linearMap (φ : ℍ →ₗ[ℝ] ℝ) {x : ℍ} (hx : φ x ≠ 0)
    (q : ℍ) : ¬LeftQuotientDifferentiableAt (fun y ↦ (φ y : ℍ)) q ∧
      ¬RightQuotientDifferentiableAt (fun y ↦ (φ y : ℍ)) q := by
  have hφ : HasFDerivAt (fun y ↦ φ y) φ.toContinuousLinearMap q :=
    φ.toContinuousLinearMap.hasFDerivAt
  have hne : φ.toContinuousLinearMap ≠ 0 := fun h ↦ hx (by simpa using DFunLike.congr_fun h x)
  exact ⟨hφ.not_leftQuotientDifferentiableAt_coe_comp hne,
    hφ.not_rightQuotientDifferentiableAt_coe_comp hne⟩

/-- The real part map `x ↦ x.re` has no left quotient slope at any point. -/
@[simp]
theorem not_leftQuotientDifferentiableAt_re (q : ℍ) :
    ¬LeftQuotientDifferentiableAt (fun x : ℍ ↦ (x.re : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
    (x := 1) (by simp) q).1

/-- The real part map `x ↦ x.re` has no left quotient slope `b` at any point. -/
@[simp]
theorem not_hasLeftQuotientFDerivAt_re (q b : ℍ) :
    ¬HasLeftQuotientFDerivAt (fun x : ℍ ↦ (x.re : ℍ)) q b := fun h ↦
  not_leftQuotientDifferentiableAt_re q h.leftQuotientDifferentiableAt

/-- The real part map `x ↦ x.re` has no right quotient slope at any point. -/
@[simp]
theorem not_rightQuotientDifferentiableAt_re (q : ℍ) :
    ¬RightQuotientDifferentiableAt (fun x : ℍ ↦ (x.re : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
    (x := 1) (by simp) q).2

/-- The real part map `x ↦ x.re` has no right quotient slope `b` at any point. -/
@[simp]
theorem not_hasRightQuotientFDerivAt_re (q b : ℍ) :
    ¬HasRightQuotientFDerivAt (fun x : ℍ ↦ (x.re : ℍ)) q b := fun h ↦
  not_rightQuotientDifferentiableAt_re q h.rightQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imI` has no left quotient slope at any point. -/
@[simp]
theorem not_leftQuotientDifferentiableAt_imI (q : ℍ) :
    ¬LeftQuotientDifferentiableAt (fun x : ℍ ↦ (x.imI : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 1, 0, 0⟩) (by simp) q).1

/-- The coordinate `x ↦ x.imI` has no left quotient slope `b` at any point. -/
@[simp]
theorem not_hasLeftQuotientFDerivAt_imI (q b : ℍ) :
    ¬HasLeftQuotientFDerivAt (fun x : ℍ ↦ (x.imI : ℍ)) q b := fun h ↦
  not_leftQuotientDifferentiableAt_imI q h.leftQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imI` has no right quotient slope at any point. -/
@[simp]
theorem not_rightQuotientDifferentiableAt_imI (q : ℍ) :
    ¬RightQuotientDifferentiableAt (fun x : ℍ ↦ (x.imI : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 1, 0, 0⟩) (by simp) q).2

/-- The coordinate `x ↦ x.imI` has no right quotient slope `b` at any point. -/
@[simp]
theorem not_hasRightQuotientFDerivAt_imI (q b : ℍ) :
    ¬HasRightQuotientFDerivAt (fun x : ℍ ↦ (x.imI : ℍ)) q b := fun h ↦
  not_rightQuotientDifferentiableAt_imI q h.rightQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imJ` has no left quotient slope at any point. -/
@[simp]
theorem not_leftQuotientDifferentiableAt_imJ (q : ℍ) :
    ¬LeftQuotientDifferentiableAt (fun x : ℍ ↦ (x.imJ : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 0, 1, 0⟩) (by simp) q).1

/-- The coordinate `x ↦ x.imJ` has no left quotient slope `b` at any point. -/
@[simp]
theorem not_hasLeftQuotientFDerivAt_imJ (q b : ℍ) :
    ¬HasLeftQuotientFDerivAt (fun x : ℍ ↦ (x.imJ : ℍ)) q b := fun h ↦
  not_leftQuotientDifferentiableAt_imJ q h.leftQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imJ` has no right quotient slope at any point. -/
@[simp]
theorem not_rightQuotientDifferentiableAt_imJ (q : ℍ) :
    ¬RightQuotientDifferentiableAt (fun x : ℍ ↦ (x.imJ : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 0, 1, 0⟩) (by simp) q).2

/-- The coordinate `x ↦ x.imJ` has no right quotient slope `b` at any point. -/
@[simp]
theorem not_hasRightQuotientFDerivAt_imJ (q b : ℍ) :
    ¬HasRightQuotientFDerivAt (fun x : ℍ ↦ (x.imJ : ℍ)) q b := fun h ↦
  not_rightQuotientDifferentiableAt_imJ q h.rightQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imK` has no left quotient slope at any point. -/
@[simp]
theorem not_leftQuotientDifferentiableAt_imK (q : ℍ) :
    ¬LeftQuotientDifferentiableAt (fun x : ℍ ↦ (x.imK : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 0, 0, 1⟩) (by simp) q).1

/-- The coordinate `x ↦ x.imK` has no left quotient slope `b` at any point. -/
@[simp]
theorem not_hasLeftQuotientFDerivAt_imK (q b : ℍ) :
    ¬HasLeftQuotientFDerivAt (fun x : ℍ ↦ (x.imK : ℍ)) q b := fun h ↦
  not_leftQuotientDifferentiableAt_imK q h.leftQuotientDifferentiableAt

/-- The coordinate `x ↦ x.imK` has no right quotient slope at any point. -/
@[simp]
theorem not_rightQuotientDifferentiableAt_imK (q : ℍ) :
    ¬RightQuotientDifferentiableAt (fun x : ℍ ↦ (x.imK : ℍ)) q :=
  (not_quotientDifferentiableAt_linearMap (QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1))
    (x := ⟨0, 0, 0, 1⟩) (by simp) q).2

/-- The coordinate `x ↦ x.imK` has no right quotient slope `b` at any point. -/
@[simp]
theorem not_hasRightQuotientFDerivAt_imK (q b : ℍ) :
    ¬HasRightQuotientFDerivAt (fun x : ℍ ↦ (x.imK : ℍ)) q b := fun h ↦
  not_rightQuotientDifferentiableAt_imK q h.rightQuotientDifferentiableAt

end TauCeti
