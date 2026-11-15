/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Sobolev.Local.Coordinates

/-!
# Recovering the normal derivative from the Cauchy–Riemann equation

In the coordinate `z = s + it`, the linear Cauchy–Riemann equation
`∂ₛξ + J(z) ∂ₜξ + S(z) ξ = η` for `ξ : ℂ → V` can be solved for the normal derivative: when
`J(z)² = -1`, it is equivalent to `∂ₜξ = J(z) (∂ₛξ + S(z) ξ - η)`. For a weak derivative `D` of
`ξ` the two partial derivatives are `D z 1` and `D z I`, so the equation determines `D z I` from
`D z 1`, `ξ` and `η`. This is the step of McDuff–Salamon's boundary regularity (Lemma B.4.6 and
Proposition B.4.9) that turns tangential regularity on a half-disc into full regularity: the
tangential derivative `∂ₛξ` is controlled by the order-zero estimate up to the real axis, and
the equation then gives the normal one.

The sets `U` here are arbitrary, as in `TauCeti.MemWkpLoc`: weak derivatives are taken on
`interior U` and the `Lᵖ` bounds on compact subsets of `U`, so half-discs relatively open in the
closed upper half-plane are included. The equation is taken as a hypothesis almost everywhere on
`interior U`, which is what `TauCeti.IsWeakCauchyRiemannOn` provides and what any other weak
formulation is expected to produce.

## Main results

* `TauCeti.add_apply_add_eq_iff_eq_apply_add_sub`: for `A ∘ A = -1`,
  `a + A b + c = y ↔ b = A (a + c - y)`.
* `TauCeti.ae_cauchyRiemann_iff_ae_apply_I_eq`: the almost-everywhere form of the equation is
  equivalent to the almost-everywhere normal derivative formula `D z I = J z (D z 1 + S z (ξ z) -
  η z)`.
* `TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`: the induction step of boundary regularity for
  coefficients `J`, `S` of class `C^k` near `U`. If `ξ` and `η` lie in `W^{k,q}_loc(U)` and so does
  the tangential derivative `∂ₛξ`, then `ξ` lies in `W^{k+1,q}_loc(U)`.
  `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ` is the same step for weak solutions of the
  homogeneous linear equation.
* `TauCeti.ae_cauchyRiemann_standard_iff`: for `J = i` and `S = η = 0` the formula is
  `∂ₜξ = i ∂ₛξ`. Examples at the end check it on `ξ = z` and show that the sign
  `∂ₜξ = -J(∂ₛξ + Sξ - η)` fails there.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6 and Proposition B.4.9).
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Solving the equation for the normal derivative -/

/-- **Solving for the normal derivative.** If `A ∘ A = -1`, then `a + A b + c = y` holds exactly
when `b = A (a + c - y)`: applying `A` to `A b = y - a - c` gives `-b = A (y - a - c)`. -/
theorem add_apply_add_eq_iff_eq_apply_add_sub {A : V →L[ℝ] V}
    (hA : A.comp A = -ContinuousLinearMap.id ℝ V) {a b c y : V} :
    a + A b + c = y ↔ b = A (a + c - y) := by
  have hA' (v : V) : A (A v) = -v := by
    simpa using congrArg (fun T : V →L[ℝ] V => T v) hA
  constructor
  · rintro rfl
    have hsub : a + c - (a + A b + c) = -A b := by abel
    rw [hsub, map_neg, hA', neg_neg]
  · rintro rfl
    rw [hA']
    abel

/-- **The normal derivative formula almost everywhere.** If `J z ∘ J z = -1` almost everywhere,
then the equation `D z 1 + J z (D z I) + S z (ξ z) = η z` holds almost everywhere exactly when
`D z I = J z (D z 1 + S z (ξ z) - η z)` does. For a weak derivative `D` of `ξ` this is
`∂ₜξ = J (∂ₛξ + S ξ - η)`. -/
theorem ae_cauchyRiemann_iff_ae_apply_I_eq {μ : Measure ℂ} {J S : ℂ → V →L[ℝ] V}
    {ξ η : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (hJ : ∀ᵐ z ∂μ, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) :
    (∀ᵐ z ∂μ, D z 1 + J z (D z I) + S z (ξ z) = η z) ↔
      ∀ᵐ z ∂μ, D z I = J z (D z 1 + S z (ξ z) - η z) := by
  constructor <;> intro h <;> filter_upwards [h, hJ] with z hz hJz
  · exact (add_apply_add_eq_iff_eq_apply_add_sub hJz).1 hz
  · exact (add_apply_add_eq_iff_eq_apply_add_sub hJz).2 hz

variable {q : ENNReal} {U : Set ℂ} {k : ℕ}

/-! ### The induction step for smooth coefficients -/

/-- **Normal derivative recovery, `C^k` coefficients.** Let `J` and `S` be fields of real-linear
endomorphisms of a finite-dimensional space `V`, of class `C^n` on an open neighbourhood `Ω` of
`U`, with `k ≤ n` and `J z ∘ J z = -1` on the interior of `U`. Let `ξ` have a weak derivative `D`
on the interior of `U` satisfying `∂ₛξ + J ∂ₜξ + S ξ = η` there almost everywhere. If `ξ`, `η`
and the tangential derivative `∂ₛξ = D · 1` lie in `W^{k,q}_loc(U)`, then `ξ` lies in
`W^{k+1,q}_loc(U)`: the map `J (∂ₛξ + S ξ - η)` lies in `W^{k,q}_loc(U)` and agrees with the
normal derivative `∂ₜξ = D · I` almost everywhere on the interior of `U`, so it serves as the
normal partial derivative of a weak derivative of `ξ`. On a half-disc this is the induction step of
boundary regularity. -/
theorem memWkpLoc_succ_of_ae_cauchyRiemann [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {n : WithTop ℕ∞} {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (hJ : ContDiffOn ℝ n J Ω) (hS : ContDiffOn ℝ n S Ω) (hk : (k : WithTop ℕ∞) ≤ n)
    (hU : U ⊆ Ω) (hJJ : ∀ z ∈ interior U, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hξ : MemWkpLoc q U k ξ) (hη : MemWkpLoc q U k η)
    (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D) (hD1 : MemWkpLoc q U k fun z => D z 1)
    (heq : ∀ᵐ z ∂volume.restrict (interior U), D z 1 + J z (D z I) + S z (ξ z) = η z) :
    MemWkpLoc q U (k + 1) ξ := by
  set N : ℂ → V := fun z => J z (D z 1 + S z (ξ z) - η z)
  have hN : MemWkpLoc q U k N :=
    ((hD1.add (hξ.contDiffOn_clm_apply hS hk hU)).sub hη).contDiffOn_clm_apply hJ hk hU
  have hae : ∀ᵐ z ∂volume.restrict (interior U), D z I = N z :=
    (ae_cauchyRiemann_iff_ae_apply_I_eq
      (ae_restrict_of_forall_mem isOpen_interior.measurableSet hJJ)).1 heq
  let D' : ℂ → ℂ →L[ℝ] V := fun z =>
    ContinuousLinearMap.smulRightL ℝ ℂ V reCLM (D z 1) +
      ContinuousLinearMap.smulRightL ℝ ℂ V imCLM (N z)
  have hD' : HasWeakFDerivOn volume (Opens.interior U) ξ D' := by
    refine hD.congr_ae_deriv ?_
    filter_upwards [hae] with z hz
    conv_lhs => rw [(D z).eq_reCLM_smulRight_add_imCLM_smulRight, hz]
    ext w
    simp [D']
  exact hξ.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn hD' (by simpa [D'] using hD1)
    (by simpa [D'] using hN)

/-- **Normal derivative recovery for the homogeneous linear equation.** A weak solution of
`∂ₛξ + J ∂ₜξ + S ξ = 0` on `U`, with `J`, `S` of class `C^n` near `U`, `k ≤ n` and `J ∘ J = -1`
on the interior of `U`, lies in `W^{k+1,q}_loc(U)` as soon as `ξ` and its tangential derivative
`∂ₛξ` lie in `W^{k,q}_loc(U)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {n : WithTop ℕ∞} {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (h : IsWeakLinearCauchyRiemannOn q U J S ξ) (hJ : ContDiffOn ℝ n J Ω)
    (hS : ContDiffOn ℝ n S Ω) (hk : (k : WithTop ℕ∞) ≤ n) (hU : U ⊆ Ω)
    (hJJ : ∀ z ∈ interior U, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hξ : MemWkpLoc q U k ξ) (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D)
    (hD1 : MemWkpLoc q U k fun z => D z 1) : MemWkpLoc q U (k + 1) ξ := by
  refine memWkpLoc_succ_of_ae_cauchyRiemann hJ hS hk hU hJJ hξ (η := 0) memWkpLoc_zero_fun hD hD1
    ?_
  filter_upwards [IsWeakCauchyRiemannOn.ae_eq_of_hasWeakFDerivOn h hD] with z hz
  rw [Pi.zero_apply, ← eq_neg_iff_add_eq_zero]
  exact hz

/-! ### Checks for the standard structure on `ℂ` -/

/-- **Check: the standard structure.** For `J = i` and `S = η = 0` the normal derivative formula
reads `∂ₜξ = i ∂ₛξ`, the Cauchy–Riemann equation in the form satisfied by holomorphic maps. -/
theorem ae_cauchyRiemann_standard_iff {μ : Measure ℂ} {D : ℂ → ℂ →L[ℝ] ℂ} :
    (∀ᵐ z ∂μ, D z 1 + I * D z I = 0) ↔ ∀ᵐ z ∂μ, D z I = I * D z 1 := by
  have h := ae_cauchyRiemann_iff_ae_apply_I_eq (μ := μ)
    (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0) (ξ := 0) (η := 0) (D := D)
    (Filter.Eventually.of_forall fun _ => by
      ext1 w
      simp [← mul_assoc])
  simpa using h

-- The identity `ξ = z` satisfies the normal derivative formula `∂ₜξ = i ∂ₛξ` for `J = i`.
example (z : ℂ) : fderiv ℝ id z I = I * fderiv ℝ id z 1 := by
  simp

-- The sign `∂ₜξ = -J (∂ₛξ + S ξ - η)` would make `ξ = z` fail: `i ≠ -i`.
example (z : ℂ) : fderiv ℝ id z I ≠ -(I * fderiv ℝ id z 1) := by
  norm_num [Complex.ext_iff]

end TauCeti
