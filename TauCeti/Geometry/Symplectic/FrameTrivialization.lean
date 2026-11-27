/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Analysis.ODE.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Duality
public import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Preservation of infinitesimal symplecticity under frame trivialization

Pulling a linearized symplectic ODE on `(V, ω)` back along a moving symplectic frame
`Φ : ℝ → F →L[ℝ] V` into `(F, Im ⟪·, ·⟫)` adds `-Φ(t)⁻¹ Φ'(t)` to the conjugated coefficient
`Φ(t)⁻¹ S(t) Φ(t)`, yielding `TauCeti.trivializedCoeff Φ S t`, yet preserves infinitesimal
symplecticity (`SymplecticForm.im_inner_trivializedCoeff_add_eq_zero`), supplying the `H⁰`-symmetry
needed in `TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Trivialization.lean` and
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Cylinder.lean`. Adapts
`TauCeti.isSymmetric_frameConnection`
(`TauCeti/Geometry/Symplectic/JHolomorphic/OrbitTorus/Trivialization.lean`).

For a one-periodic frame and coefficient, the trivialized coefficient is a loop on the circle, `C¹`
when `Φ` is `C²` and `S` is `C¹`, whose return map is nondegenerate when that of `S` is
(`SymplecticForm.exists_loop_eq_trivializedCoeff`): the input of the invertibility of the stationary
cylinder operator `∂s + i (∂t - S_Φ)` in a unitary trivialization.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
-/

public section

noncomputable section

namespace TauCeti.SymplecticForm

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- If `Φ` is differentiable with invertible value at `t` and pulls `ω` back to `Im ⟪·, ·⟫` on `F`,
`trivializedCoeff Φ S t` is infinitesimally symplectic on `F` whenever `S t` is for `ω`. -/
theorem im_inner_trivializedCoeff_add_eq_zero (ω : SymplecticForm V) {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hω : ∀ r v w, ω (Φ r v) (Φ r w) = (inner ℂ v w).im)
    (hS : ∀ v w, ω (S t v) w + ω v (S t w) = 0) (v w : F) :
    (inner ℂ (trivializedCoeff Φ S t v) w).im + (inner ℂ v (trivializedCoeff Φ S t w)).im = 0 := by
  have hdΦ (u : F) : HasDerivAt (fun r ↦ Φ r u) (deriv Φ t u) t := by
    simpa using hΦd.hasDerivAt.clm_apply (hasDerivAt_const t u)
  have hdω := ω.hasDerivAt_apply_comp (hdΦ v) (hdΦ w)
  rw [funext fun r ↦ hω r v w] at hdω
  have h0 := hdω.unique (hasDerivAt_const t _)
  rw [← hω t (trivializedCoeff Φ S t v) w, ← hω t v (trivializedCoeff Φ S t w),
    trivializedCoeff_apply, trivializedCoeff_apply, hΦ.self_apply_inverse, hΦ.self_apply_inverse]
  simp only [map_sub, LinearMap.sub_apply]; linarith [hS (Φ t v) (Φ t w)]

/-- **The trivialized coefficient as a loop.** Let `Φ` be a `C²` one-periodic frame
`F →L[ℝ] V` with invertible values carrying `Im ⟪·, ·⟫` to `ω`, and let `S` be a `C¹` one-periodic
loop of infinitesimally symplectic maps of `(V, ω)` whose return map has no eigenvalue `1`,
`det (1 - Ψ(1)) ≠ 0`. Then `S_Φ = trivializedCoeff Φ S` is a loop on the circle `ℝ ⧸ ℤ`, `C¹` in
`t`, infinitesimally symplectic for `Im ⟪·, ·⟫`, with `det (1 - Ψ_Φ(1)) ≠ 0` for its return map. -/
theorem exists_loop_eq_trivializedCoeff [CompleteSpace F] (ω : SymplecticForm V)
    {Φ : ℝ → F →L[ℝ] V} (hΦ : ContDiff ℝ 2 Φ) (hΦp : Function.Periodic Φ 1)
    (hΦi : ∀ t, (Φ t).IsInvertible) (hΦω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : ℝ → V →L[ℝ] V} (hS : ContDiff ℝ 1 S) (hSp : Function.Periodic S 1)
    (hSω : ∀ t v w, ω (S t v) w + ω v (S t w) = 0)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ T : C(AddCircle (1 : ℝ), F →L[ℝ] F), (fun t : ℝ ↦ T t) = trivializedCoeff Φ S ∧
      ContDiff ℝ 1 (fun t : ℝ ↦ T t) ∧
      (∀ θ v w, (inner ℂ (T θ v) w).im + (inner ℂ v (T θ w)).im = 0) ∧
      LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ T t) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0 := by
  have hΦ₁ : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hper := periodic_trivializedCoeff hΦp hSp
  have hT₁ := contDiff_trivializedCoeff (n := 1) hΦ hΦi hS
  let T : C(AddCircle (1 : ℝ), F →L[ℝ] F) :=
    ⟨hper.lift, continuous_coinduced_dom.2 hT₁.continuous⟩
  have hT : (fun t : ℝ ↦ T t) = trivializedCoeff Φ S := funext fun t ↦ hper.lift_coe t
  refine ⟨T, hT, hT ▸ hT₁, fun θ v w ↦ ?_, ?_⟩
  · induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [show T t = trivializedCoeff Φ S t from congrFun hT t]
    exact ω.im_inner_trivializedCoeff_add_eq_zero (hΦ₁.differentiable one_ne_zero t) (hΦi t) hΦω
      (hSω t) v w
  · rw [hT, det_one_sub_dysonSeriesLeft_trivializedCoeff hΦ₁ hΦi hS.continuous
      (by simpa using hΦp 0)]
    exact hdet

end TauCeti.SymplecticForm
