/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Analysis.ODE.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Duality
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

end TauCeti.SymplecticForm
