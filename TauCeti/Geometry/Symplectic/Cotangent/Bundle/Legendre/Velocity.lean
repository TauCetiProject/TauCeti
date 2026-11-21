/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Lagrangians depending only on the velocity

On a normed space `E`, viewed as a manifold modelled on itself, a tangent vector is a pair
`(q, v)` of a position and a velocity. A function `f : E → 𝕜` defines the Lagrangian
`L(q, v) = f(v)`, which does not depend on the position. Its Legendre map is
`(q, v) ↦ (q, Df(v))` (`TauCeti.legendreMap_comp_snd`), its fibre Hessian at `(q, v)` is the second
derivative `D²f(v)` (`TauCeti.fiberHessian_comp_snd`) and its energy is `Df(v)(v) - f(v)`
(`TauCeti.lagrangianEnergy_comp_snd`). So `L` is regular exactly when every second derivative of
`f` is invertible (`TauCeti.isRegularLagrangian_comp_snd_iff`), and hyperregular exactly when, in
addition, the derivative `Df : E → E'` is a bijection
(`TauCeti.isHyperregularLagrangian_comp_snd_iff`). Both conditions are needed: the image of the
Legendre map consists of the covectors in the range of `Df` (`TauCeti.range_legendreMap_comp_snd`).

The example `L(q, v) = e^v` on the real line separates the two notions. Its fibre Hessian is
`e^v > 0`, so it is regular (`TauCeti.isRegularLagrangian_exp_snd`), but its Legendre map
`(q, v) ↦ (q, e^v)` misses every covector `p ≤ 0` (`TauCeti.range_legendreMap_exp_snd`). Hence it
is not hyperregular (`TauCeti.not_isHyperregularLagrangian_exp_snd`), and the Hamiltonian
`H = E_L ∘ FL⁻¹` is not defined on all of `T*ℝ`.

## Main declarations

* `TauCeti.legendreMap_comp_snd`, `TauCeti.fiberHessian_comp_snd`,
  `TauCeti.lagrangianEnergy_comp_snd`: the Legendre map, fibre Hessian and energy of `f(v)`.
* `TauCeti.isRegularLagrangian_comp_snd_iff`, `TauCeti.isHyperregularLagrangian_comp_snd_iff`:
  regularity and hyperregularity of `f(v)` in terms of `f`.
* `TauCeti.isRegularLagrangian_exp_snd`, `TauCeti.not_isHyperregularLagrangian_exp_snd`: `e^v` is
  regular but not hyperregular.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.4.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold

namespace TauCeti

section VectorSpace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : E → 𝕜)

/-- The Legendre map of a Lagrangian `f(v)` depending only on the velocity is
`(q, v) ↦ (q, Df(v))`. -/
@[simp]
theorem legendreMap_comp_snd (v : TangentBundle 𝓘(𝕜, E) E) :
    legendreMap (fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) v =
      TotalSpace.mk' (E →L[𝕜] 𝕜) v.proj (fderiv 𝕜 f v.snd) :=
  -- On the fibre over `v.proj` the Lagrangian is `w ↦ f w`, which is `f` itself.
  legendreMap_def _ v

/-- The fibre Hessian of a Lagrangian `f(v)` depending only on the velocity is the second
derivative of `f`. -/
@[simp]
theorem fiberHessian_comp_snd (v : TangentBundle 𝓘(𝕜, E) E) :
    fiberHessian (fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) v = fderiv 𝕜 (fderiv 𝕜 f) v.snd :=
  fiberHessian_def _ v

/-- The energy of a Lagrangian `f(v)` depending only on the velocity is `Df(v)(v) - f(v)`. -/
@[simp]
theorem lagrangianEnergy_comp_snd (v : TangentBundle 𝓘(𝕜, E) E) :
    lagrangianEnergy (fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) v = fderiv 𝕜 f v.snd v.snd - f
        v.snd := by
  rw [lagrangianEnergy_apply, legendreMap_comp_snd]
  -- The sides differ only in the fibre types `TangentSpace 𝓘(𝕜, E) v.proj` and
  -- `TangentSpace 𝓘(𝕜, E) v.proj →L[𝕜] 𝕜`, which are `E` and `E →L[𝕜] 𝕜` by definition.
  rfl

/-- A Lagrangian `f(v)` depending only on the velocity is regular exactly when every second
derivative of `f` is invertible. -/
theorem isRegularLagrangian_comp_snd_iff :
    IsRegularLagrangian (fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) ↔
      ∀ w : E, (fderiv 𝕜 (fderiv 𝕜 f) w).IsInvertible := by
  simp only [isRegularLagrangian_iff, fiberHessian_comp_snd]
  exact ⟨fun h w ↦ h (TotalSpace.mk' E 0 w), fun h v ↦ h v.snd⟩

/-- The Legendre map of a Lagrangian `f(v)` depending only on the velocity takes as values the
covectors in the range of the derivative `Df : E → E'`, at every base point. -/
theorem range_legendreMap_comp_snd :
    range (legendreMap fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) =
      {z | z.snd ∈ range (fderiv 𝕜 f)} := by
  ext z
  refine ⟨?_, fun ⟨w, hw⟩ ↦ ⟨TotalSpace.mk' E z.proj w, ?_⟩⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v.snd, by rw [legendreMap_comp_snd]⟩
  · rw [legendreMap_comp_snd]
    -- `hw` applies to `u : TangentSpace 𝓘(𝕜, E) z.proj` because the fibre types
    -- `TangentSpace 𝓘(𝕜, E) z.proj` and its dual are `E` and `E →L[𝕜] 𝕜` by definition.
    exact CotangentBundle.ext rfl fun u ↦ DFunLike.congr_fun hw u

/-- The Legendre map of a Lagrangian `f(v)` depending only on the velocity is injective exactly
when the derivative `Df : E → E'` is. -/
theorem injective_legendreMap_comp_snd_iff :
    Injective (legendreMap fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) ↔
      Injective (fderiv 𝕜 f) := by
  refine ⟨fun h w w' hww' ↦ ?_, fun h v v' hvv' ↦ ?_⟩
  · have := @h (TotalSpace.mk' E 0 w) (TotalSpace.mk' E 0 w')
      (by rw [legendreMap_comp_snd, legendreMap_comp_snd, hww'])
    exact congrArg TotalSpace.snd this
  · rw [legendreMap_comp_snd, legendreMap_comp_snd] at hvv'
    obtain ⟨x, w⟩ := v
    obtain ⟨x', w'⟩ := v'
    obtain rfl : x = x' := congrArg TotalSpace.proj hvv'
    -- The empty ascription retypes the fibre equality, stated in
    -- `TangentSpace 𝓘(𝕜, E) x →L[𝕜] 𝕜`, as one in `E →L[𝕜] 𝕜`, which is the same type by
    -- definition, so that `h` applies to it.
    obtain rfl : w = w' := h (TotalSpace.mk_inj.1 hvv' :)
    rfl

/-- The Legendre map of a Lagrangian `f(v)` depending only on the velocity is surjective exactly
when the derivative `Df : E → E'` is. -/
theorem surjective_legendreMap_comp_snd_iff :
    Surjective (legendreMap fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) ↔
      Surjective (fderiv 𝕜 f) := by
  -- Every covector at every base point is a value of `Df`.
  simp only [← range_eq_univ, range_legendreMap_comp_snd, eq_univ_iff_forall]
  exact ⟨fun h p ↦ h (TotalSpace.mk' (E →L[𝕜] 𝕜) (0 : E) p), fun h z ↦ h z.snd⟩

/-- A Lagrangian `f(v)` depending only on the velocity is hyperregular exactly when every second
derivative of `f` is invertible and the derivative `Df : E → E'` is a bijection. -/
theorem isHyperregularLagrangian_comp_snd_iff :
    IsHyperregularLagrangian (fun v : TangentBundle 𝓘(𝕜, E) E ↦ f v.snd) ↔
      (∀ w : E, (fderiv 𝕜 (fderiv 𝕜 f) w).IsInvertible) ∧ Bijective (fderiv 𝕜 f) := by
  refine ⟨fun h ↦ ⟨(isRegularLagrangian_comp_snd_iff f).1 h.isRegularLagrangian,
    (injective_legendreMap_comp_snd_iff f).1 h.bijective_legendreMap.1,
    (surjective_legendreMap_comp_snd_iff f).1 h.bijective_legendreMap.2⟩, fun ⟨h₁, h₂, h₃⟩ ↦
    ⟨(isRegularLagrangian_comp_snd_iff f).2 h₁,
      (injective_legendreMap_comp_snd_iff f).2 h₂, (surjective_legendreMap_comp_snd_iff f).2 h₃⟩⟩

end VectorSpace

section Exp

/-- **`L(q, v) = e^v` is regular**: its fibre Hessian is `e^v`, which is never zero. -/
theorem isRegularLagrangian_exp_snd :
    IsRegularLagrangian (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ Real.exp v.snd) := by
  rw [isRegularLagrangian_comp_snd_iff]
  intro w
  rw [isInvertible_fderiv_fderiv_iff_iteratedDeriv_two_ne_zero, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp]
  exact Real.exp_ne_zero w

/-- The Legendre map `(q, v) ↦ (q, e^v)` of `L(q, v) = e^v` takes as values exactly the positive
covectors: those `p` with `p(1) > 0`. -/
theorem range_legendreMap_exp_snd :
    range (legendreMap fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ Real.exp v.snd) =
      {z | 0 < z.snd (1 : ℝ)} := by
  rw [range_legendreMap_comp_snd]
  ext z
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun hz ↦ ⟨Real.log (z.snd (1 : ℝ)), ?_⟩⟩
  · have hpos : 0 < fderiv ℝ Real.exp w 1 := by
      rw [fderiv_eq_smul_deriv, Real.deriv_exp, one_smul]
      exact Real.exp_pos w
    simp only [Set.mem_ofPred_eq]
    exact hw ▸ hpos
  · refine ContinuousLinearMap.ext_ring ?_
    rw [fderiv_eq_smul_deriv, Real.deriv_exp, one_smul]
    -- The sides differ only in the fibre type `TangentSpace 𝓘(ℝ, ℝ) z.proj`, which is `ℝ`.
    exact Real.exp_log hz

/-- **`L(q, v) = e^v` is not hyperregular**: its Legendre map `(q, v) ↦ (q, e^v)` misses the
covectors `p ≤ 0`, so it is not onto `T*ℝ`, and `H = E_L ∘ FL⁻¹` is not defined on `T*ℝ`. -/
theorem not_isHyperregularLagrangian_exp_snd :
    ¬IsHyperregularLagrangian (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ Real.exp v.snd) := by
  intro h
  have h0 : TotalSpace.mk' (ℝ →L[ℝ] ℝ) (0 : ℝ) 0 ∈
      range (legendreMap fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ Real.exp v.snd) :=
    h.bijective_legendreMap.2 _
  rw [range_legendreMap_exp_snd] at h0
  simp only [Set.mem_ofPred_eq] at h0
  -- The zero covector at `0` sends `1` to `0` (`zero_apply`), so `h0` reads `0 < 0`.
  exact (h0.trans_eq (zero_apply (1 : ℝ))).false

end Exp

end TauCeti
