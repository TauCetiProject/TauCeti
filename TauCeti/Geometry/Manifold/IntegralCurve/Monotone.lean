/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Monotonicity of functions along integral curves

Let `γ` be an integral curve of a vector field `v` on a manifold, and `f` a real function,
differentiable along `γ`, with `df(v) ≤ 0` along `γ`. Then `f` never increases along `γ`. If
moreover `df(v) < 0` at `γ s`, then `f` drops strictly below `f (γ s)` at every later time, with no
further sign condition at the later points.

These are the monotonicity statements behind the deformation of sublevels along descending
vector fields, which are allowed to vanish away from the region being deformed.

If instead `df(v) = 0` along an integral curve defined on an open preconnected set of times, then
`f` is constant along it. This is the conservation statement behind first integrals of a vector
field.

## Main declarations

* `IsMIntegralCurve.antitone_comp`: `f` is antitone along `γ`.
* `IsMIntegralCurve.lt_of_mvfderiv_apply_lt_zero`: `f` strictly decreases along `γ` after a time
  at which `df(v) < 0`.
* `IsMIntegralCurveOn.apply_eq_of_mvfderiv_apply_eq_zero`: `f` is constant along `γ` when
  `df(v) = 0` along it.
-/

public section

open Filter Set
open scoped Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {f : M → ℝ}

namespace IsMIntegralCurve

/-- **Monotonicity along an integral curve.** If `f` is differentiable along an integral curve `γ`
of `v` and `df(v) ≤ 0` along `γ`, then `f` is antitone along `γ`. -/
theorem antitone_comp (hγ : IsMIntegralCurve γ v)
    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    (hvf : ∀ t, mvfderiv I f (γ t) (v (γ t)) ≤ 0) : Antitone (f ∘ γ) :=
  antitone_of_hasDerivAt_nonpos
    (fun t ↦ TauCeti.Manifold.hasDerivAt_comp_curve (hf t) (hγ t)) hvf

/-- **Strict decrease along an integral curve.** If `f` is differentiable along an integral curve
`γ` of `v`, `df(v) ≤ 0` along `γ` and `df(v) < 0` at `γ s`, then `f (γ t) < f (γ s)` for every
`t > s`. -/
theorem lt_of_mvfderiv_apply_lt_zero (hγ : IsMIntegralCurve γ v)
    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    (hvf : ∀ t, mvfderiv I f (γ t) (v (γ t)) ≤ 0) {s t : ℝ}
    (hs : mvfderiv I f (γ s) (v (γ s)) < 0) (hst : s < t) : f (γ t) < f (γ s) := by
  have hd := TauCeti.Manifold.hasDerivAt_comp_curve (hf s) (hγ s)
  -- Some time `z ∈ (s, t)` has negative slope `(f (γ z) - f (γ s)) / (z - s)`, so
  -- `f (γ t) ≤ f (γ z) < f (γ s)`.
  obtain ⟨z, hz, hzt⟩ := ((hd.hasDerivWithinAt.limsup_slope_le' (lt_irrefl s) hs).and
    (Ioo_mem_nhdsGT hst)).exists
  rw [slope_def_field, div_neg_iff] at hz
  have hzs : (f ∘ γ) z < (f ∘ γ) s := by
    rcases hz with ⟨-, h⟩ | ⟨h, -⟩
    · linarith [hzt.1]
    · linarith
  exact (hγ.antitone_comp hf hvf hzt.2.le).trans_lt hzs

end IsMIntegralCurve

namespace IsMIntegralCurveOn

/-- **Constancy along an integral curve.** If `f` is differentiable along an integral curve `γ` of
`v` on an open preconnected set of times `s`, such as an open interval, and `df(v) = 0` along `γ`
on `s`, then `f` is constant along `γ` on `s`. -/
theorem apply_eq_of_mvfderiv_apply_eq_zero {s : Set ℝ} (hγ : IsMIntegralCurveOn γ v s)
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    (hvf : ∀ t ∈ s, mvfderiv I f (γ t) (v (γ t)) = 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    f (γ t) = f (γ t₀) := by
  have hd (u : ℝ) (hu : u ∈ s) : HasDerivAt (f ∘ γ) 0 u := by
    simpa only [hvf u hu] using
      TauCeti.Manifold.hasDerivAt_comp_curve (hf u hu) ((hγ u hu).hasMFDerivAt (hs.mem_nhds hu))
  exact hs.is_const_of_deriv_eq_zero hs'
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt) (fun u hu ↦ (hd u hu).deriv)
    ht ht₀

end IsMIntegralCurveOn
