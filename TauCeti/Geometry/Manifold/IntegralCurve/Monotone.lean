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
import TauCeti.Analysis.Calculus.Deriv.LevelCrossing
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Monotonicity of functions along integral curves

Let `γ` be an integral curve of a vector field `v` on a manifold, and `f` a real function,
differentiable along `γ`, with `df(v) ≤ 0` along `γ`. Then `f` never increases along `γ`. If
moreover `df(v) < 0` at `γ s`, then `f` drops strictly below `f (γ s)` at every later time, with no
further sign condition at the later points.

These are the monotonicity statements behind the deformation of sublevels along descending
vector fields, which are allowed to vanish away from the region being deformed.

If instead `df(v) = 0` along an integral curve defined on a preconnected set of times, then
`f` is constant along it. This is the conservation statement behind first integrals of a vector
field. The same holds for a map `g` into another manifold with `dg(v) = 0` along an integral curve
on an open preconnected set of times: the curve then stays in one fibre of `g`.

If `df(v) > 0` is only known at the points of `γ` on a level `f⁻¹(c)`, then `γ` crosses that level
only upwards: once `f (γ a) ≥ c`, it stays in `{f > c}` at every later time, and once
`f (γ b) ≤ c`, it was in `{f < c}` at every earlier time. This is how the trajectories of a vector
field pointing out of a domain `{f ≤ c}` along its boundary are shown never to re-enter it.

Finally, an integral curve along which the vector field vanishes does not move at all: it is a
constant curve.

## Main declarations

* `IsMIntegralCurve.antitone_comp`: `f` is antitone along `γ`.
* `IsMIntegralCurve.lt_of_mvfderiv_apply_lt_zero`: `f` strictly decreases along `γ` after a time
  at which `df(v) < 0`.
* `IsMIntegralCurveOn.apply_eq_of_mvfderiv_apply_eq_zero`: `f` is constant along `γ` when
  `df(v) = 0` along it.
* `IsMIntegralCurveOn.apply_eq_of_mfderiv_apply_eq_zero`: a manifold-valued map `g` is constant
  along `γ` when `dg(v) = 0` along it.
* `IsMIntegralCurveOn.lt_apply_of_le_apply`, `IsMIntegralCurveOn.apply_lt_of_apply_le`: `γ` crosses
  a level of `f` only upwards when `df(v) > 0` along that level.
* `IsMIntegralCurve.apply_eq_of_forall_eq_zero`: an integral curve along which the vector field
  vanishes is constant.
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

/-- **An integral curve along which the field vanishes is constant.** If `v (γ t) = 0` for every
`t`, then the integral curve `γ` of `v` has zero derivative everywhere, so it is constant. -/
theorem apply_eq_of_forall_eq_zero [IsManifold I 1 M] (hγ : IsMIntegralCurve γ v)
    (hv : ∀ t, v (γ t) = 0) (s t : ℝ) : γ t = γ s :=
  MDifferentiable.apply_eq_of_mfderiv_eq_zero (fun u ↦ (hγ u).mdifferentiableAt)
    (fun u ↦ by
      rw [(hγ u).mfderiv, hv u, ContinuousLinearMap.smulRight_zero]
      -- The two zeros live in the tangent-space and the model-space spelling of one type.
      rfl) t s

end IsMIntegralCurve

namespace IsMIntegralCurveOn

/-- **Constancy along an integral curve.** If `f` is differentiable along an integral curve `γ` of
`v` on a preconnected set of times `s`, such as an interval, and `df(v) = 0` along `γ` on `s`, then
`f` is constant along `γ` on `s`. -/
theorem apply_eq_of_mvfderiv_apply_eq_zero {s : Set ℝ} (hγ : IsMIntegralCurveOn γ v s)
    (hs' : IsPreconnected s) (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    (hvf : ∀ t ∈ s, mvfderiv I f (γ t) (v (γ t)) = 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    f (γ t) = f (γ t₀) := by
  have hd (u : ℝ) (hu : u ∈ s) : HasDerivWithinAt (f ∘ γ) 0 s u := by
    simpa only [hvf u hu] using TauCeti.Manifold.hasDerivWithinAt_comp_curve (hf u hu) (hγ u hu)
  have hconv : Convex ℝ s := Real.convex_iff_isPreconnected.2 hs'
  simpa [sub_eq_zero] using hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ ↦ 0) (C := 0) hd (fun _ _ ↦ by simp) ht₀ ht

/-- **Constancy of a manifold-valued map along an integral curve.** If `g : M → N` is
differentiable along an integral curve `γ` of `v` on an open preconnected set of times `s`, such as
an open interval, and `dg(v) = 0` along `γ` on `s`, then `g` is constant along `γ` on `s`: the
curve stays in one fibre of `g`. -/
theorem apply_eq_of_mfderiv_apply_eq_zero {F H' N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J 1 N] {g : M → N} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ v s) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hg : ∀ t ∈ s, MDifferentiableAt I J g (γ t))
    (hvg : ∀ t ∈ s, mfderiv I J g (γ t) (v (γ t)) = 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    g (γ t) = g (γ t₀) := by
  -- The derivative of `g ∘ γ` at a time `u ∈ s` sends `r` to `r • dg(v) = 0`, so it vanishes.
  have hd (u : ℝ) (hu : u ∈ s) :
      MDifferentiableAt 𝓘(ℝ, ℝ) J (g ∘ γ) u ∧ mfderiv 𝓘(ℝ, ℝ) J (g ∘ γ) u = 0 := by
    have hγu := (hγ u hu).hasMFDerivAt (hs.mem_nhds hu)
    refine ⟨(hg u hu).comp u hγu.mdifferentiableAt, ?_⟩
    rw [mfderiv_comp u (hg u hu) hγu.mdifferentiableAt, hγu.mfderiv]
    refine ContinuousLinearMap.ext fun (r : ℝ) ↦ ?_
    -- The composite sends `r` to `dg (r • v)`; the tangent space of `ℝ` at `u` is `ℝ` itself, so
    -- this unfolding is definitional.
    calc (mfderiv I J g (γ u)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ u))) r
        = mfderiv I J g (γ u) (r • v (γ u)) := rfl
      _ = 0 := by rw [map_smul, hvg u hu, smul_zero]
  -- So `g ∘ γ` is locally constant on the open set `s`, hence constant on its preconnected
  -- subtype.
  have hloc (u : ℝ) (hu : u ∈ s) : (g ∘ γ) =ᶠ[𝓝 u] fun _ ↦ (g ∘ γ) u :=
    MDifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero
      (fun w hw ↦ (hd w hw).1.mdifferentiableWithinAt) hs (fun w hw ↦ (hd w hw).2) hu
  have hlc : IsLocallyConstant (s.domRestrict (g ∘ γ)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨u, hu⟩
    exact (continuous_subtype_val.tendsto (⟨u, hu⟩ : s)).eventually (hloc u hu)
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs'
  exact hlc.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨t₀, ht₀⟩

variable {s : Set ℝ} {c a b : ℝ}

/-- **Integral curves cross a level only upwards.** Let `γ` be an integral curve of `v` on an open
set containing `[a, b]`, with `f ∘ γ` continuous on `[a, b]`, and suppose that `f` is
differentiable with `df(v) > 0` at every point `γ t`, `t ∈ [a, b]`, of the level `f⁻¹(c)`. If
`c ≤ f (γ a)`, then `c < f (γ t)` for every `t ∈ (a, b]`. -/
theorem lt_apply_of_le_apply (hγ : IsMIntegralCurveOn γ v s) (hs : IsOpen s) (hab : Icc a b ⊆ s)
    (hf : ContinuousOn (f ∘ γ) (Icc a b))
    (hvf : ∀ t ∈ Icc a b, f (γ t) = c →
      MDifferentiableAt I 𝓘(ℝ) f (γ t) ∧ 0 < mvfderiv I f (γ t) (v (γ t)))
    (ha : c ≤ f (γ a)) : ∀ ⦃t⦄, t ∈ Ioc a b → c < f (γ t) :=
  TauCeti.lt_image_of_deriv_pos_boundary (g := f ∘ γ) (g' := fun t ↦ mvfderiv I f (γ t) (v (γ t)))
    hf (fun _ ht hft ↦
      ⟨TauCeti.Manifold.hasDerivAt_comp_curve (hvf _ ht hft).1
        ((hγ.isMIntegralCurveAt (hs.mem_nhds (hab ht))).hasMFDerivAt), (hvf _ ht hft).2⟩) ha

/-- **Integral curves cross a level only upwards, looking backwards.** Let `γ` be an integral curve
of `v` on an open set containing `[a, b]`, with `f ∘ γ` continuous on `[a, b]`, and suppose that
`f` is differentiable with `df(v) > 0` at every point `γ t`, `t ∈ [a, b]`, of the level `f⁻¹(c)`.
If `f (γ b) ≤ c`, then `f (γ t) < c` for every `t ∈ [a, b)`. -/
theorem apply_lt_of_apply_le (hγ : IsMIntegralCurveOn γ v s) (hs : IsOpen s) (hab : Icc a b ⊆ s)
    (hf : ContinuousOn (f ∘ γ) (Icc a b))
    (hvf : ∀ t ∈ Icc a b, f (γ t) = c →
      MDifferentiableAt I 𝓘(ℝ) f (γ t) ∧ 0 < mvfderiv I f (γ t) (v (γ t)))
    (hb : f (γ b) ≤ c) : ∀ ⦃t⦄, t ∈ Ico a b → f (γ t) < c := fun _ ht ↦ not_le.1 fun hct ↦
  (hγ.lt_apply_of_le_apply hs ((Icc_subset_Icc_left ht.1).trans hab)
    (hf.mono (Icc_subset_Icc_left ht.1)) (fun u hu ↦ hvf u (Icc_subset_Icc_left ht.1 hu)) hct
    ⟨ht.2, le_rfl⟩).not_ge hb

end IsMIntegralCurveOn
