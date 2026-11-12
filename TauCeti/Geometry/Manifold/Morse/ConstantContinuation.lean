/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.IntervalBase
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Prod
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# Trajectories of the continuation field of a constant path

A continuation from a Morse function `f₀` to a Morse function `f₁` on `M` counts trajectories of a
vector field on `M × ℝ` running from `(p, 0)` to `(q, 1)`, for critical points `p` of `f₀` and `q`
of `f₁`. For the large-constant product realization, the field has time component
`C t (1 - t²) - ∂ₜ f_t`, the negative gradient of `C h(t) + f_t(x)` with `h(t) = (t² - 1)² / 4`
for every metric `dt² + g_t`. For the constant path `f_t = f` there is no time derivative, and
with an adapted pseudo-gradient `X` of `f` in the space direction the field is the product field

`V(x, t) = (X x, C t (1 - t²))` (`TauCeti.constantContinuationField`).

This file determines all of its trajectories between the critical points `(p, 0)` and `(q, 1)` of
the slab, on a compact boundaryless manifold `M` and for `C > 0`.

* **Product structure.** A curve is an integral curve of `V` exactly when its components are an
  integral curve of `X` and a negative gradient trajectory of the base potential
  `TauCeti.intervalBasePotential C` (`TauCeti.isMIntegralCurve_constantContinuationField_iff`).
* **Trajectories across the slab.** The trajectories from `(p, 0)` to `(q, 1)` are the curves
  `s ↦ (φ_s y, q_C(s + τ))`, where `y` lies on a trajectory of `X` from `p` to `q`, `φ` is the flow
  of `X` and `q_C` is the base trajectory `TauCeti.intervalBaseOrbit C` from `0` to `1`. The two
  components run independently, so the unparametrized trajectories form the product of the
  trajectory set `W^u(p) ∩ W^s(q)` of `X` with the line of shifts `τ`.
* **Trajectories in an end level.** The trajectories from `(p, 0)` to `(q, 0)`, and likewise from
  `(p, 1)` to `(q, 1)`, stay in the level and are the trajectories of `X` from `p` to `q`. So the
  two ends of the slab carry the Morse trajectories of `f` itself.
* **The constant-path identity.** Under the Morse–Smale condition, if `ind p ≤ ind q` then a
  trajectory from `(p, 0)` to `(q, 1)` exists only for `q = p`, and it is then
  `s ↦ (p, q_C(s + τ))` for a shift `τ`. So between critical points of equal index there is
  exactly one unparametrized continuation trajectory from `(p, 0)` to `(p, 1)` and none from
  `(p, 0)` to `(q, 1)` with `q ≠ p`. These are the counts defining the continuation map, so for a
  constant path they form the identity matrix.

## Main declarations

* `TauCeti.constantContinuationField`: the field `(X x, C t (1 - t²))` on `M × ℝ`.
* `TauCeti.isMIntegralCurve_constantContinuationField_iff`: its integral curves are pairs.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMIntegralCurve_constantContinuationField_and_tendsto_iff`: the trajectories from `(p, 0)` to
  `(q, 1)`.
* `isMIntegralCurve_constantContinuationField_and_tendsto_level_iff`: the trajectories inside an
  end level.
* `IsMorseSmale.isMIntegralCurve_constantContinuationField_and_tendsto_iff_of_le`: the
  constant-path identity.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4, Exercise 1 (the continuation map of a constant path is the
  identity).
-/

public section

open Filter Set Topology
open scoped ContDiff Gradient Manifold

namespace TauCeti

section Field

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The **continuation field of a constant path** on `M × ℝ`: the product of a vector field `X` on
`M` with the negative gradient `C t (1 - t²)` of the base potential `C (t² - 1)² / 4` on `ℝ`.
Its time component is that of the continuation field of a path `f_t` of functions on `M`,
`C t (1 - t²) - ∂ₜ f_t`, for the constant path `f_t = f`; with an adapted pseudo-gradient `X` of
`f` in the space direction, it is the continuation field of that constant path. -/
noncomputable def constantContinuationField (X : (x : M) → TangentSpace I x) (C : ℝ) :
    (z : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ)) z :=
  Manifold.prodVectorField X fun t ↦ (-∇ (intervalBasePotential C) t : TangentSpace 𝓘(ℝ) t)

/-- The space component of the continuation field of a constant path is the field `X`. -/
@[simp]
theorem constantContinuationField_fst (X : (x : M) → TangentSpace I x) (C : ℝ) (z : M × ℝ) :
    (constantContinuationField X C z).1 = X z.1 :=
  Manifold.prodVectorField_fst _ _ z

/-- The time component of the continuation field of a constant path is `C t (1 - t²)`. -/
@[simp]
theorem constantContinuationField_snd (X : (x : M) → TangentSpace I x) (C : ℝ) (z : M × ℝ) :
    (constantContinuationField X C z).2 = C * z.2 * (1 - z.2 ^ 2) :=
  (Manifold.prodVectorField_snd _ _ z).trans (by rw [gradient_intervalBasePotential]; ring)

/-- **The trajectories of the continuation field of a constant path are pairs**: a curve in
`M × ℝ` is an integral curve of `constantContinuationField X C` exactly when its space component is
an integral curve of `X` and its time component a negative gradient trajectory of the base
potential `TauCeti.intervalBasePotential C`. -/
theorem isMIntegralCurve_constantContinuationField_iff {X : (x : M) → TangentSpace I x} {C : ℝ}
    {γ : ℝ → M × ℝ} :
    IsMIntegralCurve γ (constantContinuationField X C) ↔
      IsMIntegralCurve (fun s ↦ (γ s).1) X ∧
        IsIntegralCurve (fun s ↦ (γ s).2) (fun _ t ↦ -∇ (intervalBasePotential C) t) :=
  Manifold.isMIntegralCurve_prodVectorField_iff.trans <| and_congr Iff.rfl <|
    isMIntegralCurve_iff_isMIntegralCurveOn.trans <|
      isMIntegralCurveOn_iff_isIntegralCurveOn.trans isIntegralCurveOn_univ

end Field

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ} {p q : M} {γ : ℝ → M × ℝ}

namespace IsAdaptedPseudoGradient

section

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- An integral curve of an adapted pseudo-gradient from `p` to `q` is the orbit of a point of
`W^u(p) ∩ W^s(q)`. -/
private theorem mem_unstableSet_inter_stableSet_of_isMIntegralCurve {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) (hp : Tendsto γ atBot (𝓝 p)) (hq : Tendsto γ atTop (𝓝 q)) :
    γ 0 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ γ = fun s ↦ hX.flow s (γ 0) := by
  have hflow : γ = fun s ↦ hX.flow s (γ 0) := funext fun s ↦
    (hX.flow_apply_eq_of_isMIntegralCurve hγ s).symm
  rw [hflow] at hp hq
  exact ⟨⟨Flow.mem_unstableSet.2 hp, Flow.mem_stableSet.2 hq⟩, hflow⟩

/-- **The trajectories of the constant continuation across the slab.** For `C > 0`, the integral
curves of `constantContinuationField X C` tending to `(p, 0)` at `-∞` and to `(q, 1)` at `+∞` are
the curves `s ↦ (φ_s y, q_C(s + τ))`, for `y` on a trajectory of `X` from `p` to `q` and a shift
`τ`, where `φ` is the flow of `X` and `q_C` the base trajectory `TauCeti.intervalBaseOrbit C`. -/
theorem isMIntegralCurve_constantContinuationField_and_tendsto_iff (hC : 0 < C) :
    (IsMIntegralCurve γ (constantContinuationField X C) ∧ Tendsto γ atBot (𝓝 (p, 0)) ∧
        Tendsto γ atTop (𝓝 (q, 1))) ↔
      ∃ y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q, ∃ τ,
        γ = fun s ↦ (hX.flow s y, intervalBaseOrbit C (s + τ)) := by
  rw [isMIntegralCurve_constantContinuationField_iff]
  constructor
  · rintro ⟨⟨hγ₁, hγ₂⟩, hp, hq⟩
    obtain ⟨hy, hflow⟩ := hX.mem_unstableSet_inter_stableSet_of_isMIntegralCurve hγ₁
      ((continuous_fst.tendsto _).comp hp) ((continuous_fst.tendsto _).comp hq)
    obtain ⟨τ, hτ⟩ := exists_eq_intervalBaseOrbit_of_isIntegralCurve hC hγ₂
      ((continuous_snd.tendsto _).comp hp) ((continuous_snd.tendsto _).comp hq)
    exact ⟨_, hy, τ, funext fun s ↦ Prod.ext (congrFun hflow s) (congrFun hτ s)⟩
  · rintro ⟨y, hy, τ, rfl⟩
    have hshift : Tendsto (fun s : ℝ ↦ s + τ) atBot atBot := tendsto_atBot_add_const_right _ τ
      tendsto_id
    refine ⟨⟨hX.isMIntegralCurve_flow y, fun s ↦ ?_⟩, (Flow.mem_unstableSet.1 hy.1).prodMk_nhds
      ((tendsto_intervalBaseOrbit_atBot hC).comp hshift), (Flow.mem_stableSet.1 hy.2).prodMk_nhds
      ((tendsto_intervalBaseOrbit_atTop hC).comp (tendsto_atTop_add_const_right _ τ tendsto_id))⟩
    exact (isIntegralCurve_intervalBaseOrbit C (s + τ)).comp_add_const s τ

/-- **The trajectories of the constant continuation in an end level.** For `C > 0` and a critical
point `a` of the base potential, the integral curves of `constantContinuationField X C` tending
to `(p, a)` at `-∞` and to `(q, a)` at `+∞` stay in the level `t = a` and are the trajectories of
`X` from `p` to `q`. For `a = 0` and `a = 1` these are the trajectories in the two ends of the
slab. -/
theorem isMIntegralCurve_constantContinuationField_and_tendsto_level_iff (hC : 0 < C) {a : ℝ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1) :
    (IsMIntegralCurve γ (constantContinuationField X C) ∧ Tendsto γ atBot (𝓝 (p, a)) ∧
        Tendsto γ atTop (𝓝 (q, a))) ↔
      ∃ y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q, γ = fun s ↦ (hX.flow s y, a) := by
  rw [isMIntegralCurve_constantContinuationField_iff]
  constructor
  · rintro ⟨⟨hγ₁, hγ₂⟩, hp, hq⟩
    obtain ⟨hy, hflow⟩ := hX.mem_unstableSet_inter_stableSet_of_isMIntegralCurve hγ₁
      ((continuous_fst.tendsto _).comp hp) ((continuous_fst.tendsto _).comp hq)
    have hconst := eq_const_of_isIntegralCurve_intervalBasePotential hC hγ₂
      (by rcases ha with rfl | rfl | rfl <;> norm_num)
      ((continuous_snd.tendsto (p, a)).comp hp) ((continuous_snd.tendsto (q, a)).comp hq)
    exact ⟨_, hy, funext fun s ↦ Prod.ext (congrFun hflow s) (congrFun hconst s)⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨hX.isMIntegralCurve_flow y, fun s ↦ ?_⟩,
      (Flow.mem_unstableSet.1 hy.1).prodMk_nhds tendsto_const_nhds,
      (Flow.mem_stableSet.1 hy.2).prodMk_nhds tendsto_const_nhds⟩
    have h0 : -∇ (intervalBasePotential C) a = 0 := by
      rw [gradient_intervalBasePotential]
      rcases ha with rfl | rfl | rfl <;> ring
    exact (hasDerivAt_const s a).congr_deriv h0.symm

end

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **The constant-path continuation trajectories.** Under the Morse–Smale condition,
for `C > 0`, a critical point `p` and a point `q` with `ind p ≤ ind q`, an integral curve of
`constantContinuationField X C` runs from `(p, 0)` to `(q, 1)` exactly when `q = p` and it is
`s ↦ (p, q_C(s + τ))` for a shift `τ`. In particular, between critical points of equal index the
trajectories from `(p, 0)` to `(q, 1)` form a single orbit of the time translations if `q = p`,
and there are none if `q ≠ p`: the trajectory counts of the continuation map of a constant path
form the identity matrix. -/
theorem isMIntegralCurve_constantContinuationField_and_tendsto_iff_of_le (hC : 0 < C)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ manifoldMorseIndex 𝓘(ℝ, E) f q) :
    (IsMIntegralCurve γ (constantContinuationField X C) ∧ Tendsto γ atBot (𝓝 (p, 0)) ∧
        Tendsto γ atTop (𝓝 (q, 1))) ↔
      q = p ∧ ∃ τ, γ = fun s ↦ (p, intervalBaseOrbit C (s + τ)) := by
  have hfix := hX.flow_apply_of_mfderiv_eq_zero (mem_criticalPoints_iff_mfderiv_eq_zero.1 hp)
  rw [hX.isMIntegralCurve_constantContinuationField_and_tendsto_iff hC]
  constructor
  · rintro ⟨y, hy, τ, rfl⟩
    -- A trajectory of `X` from `p` to `q ≠ p` would force `ind q < ind p`.
    obtain rfl : q = p := by
      by_contra hqp
      exact (h.manifoldMorseIndex_lt hf (Ne.symm hqp) ⟨y, hy⟩).not_ge hind
    -- A trajectory of `X` from `p` back to `p` is constant.
    obtain rfl := hX.eq_of_mem_unstableSet_inter_stableSet_self
      (hf.contMDiff.mdifferentiable (by simp)) hy
    exact ⟨rfl, τ, funext fun s ↦ by rw [hfix]⟩
  · rintro ⟨rfl, τ, rfl⟩
    exact ⟨q, ⟨Flow.self_mem_unstableSet_iff.2 hfix, Flow.self_mem_stableSet_iff.2 hfix⟩, τ,
      funext fun s ↦ by rw [hfix]⟩

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
