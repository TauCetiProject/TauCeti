/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.TransverseDisc
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.Geometry.Manifold.TransverseDisc
import TauCeti.Analysis.Normed.Module.Complemented

/-!
# Model-flow gluing of broken pseudo-gradient trajectories in a Morse box

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `x`, `r` critical points with
`ind p > ind x > ind r`. In the split coordinates `(u, v)` (contracting and expanding) of a Morse
chart `φ` at `x`, the model flow is the split hyperbolic flow `(u, v) ↦ (e^{-t} u, e^t v)`. It is
the flow of `X` only in a Morse chart in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, such as the
chart given by the definition of an adapted pseudo-gradient; the results here hold for an arbitrary
Morse chart and are stated for the model flow. A broken trajectory from `p` to `r` through `x`
enters the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` along the stable manifold of `x` and leaves it along the
unstable manifold.

The gluing theorems in the split model take as input discs through the entrance and exit points:
`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt` a disc whose expanding
component has invertible derivative and one whose contracting component has invertible derivative,
and `TauCeti.exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt` families of
such discs, given as discs with a parameter. This file supplies them:

* the level cut `W^u(p) ∩ {f = c}` through the entrance point is a disc of dimension `ind p - 1`
  whose expanding component has surjective derivative, because `W^u(p)` and `W^s(x)` are
  transverse and `X`, tangent to both, is not tangent to the level. The kernel of that derivative
  has dimension `ind p - ind x - 1`, that of the family of trajectories from `p` to `x`; it is zero
  when `ind p = ind x + 1`, and the derivative is then invertible;
* dually, the level cut `W^s(r) ∩ {f = c}` through the exit point is a disc whose contracting
  component has surjective derivative, with kernel of dimension `ind x - ind r - 1`.

These are instances of
`TauCeti.exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top`. A complement of
the kernel parametrizes each disc as a family of transverse discs
(`ContinuousLinearMap.exists_isInvertible_prod_of_surjective`), and the parameter of a point of a
level cut is determined by the model orbit through it, since in the chart `f - f x` is half of
`Σᵢ uᵢ² - Σⱼ vⱼ²`, which strictly decreases along the model orbits
(`TauCeti.MorseChart.eq_of_splitQuadraticFlow_eq`). Feeding both families to the model gluing
theorem shows that, in the split coordinates, the model-flow orbits from `W^u(p)` to `W^s(r)` near
the broken one, together with the broken ones, form a product of `[0, r₀]` with a ball of dimension
`ind p - ind r - 2`, whose face at `0` consists of the broken pairs. This is the local model of a
collar of the compactified space of trajectories from `p` to `r` along its face of trajectories
broken once at `x`. When `ind p = ind x + 1 = ind r + 2` the ball is a point, and the orbits form a
half-open arc whose closure adds exactly the broken trajectory and is homeomorphic to a closed
interval: the local model at the broken trajectories of the compactified space of index-two
trajectories. Assembling these local models into a manifold with corners is not done here.

## Main results

In the namespace `TauCeti.MorseChart`:

* `eq_of_splitQuadraticFlow_eq`: a model orbit meets a level of `f` at most once.
* `exists_mem_nhds_eq_of_splitQuadraticFlow_eq`: the parameter of a point of a parametrized level
  cut is determined by the model orbit through it.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_unstableSet_level_param_of_ne`,
  `IsMorseSmale.exists_unstableSet_level_param`: the entrance disc in `W^u(p)`, in any index
  difference and in index difference one.
* `IsMorseSmale.exists_stableSet_level_param_of_ne`, `IsMorseSmale.exists_stableSet_level_param`:
  the exit disc in `W^s(r)`.
* `IsMorseSmale.exists_homeomorph_closure_biUnion_splitGluingPairs`: the chart `[0, r₀] × S` of
  model-flow glued trajectories near once-broken trajectories, in any index differences, in the
  split coordinates of a Morse chart.
* `IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`: the closed interval chart, in index
  differences one.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x y : M}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **A model orbit meets a level of `f` once.** In a Morse chart `φ` at `x`, let `w` and `w'` be
points of the chart on a common level of `f`. If their split coordinates lie on a common orbit of
the split hyperbolic flow `(u, v) ↦ (e^{-t} u, e^t v)`, then `w = w'`. Indeed, in the split
coordinates `(u, v)` the function `f - f x` is half of `Σᵢ uᵢ² - Σⱼ vⱼ²`
(`TauCeti.MorseChart.apply_toChart_symm_coord_symm_splitCoord_symm`), and along the orbit of a
point other than the centre this quadratic form is strictly decreasing
(`TauCeti.strictAnti_sum_sq_sub_sum_sq_splitQuadraticFlow`); the orbit of the centre is the centre.
-/
theorem eq_of_splitQuadraticFlow_eq (φ : MorseChart E f x) {w w' : M}
    (hw : w ∈ φ.toChart.source) (hw' : w' ∈ φ.toChart.source) (hf : f w = f w') {t t' : ℝ}
    (h : splitQuadraticFlow t (φ.splitCoord (φ.coord (φ.toChart w))) =
      splitQuadraticFlow t' (φ.splitCoord (φ.coord (φ.toChart w')))) :
    w = w' := by
  set a := φ.splitCoord (φ.coord (φ.toChart w))
  set b := φ.splitCoord (φ.coord (φ.toChart w'))
  -- The split coordinates of `w` lie on the orbit of those of `w'`, at time `s = t' - t`.
  set s := t' - t
  have hab : a = splitQuadraticFlow s b := by
    have := congrArg (splitQuadraticFlow (-t)) h
    rwa [← Flow.map_add, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply,
      neg_add_eq_sub] at this
  -- On the chart, `f = f x + (Σ uᵢ² - Σ vⱼ²) / 2`.
  have hval (v : M) (hv : v ∈ φ.toChart.source) :
      f v = f x + 2⁻¹ * (∑ i, (φ.splitCoord (φ.coord (φ.toChart v))).fst i ^ 2 -
        ∑ i, (φ.splitCoord (φ.coord (φ.toChart v))).snd i ^ 2) := by
    have hz : φ.coord.symm (φ.splitCoord.symm (φ.splitCoord (φ.coord (φ.toChart v)))) ∈
        φ.toChart.target := by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact φ.toChart.map_source hv
    have := φ.apply_toChart_symm_coord_symm_splitCoord_symm hz
    rwa [φ.toChart_symm_coord_symm_splitCoord_symm_splitCoord_coord_toChart hv] at this
  -- If `b ≠ 0`, the quadratic form takes the same value at `a = φ_s b` and at `b = φ_0 b`, and it
  -- strictly decreases along the orbit, so `s = 0`. If `b = 0`, its orbit is `0`.
  have hab' : a = b := by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hab, hb, splitQuadraticFlow_apply]
      simp
    have hva : f w = f x + 2⁻¹ * (∑ i, a.fst i ^ 2 - ∑ i, a.snd i ^ 2) := hval w hw
    have hvb : f w' = f x + 2⁻¹ * (∑ i, b.fst i ^ 2 - ∑ i, b.snd i ^ 2) := hval w' hw'
    have hs : s = 0 := (strictAnti_sum_sq_sub_sum_sq_splitQuadraticFlow hb).injective <| by
      simp only [Flow.map_zero_apply, ← hab]
      linarith
    rw [hab, hs, Flow.map_zero_apply]
  rw [← φ.toChart_symm_coord_symm_splitCoord_symm_splitCoord_coord_toChart hw,
    ← φ.toChart_symm_coord_symm_splitCoord_symm_splitCoord_coord_toChart hw']
  exact congrArg (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) hab'

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **Model orbits determine the parameters of a level cut.** Let `ι` parametrize, near `0`, a
subset `S` of a level of `f` through a point `ι 0` of a Morse chart `φ` at `x`, and be injective
near `0`. Then near `0` the parameters are sent into any prescribed neighbourhood `U`
of `ι 0`, into `S` and into the level, and a parameter is determined by the orbit of the split
hyperbolic flow through the split coordinates of its point
(`TauCeti.MorseChart.eq_of_splitQuadraticFlow_eq`). This is the hypothesis of the gluing of
families of transverse discs that the entrance or exit point of an orbit through a disc determines
its parameter. -/
theorem exists_mem_nhds_eq_of_splitQuadraticFlow_eq (φ : MorseChart E f x) {F : Type*}
    [TopologicalSpace F] [Zero F] {ι : F → M} {S U : Set M} (hι : ContinuousAt ι 0)
    (hι₀ : ι 0 ∈ φ.toChart.source)
    (hιS : ∀ᶠ z in 𝓝 0, ι z ∈ S ∧ f (ι z) = f (ι 0)) (hinj : ∃ W ∈ 𝓝 (0 : F), InjOn ι W)
    (hU : U ∈ 𝓝 (ι 0)) :
    ∃ U' ∈ 𝓝 (0 : F), (∀ z ∈ U', ι z ∈ U ∧ ι z ∈ S ∧ f (ι z) = f (ι 0)) ∧
      ∀ z ∈ U', ∀ z' ∈ U', ∀ t t' : ℝ,
        splitQuadraticFlow t (φ.splitCoord (φ.coord (φ.toChart (ι z)))) =
          splitQuadraticFlow t' (φ.splitCoord (φ.coord (φ.toChart (ι z')))) → z = z' := by
  obtain ⟨W, hW, hinj⟩ := hinj
  have hUι : ∀ᶠ z in 𝓝 (0 : F), ι z ∈ U := hι.preimage_mem_nhds hU
  have hWι : ∀ᶠ z in 𝓝 (0 : F), z ∈ W := hW
  have hφι : ∀ᶠ z in 𝓝 (0 : F), ι z ∈ φ.toChart.source :=
    hι.preimage_mem_nhds (φ.toChart.open_source.mem_nhds hι₀)
  exact ⟨{z | ι z ∈ U ∧ (ι z ∈ S ∧ f (ι z) = f (ι 0)) ∧ z ∈ W ∧ ι z ∈ φ.toChart.source},
    hUι.and (hιS.and (hWι.and hφι)), fun z hz ↦ ⟨hz.1, hz.2.1⟩,
    fun z hz z' hz' t t' h ↦ hinj hz.2.2.1 hz'.2.2.1 (φ.eq_of_splitQuadraticFlow_eq hz.2.2.2
      hz'.2.2.2 (hz.2.1.2.trans hz'.2.1.2.symm) h)⟩

end MorseChart

namespace IsAdaptedPseudoGradient

/-- **The entrance disc of an unstable manifold, in any index difference.** Let `x` be a critical
point with Morse chart `φ`, and `p ≠ x` a critical point, for a Morse–Smale adapted
pseudo-gradient. Let `y` be a point of a trajectory from `p` to `x` in the chart, near which the
stable manifold of `x` lies in the contracting coordinates of `φ` (the second split coordinate
vanishes). Then the level cut `W^u(p) ∩ {f = f y}`, of dimension `ind p - 1`, is near `y` a disc
whose split coordinates have a derivative `ψ'` at `y` with surjective expanding component: there is
a parametrization `ι` of it with `ι 0 = y`, injective near `0` and reaching every point of the cut
near `y` from small parameters, whose split coordinates are strictly differentiable at `0` with
derivative `ψ'`. The kernel of the expanding component of `ψ'` is tangent to the family of the
trajectories from `p` to `x`, of dimension `ind p - ind x - 1`. -/
theorem IsMorseSmale.exists_unstableSet_level_param_of_ne {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p : M} (hpx : p ≠ x)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.unstableSet p ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      Function.Surjective (WithLp.sndL 2 ℝ _ _ ∘L ψ') ∧
      Module.finrank ℝ F + 1 = manifoldMorseIndex 𝓘(ℝ, E) f p ∧
      (∃ V ∈ 𝓝 (0 : F), InjOn ι V) ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet p → f w = f y →
        ∃ z ∈ V, ι z = w := by
  obtain ⟨L, q, -, hyq, hq, hs⟩ :=
    hX.exists_isSliceChart_unstableSet hf (hX.mfderiv_eq_zero_of_mem_unstableSet hy.1) hy.1
  set P := WithLp.sndL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    (φ.splitCoordL : E →L[ℝ] _)
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (0, b))
    exact ⟨u, by simp [P, hu]⟩
  have hX0 : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet p)
      hy.1)
  have hX0' : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet x) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet x)
      hy.2)
  obtain ⟨F, ι, ι', hι0, hι, hιs, hd, hsurj, hdim, hinj, hexh⟩ :=
    exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top (by simp) hq hs hyq
      hy.1 hy.2 isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn
      (h.span_mtangentConeAt_sup_eq_top hy) hX0 hX0'
      (hX.mvfderiv_apply_lt_zero y
        (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hpx hy)).ne
      φ.mem_maximalAtlas hyφ hPs (by simpa [P] using hloc)
  refine ⟨F, ι, (φ.splitCoordL : E →L[ℝ] _) ∘L ι', hι0, hι, hιs, ?_, ?_, ?_, hinj, hexh⟩
  · simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd
  · rwa [← ContinuousLinearMap.comp_assoc]
  · rw [hdim, hX.finrank_span_mtangentConeAt_unstableSet hf hy.1]

/-- **The entrance disc of an unstable manifold.** Let `x` be a critical point with Morse chart
`φ`, and `p` a critical point of index `ind x + 1`, for a Morse–Smale adapted pseudo-gradient. Let
`y` be a point of a trajectory from `p` to `x` in the chart, near which the stable manifold of `x`
lies in the contracting coordinates of `φ` (the second split coordinate vanishes). Then the level
cut `W^u(p) ∩ {f = f y}` is, near `y`, a disc transverse to the stable set of the model flow: there
is a parametrization `ι` of it with `ι 0 = y`, reaching every point of the cut near `y` from small
parameters, whose split coordinates are strictly differentiable at `0` with derivative `ψ'`
such that the expanding component of `ψ'` is invertible. -/
theorem IsMorseSmale.exists_unstableSet_level_param {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.unstableSet p ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      (WithLp.sndL 2 ℝ _ _ ∘L ψ').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet p → f w = f y →
        ∃ z ∈ V, ι z = w := by
  obtain ⟨F, ι, ψ', hι0, hι, hιs, hd, hsurj, hdim, -, hexh⟩ :=
    h.exists_unstableSet_level_param_of_ne hf (by rintro rfl; omega) φ hy hyφ hloc
  -- The expanding component is a surjection between spaces of the same dimension.
  have hdim' : Module.finrank ℝ F = Module.finrank ℝ ({i // ¬φ.weight i = 1} → ℝ) := by
    rw [φ.finrank_snd_splitCoord]
    omega
  exact ⟨F, ι, ψ', hι0, hι, hιs, hd,
    (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim').2
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (WithLp.sndL 2 ℝ _ _ ∘L ψ' : F →ₗ[ℝ] _)) hdim').2 hsurj), hexh⟩

/-- **The exit disc of a stable manifold, in any index difference.** Let `x` be a critical point
with Morse chart `φ`, and `r ≠ x` a critical point, for a Morse–Smale adapted pseudo-gradient. Let
`y` be a point of a trajectory from `x` to `r` in the chart, near which the unstable manifold of
`x` lies in the expanding coordinates of `φ` (the first split coordinate vanishes). Then the level
cut `W^s(r) ∩ {f = f y}`, of dimension `dim M - ind r - 1`, is near `y` a disc whose split
coordinates have a derivative `ψ'` at `y` with surjective contracting component: there is a
parametrization `ι` of it with `ι 0 = y`, injective near `0` and reaching every point of the cut
near `y` from small parameters, whose split coordinates are strictly differentiable at `0` with
derivative `ψ'`. The kernel of the contracting component of `ψ'` is tangent to the family of the
trajectories from `x` to `r`, of dimension `ind x - ind r - 1`. -/
theorem IsMorseSmale.exists_stableSet_level_param_of_ne {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {r : M} (hxr : x ≠ r)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.stableSet r ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      Function.Surjective (WithLp.fstL 2 ℝ _ _ ∘L ψ') ∧
      Module.finrank ℝ F + 1 + manifoldMorseIndex 𝓘(ℝ, E) f r = Module.finrank ℝ E ∧
      (∃ V ∈ 𝓝 (0 : F), InjOn ι V) ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet r → f w = f y →
        ∃ z ∈ V, ι z = w := by
  obtain ⟨L, q, -, hyq, hq, hs⟩ :=
    hX.exists_isSliceChart_stableSet (hX.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  set P := WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L
    (φ.splitCoordL : E →L[ℝ] _)
  have hPs : Function.Surjective P := fun b ↦ by
    obtain ⟨u, hu⟩ := φ.splitCoordL.surjective (WithLp.toLp 2 (b, 0))
    exact ⟨u, by simp [P, hu]⟩
  have hX0 : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet r) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet r)
      hy.2)
  have hX0' : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant
      (hX.flow.isInvariant_unstableSet x) hy.1)
  obtain ⟨F, ι, ι', hι0, hι, hιs, hd, hsurj, hdim, hinj, hexh⟩ :=
    exists_param_inter_preimage_surjective_of_span_mtangentConeAt_sup_eq_top (by simp) hq hs hyq
      hy.2 hy.1 isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn
      (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top hy) hX0 hX0'
      (hX.mvfderiv_apply_lt_zero y
        (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hxr hy)).ne
      φ.mem_maximalAtlas hyφ hPs (by simpa [P] using hloc)
  refine ⟨F, ι, (φ.splitCoordL : E →L[ℝ] _) ∘L ι', hι0, hι, hιs, ?_, ?_, ?_, hinj, hexh⟩
  · simpa using φ.splitCoordL.hasStrictFDerivAt.comp 0 hd
  · rwa [← ContinuousLinearMap.comp_assoc]
  · rw [hdim, hX.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hy.2]

/-- **The exit disc of a stable manifold.** Let `x` be a critical point with Morse chart `φ`, and
`r` a critical point of index `ind x - 1`, for a Morse–Smale adapted pseudo-gradient. Let `y` be a
point of a trajectory from `x` to `r` in the chart, near which the unstable manifold of `x` lies in
the expanding coordinates of `φ` (the first split coordinate vanishes). Then the level cut
`W^s(r) ∩ {f = f y}` is, near `y`, a disc transverse to the unstable set of the model flow: there is
a parametrization `ι` of it with `ι 0 = y`, reaching every point of the cut near `y` from small
parameters, whose split coordinates are strictly differentiable at `0` with derivative `ψ'`
such that the contracting component of `ψ'` is invertible. -/
theorem IsMorseSmale.exists_stableSet_level_param {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {r : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (φ : MorseChart E f x) (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r)
    (hyφ : y ∈ φ.toChart.source)
    (hloc : ∀ᶠ w in 𝓝 y, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) :
    ∃ (F : Submodule ℝ E) (ι : F → M)
      (ψ' : F →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      ι 0 = y ∧ ContinuousAt ι 0 ∧
      (∀ᶠ z in 𝓝 0, ι z ∈ hX.flow.stableSet r ∧ f (ι z) = f y) ∧
      HasStrictFDerivAt (fun z ↦ φ.splitCoord (φ.coord (φ.toChart (ι z)))) ψ' 0 ∧
      (WithLp.fstL 2 ℝ _ _ ∘L ψ').IsInvertible ∧
      ∀ V ∈ 𝓝 (0 : F), ∀ᶠ w in 𝓝 y, w ∈ hX.flow.stableSet r → f w = f y →
        ∃ z ∈ V, ι z = w := by
  obtain ⟨F, ι, ψ', hι0, hι, hιs, hd, hsurj, hdim, -, hexh⟩ :=
    h.exists_stableSet_level_param_of_ne hf (by rintro rfl; omega) φ hy hyφ hloc
  -- The contracting component is a surjection between spaces of the same dimension.
  have hdim' : Module.finrank ℝ F = Module.finrank ℝ ({i // φ.weight i = 1} → ℝ) := by
    have := φ.finrank_fst_splitCoord_add_manifoldMorseIndex
    omega
  exact ⟨F, ι, ψ', hι0, hι, hιs, hd,
    (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim').2
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (WithLp.fstL 2 ℝ _ _ ∘L ψ' : F →ₗ[ℝ] _)) hdim').2 hsurj), hexh⟩

/-- **Gluing a broken trajectory in a Morse box.** Let `p`, `x`, `r` be critical points of
consecutive indices `ind p = ind x + 1 = ind r + 2` of a Morse function, with a Morse–Smale adapted
pseudo-gradient and a Morse chart `φ` at `x`. Consider a broken trajectory from `p` to `r` through
`x`, entering the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of the split coordinates `(u, v)` of `φ` at a point `y₁`
of `W^u(p) ∩ W^s(x)` on the entrance face `‖u‖ = ε`, and leaving it at a point `y₂` of
`W^u(x) ∩ W^s(r)` on the exit face `‖v‖ = ε`, where the stable and unstable manifolds of `x` lie in
the corresponding coordinate subspaces.

Read in the split coordinates, the pairs formed by the entrance point, under the model flow, of the
orbit of a point of `W^u(p) ∩ {f = f y₁}` near `y₁`, and the exit point of the orbit of a point of
`W^s(r) ∩ {f = f y₂}` near `y₂`, when the model passage map joins them, form a half-open arc
`TauCeti.splitGluingPairs`. Its closure is homeomorphic to a closed interval, with the
broken pair of coordinates of `y₁` and `y₂` as the endpoint `0`, and adds no other point; the
inverse coordinate is the norm of the expanding entrance coordinate divided by `ε`. Every point of
the arc comes from points of the two level cuts in prescribed neighbourhoods `U` of `y₁` and `V` of
`y₂`, and conversely every such pair of points near `(y₁, y₂)` whose model orbits are joined by the
passage map lies on the arc.

The chart `φ` is arbitrary, so this is a statement about the model flow. When `X` is the linear
field `z ↦ (-wᵢ zᵢ)ᵢ` in `φ`, model orbits that stay in a box inside the chart are the orbits of the
pseudo-gradient (`TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime`). -/
theorem IsMorseSmale.exists_homeomorph_closure_splitGluingPairs {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p r y₁ y₂ : M}
    (hpx : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1)
    (hxr : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (φ : MorseChart E f x)
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x) (hy₁φ : y₁ ∈ φ.toChart.source)
    (hy₂ : y₂ ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r) (hy₂φ : y₂ ∈ φ.toChart.source)
    (hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)
    (hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)
    {ε : ℝ} (hε : 0 < ε) (hy₁ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε)
    (hy₂ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε)
    {U V : Set M} (hU : U ∈ 𝓝 y₁) (hV : V ∈ 𝓝 y₂) :
    ∃ (r₀ : ℝ) (hr₀ : 0 < r₀) (g : ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ)
      (k : ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      (∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k),
        (∀ q, (e.symm q : ℝ) = ‖q.val.1.snd‖ / ε) ∧
        (e ⟨0, left_mem_Icc.2 hr₀.le⟩).val = (φ.splitCoord (φ.coord (φ.toChart y₁)),
          φ.splitCoord (φ.coord (φ.toChart y₂)))) ∧
      closure (splitGluingPairs ε r₀ g k) = insert (φ.splitCoord (φ.coord (φ.toChart y₁)),
        φ.splitCoord (φ.coord (φ.toChart y₂))) (splitGluingPairs ε r₀ g k) ∧
      (∀ q ∈ splitGluingPairs ε r₀ g k,
        (∃ w ∈ U, w ∈ hX.flow.unstableSet p ∧ f w = f y₁ ∧
          splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = q.1) ∧
        ∃ w ∈ V, w ∈ hX.flow.stableSet r ∧ f w = f y₂ ∧
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = q.2) ∧
      ∀ᶠ w : M × M in 𝓝 (y₁, y₂), w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ →
        w.2 ∈ hX.flow.stableSet r → f w.2 = f y₂ →
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
          (φ.splitCoord (φ.coord (φ.toChart w.1)))).snd ≠ 0 →
        splitPassage ε (splitQuadraticFlow
            (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
            (φ.splitCoord (φ.coord (φ.toChart w.1)))) =
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
            (φ.splitCoord (φ.coord (φ.toChart w.2))) →
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
            (φ.splitCoord (φ.coord (φ.toChart w.1))),
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
            (φ.splitCoord (φ.coord (φ.toChart w.2)))) ∈ splitGluingPairs ε r₀ g k := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψ', hexh₁⟩ :=
    h.exists_unstableSet_level_param hf hpx φ hy₁ hy₁φ hloc₁
  obtain ⟨F₂, ι₂, χ', hι₂0, hι₂, hι₂s, hχ, hχ', hexh₂⟩ :=
    h.exists_stableSet_level_param hf hxr φ hy₂ hy₂φ hloc₂
  -- The broken pair: `y₁` lies on the stable set of `x` and `y₂` on its unstable set.
  have hψ₀ : Φ (ι₁ 0) = WithLp.toLp 2 ((Φ y₁).fst, 0) := by
    rw [hι₁0, ← hloc₁.self_of_nhds hy₁.2]
    rfl
  have hχ₀ : Φ (ι₂ 0) = WithLp.toLp 2 (0, (Φ y₂).snd) := by
    rw [hι₂0, ← hloc₂.self_of_nhds hy₂.1]
    rfl
  -- Parameters near `0` whose points lie in the prescribed neighbourhoods and level cuts.
  set U' : Set F₁ := {z | ι₁ z ∈ U ∧ ι₁ z ∈ hX.flow.unstableSet p ∧ f (ι₁ z) = f y₁}
  set V' : Set F₂ := {z | ι₂ z ∈ V ∧ ι₂ z ∈ hX.flow.stableSet r ∧ f (ι₂ z) = f y₂}
  have hU'0 : U' ∈ 𝓝 0 := by
    have hU₁ : ∀ᶠ z in 𝓝 (0 : F₁), ι₁ z ∈ U := hι₁.preimage_mem_nhds (by rwa [hι₁0])
    exact hU₁.and hι₁s
  have hV'0 : V' ∈ 𝓝 0 := by
    have hV₂ : ∀ᶠ z in 𝓝 (0 : F₂), ι₂ z ∈ V := hι₂.preimage_mem_nhds (by rwa [hι₂0])
    exact hV₂.and hι₂s
  obtain ⟨r₀, hr₀, g, k, ⟨e, he, he₀⟩, hcl, hpairs, hexh⟩ :=
    exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt hψ hψ' hψ₀ hy₁ε hχ hχ' hχ₀
      hy₂ε hε hU'0 hV'0
  refine ⟨r₀, hr₀, g, k, ⟨e, he, by rw [he₀, ← hψ₀, ← hχ₀, hι₁0, hι₂0]⟩,
    by rw [hcl, ← hψ₀, ← hχ₀, hι₁0, hι₂0], ?_, ?_⟩
  · intro q hq
    obtain ⟨⟨z₁, ⟨hz₁U, hz₁s, hz₁f⟩, hz₁⟩, z₂, ⟨hz₂V, hz₂s, hz₂f⟩, hz₂⟩ := hpairs q hq
    exact ⟨⟨ι₁ z₁, hz₁U, hz₁s, hz₁f, hz₁⟩, ι₂ z₂, hz₂V, hz₂s, hz₂f, hz₂⟩
  · -- Points of the level cuts near `y₁` and `y₂` are reached from small parameters.
    obtain ⟨A₁, hA₁, A₂, hA₂, hA⟩ := mem_nhds_prod_iff.1 hexh
    filter_upwards [(hexh₁ A₁ hA₁).prodMk_nhds (hexh₂ A₂ hA₂)] with w hw hw₁s hw₁f hw₂s hw₂f
    obtain ⟨z₁, hz₁, hz₁w⟩ := hw.1 hw₁s hw₁f
    obtain ⟨z₂, hz₂, hz₂w⟩ := hw.2 hw₂s hw₂f
    rw [← hz₁w, ← hz₂w]
    have hq := hA (mk_mem_prod hz₁ hz₂)
    rw [mem_ofPred_eq] at hq
    exact hq

/-- **Gluing once-broken trajectories in a Morse box, in any index difference.** Let `p`, `x`, `r`
be critical points of a Morse function with `ind p = ind x + m₁ + 1` and `ind x = ind r + m₂ + 1`,
with a Morse–Smale adapted pseudo-gradient and a Morse chart `φ` at `x`. Consider a broken
trajectory from `p` to `r` through `x`, entering the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of the split
coordinates `(u, v)` of `φ` at a point `y₁` of `W^u(p) ∩ W^s(x)` on the entrance face `‖u‖ = ε`,
and leaving it at a point `y₂` of `W^u(x) ∩ W^s(r)` on the exit face `‖v‖ = ε`, where the stable
and unstable manifolds of `x` lie in the corresponding coordinate subspaces.

The trajectories from `p` to `x` near the first piece form a family of dimension `m₁`, and those
from `x` to `r` near the second piece one of dimension `m₂`. Accordingly there are maps `g` and
`k` such that, read in the split coordinates, the entrance points of the model orbits of the level
cut `W^u(p) ∩ {f = f y₁}` near `y₁` lie on the graphs `v ↦ (g (s, v), v)`, `s ∈ ℝ^m₁`, and the
exit points of the model orbits of the level cut `W^s(r) ∩ {f = f y₂}` near `y₂` on the graphs
`u ↦ (u, k (t, u))`, `t ∈ ℝ^m₂`; the parameter `0` gives the graphs through `y₁` and `y₂`. For a
small closed ball `S` of parameters `(s, t)`:

* the closure of the union over `(s, t) ∈ S` of the arcs
  `splitGluingPairs ε r₀ (g (s, ·)) (k (t, ·))` of entrance and exit points joined by the model
  passage map is homeomorphic to `[0, r₀] × S`,
  with the gluing coordinate `‖v‖ / ε` of the entrance point as first inverse coordinate, a pair of
  the arc of `(s, t)` at positive gluing coordinate, and the broken pair
  `((g (s, 0), 0), (0, k (t, 0)))` at gluing coordinate `0`;
* the closure adds exactly these broken pairs;
* the broken pairs and the pairs on the arcs consist of the entrance point of the model orbit of a
  point of the first level cut in a prescribed neighbourhood `U` of `y₁` and the exit point of the
  model orbit of a point of the second level cut in a prescribed neighbourhood `V` of `y₂`;
* conversely, the entrance and exit points of the model orbits of two points of the level cuts near
  `y₁` and `y₂`, when the passage map joins them, form a pair on one of the arcs.

So, once the broken pairs are added, the model-flow trajectories from `W^u(p)` to `W^s(r)` near
the broken trajectory form a product of `[0, r₀]` with a ball of dimension `m₁ + m₂`: the local
model of a collar of the compactified space of trajectories from `p` to `r` along its face of
trajectories broken at `x`. The parameter of an entrance point is determined by its point on the
level cut, as a model orbit meets the level once (`TauCeti.MorseChart.eq_of_splitQuadraticFlow_eq`).
For `m₁ = m₂ = 0` the parameter ball is a point, as in
`IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`. -/
theorem IsMorseSmale.exists_homeomorph_closure_biUnion_splitGluingPairs
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r y₁ y₂ : M} {m₁ m₂ : ℕ}
    (hpx : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + m₁ + 1)
    (hxr : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f r + m₂ + 1)
    (φ : MorseChart E f x)
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x) (hy₁φ : y₁ ∈ φ.toChart.source)
    (hy₂ : y₂ ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet r) (hy₂φ : y₂ ∈ φ.toChart.source)
    (hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)
    (hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet x →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)
    {ε : ℝ} (hε : 0 < ε) (hy₁ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε)
    (hy₂ε : ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε)
    {U V : Set M} (hU : U ∈ 𝓝 y₁) (hV : V ∈ 𝓝 y₂) :
    ∃ (r₀ ρ : ℝ) (hr₀ : 0 < r₀) (_ : 0 < ρ)
      (g : EuclideanSpace ℝ (Fin m₁) × ({i // ¬φ.weight i = 1} → ℝ) → {i // φ.weight i = 1} → ℝ)
      (k : EuclideanSpace ℝ (Fin m₂) × ({i // φ.weight i = 1} → ℝ) → {i // ¬φ.weight i = 1} → ℝ),
      g 0 = (φ.splitCoord (φ.coord (φ.toChart y₁))).fst ∧
      k 0 = (φ.splitCoord (φ.coord (φ.toChart y₂))).snd ∧
      (∃ e : (Icc 0 r₀ ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ :
          Set (ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)))) ≃ₜ
          closure (⋃ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
            splitGluingPairs ε r₀ (fun v ↦ g (q.1, v)) (fun u ↦ k (q.2, u))),
        (∀ w, (e.symm w : ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂))).1 =
          ‖w.val.1.snd‖ / ε) ∧
        (∀ q : (Icc 0 r₀ ×ˢ
            closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ :
            Set (ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)))),
          0 < (q : ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂))).1 →
          (e q).val ∈ splitGluingPairs ε r₀
            (fun v ↦ g ((q : ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂))).2.1, v))
            (fun u ↦ k ((q : ℝ × (EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂))).2.2, u)))
          ∧
        ∀ q (hq : q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ),
          (e ⟨(0, q), left_mem_Icc.2 hr₀.le, hq⟩).val =
            (WithLp.toLp 2 (g (q.1, 0), 0), WithLp.toLp 2 (0, k (q.2, 0)))) ∧
      closure (⋃ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
          splitGluingPairs ε r₀ (fun v ↦ g (q.1, v)) (fun u ↦ k (q.2, u))) =
        (⋃ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
          splitGluingPairs ε r₀ (fun v ↦ g (q.1, v)) (fun u ↦ k (q.2, u))) ∪
        (fun q ↦ (WithLp.toLp 2 (g (q.1, 0), 0), WithLp.toLp 2 (0, k (q.2, 0)))) ''
          closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ ∧
      (∀ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
        (∃ w ∈ U, w ∈ hX.flow.unstableSet p ∧ f w = f y₁ ∧
          splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = WithLp.toLp 2 (g (q.1, 0), 0)) ∧
        ∃ w ∈ V, w ∈ hX.flow.stableSet r ∧ f w = f y₂ ∧
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = WithLp.toLp 2 (0, k (q.2, 0))) ∧
      (∀ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
        ∀ a ∈ splitGluingPairs ε r₀ (fun v ↦ g (q.1, v)) (fun u ↦ k (q.2, u)),
        (∃ w ∈ U, w ∈ hX.flow.unstableSet p ∧ f w = f y₁ ∧
          splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = a.1) ∧
        ∃ w ∈ V, w ∈ hX.flow.stableSet r ∧ f w = f y₂ ∧
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
            (φ.splitCoord (φ.coord (φ.toChart w))) = a.2) ∧
      ∀ᶠ w : M × M in 𝓝 (y₁, y₂), w.1 ∈ hX.flow.unstableSet p → f w.1 = f y₁ →
        w.2 ∈ hX.flow.stableSet r → f w.2 = f y₂ →
        (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
          (φ.splitCoord (φ.coord (φ.toChart w.1)))).snd ≠ 0 →
        splitPassage ε (splitQuadraticFlow
            (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
            (φ.splitCoord (φ.coord (φ.toChart w.1)))) =
          splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
            (φ.splitCoord (φ.coord (φ.toChart w.2))) →
        ∃ q ∈ closedBall (0 : EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin m₂)) ρ,
          (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w.1))))
              (φ.splitCoord (φ.coord (φ.toChart w.1))),
            splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w.2))))
              (φ.splitCoord (φ.coord (φ.toChart w.2)))) ∈
            splitGluingPairs ε r₀ (fun v ↦ g (q.1, v)) (fun u ↦ k (q.2, u)) := by
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w))
  obtain ⟨F₁, ι₁, ψ', hι₁0, hι₁, hι₁s, hψ, hψs, hdim₁, ⟨W₁, hW₁, hinj₁⟩, hexh₁⟩ :=
    h.exists_unstableSet_level_param_of_ne hf (by rintro rfl; omega) φ hy₁ hy₁φ hloc₁
  obtain ⟨F₂, ι₂, χ', hι₂0, hι₂, hι₂s, hχ, hχs, hdim₂, ⟨W₂, hW₂, hinj₂⟩, hexh₂⟩ :=
    h.exists_stableSet_level_param_of_ne hf (by rintro rfl; omega) φ hy₂ hy₂φ hloc₂
  -- Parameters of the two families: complements of the kernels of the transverse components.
  obtain ⟨c, hc⟩ := ContinuousLinearMap.exists_isInvertible_prod_of_surjective
    (F := EuclideanSpace ℝ (Fin m₁)) hψs
    (by rw [finrank_euclideanSpace_fin, φ.finrank_snd_splitCoord]; omega)
  obtain ⟨d, hd⟩ := ContinuousLinearMap.exists_isInvertible_prod_of_surjective
    (F := EuclideanSpace ℝ (Fin m₂)) hχs
    (by have := φ.finrank_fst_splitCoord_add_manifoldMorseIndex
        rw [finrank_euclideanSpace_fin]; omega)
  -- The broken pair: `y₁` lies on the stable set of `x` and `y₂` on its unstable set.
  have hψ₀ : Φ (ι₁ 0) = WithLp.toLp 2 ((Φ y₁).fst, 0) := by
    rw [hι₁0, ← hloc₁.self_of_nhds hy₁.2]; rfl
  have hχ₀ : Φ (ι₂ 0) = WithLp.toLp 2 (0, (Φ y₂).snd) := by
    rw [hι₂0, ← hloc₂.self_of_nhds hy₂.1]; rfl
  -- Near `0`, the parameters are sent into `U` and `V` and the level cuts, and the entrance or exit
  -- point of the model orbit through a point of a level cut determines its parameter.
  obtain ⟨U', hU'0, hU', hψU⟩ := φ.exists_mem_nhds_eq_of_splitQuadraticFlow_eq hι₁
    (hι₁0 ▸ hy₁φ) (hι₁0 ▸ hι₁s) ⟨W₁, hW₁, hinj₁⟩ (hι₁0 ▸ hU)
  obtain ⟨V', hV'0, hV', hχV⟩ := φ.exists_mem_nhds_eq_of_splitQuadraticFlow_eq hι₂
    (hι₂0 ▸ hy₂φ) (hι₂0 ▸ hι₂s) ⟨W₂, hW₂, hinj₂⟩ (hι₂0 ▸ hV)
  obtain ⟨r₀, ρ, hr₀, hρ, g, k, hg₀, hk₀, he, hcl, hbroken, hpairs, hev⟩ :=
    exists_homeomorph_closure_biUnion_splitGluingPairs_of_hasStrictFDerivAt hψ
      c.hasStrictFDerivAt hc hψ₀ (map_zero c) hy₁ε hχ d.hasStrictFDerivAt hd hχ₀ (map_zero d)
      hy₂ε hε hU'0 hV'0 (fun z hz z' hz' h ↦ by rw [hψU z hz z' hz' _ _ h])
      (fun z hz z' hz' h ↦ by rw [hχV z hz z' hz' _ _ h])
  refine ⟨r₀, ρ, hr₀, hρ, g, k, hg₀, hk₀, he, hcl, fun q hq ↦ ?_, fun q hq a ha ↦ ?_, ?_⟩
  · obtain ⟨⟨z₁, hz₁, -, hz₁e⟩, z₂, hz₂, -, hz₂e⟩ := hbroken q hq
    exact ⟨⟨ι₁ z₁, (hU' z₁ hz₁).1, (hU' z₁ hz₁).2.1, hι₁0 ▸ (hU' z₁ hz₁).2.2, hz₁e⟩,
      ι₂ z₂, (hV' z₂ hz₂).1, (hV' z₂ hz₂).2.1, hι₂0 ▸ (hV' z₂ hz₂).2.2, hz₂e⟩
  · obtain ⟨⟨z₁, hz₁, -, hz₁e⟩, z₂, hz₂, -, hz₂e⟩ := hpairs q hq a ha
    exact ⟨⟨ι₁ z₁, (hU' z₁ hz₁).1, (hU' z₁ hz₁).2.1, hι₁0 ▸ (hU' z₁ hz₁).2.2, hz₁e⟩,
      ι₂ z₂, (hV' z₂ hz₂).1, (hV' z₂ hz₂).2.1, hι₂0 ▸ (hV' z₂ hz₂).2.2, hz₂e⟩
  · -- Points of the level cuts near `y₁` and `y₂` are reached from small parameters.
    obtain ⟨A₁, hA₁, A₂, hA₂, hA⟩ := mem_nhds_prod_iff.1 hev
    filter_upwards [(hexh₁ A₁ hA₁).prodMk_nhds (hexh₂ A₂ hA₂)] with w hw hw₁s hw₁f hw₂s hw₂f
    obtain ⟨z₁, hz₁, hz₁w⟩ := hw.1 hw₁s hw₁f
    obtain ⟨z₂, hz₂, hz₂w⟩ := hw.2 hw₂s hw₂f
    obtain ⟨hq₁, hq₂⟩ := hA (mk_mem_prod hz₁ hz₂)
    rw [← hz₁w, ← hz₂w]
    exact fun hne hpass ↦ ⟨_, hq₁, hq₂ hne hpass⟩

end IsAdaptedPseudoGradient

end TauCeti
