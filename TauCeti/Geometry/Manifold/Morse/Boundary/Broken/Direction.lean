/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Broken.Comparison
import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Crossing

/-!
# The gluing direction at a broken trajectory points outward

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold, linear in Morse
charts `φp`, `φr`, `φq` at critical points `p`, `r`, `q`. Consider a broken trajectory `(u, v)`,
with `u` from `p` to `r` through `y₀` and `v` from `r` to `q` through `z₀`, and trajectories from
`p` to `q` through points `yₙ → y₀` whose orbits reach points `zₙ → z₀` at times `Tₙ → ∞`, as in
`TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`; such orbits cross the
Morse chart of `r` along its linear flow
(`TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`). Their
comparison maps tend to `G = (id × B₂) ∘ A`, where `A = C_{pr}(y₀)` and `B = (B₁, B₂) = C_{rq}(z₀)`.
When `X` is Morse–Smale and `ind p = ind r + 1 = ind q + 2`, the maps `A` and `B` are isomorphisms
(`TauCeti.IsAdaptedPseudoGradient.bijective_trajectoryComparison`) and the line `ker G` is spanned
by the **gluing direction** `g`, the vector with `A g = (0, w)` and `B w = (1, 0)`;
`TauCeti.LinearAlgebra.Orientation.Breaking` orients `ker G` by `-ε(u) ε(v)` times `g`. This file
shows on which side of `y₀` the trajectories `yₙ` lie: the function `y ↦ ℓ (n(y))` below, for a
linear form `ℓ` positive on the leaving direction, vanishes at `y₀`, is eventually positive at the
`yₙ` and decreases along `g`. In this sense `g` points from the nearby trajectories towards `y₀`,
out of the space of unbroken trajectories at the broken end.

Fix a time `a` of linear forward flow of `y₀` and a time `b` of linear backward flow of `z₀` in the
chart `φr`, and read the coordinates of negative weight `n(y) = N(φr (Φ_a y))` of points near `y₀`.

* **The point `y₀` lies on the stable set of `r`**, so `n(y₀) = 0`
  (`negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`).
* **The nearby trajectories leave `r` along `v`.** Across the chart the flow is the linear flow
  (`coord_toChart_flow_add`), which multiplies the coordinates of negative weight, all of weight
  `-1`, by `e^{t}`. So `e^{Tₙ - a - b} n(yₙ)` is the vector of coordinates of negative weight of
  `Φ_{-b} zₙ`, and it tends to the **leaving direction** `ζ = N(φr (Φ_{-b} z₀))` of `v`
  (`tendsto_exp_smul_negativeCoord_toChart_flow_of_broken`), which is nonzero
  (`negativeCoord_toChart_flow_neg_ne_zero`). In particular, for every linear form `ℓ` with
  `ℓ ζ > 0`, eventually `ℓ (n(yₙ)) > 0`
  (`eventually_pos_negativeCoord_toChart_flow_of_broken`).
* **The gluing direction leaves the trajectories.** The unstable frame of `r` at `z₀` sends
  `e^{b} ζ` to the velocity `X z₀`, which is tangent to `W^s(q)` and decreases `f`, so
  `B (e^{b} ζ) = (df (X z₀), 0)` with `df (X z₀) < 0`
  (`trajectoryComparison_exp_smul_negativeCoord`). Hence `w` is a negative multiple of `ζ`
  (`eq_smul_negativeCoord_of_trajectoryComparison_eq`), and the derivative at `y₀` of
  `y ↦ ℓ (n(y))` along the unstable frame of the gluing direction `g` is negative
  (`apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`). By continuity
  of the unstable frame along `W^u(p)`, so is its derivative at points of `W^u(p)` near `y₀` along
  the frame of vectors near `g`
  (`eventually_apply_negativeCoord_mvfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`).

So the smooth function `h = ℓ ∘ n` vanishes at the broken end `y₀`, is positive on the nearby
unbroken trajectories and decreases along the gluing direction: the trajectories approach `y₀` from
the side of `-g`, and `g` points out of the space of unbroken trajectories. With the orientation
`-ε(u) ε(v) g` of the limiting tangent line, this is the comparison of the gluing direction with
the outward direction that turns the signed count of broken trajectories, whose vanishing is
`∂ ∘ ∂ = 0` (`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff`), into a
signed count of the ends of compact oriented one-manifolds.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `tendsto_exp_smul_negativeCoord_toChart_flow_of_broken`: near a broken trajectory, the rescaled
  coordinates of negative weight tend to the leaving direction of its second component.
* `eventually_pos_negativeCoord_toChart_flow_of_broken`: the nearby trajectories lie on the side of
  the leaving direction.
* `trajectoryComparison_exp_smul_negativeCoord`: the comparison map sends the leaving direction to
  `(df (X z₀), 0)`.
* `eq_smul_negativeCoord_of_trajectoryComparison_eq`: the vector `w` with `B w = (1, 0)` is a
  negative multiple of the leaving direction.
* `apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`: the gluing
  direction decreases the coordinates of negative weight on the side of the leaving direction.
* `eventually_apply_negativeCoord_mvfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`: so
  do vectors near the gluing direction, at points of `W^u(p)` near the broken end.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the boundary orientation of the compactified space of
  index-two trajectories at a broken trajectory).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (orientations and the Morse complex with integer coefficients).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p r q : M} {φp : MorseChart E f p}
  {φr : MorseChart E f r} {φq : MorseChart E f q}
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
include hφr

/-! ### Trajectories near a broken trajectory -/

/-- **Trajectories near a broken trajectory leave `r` along its second component.** Let `y₀` be a
point of `W^s(r)` with a time `a` of linear forward flow in the Morse chart `φr`, and `z₀` a point
of `W^u(r)` with a time `b` of linear backward flow. Let `yₙ → y₀` and `Tₙ → ∞` with
`Φ_{Tₙ} yₙ → z₀`. Then `e^{Tₙ - a - b}` times the coordinates of negative
weight of `Φ_a yₙ` tend to the leaving direction, the coordinates of negative weight of
`Φ_{-b} z₀`. -/
theorem tendsto_exp_smul_negativeCoord_toChart_flow_of_broken (hf : IsMorse 𝓘(ℝ, E) f)
    {y₀ z₀ : M} {a b : ℝ} (hy₀r : y₀ ∈ hX.flow.stableSet r) (ha : a ∈ hX.linearForwardTimes φr y₀)
    (hz₀r : z₀ ∈ hX.flow.unstableSet r) (hb : b ∈ hX.linearBackwardTimes φr z₀)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hT : Tendsto T l atTop) (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀)) :
    Tendsto (fun n ↦ Real.exp (T n - a - b) • φr.negativeCoord (φr.toChart (hX.flow a (y n)))) l
      (𝓝 (φr.negativeCoord (φr.toChart (hX.flow (-b) z₀)))) := by
  -- The rescaled coordinates are those of `Φ_{-b} zₙ`, which tends to `Φ_{-b} z₀` in the chart.
  have hcont : Tendsto
      (fun n ↦ φr.negativeCoord (φr.toChart (hX.flow (-b) (hX.flow (T n) (y n))))) l
      (𝓝 (φr.negativeCoord (φr.toChart (hX.flow (-b) z₀)))) :=
    (φr.negativeCoord.continuous_of_finiteDimensional.tendsto _).comp
      ((φr.toChart.continuousAt ((hX.mem_linearBackwardTimes φr).1 hb).1).tendsto.comp
        (((hX.contMDiff_flow_apply (-b)).continuous.tendsto z₀).comp hz))
  have hya : ∀ᶠ n in l, hX.flow a (y n) ∈ φr.toChart.source :=
    (((hX.contMDiff_flow_apply a).continuous.tendsto y₀).comp hy).eventually
      (φr.toChart.open_source.mem_nhds ((hX.mem_linearForwardTimes φr).1 ha).1)
  refine hcont.congr' ?_
  filter_upwards [hya,
    eventually_forall_linearFlow_mem_target_of_broken hφr hf hy₀r ha hz₀r hb hy hz,
    hT.eventually (eventually_ge_atTop (a + b))] with n hn hcn hTn
  -- Across the chart the linear flow multiplies the coordinates of negative weight by `e^{t}`.
  rw [← Flow.map_add, show -b + T n = T n - a - b + a by ring]
  refine φr.negativeCoord_eq_exp_smul_of_coord_eq
    (coord_toChart_flow_add hφr hn fun t ht ↦ hcn t ?_)
  rwa [uIcc_of_le (by linarith)] at ht

/-- **Trajectories near a broken trajectory lie on the side of the leaving direction.** Under the
hypotheses of `tendsto_exp_smul_negativeCoord_toChart_flow_of_broken`, for every linear form `ℓ`
positive on the leaving direction, `ℓ` is eventually positive on the coordinates of negative weight
of `Φ_a yₙ`. -/
theorem eventually_pos_negativeCoord_toChart_flow_of_broken (hf : IsMorse 𝓘(ℝ, E) f)
    {y₀ z₀ : M} {a b : ℝ} (hy₀r : y₀ ∈ hX.flow.stableSet r) (ha : a ∈ hX.linearForwardTimes φr y₀)
    (hz₀r : z₀ ∈ hX.flow.unstableSet r) (hb : b ∈ hX.linearBackwardTimes φr z₀)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hT : Tendsto T l atTop) (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀))
    (ℓ : ({i // φr.weight i < 0} → ℝ) →ₗ[ℝ] ℝ)
    (hℓ : 0 < ℓ (φr.negativeCoord (φr.toChart (hX.flow (-b) z₀)))) :
    ∀ᶠ n in l, 0 < ℓ (φr.negativeCoord (φr.toChart (hX.flow a (y n)))) := by
  have h := ((ℓ.continuous_of_finiteDimensional.tendsto _).comp
    (tendsto_exp_smul_negativeCoord_toChart_flow_of_broken hφr hf hy₀r ha hz₀r hb hy hT
      hz)).eventually (lt_mem_nhds hℓ)
  filter_upwards [h] with n hn
  rw [comp_apply, map_smul, smul_eq_mul] at hn
  exact pos_of_mul_pos_right hn (Real.exp_pos _).le

/-! ### The gluing direction -/

variable (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφq

/-- **The comparison map on the leaving direction.** Let `z` lie in `W^u(r) ∩ W^s(q)` and `b` be a
time of linear backward flow of `z` in the Morse chart `φr`. The comparison map `C_{rq}(z)` sends
`e^{b}` times the leaving direction, the coordinates of negative weight of `Φ_{-b} z`, to
`(df (X z), 0)`: the unstable frame sends it to the velocity `X z`, which is tangent to `W^s(q)`. -/
theorem trajectoryComparison_exp_smul_negativeCoord (hf : IsMorse 𝓘(ℝ, E) f) {z : M}
    (hzu : z ∈ hX.flow.unstableSet r) (hzs : z ∈ hX.flow.stableSet q) {b : ℝ}
    (hb : b ∈ hX.linearBackwardTimes φr z) :
    hX.trajectoryComparison φr φq z
        (Real.exp b • φr.negativeCoord (φr.toChart (hX.flow (-b) z))) =
      (mvfderiv 𝓘(ℝ, E) f z (X z), 0) := by
  rw [trajectoryComparison_apply, unstableFrame_exp_smul_negativeCoord hφr hf hzu hb,
    (stableNormal_eq_zero_iff hφq hzs (X z)).2 (Submodule.subset_span
      (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet q) hzs))]

/-- **The vector `w` with `B w = (1, 0)` is a negative multiple of the leaving direction.** Let
`z` lie in `W^u(r) ∩ W^s(q)` with `r ≠ q`, let `b` be a time of linear backward flow of `z` in the
Morse chart `φr`, and suppose that the comparison map `B = C_{rq}(z)` is injective, as it is when
`ind r = ind q + 1` and `X` is Morse–Smale (`bijective_trajectoryComparison`). If `B w = (1, 0)`,
then `w` is `e^{b} / df (X z)` times the leaving direction; here `df (X z) < 0`, since `z` is not a
critical point (`mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet`). -/
theorem eq_smul_negativeCoord_of_trajectoryComparison_eq (hf : IsMorse 𝓘(ℝ, E) f) (hrq : r ≠ q)
    {z : M} (hz : z ∈ hX.flow.unstableSet r ∩ hX.flow.stableSet q) {b : ℝ}
    (hb : b ∈ hX.linearBackwardTimes φr z) (hinj : Injective (hX.trajectoryComparison φr φq z))
    {w : {i // φr.weight i < 0} → ℝ} (hw : hX.trajectoryComparison φr φq z w = (1, 0)) :
    w = ((mvfderiv 𝓘(ℝ, E) f z (X z))⁻¹ * Real.exp b) •
      φr.negativeCoord (φr.toChart (hX.flow (-b) z)) := by
  have hd := hX.mvfderiv_apply_lt_zero z
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hrq hz)
  refine hinj ?_
  rw [hw, mul_smul, map_smul, trajectoryComparison_exp_smul_negativeCoord hφr hφq hf hz.1 hz.2 hb,
    Prod.smul_mk, smul_eq_mul, inv_mul_cancel₀ hd.ne, smul_zero]

/-- **The gluing direction points from the nearby trajectories towards the broken end.** Let `a` be
a time of linear forward flow of `y₀` in the Morse chart `φr`, let `z` lie in `W^u(r) ∩ W^s(q)`
with `r ≠ q` and with a time `b` of linear backward flow in `φr`, and suppose that the comparison
map `B = C_{rq}(z)` is injective. Let `g` be a gluing direction: `C_{pr}(y₀) g = (0, w)` with
`B w = (1, 0)`. Then for every linear form `ℓ` positive on the leaving direction, the derivative at
`y₀` of `y ↦ ℓ (N(φr (Φ_a y)))`, read through `φr ∘ Φ_a` on the coordinates `N` of negative weight,
is negative along the unstable frame of `g`.

By `eventually_pos_negativeCoord_toChart_flow_of_broken` this function is positive at the
trajectories near the broken trajectory through `y₀` and `z`, and it vanishes at `y₀` when `y₀`
lies in `W^s(r)` (`negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`): the gluing direction is
the outward direction of the space of trajectories at the broken end. -/
theorem apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq
    (hf : IsMorse 𝓘(ℝ, E) f) (hrq : r ≠ q) {y₀ z : M} {a b : ℝ}
    (ha : a ∈ hX.linearForwardTimes φr y₀) (hz : z ∈ hX.flow.unstableSet r ∩ hX.flow.stableSet q)
    (hb : b ∈ hX.linearBackwardTimes φr z) (hinj : Injective (hX.trajectoryComparison φr φq z))
    {g : {i // φp.weight i < 0} → ℝ} {w : {i // φr.weight i < 0} → ℝ}
    (hg : hX.trajectoryComparison φp φr y₀ g = (0, w))
    (hw : hX.trajectoryComparison φr φq z w = (1, 0))
    (ℓ : ({i // φr.weight i < 0} → ℝ) →ₗ[ℝ] ℝ)
    (hℓ : 0 < ℓ (φr.negativeCoord (φr.toChart (hX.flow (-b) z)))) :
    ℓ (φr.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y₀
      (hX.unstableFrame φp y₀ g))) < 0 := by
  have hd := hX.mvfderiv_apply_lt_zero z
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hrq hz)
  have hweq := eq_smul_negativeCoord_of_trajectoryComparison_eq hφr hφq hf hrq hz hb hinj hw
  -- The normal coordinates of `W^s(r)` at `y₀` are `e^{-a}` times the coordinates of negative
  -- weight read through `φr ∘ Φ_a`, and they send the frame of `g` to `w`.
  have hN : hX.stableNormal φr y₀ (hX.unstableFrame φp y₀ g) = w := by
    simpa using congrArg Prod.snd hg
  rw [stableNormal_apply hφr ha] at hN
  have hexp : φr.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y₀
      (hX.unstableFrame φp y₀ g)) = Real.exp a • w := by
    rw [← hN, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  rw [hexp, hweq, smul_smul, map_smul, smul_eq_mul]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (Real.exp_pos a) (mul_neg_of_neg_of_pos (inv_lt_zero.2 hd)
      (Real.exp_pos b))) hℓ

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
include hφp

/-- **Near the broken end the gluing direction keeps pointing outward.** Under the hypotheses of
`apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`, let `y₀` lie in
`W^u(p)`, let `yₙ ∈ W^u(p)` tend to `y₀`, and let `vₙ` tend to the gluing direction `g`. Then
eventually the derivative at `yₙ` of `y ↦ ℓ (N(φr (Φ_a y)))` along the unstable frame of `vₙ` is
negative: the unstable frame of `p` varies continuously along `W^u(p)`
(`continuousWithinAt_mvfderiv_comp_unstableFrame`).

Tangent vectors to the trajectories near the broken one whose frame coordinates tend to a positive
multiple of `g`, such as positively oriented ones when `ker G` is oriented by `g`, therefore
decrease this function, which is positive on these trajectories
(`eventually_pos_negativeCoord_toChart_flow_of_broken`). -/
theorem eventually_apply_negativeCoord_mvfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq
    (hf : IsMorse 𝓘(ℝ, E) f) (hrq : r ≠ q) {y₀ z : M} {a b : ℝ}
    (hy₀ : y₀ ∈ hX.flow.unstableSet p) (ha : a ∈ hX.linearForwardTimes φr y₀)
    (hz : z ∈ hX.flow.unstableSet r ∩ hX.flow.stableSet q) (hb : b ∈ hX.linearBackwardTimes φr z)
    (hinj : Injective (hX.trajectoryComparison φr φq z))
    {g : {i // φp.weight i < 0} → ℝ} {w : {i // φr.weight i < 0} → ℝ}
    (hg : hX.trajectoryComparison φp φr y₀ g = (0, w))
    (hw : hX.trajectoryComparison φr φq z w = (1, 0))
    (ℓ : ({i // φr.weight i < 0} → ℝ) →ₗ[ℝ] ℝ)
    (hℓ : 0 < ℓ (φr.negativeCoord (φr.toChart (hX.flow (-b) z))))
    {ι : Type*} {l : Filter ι} {y : ι → M} {v : ι → {i // φp.weight i < 0} → ℝ}
    (hy : Tendsto y l (𝓝 y₀)) (hyu : ∀ᶠ n in l, y n ∈ hX.flow.unstableSet p)
    (hv : Tendsto v l (𝓝 g)) :
    ∀ᶠ n in l, ℓ (φr.negativeCoord (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) (y n)
      (hX.unstableFrame φp (y n) (v n)))) < 0 := by
  -- The derivative along the frame is continuous along `W^u(p)`, and so is its value at `vₙ`.
  have hframe := (hX.continuousWithinAt_mvfderiv_comp_unstableFrame hφp hf
    ((contMDiffAt_toChart_comp_flow ((hX.mem_linearForwardTimes φr).1 ha).1).of_le
      (by norm_cast)) hy₀).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hy, hyu⟩)
  have happ := (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hframe.prodMk_nhds hv)
  have hlim := ((ℓ.comp φr.negativeCoord).continuous_of_finiteDimensional.tendsto _).comp happ
  have hneg := apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq hφr hφq
    hf hrq ha hz hb hinj hg hw ℓ hℓ
  simp only [comp_apply, ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply] at hlim ⊢
  exact hlim.eventually (gt_mem_nhds hneg)

end IsAdaptedPseudoGradient

end TauCeti
