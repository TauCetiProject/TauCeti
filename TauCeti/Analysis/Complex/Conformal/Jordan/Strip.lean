/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.CrossRatio
public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import TauCeti.Analysis.Complex.UpperHalfPlane.Log
import TauCeti.Analysis.Complex.Conformal.Strip.Basic

/-!
# Conformal maps of the strip onto a Jordan domain with two marked boundary points

Let `Ω` be a bounded domain of `ℂ` whose frontier is a Jordan curve, and let `x ≠ y` be two points
of that frontier. They cut the frontier into two arcs, and `Ω` is a *bigon* with corners `x` and
`y`. This file shows that `Ω` is the image of the strip `ℝ × (0, 1) = {z | 0 < z.im < 1}` under a
holomorphic bijection `u` which extends continuously and injectively to the closed strip, carries
the two boundary lines `ℝ` and `ℝ + i` onto `frontier Ω \ {x, y}`, and tends to `x` at the negative
end and to `y` at the positive end of the strip. Two such maps whose lower boundary lines have
images that meet differ by a translation of the strip in the real direction.

These are the holomorphic strips of Lagrangian Floer theory and of Heegaard Floer homology in their
simplest local model: a strip `u : ℝ × [0, 1] → Σ` with `u(s, 0)` on one curve and `u(s, 1)` on
another, running from the corner `x` to the corner `y`, whose domain is an embedded bigon. The
results here say that such strips exist, and that two of them whose lower boundary lines run along
the same arc are related by the translation action of `ℝ`.

## Main results

* `TauCeti.exists_continuousOn_bijOn_strip_of_isJordanCurve_frontier`: **existence**. There is a
  holomorphic bijection of the open strip onto `Ω`, continuous on the closed strip, which maps the
  closed strip bijectively onto `closure Ω \ {x, y}` and its two boundary lines onto
  `frontier Ω \ {x, y}`, and tends to `x` as `re z → -∞` and to `y` as `re z → ∞`.
* `TauCeti.eqOn_add_of_tendsto_of_bijOn_strip`: **uniqueness up to translation**. Two holomorphic
  bijections `u` and `v` of the open strip onto `Ω` with the same limits at the two ends which have
  the same boundary limit at the points `s` and `t` of the lower boundary line satisfy
  `u z = v (z + (t - s))` on the strip.
* `TauCeti.exists_eqOn_add_of_continuousOn_strip`: hence two such maps which are continuous on the
  closed strip, and whose lower boundary lines have intersecting images, differ by a translation on
  the closed strip.

The exponential `z ↦ exp (π z)` maps the open strip onto the upper half-plane, the closed strip onto
the closed upper half-plane with `0` removed, the union of the two boundary lines onto the real line
with `0` removed, and the two ends to `0` and `∞` (`TauCeti.bijOn_exp_pi_mul_add_strip` and its
companions). Existence follows from Carathéodory's theorem on the closed upper half-plane,
`TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier`, with `∞` sent to
`y`, after translating a preimage of `x` to `0`. For uniqueness, the real Möbius transformation
`w ↦ (w - 1) / w` and the logarithm give a holomorphic bijection of the upper half-plane onto the
strip (`TauCeti.bijOn_log_sub_div_sub_div_pi` and its companions) sending the real points `1`, `0`
and `-1` to the negative end, the positive end and the point `log 2 / π` of the lower boundary line.
Composed with it, two strip maps with the same limits at the ends and at that point become conformal
maps of the upper half-plane onto `Ω` with the same limits at three real points, which coincide by
the three-point normalization
`TauCeti.eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn`.

The uniqueness statements here assume that the two maps meet on their lower boundary lines. For
maps which, like those of the existence statement, extend continuously to the closed strip without
taking the values `x` and `y` there, `TauCeti.exists_eqOn_add_of_bijOn_of_notMem_image` removes
that assumption: a holomorphic automorphism of the strip fixing both ends is a translation
(`TauCeti.exists_eqOn_add_of_bijOn_strip`), so it preserves each boundary line. The existence
statement does not say which of the two arcs carries the lower boundary line.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Sections 1--2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), 1027--1158.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane
open scoped Real

namespace TauCeti

/-! ### Existence -/

/-- **A Jordan bigon is the conformal image of a strip.** Let `Ω` be a bounded, connected open
subset of `ℂ` whose frontier is a Jordan curve, and let `x ≠ y` be points of that frontier. Then
there is a map `u`, holomorphic on the open strip `0 < z.im < 1` and continuous on the closed strip,
which maps the open strip bijectively onto `Ω`, the closed strip bijectively onto
`closure Ω \ {x, y}` and its two boundary lines bijectively onto `frontier Ω \ {x, y}`, and which
tends to `x` as `re z → -∞` and to `y` as `re z → ∞` within the closed strip. -/
theorem exists_continuousOn_bijOn_strip_of_isJordanCurve_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsConnected Ω) (hΩb : IsBounded Ω) (hΩJ : IsJordanCurve (frontier Ω)) {x y : ℂ}
    (hx : x ∈ frontier Ω) (hy : y ∈ frontier Ω) (hxy : x ≠ y) :
    ∃ u : ℂ → ℂ, ContinuousOn u {z | z.im ∈ Icc 0 1} ∧
      DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1} ∧ BijOn u {z | z.im ∈ Ioo 0 1} Ω ∧
      BijOn u {z | z.im ∈ Icc 0 1} (closure Ω \ {x, y}) ∧
      BijOn u {z | z.im = 0 ∨ z.im = 1} (frontier Ω \ {x, y}) ∧
      Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 x) ∧
      Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Icc 0 1}) (𝓝 y) := by
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfy⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ hy
  -- a real preimage `a` of `x`
  obtain ⟨z₀, hz₀, hfz₀⟩ := hfR.surjOn ⟨hx, hxy⟩
  set a : ℝ := z₀.re
  have ha : (a : ℂ) = z₀ := Complex.ext (by simp [a]) (by simpa using hz₀.symm)
  have hfa : f a = x := ha ▸ hfz₀
  set T : ℂ → ℂ := fun z => cexp (π * z) + a
  have hdiff : Differentiable ℂ T := fun z =>
    ((differentiableAt_const _).mul differentiableAt_id).cexp.add_const _
  have hpair (S : Set ℂ) : (S \ {y}) \ {x} = S \ {x, y} := by
    rw [sdiff_sdiff, union_comm, singleton_union]
  have hcl := hfcl.sdiff_singleton (a := (a : ℂ)) (by simp)
  have hR := hfR.sdiff_singleton (a := (a : ℂ)) (by simp)
  rw [hfa, hpair] at hcl hR
  have hT₀ := bijOn_exp_pi_mul_add_closedStrip a
  refine ⟨f ∘ T, hfc.comp hdiff.continuous.continuousOn fun z hz => (hT₀.mapsTo hz).1,
    hfd.comp hdiff.differentiableOn (bijOn_exp_pi_mul_add_strip a).mapsTo,
    hfH.comp (bijOn_exp_pi_mul_add_strip a), hcl.comp hT₀,
    hR.comp (bijOn_exp_pi_mul_add_strip_boundary a), ?_, ?_⟩
  · have hT : Tendsto T (comap re atBot ⊓ 𝓟 {z | z.im ∈ Icc 0 1})
        (𝓝[{w : ℂ | 0 ≤ w.im}] (a : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(tendsto_exp_pi_mul_add_comap_re_atBot a).mono_left inf_le_left,
        mem_inf_of_right (mem_principal.mpr fun z hz => (hT₀.mapsTo hz).1)⟩
    exact hfa ▸ ((hfc _ (by simp)).tendsto.comp hT)
  · have hT : Tendsto T (comap re atTop ⊓ 𝓟 {z | z.im ∈ Icc 0 1})
        (cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 ≤ w.im}) :=
      tendsto_inf.mpr ⟨(tendsto_exp_pi_mul_add_comap_re_atTop a).mono_left inf_le_left,
        tendsto_principal.mpr (mem_inf_of_right (mem_principal.mpr fun z hz =>
          (hT₀.mapsTo hz).1))⟩
    exact hfy.comp hT

/-! ### Uniqueness up to translation -/

/-- Uniqueness of strip maps normalized at the point `log 2 / π` of the lower boundary line. -/
private theorem eqOn_of_tendsto_log_two_div_pi {Ω : Set ℂ} (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1})
    (hv : DifferentiableOn ℂ v {z | z.im ∈ Ioo 0 1}) (huΩ : BijOn u {z | z.im ∈ Ioo 0 1} Ω)
    (hvΩ : BijOn v {z | z.im ∈ Ioo 0 1} Ω) {x y w : ℂ}
    (hux : Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (hvx : Tendsto v (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (huy : Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (hvy : Tendsto v (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (huw : Tendsto u (𝓝[{z | z.im ∈ Ioo 0 1}] ((Real.log 2 / π : ℝ) : ℂ)) (𝓝 w))
    (hvw : Tendsto v (𝓝[{z | z.im ∈ Ioo 0 1}] ((Real.log 2 / π : ℝ) : ℂ)) (𝓝 w)) :
    EqOn u v {z | z.im ∈ Ioo 0 1} := by
  have hL := bijOn_log_sub_div_sub_div_pi zero_lt_one
  have hLd := differentiableOn_log_sub_div_sub_div_pi zero_lt_one
  have h1 := tendsto_log_sub_div_sub_div_pi_comap_re_atBot zero_lt_one
  have h0 := tendsto_log_sub_div_sub_div_pi_comap_re_atTop zero_lt_one
  have h2 := tendsto_log_sub_div_sub_div_pi_of_notMem_Icc (r := -1) zero_lt_one (by norm_num)
  rw [show ((-1 : ℝ) - 1) / (-1 - 0) = 2 by norm_num] at h2
  have hEq : EqOn (u ∘ _) (v ∘ _) upperHalfPlaneSet :=
    eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn (x₁ := 1) (x₂ := 0) (x₃ := -1) hΩb hΩJ
      (hu.comp hLd hL.mapsTo) (hv.comp hLd hL.mapsTo) (huΩ.comp hL) (hvΩ.comp hL)
      one_ne_zero (by norm_num) (by norm_num)
      (by simpa using hux.comp h1) (by simpa using huy.comp h0) (by simpa using huw.comp h2)
      (by simpa using hvx.comp h1) (by simpa using hvy.comp h0) (by simpa using hvw.comp h2)
  intro z hz
  obtain ⟨w', hw', rfl⟩ := hL.surjOn hz
  exact hEq hw'

/-- Translation by a real number preserves the open strip. -/
private theorem add_ofReal_mem_strip {z : ℂ} (c : ℝ) (hz : z ∈ {z : ℂ | z.im ∈ Ioo 0 1}) :
    z + c ∈ {z : ℂ | z.im ∈ Ioo 0 1} := by
  simpa using hz

/-- Translating a strip map by a real number `c` keeps it a holomorphic bijection onto `Ω` with the
same limits at the two ends. -/
private theorem translate_strip {Ω : Set ℂ} {u : ℂ → ℂ} (c : ℝ)
    (hu : DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1}) (huΩ : BijOn u {z | z.im ∈ Ioo 0 1} Ω)
    {x y : ℂ} (hux : Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (huy : Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y)) :
    DifferentiableOn ℂ (fun z => u (z + c)) {z | z.im ∈ Ioo 0 1} ∧
      BijOn (fun z => u (z + c)) {z | z.im ∈ Ioo 0 1} Ω ∧
      Tendsto (fun z => u (z + c)) (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x) ∧
      Tendsto (fun z => u (z + c)) (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y) := by
  have hT : BijOn (fun z : ℂ => z + c) {z | z.im ∈ Ioo 0 1} {z | z.im ∈ Ioo 0 1} :=
    ⟨fun z hz => add_ofReal_mem_strip c hz, (add_left_injective _).injOn,
      fun z hz => ⟨z - c, by simpa using hz, by simp⟩⟩
  have hend (l : Filter ℝ) (hl : Tendsto (fun r : ℝ => r + c) l l) :
      Tendsto (fun z : ℂ => z + c) (comap re l ⊓ 𝓟 {z | z.im ∈ Ioo 0 1})
        (comap re l ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) :=
    tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (by
        simpa [comp_def] using hl.comp (tendsto_comap.mono_left inf_le_left)),
      tendsto_principal.mpr (mem_inf_of_right (mem_principal.mpr fun z hz => hT.mapsTo hz))⟩
  exact ⟨hu.comp ((differentiable_id.add_const _).differentiableOn) hT.mapsTo, huΩ.comp hT,
    hux.comp (hend atBot (tendsto_atBot_add_const_right _ _ tendsto_id)),
    huy.comp (hend atTop (tendsto_atTop_add_const_right _ _ tendsto_id))⟩

/-- **Uniqueness of strip maps up to translation.** Let `Ω` be a bounded domain whose frontier is a
Jordan curve, and let `u` and `v` be holomorphic bijections of the open strip `0 < z.im < 1` onto
`Ω` which have the same limit `x` as `re z → -∞` and the same limit `y` as `re z → ∞`. If `u` has
the same limit along the strip at the point `s` of the lower boundary line as `v` has at the point
`t`, then `u z = v (z + (t - s))` throughout the strip. -/
theorem eqOn_add_of_tendsto_of_bijOn_strip {Ω : Set ℂ} (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1})
    (hv : DifferentiableOn ℂ v {z | z.im ∈ Ioo 0 1}) (huΩ : BijOn u {z | z.im ∈ Ioo 0 1} Ω)
    (hvΩ : BijOn v {z | z.im ∈ Ioo 0 1} Ω) {x y : ℂ}
    (hux : Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (hvx : Tendsto v (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (huy : Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (hvy : Tendsto v (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y)) {s t : ℝ} {w : ℂ}
    (hus : Tendsto u (𝓝[{z | z.im ∈ Ioo 0 1}] (s : ℂ)) (𝓝 w))
    (hvt : Tendsto v (𝓝[{z | z.im ∈ Ioo 0 1}] (t : ℂ)) (𝓝 w)) :
    EqOn u (fun z => v (z + (t - s))) {z | z.im ∈ Ioo 0 1} := by
  set σ : ℝ := Real.log 2 / π
  -- translate both maps so that the two boundary points move to `σ`
  have hshift {f : ℂ → ℂ} (r : ℝ) (hf : Tendsto f (𝓝[{z | z.im ∈ Ioo 0 1}] (r : ℂ)) (𝓝 w)) :
      Tendsto (fun z => f (z + ((r - σ : ℝ) : ℂ))) (𝓝[{z | z.im ∈ Ioo 0 1}] (σ : ℂ)) (𝓝 w) := by
    refine hf.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
      add_ofReal_mem_strip _ hz⟩)
    have : ContinuousAt (fun z : ℂ => z + ((r - σ : ℝ) : ℂ)) (σ : ℂ) :=
      continuousAt_id.add continuousAt_const
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨hu', huΩ', hux', huy'⟩ := translate_strip (s - σ) hu huΩ hux huy
  obtain ⟨hv', hvΩ', hvx', hvy'⟩ := translate_strip (t - σ) hv hvΩ hvx hvy
  have hEq := eqOn_of_tendsto_log_two_div_pi hΩb hΩJ hu' hv' huΩ' hvΩ' hux' hvx' huy' hvy'
    (hshift s hus) (hshift t hvt)
  intro z hz
  have hz' : z - ((s - σ : ℝ) : ℂ) ∈ {z : ℂ | z.im ∈ Ioo 0 1} := by simpa using hz
  have := hEq hz'
  simp only at this
  convert this using 2 <;> push_cast <;> ring

/-- **Strip maps continuous up to the boundary are unique up to translation.** Let `Ω` be a bounded
domain whose frontier is a Jordan curve, and let `u` and `v` be holomorphic bijections of the open
strip `0 < z.im < 1` onto `Ω`, continuous on the closed strip, which have the same limit `x` as
`re z → -∞` and the same limit `y` as `re z → ∞`. If the images of the lower boundary line under
`u` and `v` meet, then `u` and `v` differ by a real translation on the closed strip. -/
theorem exists_eqOn_add_of_continuousOn_strip {Ω : Set ℂ} (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) {u v : ℂ → ℂ}
    (huc : ContinuousOn u {z | z.im ∈ Icc 0 1}) (hvc : ContinuousOn v {z | z.im ∈ Icc 0 1})
    (hu : DifferentiableOn ℂ u {z | z.im ∈ Ioo 0 1})
    (hv : DifferentiableOn ℂ v {z | z.im ∈ Ioo 0 1}) (huΩ : BijOn u {z | z.im ∈ Ioo 0 1} Ω)
    (hvΩ : BijOn v {z | z.im ∈ Ioo 0 1} Ω) {x y : ℂ}
    (hux : Tendsto u (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (hvx : Tendsto v (comap re atBot ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 x))
    (huy : Tendsto u (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (hvy : Tendsto v (comap re atTop ⊓ 𝓟 {z | z.im ∈ Ioo 0 1}) (𝓝 y))
    (hmeet : (u '' {z | z.im = 0} ∩ v '' {z | z.im = 0}).Nonempty) :
    ∃ c : ℝ, EqOn u (fun z => v (z + c)) {z | z.im ∈ Icc 0 1} := by
  obtain ⟨_, ⟨z₁, hz₁, rfl⟩, z₂, hz₂, hz₁₂⟩ := hmeet
  have hsub : {z : ℂ | z.im ∈ Ioo 0 1} ⊆ {z : ℂ | z.im ∈ Icc 0 1} := fun z hz =>
    Ioo_subset_Icc_self hz
  have hmem {z : ℂ} (hz : z.im = 0) : z ∈ {z : ℂ | z.im ∈ Icc 0 1} := by simp [hz]
  have hlim {f : ℂ → ℂ} (hf : ContinuousOn f {z | z.im ∈ Icc 0 1}) {z : ℂ} (hz : z.im = 0) :
      Tendsto f (𝓝[{z | z.im ∈ Ioo 0 1}] (z.re : ℂ)) (𝓝 (f z)) := by
    have hzr : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz])
    rw [hzr]
    exact ((hf z (hmem hz)).mono hsub).tendsto
  have hEq := eqOn_add_of_tendsto_of_bijOn_strip hΩb hΩJ hu hv huΩ hvΩ hux hvx huy hvy
    (hlim huc hz₁) (hz₁₂ ▸ hlim hvc hz₂)
  refine ⟨z₂.re - z₁.re, eqOn_add_closedStrip_of_eqOn_strip huc hvc ?_⟩
  push_cast
  exact hEq

end TauCeti
