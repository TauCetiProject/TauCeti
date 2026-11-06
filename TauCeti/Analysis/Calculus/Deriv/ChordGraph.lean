/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Short arcs of a regular curve are graphs over their chords

Let `γ : ℝ → E` be a curve in a real normed space and let `a ≤ b` be parameters with
`u = γ b - γ a ≠ 0`. Choose a continuous linear functional `φ` with `φ u = 1` and `‖φ‖ = ‖u‖⁻¹`.
The affine coordinates `v ↦ (φ (v - γ a), (v - γ a) - φ (v - γ a) • u)` identify `E` with
`ℝ × ker φ`, sending the chord from `γ a` to `γ b` onto the segment `[0, 1] × {0}`. If the velocity
of `γ` stays close to the direction of the chord, say `‖(b - a) • γ' t - u‖ ≤ θ ‖u‖` for some
`θ < 1`, then in these coordinates the arc `γ [a, b]` is the graph of a continuous function
`g : ℝ → ker φ` over `[0, 1]`, which vanishes outside `(0, 1)` and satisfies
`‖g ξ‖ ≤ 2θ / (1 - θ) · ‖u‖ · min ξ (1 - ξ)`
(`TauCeti.exists_graph_over_chord_of_norm_smul_deriv_sub_sub_le`). The right-hand side is a
multiple of the distance from the point `γ a + ξ • u` of the chord to its nearer end, so the arc
stays inside a thin double cone around the chord, pinched at the two ends.

For a `C¹` curve with nowhere vanishing derivative, the velocity is uniformly close to the chord
direction on all short enough parameter windows `[a, b]` with `a` in a compact interval
(`ContDiff.exists_norm_smul_deriv_sub_sub_le`). So every short arc of such a curve is a graph over
its chord, with an arbitrarily small constant in place of `2θ / (1 - θ)`
(`ContDiff.exists_graph_over_chord`). This is the local description of a knot of class `C¹` near
the edges of a fine inscribed polygon used to straighten the knot onto the polygon, as in Crowell
and Fox, Appendix I: an ambient isotopy of `ℝ × ker φ` which is supported near the graph of `g` and
moves it onto the zero section carries the arc onto the chord. In particular such a curve is
strictly increasing along a continuous linear functional on every short parameter window, of a
width that is uniform for starting parameters in a compact interval
(`ContDiff.exists_strictMonoOn_dual_comp`). The same holds uniformly along a jointly `C¹` family
`Γ t` of such curves, for the curves `u ↦ Γ (τ u) u` whose time `τ` stays in a compact interval and
moves slowly with the parameter (`ContDiff.exists_strictMonoOn_dual_comp_uncurry`).

The graph description comes from a general principle
(`TauCeti.exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv`): let a curve `t ↦ (x t, w t)`
in `ℝ × W` have `x' > 0` and `‖w'‖ ≤ ε x'` on `[a, b]`, with `w` vanishing at both ends. Then `x`
is a homeomorphism of `[a, b]` onto `[x a, x b]`, so `w = g ∘ x` on `[a, b]` for a continuous `g`
vanishing outside `(x a, x b)`, and `‖g ξ‖ ≤ ε · min (ξ - x a) (x b - ξ)`. The bound is the fencing
form of the mean value inequality, `‖w t - w s‖ ≤ ε (x t - x s)` for `s ≤ t`
(`TauCeti.norm_sub_le_mul_sub_of_norm_deriv_le_mul_deriv`).

## Main results

* `TauCeti.norm_sub_le_mul_sub_of_norm_deriv_le_mul_deriv`: the mean value inequality relative to
  a real function, `‖w t - w s‖ ≤ ε (x t - x s)` when `‖w'‖ ≤ ε x'`.
* `TauCeti.exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv`: a curve with `‖w'‖ ≤ ε x'`
  and `x' > 0` is the graph of a continuous function of `x`.
* `TauCeti.exists_graph_over_chord_of_norm_smul_deriv_sub_sub_le`: an arc whose velocity stays
  close to the direction of its chord is a graph over the chord.
* `ContDiff.exists_norm_smul_deriv_sub_sub_le`: on short parameter windows, the velocity of a
  regular `C¹` curve is uniformly close to the direction of the chord.
* `ContDiff.exists_graph_over_chord`: short arcs of a regular `C¹` curve are graphs over their
  chords, with uniformly small slope.
* `ContDiff.exists_strictMonoOn_dual_comp`: uniform windows on which a regular `C¹` curve is
  strictly increasing along a continuous linear functional.
* `ContDiff.exists_strictMonoOn_dual_comp_uncurry`: the same uniformly along a `C¹` family of
  regular curves, even when the time moves slowly with the curve parameter.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I,
  for the arcs of a knot of class `C¹` over the chords of a fine inscribed polygon.
-/

public section

open Function Set

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

namespace TauCeti

/-- The mean value inequality relative to a real function: if `‖w'‖ ≤ ε x'` on `[a, b]`, then
`‖w t - w s‖ ≤ ε (x t - x s)` for `a ≤ s ≤ t ≤ b`. -/
theorem norm_sub_le_mul_sub_of_norm_deriv_le_mul_deriv {x x' : ℝ → ℝ} {w w' : ℝ → W}
    {a b ε : ℝ} (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (w' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖w' t‖ ≤ ε * x' t) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    ‖w t - w s‖ ≤ ε * (x t - x s) := by
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hs.1
  have hIco : ∀ r ∈ Ico s b, r ∈ Ico a b := fun r hr ↦ ⟨hs.1.trans hr.1, hr.2⟩
  have hnhds : ∀ r ∈ Ico s b, Icc a b ∈ nhdsWithin r (Ici r) := fun r hr ↦
    Icc_mem_nhdsGE_of_mem (hIco r hr)
  have hxc : ContinuousOn x (Icc a b) := fun r hr ↦ (hx r hr).continuousWithinAt
  have hwc : ContinuousOn w (Icc a b) := fun r hr ↦ (hw r hr).continuousWithinAt
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun r ↦ w r - w s)
    (f' := w') (B := fun r ↦ ε * (x r - x s)) (B' := fun r ↦ ε * x' r) ?_ ?_ (by simp) ?_ ?_
    (fun r hr ↦ hbound r (hIco r hr)) ht
  · exact (hwc.mono hsub).sub continuousOn_const
  · exact fun r hr ↦ (((hw r (Ico_subset_Icc_self (hIco r hr))).mono_of_mem_nhdsWithin
      (hnhds r hr)).sub_const (w s))
  · exact continuousOn_const.mul ((hxc.mono hsub).sub continuousOn_const)
  · exact fun r hr ↦ (((hx r (Ico_subset_Icc_self (hIco r hr))).mono_of_mem_nhdsWithin
      (hnhds r hr)).sub_const (x s)).const_mul ε

/-- A curve `t ↦ (x t, w t)` in `ℝ × W` on `[a, b]` with `x' > 0` and `‖w'‖ ≤ ε x'`, and with `w`
vanishing at both ends, is the graph of a continuous function `g` of `x`: `x` is strictly
increasing on `[a, b]` and `w t = g (x t)`, where `g` vanishes outside `(x a, x b)` and
`‖g ξ‖ ≤ ε · min (ξ - x a) (x b - ξ)` on `[x a, x b]`. -/
theorem exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv {x x' : ℝ → ℝ} {w w' : ℝ → W}
    {a b ε : ℝ} (hab : a ≤ b)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (w' t) (Icc a b) t)
    (hpos : ∀ t ∈ Ioo a b, 0 < x' t) (hbound : ∀ t ∈ Ico a b, ‖w' t‖ ≤ ε * x' t)
    (ha : w a = 0) (hb : w b = 0) :
    StrictMonoOn x (Icc a b) ∧ ∃ g : C(ℝ, W), (∀ t ∈ Icc a b, g (x t) = w t) ∧
      (∀ ξ ∉ Ioo (x a) (x b), g ξ = 0) ∧
      ∀ ξ ∈ Icc (x a) (x b), ‖g ξ‖ ≤ ε * min (ξ - x a) (x b - ξ) := by
  have hxc : ContinuousOn x (Icc a b) := fun t ht ↦ (hx t ht).continuousWithinAt
  have hwc : ContinuousOn w (Icc a b) := fun t ht ↦ (hw t ht).continuousWithinAt
  have hmono : StrictMonoOn x (Icc a b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hxc (fun t ht ↦ ?_)
      (fun t ht ↦ hpos t (by rwa [interior_Icc] at ht))
    rw [interior_Icc] at ht ⊢
    exact (hx t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
  have hmaps : MapsTo x (Icc a b) (Icc (x a) (x b)) := hmono.monotoneOn.mapsTo_Icc
  have hxab : x a ≤ x b := (hmaps (left_mem_Icc.2 hab)).2
  -- By the intermediate value theorem, `x` is a strictly increasing bijection of `[a, b]` onto
  -- `[x a, x b]`, hence an order isomorphism and a homeomorphism `e`.
  let S : Icc a b → Icc (x a) (x b) := fun t ↦ ⟨x t, hmaps t.2⟩
  have hS : StrictMono S := fun t u htu ↦ hmono t.2 u.2 htu
  have hsurj : Function.Surjective S := fun ξ ↦ by
    obtain ⟨t, ht, htξ⟩ := intermediate_value_Icc hab hxc ξ.2
    exact ⟨⟨t, ht⟩, Subtype.ext htξ⟩
  let e : Icc a b ≃ₜ Icc (x a) (x b) := (hS.orderIsoOfSurjective S hsurj).toHomeomorph
  have he : ∀ t (ht : t ∈ Icc a b), e ⟨t, ht⟩ = ⟨x t, hmaps ht⟩ := fun t ht ↦ by
    rw [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
  let g : C(ℝ, W) :=
    ⟨fun ξ ↦ w (e.symm (projIcc (x a) (x b) hxab ξ)),
      hwc.comp_continuous (continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc))
        fun ξ ↦ (e.symm _).2⟩
  have hg : ∀ t ∈ Icc a b, g (x t) = w t := fun t ht ↦ by
    simp only [g, ContinuousMap.coe_mk, projIcc_of_mem hxab (hmaps ht), ← he t ht,
      e.symm_apply_apply]
  refine ⟨hmono, g, hg, fun ξ hξ ↦ ?_, fun ξ hξ ↦ ?_⟩
  · simp only [mem_Ioo, not_and_or, not_lt] at hξ
    rcases hξ with hξ | hξ
    · simp only [g, ContinuousMap.coe_mk, projIcc_of_le_left hxab hξ,
        ← he a (left_mem_Icc.2 hab), e.symm_apply_apply, ha]
    · simp only [g, ContinuousMap.coe_mk, projIcc_of_right_le hxab hξ,
        ← he b (right_mem_Icc.2 hab), e.symm_apply_apply, hb]
  · obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hab hxc hξ
    have h₁ : ‖w t‖ ≤ ε * (x t - x a) := by
      simpa [ha] using norm_sub_le_mul_sub_of_norm_deriv_le_mul_deriv hx hw hbound
        (left_mem_Icc.2 hab) ht
    have h₂ : ‖w t‖ ≤ ε * (x b - x t) := by
      simpa [hb, norm_sub_rev] using norm_sub_le_mul_sub_of_norm_deriv_le_mul_deriv hx hw hbound
        ht ⟨ht.2, le_rfl⟩
    rw [hg t ht]
    rcases min_cases (x t - x a) (x b - x t) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption

/-- If `φ u = 1` and `‖φ‖ = ‖u‖⁻¹`, then `‖u‖ ≠ 0` and `|φ y| ≤ ‖u‖⁻¹ ‖y‖` for every `y`. -/
private lemma norm_ne_zero_and_abs_apply_le {φ : StrongDual ℝ E} {u : E} (hφu : φ u = 1)
    (hφ : ‖φ‖ = ‖u‖⁻¹) : ‖u‖ ≠ 0 ∧ ∀ y, |φ y| ≤ ‖u‖⁻¹ * ‖y‖ :=
  ⟨norm_ne_zero_iff.2 fun hu ↦ by simp [hu] at hφu,
    fun y ↦ by simpa [Real.norm_eq_abs, hφ] using φ.le_opNorm y⟩

/-- If `φ u = 1`, `‖φ‖ = ‖u‖⁻¹` and `‖h • v - u‖ ≤ θ ‖u‖`, then `1 - θ ≤ h φ v`. -/
private lemma one_sub_le_mul_of_norm_smul_sub_le {φ : StrongDual ℝ E} {u v : E} {h θ : ℝ}
    (hφu : φ u = 1) (hφ : ‖φ‖ = ‖u‖⁻¹) (hv : ‖h • v - u‖ ≤ θ * ‖u‖) : 1 - θ ≤ h * φ v := by
  obtain ⟨hu0, hφy⟩ := norm_ne_zero_and_abs_apply_le hφu hφ
  have h₁ := hφy (h • v - u)
  have h₂ : ‖u‖⁻¹ * ‖h • v - u‖ ≤ θ := by
    rw [inv_mul_le_iff₀ ((norm_nonneg u).lt_of_ne' hu0), mul_comm]
    exact hv
  rw [map_sub, map_smul, hφu, smul_eq_mul] at h₁
  linarith [neg_abs_le (h * φ v - 1)]

/-- If `φ u = 1`, `‖φ‖ = ‖u‖⁻¹` and `‖h • v - u‖ ≤ θ ‖u‖` with `h > 0` and `θ < 1`, then the
component `v - φ v • u` of `v` in the kernel of `φ` is at most `2θ / (1 - θ) · ‖u‖ · φ v`. -/
private lemma norm_sub_smul_le_of_norm_smul_sub_le {φ : StrongDual ℝ E} {u v : E} {h θ : ℝ}
    (hφu : φ u = 1) (hφ : ‖φ‖ = ‖u‖⁻¹) (hh : 0 < h) (hθ : θ < 1)
    (hv : ‖h • v - u‖ ≤ θ * ‖u‖) : ‖v - φ v • u‖ ≤ 2 * θ / (1 - θ) * ‖u‖ * φ v := by
  have hlow := one_sub_le_mul_of_norm_smul_sub_le hφu hφ hv
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ
  have hpos : 0 < φ v := pos_of_mul_pos_right (h1θ.trans_le hlow) hh.le
  obtain ⟨hu0, hφy⟩ := norm_ne_zero_and_abs_apply_le hφu hφ
  -- `h • (v - φ v • u) = r - φ r • u` with `r = h • v - u`, since `φ u = 1`.
  have hr : h * ‖v - φ v • u‖ ≤ 2 * θ * ‖u‖ := by
    have hφr := hφy (h • v - u)
    have hsplit : h • (v - φ v • u) = h • v - u - φ (h • v - u) • u := by
      simp only [map_sub, map_smul, hφu, smul_eq_mul, smul_sub, sub_smul, mul_smul, one_smul]
      abel
    rw [← Real.norm_of_nonneg hh.le, ← norm_smul, hsplit]
    calc ‖h • v - u - φ (h • v - u) • u‖ ≤ ‖h • v - u‖ + |φ (h • v - u)| * ‖u‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ θ * ‖u‖ + ‖u‖⁻¹ * (θ * ‖u‖) * ‖u‖ := by
          gcongr
          exact hφr.trans (by gcongr)
      _ = 2 * θ * ‖u‖ := by
          field_simp; ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h1θ]
  calc ‖v - φ v • u‖ * (1 - θ) ≤ ‖v - φ v • u‖ * (h * φ v) :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = h * ‖v - φ v • u‖ * φ v := by ring
    _ ≤ 2 * θ * ‖u‖ * φ v := mul_le_mul_of_nonneg_right hr hpos.le

/-- An arc of a curve whose velocity stays close to the direction of its chord is a graph over
the chord. Let `u = γ b - γ a ≠ 0` and suppose `‖(b - a) • γ' t - u‖ ≤ θ ‖u‖` on `[a, b)` with
`θ < 1`. Then there are a continuous linear functional `φ` with `φ u = 1` and `‖φ‖ = ‖u‖⁻¹`, along
which `γ` is strictly increasing on `[a, b]`, and a continuous `g : ℝ → ker φ` vanishing outside
`(0, 1)`, with `‖g ξ‖ ≤ 2θ / (1 - θ) · ‖u‖ · min ξ (1 - ξ)` on `[0, 1]`, such that
`γ t = γ a + ξ • u + g ξ` for every `t ∈ [a, b]`, where `ξ = φ (γ t - γ a)`. -/
theorem exists_graph_over_chord_of_norm_smul_deriv_sub_sub_le {γ γ' : ℝ → E} {a b θ : ℝ}
    (hab : a ≤ b) (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (γ' t) (Icc a b) t)
    (hu : γ b ≠ γ a) (hθ : θ < 1)
    (hclose : ∀ t ∈ Ico a b, ‖(b - a) • γ' t - (γ b - γ a)‖ ≤ θ * ‖γ b - γ a‖) :
    ∃ φ : StrongDual ℝ E, φ (γ b - γ a) = 1 ∧ ‖φ‖ = ‖γ b - γ a‖⁻¹ ∧
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc a b) ∧
      ∃ g : C(ℝ, LinearMap.ker (φ : E →ₗ[ℝ] ℝ)), (∀ ξ ∉ Ioo 0 1, g ξ = 0) ∧
        (∀ ξ ∈ Icc 0 1, ‖g ξ‖ ≤ 2 * θ / (1 - θ) * ‖γ b - γ a‖ * min ξ (1 - ξ)) ∧
        ∀ t ∈ Icc a b, γ t = γ a + φ (γ t - γ a) • (γ b - γ a) + (g (φ (γ t - γ a)) : E) := by
  have hab' : a < b := hab.lt_of_ne fun h ↦ hu (h ▸ rfl)
  set u := γ b - γ a with hu_def
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
  -- The functional `φ`, normalized by `φ u = 1`, and the projection `P` onto its kernel along `u`.
  obtain ⟨φ₀, hφ₀, hφ₀u⟩ := exists_dual_vector ℝ u hu0.ne'
  set φ : StrongDual ℝ E := ‖u‖⁻¹ • φ₀
  have hφu : φ u = 1 := by
    simp [φ, hφ₀u, inv_mul_cancel₀ hu0.ne']
  have hφnorm : ‖φ‖ = ‖u‖⁻¹ := by
    simp [φ, norm_smul, hφ₀]
  have hright : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℝ u) φ := fun r ↦ by
    simp [hφu]
  set P := φ.projKerOfRightInverse _ hright
  have hP : ∀ z, (P z : E) = z - φ z • u := fun z ↦ by simp [P]
  have hPu : P u = 0 := by
    ext1
    simp [hP, hφu]
  -- In the coordinates `x = φ (· - γ a)` and `w = P (· - γ a)`, the arc has slope at most
  -- `2θ / (1 - θ) · ‖u‖`.
  have hx : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ φ (γ t - γ a)) (φ (γ' t)) (Icc a b) t :=
    fun t ht ↦ φ.hasFDerivAt.comp_hasDerivWithinAt t ((hγ t ht).sub_const (γ a))
  have hw : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ P (γ t - γ a)) (P (γ' t)) (Icc a b) t :=
    fun t ht ↦ P.hasFDerivAt.comp_hasDerivWithinAt t ((hγ t ht).sub_const (γ a))
  have hba : 0 < b - a := sub_pos.2 hab'
  have hpos : ∀ t ∈ Ico a b, 0 < φ (γ' t) := fun t ht ↦
    pos_of_mul_pos_right ((sub_pos.2 hθ).trans_le
      (one_sub_le_mul_of_norm_smul_sub_le hφu hφnorm (hclose t ht))) hba.le
  have hbound : ∀ t ∈ Ico a b, ‖P (γ' t)‖ ≤ 2 * θ / (1 - θ) * ‖u‖ * φ (γ' t) := fun t ht ↦ by
    rw [← Submodule.norm_coe, hP]
    exact norm_sub_smul_le_of_norm_smul_sub_le hφu hφnorm hba hθ (hclose t ht)
  obtain ⟨hmono, g, hg, hg0, hgb⟩ := exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv hab
    hx hw (fun t ht ↦ hpos t (Ioo_subset_Ico_self ht)) hbound (by simp [P])
    (by rw [← hu_def, hPu])
  simp only [sub_self, map_zero, ← hu_def, hφu, sub_zero] at hg0 hgb
  refine ⟨φ, hφu, hφnorm, fun s hs t ht hst ↦ ?_, g, hg0, hgb, fun t ht ↦ ?_⟩
  · simpa only [map_sub, sub_lt_sub_iff_right] using hmono hs ht hst
  · rw [hg t ht, hP]
    abel

/-- The chord of a curve whose velocity stays within `η` of `v` on `[a, b]` is within
`η (b - a)` of `(b - a) • v`: apply the mean value inequality to `s ↦ γ s - s • v`. -/
private lemma norm_sub_sub_smul_le_of_norm_deriv_sub_le {γ : ℝ → E} {v : E} {a b η : ℝ}
    (hab : a ≤ b) (hγ : Differentiable ℝ γ) (hclose : ∀ s ∈ Icc a b, ‖deriv γ s - v‖ ≤ η) :
    ‖γ b - γ a - (b - a) • v‖ ≤ η * (b - a) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := γ - fun s ↦ s • v)
    (f' := fun s ↦ deriv γ s - v) (fun s _ ↦ by
      simpa only [one_smul] using
        ((hγ s).hasDerivAt.sub ((hasDerivAt_id' s).smul_const v)).hasDerivWithinAt)
    (fun s hs ↦ hclose s (Ico_subset_Icc_self hs)) b (right_mem_Icc.2 hab)
  convert this using 2
  simp only [Pi.sub_apply, sub_smul]
  abel

end TauCeti

namespace ContDiff

variable {γ : ℝ → E}

/-- On short parameter windows, the velocity of a `C¹` curve with nowhere vanishing derivative is
uniformly close to the direction of the chord: for every `θ > 0` there is `δ > 0` with
`‖(b - a) • γ' t - (γ b - γ a)‖ ≤ θ ‖γ b - γ a‖` whenever `a` lies in a given compact interval,
`a < b ≤ a + δ` and `t ∈ [a, b]`. -/
theorem exists_norm_smul_deriv_sub_sub_le (hγ : ContDiff ℝ 1 γ) (hderiv : ∀ t, deriv γ t ≠ 0)
    (c d : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ > 0, ∀ a ∈ Icc c d, ∀ b ∈ Ioc a (a + δ), ∀ t ∈ Icc a b,
      ‖(b - a) • deriv γ t - (γ b - γ a)‖ ≤ θ * ‖γ b - γ a‖ := by
  rcases lt_or_ge d c with hdc | hcd
  · exact ⟨1, one_pos, fun a ha ↦ absurd (ha.1.trans ha.2) (not_le.2 hdc)⟩
  have hcont : Continuous (deriv γ) := hγ.continuous_deriv_one
  have hdiff : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  -- A lower bound `m > 0` for `‖γ'‖` and a modulus of uniform continuity of `γ'` on `[c, d + 1]`,
  -- for the tolerance `η = κ m`.
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith : c ≤ d + 1))
    hcont.norm.continuousOn
  set m := ‖deriv γ t₀‖
  have hm : 0 < m := norm_pos_iff.2 (hderiv t₀)
  set κ := min (θ / 4) (1 / 2)
  have hκ : 0 < κ := by positivity
  have hκθ : κ ≤ θ / 4 := min_le_left _ _
  have hκ2 : κ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨δ₀, hδ₀, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := c) (b := d + 1)).uniformContinuousOn_of_continuous hcont.continuousOn)
    (κ * m) (by positivity)
  refine ⟨min (δ₀ / 2) 1, by positivity, fun a ha b hb t ht ↦ ?_⟩
  have hδ₁ : min (δ₀ / 2) 1 ≤ δ₀ / 2 := min_le_left _ _
  have hδ₂ : min (δ₀ / 2) 1 ≤ 1 := min_le_right _ _
  set h := b - a
  have hh : 0 < h := sub_pos.2 hb.1
  set v := deriv γ a
  have hclose : ∀ s ∈ Icc a b, ‖deriv γ s - v‖ ≤ κ * m := fun s hs ↦ by
    have := hunif s ⟨ha.1.trans hs.1, by linarith [hs.2, hb.2, ha.2]⟩ a ⟨ha.1, by linarith [ha.2]⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2, hb.2])
    rw [dist_eq_norm] at this
    exact this.le
  -- The chord `u = γ b - γ a` is within `κ m h` of `h • γ' a`, so `‖u‖ ≥ (1 - κ) h m`, while the
  -- left-hand side is at most `2 κ m h`. The choice `κ ≤ θ / 4`, `κ ≤ 1 / 2` gives
  -- `2 κ ≤ θ / 2 ≤ θ (1 - κ)`.
  have hmvt : ‖γ b - γ a - h • v‖ ≤ κ * m * h :=
    TauCeti.norm_sub_sub_smul_le_of_norm_deriv_sub_le hb.1.le hdiff hclose
  have hv : h * m ≤ h * ‖v‖ := mul_le_mul_of_nonneg_left (ht₀ ⟨ha.1, by linarith [ha.2]⟩) hh.le
  have hu : (1 - κ) * (h * m) ≤ ‖γ b - γ a‖ := by
    have h1 : ‖h • v‖ ≤ ‖γ b - γ a‖ + ‖γ b - γ a - h • v‖ := by
      simpa only [norm_sub_rev (h • v)] using norm_le_norm_add_norm_sub' (h • v) (γ b - γ a)
    rw [norm_smul, Real.norm_of_nonneg hh.le] at h1
    linarith
  have hsplit : (b - a) • deriv γ t - (γ b - γ a) = h • (deriv γ t - v) - (γ b - γ a - h • v) := by
    simp only [h, smul_sub]
    abel
  have hκ' : 2 * κ ≤ θ * (1 - κ) := by nlinarith
  rw [hsplit]
  calc ‖h • (deriv γ t - v) - (γ b - γ a - h • v)‖
      ≤ h * (κ * m) + κ * m * h := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hmvt)
        rw [norm_smul, Real.norm_of_nonneg hh.le]
        exact mul_le_mul_of_nonneg_left (hclose t ht) hh.le
    _ = 2 * κ * (h * m) := by ring
    _ ≤ θ * (1 - κ) * (h * m) := mul_le_mul_of_nonneg_right hκ' (mul_pos hh hm).le
    _ ≤ θ * ‖γ b - γ a‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hu hθ.le

/-- Short arcs of a `C¹` curve with nowhere vanishing derivative are graphs over their chords,
with uniformly small slope. For every `ε > 0` there is `δ > 0` such that, whenever `a` lies in a
given compact interval and `a < b ≤ a + δ`, writing `u = γ b - γ a`: there are a continuous linear
functional `φ` with `φ u = 1` and `‖φ‖ = ‖u‖⁻¹`, along which `γ` is strictly increasing on
`[a, b]`, and a continuous `g : ℝ → ker φ` vanishing outside `(0, 1)`, with
`‖g ξ‖ ≤ ε ‖u‖ min ξ (1 - ξ)` on `[0, 1]`, such that `γ t = γ a + ξ • u + g ξ` for every
`t ∈ [a, b]`, where `ξ = φ (γ t - γ a)`. -/
theorem exists_graph_over_chord (hγ : ContDiff ℝ 1 γ) (hderiv : ∀ t, deriv γ t ≠ 0) (c d : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Icc c d, ∀ b ∈ Ioc a (a + δ), ∃ φ : StrongDual ℝ E,
      φ (γ b - γ a) = 1 ∧ ‖φ‖ = ‖γ b - γ a‖⁻¹ ∧ StrictMonoOn (fun t ↦ φ (γ t)) (Icc a b) ∧
      ∃ g : C(ℝ, LinearMap.ker (φ : E →ₗ[ℝ] ℝ)), (∀ ξ ∉ Ioo 0 1, g ξ = 0) ∧
        (∀ ξ ∈ Icc 0 1, ‖g ξ‖ ≤ ε * ‖γ b - γ a‖ * min ξ (1 - ξ)) ∧
        ∀ t ∈ Icc a b, γ t = γ a + φ (γ t - γ a) • (γ b - γ a) + (g (φ (γ t - γ a)) : E) := by
  set θ := min (1 / 2) (ε / 4) with hθ_def
  have hθ : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := min_le_left _ _
  have hθε : θ ≤ ε / 4 := min_le_right _ _
  obtain ⟨δ, hδ, hchord⟩ := hγ.exists_norm_smul_deriv_sub_sub_le hderiv c d hθ
  refine ⟨δ, hδ, fun a ha b hb ↦ ?_⟩
  have hdiff : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have hab : a < b := hb.1
  -- The chord is nonzero, since otherwise the velocity would vanish on `[a, b]`.
  have hu : γ b ≠ γ a := by
    intro hba
    have := hchord a ha b hb a (left_mem_Icc.2 hab.le)
    simp [hba, sub_eq_zero, hab.ne', hderiv a] at this
  obtain ⟨φ, hφu, hφnorm, hmono, g, hg0, hgb, hγg⟩ :=
    TauCeti.exists_graph_over_chord_of_norm_smul_deriv_sub_sub_le hab.le
      (fun t _ ↦ (hdiff t).hasDerivAt.hasDerivWithinAt) hu (by linarith)
      fun t ht ↦ hchord a ha b hb t (Ico_subset_Icc_self ht)
  refine ⟨φ, hφu, hφnorm, hmono, g, hg0, fun ξ hξ ↦ (hgb ξ hξ).trans ?_, hγg⟩
  have hmin : 0 ≤ min ξ (1 - ξ) := le_min hξ.1 (sub_nonneg.2 hξ.2)
  have hslope : 2 * θ / (1 - θ) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hslope (norm_nonneg _)) hmin

/-- The constants for `ContDiff.exists_strictMonoOn_dual_comp_uncurry`, from compactness of
`[t₀, t₁] × [a, b + 1]`: a time-Lipschitz bound `B` for `Γ`, a lower bound `m` for the speed of the
curves `Γ t`, with derivative `v t`, a window width `δ ≤ 1` on which `v` varies by less than
`m / 4`, and a speed `lam ≤ 1` with `B * lam ≤ m / 2`. -/
private theorem exists_uniform_velocity_constants {Γ : ℝ → ℝ → E}
    (hΓ : ContDiff ℝ 1 (uncurry Γ)) {t₀ t₁ : ℝ} (hderiv : ∀ t ∈ Icc t₀ t₁, ∀ s, deriv (Γ t) s ≠ 0)
    {a b : ℝ} (ht : t₀ ≤ t₁) (hab : a ≤ b) :
    ∃ (B m δ lam : ℝ) (v : ℝ → ℝ → E), 0 ≤ B ∧ 0 < m ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < lam ∧ lam ≤ 1 ∧
      B * lam ≤ m / 2 ∧ (∀ t s, HasDerivAt (Γ t) (v t s) s) ∧
      (∀ t t' s, t ∈ Icc t₀ t₁ → t' ∈ Icc t₀ t₁ → s ∈ Icc a (b + 1) →
        ‖Γ t s - Γ t' s‖ ≤ B * |t - t'|) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ s ∈ Icc a (b + 1), m ≤ ‖v t s‖) ∧
      ∀ t t' s s', t ∈ Icc t₀ t₁ → t' ∈ Icc t₀ t₁ → s ∈ Icc a (b + 1) → s' ∈ Icc a (b + 1) →
        |t - t'| ≤ δ → |s - s'| ≤ δ → ‖v t s - v t' s'‖ < m / 4 := by
  set Q : Set (ℝ × ℝ) := Icc t₀ t₁ ×ˢ Icc a (b + 1)
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQv : Convex ℝ Q := (convex_Icc _ _).prod (convex_Icc _ _)
  have hQ0 : (t₀, a) ∈ Q := ⟨⟨le_rfl, ht⟩, ⟨le_rfl, by linarith⟩⟩
  have hdiff : Differentiable ℝ (uncurry Γ) := hΓ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ (uncurry Γ)) := hΓ.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn hfc.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hQ0)
  have hlipΓ {t₁ t₂ s : ℝ} (h₁ : (t₁, s) ∈ Q) (h₂ : (t₂, s) ∈ Q) :
      ‖Γ t₁ s - Γ t₂ s‖ ≤ B * |t₁ - t₂| := by
    have := hQv.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ hdiff x) hB h₂ h₁
    simpa [Prod.norm_def, Real.norm_eq_abs] using this
  -- The derivative `v (t, s)` of the curve `Γ t` at `s`.
  set v : ℝ × ℝ → E := fun p ↦ fderiv ℝ (uncurry Γ) p ((0 : ℝ), (1 : ℝ))
  have hvc : Continuous v := hfc.clm_apply continuous_const
  have hvd (t s : ℝ) : HasDerivAt (Γ t) (v (t, s)) s := by
    have h := (hdiff (t, s)).hasFDerivAt.comp_hasDerivAt s
      (HasDerivAt.prodMk (hasDerivAt_const s t) (hasDerivAt_id s))
    have e : (uncurry Γ ∘ Prod.mk t) = Γ t := by funext s; simp
    rwa [e] at h
  obtain ⟨p₀, hp₀, hmin⟩ := hQc.exists_isMinOn ⟨_, hQ0⟩ hvc.norm.continuousOn
  set m := ‖v p₀‖
  have hm : 0 < m := norm_pos_iff.2 fun h0 ↦
    hderiv _ hp₀.1 p₀.2 (by rw [(hvd p₀.1 p₀.2).deriv, Prod.mk.eta, h0])
  obtain ⟨δ₁, hδ₁, huc⟩ := Metric.uniformContinuousOn_iff.1
    (hQc.uniformContinuousOn_of_continuous hvc.continuousOn) (m / 4) (by positivity)
  set δ := min (δ₁ / 2) 1
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ₁' : δ ≤ δ₁ / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set lam := min 1 (m / (2 * (B + 1)))
  have hlam : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hBlam : B * lam ≤ m / 2 := by
    have h₁ : lam * (2 * (B + 1)) ≤ m := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  refine ⟨B, m, δ, lam, fun t s ↦ v (t, s), hB0, hm, hδ, hδ1, hlam, hlam1, hBlam,
    fun t s ↦ hvd t s, fun t t' s h h' hs ↦ hlipΓ ⟨h, hs⟩ ⟨h', hs⟩,
    fun t h s hs ↦ isMinOn_iff.1 hmin (t, s) ⟨h, hs⟩, fun t t' s s' h h' hs hs' h₁ h₂ ↦ ?_⟩
  have hd : dist (t, s) (t', s') < δ₁ := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact max_lt (by linarith) (by linarith)
  simpa [dist_eq_norm] using huc (t, s) ⟨h, hs⟩ (t', s') ⟨h', hs'⟩ hd

/-- The curve `u ↦ Γ (τ u) u` is strictly increasing along a functional `φ` of norm at most one
between `x < y`, if `Γ (τ y)` has speed at least `3 m / 4` along `φ` on `[x, y]` and the time `τ`
moves slowly (`B * lam ≤ m / 2`). -/
private theorem lt_dual_comp_of_lower_bound {Γ v : ℝ → ℝ → E} {φ : StrongDual ℝ E} {τ : ℝ → ℝ}
    {B m lam x y : ℝ} (hvd : ∀ t s, HasDerivAt (Γ t) (v t s) s) (hφle : ∀ w, |φ w| ≤ ‖w‖)
    (hm : 0 < m) (hB0 : 0 ≤ B) (hBlam : B * lam ≤ m / 2) (hxy : x < y)
    (hlipΓ : ‖Γ (τ y) x - Γ (τ x) x‖ ≤ B * |τ y - τ x|) (hlip : |τ y - τ x| ≤ lam * (y - x))
    (hnear : ∀ u ∈ Icc x y, 3 * m / 4 ≤ φ (v (τ y) u)) :
    φ (Γ (τ x) x) < φ (Γ (τ y) y) := by
  -- Moving the curve parameter from `x` to `y` at the fixed time `τ y` gains at least `3m/4` per
  -- unit, while changing the time from `τ x` to `τ y` costs at most `B lam ≤ m/2` per unit.
  have hg : 3 * m / 4 * (y - x) ≤ φ (Γ (τ y) y) - φ (Γ (τ y) x) := by
    have hderg (u : ℝ) : HasDerivAt (fun u ↦ φ (Γ (τ y) u)) (φ (v (τ y) u)) u :=
      φ.hasFDerivAt.comp_hasDerivAt u (hvd (τ y) u)
    refine (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun u _ ↦ (hderg u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hderg u).differentiableAt.differentiableWithinAt) (fun u hu ↦ ?_)
      x (left_mem_Icc.2 hxy.le) y (right_mem_Icc.2 hxy.le) hxy.le
    rw [(hderg u).deriv]
    exact hnear u (interior_subset hu)
  have htime : |φ (Γ (τ y) x) - φ (Γ (τ x) x)| ≤ m / 2 * (y - x) := by
    rw [← map_sub]
    refine (hφle _).trans (hlipΓ.trans ?_)
    calc B * |τ y - τ x| ≤ B * (lam * (y - x)) := by gcongr
      _ = B * lam * (y - x) := by ring
      _ ≤ m / 2 * (y - x) := by gcongr
  nlinarith [abs_le.1 htime, sub_pos.2 hxy]

/-- A `C¹` curve with nowhere vanishing derivative is strictly increasing after a suitable
continuous linear functional on every window `[s, s + δ]` of a uniform width `δ > 0`, for starting
parameters `s` in a compact interval `[a, b]`: take the functional normalized on the chord from
`γ s` to `γ (s + δ)` given by `ContDiff.exists_graph_over_chord`. -/
theorem exists_strictMonoOn_dual_comp (hγ : ContDiff ℝ 1 γ) (hderiv : ∀ t, deriv γ t ≠ 0)
    (a b : ℝ) :
    ∃ δ > 0, ∀ s ∈ Icc a b, ∃ φ : StrongDual ℝ E,
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc s (s + δ)) := by
  obtain ⟨δ, hδ, h⟩ := hγ.exists_graph_over_chord hderiv a b one_pos
  exact ⟨δ, hδ, fun s hs ↦
    (h s hs (s + δ) ⟨lt_add_of_pos_right s hδ, le_rfl⟩).imp fun _ hφ ↦ hφ.2.2.1⟩

/-- **Lipschitz bound for a jointly `C¹` family on a box.** If `Γ t s` is `C¹` in `(t, s)`, there is
a constant `B` such that `‖Γ t₁ s₁ - Γ t₂ s₂‖ ≤ B * max |t₁ - t₂| |s₁ - s₂|` for all `t₁, t₂` in
`[t₀, t₁']` and all `s₁, s₂` in `[a, b]`. -/
theorem exists_norm_sub_le_mul_max_uncurry {Γ : ℝ → ℝ → E} (hΓ : ContDiff ℝ 1 (uncurry Γ))
    (t₀ t₀' a b : ℝ) :
    ∃ B : NNReal, ∀ ⦃x₁ y₁ x₂ y₂ : ℝ⦄, x₁ ∈ Icc t₀ t₀' → y₁ ∈ Icc a b → x₂ ∈ Icc t₀ t₀' →
      y₂ ∈ Icc a b → ‖Γ x₁ y₁ - Γ x₂ y₂‖ ≤ B * max |x₁ - x₂| |y₁ - y₂| := by
  have hQc : IsCompact (Icc t₀ t₀' ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hQv : Convex ℝ (Icc t₀ t₀' ×ˢ Icc a b) := (convex_Icc _ _).prod (convex_Icc _ _)
  have hdiff : Differentiable ℝ (uncurry Γ) := hΓ.differentiable one_ne_zero
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn
    (hΓ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨B.toNNReal, fun x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ ↦ ?_⟩
  have h₁ : (x₁, y₁) ∈ Icc t₀ t₀' ×ˢ Icc a b := ⟨hx₁, hy₁⟩
  have h₂ : (x₂, y₂) ∈ Icc t₀ t₀' ×ˢ Icc a b := ⟨hx₂, hy₂⟩
  have := hQv.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ hdiff x)
    (fun p hp ↦ (hB p hp).trans (Real.le_coe_toNNReal B)) h₂ h₁
  simpa [Prod.norm_def, Real.norm_eq_abs] using this

/-- **Uniform windows along a `C¹` family of curves.** Let `Γ t` be a family of curves, jointly
`C¹` in the time `t` and the curve parameter, such that each `Γ t` with `t ∈ [t₀, t₁]` has nowhere
vanishing derivative. Then there are a window width `δ > 0` and a speed `lam > 0` such that, for
every time function `τ` with values in `[t₀, t₁]` which is `lam`-Lipschitz, the curve
`u ↦ Γ (τ u) u` is strictly increasing after a suitable continuous linear functional on every
window `[s, s + δ]` with `s ∈ [a, b]`. -/
theorem exists_strictMonoOn_dual_comp_uncurry {Γ : ℝ → ℝ → E}
    (hΓ : ContDiff ℝ 1 (uncurry Γ)) {t₀ t₁ : ℝ} (hderiv : ∀ t ∈ Icc t₀ t₁, ∀ s, deriv (Γ t) s ≠ 0)
    (a b : ℝ) :
    ∃ δ > 0, ∃ lam > 0, ∀ τ : ℝ → ℝ, (∀ u, τ u ∈ Icc t₀ t₁) →
      (∀ x y, |τ x - τ y| ≤ lam * |x - y|) → ∀ s ∈ Icc a b, ∃ φ : StrongDual ℝ E,
        StrictMonoOn (fun u ↦ φ (Γ (τ u) u)) (Icc s (s + δ)) := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨1, one_pos, 1, one_pos, fun _ _ _ s hs ↦ absurd (hs.1.trans hs.2) (not_le.2 hba)⟩
  rcases lt_or_ge t₁ t₀ with ht | ht
  · exact ⟨1, one_pos, 1, one_pos, fun τ hτ _ ↦ absurd ((hτ 0).1.trans (hτ 0).2) (not_le.2 ht)⟩
  obtain ⟨B, m, δ, lam, v, hB0, hm, hδ, hδ1, hlam, hlam1, hBlam, hvd, hlipΓ, hvm, huc⟩ :=
    exists_uniform_velocity_constants hΓ hderiv ht hab
  refine ⟨δ, hδ, lam, hlam, fun τ hτI hlip s hs ↦ ?_⟩
  have memQ {u : ℝ} (hu : u ∈ Icc s (s + δ)) : u ∈ Icc a (b + 1) :=
    ⟨by linarith [hu.1, hs.1], by linarith [hu.2, hs.2]⟩
  have hs' : s ∈ Icc s (s + δ) := ⟨le_rfl, by linarith⟩
  -- Along `φ`, the dual vector of `v (τ s) s`, the curve increases on `[s, s + δ]`.
  obtain ⟨φ, hφ, hφv⟩ := exists_dual_vector'' ℝ (v (τ s) s)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hφv
  have hφle (w : E) : |φ w| ≤ ‖w‖ := by
    simpa [Real.norm_eq_abs] using
      (φ.le_opNorm w).trans (mul_le_of_le_one_left (norm_nonneg _) hφ)
  have hnear {y u : ℝ} (hy : y ∈ Icc s (s + δ)) (hu : u ∈ Icc s (s + δ)) :
      3 * m / 4 ≤ φ (v (τ y) u) := by
    have h₁ : |τ y - τ s| ≤ |y - s| :=
      (hlip y s).trans (mul_le_of_le_one_left (abs_nonneg _) hlam1)
    have h₂ := huc (τ y) (τ s) u s (hτI y) (hτI s) (memQ hu) (memQ hs')
      (h₁.trans (abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩))
      (abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    have h₃ : m ≤ ‖v (τ s) s‖ := hvm (τ s) (hτI s) s (memQ hs')
    have h₄ := hφle (v (τ y) u - v (τ s) s)
    rw [map_sub, hφv] at h₄
    linarith [neg_abs_le (φ (v (τ y) u) - ‖v (τ s) s‖), norm_nonneg (v (τ y) u - v (τ s) s)]
  refine ⟨φ, fun x hx y hy hxy ↦ lt_dual_comp_of_lower_bound hvd hφle hm hB0 hBlam hxy
    (hlipΓ _ _ _ (hτI y) (hτI x) (memQ hx)) (by simpa [abs_of_pos (sub_pos.2 hxy)] using hlip y x)
    fun u hu ↦ hnear hy ⟨hx.1.trans hu.1, hu.2.trans hy.2⟩⟩

end ContDiff
