/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
moves it onto the zero section carries the arc onto the chord.

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

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I,
  for the arcs of a knot of class `C¹` over the chords of a fine inscribed polygon.
-/

public section

open Set

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
vanishing at both ends, is the graph of a continuous function `g` of `x`: `w t = g (x t)`, where
`g` vanishes outside `(x a, x b)` and `‖g ξ‖ ≤ ε · min (ξ - x a) (x b - ξ)` on `[x a, x b]`. -/
theorem exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv {x x' : ℝ → ℝ} {w w' : ℝ → W}
    {a b ε : ℝ} (hab : a ≤ b)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (w' t) (Icc a b) t)
    (hpos : ∀ t ∈ Ioo a b, 0 < x' t) (hbound : ∀ t ∈ Ico a b, ‖w' t‖ ≤ ε * x' t)
    (ha : w a = 0) (hb : w b = 0) :
    ∃ g : C(ℝ, W), (∀ t ∈ Icc a b, g (x t) = w t) ∧ (∀ ξ ∉ Ioo (x a) (x b), g ξ = 0) ∧
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
  refine ⟨g, hg, fun ξ hξ ↦ ?_, fun ξ hξ ↦ ?_⟩
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
  have hθ0 : 0 ≤ θ := by
    have := (norm_nonneg _).trans (hclose a (left_mem_Ico.2 hab'))
    exact nonneg_of_mul_nonneg_left this hu0
  -- The functional `φ`, normalized by `φ u = 1`, and the projection `P` onto its kernel along `u`.
  obtain ⟨φ₀, hφ₀, hφ₀u⟩ := exists_dual_vector ℝ u hu0.ne'
  set φ : StrongDual ℝ E := ‖u‖⁻¹ • φ₀ with hφ_def
  have hφu : φ u = 1 := by
    simp [φ, hφ₀u, inv_mul_cancel₀ hu0.ne']
  have hφnorm : ‖φ‖ = ‖u‖⁻¹ := by
    rw [hφ_def, norm_smul, hφ₀, mul_one, norm_inv, norm_norm]
  have hφle : ∀ z, |φ z| ≤ ‖u‖⁻¹ * ‖z‖ := fun z ↦ by
    simpa [Real.norm_eq_abs, hφnorm] using φ.le_opNorm z
  have hright : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℝ u) φ := fun r ↦ by
    simp [hφu]
  set P := φ.projKerOfRightInverse _ hright
  have hP : ∀ z, (P z : E) = z - φ z • u := fun z ↦ by simp [P]
  have hPu : P u = 0 := by
    ext1
    rw [hP, hφu, one_smul, sub_self, Submodule.coe_zero]
  -- In the coordinates `x = φ (· - γ a)` and `w = P (· - γ a)`, the arc has slope at most
  -- `2θ / (1 - θ) · ‖u‖`.
  have hx : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ φ (γ t - γ a)) (φ (γ' t)) (Icc a b) t :=
    fun t ht ↦ φ.hasFDerivAt.comp_hasDerivWithinAt t ((hγ t ht).sub_const (γ a))
  have hw : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ P (γ t - γ a)) (P (γ' t)) (Icc a b) t :=
    fun t ht ↦ P.hasFDerivAt.comp_hasDerivWithinAt t ((hγ t ht).sub_const (γ a))
  have hlow : ∀ t ∈ Ico a b, 1 - θ ≤ (b - a) * φ (γ' t) := fun t ht ↦ by
    have h := hφle ((b - a) • γ' t - u)
    rw [map_sub, map_smul, hφu, smul_eq_mul] at h
    have h' : ‖u‖⁻¹ * ‖(b - a) • γ' t - u‖ ≤ θ := by
      rw [inv_mul_le_iff₀ hu0, mul_comm]
      exact hclose t ht
    linarith [neg_abs_le ((b - a) * φ (γ' t) - 1)]
  have hba : 0 < b - a := sub_pos.2 hab'
  have hpos : ∀ t ∈ Ico a b, 0 < φ (γ' t) := fun t ht ↦
    pos_of_mul_pos_right ((sub_pos.2 hθ).trans_le (hlow t ht)) hba.le
  have hbound : ∀ t ∈ Ico a b, ‖P (γ' t)‖ ≤ 2 * θ / (1 - θ) * ‖u‖ * φ (γ' t) := fun t ht ↦ by
    -- `(b - a) • P (γ' t) = P r` with `r = (b - a) • γ' t - u`, since `P u = 0`.
    have hr : ‖(b - a) • (P (γ' t) : E)‖ ≤ 2 * θ * ‖u‖ := by
      have hPr : (b - a) • (P (γ' t) : E) = P ((b - a) • γ' t - u) := by
        rw [map_sub, map_smul, hPu, sub_zero, Submodule.coe_smul]
      rw [hPr, hP]
      calc ‖(b - a) • γ' t - u - φ ((b - a) • γ' t - u) • u‖
          ≤ ‖(b - a) • γ' t - u‖ + |φ ((b - a) • γ' t - u)| * ‖u‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ θ * ‖u‖ + ‖u‖⁻¹ * (θ * ‖u‖) * ‖u‖ := by
            gcongr
            · exact hclose t ht
            · exact (hφle _).trans (by gcongr; exact hclose t ht)
        _ = 2 * θ * ‖u‖ := by field_simp; ring
    rw [norm_smul, Real.norm_of_nonneg hba.le, Submodule.norm_coe] at hr
    have h1θ : 0 < 1 - θ := sub_pos.2 hθ
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h1θ]
    calc ‖P (γ' t)‖ * (1 - θ) ≤ ‖P (γ' t)‖ * ((b - a) * φ (γ' t)) :=
          mul_le_mul_of_nonneg_left (hlow t ht) (norm_nonneg _)
      _ = (b - a) * ‖P (γ' t)‖ * φ (γ' t) := by ring
      _ ≤ 2 * θ * ‖u‖ * φ (γ' t) := mul_le_mul_of_nonneg_right hr (hpos t ht).le
  obtain ⟨g, hg, hg0, hgb⟩ := exists_continuousMap_comp_eq_of_norm_deriv_le_mul_deriv hab hx hw
    (fun t ht ↦ hpos t (Ioo_subset_Ico_self ht)) hbound (by simp [P]) (by rw [← hu_def, hPu])
  simp only [sub_self, map_zero, ← hu_def, hφu, sub_zero] at hg0 hgb
  refine ⟨φ, hφu, hφnorm, ?_, g, hg0, hgb, fun t ht ↦ ?_⟩
  · refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) (fun t ht ↦
      (φ.continuous.comp_continuousOn (fun t ht ↦ (hγ t ht).continuousWithinAt)) t ht)
      (fun t ht ↦ ?_) (fun t ht ↦ hpos t (Ioo_subset_Ico_self (by rwa [interior_Icc] at ht)))
    rw [interior_Icc] at ht ⊢
    exact (φ.hasFDerivAt.comp_hasDerivWithinAt t (hγ t (Ioo_subset_Icc_self ht))).mono
      Ioo_subset_Icc_self
  · rw [hg t ht, hP]
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
  -- A lower bound `m > 0` for `‖γ'‖` and a modulus of uniform continuity of `γ'` on `[c, d + 1]`.
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith : c ≤ d + 1))
    hcont.norm.continuousOn
  set m := ‖deriv γ t₀‖
  have hm : 0 < m := norm_pos_iff.2 (hderiv t₀)
  set η := min θ 1 * m / 4 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ₀, hδ₀, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := c) (b := d + 1)).uniformContinuousOn_of_continuous hcont.continuousOn)
    η hη
  refine ⟨min (δ₀ / 2) 1, by positivity, fun a ha b hb t ht ↦ ?_⟩
  have hδ₁ : min (δ₀ / 2) 1 ≤ δ₀ / 2 := min_le_left _ _
  have hδ₂ : min (δ₀ / 2) 1 ≤ 1 := min_le_right _ _
  set h := b - a
  have hh : 0 < h := sub_pos.2 hb.1
  have hhδ : h ≤ min (δ₀ / 2) 1 := by simp only [h]; linarith [hb.2]
  set v := deriv γ a
  have hclose : ∀ s ∈ Icc a b, ‖deriv γ s - v‖ ≤ η := fun s hs ↦ by
    have := hunif s ⟨ha.1.trans hs.1, by linarith [hs.2, ha.2]⟩ a ⟨ha.1, by linarith [ha.2]⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2])
    rw [dist_eq_norm] at this
    exact this.le
  -- The chord is within `η h` of `h • γ' a`, by the mean value inequality for `γ s - s • γ' a`.
  have hmvt : ‖γ b - γ a - h • v‖ ≤ η * h := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := γ - fun s ↦ s • v)
      (f' := fun s ↦ deriv γ s - v) (fun s _ ↦ by
        simpa only [one_smul] using
          ((hdiff s).hasDerivAt.sub ((hasDerivAt_id' s).smul_const v)).hasDerivWithinAt)
      (fun s hs ↦ hclose s (Ico_subset_Icc_self hs)) b (right_mem_Icc.2 hb.1.le)
    convert this using 2
    simp only [Pi.sub_apply, h, sub_smul]
    abel
  have hv : m ≤ ‖v‖ := ht₀ ⟨ha.1, by linarith [ha.2]⟩
  have hu : h * m - η * h ≤ ‖γ b - γ a‖ := by
    have h1 : ‖h • v‖ ≤ ‖γ b - γ a‖ + ‖γ b - γ a - h • v‖ := by
      simpa only [norm_sub_rev (h • v)] using norm_le_norm_add_norm_sub' (h • v) (γ b - γ a)
    rw [norm_smul, Real.norm_of_nonneg hh.le] at h1
    nlinarith
  have hsplit : (b - a) • deriv γ t - (γ b - γ a) = h • (deriv γ t - v) - (γ b - γ a - h • v) := by
    simp only [h, smul_sub]
    abel
  rw [hsplit]
  have hθm : min θ 1 ≤ θ := min_le_left _ _
  have hθ1 : min θ 1 ≤ 1 := min_le_right _ _
  calc ‖h • (deriv γ t - v) - (γ b - γ a - h • v)‖
      ≤ h * η + η * h := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hmvt)
        rw [norm_smul, Real.norm_of_nonneg hh.le]
        exact mul_le_mul_of_nonneg_left (hclose t ht) hh.le
    _ ≤ min θ 1 * (h * m - η * h) := by
        have hθ0 : 0 ≤ min θ 1 := by positivity
        have key : 0 ≤ min θ 1 * (h * m) * (1 / 2 - min θ 1 / 4) :=
          mul_nonneg (mul_nonneg hθ0 (mul_pos hh hm).le) (by linarith)
        have : min θ 1 * (h * m - η * h) - (h * η + η * h) =
            min θ 1 * (h * m) * (1 / 2 - min θ 1 / 4) := by
          rw [hη_def]; ring
        linarith
    _ ≤ θ * ‖γ b - γ a‖ := by
        refine mul_le_mul hθm hu ?_ hθ.le
        rw [hη_def]
        nlinarith [mul_pos hh hm]

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
    rw [hba, sub_self, norm_zero, mul_zero, sub_zero, norm_le_zero_iff,
      smul_eq_zero] at this
    exact this.elim (fun h ↦ (sub_ne_zero.2 hab.ne').elim h) (hderiv a)
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

end ContDiff
