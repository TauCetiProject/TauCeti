/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Substitutions in interval integrals

On an interval of nonnegative reals the map `x ↦ x²` is monotone with derivative `2 x ≥ 0`, so
Mathlib's change of variables `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` applies
to any integrand `g`, with no continuity or integrability hypothesis on `g`:
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u`.

Similarly, on any interval not containing `0`, the map `t ↦ c / t` is monotone or antitone with
derivative `-c / t²`, giving both the interval-integrability equivalence and the substitution
identity `∫ t in a..b, (c / t²) • f (c / t) = ∫ u in (c / b)..(c / a), f u` with no continuity
or integrability assumption on `f`.

In an iterated interval integral whose outer variable `s` enters the integrand only through a
monotone `C¹` change of variables `β s` and its derivative, exchanging the two integrals (Fubini)
and substituting `σ = β s` in the new inner integral moves the substitution inside:
`∫ s in a..b, ∫ r in c..d, β' s • K r (β s) = ∫ r in c..d, ∫ σ in β a..β b, K r σ`.

## Main declarations

* `TauCeti.intervalIntegral.integral_comp_sq_mul`
* `TauCeti.intervalIntegral.intervalIntegrable_div_sq_smul_comp_div_iff`
* `TauCeti.intervalIntegral.integral_div_sq_smul_comp_div`
* `TauCeti.intervalIntegral.integral_integral_deriv_smul_comp_of_deriv_nonneg`
-/

public section

open MeasureTheory Set
open scoped Interval

namespace TauCeti

namespace intervalIntegral

/-- **Substituting `u = x²`.** For `0 ≤ a` and `0 ≤ b`,
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u` for every `g : ℝ → ℝ`. -/
theorem integral_comp_sq_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ → ℝ) :
    ∫ x in a..b, g (x ^ 2) * (2 * x) = ∫ u in a ^ 2..b ^ 2, g u :=
  _root_.intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := fun x => x ^ 2)
    (by fun_prop) (fun x _ => by simpa using hasDerivAt_pow 2 x) fun x hx => by
      linarith [(le_min ha hb).trans_lt hx.1]

private theorem continuousOn_const_div_of_notMem {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    ContinuousOn (fun t : ℝ ↦ c / t) (uIcc a b) :=
  continuousOn_const.div continuousOn_id fun _ ht h ↦ h0 (h ▸ ht)

private theorem hasDerivAt_const_div_of_mem_Ioo {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt (fun t : ℝ ↦ c / t) (-c / t ^ 2) t := by
  intro t ht
  have ht0 : t ≠ 0 := fun h ↦ h0 (h ▸ Ioo_subset_Icc_self ht)
  refine ((hasDerivAt_const t c).div (hasDerivAt_id' t) ht0).congr_deriv ?_
  ring

/-- **Substitution `u = c / t` for interval integrability.** Whenever `0 ∉ uIcc a b`,
`(c / t ^ 2) • f (c / t)` is interval integrable on `a..b` if and only if `f` is interval
integrable on `(c / b)..(c / a)`. -/
theorem intervalIntegrable_div_sq_smul_comp_div_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) (f : ℝ → E) :
    IntervalIntegrable (fun t ↦ (c / t ^ 2) • f (c / t)) volume a b ↔
      IntervalIntegrable f volume (c / b) (c / a) := by
  have hcont := continuousOn_const_div_of_notMem (c := c) h0
  have hderiv := hasDerivAt_const_div_of_mem_Ioo (c := c) h0
  have hneg :
      (IntervalIntegrable (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) volume a b ↔
          IntervalIntegrable (fun t ↦ (c / t ^ 2) • f (c / t)) volume a b) := by
    have heq : (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) =
        fun t ↦ -((c / t ^ 2) • f (c / t)) := funext fun t ↦ by
      simp [neg_div, neg_smul]
    rw [heq]
    exact ⟨fun h ↦ h.neg.congr fun t _ ↦ by simp, fun h ↦ h.neg⟩
  rw [← hneg]
  rcases le_total 0 c with hc | hc
  · rw [_root_.intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos hcont hderiv
        fun t _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg t),
      IntervalIntegrable.symm_iff]
  · rw [_root_.intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg hcont hderiv
        fun t _ ↦ div_nonneg (neg_nonneg.mpr hc) (sq_nonneg t),
      IntervalIntegrable.symm_iff]

/-- **Substituting `u = c / t`.** Whenever `0 ∉ uIcc a b`,
`∫ t in a..b, (c / t ^ 2) • f (c / t) = ∫ u in (c / b)..(c / a), f u` for every
`f : ℝ → E`, with no continuity or integrability hypothesis on `f`. -/
theorem integral_div_sq_smul_comp_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) (f : ℝ → E) :
    ∫ t in a..b, (c / t ^ 2) • f (c / t) = ∫ u in c / b..c / a, f u := by
  have hcont := continuousOn_const_div_of_notMem (c := c) h0
  have hderiv := hasDerivAt_const_div_of_mem_Ioo (c := c) h0
  have hneg :
      ∫ t in a..b, (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t =
        -∫ t in a..b, (c / t ^ 2) • f (c / t) := by
    have heq : (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) =
        fun t ↦ -((c / t ^ 2) • f (c / t)) := funext fun t ↦ by
      simp [neg_div, neg_smul]
    rw [heq, _root_.intervalIntegral.integral_neg]
  rcases le_total 0 c with hc | hc
  · have h := _root_.intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (g := f)
      hcont hderiv fun t _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg t)
    rw [hneg, _root_.intervalIntegral.integral_symm (c / b) (c / a)] at h
    exact neg_injective h
  · have h := _root_.intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := f)
      hcont hderiv fun t _ ↦ div_nonneg (neg_nonneg.mpr hc) (sq_nonneg t)
    rw [hneg, _root_.intervalIntegral.integral_symm (c / b) (c / a)] at h
    exact neg_injective h

/-- **Substituting in an iterated interval integral.** If `β` has a derivative `β'` at every point
of `[a, b]`, with `β'` continuous on `[a, b]` and nonnegative on `(a, b)`, then for every `K`
continuous on `[c, d] × [β a, β b]`, exchanging the two integrals and substituting `σ = β s` gives
`∫ s in a..b, ∫ r in c..d, β' s • K r (β s) = ∫ r in c..d, ∫ σ in β a..β b, K r σ`. -/
theorem integral_integral_deriv_smul_comp_of_deriv_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {β β' : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hβ : ∀ x ∈ Icc a b, HasDerivAt β (β' x) x) (hβ' : ContinuousOn β' (Icc a b))
    (hβ'₀ : ∀ x ∈ Ioo a b, 0 ≤ β' x) {K : ℝ → ℝ → E}
    (hK : ContinuousOn (Function.uncurry K) ([[c, d]] ×ˢ Icc (β a) (β b))) :
    ∫ s in a..b, ∫ r in c..d, β' s • K r (β s) = ∫ r in c..d, ∫ σ in β a..β b, K r σ := by
  have hcβ : ContinuousOn β (Icc a b) := fun x hx ↦ (hβ x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn β (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcβ
      (fun x hx ↦ (hβ x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      fun x hx ↦ ?_
    rw [interior_Icc] at hx
    rw [(hβ x (Ioo_subset_Icc_self hx)).deriv]
    exact hβ'₀ x hx
  have hmaps : MapsTo (fun p : ℝ × ℝ ↦ (p.2, β p.1)) (Icc a b ×ˢ [[c, d]])
      ([[c, d]] ×ˢ Icc (β a) (β b)) := fun p hp ↦
    ⟨hp.2, hmono ⟨le_rfl, hab⟩ hp.1 hp.1.1, hmono hp.1 ⟨hab, le_rfl⟩ hp.1.2⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦ β' p.1 • K p.2 (β p.1)) (Icc a b ×ˢ [[c, d]]) :=
    (hβ'.comp continuousOn_fst mapsTo_fst_prod).smul (hK.comp
      (continuousOn_snd.prodMk (hcβ.comp continuousOn_fst mapsTo_fst_prod)) hmaps)
  rw [intervalIntegral_intervalIntegral_swap (F := fun s r ↦ β' s • K r (β s))
    ((hc.integrableOn_compact (isCompact_Icc.prod isCompact_uIcc)).mono_set
      (prod_mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self) uIoc_subset_uIcc))]
  -- Substitute `σ = β s` in the new inner integral.
  have hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt β (β' x) x := by
    rw [min_eq_left hab, max_eq_right hab]
    exact fun x hx ↦ hβ x (Ioo_subset_Icc_self hx)
  have hd₀ : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ β' x := by
    rw [min_eq_left hab, max_eq_right hab]
    exact hβ'₀
  exact _root_.intervalIntegral.integral_congr fun r _ ↦
    _root_.intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := K r)
      (by rwa [uIcc_of_le hab]) hd hd₀

end intervalIntegral

end TauCeti
