/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.LipschitzRegularity
public import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.PVAggregation
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.LipschitzBoundedIntegrand
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.Analysis.Contour.Winding.PrincipalValueRealIntegral

/-!
# The real bounded-integrand formula for the winding number, allowing crossings

Hungerbühler–Wasem Proposition 2.3 evaluates the generalized winding number by the real,
non-principal-value integral

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`,

for a closed piecewise-`C¹` immersion `γ`. `Winding.RealIntegral.Basic` proves this when `γ`
avoids `s` throughout, where the winding number is already a genuine integer. This file drops
that avoidance hypothesis: `s` may be a value of `γ`, so long as every parameter where `γ` meets
`s` is interior to `[a, b]` **and** `derivWithin γ` is Lipschitz on a one-sided closed piece
ending or starting there (`C^{1,1}`, possibly a different piece on each side, so a crossing may
coincide with a breakpoint of the immersion). The generalized winding number is then a genuine
Cauchy principal value rather than an ordinary index integral, and this theorem shows it is still
real and equal
to the same bounded real integral. Unlike the avoiding case, interval-integrability of that
integral is not assumed here: it follows from a.e. strong measurability together with the
boundedness above, but the two draw from different sources -- measurability from `γ`'s
continuity plus Mathlib's unconditional measurability of `deriv` (`aestronglyMeasurable_deriv`),
no different from the avoiding case; boundedness alone from the `C^{1,1}` crossing regularity
this file's boundedness result needs. (That regularity hypothesis is satisfied vacuously when
`γ` never meets `s`, so this also recovers the
avoiding case *for piecewise-`C¹` immersions* — but `Winding.RealIntegral.Basic`'s theorem
remains needed for avoiding curves that are not immersions, since it only assumes continuity,
differentiability off a countable set, avoidance, and integrability; the two are kept as separate
theorems, with incomparable hypotheses.)

This bundles two independent facts about the single-point Cauchy principal value
`L := 2πi · n_s(γ)` of the Cauchy kernel `(z - s)⁻¹` along `γ`:

* **Reality** (`Re L = 0`): the real part of the truncated index integral telescopes to
  `Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖` regardless of any branch-cut/slit-plane data — the
  real part of `Complex.log` never depends on a branch — and this vanishes by closedness.
* **The integral identity** (`Im L = ∫ h`, `h` the real winding integrand): supplied directly by
  `HasCauchyPVAt.im_eq_integral_realWindingIntegrand`, since `h` is interval-integrable.

Both facts are read off the *same* explicit principal-value witness, built by
`Crossing.PVAggregation`'s per-window aggregation from the plain (avoiding) pieces and the
per-crossing windows along the sorted crossing list.

## Main results

* `TauCeti.Contour.windingNumber_eq_real_integral_of_closed_interior_crossings` — the real
  bounded-integrand formula for a closed immersion that avoids `s` at its basepoint (so every
  crossing of `s`, if any, is automatically interior).
* `TauCeti.Contour.isBounded_image_realWindingIntegrand_of_interior_crossings` and
  `TauCeti.Contour.intervalIntegrable_realWindingIntegrand_of_interior_crossings` — the
  boundedness and interval-integrability facts the formula above is built from, for callers that
  need those facts rather than just the equality.

## Provenance

New assembly of HW Prop 2.3, built from existing Tau Ceti
contour-integration infrastructure: the per-crossing window value
(`exists_radius_perWindow_tendsto_log_norm_add_arg`), the existence-and-real-part aggregation
(`exists_hasCauchyPVAt_re_eq_of_perWindow_tendsto_of_interiorDisjoint`), the integral-identity
bridge (`HasCauchyPVAt.im_eq_integral_realWindingIntegrand`), and the plain-piece log-norm
telescoping (`Winding.SegmentSum.re_integral_inv_sub_mul_deriv_eq_log_norm`), which feeds the
real-part telescoping hypothesis of the aggregation theorem. This file's own content is deriving
the real winding integrand's boundedness and interval-integrability from the crossing regularity
rather than assuming them, via `Winding.LipschitzBoundedIntegrand`'s one-sided bounds
instantiating `Crossing.Windows`'s generic sorted-crossing-list gluing induction
(`sorted_crossing_gluing_induction`) with that integrability invariant directly, the same way
`Crossing.PVAggregation`'s own per-window aggregation theorems instantiate it for their
value-carrying invariants, rather than re-deriving the induction shape by hand -- and the
assembly of all of the above into the final formula. The per-crossing window value this file
reads off (`exists_radius_perWindow_tendsto_log_norm_add_arg`), with both its real and imaginary
parts, is proved once, generically, in `InvSubCPVExistence`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology intervalIntegral

open scoped Interval NNReal

namespace TauCeti.Contour

/-! ### Interval-integrability of the real winding integrand, allowing crossings -/

/-- **The real winding integrand is interval-integrable on a window where `γ` is continuous and
the integrand is bounded.** Measurability of `deriv γ` is unconditional in Mathlib
(`aestronglyMeasurable_deriv`), so no `derivWithin`-congruence argument off a null set is needed
here, unlike `intervalIntegrable_inv_sub_truncated`, which must bridge to `derivWithin` on an
avoidance-free piece. Used at a `C^{1,1}` crossing with `hbdd` supplied by
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right`/`_left`'s
window, shrunk to any sub-window the caller needs; needs no avoidance hypothesis or the two
sides of a crossing to agree. -/
private theorem intervalIntegrable_realWindingIntegrand_window {γ : ℝ → ℂ} {s : ℂ} {p q : ℝ}
    (hpq : p ≤ q) (hγc : ContinuousOn γ (Icc p q))
    (hbdd : Bornology.IsBounded
      ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc p q)) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume p q := by
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  have huIoc_sub : uIoc p q ⊆ Icc p q := (uIoc_subset_uIcc).trans (by rw [uIcc_of_le hpq])
  have haesm : AEStronglyMeasurable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t))
      (volume.restrict (uIoc p q)) := by
    have hγ_aem : AEMeasurable γ (volume.restrict (uIoc p q)) :=
      ((hγc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    have hd_aesm : AEStronglyMeasurable (deriv γ) (volume.restrict (uIoc p q)) :=
      aestronglyMeasurable_deriv γ _
    refine (Complex.imCLM.continuous.comp_aestronglyMeasurable
      ((hγ_aem.sub_const s).inv.aestronglyMeasurable.mul hd_aesm)).congr
      (MeasureTheory.ae_of_all _ fun t ↦ ?_)
    simp only [Complex.imCLM_apply, realWindingIntegrand_def, Pi.mul_apply, Pi.inv_apply]
  rw [intervalIntegrable_iff]
  have : IsFiniteMeasure (volume.restrict (uIoc p q)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono uIoc_subset_uIcc).trans_lt
      (by rw [uIcc_of_le hpq]; exact isCompact_Icc.measure_lt_top)).ne
  refine Integrable.of_bound haesm C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  exact hC _ ⟨t, huIoc_sub ht, rfl⟩

/-! ### Assembly -/

/-- **The real winding integrand is bounded on `[a, b]`, from a common crossing-window radius
and a per-window bound.** Self-contained from the principal-value machinery: bounded on each of
the finitely many crossing windows `[t₀ - ρ_lip t₀, t₀ + ρ_lip t₀]` (themselves bounded by
`hρ_lip_bdd`, typically from the crossing's `C^{1,1}` regularity), and bounded away from every
smaller window `[t₀ - ρ, t₀ + ρ]` (`ρ ≤ ρ_lip t₀` throughout) by the crude `‖v‖ / m` estimate,
`m` the lower bound `hm` on `‖γ - s‖` there and `Cd` a bound on `‖deriv γ‖` over all of `[a, b]`
(piecewise-`C¹`, hence bounded on finitely many pieces). -/
private theorem isBounded_realWindingIntegrand_of_crossing_windows {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (T : Finset ℝ) {ρ : ℝ}
    (ρ_lip : ℝ → ℝ) (hρ_le_ρlip : ∀ t ∈ T, ρ ≤ ρ_lip t)
    (hρ_lip_bdd : ∀ t₀ ∈ T, Bornology.IsBounded
      ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) ''
        Icc (t₀ - ρ_lip t₀) (t₀ + ρ_lip t₀)))
    {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ u ∈ Icc a b, (∀ t ∈ T, u ∉ Ioo (t - ρ) (t + ρ)) → m ≤ ‖γ u - s‖) :
    Bornology.IsBounded ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) := by
  obtain ⟨Cd, hCd⟩ := h_imm.isPiecewiseC1On.isBounded_image_deriv.exists_norm_le
  have hwin_union_bdd : Bornology.IsBounded
      (⋃ t₀ ∈ T, (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) ''
        Icc (t₀ - ρ) (t₀ + ρ)) :=
    (Bornology.isBounded_biUnion_finset T).mpr fun t₀ ht₀ ↦ by
      have hsub : Icc (t₀ - ρ) (t₀ + ρ) ⊆ Icc (t₀ - ρ_lip t₀) (t₀ + ρ_lip t₀) :=
        Icc_subset_Icc (by linarith [hρ_le_ρlip t₀ ht₀]) (by linarith [hρ_le_ρlip t₀ ht₀])
      exact (hρ_lip_bdd t₀ ht₀).subset (Set.image_mono hsub)
  refine (hwin_union_bdd.union (Metric.isBounded_closedBall
    (x := (0 : ℝ)) (r := Cd / m))).subset ?_
  rintro y ⟨t, ht, rfl⟩
  by_cases hcase : ∀ t₀ ∈ T, t ∉ Ioo (t₀ - ρ) (t₀ + ρ)
  · refine Or.inr ?_
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    have hm_le : m ≤ ‖γ t - s‖ := hm t ht hcase
    have hv_le : ‖deriv γ t‖ ≤ Cd := hCd _ ⟨t, uIcc_of_le hab ▸ ht, rfl⟩
    calc |realWindingIntegrand (γ t - s) (deriv γ t)| ≤ ‖deriv γ t‖ / m :=
          abs_realWindingIntegrand_le_div_of_le_norm hm_pos hm_le
      _ ≤ Cd / m := by gcongr
  · push Not at hcase
    obtain ⟨t₀, ht₀, htwin⟩ := hcase
    exact Or.inl (Set.mem_biUnion ht₀ ⟨t, Ioo_subset_Icc_self htwin, rfl⟩)

/-- On a sub-interval where `γ` stays at distance at least `m > 0` from `s`, the curve avoids `s`
there and the complex index integrand is interval-integrable.

Only continuity of `γ` and integrability of its derivative are needed; no regularity at a
crossing, since the interval carries none. -/
private theorem ne_and_intervalIntegrable_inv_sub_mul_deriv_of_le_norm_sub
    {γ : ℝ → ℂ} {s : ℂ} {a b m : ℝ} (hγ_cont : ContinuousOn γ (Icc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hm_pos : 0 < m)
    {l u : ℝ} (hA : a ≤ l) (hlu : l ≤ u) (hu : u ≤ b)
    (h_far : ∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) :
    (∀ t ∈ Icc l u, γ t ≠ s) ∧
      IntervalIntegrable (fun t ↦ (γ t - s)⁻¹ * deriv γ t) volume l u :=
  have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq ↦ by
    have := h_far t ht
    rw [h_eq, sub_self, norm_zero] at this
    linarith
  ⟨h_ne, intervalIntegrable_inv_sub_mul_deriv
    (by rw [uIcc_of_le hlu]; exact hγ_cont.mono (Icc_subset_Icc hA hu))
    (by intro t ht; rw [uIcc_of_le hlu] at ht; exact h_ne t ht)
    (hderiv_int.mono_set (by
      rw [uIcc_of_le hlu, uIcc_of_le (hA.trans (hlu.trans hu))]
      exact Icc_subset_Icc hA hu))⟩

/-- Wherever the complex index integrand is interval-integrable, so is the real winding
integrand. -/
private theorem intervalIntegrable_realWindingIntegrand_of_inv_sub_mul_deriv
    {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    (hcplx : IntervalIntegrable (fun t ↦ (γ t - s)⁻¹ * deriv γ t) volume l u) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume l u := by
  -- the real integrand is the imaginary part of the index integrand
  have hfun_eq : (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t))
      = (fun t ↦ ((γ t - s)⁻¹ * deriv γ t).im) :=
    funext fun t ↦ realWindingIntegrand_def (γ t - s) (deriv γ t)
  rw [hfun_eq]
  exact ⟨hcplx.1.im, hcplx.2.im⟩

/-- **A bounded window at each interior crossing.** From one-sided `C^{1,1}` regularity at an
interior crossing `t₀` of `s`, the real winding integrand is bounded on some window
`[t₀ - ρ, t₀ + ρ]`, and interval-integrable on every smaller symmetric window. -/
private theorem exists_window_isBounded_intervalIntegrable_realWindingIntegrand
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hγt₀ : γ t₀ = s) (hlip : HasLipschitzDerivOnEachSideAt γ t₀) :
    ∃ ρ > 0, Bornology.IsBounded
        ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc (t₀ - ρ) (t₀ + ρ)) ∧
      ∀ r, 0 < r → r ≤ ρ → IntervalIntegrable
        (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume (t₀ - r) (t₀ + r) := by
  have hab : a ≤ b := (ht₀.1.trans ht₀.2).le
  have h_Ico : t₀ ∈ Ico (min a b) (max a b) := by
    rw [min_eq_left hab, max_eq_right hab]; exact ⟨ht₀.1.le, ht₀.2⟩
  have h_Ioc : t₀ ∈ Ioc (min a b) (max a b) := by
    rw [min_eq_left hab, max_eq_right hab]; exact ⟨ht₀.1, ht₀.2.le⟩
  obtain ⟨εR, hεR, KR, hlipR, εL, hεL, KL, hlipL⟩ := hasLipschitzDerivOnEachSideAt_iff.mp hlip
  -- Each side's Lipschitz window need not avoid every breakpoint of the immersion, so shrink it
  -- to a piece that does, picking up differentiability there for free.
  obtain ⟨d, htd, -, hdiffR, hlipR'⟩ := h_imm.exists_lipschitzOnWith_derivWithin_shrink_right
    h_Ico (by linarith : t₀ < t₀ + εR) hlipR
  obtain ⟨c, -, hct, hdiffL, hlipL'⟩ := h_imm.exists_lipschitzOnWith_derivWithin_shrink_left
    h_Ioc (by linarith : t₀ - εL < t₀) hlipL
  obtain ⟨ρ, hρ_pos, hρ_lt, hbdd⟩ :=
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner hct htd
      hdiffR hlipR' hdiffL hlipL' hγt₀ (h_imm.derivWithin_ne_zero_right h_Ico htd)
      (h_imm.derivWithin_ne_zero_left h_Ioc hct)
  have hρR : ρ ≤ d - t₀ := (hρ_lt.trans_le (min_le_left _ _)).le
  have hρL : ρ ≤ t₀ - c := (hρ_lt.trans_le (min_le_right _ _)).le
  refine ⟨ρ, hρ_pos, hbdd, fun r hr hrρ ↦ ?_⟩
  -- the two halves of the window, each inside one of the one-sided pieces
  exact (intervalIntegrable_realWindingIntegrand_window (by linarith)
      (hdiffL.continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl))
      (hbdd.subset (Set.image_mono (Icc_subset_Icc (by linarith) (by linarith))))).trans
    (intervalIntegrable_realWindingIntegrand_window (by linarith)
      (hdiffR.continuousOn.mono (Icc_subset_Icc le_rfl (by linarith)))
      (hbdd.subset (Set.image_mono (Icc_subset_Icc (by linarith) (by linarith)))))

/-- **A window radius at an interior crossing.** From one-sided `C^{1,1}` regularity at an interior
crossing `t₀` of `s`, there is a radius `R > 0` such that the real winding integrand is bounded on
`[t₀ - R, t₀ + R]` and interval-integrable on every smaller symmetric window, and on every
smaller window inside `(a, b]` meeting `s` only at `t₀` the truncated integrals of the index
integrand converge, as the truncation tends to `0`, to a value whose real part is the log-norm
difference at the window's endpoints. -/
private theorem exists_crossing_window_isBounded_intervalIntegrable_tendsto
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hγt₀ : γ t₀ = s) (hlip : HasLipschitzDerivOnEachSideAt γ t₀) :
    ∃ R > 0, Bornology.IsBounded
        ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc (t₀ - R) (t₀ + R)) ∧
      (∀ r, 0 < r → r ≤ R → IntervalIntegrable
        (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume (t₀ - r) (t₀ + r)) ∧
      ∀ r, 0 < r → r ≤ R → a < t₀ - r → t₀ + r ≤ b →
        (∀ t ∈ Icc (t₀ - r) (t₀ + r), γ t = s → t = t₀) →
        ∃ v : ℂ, v.re = Real.log ‖γ (t₀ + r) - s‖ - Real.log ‖γ (t₀ - r) - s‖ ∧
          Tendsto (fun ε : ℝ ↦ ∫ u in (t₀ - r)..(t₀ + r),
            if ‖γ u - s‖ > ε then (γ u - s)⁻¹ * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  obtain ⟨R₀, hR₀, L_R, L_L, -, -, -, -, h_spec⟩ :=
    exists_radius_perWindow_tendsto_log_norm_add_arg h_imm ht₀ hγt₀
  obtain ⟨ρ, hρ, hbdd, hint⟩ :=
    exists_window_isBounded_intervalIntegrable_realWindingIntegrand h_imm ht₀ hγt₀ hlip
  refine ⟨min R₀ ρ, lt_min hR₀ hρ, hbdd.subset (Set.image_mono (Icc_subset_Icc
    (by linarith [min_le_right R₀ ρ]) (by linarith [min_le_right R₀ ρ]))),
    fun r hr hrR ↦ hint r hr (hrR.trans (min_le_right _ _)), fun r hr hrR hl hu huniq ↦ ?_⟩
  have hrR₀ := hrR.trans (min_le_left R₀ ρ)
  exact ⟨((Real.log ‖γ (t₀ + r) - s‖ - Real.log ‖γ (t₀ - r) - s‖ : ℝ) : ℂ) +
      ((((-L_L) / (γ (t₀ - r) - s)).arg + ((γ (t₀ + r) - s) / L_R).arg : ℝ) : ℂ) * Complex.I,
    by simp, h_spec (t₀ - r) (t₀ + r) (by linarith) (by linarith) (by linarith) (by linarith)
      hl hu huniq⟩

/-- **The real part of a plain piece's index integral is the log-norm difference.** On a piece
`[l, u] ⊆ [a, b]` of a piecewise `C¹` immersion where `γ` stays at distance at least `m > 0` from
`s`, the real part of `∫ (γ t - s)⁻¹ γ'(t) dt` is `log ‖γ u - s‖ - log ‖γ l - s‖`. -/
private theorem re_integral_inv_sub_mul_deriv_eq_log_norm_of_le_norm_sub {γ : ℝ → ℂ}
    {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) {m : ℝ} (hm_pos : 0 < m)
    {l u : ℝ} (hA : a ≤ l) (hlu : l ≤ u) (hu : u ≤ b) (h_far : ∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) :
    (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab).ge
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  rw [min_eq_left hab, max_eq_right hab] at hp
  obtain ⟨h_ne, hcplx⟩ := ne_and_intervalIntegrable_inv_sub_mul_deriv_of_le_norm_sub hγ_cont
    h_imm.isPiecewiseC1On.intervalIntegrable_deriv hm_pos hA hlu hu h_far
  exact re_integral_inv_sub_mul_deriv_eq_log_norm hlu p.countable_toSet
    (hγ_cont.mono (Icc_subset_Icc hA hu))
    (fun t ht ↦ hp t ⟨Ioo_subset_Ioo hA hu ht.1, ht.2⟩) h_ne hcplx

/-- **Interval-integrability of the real winding integrand from crossing windows.** If every
crossing `t₀ ∈ T` of `s` has a symmetric window of radius `ρ ≤ ρ_lip t₀` on which the integrand is
interval-integrable, the windows are separated and interior, and `γ` stays at distance `m > 0`
from `s` off the windows, then the integrand is interval-integrable on `[a, b]`: away from the
windows it is the imaginary part of the integrable index integrand, and the pieces are glued. -/
private theorem intervalIntegrable_realWindingIntegrand_of_crossing_windows {γ : ℝ → ℂ}
    {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (T : Finset ℝ) {ρ : ℝ}
    (ρ_lip : ℝ → ℝ) (hρ_pos : 0 < ρ) (h_endpts : ∀ t ∈ T, a + ρ < t ∧ t < b - ρ)
    (h_pair : ∀ t ∈ T, ∀ t' ∈ T, t' ≠ t → 2 * ρ < |t - t'|)
    (hρ_le_ρlip : ∀ t ∈ T, ρ ≤ ρ_lip t)
    (hρ_lip_int : ∀ t₀ ∈ T, ∀ r, 0 < r → r ≤ ρ_lip t₀ → IntervalIntegrable
      (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume (t₀ - r) (t₀ + r))
    {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ u ∈ Icc a b, (∀ t ∈ T, u ∉ Ioo (t - ρ) (t + ρ)) → m ≤ ‖γ u - s‖) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume a b := by
  have h_piece : ∀ l u : ℝ, a ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume l u :=
    fun l u hA hlu hu h_far' ↦ intervalIntegrable_realWindingIntegrand_of_inv_sub_mul_deriv
      (ne_and_intervalIntegrable_inv_sub_mul_deriv_of_le_norm_sub
        (h_imm.continuousOn.mono (uIcc_of_le hab).ge)
        h_imm.isPiecewiseC1On.intervalIntegrable_deriv hm_pos hA hlu hu h_far').2
  exact sorted_crossing_gluing_induction h_piece (fun _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)
    (T.sort (· ≤ ·)) (Finset.sortedLT_sort T) a le_rfl hab
    (fun t ht ↦ by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
    (fun t ht ↦ by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
    (fun t ht t' ht' hne ↦ (h_pair t ((Finset.mem_sort _).mp ht) t'
      ((Finset.mem_sort _).mp ht') hne).le)
    (fun t ht ↦ hρ_lip_int t ((Finset.mem_sort _).mp ht) ρ hρ_pos
      (hρ_le_ρlip t ((Finset.mem_sort _).mp ht)))
    (fun u hu h_avoid ↦ hm u hu fun t ht ↦ h_avoid t ((Finset.mem_sort _).mpr ht))

/-- **The real bounded-integrand formula's boundedness, integrability, and Cauchy-PV facts, from
interior crossings alone** (Hungerbühler–Wasem Prop 2.3's analytic content). Unlike
`windingNumber_eq_real_integral_of_closed_interior_crossings` below, this needs no closedness
assumption -- the caller must instead directly supply that every crossing of `s` is interior,
which closedness would otherwise buy for free (an endpoint avoiding `s` forces the other endpoint
to as well, so no crossing can sit exactly at either). Closedness's other role is to show the
principal value's real part vanishes, which is a one-line addition on top of what this theorem
already supplies (`L.re = Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖`, zero exactly when `γ a = γ b`).

Unlike the off-curve case, the real winding integrand `h t := realWindingIntegrand (γ t - s)
(deriv γ t)`'s boundedness and interval-integrability are not assumed here: both are derived from
the crossing regularity, via
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner`'s boundedness
at each `C^{1,1}` crossing, its continuity off the crossing itself giving the measurability half,
and the ordinary avoidance argument between crossings — the actual content of HW Prop 2.3. -/
private theorem isBounded_intervalIntegrable_cauchyPV_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → HasLipschitzDerivOnEachSideAt γ t) :
    Bornology.IsBounded ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) ∧
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    ∃ L : ℂ, HasCauchyPVAt γ a b (fun z ↦ (z - s)⁻¹) s L ∧
      L.re = Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖ ∧
      L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) := by
  classical
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} ↦ by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings_of_le hab]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq ↦ hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht ↦
    h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab).ge
  have h_int_tr : ∀ ε : ℝ, 0 < ε → IntervalIntegrable
      (fun t ↦ if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) volume a b :=
    fun _ hε ↦ intervalIntegrable_inv_sub_truncated h_imm.continuousOn
      h_imm.isPiecewiseC1On.intervalIntegrable_deriv hε
  -- Each crossing gets a window radius carrying its bounded, integrable and principal-value facts.
  choose! R hR_pos hR_bdd hR_int hR_win using fun t₀ (ht₀ : t₀ ∈ T) ↦
    exists_crossing_window_isBounded_intervalIntegrable_tendsto h_imm (h_Ioo t₀ ht₀)
      (hT_mem.mp ht₀).2 (hγ_lip t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2)
  obtain ⟨ρ, hρ_pos, h_endpts, h_pair, hρ_le_R⟩ := exists_common_window_radius_le h_Ioo R hR_pos
  have h_unique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀ := fun t₀ ht₀ t ht h_eq ↦
    eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀) (h_pair t₀ ht₀) h_complete ht h_eq
  obtain ⟨m, hm_pos, hm⟩ := exists_complement_windows_dist_lower_bound hγ_cont h_complete
    (fun _ ↦ ρ) fun t _ ↦ hρ_pos
  have h_int : IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume
      a b :=
    intervalIntegrable_realWindingIntegrand_of_crossing_windows h_imm hab T R hρ_pos
      h_endpts h_pair hρ_le_R hR_int hm_pos hm
  -- Both the principal-value witness and the real-part telescoping are read off in one call:
  -- the plain pieces telescope in real part to the log-norm difference
  -- (`re_integral_inv_sub_mul_deriv_eq_log_norm`), and each window's explicit limit value has
  -- exactly that real part built in already (`exists_radius_perWindow_tendsto_log_norm_add_arg`).
  obtain ⟨L, hHCPV, hRe0⟩ := exists_hasCauchyPVAt_re_eq_of_perWindow_tendsto_of_interiorDisjoint
    (g := fun z ↦ (z - s)⁻¹) (Ψ := fun t ↦ Real.log ‖γ t - s‖) hab T
    (fun _ ↦ hρ_pos.le)
    (fun t ht ↦ by linarith [(h_endpts t ht).1])
    (fun t ht ↦ by linarith [(h_endpts t ht).2])
    (fun t ht t' ht' hne ↦ (h_pair t ht t' ht' hne).le)
    h_int_tr
    (fun l u hA hlu hu h_far' ↦
      re_integral_inv_sub_mul_deriv_eq_log_norm_of_le_norm_sub h_imm hab hm_pos hA hlu hu h_far')
    (fun t ht ↦ hR_win t ht ρ hρ_pos (hρ_le_R t ht) (by linarith [(h_endpts t ht).1])
      (by linarith [(h_endpts t ht).2]) (h_unique t ht))
    ⟨hm_pos, hm⟩
  -- The integral identity: the imaginary part is the ordinary integral of the real integrand.
  -- Reuses the upstream principal-value/real-integrand bridge directly, rather than re-deriving
  -- its dominated-convergence argument here.
  have hIm : L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) :=
    hHCPV.im_eq_integral_realWindingIntegrand h_int
  have h_bdd : Bornology.IsBounded
      ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) :=
    isBounded_realWindingIntegrand_of_crossing_windows h_imm hab T R hρ_le_R
      hR_bdd hm_pos hm
  exact ⟨h_bdd, h_int, L, hHCPV, hRe0, hIm⟩

/-- **The `uIcc`-generic (orientation-generic) form of
`isBounded_intervalIntegrable_cauchyPV_of_interior_crossings`.** Supplies the same triple —
boundedness, interval-integrability, and the Cauchy-PV witness with its real and imaginary
parts — without an `a ≤ b` hypothesis, by reducing to that `a ≤ b`-ordered theorem and, in the
reversed case, negating the principal value and flipping the integral (`HasCauchyPVAt.symm`,
`intervalIntegral.integral_symm`) to convert the result back to the caller's own order. The
two public projections below (and `windingNumber_eq_real_integral_of_closed_interior_crossings`)
all read off this one. -/
private theorem isBounded_intervalIntegrable_cauchyPV_of_interior_crossings_uIcc
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b)
    (h_interior : ∀ t ∈ uIcc a b, γ t = s → t ∈ Ioo (min a b) (max a b))
    (hγ_lip : ∀ t ∈ uIcc a b, γ t = s → HasLipschitzDerivOnEachSideAt γ t) :
    Bornology.IsBounded ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' uIcc a b) ∧
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    ∃ L : ℂ, HasCauchyPVAt γ a b (fun z ↦ (z - s)⁻¹) s L ∧
      L.re = Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖ ∧
      L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h_interior hγ_lip
    rw [min_eq_left hab, max_eq_right hab] at h_interior
    rw [uIcc_of_le hab]
    exact isBounded_intervalIntegrable_cauchyPV_of_interior_crossings h_imm hab h_interior hγ_lip
  · rw [uIcc_comm, uIcc_of_le hab] at h_interior hγ_lip
    rw [min_eq_right hab, max_eq_left hab] at h_interior
    obtain ⟨hbdd, hint, L, hHCPV, hRe0, hIm⟩ :=
      isBounded_intervalIntegrable_cauchyPV_of_interior_crossings h_imm.symm hab h_interior hγ_lip
    refine ⟨?_, hint.symm, -L, hHCPV.symm, ?_, ?_⟩
    · rwa [uIcc_comm, uIcc_of_le hab]
    · rw [Complex.neg_re, hRe0]
      ring
    · rw [Complex.neg_im, hIm, intervalIntegral.integral_symm, neg_neg]

/-- **The real winding integrand is bounded on all of `[[a, b]]` for an immersion with interior
crossings** (Hungerbühler–Wasem Prop 2.3, boundedness half). Needs no closedness, only that every
crossing of `s` is interior to `[[a, b]]`. Orientation-generic, like `IsPwC1ImmersionOn` itself:
no `a ≤ b` is needed. See `windingNumber_eq_real_integral_of_closed_interior_crossings` below for
the closed-curve equality and the full documentation of `hγ_lip`. -/
theorem isBounded_image_realWindingIntegrand_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b)
    (h_interior : ∀ t ∈ uIcc a b, γ t = s → t ∈ Ioo (min a b) (max a b))
    (hγ_lip : ∀ t ∈ uIcc a b, γ t = s → HasLipschitzDerivOnEachSideAt γ t) :
    Bornology.IsBounded ((fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) '' uIcc a b) :=
  (isBounded_intervalIntegrable_cauchyPV_of_interior_crossings_uIcc h_imm h_interior hγ_lip).1

/-- **The real winding integrand is interval-integrable along an immersion with interior
crossings** (Hungerbühler–Wasem Prop 2.3, integrability half). Needs no closedness, only that
every crossing of `s` is interior to `[[a, b]]`. Orientation-generic, like `IsPwC1ImmersionOn`
itself: no `a ≤ b` is needed. See `windingNumber_eq_real_integral_of_closed_interior_crossings`
below for the closed-curve equality and the full documentation of `hγ_lip`. -/
theorem intervalIntegrable_realWindingIntegrand_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b)
    (h_interior : ∀ t ∈ uIcc a b, γ t = s → t ∈ Ioo (min a b) (max a b))
    (hγ_lip : ∀ t ∈ uIcc a b, γ t = s → HasLipschitzDerivOnEachSideAt γ t) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t - s) (deriv γ t)) volume a b :=
  (isBounded_intervalIntegrable_cauchyPV_of_interior_crossings_uIcc h_imm h_interior hγ_lip).2.1

/-- **The real bounded-integrand formula, allowing crossings** (Hungerbühler–Wasem Prop 2.3).
For a closed piecewise-`C¹` immersion `γ` on `[[a, b]]` that avoids `s` at the basepoint `a`
(`hsa`, so also at `b` by closedness — every other crossing of `s`, if any, is automatically
interior to `[[a, b]]`) and is `C^{1,1}` on each side of any such crossing (`derivWithin γ`
Lipschitz on a one-sided closed piece ending or starting there, `hγ_lip` — the two sides need not
agree, so a crossing may coincide with a breakpoint of the immersion) — in particular satisfied
vacuously if `γ` never meets `s` — the generalized winding number `n_s(γ)` is a real number equal
to its ordinary (non-principal-value) integral:

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`.

The two sides of a crossing need not agree: `hγ_lip` allows the crossing to coincide with a
breakpoint of the piecewise-`C¹` immersion (a corner), matching Hungerbühler–Wasem's own proof of
Prop 2.3, which handles that case via the same one-sided splitting (arXiv:1808.00997, p. 9).
Orientation-generic, like `windingNumber` and `intervalIntegral` themselves: no `a ≤ b` is
needed. -/
theorem windingNumber_eq_real_integral_of_closed_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b)
    (hclosed : γ a = γ b) (hsa : γ a ≠ s)
    (hγ_lip : ∀ t ∈ uIcc a b, γ t = s → HasLipschitzDerivOnEachSideAt γ t) :
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) := by
  -- Every crossing is interior: on `[[a, b]]`, `t ∈ Ioo (min a b) (max a b)` reduces to
  -- `t ≠ a ∧ t ≠ b`, and both endpoints avoid `s` -- `a` directly by `hsa`, `b` via
  -- `hclosed : γ a = γ b`.
  have hsb : γ b ≠ s := hclosed ▸ hsa
  have hs_min : γ (min a b) ≠ s := by rcases min_choice a b with h | h <;> rw [h] <;> assumption
  have hs_max : γ (max a b) ≠ s := by rcases max_choice a b with h | h <;> rw [h] <;> assumption
  have h_interior : ∀ t ∈ uIcc a b, γ t = s → t ∈ Ioo (min a b) (max a b) := fun t ht h_eq ↦ by
    rw [← Icc_min_max] at ht
    exact ⟨ht.1.lt_of_ne (by rintro rfl; exact hs_min h_eq),
      ht.2.lt_of_ne (by intro h; exact hs_max (h ▸ h_eq))⟩
  -- Closedness is used only here: to show every crossing is interior (above) and that the
  -- principal value's real part vanishes (`hRe` below, `= Real.log ‖γ b - s‖ -
  -- Real.log ‖γ a - s‖` by `hRe0`, which is `0` exactly when `γ a = γ b`). The boundedness,
  -- integrability, and Cauchy-PV construction themselves need no closedness assumption -- see
  -- `isBounded_image_realWindingIntegrand_of_interior_crossings` and
  -- `intervalIntegrable_realWindingIntegrand_of_interior_crossings` above, which project them
  -- directly from `isBounded_intervalIntegrable_cauchyPV_of_interior_crossings`.
  obtain ⟨-, -, L, hHCPV, hRe0, hIm⟩ :=
    isBounded_intervalIntegrable_cauchyPV_of_interior_crossings_uIcc h_imm h_interior hγ_lip
  have hwind : windingNumber γ a b s = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L :=
    windingNumber_eq_of_hasCauchyPVAt hHCPV
  have hRe : L.re = 0 := by rw [hRe0, hclosed, sub_self]
  rw [hwind, ← Complex.re_add_im L, hRe, hIm]
  push_cast
  field_simp
  ring

end TauCeti.Contour

end
