/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
public import TauCeti.Analysis.Complex.Conformal.BlaschkeProduct
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Order.Interval.Set.Infinite
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.Poisson.Basic
import TauCeti.Analysis.Complex.Poisson.Logarithm
import TauCeti.Analysis.Complex.RadialUniqueness
import TauCeti.Analysis.Meromorphic.Order

/-!
# Nevanlinna's quotient representation and its optimality

Given a function `g : ℂ → ℂ` analytic on a neighbourhood of a closed disc `closedBall 0 R`,
Nevanlinna's quotient representation expresses `g` as a quotient `f₁ / h` of bounded analytic
functions near `closedBall 0 R` normalized by `h 0 = 1`, controlling both `Real.log ‖h z‖` and
`Real.log ‖h z * g z‖` on the disc in terms of the Nevanlinna proximity function
`m(R, g) = ValueDistribution.proximity g ⊤ R = circleAverage (Real.posLog ‖g ·‖) 0 R`.

The construction proceeds in three steps:

1. **Blaschke factorization on a zero-free circle**
   (`AnalyticOnNhd.exists_blaschkeProduct_div_mul_eq`).
   When `g` is analytic on `closedBall 0 r` (`0 < r`) and has no zeros on `sphere 0 r`, Mathlib's
   extended canonical decomposition `MeromorphicOn.exists_ecanonicalDecomp` and the reciprocal
   identity `TauCeti.blaschkeFactor_div_eq_inv_canonicalFactor` write
   `g z = blaschkeProduct a n (z / r) * G z` throughout `closedBall 0 r`, with interior parameters
   `‖a i‖ < 1` and `G` analytic and zero-free on `closedBall 0 r`.
2. **The radius-`r` quotient multiplier (`TauCeti.quotientMultiplier`).**
   Setting
   `quotientMultiplier g r z = exp (m(r, g) - circleAverage (w ↦ H(z, w) • log⁺ ‖g w‖) 0 r)`,
   where `H(z, w) = herglotzRieszKernel 0 z w`, gives a zero-free function analytic off
   `sphere 0 |r|` with `quotientMultiplier g r 0 = 1` (`r ≠ 0`). Combining the exponentiated
   Herglotz formula for `G` with `log ‖g‖ = log⁺ ‖g‖ - log⁺ ‖g‖⁻¹` yields the complex product
   identity `AnalyticOnNhd.quotientMultiplier_mul_of_norm_eq` (exhibiting the unimodular centre
   phase `G 0 / ‖G 0‖`) and the interior bounds
   `Real.log ‖quotientMultiplier g r z‖ ≤ m(r, g)` and
   `Real.log ‖quotientMultiplier g r z * g z‖ ≤ m(r, g)` for `z ∈ ball 0 r`.
3. **Radial smoothing across boundary zeros (`AnalyticOnNhd.exists_log_norm_le_proximity_add`).**
   When `g` has zeros on `sphere 0 R` (for instance `g z = z - 1` at `R = 1`), the zero-free
   Herglotz formula does not apply on `closedBall 0 R` directly. Extending `g` to a slightly larger
   open disc, choosing `r > R` avoiding the finitely many zeros of `g` there, and using continuity
   of `r ↦ m(r, g)` (`AnalyticOnNhd.continuousAt_proximity_top`) yields `h` analytic near
   `closedBall 0 R` with `h 0 = 1` and both `Real.log ‖h z‖` and `Real.log ‖h z * g z‖` bounded by
   `m(R, g) + ε` on `closedBall 0 R`.

Conversely, Jensen's inequality at `h 0 = 1` together with the almost-everywhere identity
`log ‖h z‖ + log⁺ ‖g z‖ = max (log ‖h z‖) (log ‖h z * g z‖)` off the isolated zeros of `h` and `g`
on `sphere 0 R` shows that no multiplier `h` with `h 0 = 1` can improve upon `m(R, g)`
(`AnalyticOnNhd.proximity_top_le_max_sSup_log_norm`), identifying `m(R, g)` as the infimum over
all normalized multipliers (`AnalyticOnNhd.sInf_max_sSup_log_norm_eq_proximity_top`).

## Main definitions

* `TauCeti.quotientMultiplier g r`: Nevanlinna's radius-`r` quotient multiplier
  `z ↦ exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖) 0 r)`.

## Main results

* `TauCeti.blaschkeFactor_div_eq_inv_canonicalFactor` and
  `TauCeti.analyticOnNhd_blaschkeProduct_div`: for `u ∈ ball 0 r`,
  `blaschkeFactor (u / r) (z / r) = (canonicalFactor r u z)⁻¹`, and rescaled Blaschke products are
  analytic near `closedBall 0 r`.
* `AnalyticOnNhd.exists_blaschkeProduct_div_mul_eq`: Blaschke factorization on `closedBall 0 r`
  when `g` has no zeros on `sphere 0 r`.
* `AnalyticOnNhd.quotientMultiplier_mul_of_norm_eq` and
  `AnalyticOnNhd.log_norm_quotientMultiplier_mul_le_proximity`: the complex product identity (with
  centre phase `G 0 / ‖G 0‖`) and interior logarithmic bound for `quotientMultiplier g r * g`.
* `AnalyticOnNhd.continuousAt_proximity_top` and
  `AnalyticOnNhd.exists_gt_log_norm_quotientMultiplier_le_proximity_add`: continuity of
  `ValueDistribution.proximity g ⊤` at `R ≥ 0` and radial smoothing of `quotientMultiplier` across
  boundary zeros.
* `AnalyticOnNhd.exists_log_norm_le_proximity_add` and
  `AnalyticOnNhd.exists_max_sSup_log_norm_le_proximity_add`: Nevanlinna's quotient representation.
* `AnalyticOnNhd.log_norm_le_circleAverage_log_norm`,
  `AnalyticOnNhd.proximity_top_le_of_forall_mem_sphere_log_norm_le`,
  `AnalyticOnNhd.proximity_top_le_max_sSup_log_norm`, and
  `AnalyticOnNhd.sInf_max_sSup_log_norm_eq_proximity_top`: optimality of the quotient bound and
  variational characterization of `m(R, g)`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), Lemma 2.3.1 and Remark 2.3.3 (pp. 639–641).
* R. Nevanlinna, *Analytic Functions*, Grundlehren der mathematischen Wissenschaften **162**,
  Springer (1970), Chapter VI.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology
open scoped ComplexConjugate

namespace TauCeti

/-! ### Rescaled Blaschke factors and Nevanlinna's quotient multiplier -/

/-- For an interior parameter `u ∈ ball 0 r` (`0 < r`), the rescaled Blaschke factor
`z ↦ blaschkeFactor (u / r) (z / r)` is the reciprocal of Mathlib's canonical factor
`Complex.canonicalFactor r u`. -/
lemma blaschkeFactor_div_eq_inv_canonicalFactor {u : ℂ} {r : ℝ} (hu : u ∈ ball 0 r) (z : ℂ) :
    blaschkeFactor (u / r) (z / r) = (canonicalFactor r u z)⁻¹ := by
  have hr : 0 < r := pos_of_mem_ball hu
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hur : ‖u / r‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr]
    exact mem_ball_zero_iff.mp hu
  have hnum : (r : ℂ) ^ 2 * (z / r - u / r) = r * (z - u) := by field_simp
  have hden : (r : ℂ) ^ 2 * (1 - conj (u / r) * (z / r)) = r ^ 2 - conj u * z := by
    rw [map_div₀, conj_ofReal]
    field_simp
  rw [blaschkeFactor_of_norm_lt_one hur, canonicalFactor_apply, inv_div,
    ← mul_div_mul_left _ _ (pow_ne_zero 2 hr0), hnum, hden]

/-- For `0 < r`, the rescaled Blaschke product `z ↦ blaschkeProduct a n (z / r)` is analytic on a
neighbourhood of `closedBall 0 r`. -/
lemma analyticOnNhd_blaschkeProduct_div {ι : Type*} [Fintype ι] (a : ι → ℂ) (n : ι → ℕ)
    {r : ℝ} (hr : 0 < r) :
    AnalyticOnNhd ℂ (fun z ↦ blaschkeProduct a n (z / r)) (closedBall 0 r) := by
  intro z hz
  have hzr : z / r ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_le_one hr]
    exact mem_closedBall_zero_iff.mp hz
  have hdiv_an : AnalyticAt ℂ (fun w : ℂ ↦ w / r) z := by
    fun_prop (disch := exact Complex.ofReal_ne_zero.mpr hr.ne')
  exact (analyticOnNhd_blaschkeProduct a n (z / r) hzr).fun_comp
    (f := fun w : ℂ ↦ w / r) hdiv_an

/-- **Nevanlinna's quotient multiplier** on the disc of radius `r`:
`quotientMultiplier g r z =`
`exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖) 0 r)`,
where `m(r, g) = ValueDistribution.proximity g ⊤ r`. -/
noncomputable def quotientMultiplier (g : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
    circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r)

/-- Defining formula for `TauCeti.quotientMultiplier`. -/
lemma quotientMultiplier_apply (g : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    quotientMultiplier g r z =
      Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r) :=
  (rfl)

/-- The quotient multiplier is nowhere zero. -/
@[simp]
lemma quotientMultiplier_ne_zero (g : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    quotientMultiplier g r z ≠ 0 :=
  Complex.exp_ne_zero _

/-- For a constant `c` of norm at most `1`, `log⁺ ‖c‖ = 0` and the quotient multiplier is `1`. -/
lemma quotientMultiplier_const_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (r : ℝ) (z : ℂ) :
    quotientMultiplier (fun _ ↦ c) r z = 1 := by
  have hlog : Real.posLog ‖c‖ = 0 := (Real.posLog_eq_zero_iff ‖c‖).mpr (by simpa using hc)
  simp [quotientMultiplier_apply, hlog, circleAverage_const]

@[simp]
lemma quotientMultiplier_zero_left (r : ℝ) (z : ℂ) :
    quotientMultiplier 0 r z = 1 := by
  rw [Pi.zero_def]
  exact quotientMultiplier_const_of_norm_le_one (by norm_num) r z

@[simp]
lemma quotientMultiplier_one_left (r : ℝ) (z : ℂ) :
    quotientMultiplier 1 r z = 1 := by
  rw [Pi.one_def]
  exact quotientMultiplier_const_of_norm_le_one (by norm_num) r z

/-- For any nonzero radius `r`, the quotient multiplier is normalized by `h_r(0) = 1`. -/
@[simp]
lemma quotientMultiplier_apply_zero (g : ℂ → ℂ) {r : ℝ} (hr : r ≠ 0) :
    quotientMultiplier g r 0 = 1 := by
  have hsphere : EqOn (fun w ↦ herglotzRieszKernel 0 0 w • (Real.posLog ‖g w‖ : ℂ))
      (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) (sphere 0 |r|) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hw
      exact norm_ne_zero_iff.mp (hw.trans_ne (abs_ne_zero.mpr hr))
    simp [herglotzRieszKernel_def, div_self hw0]
  have havg : circleAverage (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) 0 r =
      (ValueDistribution.proximity g ⊤ r : ℂ) := by
    simp [ValueDistribution.proximity_top, circleAverage_def, real_smul,
      intervalIntegral.integral_ofReal]
  rw [quotientMultiplier_apply, circleAverage_congr_sphere hsphere, havg, sub_self,
    Complex.exp_zero]

/-- When `log⁺ ‖g‖` is circle-integrable on `sphere 0 |r|`, `quotientMultiplier g r` is analytic on
the complement of `sphere 0 |r|` (in particular on `ball 0 |r|`). -/
lemma analyticOnNhd_quotientMultiplier {g : ℂ → ℂ} {r : ℝ}
    (hg : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r) :
    AnalyticOnNhd ℂ (quotientMultiplier g r) (sphere 0 |r|)ᶜ := by
  have hg' : CircleIntegrable (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) 0 r := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  intro z hz
  exact (analyticAt_const.sub
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hg' z hz)).cexp'

/-- When `log⁺ ‖g‖` is circle-integrable on `sphere 0 |r|`, nonnegativity of the Poisson kernel and
of `log⁺ ‖g‖` bounds `Real.log ‖quotientMultiplier g r z‖` by `ValueDistribution.proximity g ⊤ r`
for every `z ∈ ball 0 r`. -/
lemma log_norm_quotientMultiplier_le_proximity {g : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hg : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r) (hz : z ∈ ball 0 r) :
    Real.log ‖quotientMultiplier g r z‖ ≤ ValueDistribution.proximity g ⊤ r := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hz_not : z ∉ sphere (0 : ℂ) |r| := by
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm]
    exact (mem_ball_zero_iff.mp hz).ne
  rw [quotientMultiplier_apply, Complex.norm_exp, Real.log_exp, Complex.sub_re, Complex.ofReal_re,
    re_circleAverage_herglotzRieszKernel_smul hg hz_not, ← poissonKernel_eq_re_herglotzRieszKernel]
  have hnonneg : 0 ≤ circleAverage (poissonKernel 0 z • fun w ↦ Real.posLog ‖g w‖) 0 r := by
    refine Real.circleAverage_nonneg_of_nonneg fun w hw ↦ ?_
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm] at hw
    have hzw : ‖z - 0‖ ≤ ‖w - 0‖ := by
      simpa [hw] using (mem_ball_zero_iff.mp hz).le
    exact mul_nonneg (poissonKernel_nonneg hzw) Real.posLog_nonneg
  linarith

end TauCeti

namespace AnalyticOnNhd

/-! ### Blaschke factorization on a disc and complex product identity -/

/-- **Blaschke factorization on a disc of radius `r`.** If `g` is analytic on a neighbourhood of
`closedBall 0 r` (`0 < r`) and has no zeros on `sphere 0 r`, then `g` factors on `closedBall 0 r`
as `g z = blaschkeProduct a n (z / r) * G z`, where `a` is a finite family of interior parameters
(`‖a i‖ < 1`) and `G` is analytic and zero-free on `closedBall 0 r`. -/
theorem exists_blaschkeProduct_div_mul_eq {g : ℂ → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hr : 0 < r) (hs : ∀ w ∈ sphere 0 r, g w ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (n : ι → ℕ) (G : ℂ → ℂ),
      (∀ i, ‖a i‖ < 1) ∧ AnalyticOnNhd ℂ G (closedBall 0 r) ∧
      (∀ z ∈ closedBall 0 r, G z ≠ 0) ∧
      ∀ z ∈ closedBall 0 r, g z = TauCeti.blaschkeProduct a n (z / r) * G z := by
  classical
  have hord : ∀ u : closedBall (0 : ℂ) r, meromorphicOrderAt g u ≠ ⊤ := fun u ↦
    hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hs u.2
  obtain ⟨G, D⟩ := hg.meromorphicOn.exists_ecanonicalDecomp hord
  have hdiv_sphere : ∀ v : ℂ, MeromorphicOn.divisor g (sphere 0 r) v = 0 := fun v ↦ by
    by_cases hv : v ∈ sphere 0 r
    · simp [MeromorphicOn.divisor_apply (hg.meromorphicOn.mono_set sphere_subset_closedBall) hv,
        (hg v (sphere_subset_closedBall hv)).meromorphicOrderAt_eq,
        (hg v (sphere_subset_closedBall hv)).analyticOrderAt_eq_zero.mpr (hs v hv)]
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hv
  set d := MeromorphicOn.divisor g (ball 0 r) with hd_def
  have hd_fin : d.support.Finite := hg.meromorphicOn.divisor_ball_support_finite
  let s : Finset ℂ := hd_fin.toFinset
  have hs_ball : ∀ i : s, (i : ℂ) ∈ ball 0 r := fun i ↦
    d.supportWithinDomain (hd_fin.mem_toFinset.mp i.2)
  have hd_nonneg : ∀ u : ℂ, 0 ≤ d u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hg.mono ball_subset_closedBall)
  let a : s → ℂ := fun i ↦ (i : ℂ) / r
  let n : s → ℕ := fun i ↦ (d i).toNat
  have ha : ∀ i : s, ‖a i‖ < 1 := fun i ↦ by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr]
    exact mem_ball_zero_iff.mp (hs_ball i)
  -- Identify the product of reciprocal canonical factors with the rescaled Blaschke product.
  have hprod : ∀ z : ℂ, (∏ᶠ u, canonicalFactor r u ^ (-d u)) z =
      TauCeti.blaschkeProduct a n (z / r) := by
    have hmul_sub : (fun u ↦ canonicalFactor r u ^ (-d u)).mulSupport ⊆ (s : Set ℂ) := by
      intro u hu
      rw [Finset.mem_coe, hd_fin.mem_toFinset, Function.mem_support]
      exact fun hdu ↦ hu (by simp [hdu])
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset _ hmul_sub, Finset.prod_apply,
      TauCeti.blaschkeProduct_apply, ← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hdi : (n i : ℤ) = d i := Int.toNat_of_nonneg (hd_nonneg i)
    simp only [a, ← hdi, zpow_neg, zpow_natCast, ← inv_pow, Pi.pow_apply,
      TauCeti.blaschkeFactor_div_eq_inv_canonicalFactor (hs_ball i) z]
  refine ⟨s, inferInstance, a, n, G, ha, D.analyticOnNhd, D.ne_zero, ?_⟩
  have hB_an := (TauCeti.analyticOnNhd_blaschkeProduct_div a n hr).mul D.analyticOnNhd
  have h0_mem : (0 : ℂ) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have hfreq : ∃ᶠ x in 𝓝[≠] (0 : ℂ), g x = TauCeti.blaschkeProduct a n (x / r) * G x := by
    refine Eventually.frequently ?_
    filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp D.eventuallyEq 0 h0_mem,
      nhdsWithin_le_nhds (closedBall_mem_nhds 0 hr)] with x hx hxU
    have hx' := hx.resolve_right (not_not_intro hxU)
    rw [Set.mem_ofPred_eq] at hx'
    simpa only [hdiv_sphere, zpow_zero, finprod_one, mul_one, smul_eq_mul, Pi.mul_apply,
      ← hd_def, hprod x] using hx'
  exact fun z hz ↦ hg.eqOn_of_preconnected_of_frequently_eq hB_an
    (convex_closedBall 0 r).isPreconnected h0_mem hfreq hz

/-- **Complex product identity for the quotient multiplier.** If `G` is analytic and zero-free near
`closedBall 0 r` and `‖g‖ = ‖G‖` on `sphere 0 r`, then for every `z ∈ ball 0 r`
`quotientMultiplier g r z * G z` equals `(G 0 / ‖G 0‖)` times
`exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖⁻¹) 0 r)`. -/
theorem quotientMultiplier_mul_of_norm_eq {g G : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r)) (hG0 : ∀ w ∈ closedBall 0 r, G w ≠ 0)
    (hgnorm : EqOn (fun w ↦ ‖g w‖) (fun w ↦ ‖G w‖) (sphere 0 r)) (hz : z ∈ ball 0 r) :
    TauCeti.quotientMultiplier g r z * G z =
      (G 0 / ‖G 0‖) * Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r) := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hz_not : z ∉ sphere (0 : ℂ) |r| := by
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm]
    exact (mem_ball_zero_iff.mp hz).ne
  have hGc : G 0 ≠ 0 := hG0 0 (mem_closedBall_self hr.le)
  have hG_norm_ne : (‖G 0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hGc)
  have hexpG := hG.exp_circleAverage_herglotzRieszKernel_smul_log_norm hG0 hz
  have hGz : G z = (G 0 / ‖G 0‖) *
      Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r) :=
    by rw [hexpG]; field_simp
  -- Split `log ‖G‖ = log⁺ ‖g‖ - log⁺ ‖g‖⁻¹` on `sphere 0 |r|`.
  have hcont_norm : ContinuousOn (fun w ↦ ‖G w‖) (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact continuous_norm.comp_continuousOn (hG.continuousOn.mono sphere_subset_closedBall)
  have hint_pos : CircleIntegrable
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r := by
    have hcont : ContinuousOn (fun w ↦ (Real.posLog ‖G w‖ : ℂ)) (sphere 0 |r|) :=
      continuous_ofReal.comp_continuousOn (continuous_posLog.comp_continuousOn hcont_norm)
    refine (hcont.circleIntegrable'.continuousOn_smul
      (continuousOn_herglotzRieszKernel_sphere hz_not)).congr ?_
    intro θ _
    have hmem : circleMap 0 r θ ∈ sphere 0 r := circleMap_mem_sphere 0 hr.le θ
    simp [hgnorm hmem]
  have hint_inv : CircleIntegrable
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r := by
    have hcont_inv : ContinuousOn (fun w ↦ ‖G w‖⁻¹) (sphere 0 |r|) :=
      hcont_norm.inv₀ fun w hw ↦
        norm_ne_zero_iff.mpr (hG0 w (sphere_subset_closedBall (abs_of_pos hr ▸ hw)))
    have hcont : ContinuousOn (fun w ↦ (Real.posLog ‖G w‖⁻¹ : ℂ)) (sphere 0 |r|) :=
      continuous_ofReal.comp_continuousOn (continuous_posLog.comp_continuousOn hcont_inv)
    refine (hcont.circleIntegrable'.continuousOn_smul
      (continuousOn_herglotzRieszKernel_sphere hz_not)).congr ?_
    intro θ _
    have hmem : circleMap 0 r θ ∈ sphere 0 r := circleMap_mem_sphere 0 hr.le θ
    simp [hgnorm hmem]
  have hsplit : circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r =
      circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r := by
    rw [← circleAverage_sub hint_pos hint_inv]
    refine circleAverage_congr_sphere fun w hw ↦ ?_
    rw [abs_of_pos hr] at hw
    have hgw : ‖G w‖ = ‖g w‖ := (hgnorm hw).symm
    simp only [Pi.sub_apply, hgw, ← Real.posLog_sub_posLog_inv, Complex.ofReal_sub, smul_sub]
  rw [hGz, TauCeti.quotientMultiplier_apply, hsplit, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- **Interior product bound for the quotient multiplier.** If `g` is analytic on a neighbourhood of
`closedBall 0 r` and has no zeros on `sphere 0 r`, then for every `z ∈ ball 0 r`
`Real.log ‖quotientMultiplier g r z * g z‖ ≤ ValueDistribution.proximity g ⊤ r`. -/
theorem log_norm_quotientMultiplier_mul_le_proximity {g : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hs : ∀ w ∈ sphere 0 r, g w ≠ 0)
    (hz : z ∈ ball 0 r) :
    Real.log ‖TauCeti.quotientMultiplier g r z * g z‖ ≤ ValueDistribution.proximity g ⊤ r := by
  have hr : 0 < r := pos_of_mem_ball hz
  obtain ⟨ι, _, a, n, G, ha, hG, hG0, hg_eq⟩ := hg.exists_blaschkeProduct_div_mul_eq hr hs
  have hgnorm : EqOn (fun w ↦ ‖g w‖) (fun w ↦ ‖G w‖) (sphere 0 r) := by
    intro w hw
    have hwr : ‖w / r‖ = 1 := by
      rw [norm_div, mem_sphere_zero_iff_norm.mp hw, Complex.norm_real, Real.norm_of_nonneg hr.le,
        div_self hr.ne']
    simp only
    rw [hg_eq w (sphere_subset_closedBall hw), norm_mul,
      TauCeti.norm_blaschkeProduct_eq_one (fun i ↦ (ha i).le) hwr, one_mul]
  have hprod : TauCeti.quotientMultiplier g r z * g z =
      TauCeti.blaschkeProduct a n (z / r) * (TauCeti.quotientMultiplier g r z * G z) := by
    rw [hg_eq z (ball_subset_closedBall hz)]
    ring
  have hB_le : ‖TauCeti.blaschkeProduct a n (z / r)‖ ≤ 1 := by
    refine TauCeti.norm_blaschkeProduct_le_one (fun i ↦ (ha i).le) ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_le_one hr]
    exact (mem_ball_zero_iff.mp hz).le
  have hphase_norm : ‖G 0 / ‖G 0‖‖ = 1 := by
    have hGc : ‖G 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hG0 0 (mem_closedBall_self hr.le))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hGc]
  have hg_abs : AnalyticOnNhd ℂ g (closedBall 0 |r|) := by rwa [abs_of_pos hr]
  have hint_inv : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖⁻¹) 0 r :=
    (hg_abs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_posLog_inv_norm
  have hz_not : z ∉ sphere (0 : ℂ) |r| := by
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm]
    exact (mem_ball_zero_iff.mp hz).ne
  have hnonneg : 0 ≤ (circleAverage
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r).re := by
    rw [re_circleAverage_herglotzRieszKernel_smul hint_inv hz_not,
      ← poissonKernel_eq_re_herglotzRieszKernel]
    refine Real.circleAverage_nonneg_of_nonneg fun w hw ↦ ?_
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm] at hw
    have hzw : ‖z - 0‖ ≤ ‖w - 0‖ := by simpa [hw] using (mem_ball_zero_iff.mp hz).le
    exact mul_nonneg (TauCeti.poissonKernel_nonneg hzw) Real.posLog_nonneg
  have hexp_le : ‖TauCeti.quotientMultiplier g r z * g z‖ ≤
      Real.exp (ValueDistribution.proximity g ⊤ r) := by
    rw [hprod, hG.quotientMultiplier_mul_of_norm_eq hG0 hgnorm hz, norm_mul, norm_mul,
      hphase_norm, one_mul, Complex.norm_exp, Complex.sub_re, Complex.ofReal_re]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) hB_le).trans
      (Real.exp_le_exp.mpr (by linarith))
  rcases (norm_nonneg (TauCeti.quotientMultiplier g r z * g z)).eq_or_lt with h0 | hpos
  · simp only [← h0, Real.log_zero]
    exact ValueDistribution.proximity_nonneg r
  · exact (Real.log_le_log hpos hexp_le).trans_eq (Real.log_exp _)

/-! ### Radial continuity of proximity and Nevanlinna's quotient representation -/

/-- If `g` is analytic on a neighbourhood of `closedBall 0 R` (`0 ≤ R`), its Nevanlinna proximity
function `ValueDistribution.proximity g ⊤` is continuous at `R` (including across boundary zeros of
`g`, since `Real.posLog ‖g ·‖` is continuous everywhere where `g` is continuous). -/
theorem continuousAt_proximity_top {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 ≤ R) :
    ContinuousAt (ValueDistribution.proximity g ⊤) R := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open
    (isOpen_analyticAt ℂ g) hg
  have hg_ball : AnalyticOnNhd ℂ g (ball 0 (R + δ)) := by
    rwa [thickening_closedBall hδ hR, add_comm] at hsub
  have hcont_Ico : ContinuousOn (ValueDistribution.proximity g ⊤) (Ico 0 (R + δ)) := by
    rw [ValueDistribution.proximity_top]
    refine ContinuousOn.circleAverage ?_ fun _ hr ↦ hr.1
    have hset : {z : ℂ | ‖z - 0‖ ∈ Ico 0 (R + δ)} = ball 0 (R + δ) := by
      ext z
      simp
    rw [hset]
    exact continuous_posLog.comp_continuousOn
      (continuous_norm.comp_continuousOn hg_ball.continuousOn)
  have heven :
      ∀ r : ℝ, ValueDistribution.proximity g ⊤ |r| = ValueDistribution.proximity g ⊤ r := by
    intro r
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg hr, ValueDistribution.proximity_even r]
  have hcont_ball : ContinuousOn (ValueDistribution.proximity g ⊤) (ball (0 : ℝ) (R + δ)) := by
    refine (hcont_Ico.comp continuous_abs.continuousOn ?_).congr fun r _ ↦ (heven r).symm
    intro r hr
    exact ⟨abs_nonneg r, by simpa [Real.norm_eq_abs] using mem_ball_zero_iff.mp hr⟩
  refine hcont_ball.continuousAt (isOpen_ball.mem_nhds ?_)
  rw [mem_ball_zero_iff, Real.norm_of_nonneg hR]
  linarith

/-- **Radial smoothing of the quotient multiplier across boundary zeros.** If `g` is analytic on a
neighbourhood of `closedBall 0 R` (`0 < R`), does not vanish identically on `closedBall 0 R`, and
`0 < ε`, there exists `r > R` such that `g` is analytic near `closedBall 0 r`, has no zeros on
`sphere 0 r`, `quotientMultiplier g r` is analytic near `closedBall 0 R`, and both
`Real.log ‖quotientMultiplier g r z‖` and `Real.log ‖quotientMultiplier g r z * g z‖` are at most
`ValueDistribution.proximity g ⊤ R + ε` on `closedBall 0 R`. -/
theorem exists_gt_log_norm_quotientMultiplier_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 < R)
    (hne : ∃ z₀ ∈ closedBall (0 : ℂ) R, g z₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > R, AnalyticOnNhd ℂ g (closedBall 0 r) ∧ (∀ w ∈ sphere (0 : ℂ) r, g w ≠ 0) ∧
      AnalyticOnNhd ℂ (TauCeti.quotientMultiplier g r) (closedBall 0 R) ∧
      ∀ z ∈ closedBall (0 : ℂ) R,
        Real.log ‖TauCeti.quotientMultiplier g r z‖ ≤ ValueDistribution.proximity g ⊤ R + ε ∧
        Real.log ‖TauCeti.quotientMultiplier g r z * g z‖ ≤
          ValueDistribution.proximity g ⊤ R + ε := by
  obtain ⟨z₀, hz₀, hgz₀⟩ := hne
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open
    (isOpen_analyticAt ℂ g) hg
  have hg_ball : AnalyticOnNhd ℂ g (ball 0 (R + δ)) := by
    rwa [thickening_closedBall hδ hR.le, add_comm] at hsub
  obtain ⟨δ₁, hδ₁, hprox⟩ :=
    Metric.continuousAt_iff.mp (hg.continuousAt_proximity_top hR.le) ε hε
  set r_max := R + min (δ / 2) δ₁
  have hR_lt : R < r_max := lt_add_of_pos_right R (lt_min (half_pos hδ) hδ₁)
  -- Finitely many zeros of `g` lie in `closedBall 0 (R + δ / 2)`; pick `r ∈ (R, r_max)` avoiding
  -- their moduli.
  have hZ_fin : {z ∈ closedBall (0 : ℂ) (R + δ / 2) | g z = 0}.Finite :=
    hg_ball.finite_setOf_mem_and_eq_zero_of_isCompact (convex_ball 0 (R + δ)).isPreconnected
      (closedBall_subset_ball (by linarith) hz₀) hgz₀
      (isCompact_closedBall 0 (R + δ / 2)) (closedBall_subset_ball (by linarith))
  obtain ⟨r, hr_mem, hr_not⟩ := ((Set.Ioo_infinite hR_lt).sdiff (hZ_fin.image norm)).nonempty
  have hr_pos : 0 < r := hR.trans hr_mem.1
  have hg_r : AnalyticOnNhd ℂ g (closedBall 0 r) :=
    hg_ball.mono (closedBall_subset_ball (by linarith [hr_mem.2, min_le_left (δ / 2) δ₁]))
  have hs_r : ∀ w ∈ sphere (0 : ℂ) r, g w ≠ 0 := fun w hw hgw ↦
    hr_not ⟨w, ⟨by rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp hw]; linarith
      [hr_mem.2, min_le_left (δ / 2) δ₁], hgw⟩, mem_sphere_zero_iff_norm.mp hw⟩
  have hg_r_abs : AnalyticOnNhd ℂ g (closedBall 0 |r|) := by rwa [abs_of_pos hr_pos]
  have hint_r : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r :=
    (hg_r_abs.continuousOn.mono sphere_subset_closedBall).circleIntegrable_posLog_norm
  have hprox_le : ValueDistribution.proximity g ⊤ r ≤ ValueDistribution.proximity g ⊤ R + ε := by
    have hdist : dist r R < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hr_mem.1)]
      linarith [hr_mem.2, min_le_right (δ / 2) δ₁]
    linarith [(abs_lt.mp (Real.dist_eq _ _ ▸ hprox hdist)).2]
  refine ⟨r, hr_mem.1, hg_r, hs_r, (TauCeti.analyticOnNhd_quotientMultiplier hint_r).mono ?_,
    fun z hz ↦ ?_⟩
  · intro z hz
    rw [mem_compl_iff, mem_sphere_zero_iff_norm, abs_of_pos hr_pos]
    exact ((mem_closedBall_zero_iff.mp hz).trans_lt hr_mem.1).ne
  · have hzr : z ∈ ball (0 : ℂ) r := closedBall_subset_ball hr_mem.1 hz
    exact ⟨(TauCeti.log_norm_quotientMultiplier_le_proximity hint_r hzr).trans hprox_le,
      (hg_r.log_norm_quotientMultiplier_mul_le_proximity hs_r hzr).trans hprox_le⟩

/-- **Nevanlinna's quotient representation** (Calegari–Dimitrov–Tang, Lemma 2.3.1).
If `g` is analytic on a neighbourhood of `closedBall 0 R` and `0 < ε`, there exists `h` analytic on
a neighbourhood of `closedBall 0 R` with `h 0 = 1` such that both `Real.log ‖h z‖` and
`Real.log ‖h z * g z‖` are at most `ValueDistribution.proximity g ⊤ R + ε` for every
`z ∈ closedBall 0 R` (and in particular for every `z ∈ sphere 0 R`). -/
theorem exists_log_norm_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) R,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ R + ε ∧
        Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ R + ε := by
  rcases lt_trichotomy R 0 with hRneg | rfl | hRpos
  · exact ⟨1, analyticOnNhd_const, rfl, fun _ hz ↦
      False.elim ((closedBall_eq_empty.mpr hRneg).subset hz)⟩
  · refine ⟨1, analyticOnNhd_const, rfl, fun z hz ↦ ?_⟩
    rw [closedBall_zero, mem_singleton_iff] at hz
    subst hz
    rw [ValueDistribution.proximity_top, circleAverage_zero]
    exact ⟨by simp; linarith [Real.posLog_nonneg (x := ‖g 0‖)],
      by simp [Real.posLog_apply]; linarith [le_max_right 0 (Real.log ‖g 0‖)]⟩
  · by_cases hall : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0
    · refine ⟨1, analyticOnNhd_const, rfl, fun z hz ↦ ?_⟩
      simp [hall z hz, add_nonneg (ValueDistribution.proximity_nonneg R) hε.le]
    · push Not at hall
      obtain ⟨r, hr, -, -, hh, hbound⟩ :=
        hg.exists_gt_log_norm_quotientMultiplier_le_proximity_add hRpos hall hε
      exact ⟨TauCeti.quotientMultiplier g r, hh,
        TauCeti.quotientMultiplier_apply_zero g (hRpos.trans hr).ne', hbound⟩

/-- Supremum form of **Nevanlinna's quotient representation** on `sphere 0 R`: if `g` is analytic on
a neighbourhood of `closedBall 0 R` (`0 ≤ R`) and `0 < ε`, some normalized analytic multiplier `h`
near `closedBall 0 R` bounds both boundary logarithmic suprema by
`ValueDistribution.proximity g ⊤ R + ε`. -/
theorem exists_max_sSup_log_norm_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
          (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R)) ≤
        ValueDistribution.proximity g ⊤ R + ε := by
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  have hne : (sphere (0 : ℂ) R).Nonempty := ⟨R, by simp [abs_of_nonneg hR]⟩
  refine ⟨h, hh, hh0, max_le ?_ ?_⟩
  · exact csSup_le (hne.image _) fun _ ⟨z, hz, hzv⟩ ↦
      hzv ▸ (hbound z (sphere_subset_closedBall hz)).1
  · exact csSup_le (hne.image _) fun _ ⟨z, hz, hzv⟩ ↦
      hzv ▸ (hbound z (sphere_subset_closedBall hz)).2

/-! ### Optimality of the quotient bound -/

/-- **Sub-mean-value inequality for `log ‖f‖`** (Jensen's inequality at a non-vanishing centre).
If `f` is analytic on a neighbourhood of `closedBall c |r|` and `f c ≠ 0`, then
`Real.log ‖f c‖ ≤ circleAverage (fun z ↦ Real.log ‖f z‖) c r`. -/
theorem log_norm_le_circleAverage_log_norm {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c |r|)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hord : analyticOrderNatAt f c = 0 := by
      by_contra hne
      exact hfc (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
    have htrail : meromorphicTrailingCoeffAt f c = f c :=
      (hf c (mem_closedBall_self (abs_nonneg r))).meromorphicTrailingCoeffAt_of_ne_zero hfc
    simpa [hord, htrail] using hf.le_circleAverage_log_norm hr

/-- If `f` and `g` are analytic on a neighbourhood of `closedBall c R` and neither vanishes
identically on `closedBall c R`, then off a discrete subset of `closedBall c R`
`log ‖f z‖ + log⁺ ‖g z‖` agrees with `max (log ‖f z‖) (log ‖f z * g z‖)`. -/
theorem eventuallyEq_codiscreteWithin_log_norm_add_posLog {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hf0 : ∃ z ∈ closedBall c R, f z ≠ 0) (hg0 : ∃ z ∈ closedBall c R, g z ≠ 0) :
    ((fun z ↦ Real.log ‖f z‖) + fun z ↦ Real.posLog ‖g z‖) =ᶠ[
      codiscreteWithin (closedBall c R)]
      fun z ↦ max (Real.log ‖f z‖) (Real.log ‖f z * g z‖) := by
  obtain ⟨z₁, hz₁, hfz₁⟩ := hf0
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp hz₁)
  have hconn : IsConnected (closedBall c R) :=
    ⟨nonempty_closedBall.mpr hR, (convex_closedBall c R).isPreconnected⟩
  have hord_f : ∀ u ∈ closedBall c R, meromorphicOrderAt f u ≠ ⊤ := fun _ hu ↦
    hf.meromorphicOrderAt_ne_top_of_exists_ne_zero hconn ⟨z₁, hz₁, hfz₁⟩ hu
  have hord_g : ∀ u ∈ closedBall c R, meromorphicOrderAt g u ≠ ⊤ := fun _ hu ↦
    hg.meromorphicOrderAt_ne_top_of_exists_ne_zero hconn hg0 hu
  filter_upwards [hf.meromorphicOn.codiscreteWithin_setOfPred_ne_zero hord_f,
    hg.meromorphicOn.codiscreteWithin_setOfPred_ne_zero hord_g] with z hzf hzg
  simp [Pi.add_apply, Real.posLog_apply, add_max,
    Real.log_mul (norm_ne_zero_iff.mpr hzf) (norm_ne_zero_iff.mpr hzg)]

/-- **Optimality of Nevanlinna's quotient bound, bound form** (Calegari–Dimitrov–Tang,
Remark 2.3.3). If `g` and `h` are analytic on a neighbourhood of `closedBall 0 R` (`0 ≤ R`) with
`1 ≤ ‖h 0‖` (in particular when `h 0 = 1`), and both `Real.log ‖h z‖ ≤ M` and
`Real.log ‖h z * g z‖ ≤ M` hold on `sphere 0 R`, then `ValueDistribution.proximity g ⊤ R ≤ M`. -/
theorem proximity_top_le_of_forall_mem_sphere_log_norm_le {g h : ℂ → ℂ} {R M : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hh : AnalyticOnNhd ℂ h (closedBall 0 R))
    (hR : 0 ≤ R) (hh0 : 1 ≤ ‖h 0‖)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖h z‖ ≤ M ∧ Real.log ‖h z * g z‖ ≤ M) :
    ValueDistribution.proximity g ⊤ R ≤ M := by
  have hh0_pos : 0 < ‖h 0‖ := zero_lt_one.trans_le hh0
  have hlog_h0 : 0 ≤ Real.log ‖h 0‖ := Real.log_nonneg hh0
  rcases hR.eq_or_lt with rfl | hRpos
  · have h0 := hM 0 (by simp)
    rw [ValueDistribution.proximity_top, circleAverage_zero, Real.posLog_apply]
    rcases eq_or_ne ‖g 0‖ 0 with hg0 | hg0
    · simp [hg0]; linarith [h0.1]
    · have hmul : Real.log ‖h 0 * g 0‖ = Real.log ‖h 0‖ + Real.log ‖g 0‖ := by
        rw [norm_mul, Real.log_mul hh0_pos.ne' hg0]
      exact max_le (by linarith [h0.1]) (by linarith [h0.2, hmul])
  · have hh_abs : AnalyticOnNhd ℂ h (closedBall 0 |R|) := by rwa [abs_of_pos hRpos]
    have hjensen : 0 ≤ circleAverage (fun z ↦ Real.log ‖h z‖) 0 R :=
      hlog_h0.trans (hh_abs.log_norm_le_circleAverage_log_norm (norm_pos_iff.mp hh0_pos))
    have hint_h : CircleIntegrable (fun z ↦ Real.log ‖h z‖) 0 R :=
      (hh_abs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    by_cases hall : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0
    · have hM0 : 0 ≤ M :=
        hjensen.trans (circleAverage_mono_on_of_le_circle hint_h fun z hz ↦
          (hM z (abs_of_pos hRpos ▸ hz)).1)
      have hprox0 : ValueDistribution.proximity g ⊤ R = 0 := by
        rw [ValueDistribution.proximity_top, circleAverage_congr_sphere (f₂ := fun _ ↦ (0 : ℝ))]
        · simp [circleAverage_const]
        · exact fun z hz ↦ by simp [hall z (sphere_subset_closedBall (abs_of_pos hRpos ▸ hz))]
      linarith
    · push Not at hall
      obtain ⟨z₀, hz₀, hgz₀⟩ := hall
      have hg_abs : AnalyticOnNhd ℂ g (closedBall 0 |R|) := by rwa [abs_of_pos hRpos]
      have hz₀' : z₀ ∈ closedBall (0 : ℂ) |R| := by rwa [abs_of_pos hRpos]
      have hcod := (hh_abs.eventuallyEq_codiscreteWithin_log_norm_add_posLog hg_abs
        ⟨0, mem_closedBall_self (abs_nonneg R), norm_pos_iff.mp hh0_pos⟩
        ⟨z₀, hz₀', hgz₀⟩).filter_mono (codiscreteWithin_mono sphere_subset_closedBall)
      have hint_g : CircleIntegrable (fun z ↦ Real.posLog ‖g z‖) 0 R :=
        (hg_abs.continuousOn.mono sphere_subset_closedBall).circleIntegrable_posLog_norm
      have hsum_le :
          circleAverage (fun z ↦ Real.log ‖h z‖) 0 R + ValueDistribution.proximity g ⊤ R ≤ M := by
        rw [ValueDistribution.proximity_top, ← circleAverage_add hint_h hint_g,
          circleAverage_congr_codiscreteWithin hcod hRpos.ne']
        exact circleAverage_mono_on_of_le_circle
          (CircleIntegrable.congr_codiscreteWithin hcod (hint_h.add hint_g)) fun z hz ↦
          max_le (hM z (abs_of_pos hRpos ▸ hz)).1 (hM z (abs_of_pos hRpos ▸ hz)).2
      linarith

/-- **Optimality of Nevanlinna's quotient bound** (Calegari–Dimitrov–Tang, Remark 2.3.3).
For `g` and `h` analytic near `closedBall 0 R` (`0 ≤ R`) with `1 ≤ ‖h 0‖` (in particular when
`h 0 = 1`), `m(R, g) ≤ max (sup_{|z|=R} log ‖h z‖) (sup_{|z|=R} log ‖h z * g z‖)`.

Because `1 ≤ ‖h 0‖` forces `sup_{|z|=R} log ‖h z‖ ≥ 0` by the maximum modulus principle, Lean's
totalized value `Real.log 0 = 0` at any boundary zero of `h` or `h * g` never alters the maximum
of the two suprema. -/
theorem proximity_top_le_max_sSup_log_norm {g h : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hh : AnalyticOnNhd ℂ h (closedBall 0 R))
    (hR : 0 ≤ R) (hh0 : 1 ≤ ‖h 0‖) :
    ValueDistribution.proximity g ⊤ R ≤
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R)) := by
  have hbdd_h : BddAbove ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R) := by
    obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : ℂ) R).image_of_continuousOn
      (continuous_posLog.comp_continuousOn (continuous_norm.comp_continuousOn
        (hh.continuousOn.mono sphere_subset_closedBall)))).bddAbove
    exact ⟨B, fun _ ⟨z, hz, hzv⟩ ↦ hzv ▸ (le_max_right 0 _).trans (hB ⟨z, hz, rfl⟩)⟩
  have hbdd_hg : BddAbove ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R) := by
    obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : ℂ) R).image_of_continuousOn
      (continuous_posLog.comp_continuousOn (continuous_norm.comp_continuousOn
        ((hh.mul hg).continuousOn.mono sphere_subset_closedBall)))).bddAbove
    exact ⟨B, fun _ ⟨z, hz, hzv⟩ ↦ hzv ▸ (le_max_right 0 _).trans (hB ⟨z, hz, rfl⟩)⟩
  refine hg.proximity_top_le_of_forall_mem_sphere_log_norm_le hh hR hh0 fun z hz ↦ ⟨?_, ?_⟩
  · exact (le_csSup hbdd_h ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  · exact (le_csSup hbdd_hg ⟨z, hz, rfl⟩).trans (le_max_right _ _)

/-- **Variational characterization of the Nevanlinna proximity function.** For `g` analytic near
`closedBall 0 R` (`0 ≤ R`), `ValueDistribution.proximity g ⊤ R` is the infimum of
`max (sup_{|z|=R} log ‖h z‖) (sup_{|z|=R} log ‖h z * g z‖)` over all `h` analytic near
`closedBall 0 R` with `h 0 = 1`. -/
theorem sInf_max_sSup_log_norm_eq_proximity_top {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 ≤ R) :
    sInf ((fun h : ℂ → ℂ ↦ max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R))) ''
      {h : ℂ → ℂ | AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1}) =
      ValueDistribution.proximity g ⊤ R := by
  set F : (ℂ → ℂ) → ℝ := fun h ↦
    max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
      (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R))
  set S : Set (ℂ → ℂ) := {h : ℂ → ℂ | AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1}
  have hne : (F '' S).Nonempty := ⟨F 1, ⟨1, ⟨analyticOnNhd_const, rfl⟩, rfl⟩⟩
  have hbdd : BddBelow (F '' S) := by
    refine ⟨ValueDistribution.proximity g ⊤ R, ?_⟩
    rintro _ ⟨h, ⟨hh, hh0⟩, rfl⟩
    exact hg.proximity_top_le_max_sSup_log_norm hh hR (by simp [hh0])
  refine le_antisymm ?_ (le_csInf hne fun _ ⟨h, ⟨hh, hh0⟩, hv⟩ ↦
    hv ▸ hg.proximity_top_le_max_sSup_log_norm hh hR (by simp [hh0]))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨h, hh, hh0, hle⟩ := hg.exists_max_sSup_log_norm_le_proximity_add hR hε
  exact (csInf_le hbdd ⟨h, ⟨hh, hh0⟩, rfl⟩).trans hle

end AnalyticOnNhd

/-! ### Non-vacuity checks

1. Specialization of `AnalyticOnNhd.exists_log_norm_le_proximity_add` to the closed unit disc and
   unit circle.
2. For `g = 1` and `h = 1` on the unit circle, both logarithmic suprema and `m(1, 1)` equal `0`.
3. For `g z = z - 1` (which vanishes on the boundary at `z = 1`), radial smoothing still produces a
   normalized analytic multiplier near `closedBall 0 1` for every `ε > 0`. -/

example {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ h 0 = 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ 1 + ε ∧
        Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ 1 + ε := by
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  exact ⟨h, hh, hh0, fun z hz ↦ hbound z (sphere_subset_closedBall hz)⟩

example :
    sSup ((fun z : ℂ ↦ Real.log ‖(1 : ℂ → ℂ) z‖) '' sphere (0 : ℂ) 1) = 0 ∧
      ValueDistribution.proximity (1 : ℂ → ℂ) ⊤ 1 = 0 := by
  have hne : (sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  have himg : (fun z : ℂ ↦ Real.log ‖(1 : ℂ → ℂ) z‖) '' sphere (0 : ℂ) 1 = {0} := by
    simp [hne.image_const]
  refine ⟨by rw [himg, csSup_singleton], ?_⟩
  rw [Pi.one_def]
  simp

example {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ h 0 = 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity (fun w ↦ w - 1) ⊤ 1 + ε ∧
        Real.log ‖h z * (z - 1)‖ ≤ ValueDistribution.proximity (fun w ↦ w - 1) ⊤ 1 + ε := by
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦ w - 1) (closedBall 0 1) :=
    analyticOnNhd_id.sub analyticOnNhd_const
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  exact ⟨h, hh, hh0, fun z hz ↦ hbound z (sphere_subset_closedBall hz)⟩
