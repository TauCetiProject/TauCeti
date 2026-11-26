/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.IteratedDeriv.ReciprocalPower
import TauCeti.Analysis.Complex.Taylor.CauchyEstimate
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Contour.MeromorphicLaurent
import TauCeti.Analysis.SpecialFunctions.Choose

/-!
# Taylor coefficients near a pole of finite order

For a holomorphic function on a disc punctured at `ρ`, subtract its finite principal part
at `ρ`. Cauchy's estimate bounds the Taylor coefficients of the holomorphic remainder.
When `ρ` lies inside the disc and away from its centre `z`, the highest-order pole term
dominates the Taylor coefficients. We use the Taylor variable `t = z - s`, so the
coefficient of degree `k` contains the sign `(-1) ^ k`.

These estimates are the pole case of Darboux's method (F. W. J. Olver, *Asymptotics and
Special Functions*, Chapter 8, §9). They give the coefficient lower bounds needed to
compare a meromorphic Laplace transform with an upper bound coming from its input.
A simple pole is the case `m = 0` of the order-`m + 1` statements.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, section 9 (Darboux's method).
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet L-functions
  (<https://github.com/leanprover-community/riemann-hypothesis>), `Deduction.landau_pole_asym` in
  `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauPoleAsym.lean`: the
  simple-pole case of the comparison bound `M / r' ^ k` and of the two lower bounds with the
  factor `1 / 2`.
-/

public section

open Filter Metric Set
open scoped Topology

namespace TauCeti.Complex

/-- The binomial normalization `(k + m).choose m` of an order-`m + 1` pole is at least one. -/
private theorem one_le_cast_choose_add (k m : ℕ) : (1 : ℝ) ≤ ((k + m).choose m : ℝ) := by
  exact_mod_cast Nat.choose_pos (m.le_add_left k)

/-- The binomial normalization `(k + m).choose m` is nonzero in `ℂ`. -/
private theorem cast_choose_add_ne_zero (k m : ℕ) : (((k + m).choose m : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_pos (m.le_add_left k)).ne'

/-- Each term of a Laurent principal part is analytic away from its pole. -/
private theorem analyticAt_laurent_term (c ρ s : ℂ) (j : ℕ) (hs : s ≠ ρ) :
    AnalyticAt ℂ (fun w ↦ c / (w - ρ) ^ (j + 1)) s :=
  analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hs))

/-- If `f` agrees near the Taylor centre with a finite principal part plus a function holomorphic
on the whole disc, subtracting the polar coefficients leaves an error bounded by `M / r' ^ k`
on any smaller circle of radius `r'`. The local equality at the centre suffices. -/
theorem exists_norm_neg_one_pow_mul_iteratedDeriv_div_factorial_sub_laurent_le_of_eventuallyEq
    {f g : ℂ → ℂ} {z ρ : ℂ} {r r' : ℝ} {n : ℕ} {c : Fin n → ℂ}
    (hg : DifferentiableOn ℂ g (ball z r))
    (heq : f =ᶠ[𝓝 z] fun s ↦ g s + ∑ i, c i / (s - ρ) ^ (i.val + 1))
    (hzρ : z ≠ ρ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * (iteratedDeriv k f z / (k.factorial : ℂ)) -
        ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / (z - ρ) ^ (k + i.val + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨M, hM⟩ := hg.exists_norm_iteratedDeriv_div_factorial_le hr' hrr
  refine ⟨M, fun k ↦ ?_⟩
  let P (s : ℂ) := ∑ i, c i / (s - ρ) ^ (i.val + 1)
  have hterm (i : Fin n) := analyticAt_laurent_term (c i) ρ z i.val hzρ
  have hP : AnalyticAt ℂ P z := Finset.analyticAt_fun_sum _ fun i _ ↦ hterm i
  have hgz := hg.analyticAt (ball_mem_nhds z (hr'.trans hrr))
  have hcoeff : (-1 : ℂ) ^ k * (iteratedDeriv k P z / k.factorial) =
      ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / (z - ρ) ^ (k + i.val + 1) := by
    rw [iteratedDeriv_fun_sum (fun i _ ↦ (hterm i).contDiffAt), Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      neg_one_pow_mul_iteratedDeriv_div_factorial_const_div_sub_pow i.val k (c i) z ρ
  have hdiff : (-1) ^ k * (iteratedDeriv k f z / (k.factorial : ℂ)) -
      ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / (z - ρ) ^ (k + i.val + 1) =
        (-1) ^ k * (iteratedDeriv k g z / (k.factorial : ℂ)) := by
    rw [heq.iteratedDeriv_eq k, iteratedDeriv_fun_add hgz.contDiffAt hP.contDiffAt, ← hcoeff]
    ring
  simpa only [hdiff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
    Complex.norm_natCast] using hM k

/-- Subtracting the contribution of a finite principal part leaves Taylor coefficients bounded
by `M / r' ^ k` on any smaller circle of radius `r'`. The coefficient `c i` multiplies the
pole term of order `i + 1`. Continuity of the remainder `g` at `ρ` suffices: off `ρ` it agrees
with `f` minus the principal part, so a pole inside the disc leaves a removable singularity. -/
theorem exists_norm_neg_one_pow_mul_iteratedDeriv_div_factorial_sub_laurent_le
    {f g : ℂ → ℂ} {z ρ : ℂ} {r r' : ℝ} {n : ℕ} {c : Fin n → ℂ}
    (hf : DifferentiableOn ℂ f (ball z r \ {ρ})) (hg : ContinuousAt g ρ)
    (heq : ∀ᶠ s in 𝓝[≠] ρ, f s = g s + ∑ i, c i / (s - ρ) ^ (i.val + 1))
    (hzρ : z ≠ ρ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * (iteratedDeriv k f z / (k.factorial : ℂ)) -
        ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / (z - ρ) ^ (k + i.val + 1)‖ ≤ M / r' ^ k := by
  let P (s : ℂ) := ∑ i, c i / (s - ρ) ^ (i.val + 1)
  have hP {s : ℂ} (hs : s ≠ ρ) : AnalyticAt ℂ P s :=
    Finset.analyticAt_fun_sum _ fun i _ ↦ analyticAt_laurent_term (c i) ρ s i.val hs
  have hfP : DifferentiableOn ℂ (fun s ↦ f s - P s) (ball z r \ {ρ}) :=
    hf.sub fun s hs ↦ (hP hs.2).differentiableAt.differentiableWithinAt
  obtain ⟨G, hG, hGeq⟩ := exists_differentiableOn_eqOn_of_analyticAt_nhdsNE
    (compl_singleton_mem_codiscreteWithin ρ) hfP (by
      rintro a ⟨ha, rfl : a = ρ⟩
      have hfg : (fun s ↦ f s - P s) =ᶠ[𝓝[≠] a] g := heq.mono fun s hs ↦ sub_eq_of_eq_add hs
      refine ⟨g, _root_.Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        ?_ hg, hfg⟩
      filter_upwards [eventually_eventually_nhdsWithin.mpr hfg,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds ha), self_mem_nhdsWithin] with s hs hsU hsρ
      rw [isOpen_compl_singleton.nhdsWithin_eq hsρ] at hs
      exact (hfP s ⟨hsU, hsρ⟩).differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds
        ⟨hsU, hsρ⟩) |>.congr_of_eventuallyEq (hs.mono fun _ h ↦ h.symm))
  refine exists_norm_neg_one_pow_mul_iteratedDeriv_div_factorial_sub_laurent_le_of_eventuallyEq
    hG ?_ hzρ hr' hrr
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds
    ⟨mem_ball_self (hr'.trans hrr), hzρ⟩] with s hs
  exact sub_eq_iff_eq_add.mp (hGeq hs)

/-- The lower pole terms vanish relative to the leading term under the Taylor coefficient
normalization for an order-`m + 1` pole. -/
private theorem tendsto_normalized_laurent_sum {m : ℕ} (c : Fin (m + 1) → ℂ) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun k : ℕ ↦ (w ^ (k + m + 1) / (↑((k + m).choose m) : ℂ)) *
      ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / w ^ (k + i.val + 1))
      atTop (𝓝 (c (Fin.last m))) := by
  have hterm (i : Fin (m + 1)) (k : ℕ) :
      w ^ (k + m + 1) / (↑((k + m).choose m) : ℂ) *
        ((↑((k + i.val).choose i.val) : ℂ) * c i / w ^ (k + i.val + 1)) =
      (c i * w ^ (m - i.val)) * ((↑((k + i.val).choose i.val) : ℂ) / ↑((k + m).choose m)) := by
    have hexp : k + m + 1 = (k + i.val + 1) + (m - i.val) := by omega
    rw [hexp, pow_add]
    have hchoose : (↑((k + m).choose m) : ℂ) ≠ 0 :=
      cast_choose_add_ne_zero k m
    field_simp [pow_ne_zero _ hw]
  have hsmall (i : Fin m) : Tendsto
      (fun k : ℕ ↦ (↑((k + i.val).choose i.val) : ℂ) / ↑((k + m).choose m)) atTop (𝓝 0) := by
    have htop : Tendsto (fun k : ℕ ↦ ((k + m).choose (m - i.val) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        ((tendsto_choose_atTop (by omega)).comp (tendsto_add_atTop_nat m))
    have hzero : Tendsto (fun k : ℕ ↦ (m.choose i.val : ℝ) / ((k + m).choose (m - i.val) : ℝ))
        atTop (𝓝 0) := htop.const_div_atTop _
    refine (_root_.Complex.continuous_ofReal.tendsto 0 |>.comp hzero).congr fun k ↦ ?_
    have him := i.isLt.le
    have he := Nat.choose_mul (n := k + m) (Nat.sub_le m i.val)
    rw [Nat.add_sub_assoc (Nat.sub_le m i.val), Nat.sub_sub_self him, Nat.choose_symm him] at he
    have he' : (↑((k + m).choose m) : ℂ) * ↑(m.choose i.val) =
        ↑((k + m).choose (m - i.val)) * ↑((k + i.val).choose i.val) := by exact_mod_cast he
    simp only [Function.comp_apply, _root_.Complex.ofReal_div, _root_.Complex.ofReal_natCast]
    refine (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
      (cast_choose_add_ne_zero k m)).2 ?_
    simpa only [mul_comm] using he'
  have hsum : Tendsto (fun k : ℕ ↦ ∑ i : Fin m, (c i.castSucc * w ^ (m - i.val)) *
      ((↑((k + i.val).choose i.val) : ℂ) / ↑((k + m).choose m))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ ↦
      (hsmall i).const_mul (c i.castSucc * w ^ (m - i.val))
  have hsum' := (tendsto_const_nhds (x := c (Fin.last m))).add hsum
  rw [add_zero] at hsum'
  refine hsum'.congr fun k ↦ ?_
  rw [Finset.mul_sum]
  simp only [hterm, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    tsub_self, pow_zero, mul_one]
  rw [div_self (cast_choose_add_ne_zero k m), mul_one, add_comm]

/-- The Taylor coefficients of `t ↦ f (z - t)` scaled by
`(z - ρ) ^ (k + m + 1) / (k + m).choose m` converge to the coefficient of the
highest pole term, of order `m + 1`. -/
theorem tendsto_normalized_iteratedDeriv_of_laurent
    {f g : ℂ → ℂ} {z ρ : ℂ} {r : ℝ} {m : ℕ} {c : Fin (m + 1) → ℂ}
    (hf : DifferentiableOn ℂ f (ball z r \ {ρ})) (hg : ContinuousAt g ρ)
    (heq : ∀ᶠ s in 𝓝[≠] ρ, f s = g s + ∑ i, c i / (s - ρ) ^ (i.val + 1))
    (hzρ : z ≠ ρ) (hd : ‖z - ρ‖ < r) :
    Tendsto (fun k : ℕ ↦ ((z - ρ) ^ (k + m + 1) / (↑((k + m).choose m) : ℂ)) *
      ((-1) ^ k * (iteratedDeriv k f z / (k.factorial : ℂ)))) atTop (𝓝 (c (Fin.last m))) := by
  obtain ⟨r', hdr', hrr⟩ := exists_between hd
  have hr' := (norm_nonneg _).trans_lt hdr'
  obtain ⟨M, hM⟩ := exists_norm_neg_one_pow_mul_iteratedDeriv_div_factorial_sub_laurent_le
    hf hg heq hzρ hr' hrr
  let S (k : ℕ) : ℂ := ∑ i, (↑((k + i.val).choose i.val) : ℂ) * c i / (z - ρ) ^ (k + i.val + 1)
  let A (k : ℕ) : ℂ := (-1) ^ k * (iteratedDeriv k f z / (k.factorial : ℂ))
  let N (k : ℕ) : ℂ := (z - ρ) ^ (k + m + 1) / (↑((k + m).choose m) : ℂ)
  have herror : Tendsto (fun k ↦ N k * (A k - S k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hgeom : Tendsto (fun k : ℕ ↦ M * ‖z - ρ‖ ^ (m + 1) * (‖z - ρ‖ / r') ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ ‖z - ρ‖ / r')
        ((div_lt_one hr').2 hdr')).const_mul (M * ‖z - ρ‖ ^ (m + 1))
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hgeom
    have hbinom := one_le_cast_choose_add k m
    calc
      ‖N k * (A k - S k)‖ ≤ ‖z - ρ‖ ^ (k + m + 1) * (M / r' ^ k) := by
        rw [norm_mul, norm_div, norm_pow, _root_.Complex.norm_natCast]
        exact mul_le_mul (div_le_self (by positivity) hbinom) (hM k) (norm_nonneg _) (by positivity)
      _ = M * ‖z - ρ‖ ^ (m + 1) * (‖z - ρ‖ / r') ^ k := by
        rw [div_pow, Nat.add_assoc k m 1, pow_add]
        ring
  have hsum := (tendsto_normalized_laurent_sum c (sub_ne_zero.mpr hzρ)).add herror
  rw [add_zero] at hsum
  refine hsum.congr fun k ↦ ?_
  -- Both summands use the same scale; their sum is the scaled Taylor coefficient.
  exact (mul_add (N k) (S k) (A k - S k)).symm.trans (by rw [add_sub_cancel])

/-- A pole of order `m + 1` inside the disc forces the absolute Taylor coefficients at its
centre to be at least `‖meromorphicTrailingCoeffAt f ρ‖ / (2 * ‖z - ρ‖ ^ (k + m + 1))`
for all sufficiently large `k`. At `z = ρ` the bound is just nonnegativity. -/
theorem eventually_le_norm_iteratedDeriv_div_factorial_of_pole
    {f : ℂ → ℂ} {z ρ : ℂ} {r : ℝ} {m : ℕ}
    (hf : DifferentiableOn ℂ f (ball z r \ {ρ}))
    (hord : meromorphicOrderAt f ρ = (-(↑(m + 1) : ℤ) : WithTop ℤ)) (hd : ‖z - ρ‖ < r) :
    ∀ᶠ k : ℕ in atTop, ‖meromorphicTrailingCoeffAt f ρ‖ / 2 / ‖z - ρ‖ ^ (k + m + 1) ≤
      ‖iteratedDeriv k f z / (k.factorial : ℂ)‖ := by
  rcases eq_or_ne z ρ with rfl | hzρ
  · exact .of_forall fun k ↦ by simpa using norm_nonneg (iteratedDeriv k f z / (k.factorial : ℂ))
  obtain ⟨c, g, hg, heq, hc⟩ :=
    Contour.exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ hord
  rcases eq_or_ne (meromorphicTrailingCoeffAt f ρ) 0 with hc0 | hc0
  · refine .of_forall fun k ↦ ?_
    simpa only [hc0, norm_zero, zero_div] using
      norm_nonneg (iteratedDeriv k f z / (k.factorial : ℂ))
  have ht := (tendsto_normalized_iteratedDeriv_of_laurent hf hg.continuousAt heq hzρ hd).norm
  rw [hc] at ht
  filter_upwards [ht.eventually_const_lt (half_lt_self (norm_pos_iff.mpr hc0))] with k hk
  simp only [norm_mul, norm_div (a := (z - ρ) ^ _), norm_pow, _root_.Complex.norm_natCast,
    norm_neg, norm_one, one_pow, one_mul] at hk
  have hchoose := one_le_cast_choose_add k m
  refine (div_le_iff₀ (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzρ)) _)).2 ?_
  calc
    ‖meromorphicTrailingCoeffAt f ρ‖ / 2 ≤ _ := hk.le
    _ ≤ ‖z - ρ‖ ^ (k + m + 1) * ‖iteratedDeriv k f z / (k.factorial : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (div_le_self (by positivity) hchoose) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- At a real pole to the left of the centre, a leading coefficient with positive real part
forces a positive lower bound on the real parts of the Taylor coefficients in the variable
`t = x - s`. No reality condition on the Laurent expansion is needed. -/
theorem eventually_le_re_neg_one_pow_mul_iteratedDeriv_div_factorial_of_pole
    {f : ℂ → ℂ} {x y r : ℝ} {m : ℕ}
    (hf : DifferentiableOn ℂ f (ball (x : ℂ) r \ {(y : ℂ)}))
    (hord : meromorphicOrderAt f y = (-(↑(m + 1) : ℤ) : WithTop ℤ))
    (hc : 0 < (meromorphicTrailingCoeffAt f y).re) (hyx : y < x) (hd : x - y < r) :
    ∀ᶠ k : ℕ in atTop, (meromorphicTrailingCoeffAt f y).re / 2 / (x - y) ^ (k + m + 1) ≤
      ((-1) ^ k * (iteratedDeriv k f x / (k.factorial : ℂ))).re := by
  obtain ⟨c, g, hg, heq, hlead⟩ :=
    Contour.exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ hord
  have hxy : (x : ℂ) ≠ y := by exact_mod_cast hyx.ne'
  have hd' : ‖(x : ℂ) - y‖ < r := by
    simpa only [← _root_.Complex.ofReal_sub, _root_.Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hyx)] using hd
  have ht := _root_.Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalized_iteratedDeriv_of_laurent hf hg.continuousAt heq hxy hd')
  rw [hlead] at ht
  filter_upwards [ht.eventually_const_lt (half_lt_self hc)] with k hk
  let A := (-1 : ℂ) ^ k * (iteratedDeriv k f x / (k.factorial : ℂ))
  have hreal : ((x : ℂ) - y) ^ (k + m + 1) / (↑((k + m).choose m) : ℂ) =
      (↑((x - y) ^ (k + m + 1) / ((k + m).choose m : ℝ)) : ℂ) := by norm_cast
  have hlt : (meromorphicTrailingCoeffAt f y).re / 2 <
      ((x - y) ^ (k + m + 1) / ((k + m).choose m : ℝ)) * A.re := by
    rw [Function.comp_apply, hreal, _root_.Complex.mul_re] at hk
    simpa only [_root_.Complex.ofReal_re, _root_.Complex.ofReal_im, zero_mul, sub_zero] using hk
  have hpos : 0 < (x - y) ^ (k + m + 1) := pow_pos (sub_pos.mpr hyx) _
  have hchoose := one_le_cast_choose_add k m
  have hA : 0 ≤ A.re := nonneg_of_mul_nonneg_right
    ((half_pos hc).le.trans hlt.le) (div_pos hpos (zero_lt_one.trans_le hchoose))
  refine (div_le_iff₀ hpos).2 ?_
  calc
    (meromorphicTrailingCoeffAt f y).re / 2 ≤ _ := hlt.le
    _ ≤ (x - y) ^ (k + m + 1) * A.re :=
      mul_le_mul_of_nonneg_right (div_le_self hpos.le hchoose) hA
    _ = _ := mul_comm _ _

end TauCeti.Complex
