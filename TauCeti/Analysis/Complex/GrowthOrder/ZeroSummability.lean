/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder.ZeroCount
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summability over zeros of an entire function of finite order

For an entire function of order at most `A` that is nonzero at the origin,
its zeros, counted with multiplicity, have summable reciprocal `p`th powers
whenever `p > 0` and `p > A`. The family is indexed by the support of
Mathlib's native divisor on the whole plane. Its integer values are
nonnegative because the function is entire.

The proof uses `TauCeti.OrderLE.isBigO_sum_divisor` at an intermediate
exponent `B < p`. On each dyadic annulus, the contribution is bounded by a
constant times `2 ^ ((B - p) * n)`. Mathlib's `summable_partition` and its
geometric-series theorem then give summability. Local finiteness of the
native divisor handles the zeros in the unit disk. No enumeration of the
zeros is required.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Filter Metric Topology
open scoped BigOperators

namespace TauCeti

private theorem dyadic_floor_bounds {r : ℝ} (hr : 1 ≤ r) :
    (2 : ℝ) ^ ⌊Real.logb 2 r⌋₊ ≤ r ∧ r < (2 : ℝ) ^ (⌊Real.logb 2 r⌋₊ + 1) := by
  have h0 : 0 < r := zero_lt_one.trans_le hr
  have hl : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · simpa only [Real.rpow_natCast] using
      (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) h0).mp (Nat.floor_le hl)
  · rw [← Real.rpow_natCast]
    apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) h0).mp
    push_cast
    exact Nat.lt_floor_add_one (Real.logb 2 r)

private theorem summable_mul_rpow_of_count_growth {ι : Type*} (r w : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hfinite : ∀ R : ℝ, {i | r i ≤ R}.Finite)
    {C B p : ℝ} (hp : 0 ≤ p) (hBp : B < p)
    (hcount : ∀ᶠ R : ℝ in atTop,
      (∑' i : {i | r i ≤ R}, w i) ≤ C * R ^ B) :
    Summable (fun i ↦ w i * (r i) ^ (-p)) := by
  classical
  let bin (i : ι) : ℕ := ⌊Real.logb 2 (r i)⌋₊
  have hb (i : ι) : (2 : ℝ) ^ bin i ≤ r i ∧ r i < (2 : ℝ) ^ (bin i + 1) :=
    dyadic_floor_bounds (hr i)
  have hbinfinite (n : ℕ) : {i | bin i = n}.Finite :=
    (hfinite ((2 : ℝ) ^ (n + 1))).subset (fun i hi ↦ by
      have hi' : bin i = n := hi
      change r i ≤ _
      simpa only [hi'] using (hb i).2.le)
  let (n : ℕ) : Fintype {i | bin i = n} := (hbinfinite n).fintype
  let (R : ℝ) : Fintype {i | r i ≤ R} := (hfinite R).fintype
  rw [summable_partition (fun i ↦ mul_nonneg (hw i) (Real.rpow_nonneg (by linarith [hr i]) _))
    (s := fun n ↦ {i | bin i = n}) (fun i ↦ ⟨bin i, rfl, fun n hn ↦ hn.symm⟩)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  let q : ℝ := 2 ^ (B - p)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hBp)
  have hgeo := (summable_geometric_of_lt_one hq0 hq1).mul_left (C * 2 ^ B)
  apply hgeo.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hcount] with n hn
  have hsum0 : 0 ≤ ∑' i : {i | bin i = n}, w i * (r i) ^ (-p) :=
    tsum_nonneg (fun i ↦ mul_nonneg (hw i) (Real.rpow_nonneg (by linarith [hr i]) _))
  rw [Real.norm_eq_abs, abs_of_nonneg hsum0]
  have hweight : (∑' i : {i | bin i = n}, w i) ≤
      ∑' i : {i | r i ≤ (2 : ℝ) ^ (n + 1)}, w i := by
    let e : {i | bin i = n} → {i | r i ≤ (2 : ℝ) ^ (n + 1)} :=
      fun i ↦ ⟨i, by
        have hi : bin i = n := i.property
        change r i ≤ _
        simpa only [hi] using (hb i).2.le⟩
    apply Summable.tsum_le_tsum_of_inj e
      (fun i j h ↦ Subtype.ext (congrArg
        (fun t : {i | r i ≤ (2 : ℝ) ^ (n + 1)} ↦ (t : ι)) h))
      (fun i _ ↦ hw i) (fun i ↦ le_rfl) Summable.of_finite Summable.of_finite
  have hscale : ((2 : ℝ) ^ (n + 1)) ^ B * ((2 : ℝ) ^ n) ^ (-p) =
      2 ^ B * q ^ n := by
    dsimp only [q]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑' i : {i | bin i = n}, w i * ((2 : ℝ) ^ n) ^ (-p) := by
      apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
      intro i
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp)
      have hi : bin i = n := i.property
      simpa only [hi] using (hb i).1
    _ = (∑' i : {i | bin i = n}, w i) * ((2 : ℝ) ^ n) ^ (-p) := tsum_mul_right
    _ ≤ (C * ((2 : ℝ) ^ (n + 1)) ^ B) * ((2 : ℝ) ^ n) ^ (-p) :=
      mul_le_mul_of_nonneg_right (hweight.trans hn) (by positivity)
    _ = (C * 2 ^ B) * q ^ n := by rw [mul_assoc, hscale]; ring

private theorem finite_divisor_norm_sublevel (f : ℂ → ℂ) (R : ℝ) :
    {ρ : (MeromorphicOn.divisor f Set.univ).support | ‖(ρ : ℂ)‖ ≤ R}.Finite := by
  let d := MeromorphicOn.divisor f Set.univ
  have hd := LocallyFiniteSupport.finite_inter_support_of_isCompact
    (Function.locallyFinsupp.locallyFiniteSupport d) (isCompact_closedBall 0 R)
  apply (Set.finite_image_iff (f := fun ρ : d.support ↦ (ρ : ℂ))
    Subtype.coe_injective.injOn).mp
  apply hd.subset
  rintro z ⟨ρ, hρ, rfl⟩
  have hρ' : ‖(ρ : ℂ)‖ ≤ R := hρ
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hρ', ρ.property⟩

/-- The reciprocal `p`th powers of the zeros of an entire function of order at most `A`
are summable with their divisor multiplicities when `p > 0` and `p > A`, provided the
function is nonzero at the origin. -/
theorem OrderLE.summable_divisor_mul_norm_rpow {f : ℂ → ℂ} {A p : ℝ}
    (h : OrderLE f A) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hp : 0 < p) (hAp : A < p) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      (MeromorphicOn.divisor f Set.univ ρ : ℝ) * ‖(ρ : ℂ)‖ ^ (-p)) := by
  classical
  let d := MeromorphicOn.divisor f Set.univ
  let r (ρ : d.support) : ℝ := max 1 ‖(ρ : ℂ)‖
  let w (ρ : d.support) : ℝ := d ρ
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  have hw (ρ : d.support) : 0 ≤ w ρ := by
    dsimp only [w, d]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa ρ
  have hfinite (R : ℝ) : {ρ : d.support | r ρ ≤ R}.Finite := by
    apply (finite_divisor_norm_sublevel f R).subset
    intro ρ hρ
    have hρ' : r ρ ≤ R := hρ
    change ‖(ρ : ℂ)‖ ≤ R
    exact (le_max_right _ _).trans hρ'
  let (R : ℝ) : Fintype {ρ : d.support | r ρ ≤ R} := (hfinite R).fintype
  have hcompare (R : ℝ) : (∑' ρ : {ρ : d.support | r ρ ≤ R}, w ρ) ≤
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) := by
    let D := MeromorphicOn.divisor f (closedBall 0 R)
    have hD : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall 0 R)
    have hcast : Function.HasFiniteSupport (fun z ↦ (D z : ℝ)) := by
      apply hD.subset
      intro z hz
      change (D z : ℝ) ≠ 0 at hz
      change D z ≠ 0
      exact fun hzero ↦ hz (by rw [hzero, Int.cast_zero])
    have hball : AnalyticOnNhd ℂ f (closedBall 0 R) := fun z _ ↦ hf.analyticAt z
    let e : {ρ : d.support | r ρ ≤ R} → ℂ := fun ρ ↦ (ρ.val : ℂ)
    have hde (ρ : {ρ : d.support | r ρ ≤ R}) : D (e ρ) = d ρ := by
      have hρ : ‖e ρ‖ ≤ R := (le_max_right _ _).trans ρ.property
      rw [MeromorphicOn.divisor_apply hball.meromorphicOn
        (by simpa only [mem_closedBall, dist_zero_right] using hρ),
        MeromorphicOn.divisor_apply hfa.meromorphicOn (Set.mem_univ _)]
    calc
      _ ≤ ∑' z, (D z : ℝ) := by
        apply Summable.tsum_le_tsum_of_inj e
          (fun ρ σ hρσ ↦ Subtype.ext (Subtype.ext hρσ))
          (fun z _ ↦ by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hball z)
          (fun ρ ↦ by dsimp only [w]; rw [hde ρ]) Summable.of_finite
          (summable_of_hasFiniteSupport hcast)
      _ = ∑ᶠ z, (D z : ℝ) := tsum_eq_finsum hcast
      _ = ((∑ᶠ z, D z : ℤ) : ℝ) := (map_finsum (Int.castRingHom ℝ) hD).symm
  let B : ℝ := (max A 0 + p) / 2
  have hAB : A < B := by have := le_max_left A 0; have := max_lt hAp hp; dsimp [B]; linarith
  have hBp : B < p := by have := max_lt hAp hp; dsimp [B]; linarith
  obtain ⟨C, _, hC⟩ := (h.isBigO_sum_divisor hf hf0 hAB).exists_pos
  have hcount : ∀ᶠ R : ℝ in atTop, (∑' ρ : {ρ : d.support | r ρ ≤ R}, w ρ) ≤ C * R ^ B := by
    filter_upwards [hC.bound, eventually_ge_atTop (0 : ℝ)] with R hR hR0
    have hn : 0 ≤ ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) := by
      exact_mod_cast finsum_nonneg
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ ↦ hf.analyticAt z))
    apply (hcompare R).trans
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
      abs_of_nonneg (Real.rpow_nonneg hR0 B)] using hR
  have hs := summable_mul_rpow_of_count_growth r w (fun ρ ↦ le_max_left _ _) hw hfinite
    hp.le hBp hcount
  apply hs.congr_cofinite
  filter_upwards [(finite_divisor_norm_sublevel f 1).eventually_cofinite_notMem] with ρ hρ
  have hρnorm : 1 ≤ ‖(ρ : ℂ)‖ := le_of_lt (lt_of_not_ge hρ)
  simp only [r, w, d, max_eq_right hρnorm]

end TauCeti
