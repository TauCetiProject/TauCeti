/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Specialisation of `ℤ_p⟦T, p/T⟧` on the open annulus `p⁻¹ < |t| < 1`

For any complete normed field extension `K` of `ℚ_p` and any point `t ∈ K` in the open annulus
`p⁻¹ < ‖t‖ < 1`, the valuation bound `‖d_m‖ ≤ p ^ min 0 m` on coefficients of `x ∈ H`
(`H = AnnularRing p`) forces `‖d_m‖ ‖t‖ ^ m ≤ ‖t‖ ^ m` for `m ≥ 0` and
`‖d_{-n}‖ ‖t‖ ^ (-n) ≤ (p ‖t‖)⁻¹ ^ n` for `n ≥ 0`, with both geometric ratios strictly less than
`1`. Thus the two-sided Laurent series `∑_{m ∈ ℤ} d_m t ^ m` converges absolutely in `K` and
defines a ring homomorphism `TauCeti.AnnularRing.eval ht : AnnularRing p →+* K` sending `T ↦ t` and
`U ↦ p / t`; when `K` is ultrametric, every element of `H` has evaluation norm at most `1`.

Because `t ≠ 0`, `eval ht` extends uniquely across `Localization.Away T` to
`TauCeti.AnnularLaurent.eval hα ht : AnnularLaurent p hα →+* K`. When `K` is ultrametric, for every
gauge radius `α ∈ (0, 1)` and every `t` in the open annulus, `AnnularLaurent.eval hα ht` is
continuous for the Tate gauge topology (`‖z‖ ≤ α ^ r` implies `‖eval z‖ ≤ ‖t‖ ^ r`); however,
whenever `α < ‖t‖` this continuous specialisation is not Lipschitz (`not_lipschitzWith_eval_of_lt`).

Over the ground field `ℚ_p` there are no points with `p⁻¹ < ‖t‖ < 1`
(`not_exists_padic_norm_mem_Ioo`), because nonzero norms in `ℚ_p` are integer powers of `p`. Over
`ℂ_p`, by contrast, rational valuations separate every nonzero series by a unique dominant term, so
the annulus evaluations are jointly injective (`eq_of_forall_eval_eq`) and prove that
`AnnularRing p` and `AnnularLaurent p hα` are integral domains of characteristic zero.

## Main definitions

* `TauCeti.AnnularRing.eval ht`: evaluation `AnnularRing p →+* K` at `t ∈ K` with
  `‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1`.
* `TauCeti.AnnularRing.evalAway ht` and `TauCeti.AnnularLaurent.eval hα ht`: extension of
  `eval ht` to `Localization.Away T` and `AnnularLaurent p hα`.

## Main results

* `TauCeti.AnnularRing.not_exists_padic_norm_mem_Ioo`: the open annulus `p⁻¹ < ‖t‖ < 1` has no
  `ℚ_p`-rational points.
* `TauCeti.AnnularRing.hasSum_eval`, `TauCeti.AnnularRing.eval_T`, `TauCeti.AnnularRing.eval_U`,
  and `TauCeti.AnnularRing.norm_eval_le_one`: basic properties of annulus evaluation on `H`.
* `TauCeti.AnnularLaurent.continuous_eval`,
  `TauCeti.AnnularLaurent.not_lipschitzWith_eval_of_lt`, and
  `TauCeti.AnnularLaurent.exists_continuous_not_lipschitzWith_eval`: every annulus specialisation
  is Tate-gauge continuous, while points with `α < ‖t‖ < 1` in `ℂ_p` give continuous
  non-Lipschitz specialisations.
* `TauCeti.AnnularRing.eq_of_forall_eval_eq`, `TauCeti.AnnularRing.instIsDomain`, and
  `TauCeti.AnnularLaurent.instIsDomain`: joint injectivity over the `ℂ_p`-annulus and the
  resulting domain instances.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology
open scoped NNReal

namespace TauCeti

namespace AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt

private theorem p_pos : (0 : ℝ) < p := zero_lt_one.trans one_lt_p

/-- The open annulus `p⁻¹ < ‖t‖ < 1` has no points in `ℚ_p`, since nonzero `p`-adic norms are
integer powers of `p`. -/
theorem not_exists_padic_norm_mem_Ioo : ¬ ∃ t : ℚ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 := by
  rintro ⟨t, hlow, hhigh⟩
  have ht0 : t ≠ 0 := norm_pos_iff.1 ((inv_pos.2 p_pos).trans hlow)
  rw [Padic.norm_eq_zpow_neg_valuation ht0] at hlow hhigh
  have h1 : (-1 : ℤ) < -t.valuation :=
    (zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))).1 (by rwa [zpow_neg_one])
  have h2 : -t.valuation < (0 : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))).1 (by rwa [zpow_zero])
  omega

section Eval

variable {K : Type*} [NormedField K] {t : K}

/-- Any point in the open annulus `p⁻¹ < ‖t‖ < 1` is nonzero. -/
theorem ne_zero_of_norm_mem_Ioo (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : t ≠ 0 :=
  norm_pos_iff.1 ((inv_pos.2 (p_pos (p := p))).trans ht.1)

private theorem inv_p_mul_norm_lt_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    ((p : ℝ) * ‖t‖)⁻¹ < 1 := by
  refine inv_lt_one_of_one_lt₀ ?_
  calc (1 : ℝ) = (p : ℝ) * (p : ℝ)⁻¹ := (mul_inv_cancel₀ (p_pos (p := p)).ne').symm
    _ < (p : ℝ) * ‖t‖ := mul_lt_mul_of_pos_left ht.1 (p_pos (p := p))

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- Termwise divisibility bound `‖d_m t ^ m‖ ≤ p ^ min 0 m * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le (x : AnnularRing p) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ (p : ℝ) ^ min 0 m * ‖t‖ ^ m := by
  rw [norm_mul, norm_padicIntAlgebraMap, norm_zpow]
  exact mul_le_mul_of_nonneg_right (x.norm_coeff_le m) (zpow_nonneg (norm_nonneg t) m)

/-- Every term of the Laurent series at `t` has norm at most `1` on the open annulus. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ 1 := by
  refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t m).trans ?_
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    rw [min_eq_left (Nat.cast_nonneg m), zpow_zero, one_mul, zpow_natCast]
    exact pow_le_one₀ (norm_nonneg t) ht.2.le
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    have hpow : (p : ℝ) ^ min (0 : ℤ) (-n) * ‖t‖ ^ (-(n : ℤ)) = (((p : ℝ) * ‖t‖)⁻¹) ^ n := by
      rw [min_eq_right (by omega), zpow_neg, zpow_natCast, zpow_neg, zpow_natCast,
        ← mul_inv, ← mul_pow, inv_pow]
    rw [hpow]
    exact pow_le_one₀ (by positivity) (inv_p_mul_norm_lt_one ht).le

/-- The norms of the Laurent series terms of `x` at `t` are summable in `ℝ`. -/
theorem summable_norm_evalTerm (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ := by
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (summable_geometric_of_lt_one (norm_nonneg t) ht.2)
    refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t n).trans_eq ?_
    rw [min_eq_left (Nat.cast_nonneg n), zpow_zero, one_mul, zpow_natCast]
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht))
    refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t (-n)).trans_eq ?_
    rw [min_eq_right (by omega), zpow_neg, zpow_natCast, zpow_neg, zpow_natCast,
      ← mul_inv, ← mul_pow, inv_pow]

variable [CompleteSpace K]

/-- The Laurent series of `x` at `t` is summable in `K`. -/
theorem summable_evalTerm (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m :=
  (summable_norm_evalTerm ht x).of_norm

/-- Specialisation `H →+* K` at a point `t` of the open annulus `p⁻¹ < ‖t‖ < 1`, sending
`∑_{m ∈ ℤ} d_m T ^ m` to `∑_{m ∈ ℤ} d_m t ^ m`. -/
def eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m
  map_zero' := by simp
  map_one' := by
    rw [tsum_eq_single 0 fun m hm ↦ by simp [coeff_one, hm]]
    simp
  map_add' x y := by
    have hcongr : (fun m : ℤ ↦ padicIntAlgebraMap p K ((x + y).coeff m) * t ^ m) =
        fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m +
          padicIntAlgebraMap p K (y.coeff m) * t ^ m := by
      ext m
      rw [coeff_add, map_add, add_mul]
    rw [hcongr, (summable_evalTerm ht x).tsum_add (summable_evalTerm ht y)]
  map_mul' x y := by
    have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
    have hprod := DiscreteConvolution.hasSum_tsum_mul_sub
      (summable_norm_evalTerm ht x) (summable_norm_evalTerm ht y)
    refine (hprod.congr_fun fun m ↦ ?_).tsum_eq
    have hterm : (fun i : ℤ ↦ (padicIntAlgebraMap p K (x.coeff i) * t ^ i) *
        (padicIntAlgebraMap p K (y.coeff (m - i)) * t ^ (m - i))) =
        fun i : ℤ ↦ padicIntAlgebraMap p K (x.coeff i * y.coeff (m - i)) * t ^ m := by
      ext i
      rw [map_mul, mul_mul_mul_comm, ← zpow_add₀ ht0, add_sub_cancel]
    rw [hterm]
    exact (((hasSum_coeff_mul x y m).map (padicIntAlgebraMap p K)
      continuous_padicIntAlgebraMap).mul_right (t ^ m)).tsum_eq.symm

theorem eval_apply (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    eval ht x = ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m := (rfl)

theorem hasSum_eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m) (eval ht x) :=
  (summable_evalTerm ht x).hasSum

@[simp]
theorem eval_algebraMap (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (c : ℤ_[p]) :
    eval ht (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c := by
  rw [eval_apply, tsum_eq_single 0 fun m hm ↦ by simp [coeff_algebraMap, hm]]
  simp

@[simp]
theorem eval_T (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht T = t := by
  rw [eval_apply, tsum_eq_single 1 fun m hm ↦ by simp [coeff_T, hm]]
  simp [coeff_T]

@[simp]
theorem eval_U (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht U = (p : K) / t := by
  rw [eval_apply, tsum_eq_single (-1) fun m hm ↦ by simp [coeff_U, hm]]
  simp [coeff_U, div_eq_mul_inv]

/-- Elements of `AnnularRing p` are bounded by `1` at every point of the open annulus in an
ultrametric extension. -/
theorem norm_eval_le_one [IsUltrametricDist K] (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) :
    ‖eval ht x‖ ≤ 1 := by
  rw [eval_apply]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one
    (norm_padicIntAlgebraMap_coeff_mul_zpow_le_one ht x)

/-- Evaluating `ofPowerSeriesT f` at `t` sums the power series `f` at `t`. -/
theorem hasSum_eval_ofPowerSeriesT (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (f : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n f) * t ^ n)
      (eval ht (ofPowerSeriesT f)) := by
  have hinj : Function.Injective ((↑) : ℕ → ℤ) := Nat.cast_injective
  have h1 : HasSum
      ((fun m : ℤ ↦ padicIntAlgebraMap p K ((ofPowerSeriesT f).coeff m) * t ^ m) ∘ ((↑) : ℕ → ℤ))
      (eval ht (ofPowerSeriesT f)) := by
    refine (hinj.hasSum_iff ?_).2 (hasSum_eval ht (ofPowerSeriesT f))
    rintro m hm
    have hneg : m < 0 := by
      by_contra! hnonneg
      lift m to ℕ using hnonneg
      exact hm ⟨m, rfl⟩
    simp [coeff_ofPowerSeriesT_of_neg f hneg]
  simpa [Function.comp_def] using h1

/-- Evaluating `ofPowerSeriesU g` at `t` sums the power series `g` at `p / t`. -/
theorem hasSum_eval_ofPowerSeriesU (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (g : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n g) * ((p : K) / t) ^ n)
      (eval ht (ofPowerSeriesU g)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ -(n : ℤ)) :=
    neg_injective.comp Nat.cast_injective
  have h1 : HasSum
      ((fun m : ℤ ↦ padicIntAlgebraMap p K ((ofPowerSeriesU g).coeff m) * t ^ m) ∘
        fun n : ℕ ↦ -(n : ℤ))
      (eval ht (ofPowerSeriesU g)) := by
    refine (hinj.hasSum_iff ?_).2 (hasSum_eval ht (ofPowerSeriesU g))
    rintro m hm
    have hpos : 0 < m := by
      by_contra! hnonpos
      exact hm ⟨(-m).toNat, by dsimp; omega⟩
    simp [coeff_ofPowerSeriesU_of_pos g hpos]
  refine h1.congr_fun fun n ↦ ?_
  simp only [Function.comp_apply]
  rw [coeff_ofPowerSeriesU_neg_natCast, map_mul, map_pow, map_natCast,
    zpow_neg, zpow_natCast, ← inv_pow, mul_right_comm, ← mul_pow, div_eq_mul_inv, mul_comm]

/-- Extension of `eval ht` to `Localization.Away (T : AnnularRing p)`. -/
def evalAway (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Localization.Away (T : AnnularRing p) →+* K :=
  IsLocalization.Away.lift (T : AnnularRing p)
    (g := eval ht) (by rw [eval_T]; exact (ne_zero_of_norm_mem_Ioo ht).isUnit)

@[simp]
theorem evalAway_algebraMap (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    evalAway ht (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p)) x) =
      eval ht x :=
  IsLocalization.Away.lift_eq _ _ x

end NormedAlgebra

end Eval

/-! ### Joint injectivity on the `ℂ_p`-annulus and integral domain structure -/

section JointInjectivity

private def valScore (x : AnnularRing p) (m : ℤ) : ℤ :=
  -2 * ((x.coeff m).valuation : ℤ) - m

private theorem valScore_le_neg_abs {x : AnnularRing p} {m : ℤ} (hm : x.coeff m ≠ 0) :
    valScore x m ≤ -|m| := by
  have hk : -(min 0 m) ≤ ((x.coeff m).valuation : ℤ) := by
    have h := x.norm_coeff_le m
    rw [PadicInt.norm_eq_zpow_neg_valuation hm,
      zpow_le_zpow_iff_right₀ (one_lt_p (p := p))] at h
    omega
  rw [valScore]
  rcases le_or_gt 0 m with h0 | h0
  · rw [abs_of_nonneg h0]
    omega
  · rw [abs_of_neg h0]
    omega

/-- For any nonzero `x : AnnularRing p`, there is a threshold `B₀` such that for every `B ≥ B₀`
and every `t ∈ ℂ_[p]` of additive valuation `B / (2 B + 1)`, the series `x(t)` has a unique
strictly dominant term and therefore `eval ht x ≠ 0`. -/
private theorem exists_forall_eval_ne_zero_of_ne_zero {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ B₀ : ℕ, ∀ ⦃B : ℕ⦄, B₀ ≤ B → ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      PadicComplex.addValuation p t = ((B : ℚ) / (2 * B + 1) : ℚ) → eval ht x ≠ 0 := by
  classical
  have hex : ∃ m₁ : ℤ, x.coeff m₁ ≠ 0 := by
    by_contra! hall
    exact hx (AnnularRing.ext (funext hall))
  obtain ⟨m₁, hm₁⟩ := hex
  set R : ℕ := m₁.natAbs + 2 * (x.coeff m₁).valuation
  let S : Finset ℤ := (Finset.Icc (-(R : ℤ)) R).filter fun m ↦ x.coeff m ≠ 0
  have hm₁S : m₁ ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ?_, hm₁⟩
    have := Int.abs_eq_natAbs m₁
    omega
  have hSne : S.Nonempty := ⟨m₁, hm₁S⟩
  let M : ℤ := S.sup' hSne (valScore x)
  let Smax : Finset ℤ := S.filter fun m ↦ valScore x m = M
  have hSmax : Smax.Nonempty := by
    obtain ⟨m, hmS, hmM⟩ := Finset.exists_mem_eq_sup' hSne (valScore x)
    exact ⟨m, Finset.mem_filter.2 ⟨hmS, hmM.symm⟩⟩
  let m₀ : ℤ := Smax.max' hSmax
  have hm₀Smax : m₀ ∈ Smax := Finset.max'_mem Smax hSmax
  have hm₀S : m₀ ∈ S := (Finset.mem_filter.1 hm₀Smax).1
  have hm₀_score : valScore x m₀ = M := (Finset.mem_filter.1 hm₀Smax).2
  have hm₀_ne : x.coeff m₀ ≠ 0 := (Finset.mem_filter.1 hm₀S).2
  have hm₀_Icc : -(R : ℤ) ≤ m₀ ∧ m₀ ≤ R := Finset.mem_Icc.1 (Finset.mem_filter.1 hm₀S).1
  have hm₀_score_ge : -(R : ℤ) ≤ valScore x m₀ := by
    have hm₁_ge : -(R : ℤ) ≤ valScore x m₁ := by
      simp only [valScore, R]
      omega
    exact hm₁_ge.trans (hm₀_score ▸ Finset.le_sup' (valScore x) hm₁S)
  refine ⟨R + 1, fun B hB t ht hval ↦ ?_⟩
  have hRB : (R : ℤ) < B := by omega
  have h2B1_pos : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
  have hnorm_t : ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_one] using
      (PadicComplex.addValuation_eq_coe_iff (p := p)).1 hval
  let f : ℤ → ℂ_[p] := fun m ↦ padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  let E : ℤ → ℤ := fun m ↦ -(((x.coeff m).valuation : ℤ) * (2 * B + 1)) - B * m
  have h2E (m : ℤ) : 2 * E m = (2 * (B : ℤ) + 1) * valScore x m + m := by
    simp only [E, valScore]
    ring
  have hnorm_eq {m : ℤ} (hm : x.coeff m ≠ 0) :
      ‖f m‖ = (p : ℝ) ^ ((E m : ℝ) / (2 * B + 1)) := by
    rw [show ‖f m‖ = ‖x.coeff m‖ * ‖t‖ ^ m by simp [f, norm_mul, norm_zpow],
      PadicInt.norm_eq_zpow_neg_valuation hm, hnorm_t, ← Real.rpow_intCast,
      ← Real.rpow_intCast (n := m), ← Real.rpow_mul p_pos.le,
      ← Real.rpow_add p_pos]
    congr 1
    simp only [E]
    push_cast
    field_simp [h2B1_pos.ne']
    ring
  have hE_lt {m : ℤ} (hm_ne : m ≠ m₀) (hm0 : x.coeff m ≠ 0) : E m ≤ E m₀ - 1 := by
    suffices h2 : 2 * E m < 2 * E m₀ by omega
    rw [h2E m, h2E m₀]
    by_cases hmIcc : -(R : ℤ) ≤ m ∧ m ≤ R
    · have hmS : m ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hmIcc, hm0⟩
      have hleM : valScore x m ≤ valScore x m₀ := hm₀_score ▸ Finset.le_sup' (valScore x) hmS
      rcases hleM.eq_or_lt with heq | hlt
      · have hmSmax : m ∈ Smax := Finset.mem_filter.2 ⟨hmS, heq.trans hm₀_score⟩
        have hmlt : m < m₀ := lt_of_le_of_ne (Finset.le_max' Smax m hmSmax) hm_ne
        rw [heq]
        linarith
      · have hle1 : valScore x m ≤ valScore x m₀ - 1 := by omega
        nlinarith [hle1, hRB, hmIcc.2, hm₀_Icc.1]
    · have habs : (R : ℤ) + 1 ≤ |m| := by
        rcases le_or_gt 0 m with h0 | h0
        · rw [abs_of_nonneg h0]; omega
        · rw [abs_of_neg h0]; omega
      have hsc : valScore x m ≤ -|m| := valScore_le_neg_abs hm0
      have hm_le_abs : m ≤ |m| := le_abs_self m
      nlinarith [hRB, hm₀_Icc.1]
  set r : ℝ := (p : ℝ) ^ (((E m₀ - 1 : ℤ) : ℝ) / (2 * B + 1))
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg p_pos.le _
  have hr_lt : r < ‖f m₀‖ := by
    rw [hnorm_eq hm₀_ne]
    refine Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p)) ?_
    exact div_lt_div_of_pos_right (by exact_mod_cast (sub_one_lt (E m₀))) h2B1_pos
  have htail_bound (m : ℤ) : ‖if m = m₀ then (0 : ℂ_[p]) else f m‖ ≤ r := by
    split_ifs with hm_eq
    · simpa using hr_nonneg
    · by_cases hm0 : x.coeff m = 0
      · simpa [f, hm0] using hr_nonneg
      · rw [hnorm_eq hm0]
        refine Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le ?_
        exact div_le_div_of_nonneg_right (by exact_mod_cast hE_lt hm_eq hm0) h2B1_pos.le
  have htail_norm : ‖∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m‖ ≤ r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr_nonneg htail_bound
  intro heval0
  have hsplit : eval ht x = f m₀ + ∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m :=
    (summable_evalTerm ht x).tsum_eq_add_tsum_ite m₀
  rw [heval0] at hsplit
  have hfeq : f m₀ = -(∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m) :=
    eq_neg_of_add_eq_zero_left hsplit.symm
  have hnorm_eq' : ‖f m₀‖ = ‖∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m‖ := by
    rw [hfeq, norm_neg]
  linarith

private theorem exists_padicComplex_addValuation_ratio (B : ℕ) (hB : 1 ≤ B) :
    ∃ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧
      PadicComplex.addValuation p t = ((B : ℚ) / (2 * B + 1) : ℚ) := by
  obtain ⟨t, htval⟩ := PadicComplex.addValuation_surjective (p := p)
    (((B : ℚ) / (2 * B + 1) : ℚ) : WithTop ℚ)
  have hnorm : ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by
    simpa [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_one] using
      (PadicComplex.addValuation_eq_coe_iff (p := p)).1 htval
  have h2B1 : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
  have hBpos : (0 : ℝ) < B := by positivity
  have hq0 : -((B : ℝ) / (2 * B + 1)) < 0 := neg_neg_of_pos (div_pos hBpos h2B1)
  have hqm1 : (-1 : ℝ) < -((B : ℝ) / (2 * B + 1)) := by
    rw [neg_lt_neg_iff, div_lt_one h2B1]
    linarith
  refine ⟨t, ⟨?_, ?_⟩, htval⟩
  · rw [hnorm]
    exact (Real.rpow_neg_one (p : ℝ)).symm.trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p)) hqm1)
  · rw [hnorm]
    exact (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p)) hq0).trans_eq
      (Real.rpow_zero (p : ℝ))

/-- **Joint injectivity of annulus evaluations over `ℂ_p`.** Two elements of `AnnularRing p`
agreeing at every point of the open annulus `p⁻¹ < ‖t‖ < 1` in `ℂ_p` are equal. -/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (h : ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1), eval ht x = eval ht y) :
    x = y := by
  by_contra hxy
  obtain ⟨B₀, hB₀⟩ := exists_forall_eval_ne_zero_of_ne_zero (sub_ne_zero.2 hxy)
  obtain ⟨t, ht, htval⟩ :=
    exists_padicComplex_addValuation_ratio (p := p) (max B₀ 1) (le_max_right _ _)
  refine hB₀ (le_max_left _ _) t ht htval ?_
  rw [map_sub, h t ht, sub_self]

instance instNoZeroDivisors : NoZeroDivisors (AnnularRing p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    by_contra! hne
    obtain ⟨Bx, hBx⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.1
    obtain ⟨By, hBy⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.2
    let B := max (max Bx By) 1
    obtain ⟨t, ht, htval⟩ :=
      exists_padicComplex_addValuation_ratio (p := p) B (le_max_right _ _)
    have hx0 : eval ht x ≠ 0 :=
      hBx ((le_max_left Bx By).trans (le_max_left _ _)) t ht htval
    have hy0 : eval ht y ≠ 0 :=
      hBy ((le_max_right Bx By).trans (le_max_left _ _)) t ht htval
    have hmul : eval ht x * eval ht y = 0 := by rw [← map_mul, hxy, map_zero]
    exact mul_ne_zero hx0 hy0 hmul

instance instIsDomain : IsDomain (AnnularRing p) :=
  NoZeroDivisors.to_isDomain _

instance instCharZero : CharZero (AnnularRing p) where
  cast_injective m n h := by
    have h0 := congr_arg (coeff · 0) h
    simp only [coeff_natCast, ite_true] at h0
    exact Nat.cast_injective h0

theorem T_ne_zero : (T : AnnularRing p) ≠ 0 := by
  intro h
  have := congr_arg (coeff · 1) h
  simp [coeff_T] at this

instance instIsDomainLocalizationAway :
    IsDomain (Localization.Away (T : AnnularRing p)) :=
  Localization.Away.isDomain (T_ne_zero (p := p))

end JointInjectivity

end AnnularRing

/-! ### Continuity and non-Lipschitz behaviour on `AnnularLaurent p hα` -/

namespace AnnularLaurent

open AnnularRing

variable {p : ℕ} [Fact p.Prime] {α : ℝ}

instance instIsDomain (hα : α ∈ Set.Ioo 0 1) : IsDomain (AnnularLaurent p hα) :=
  IsLocalization.Away.isDomain (AnnularLaurent p hα) (T_ne_zero (p := p))

instance instCharZero (hα : α ∈ Set.Ioo 0 1) : CharZero (AnnularLaurent p hα) :=
  (RingHom.charZero_iff (algebraMap_localizationAway_injective (p := p))).1 inferInstance

section Eval

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
variable {t : K}

/-- Extension of annulus evaluation `AnnularRing.eval ht` to `AnnularLaurent p hα`. -/
def eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    AnnularLaurent p hα →+* K :=
  AnnularRing.evalAway ht

@[simp]
theorem eval_algebraMap (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) :
    eval hα ht (algebraMap (AnnularRing p) (AnnularLaurent p hα) x) = AnnularRing.eval ht x :=
  evalAway_algebraMap ht x

@[simp]
theorem eval_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (z : AnnularLaurent p hα) :
    eval hβ ht (ofRadius hα hβ z) = eval hα ht z := by
  have hext : (eval hβ ht).comp (ofRadius hα hβ).toRingHom = eval hα ht := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) ?_
    ext x
    simp [RingHom.comp_apply]
  exact RingHom.congr_fun hext z

theorem eval_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    eval hα ht (unitT p hα) = t := by
  rw [val_unitT, eval_algebraMap, eval_T]

@[simp]
theorem eval_zpow_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (r : ℤ) :
    eval hα ht (((unitT p hα ^ r : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα)) = t ^ r := by
  have hnat (n : ℕ) :
      eval hα ht (((unitT p hα ^ (n : ℤ) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα)) =
        t ^ (n : ℤ) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, eval_unitT, zpow_natCast]
  rcases le_or_gt 0 r with hr | hr
  · lift r to ℕ using hr
    exact hnat r
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = -n := ⟨(-r).toNat, by omega⟩
    have hmul :
        eval hα ht (((unitT p hα ^ (-(n : ℤ)) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα)) *
          t ^ (n : ℤ) = 1 := by
      rw [← hnat n, ← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
        Units.val_one, map_one]
    exact (eq_inv_of_mul_eq_one_left hmul).trans (zpow_neg t n).symm

/-- Two-sided Laurent series representation of `AnnularLaurent.eval hα ht z`. -/
theorem hasSum_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (z : AnnularLaurent p hα) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (coeff z m) * t ^ m) (eval hα ht z) := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hval : eval hα ht z * t ^ (k : ℤ) = AnnularRing.eval ht x := by
    have := congr_arg (eval hα ht) hx
    simpa [map_mul, map_pow, eval_algebraMap, eval_T, zpow_natCast] using this
  have hz_eval : eval hα ht z = AnnularRing.eval ht x * t ^ (-(k : ℤ)) := by
    rw [← hval, mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
  rw [hz_eval]
  have hshift := (Equiv.addRight (k : ℤ)).hasSum_iff.2
    ((AnnularRing.hasSum_eval ht x).mul_right (t ^ (-(k : ℤ))))
  refine hshift.congr_fun fun m ↦ ?_
  have hcoeff : coeff z m = x.coeff (m + k) := by
    have hunit :
        (((unitT p hα ^ (k : ℤ) : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα) * z) =
          algebraMap (AnnularRing p) (AnnularLaurent p hα) x := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]
    have hm := congr_arg (fun w ↦ coeff w (m + k)) hunit
    rwa [coeff_zpow_unitT_mul, add_sub_cancel_right, coeff_algebraMap] at hm
  simp only [Function.comp_apply, Equiv.coe_addRight, hcoeff, mul_assoc, ← zpow_add₀ ht0,
    add_neg_cancel_right]

/-- When the evaluation radius `‖t‖` exceeds the chosen gauge parameter `α`, the specialisation
`eval hα ht` is not Lipschitz on `AnnularLaurent p hα`. -/
theorem not_lipschitzWith_eval_of_lt (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (hαt : α < ‖t‖) (c : ℝ≥0) :
    ¬ LipschitzWith c (eval hα ht) := by
  intro hL
  have hpow_norm (j : ℕ) : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ j‖ = α ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ← val_unitT, ← pseudoUniformizer_unit (p := p) hα,
        (pseudoUniformizer hα p).norm_mul, pseudoUniformizer_unit, val_unitT,
        norm_algebraMap_T, ih, pow_succ']
  have h1 : 1 < ‖t‖ / α := (one_lt_div hα.1).2 hαt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c : ℝ) h1
  have hdist := hL.dist_le_mul (algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n) 0
  rw [map_zero, dist_zero_right, dist_zero_right, map_pow, eval_algebraMap, eval_T,
    norm_pow, hpow_norm] at hdist
  have hdiv : (‖t‖ / α) ^ n ≤ (c : ℝ) := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hα.1 n)).2 hdist
  linarith

section Ultrametric

variable [IsUltrametricDist K]

/-- Gauge-ball bound: if `‖z‖ ≤ α ^ r` in `AnnularLaurent p hα`, then `‖eval z‖ ≤ ‖t‖ ^ r`. -/
theorem norm_eval_le_zpow_of_norm_le_zpow (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) {z : AnnularLaurent p hα} {r : ℤ} (hz : ‖z‖ ≤ α ^ r) :
    ‖eval hα ht z‖ ≤ ‖t‖ ^ r := by
  rw [norm_le_zpow_iff, mem_ringOfDefinition_iff] at hz
  obtain ⟨x, hx⟩ := hz
  have hz_eq : z =
      (((unitT p hα ^ r : (AnnularLaurent p hα)ˣ) : AnnularLaurent p hα)) *
        algebraMap (AnnularRing p) (AnnularLaurent p hα) x := by
    rw [hx, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_mul]
  rw [hz_eq, map_mul, eval_zpow_unitT, eval_algebraMap, norm_mul, norm_zpow]
  exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg t) r) (norm_eval_le_one ht x)

/-- Every annulus evaluation `AnnularLaurent p hα →+* K` into a complete ultrametric field over
`ℚ_p` is continuous for the Tate gauge topology, regardless of which gauge radius `α ∈ (0, 1)` is
fixed. -/
theorem continuous_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Continuous (eval hα ht) := by
  refine continuous_of_continuousAt_zero (eval hα ht).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε ht.2
  rw [Metric.eventually_nhds_iff]
  refine ⟨α ^ (r : ℤ), zpow_pos hα.1 _, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz ⊢
  exact (norm_eval_le_zpow_of_norm_le_zpow hα ht hz.le).trans_lt (by simpa [zpow_natCast] using hr)

end Ultrametric

end Eval

/-- For every gauge parameter `α ∈ (0, 1)`, there exists a point `t ∈ ℂ_p` in the open annulus
`p⁻¹ < ‖t‖ < 1` whose evaluation on `AnnularLaurent p hα` is continuous yet not Lipschitz for any
constant. -/
theorem exists_continuous_not_lipschitzWith_eval (hα : α ∈ Set.Ioo 0 1) :
    ∃ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      Continuous (eval hα ht) ∧ ∀ c : ℝ≥0, ¬ LipschitzWith c (eval hα ht) := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hp_pos : (0 : ℝ) < p := zero_lt_one.trans hp1
  let β : ℝ := max (p : ℝ)⁻¹ α
  have hβ_pos : 0 < β := lt_max_of_lt_right hα.1
  have hβ_lt : β < 1 := max_lt (inv_lt_one_of_one_lt₀ hp1) hα.2
  have hβ_inv : 1 < β⁻¹ := (one_lt_inv₀ hβ_pos).2 hβ_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p : ℝ) hβ_inv
  let N : ℕ := m + 2
  have hN_pos : (0 : ℝ) < N := by positivity
  have hmN : (p : ℝ) < (β⁻¹) ^ N := by
    refine hm.trans_le (pow_le_pow_right₀ hβ_inv.le ?_)
    omega
  obtain ⟨t, htval⟩ := PadicComplex.addValuation_surjective (p := p)
    (((1 : ℚ) / N : ℚ) : WithTop ℚ)
  have hnorm : ‖t‖ = (p : ℝ) ^ (-((1 : ℝ) / N)) := by
    simpa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      (PadicComplex.addValuation_eq_coe_iff (p := p)).1 htval
  have hβ_lt_t : β < ‖t‖ := by
    have hrpow : (p : ℝ) ^ ((1 : ℝ) / N) < ((β⁻¹) ^ N) ^ ((1 : ℝ) / N) :=
      Real.rpow_lt_rpow hp_pos.le hmN (div_pos zero_lt_one hN_pos)
    have hrhs : ((β⁻¹) ^ N) ^ ((1 : ℝ) / N) = β⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hβ_pos.le),
        mul_one_div_cancel hN_pos.ne', Real.rpow_one]
    rw [hrhs] at hrpow
    have hinv := inv_strictAnti₀ (Real.rpow_pos_of_pos hp_pos _) hrpow
    rwa [inv_inv, ← Real.rpow_neg hp_pos.le, ← hnorm] at hinv
  have ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 := by
    refine ⟨(le_max_left _ _).trans_lt hβ_lt_t, ?_⟩
    rw [hnorm]
    exact (Real.rpow_lt_rpow_of_exponent_lt hp1
      (neg_neg_of_pos (div_pos zero_lt_one hN_pos))).trans_eq (Real.rpow_zero (p : ℝ))
  exact ⟨t, ht, continuous_eval hα ht, not_lipschitzWith_eval_of_lt hα ht
    ((le_max_right _ _).trans_lt hβ_lt_t)⟩

end AnnularLaurent

end TauCeti
