/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.AnnularRing.Presentation
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Specialisation of `ℤ_p⟦T, p/T⟧` on the open annulus `p⁻¹ < |t| < 1`

For a complete normed field extension `K` of `ℚ_p` (ultrametric via
`IsUltrametricDist.of_normedAlgebra`) and `t ∈ K` with `p⁻¹ < ‖t‖ < 1`, `∑ d_m t ^ m` defines
`TauCeti.AnnularRing.eval ht : AnnularRing p →+* K` (`T ↦ t`, `U ↦ p / t`), bounded by `1`.
Extending across `Localization.Away T` gives `TauCeti.AnnularLaurent.eval hα ht`, continuous for
`α ∈ (0, 1)`, yet not Lipschitz when `α < ‖t‖`. While `ℚ_p` has no points in `(p⁻¹, 1)`
`ℂ_p`-evaluations are jointly injective (`TauCeti.AnnularRing.eq_of_forall_eval_eq`,
`mem_span_iff_forall_eval_annulus`), making `AnnularRing p` and `AnnularLaurent p hα` domains.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology
open scoped NNReal

namespace TauCeti
namespace AnnularRing

/-- Any element `t` whose norm lies in `(p⁻¹, 1)` is nonzero. -/
theorem ne_zero_of_norm_mem_Ioo {p : ℕ} {K : Type*} [NormedAddGroup K] {t : K}
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : t ≠ 0 :=
  norm_pos_iff.1 ((inv_nonneg.2 (Nat.cast_nonneg p)).trans_lt ht.1)

variable {p : ℕ} [Fact p.Prime]

section Eval
variable {K : Type*} [NormedField K] {t : K}

private theorem inv_p_mul_norm_lt_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    ((p : ℝ) * ‖t‖)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ <| (mul_inv_cancel₀ (p_pos (p := p)).ne').symm.trans_lt
    (mul_lt_mul_of_pos_left ht.1 (p_pos (p := p)))
omit [Fact p.Prime] in
private theorem zpow_min_neg_mul_zpow (t : K) (n : ℕ) :
    (p : ℝ) ^ min (0 : ℤ) (-n) * ‖t‖ ^ (-(n : ℤ)) = (((p : ℝ) * ‖t‖)⁻¹) ^ n := by
  rw [min_eq_right (by omega)]; simp [mul_pow]; ring

section NormedAlgebra
variable [NormedAlgebra ℚ_[p] K]

/-- Norm of a scalar-monomial product `c * t ^ m` for `c : ℤ_p`: `‖c‖ * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_mul_zpow (c : ℤ_[p]) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K c * t ^ m‖ = ‖c‖ * ‖t‖ ^ m := by
  rw [norm_mul, norm_padicIntAlgebraMap, norm_zpow]
/-- Termwise norm bound: `‖x.coeff m * t ^ m‖ ≤ p ^ min 0 m * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le (x : AnnularRing p) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ (p : ℝ) ^ min 0 m * ‖t‖ ^ m := by
  rw [norm_padicIntAlgebraMap_mul_zpow]
  exact mul_le_mul_of_nonneg_right (x.norm_coeff_le m) (zpow_nonneg (norm_nonneg t) m)
/-- On `p⁻¹ < ‖t‖ < 1`, every term `x.coeff m * t ^ m` has norm `≤ 1`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) (m : ℤ) : ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ 1 := by
  refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t m).trans ?_
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    simpa [min_eq_left (Nat.cast_nonneg m)] using pow_le_one₀ (norm_nonneg t) ht.2.le
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [zpow_min_neg_mul_zpow]; exact pow_le_one₀ (by positivity) (inv_p_mul_norm_lt_one ht).le

/-- On `p⁻¹ < ‖t‖ < 1`, `∑ ‖x.coeff m * t ^ m‖` is summable via geometric bounds. -/
theorem summable_norm_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : Summable fun m : ℤ ↦ ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ :=
  Summable.of_nat_of_neg (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by
      simpa [min_eq_left (Nat.cast_nonneg n)] using norm_padicIntAlgebraMap_coeff_mul_zpow_le x t n)
      (summable_geometric_of_lt_one (norm_nonneg t) ht.2))
    (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t (-n)).trans_eq
        (zpow_min_neg_mul_zpow t n))
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht)))

private theorem norm_evalTUTerm_eval_le (F : MvPowerSeries (Fin 2) ℤ_[p]) (d : Fin 2 →₀ ℕ) :
    ‖padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1‖ ≤
      ‖t‖ ^ d 0 * (((p : ℝ) * ‖t‖)⁻¹) ^ d 1 := by
  have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    simpa [map_natCast] using norm_padicIntAlgebraMap (K := K) (p : ℤ_[p])
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, hpK, div_eq_mul_inv, mul_inv_rev,
    mul_comm (‖t‖⁻¹), norm_padicIntAlgebraMap]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (pow_nonneg (norm_nonneg t) _) (PadicInt.norm_le_one _)) (by positivity)

variable [CompleteSpace K]

private theorem summable_evalTUTerm_eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) : Summable fun d : Fin 2 →₀ ℕ ↦
    padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1 := by
  let e : (ℕ × ℕ) ≃ (Fin 2 →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)).symm
  refine .of_norm_bounded (e.summable_iff.1 ?_) (norm_evalTUTerm_eval_le F)
  simpa [Function.comp_def, e] using
    (summable_geometric_of_lt_one (norm_nonneg t) ht.2).mul_of_nonneg
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht))
      (fun _ ↦ pow_nonneg (norm_nonneg t) _) (fun _ ↦ pow_nonneg (by positivity) _)

/-- On `p⁻¹ < ‖t‖ < 1`, `∑ x.coeff m * t ^ m` is summable in a complete extension `K / ℚ_p`. -/
theorem summable_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : Summable fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m :=
  (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x).of_norm

/-- Specialisation `AnnularRing p →+* K` at `t` (`p⁻¹ < ‖t‖ < 1`), `∑ d_m T ^ m ↦ ∑ d_m t ^ m`. -/
def eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m
  map_zero' := by simp
  map_one' := by rw [tsum_eq_single 0 fun m hm ↦ by simp [coeff_one, hm]]; simp
  map_add' x y := by
    simp_rw [coeff_add, map_add, add_mul]; exact (summable_padicIntAlgebraMap_coeff_mul_zpow
      ht x).tsum_add (summable_padicIntAlgebraMap_coeff_mul_zpow ht y)
  map_mul' x y := by
    refine ((DiscreteConvolution.hasSum_tsum_mul_sub
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x)
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht y)).congr_fun fun m ↦ ?_).tsum_eq
    refine Eq.symm ((tsum_congr fun i ↦ ?_).trans (((hasSum_coeff_mul x y m).map
      (padicIntAlgebraMap p K)
      (continuous_padicIntAlgebraMap (continuous_algebraMap ℚ_[p] K))).mul_right (t ^ m)).tsum_eq)
    rw [mul_mul_mul_comm, ← zpow_add₀ (ne_zero_of_norm_mem_Ioo ht), add_sub_cancel, ← map_mul]; rfl

theorem eval_apply (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    eval ht x = ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m := (rfl)
/-- The two-sided series `∑ x.coeff m * t ^ m` sums to `eval ht x`. -/
theorem hasSum_eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m) (eval ht x) :=
  (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).hasSum
@[simp] theorem eval_algebraMap (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (c : ℤ_[p]) :
    eval ht (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c := by
  rw [eval_apply, tsum_eq_single 0 fun m hm ↦ by simp [coeff_algebraMap, hm]]; simp
@[simp] theorem eval_T (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht T = t := by
  rw [eval_apply, tsum_eq_single 1 fun m hm ↦ by simp [coeff_T, hm]]; simp [coeff_T]
@[simp] theorem eval_U (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht U = (p : K) / t := by
  rw [eval_apply, tsum_eq_single (-1) fun m hm ↦ by simp [coeff_U, hm]]
  simp [coeff_U, div_eq_mul_inv]

/-- Every annulus evaluation satisfies `‖eval ht x‖ ≤ 1`, via ultrametricity of `K`. -/
theorem norm_eval_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    ‖eval ht x‖ ≤ 1 := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  rw [eval_apply]; exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one
    (norm_padicIntAlgebraMap_coeff_mul_zpow_le_one ht x)

/-- Evaluating `ofPowerSeriesT f` at `t` computes `∑ f_n t ^ n`. -/
theorem hasSum_eval_ofPowerSeriesT (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (f : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n f) * t ^ n)
      (eval ht (ofPowerSeriesT f)) := by
  refine ((Nat.cast_injective.hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht (ofPowerSeriesT f))).congr_fun fun n ↦ by simp
  have hneg : m < 0 := by by_contra! h0; lift m to ℕ using h0; exact hm ⟨m, rfl⟩
  simp [coeff_ofPowerSeriesT_of_neg f hneg]
/-- Evaluating `ofPowerSeriesU g` at `t` computes `∑ g_n (p / t) ^ n`. -/
theorem hasSum_eval_ofPowerSeriesU (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (g : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n g) * ((p : K) / t) ^ n)
      (eval ht (ofPowerSeriesU g)) := by
  refine (((neg_injective.comp Nat.cast_injective).hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht (ofPowerSeriesU g))).congr_fun fun n ↦ ?_
  · have hpos : 0 < m := by by_contra! h0; exact hm ⟨(-m).toNat, by dsimp; omega⟩
    simp [coeff_ofPowerSeriesU_of_pos g hpos]
  · simp [coeff_ofPowerSeriesU_neg_natCast, div_eq_mul_inv, mul_pow]; ring

/-- Evaluating `F ∈ ℤ_p⟦X_0, X_1⟧` termwise at `(t, p / t)` converges to
`eval ht (ofMvPowerSeries F)`. -/
theorem hasSum_eval_ofMvPowerSeries (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    HasSum (fun d : Fin 2 →₀ ℕ ↦
      padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1)
      (eval ht (ofMvPowerSeries F)) := by
  have hs := summable_evalTUTerm_eval ht F
  have hcomp := hs.comp_injective Finsupp.finTwoSubMinEquiv.symm.injective
  dsimp only [Function.comp_def] at hcomp; convert hs.hasSum using 1
  rw [← Equiv.tsum_eq Finsupp.finTwoSubMinEquiv.symm, hcomp.tsum_prod' hcomp.prod_factor,
    eval_apply]
  refine tsum_congr fun m ↦ ?_
  have hdiag (k : ℕ) :
      padicIntAlgebraMap p K (MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F) *
          t ^ (Finsupp.finTwoSubMinEquiv.symm (m, k)) 0 *
          ((p : K) / t) ^ (Finsupp.finTwoSubMinEquiv.symm (m, k)) 1 =
        padicIntAlgebraMap p K ((p : ℤ_[p]) ^ ((-m).toNat + k) *
          MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F) * t ^ m := by
    have hpow : t ^ (m.toNat + k) / t ^ ((-m).toNat + k) = t ^ m := by
      rw [← zpow_natCast t, ← zpow_natCast t, ← zpow_sub₀ (ne_zero_of_norm_mem_Ioo ht)]
      congr 1; omega
    rw [Finsupp.finTwoSubMinEquiv_symm_apply_zero, Finsupp.finTwoSubMinEquiv_symm_apply_one,
      div_pow, ← map_natCast (padicIntAlgebraMap p K), map_mul, map_pow, mul_assoc _ (t ^ _),
      div_eq_mul_inv, mul_left_comm (t ^ _), ← div_eq_mul_inv, hpow]; ring
  simp_rw [hdiag]; rw [coeff_ofMvPowerSeries F m]
  have hsum : Summable fun k : ℕ ↦ (p : ℤ_[p]) ^ ((-m).toNat + k) *
      MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F := by
    simpa [pow_add, mul_assoc] using (PadicInt.summable_pow_mul
      (fun k ↦ MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F)).mul_left _
  exact ((hsum.hasSum.map (padicIntAlgebraMap p K) (continuous_padicIntAlgebraMap
    (continuous_algebraMap ℚ_[p] K))).mul_right (t ^ m)).tsum_eq.symm
end NormedAlgebra
end Eval

/-! ### Joint injectivity on the `ℂ_p`-annulus and integral domain structure -/

section JointInjectivity

/-- The asymptotic score `-2 * v(d_m) - m` of the `m`-th coefficient. At radius
`‖t‖ = p ^ (-B / (2B + 1))` (for large `B`), `‖d_m t ^ m‖ = p ^ (E_B(m) / (2B + 1))` with
`2 * E_B(m) = (2B + 1) * valScore x m + m`. -/
private def valScore (x : AnnularRing p) (m : ℤ) : ℤ := -2 * ((x.coeff m).valuation : ℤ) - m

/-- The integer numerator `E_B(m)` in `‖d_m t ^ m‖ = p ^ (E_B(m) / (2B + 1))` when
`‖t‖ = p ^ (-B / (2B + 1))`. -/
private def evalExponent (x : AnnularRing p) (B : ℕ) (m : ℤ) : ℤ :=
  -(((x.coeff m).valuation : ℤ) * (2 * B + 1)) - B * m

private theorem two_mul_evalExponent (x : AnnularRing p) (B : ℕ) (m : ℤ) :
    2 * evalExponent x B m = (2 * (B : ℤ) + 1) * valScore x m + m := by
  simp only [evalExponent, valScore]; ring

private theorem evalExponent_le_sub_one {x : AnnularRing p} {B : ℕ} {m m₀ : ℤ}
    (hdom : (2 * (B : ℤ) + 1) * valScore x m + m <
      (2 * (B : ℤ) + 1) * valScore x m₀ + m₀) :
    evalExponent x B m ≤ evalExponent x B m₀ - 1 := by
  have h2 : 2 * evalExponent x B m < 2 * evalExponent x B m₀ := by
    rwa [two_mul_evalExponent, two_mul_evalExponent]
  omega

/-- Because `v(d_m) ≥ max 0 (-m)` in `AnnularRing p`, we have `valScore x m ≤ -|m|` whenever
`d_m ≠ 0`, so `valScore` drops off linearly outside any finite window. -/
private theorem valScore_le_neg_abs {x : AnnularRing p} {m : ℤ} (hm : x.coeff m ≠ 0) :
    valScore x m ≤ -|m| := by
  have h := x.norm_coeff_le m
  rw [PadicInt.norm_eq_zpow_neg_valuation hm, zpow_le_zpow_iff_right₀ (one_lt_p (p := p))] at h
  rw [valScore]; cases abs_cases m <;> omega

/-- Strategy for finding a dominant term: pick any nonzero coefficient `d_{m₁}` and set the
window radius `R = |m₁| + 2 * v(d_{m₁})`, so `valScore x m₁ ≥ -R`. Among nonzero coefficients in
`[-R, R]`, let `m₀` be the largest index attaining the maximum `valScore`. For every `B ≥ R + 1`,
`(2B + 1) * valScore x m + m` is strictly largest at `m₀`:
* inside `[-R, R]`, ties in `valScore` break in favor of `m₀` by maximality (`m < m₀`), while a
  drop of at least `1` in `valScore` outweighs `m - m₀ ≤ 2R < 2B + 1`;
* outside `[-R, R]`, `|m| ≥ R + 1` gives `valScore x m ≤ -|m| < -R ≤ valScore x m₀`, and the
  margin `(2B + 1) * (valScore x m₀ - valScore x m)` dominates `m - m₀ ≤ |m| + R`. -/
private theorem exists_dominant_index {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ (R : ℕ) (m₀ : ℤ), x.coeff m₀ ≠ 0 ∧ ∀ ⦃B : ℕ⦄, R + 1 ≤ B → ∀ ⦃m : ℤ⦄, m ≠ m₀ → x.coeff m ≠ 0 →
      (2 * (B : ℤ) + 1) * valScore x m + m < (2 * (B : ℤ) + 1) * valScore x m₀ + m₀ := by
  classical
  have ⟨m₁, hm₁⟩ : ∃ m₁ : ℤ, x.coeff m₁ ≠ 0 := Classical.byContradiction fun h ↦
    hx (AnnularRing.ext (funext <| by simpa using h))
  set R : ℕ := m₁.natAbs + 2 * (x.coeff m₁).valuation
  let S : Finset ℤ := (Finset.Icc (-(R : ℤ)) R).filter fun m ↦ x.coeff m ≠ 0
  have hm₁S : m₁ ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 (by have := Int.abs_eq_natAbs m₁; omega), hm₁⟩
  let Smax : Finset ℤ := S.filter fun m ↦ valScore x m = S.sup' ⟨m₁, hm₁S⟩ (valScore x)
  have hSmax : Smax.Nonempty := let ⟨m, hm⟩ := Finset.exists_mem_eq_sup' ⟨m₁, hm₁S⟩ (valScore x)
    ⟨m, Finset.mem_filter.2 ⟨hm.1, hm.2.symm⟩⟩
  let m₀ : ℤ := Smax.max' hSmax
  obtain ⟨hm₀S, hm₀_score⟩ := Finset.mem_filter.1 (Finset.max'_mem Smax hSmax)
  obtain ⟨hm₀_Icc, hm₀_ne⟩ := Finset.mem_filter.1 hm₀S
  rw [Finset.mem_Icc] at hm₀_Icc
  refine ⟨R, m₀, hm₀_ne, fun B hB m hm_ne hm0 ↦ ?_⟩
  have hRB : (R : ℤ) < B := by omega
  by_cases hmIcc : -(R : ℤ) ≤ m ∧ m ≤ R
  · have hmS : m ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hmIcc, hm0⟩
    rcases ((Finset.le_sup' (valScore x) hmS).trans_eq hm₀_score.symm).eq_or_lt with heq | hlt
    · have hlt_m₀ := lt_of_le_of_ne
        (Finset.le_max' Smax m (Finset.mem_filter.2 ⟨hmS, heq.trans hm₀_score⟩)) hm_ne
      rw [heq]; linarith
    · nlinarith [Int.le_sub_one_of_lt hlt, hRB, hmIcc.2, hm₀_Icc.1]
  · have habs : (R : ℤ) + 1 ≤ |m| := by cases abs_cases m <;> omega
    have hm₀_ge : -(R : ℤ) ≤ valScore x m₀ := (by dsimp [valScore, R]; omega :
      -(R : ℤ) ≤ valScore x m₁).trans (hm₀_score ▸ Finset.le_sup' (valScore x) hm₁S)
    nlinarith [valScore_le_neg_abs hm0, le_abs_self m, hRB, hm₀_Icc.1, hm₀_ge]

/-- If `x ≠ 0`, then at any sufficiently large radius `‖t‖ = p ^ (-B / (2B + 1))` the dominant
term `d_{m₀} t ^ {m₀}` strictly exceeds the ultrametric bound on the rest of the series, so
`eval ht x ≠ 0`. -/
private theorem exists_forall_eval_ne_zero_of_ne_zero {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ B₀ : ℕ, ∀ ⦃B : ℕ⦄, B₀ ≤ B → ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) → eval ht x ≠ 0 := by
  classical
  obtain ⟨R, m₀, hm₀_ne, hdom⟩ := exists_dominant_index hx
  refine ⟨R + 1, fun B hB t ht hnorm_t heval0 ↦ ?_⟩
  have h2B1_pos : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
  let f : ℤ → ℂ_[p] := fun m ↦ padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  -- Every nonzero term has norm `p ^ (evalExponent x B m / (2B + 1))`.
  have hnorm_eq {m : ℤ} (hm : x.coeff m ≠ 0) :
      ‖f m‖ = (p : ℝ) ^ ((evalExponent x B m : ℝ) / (2 * B + 1)) := by
    rw [norm_padicIntAlgebraMap_mul_zpow, PadicInt.norm_eq_zpow_neg_valuation hm, hnorm_t,
      ← Real.rpow_intCast, ← Real.rpow_intCast (n := m), ← Real.rpow_mul p_pos.le,
      ← Real.rpow_add p_pos]
    congr 1; simp only [evalExponent]; push_cast; field_simp [h2B1_pos.ne']; ring
  -- Bound the tail excluding `m₀` by `r = p ^ ((evalExponent x B m₀ - 1) / (2B + 1)) < ‖f m₀‖`.
  set r : ℝ := (p : ℝ) ^ (((evalExponent x B m₀ - 1 : ℤ) : ℝ) / (2 * B + 1))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (p_pos (p := p)).le _
  have hr_lt : r < ‖f m₀‖ := by
    rw [hnorm_eq hm₀_ne]
    exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p))
      (div_lt_div_of_pos_right (by exact_mod_cast sub_one_lt (evalExponent x B m₀)) h2B1_pos)
  have htail_norm : ‖∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m‖ ≤ r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr0 fun m ↦ by
      by_cases hm_eq : m = m₀; · simp [hm_eq, hr0]
      by_cases hm0 : x.coeff m = 0; · simp [hm_eq, f, hm0, hr0]
      rw [ite_eq_right hm_eq, hnorm_eq hm0]
      exact Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le (div_le_div_of_nonneg_right
        (by exact_mod_cast evalExponent_le_sub_one (hdom hB hm_eq hm0)) h2B1_pos.le)
  -- Since `f m₀ + tail = 0`, `‖f m₀‖ = ‖tail‖ ≤ r`, contradicting `r < ‖f m₀‖`.
  have hsplit := (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).tsum_eq_add_tsum_ite m₀
  rw [← eval_apply ht x, heval0] at hsplit
  linarith [(congr_arg norm (eq_neg_of_add_eq_zero_left hsplit.symm)).trans (norm_neg _)]

/-- For any rational `q ∈ (0, 1)`, there exists `t : ℂ_[p]` in the open annulus `(p⁻¹, 1)` with
`‖t‖ = p ^ (-q)`. -/
private theorem exists_padicComplex_norm_eq_rpow_neg {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧ ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) := by
  obtain ⟨t, ht⟩ := PadicComplex.exists_norm_eq_rpow (p := p) (-q)
  have hnorm : ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) := by simpa using ht
  have hp := one_lt_p (p := p); refine ⟨t, ⟨?_, ?_⟩, hnorm⟩
  · rw [hnorm, ← Real.rpow_neg_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp (neg_lt_neg (by exact_mod_cast hq1))
  · rw [hnorm, ← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp (neg_lt_zero.2 (by exact_mod_cast hq0))

private theorem exists_padicComplex_ratio (B : ℕ) (hB : 1 ≤ B) : ∃ t : ℂ_[p],
    ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧ ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by
  simpa using exists_padicComplex_norm_eq_rpow_neg (p := p) (q := (B : ℚ) / (2 * B + 1))
    (by positivity) ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : B < 2 * B + 1)))

/-- Elements of `AnnularRing p` agreeing on `p⁻¹ < ‖t‖ < 1` in `ℂ_p` are equal. -/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (h : ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1), eval ht x = eval ht y) : x = y := by
  by_contra hxy
  obtain ⟨B₀, hB₀⟩ := exists_forall_eval_ne_zero_of_ne_zero (sub_ne_zero.2 hxy)
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_ratio (p := p) (max B₀ 1) (le_max_right _ _)
  exact hB₀ (le_max_left _ _) t ht hnorm (by rw [map_sub, h t ht, sub_self])

/-- `F ∈ ℤ_p⟦X_0, X_1⟧` lies in `(X_0 X_1 - p)` iff it vanishes on `p⁻¹ < ‖t‖ < 1` in `ℂ_p`. -/
theorem mem_span_iff_forall_eval_annulus (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    F ∈ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])} ↔
      ∀ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 →
        ∑' d : Fin 2 →₀ ℕ, padicIntAlgebraMap p ℂ_[p] (MvPowerSeries.coeff d F) *
          t ^ d 0 * ((p : ℂ_[p]) / t) ^ d 1 = 0 := by
  rw [← ker_ofMvPowerSeries, RingHom.mem_ker]
  exact ⟨fun h t ht ↦ by rw [(hasSum_eval_ofMvPowerSeries ht F).tsum_eq, h, map_zero],
    fun h ↦ eq_of_forall_eval_eq fun t ht ↦ by
      rw [← (hasSum_eval_ofMvPowerSeries ht F).tsum_eq, h t ht, map_zero]⟩

instance instNoZeroDivisors : NoZeroDivisors (AnnularRing p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    by_contra! hne
    obtain ⟨Bx, hBx⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.1
    obtain ⟨By, hBy⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.2
    obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_ratio (p := p) (max (max Bx By) 1)
      (le_max_right _ _)
    exact mul_ne_zero (hBx ((le_max_left Bx By).trans (le_max_left _ _)) t ht hnorm)
      (hBy ((le_max_right Bx By).trans (le_max_left _ _)) t ht hnorm)
      (by rw [← map_mul, hxy, map_zero])

instance instIsDomain : IsDomain (AnnularRing p) := NoZeroDivisors.to_isDomain _
instance instIsDomainLocalizationAway : IsDomain (Localization.Away (T : AnnularRing p)) :=
  Localization.Away.isDomain (T_ne_zero (p := p))
end JointInjectivity
end AnnularRing

/-! ### Continuity and non-Lipschitz behaviour on `AnnularLaurent p hα` -/

namespace AnnularLaurent
open AnnularRing
variable {p : ℕ} [Fact p.Prime] {α : ℝ}

instance instIsDomain (hα : α ∈ Set.Ioo 0 1) : IsDomain (AnnularLaurent p hα) :=
  IsLocalization.Away.isDomain (AnnularLaurent p hα) (T_ne_zero (p := p))

section Eval
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {t : K}

/-- Extension of `AnnularRing.eval ht` to `AnnularLaurent p hα`. -/
def eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularLaurent p hα →+* K :=
  IsLocalization.Away.lift (T : AnnularRing p) (g := AnnularRing.eval ht)
    (by rw [AnnularRing.eval_T]; exact (ne_zero_of_norm_mem_Ioo ht).isUnit)
@[simp] theorem eval_algebraMap (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : eval hα ht (algebraMap _ _ x) = AnnularRing.eval ht x :=
  IsLocalization.Away.lift_eq _ _ x
@[simp] theorem eval_algebraMap_padicInt (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (c : ℤ_[p]) :
    eval hα ht (algebraMap ℤ_[p] (AnnularLaurent p hα) c) = padicIntAlgebraMap p K c := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p), eval_algebraMap,
    AnnularRing.eval_algebraMap]
@[simp] theorem eval_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (z : AnnularLaurent p hα) :
    eval hβ ht (ofRadius hα hβ z) = eval hα ht z := by
  have hcomp : (eval hβ ht).comp (ofRadius hα hβ).toRingHom = eval hα ht :=
    IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) <| by ext x; simp
  exact RingHom.congr_fun hcomp z
theorem eval_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    eval hα ht (unitT p hα) = t := by rw [val_unitT, eval_algebraMap, eval_T]
@[simp] theorem eval_zpow_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (r : ℤ) :
    eval hα ht (unitT p hα ^ r).val = t ^ r := by
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Units.val_zpow_eq_zpow_val, eval_unitT] using
    congr_arg Units.val (map_zpow (Units.map (eval hα ht).toMonoidHom) (unitT p hα) r)

/-- For `z ∈ AnnularLaurent p hα`, `∑ coeff z m * t ^ m` sums to `eval hα ht z`. -/
theorem hasSum_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (z : AnnularLaurent p hα) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (coeff z m) * t ^ m) (eval hα ht z) := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hclear : (unitT p hα ^ (k : ℤ)).val * z = algebraMap (AnnularRing p) _ x := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]
  have heval : eval hα ht z = AnnularRing.eval ht x * t ^ (-(k : ℤ)) := by
    have hval : eval hα ht z * t ^ (k : ℤ) = AnnularRing.eval ht x := by
      simpa [map_mul, map_pow, eval_algebraMap, eval_T, zpow_natCast] using
        congr_arg (eval hα ht) hx
    rw [← hval, mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
  rw [heval]
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.2
    ((AnnularRing.hasSum_eval ht x).mul_right (t ^ (-(k : ℤ))))).congr_fun fun m ↦ ?_
  have hm := congr_arg (fun w ↦ coeff w (m + k)) hclear
  rw [coeff_zpow_unitT_mul, add_sub_cancel_right, coeff_algebraMap] at hm
  rw [hm]; simp only [Function.comp_apply, Equiv.coe_addRight, mul_assoc, ← zpow_add₀ ht0,
    add_neg_cancel_right]

/-- When `α < ‖t‖`, `eval hα ht` is not Lipschitz on `AnnularLaurent p hα`. -/
theorem not_lipschitzWith_eval_of_lt (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (hαt : α < ‖t‖) (c : ℝ≥0) :
    ¬ LipschitzWith c (eval hα ht) := fun hL ↦ by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c : ℝ) ((one_lt_div hα.1).2 hαt)
  have hdist := hL.dist_le_mul (algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n) 0
  simp [show ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n‖ = α ^ n by
    simpa using (pseudoUniformizer p hα).norm_pow n] at hdist
  linarith [(div_pow ‖t‖ α n).trans_le ((div_le_iff₀ (pow_pos hα.1 n)).2 hdist)]

/-- The Tate gauge bound `‖z‖ ≤ α ^ r` implies `‖eval hα ht z‖ ≤ ‖t‖ ^ r`. -/
theorem norm_eval_le_zpow_of_norm_le_zpow (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) {z : AnnularLaurent p hα} {r : ℤ}
    (hz : ‖z‖ ≤ α ^ r) : ‖eval hα ht z‖ ≤ ‖t‖ ^ r := by
  obtain ⟨x, hx⟩ := (mem_ringOfDefinition_iff _).1 ((norm_le_zpow_iff hα z r).1 hz)
  rw [show z = (unitT p hα ^ r).val * algebraMap (AnnularRing p) _ x by
      simp [hx, ← mul_assoc, ← Units.val_mul],
    map_mul, eval_zpow_unitT, eval_algebraMap, norm_mul, norm_zpow]
  exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg t) r) (norm_eval_le_one ht x)

/-- Every annulus evaluation into a complete normed field extension of `ℚ_p` is continuous. -/
theorem continuous_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Continuous (eval hα ht) := by
  refine continuous_of_continuousAt_zero (eval hα ht).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]; intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε ht.2
  refine Metric.eventually_nhds_iff.2 ⟨α ^ (r : ℤ), zpow_pos hα.1 _, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz ⊢
  exact (norm_eval_le_zpow_of_norm_le_zpow hα ht hz.le).trans_lt (by simpa [zpow_natCast] using hr)

/-- Any bounded ring homomorphism `AnnularRing p →+* K` agreeing with `AnnularRing.eval ht`
on `ℤ_p`, `T`, and `U` equals `AnnularRing.eval ht`, by truncating normal forms. -/
private theorem ringHom_eq_eval_of_bounded (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (g : AnnularRing p →+* K) {C : ℝ} (hC : ∀ y : AnnularRing p, ‖g y‖ ≤ C)
    (hg_alg : ∀ c : ℤ_[p], g (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c)
    (hgT : g T = t) (hgU : g U = (p : K) / t) : g = AnnularRing.eval ht := by
  ext x; obtain ⟨⟨f₀, g₀⟩, hx⟩ := normalForm.surjective x; rw [normalForm_apply] at hx
  have hsplit (φ : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] AnnularRing p) (s : PowerSeries ℤ_[p]) (N : ℕ) :
      φ s = (∑ i ∈ Finset.range N, algebraMap ℤ_[p] _ (PowerSeries.coeff i s) * φ .X ^ i) +
        φ .X ^ N * φ (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) s) := by
    conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc N s, ← Polynomial.eval₂_C_X_eq_coe]
    rw [map_add, map_mul, map_pow, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂,
      PowerSeries.eval₂_trunc_eq_sum_range, add_comm]
    exact congrArg (· + _) <| Finset.sum_congr rfl fun i _ ↦ by
      rw [RingHom.comp_apply, AlgHom.coe_toRingHom, PowerSeries.C_eq_algebraMap, AlgHom.commutes]
  let sT (N : ℕ) : K :=
    ∑ i ∈ Finset.range N, padicIntAlgebraMap p K (PowerSeries.coeff i f₀) * t ^ i
  let sU (N : ℕ) : K :=
    ∑ i ∈ Finset.range N, padicIntAlgebraMap p K (PowerSeries.coeff i g₀) * ((p : K) / t) ^ i
  have hnorm_p_div_t : ‖(p : K) / t‖ = ((p : ℝ) * ‖t‖)⁻¹ := by
    have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
      simpa [map_natCast] using norm_padicIntAlgebraMap (K := K) (p : ℤ_[p])
    rw [norm_div, hpK, div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hdiff (N : ℕ) :
      ‖g x - (sT N + ((p : K) / t) * sU N)‖ ≤ ‖t‖ ^ N * C + ‖(p : K) / t‖ ^ (N + 1) * C := by
    have hgx : g x - (sT N + ((p : K) / t) * sU N) =
        t ^ N * g (ofPowerSeriesT (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) f₀)) +
        ((p : K) / t) ^ (N + 1) *
          g (ofPowerSeriesU (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) g₀)) := by
      conv_lhs => rw [← hx, hsplit ofPowerSeriesT f₀ N, hsplit ofPowerSeriesU g₀ N]
      simp only [ofPowerSeriesT_X, ofPowerSeriesU_X, map_add, map_sum, map_mul, map_pow,
        hg_alg, hgT, hgU, sT, sU]; ring
    rw [hgx]; refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
      · rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have htend_bound :
      Tendsto (fun N : ℕ ↦ ‖t‖ ^ N * C + ‖(p : K) / t‖ ^ (N + 1) * C) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul, add_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg t) ht.2).mul_const C).add
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (hnorm_p_div_t ▸ inv_p_mul_norm_lt_one ht)).comp (tendsto_add_atTop_nat 1)).mul_const C)
  have htend_g : Tendsto (fun N ↦ sT N + ((p : K) / t) * sU N) atTop (𝓝 (g x)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun N ↦ (norm_sub_rev _ _).trans_le (hdiff N)) htend_bound
  have htend_eval :
      Tendsto (fun N ↦ sT N + ((p : K) / t) * sU N) atTop (𝓝 (AnnularRing.eval ht x)) := by
    rw [← hx, map_add, map_mul, eval_U]
    exact (hasSum_eval_ofPowerSeriesT ht f₀).tendsto_sum_nat.add
      (tendsto_const_nhds.mul (hasSum_eval_ofPowerSeriesU ht g₀).tendsto_sum_nat)
  exact tendsto_nhds_unique htend_g htend_eval

/-- Any continuous ring homomorphism `AnnularLaurent p hα →+* K` agreeing with
`padicIntAlgebraMap p K` on `ℤ_p` and sending `unitT p hα` to `t` equals `eval hα ht`. -/
theorem eq_eval_of_continuous {hα : α ∈ Set.Ioo 0 1} (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (f : AnnularLaurent p hα →+* K) (hf : Continuous f)
    (hc : ∀ c, f (algebraMap ℤ_[p] _ c) = padicIntAlgebraMap p K c)
    (hT : f (unitT p hα) = t) : f = eval hα ht := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  let g : AnnularRing p →+* K := f.comp (algebraMap (AnnularRing p) (AnnularLaurent p hα))
  have hg_alg (c : ℤ_[p]) : g (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c := by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]; exact hc c
  have hgT : g T = t := by rw [RingHom.comp_apply, ← val_unitT hα]; exact hT
  have hgU : g U = (p : K) / t := by
    rw [eq_div_iff ht0, mul_comm, ← hgT, ← map_mul, T_mul_U, map_natCast]
  -- Continuity at `0` bounds `g` on `AnnularRing p`, since `T ^ r * y` shrinks into the ball.
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (x := 0)) 1 zero_lt_one
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ hα.2
  have hg_bound (y : AnnularRing p) : ‖g y‖ ≤ (‖t‖ ^ r)⁻¹ := by
    have hnorm_Ty : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) (T ^ r * y)‖ < δ := by
      rw [map_mul, map_pow]; refine (norm_mul_le _ _).trans_lt <| (mul_le_mul (norm_pow_le _ r)
        (norm_algebraMap_le_one hα y) (norm_nonneg _) (by positivity)).trans_lt ?_
      simpa [norm_algebraMap_T] using hr
    have h1 : ‖f (algebraMap (AnnularRing p) (AnnularLaurent p hα) (T ^ r * y))‖ < 1 := by
      rw [← dist_zero_right, ← f.map_zero]; exact hball (by rwa [dist_zero_right])
    rw [map_mul, map_pow, f.map_mul, f.map_pow, norm_mul, norm_pow] at h1
    change ‖g T‖ ^ r * ‖g y‖ < 1 at h1; rw [hgT] at h1
    rw [← one_div, le_div_iff₀' (pow_pos (norm_pos_iff.2 ht0) r)]; exact h1.le
  exact IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) <| RingHom.ext fun x ↦
    (RingHom.congr_fun (ringHom_eq_eval_of_bounded ht g hg_bound hg_alg hgT hgU) x).trans
      (eval_algebraMap hα ht x).symm
end Eval

/-- For every `α ∈ (0, 1)`, some `t ∈ ℂ_p` in `p⁻¹ < ‖t‖ < 1` gives a continuous non-Lipschitz
evaluation on `AnnularLaurent p hα`. -/
theorem exists_continuous_not_lipschitzWith_eval (hα : α ∈ Set.Ioo 0 1) :
    ∃ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      Continuous (eval hα ht) ∧ ∀ c : ℝ≥0, ¬ LipschitzWith c (eval hα ht) := by
  let β : ℝ := max (p : ℝ)⁻¹ α
  have hβ_pos : 0 < β := lt_max_of_lt_right hα.1
  have hβ_inv : 1 < β⁻¹ :=
    (one_lt_inv₀ hβ_pos).2 (max_lt (inv_lt_one_of_one_lt₀ (one_lt_p (p := p))) hα.2)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p : ℝ) hβ_inv
  let N : ℕ := m + 2; have hN_pos : (0 : ℝ) < N := by positivity
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_norm_eq_rpow_neg (p := p) (q := (1 : ℚ) / N)
    (by positivity) ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : 1 < N)))
  have hβ_lt_t : β < ‖t‖ := by
    have hrpow : (p : ℝ) ^ ((1 : ℝ) / N) < β⁻¹ := by
      calc (p : ℝ) ^ ((1 : ℝ) / N)
          < ((β⁻¹) ^ N : ℝ) ^ ((1 : ℝ) / N) := Real.rpow_lt_rpow (p_pos (p := p)).le
            (hm.trans_le (pow_le_pow_right₀ hβ_inv.le (Nat.le_add_right m 2))) (by positivity)
        _ = β⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hβ_pos.le),
              mul_one_div_cancel hN_pos.ne', Real.rpow_one]
    calc β = (β⁻¹)⁻¹ := (inv_inv β).symm
      _ < ((p : ℝ) ^ ((1 : ℝ) / N))⁻¹ :=
          inv_strictAnti₀ (Real.rpow_pos_of_pos (p_pos (p := p)) _) hrpow
      _ = ‖t‖ := by rw [hnorm, Real.rpow_neg (p_pos (p := p)).le]; simp
  exact ⟨t, ht, continuous_eval hα ht,
    not_lipschitzWith_eval_of_lt hα ht ((le_max_right _ _).trans_lt hβ_lt_t)⟩

end AnnularLaurent
end TauCeti
