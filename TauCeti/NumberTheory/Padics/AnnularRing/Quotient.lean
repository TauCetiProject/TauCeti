/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import TauCeti.NumberTheory.Padics.AnnularRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.Topology.Algebra.InfiniteSum.Sigma

/-!
# Power-series presentation, local structure, and boundary quotient of `ℤ_p⟦T, p/T⟧`

The annular coefficient ring `H = ℤ_p⟦T, p/T⟧` (`TauCeti.AnnularRing p`) admits a surjective
`ℤ_p`-algebra homomorphism `evalTU : MvPowerSeries (Fin 2) ℤ_p →ₐ[ℤ_p] AnnularRing p` (`X 0 ↦ T`,
`X 1 ↦ U = p / T`) with kernel `(X 0 * X 1 - p)`, yielding `quotientMvPowerSeriesEquiv`. Extracting
the `U`-coefficients `uCoeff x n` (`p ^ n * uCoeff x n = x.coeff (-n)`) gives the boundary quotient
`quotientSpanTEquiv : AnnularRing p ⧸ (T) ≃+* (ZMod p)⟦X⟧`, primality of `(T) = (p, T)`
(`isPrime_span_T`), the residue map `residueTU : AnnularRing p →+* ZMod p`, and the maximal ideal
`maximalIdeal_eq_span_T_U : maximalIdeal (AnnularRing p) = (T, U)`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology PowerSeries

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
private theorem p_pos : (0 : ℝ) < p := zero_lt_one.trans one_lt_p
private theorem zpow_p_nonneg (z : ℤ) : (0 : ℝ) ≤ (p : ℝ) ^ z := (zpow_pos p_pos z).le
private theorem p_ne_zero : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

private theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, (p : ℝ) ^ (-(N : ℤ)) < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
  exact ⟨N, by simpa [zpow_neg, zpow_natCast, inv_pow] using hN⟩

/-! ### Two-variable power-series evaluation `X 0 ↦ T, X 1 ↦ U` -/

private def evalTUTerm (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) (d : Fin 2 →₀ ℕ) : ℤ_[p] :=
  MvPowerSeries.coeff d F * ((T : AnnularRing p) ^ d 0 * U ^ d 1).coeff m
private theorem evalTUTerm_eq_zero_of_ne (F : MvPowerSeries (Fin 2) ℤ_[p]) {m : ℤ}
    {d : Fin 2 →₀ ℕ} (hd : m ≠ (d 0 : ℤ) - d 1) : evalTUTerm F m d = 0 := by
  rw [evalTUTerm, coeff_T_pow_mul_U_pow, ite_eq_right hd, mul_zero]
private theorem norm_evalTUTerm_le_zpow_neg (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ)
    (d : Fin 2 →₀ ℕ) : ‖evalTUTerm F m d‖ ≤ (p : ℝ) ^ (-(d 1 : ℤ)) := by
  rw [evalTUTerm, coeff_T_pow_mul_U_pow]; split_ifs
  · rw [norm_mul, PadicInt.norm_p_pow]
    exact mul_le_of_le_one_left (zpow_p_nonneg _) (PadicInt.norm_le_one _)
  · simp
private theorem norm_evalTUTerm_le (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) (d : Fin 2 →₀ ℕ) :
    ‖evalTUTerm F m d‖ ≤ (p : ℝ) ^ min 0 m := by
  by_cases hd : m = (d 0 : ℤ) - d 1
  · exact (norm_evalTUTerm_le_zpow_neg F m d).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega))
  · simpa [evalTUTerm_eq_zero_of_ne F hd] using zpow_p_nonneg (p := p) _
private theorem summable_evalTUTerm (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    Summable (evalTUTerm F m) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Metric.tendsto_nhds.2 fun ε hε ↦ ?_)
  obtain ⟨N, hN⟩ := exists_zpow_neg_lt (p := p) hε
  refine eventually_cofinite.2 <|
    (Set.finite_Iic (Finsupp.single (0 : Fin 2) (m + N).toNat + Finsupp.single 1 N)).subset
      fun d hd ↦ ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hd
  have hne : m = (d 0 : ℤ) - d 1 := by
    by_contra h; rw [evalTUTerm_eq_zero_of_ne F h, norm_zero] at hd; linarith
  have hd1 : d 1 < N := by
    by_contra! hle; linarith [(norm_evalTUTerm_le_zpow_neg F m d).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (neg_le_neg (Nat.cast_le.2 hle)))]
  intro i; fin_cases i <;> simp <;> omega

private def evalTUAux (F : MvPowerSeries (Fin 2) ℤ_[p]) : AnnularRing p :=
  ⟨fun m ↦ ∑' d : Fin 2 →₀ ℕ, evalTUTerm F m d, fun m ↦
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (zpow_p_nonneg _)
      (norm_evalTUTerm_le F m)⟩
private theorem coeff_evalTUAux (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    (evalTUAux F).coeff m = ∑' d : Fin 2 →₀ ℕ, evalTUTerm F m d := (rfl)
private def evalTUMulTerm (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m r : ℤ)
    (d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) : ℤ_[p] := evalTUTerm F r d.1 * evalTUTerm G (m - r) d.2
private theorem summable_evalTUMulTerm (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    Summable (Function.uncurry (evalTUMulTerm F G m)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Metric.tendsto_nhds.2 fun ε hε ↦ ?_)
  obtain ⟨N, hN⟩ := exists_zpow_neg_lt (p := p) hε
  let B : Fin 2 →₀ ℕ := Finsupp.single 0 (m + 2 * N).toNat + Finsupp.single 1 N
  refine eventually_cofinite.2 <| ((Set.finite_Icc (-(N : ℤ)) (m + 2 * N)).prod
    ((Set.finite_Iic B).prod (Set.finite_Iic B))).subset fun ⟨r, d₁, d₂⟩ h ↦ ?_
  simp only [Set.mem_ofPred_eq, Function.uncurry_apply_pair, dist_zero_right, not_lt] at h
  have hr1 : r = (d₁ 0 : ℤ) - d₁ 1 := by
    by_contra hne; simp [evalTUMulTerm, evalTUTerm_eq_zero_of_ne F hne] at h; linarith
  have hr2 : m - r = (d₂ 0 : ℤ) - d₂ 1 := by
    by_contra hne; simp [evalTUMulTerm, evalTUTerm_eq_zero_of_ne G hne] at h; linarith
  have hd_sum : d₁ 1 + d₂ 1 < N := by
    by_contra! hle
    have hbd : ‖evalTUMulTerm F G m r (d₁, d₂)‖ ≤ (p : ℝ) ^ (-((d₁ 1 + d₂ 1 : ℕ) : ℤ)) := by
      rw [evalTUMulTerm, norm_mul, Nat.cast_add, neg_add, zpow_add₀ (p_pos (p := p)).ne']
      exact mul_le_mul (norm_evalTUTerm_le_zpow_neg F r d₁)
        (norm_evalTUTerm_le_zpow_neg G (m - r) d₂) (norm_nonneg _) (zpow_p_nonneg _)
    linarith [hbd.trans (zpow_le_zpow_right₀ (one_lt_p (p := p)).le
      (neg_le_neg (Nat.cast_le.2 hle)))]
  exact ⟨⟨by omega, by omega⟩, fun i ↦ by fin_cases i <;> simp [B] <;> omega,
    fun i ↦ by fin_cases i <;> simp [B] <;> omega⟩

private theorem tsum_evalTUMulTerm_col (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ)
    (d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :
    (∑' r : ℤ, evalTUMulTerm F G m r d) = MvPowerSeries.coeff d.1 F * MvPowerSeries.coeff d.2 G *
      ((T : AnnularRing p) ^ (d.1 + d.2) 0 * U ^ (d.1 + d.2) 1).coeff m := by
  rw [tsum_eq_single ((d.1 0 : ℤ) - d.1 1) fun r hr ↦ by
    rw [evalTUMulTerm, evalTUTerm_eq_zero_of_ne F hr, zero_mul]]
  simp only [evalTUMulTerm, evalTUTerm, coeff_T_pow_mul_U_pow, ite_true, Finsupp.add_apply]
  by_cases hm : m - ((d.1 0 : ℤ) - d.1 1) = (d.2 0 : ℤ) - d.2 1
  · rw [ite_eq_left hm, ite_eq_left (by omega), pow_add]; ring
  · rw [ite_eq_right hm, ite_eq_right (by omega)]; simp

private theorem evalTUAux_mul (F G : MvPowerSeries (Fin 2) ℤ_[p]) :
    evalTUAux (F * G) = evalTUAux F * evalTUAux G := by
  classical
  ext m : 2; have hΦ := summable_evalTUMulTerm F G m
  have hcomm : (∑' r : ℤ, (evalTUAux F).coeff r * (evalTUAux G).coeff (m - r)) =
      ∑' d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ), ∑' r : ℤ, evalTUMulTerm F G m r d := by
    rw [hΦ.tsum_comm]; exact tsum_congr fun r ↦
      (summable_evalTUTerm F r).tsum_mul_tsum (summable_evalTUTerm G (m - r)) (hΦ.prod_factor r)
  have hpair : Summable fun d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦
      MvPowerSeries.coeff d.1 F * MvPowerSeries.coeff d.2 G *
        ((T : AnnularRing p) ^ (d.1 + d.2) 0 * U ^ (d.1 + d.2) 1).coeff m := by
    simpa only [Function.uncurry, Prod.swap_prod_mk, tsum_evalTUMulTerm_col] using hΦ.prod_symm.prod
  rw [coeff_mul, hcomm]; simp_rw [tsum_evalTUMulTerm_col]
  rw [hpair.tsum_prod_eq_tsum_sum_antidiagonal, coeff_evalTUAux]
  refine tsum_congr fun d ↦ by
    rw [evalTUTerm, MvPowerSeries.coeff_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun kl hkl ↦ by rw [Finset.mem_antidiagonal.1 hkl]

/-- Substitution `X 0 ↦ T, X 1 ↦ U` on two-variable integral power series over `ℤ_p`. -/
def evalTU : MvPowerSeries (Fin 2) ℤ_[p] →ₐ[ℤ_[p]] AnnularRing p where
  toFun := evalTUAux
  map_one' := by
    ext m : 2; rw [coeff_evalTUAux, tsum_eq_single 0 fun d hd ↦ by
      simp [evalTUTerm, MvPowerSeries.coeff_one, hd]]; simp [evalTUTerm, coeff_one]
  map_mul' := evalTUAux_mul
  map_zero' := by ext m : 2; simp [coeff_evalTUAux, evalTUTerm]
  map_add' F G := by
    ext m : 2; rw [coeff_evalTUAux, coeff_add, coeff_evalTUAux, coeff_evalTUAux,
      ← (summable_evalTUTerm F m).tsum_add (summable_evalTUTerm G m)]
    exact tsum_congr fun d ↦ by simp [evalTUTerm, add_mul]
  commutes' c := by
    ext m : 2; rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      coeff_evalTUAux, tsum_eq_single 0 fun d hd ↦ by
        rw [evalTUTerm, MvPowerSeries.coeff_C_of_ne_zero hd, zero_mul]]
    simp [evalTUTerm, coeff_algebraMap]

private theorem evalTU_apply (F : MvPowerSeries (Fin 2) ℤ_[p]) : evalTU F = evalTUAux F := (rfl)
@[simp] theorem evalTU_C (c : ℤ_[p]) :
    evalTU (MvPowerSeries.C c) = algebraMap ℤ_[p] (AnnularRing p) c := evalTU.commutes c
@[simp] theorem evalTU_X_zero : evalTU (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℤ_[p]) = T := by
  ext m : 2; rw [evalTU_apply, coeff_evalTUAux, tsum_eq_single (Finsupp.single 0 1) fun d hd ↦ by
    simp [evalTUTerm, MvPowerSeries.coeff_X, hd]]; simp [evalTUTerm, MvPowerSeries.coeff_X, coeff_T]
@[simp] theorem evalTU_X_one : evalTU (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℤ_[p]) = U := by
  ext m : 2; rw [evalTU_apply, coeff_evalTUAux, tsum_eq_single (Finsupp.single 1 1) fun d hd ↦ by
    simp [evalTUTerm, MvPowerSeries.coeff_X, hd]]; simp [evalTUTerm, MvPowerSeries.coeff_X, coeff_U]

/-- Diagonal exponent `(m.toNat + k, (-m).toNat + k)` parameterising `{d | d 0 - d 1 = m}`. -/
def diagIdx (m : ℤ) (k : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m.toNat + k) + Finsupp.single 1 ((-m).toNat + k)
@[simp] theorem diagIdx_apply_zero (m : ℤ) (k : ℕ) : diagIdx m k 0 = m.toNat + k := by
  simp [diagIdx]
@[simp] theorem diagIdx_apply_one (m : ℤ) (k : ℕ) : diagIdx m k 1 = (-m).toNat + k := by
  simp [diagIdx]
private theorem diagIdx_injective (m : ℤ) : Function.Injective (diagIdx m) := fun k₁ k₂ h ↦ by
  have h0 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 0) h; simp only [diagIdx_apply_zero] at h0; omega

/-- Explicit diagonal formula for the `m`-th coefficient of `evalTU F`. -/
theorem coeff_evalTU (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    (evalTU F).coeff m = (p : ℤ_[p]) ^ (-m).toNat *
      ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F := by
  rw [evalTU_apply, coeff_evalTUAux,
    ← ((PadicInt.summable_pow_mul fun k ↦ MvPowerSeries.coeff (diagIdx m k) F).hasSum.mul_left
      ((p : ℤ_[p]) ^ (-m).toNat)).tsum_eq, ← (diagIdx_injective m).tsum_eq]
  · exact tsum_congr fun k ↦ by
      simp only [evalTUTerm, diagIdx_apply_zero, diagIdx_apply_one, coeff_T_pow_mul_U_pow]
      rw [ite_eq_left (by omega), pow_add]; ring
  · intro d hd
    have hm : m = (d 0 : ℤ) - d 1 := by by_contra h; exact hd (evalTUTerm_eq_zero_of_ne F h)
    exact ⟨min (d 0) (d 1), by ext i; fin_cases i <;> (simp [diagIdx]; omega)⟩

private theorem diagIdx_eq_single_zero_iff {m : ℤ} {k : ℕ} :
    diagIdx m k = Finsupp.single 0 (diagIdx m k 0) ↔ 0 ≤ m ∧ k = 0 :=
  ⟨fun h ↦ by have h1 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 1) h; simp at h1; omega,
   fun ⟨hm, hk⟩ ↦ by ext i; fin_cases i <;> simp [diagIdx, hk, hm]⟩
private theorem diagIdx_eq_single_one_iff {m : ℤ} {k : ℕ} :
    diagIdx m k = Finsupp.single 1 (diagIdx m k 1) ↔ m ≤ 0 ∧ k = 0 :=
  ⟨fun h ↦ by have h0 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 0) h; simp at h0; omega,
   fun ⟨hm, hk⟩ ↦ by ext i; fin_cases i <;> simp [diagIdx, hk, hm]⟩

@[simp] theorem evalTU_toMvPowerSeries_zero (f : ℤ_[p]⟦X⟧) :
    evalTU (f.toMvPowerSeries (0 : Fin 2)) = ofPowerSeriesT f := by
  ext m : 2; rw [coeff_evalTU]
  simp_rw [PowerSeries.coeff_toMvPowerSeries, diagIdx_eq_single_zero_iff]
  rcases lt_or_ge m 0 with hm | hm
  · simp [coeff_ofPowerSeriesT_of_neg _ hm, not_le.2 hm]
  · lift m to ℕ using hm
    rw [coeff_ofPowerSeriesT_natCast, Int.toNat_of_nonpos (by omega), pow_zero, one_mul,
      tsum_eq_single 0 fun k hk ↦ by simp [hk]]; simp
@[simp] theorem evalTU_toMvPowerSeries_one (g : ℤ_[p]⟦X⟧) :
    evalTU (g.toMvPowerSeries (1 : Fin 2)) = ofPowerSeriesU g := by
  ext m : 2; rw [coeff_evalTU]
  simp_rw [PowerSeries.coeff_toMvPowerSeries, diagIdx_eq_single_one_iff]
  rcases lt_or_ge 0 m with hm | hm
  · simp [coeff_ofPowerSeriesU_of_pos _ hm, not_le.2 hm]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [coeff_ofPowerSeriesU_neg_natCast, neg_neg, Int.toNat_natCast,
      tsum_eq_single 0 fun k hk ↦ by simp [hk]]; simp

/-- `evalTU` is surjective, via the normal form decomposition `f(T) + U g(U)`. -/
theorem evalTU_surjective : Function.Surjective (evalTU (p := p)) := fun x ↦ by
  obtain ⟨⟨f, g⟩, hfg⟩ := normalForm.surjective x
  exact ⟨f.toMvPowerSeries 0 + MvPowerSeries.X 1 * g.toMvPowerSeries 1,
    by simpa [normalForm_apply] using hfg⟩

/-! ### Kernel of `evalTU` and the presentation `ℤ_p⟦T, U⟧ ⧸ (T U - p)` -/

private def diagStep : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
private def evalTUKerQuot (F : MvPowerSeries (Fin 2) ℤ_[p]) : MvPowerSeries (Fin 2) ℤ_[p] :=
  fun d ↦ ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + (k + 1) • diagStep) F
private theorem tsum_pow_mul_coeff_add_nsmul (F : MvPowerSeries (Fin 2) ℤ_[p]) (d : Fin 2 →₀ ℕ) :
    (∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + k • diagStep) F) =
      MvPowerSeries.coeff d F + (p : ℤ_[p]) * MvPowerSeries.coeff d (evalTUKerQuot F) := by
  rw [(PadicInt.summable_pow_mul _).tsum_eq_zero_add]
  simp only [pow_zero, zero_nsmul, add_zero, one_mul, pow_succ', mul_assoc]
  rw [MvPowerSeries.coeff_apply (evalTUKerQuot F) d, evalTUKerQuot,
    ((PadicInt.summable_pow_mul _).hasSum.mul_left (p : ℤ_[p])).tsum_eq]

/-- The kernel of `evalTU` is the principal ideal `(X 0 * X 1 - p)`. -/
theorem ker_evalTU :
    RingHom.ker (evalTU (p := p)).toRingHom =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])} := by
  refine le_antisymm (fun F hF ↦ Ideal.mem_span_singleton.2
    ⟨evalTUKerQuot F, MvPowerSeries.ext fun d ↦ ?_⟩)
    (Ideal.span_le.2 (by rintro _ rfl; simp [RingHom.mem_ker]))
  rw [RingHom.mem_ker] at hF
  have hdiag (m : ℤ) : ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F = 0 := by
    have hm := congr_arg (coeff · m) hF
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_evalTU, coeff_zero] at hm
    exact (mul_eq_zero.1 hm).resolve_left (pow_ne_zero _ (p_ne_zero (p := p)))
  have hX01 : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℤ_[p]) =
      MvPowerSeries.monomial diagStep 1 := by
    rw [MvPowerSeries.X_def 0, MvPowerSeries.X_def 1, MvPowerSeries.monomial_mul_monomial,
      one_mul, diagStep]
  rw [sub_mul, map_sub, MvPowerSeries.coeff_C_mul, hX01, MvPowerSeries.coeff_monomial_mul]
  split_ifs with he
  · have hpeel : MvPowerSeries.coeff (d - diagStep) (evalTUKerQuot F) =
        MvPowerSeries.coeff d F + (p : ℤ_[p]) * MvPowerSeries.coeff d (evalTUKerQuot F) := by
      rw [MvPowerSeries.coeff_apply, evalTUKerQuot, ← tsum_pow_mul_coeff_add_nsmul]
      exact tsum_congr fun k ↦ by
        rw [add_nsmul, one_nsmul, ← add_assoc, add_right_comm _ _ diagStep,
          tsub_add_cancel_of_le he]
    rw [one_mul, hpeel, add_sub_cancel_right]
  · rw [zero_sub]
    have h01 : d 0 = 0 ∨ d 1 = 0 := by
      by_contra h; rw [not_or] at h
      exact he fun i ↦ by fin_cases i <;> simp [diagStep] <;> omega
    have hd_eq (k : ℕ) : diagIdx ((d 0 : ℤ) - d 1) k = d + k • diagStep := by
      ext i; rcases h01 with h0 | h1 <;> fin_cases i <;> simp [diagIdx, diagStep, *]
    have h0 := hdiag ((d 0 : ℤ) - d 1)
    simp_rw [hd_eq] at h0; rw [tsum_pow_mul_coeff_add_nsmul] at h0
    exact eq_neg_of_add_eq_zero_left h0

/-- Canonical `ℤ_p`-algebra isomorphism `ℤ_p⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p) ≃ₐ[ℤ_p] AnnularRing p`. -/
def quotientMvPowerSeriesEquiv :
    (MvPowerSeries (Fin 2) ℤ_[p] ⧸
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])}) ≃ₐ[ℤ_[p]]
      AnnularRing p :=
  (Ideal.quotientEquivAlgOfEq ℤ_[p] ker_evalTU.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evalTU_surjective)
@[simp] theorem quotientMvPowerSeriesEquiv_mk (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    quotientMvPowerSeriesEquiv (Ideal.Quotient.mk _ F) = evalTU F := (rfl)
@[simp] theorem quotientMvPowerSeriesEquiv_symm_T :
    quotientMvPowerSeriesEquiv.symm (T : AnnularRing p) =
      Ideal.Quotient.mk _ (MvPowerSeries.X 0) := quotientMvPowerSeriesEquiv.injective (by simp)
@[simp] theorem quotientMvPowerSeriesEquiv_symm_U :
    quotientMvPowerSeriesEquiv.symm (U : AnnularRing p) =
      Ideal.Quotient.mk _ (MvPowerSeries.X 1) := quotientMvPowerSeriesEquiv.injective (by simp)

/-! ### `U`-coefficients, boundary quotient `AnnularRing p ⧸ (T)`, and local structure -/

private theorem exists_eq_ofPowerSeriesU_add_T_mul (x : AnnularRing p) :
    ∃ g : ℤ_[p]⟦X⟧, ∃ z : AnnularRing p, x = ofPowerSeriesU g + T * z := by
  obtain ⟨⟨f, g⟩, rfl⟩ := normalForm.surjective x
  refine ⟨C (constantCoeff f) + X * g,
    ofPowerSeriesT (PowerSeries.mk fun n ↦ PowerSeries.coeff (n + 1) f), ?_⟩
  conv_lhs => rw [normalForm_apply, eq_X_mul_shift_add_const f]
  simp only [map_add, map_mul, ofPowerSeriesT_X, ofPowerSeriesU_X, C_eq_algebraMap, AlgHom.commutes]
  ring

/-- The `n`-th `U`-coefficient of `x`, satisfying `p ^ n * uCoeff x n = x.coeff (-n)`. -/
def uCoeff (x : AnnularRing p) (n : ℕ) : ℤ_[p] := (x.pow_dvd_coeff_neg n).choose
@[simp] theorem pow_mul_uCoeff (x : AnnularRing p) (n : ℕ) :
    (p : ℤ_[p]) ^ n * uCoeff x n = x.coeff (-n) := (x.pow_dvd_coeff_neg n).choose_spec.symm
/-- Uniqueness of `uCoeff`: if `p ^ n * c = x.coeff (-n)`, then `uCoeff x n = c`. -/
theorem uCoeff_eq_of_mul_eq {x : AnnularRing p} {n : ℕ} {c : ℤ_[p]}
    (h : (p : ℤ_[p]) ^ n * c = x.coeff (-n)) : uCoeff x n = c :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) ((pow_mul_uCoeff x n).trans h.symm)
@[simp] theorem uCoeff_zero_right (x : AnnularRing p) : uCoeff x 0 = x.coeff 0 := by
  simpa using pow_mul_uCoeff x 0
@[simp] theorem uCoeff_zero (n : ℕ) : uCoeff (0 : AnnularRing p) n = 0 :=
  uCoeff_eq_of_mul_eq (by simp)
@[simp] theorem uCoeff_one (n : ℕ) : uCoeff (1 : AnnularRing p) n = if n = 0 then 1 else 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_one]; by_cases hn : n = 0 <;> simp [hn])
@[simp] theorem uCoeff_add (x y : AnnularRing p) (n : ℕ) :
    uCoeff (x + y) n = uCoeff x n + uCoeff y n :=
  uCoeff_eq_of_mul_eq (by rw [mul_add, pow_mul_uCoeff, pow_mul_uCoeff, coeff_add])
@[simp] theorem uCoeff_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) (n : ℕ) :
    uCoeff (ofPowerSeriesU g) n = PowerSeries.coeff n g :=
  uCoeff_eq_of_mul_eq (coeff_ofPowerSeriesU_neg_natCast g n).symm
@[simp] theorem uCoeff_T (n : ℕ) : uCoeff (T : AnnularRing p) n = 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_T, ite_eq_right (by omega), mul_zero])
@[simp] theorem uCoeff_U (n : ℕ) : uCoeff (U : AnnularRing p) n = if n = 1 then 1 else 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_U]; by_cases hn : n = 1 <;> simp [hn])

/-- The `U`-coefficients of `ofPowerSeriesU (PowerSeries.mk 1) = ∑ U ^ n` are constantly `1` and do
not tend to `0`; thus `AnnularRing p` is strictly larger than the `p`-adic completion of
`ℤ_p⟦T⟧[p/T]`. -/
theorem not_tendsto_uCoeff_ofPowerSeriesU_mk_one :
    ¬ Tendsto (uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧))) atTop (𝓝 0) := by
  have h : uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧)) = fun _ ↦ (1 : ℤ_[p]) :=
    funext fun _ ↦ by simp
  rw [h, tendsto_const_nhds_iff]; exact one_ne_zero

/-- `T ∣ x` in `AnnularRing p` iff `p ∣ uCoeff x n` for all `n : ℕ` (equivalently,
`‖x.coeff (-n)‖ ≤ p ^ -(n + 1)`). -/
theorem T_dvd_iff {x : AnnularRing p} :
    (T : AnnularRing p) ∣ x ↔ ∀ n : ℕ, (p : ℤ_[p]) ∣ uCoeff x n := by
  refine ⟨?_, fun h ↦ ⟨⟨fun m ↦ x.coeff (m + 1), fun m ↦ ?_⟩, by ext m : 2; simp [coeff_T_mul]⟩⟩
  · rintro ⟨y, rfl⟩ n; refine ⟨uCoeff y (n + 1), uCoeff_eq_of_mul_eq ?_⟩
    rw [coeff_T_mul, show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega,
      ← pow_mul_uCoeff, pow_succ, mul_assoc]
  · rcases le_or_gt 0 m with hm | hm
    · rw [min_eq_left hm, zpow_zero]; exact PadicInt.norm_le_one _
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, m + 1 = -n := ⟨(-(m + 1)).toNat, by omega⟩
      obtain ⟨c, hc⟩ := h n
      rw [show x.coeff (m + 1) = (p : ℤ_[p]) ^ (n + 1) * c by
          rw [hn, ← pow_mul_uCoeff, hc, pow_succ, mul_assoc],
        norm_mul, PadicInt.norm_p_pow, show min 0 m = -((n + 1 : ℕ) : ℤ) by omega]
      exact mul_le_of_le_one_right (zpow_p_nonneg _) (PadicInt.norm_le_one _)

private theorem toZMod_uCoeff_T_mul (z : AnnularRing p) (n : ℕ) :
    PadicInt.toZMod (uCoeff (T * z) n) = 0 := by
  obtain ⟨c, hc⟩ := T_dvd_iff.1 (dvd_mul_right T z) n; simp [hc]

/-- Boundary reduction `AnnularRing p →+* (ZMod p)⟦X⟧` (`T ↦ 0`, `U ↦ X`) on `uCoeff` mod `p`. -/
def modT : AnnularRing p →+* (ZMod p)⟦X⟧ where
  toFun x := PowerSeries.mk fun n ↦ PadicInt.toZMod (uCoeff x n)
  map_zero' := by ext n; simp
  map_one' := by ext n; by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  map_add' x y := by ext n; simp
  map_mul' x y := by
    obtain ⟨gx, zx, rfl⟩ := exists_eq_ofPowerSeriesU_add_T_mul x
    obtain ⟨gy, zy, rfl⟩ := exists_eq_ofPowerSeriesU_add_T_mul y
    have hmap (g : ℤ_[p]⟦X⟧) (z : AnnularRing p) :
        (PowerSeries.mk fun n ↦ PadicInt.toZMod (uCoeff (ofPowerSeriesU g + T * z) n)) =
          PowerSeries.map PadicInt.toZMod g := by ext n; simp [toZMod_uCoeff_T_mul]
    rw [show (ofPowerSeriesU gx + T * zx) * (ofPowerSeriesU gy + T * zy) = ofPowerSeriesU (gx * gy)
      + T * (zx * ofPowerSeriesU gy + ofPowerSeriesU gx * zy + T * zx * zy) by rw [map_mul]; ring,
      hmap, hmap, hmap, map_mul]
@[simp] theorem coeff_modT (x : AnnularRing p) (n : ℕ) :
    PowerSeries.coeff n (modT x) = PadicInt.toZMod (uCoeff x n) := by simp [modT]
@[simp] theorem modT_T : modT (T : AnnularRing p) = 0 := by ext n; simp
@[simp] theorem modT_U : modT (U : AnnularRing p) = PowerSeries.X := by
  ext n; rw [coeff_modT, PowerSeries.coeff_X, uCoeff_U]; by_cases hn : n = 1 <;> simp [hn]
@[simp] theorem modT_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) :
    modT (ofPowerSeriesU g) = PowerSeries.map PadicInt.toZMod g := by ext n; simp
/-- `modT` sends a scalar `c : ℤ_p` to the constant power series of its reduction modulo `p`. -/
@[simp] theorem modT_algebraMap (c : ℤ_[p]) :
    modT (algebraMap ℤ_[p] (AnnularRing p) c) = PowerSeries.C (PadicInt.toZMod c) := by
  rw [← ofPowerSeriesU.commutes c, modT_ofPowerSeriesU, ← C_eq_algebraMap, PowerSeries.map_C]
/-- The boundary reduction `modT : AnnularRing p →+* (ZMod p)⟦X⟧` is surjective. -/
theorem modT_surjective : Function.Surjective (modT (p := p)) := fun φ ↦
  ⟨ofPowerSeriesU (PowerSeries.mk fun n ↦ ((PowerSeries.coeff n φ).val : ℤ_[p])), by ext n; simp⟩

/-- The kernel of the boundary reduction `modT` is the principal ideal `(T)`. -/
theorem ker_modT : RingHom.ker (modT (p := p)) = Ideal.span {T} := by
  ext x; rw [RingHom.mem_ker, Ideal.mem_span_singleton, T_dvd_iff, PowerSeries.ext_iff]
  exact forall_congr' fun n ↦ by
    rw [coeff_modT, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- Killing `T` (equivalently `(p, T)`) identifies `AnnularRing p ⧸ (T)` with `(ZMod p)⟦X⟧`. -/
def quotientSpanTEquiv : (AnnularRing p ⧸ Ideal.span {(T : AnnularRing p)}) ≃+* (ZMod p)⟦X⟧ :=
  (Ideal.quotEquivOfEq ker_modT.symm).trans (RingHom.quotientKerEquivOfSurjective modT_surjective)
@[simp] theorem quotientSpanTEquiv_mk (x : AnnularRing p) :
    quotientSpanTEquiv (Ideal.Quotient.mk _ x) = modT x := (rfl)

/-- `(T) = (p, T)` is prime in `AnnularRing p`, since `AnnularRing p ⧸ (T) ≃+* (ZMod p)⟦X⟧` is an
integral domain. -/
theorem isPrime_span_T : (Ideal.span {(T : AnnularRing p)}).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).1 quotientSpanTEquiv.toMulEquiv.isDomain

instance : IsLocalRing (AnnularRing p) :=
  IsLocalRing.of_surjective' evalTU.toRingHom evalTU_surjective

/-- The residue homomorphism `AnnularRing p →+* ZMod p` sending `x ↦ x.coeff 0 mod p`. -/
def residueTU : AnnularRing p →+* ZMod p := (PowerSeries.constantCoeff (R := ZMod p)).comp modT
theorem residueTU_apply (x : AnnularRing p) : residueTU x = PadicInt.toZMod (x.coeff 0) := by
  simp [residueTU, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
@[simp] theorem residueTU_T : residueTU (T : AnnularRing p) = 0 := by
  simp [residueTU_apply, coeff_T]
@[simp] theorem residueTU_U : residueTU (U : AnnularRing p) = 0 := by
  simp [residueTU_apply, coeff_U]
@[simp] theorem residueTU_algebraMap (c : ℤ_[p]) :
    residueTU (algebraMap ℤ_[p] (AnnularRing p) c) = PadicInt.toZMod c := by simp [residueTU_apply]
/-- The residue homomorphism `residueTU : AnnularRing p →+* ZMod p` is surjective. -/
theorem residueTU_surjective : Function.Surjective (residueTU (p := p)) :=
  ZMod.ringHom_surjective residueTU
/-- The kernel of `residueTU` is the unique maximal ideal of the local ring `AnnularRing p`. -/
theorem ker_residueTU :
    RingHom.ker (residueTU (p := p)) = IsLocalRing.maximalIdeal (AnnularRing p) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective residueTU residueTU_surjective)

/-- Unit criterion: `x ∈ AnnularRing p` is a unit iff its constant term `x.coeff 0` is a unit. -/
theorem isUnit_iff {x : AnnularRing p} : IsUnit x ↔ IsUnit (x.coeff 0) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← ker_residueTU, RingHom.mem_ker, residueTU_apply,
    ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.notMem_maximalIdeal]
/-- `T` is not a unit in `AnnularRing p`, since its constant term is `0`. -/
theorem not_isUnit_T : ¬ IsUnit (T : AnnularRing p) := by simp [isUnit_iff, coeff_T]
/-- `U` is not a unit in `AnnularRing p`, since its constant term is `0`. -/
theorem not_isUnit_U : ¬ IsUnit (U : AnnularRing p) := by simp [isUnit_iff, coeff_U]
/-- The prime `p` is not a unit in `AnnularRing p`, since `p ∈ ℤ_p` is not a unit. -/
theorem not_isUnit_p : ¬ IsUnit (p : AnnularRing p) := by
  simpa [isUnit_iff, mem_nonunits_iff] using PadicInt.p_nonunit (p := p)

/-- The maximal ideal of `AnnularRing p` is `(T, U)` (containing `p = T U`). -/
theorem maximalIdeal_eq_span_T_U :
    IsLocalRing.maximalIdeal (AnnularRing p) = Ideal.span {T, U} := by
  rw [← ker_residueTU]
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.2 fun y hy ↦ ?_)
  · rw [RingHom.mem_ker, residueTU_apply, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
    obtain ⟨c₀, hc₀⟩ := hx; obtain ⟨⟨f, g⟩, rfl⟩ := normalForm.surjective x
    have hc₀' : constantCoeff f = (p : ℤ_[p]) * c₀ := by
      simpa [coeff_zero_eq_constantCoeff_apply] using
        (coeff_normalForm_natCast f g 0).symm.trans hc₀
    rw [normalForm_apply, eq_X_mul_shift_add_const f, map_add, map_mul, ofPowerSeriesT_X,
      C_eq_algebraMap, AlgHom.commutes, hc₀', map_mul, map_natCast, ← T_mul_U, mul_assoc]
    have hT : (T : AnnularRing p) ∈ Ideal.span {T, U} := Ideal.subset_span (by simp)
    have hU : (U : AnnularRing p) ∈ Ideal.span {T, U} := Ideal.subset_span (by simp)
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hT)
      (Ideal.mul_mem_right _ _ hT)) (Ideal.mul_mem_right _ _ hU)
  · rcases hy with rfl | rfl <;> simp [RingHom.mem_ker]

end TauCeti.AnnularRing
