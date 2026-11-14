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
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.RingTheory.MvPowerSeries.Equiv

/-!
# Power-series presentation, local structure, and boundary quotient of `ℤ_p⟦T, p/T⟧`

The annular coefficient ring `H = ℤ_p⟦T, p/T⟧` (`TauCeti.AnnularRing p`) admits a surjective
`ℤ_p`-algebra homomorphism `evalTU : MvPowerSeries (Fin 2) ℤ_p →ₐ[ℤ_p] AnnularRing p` sending
`X 0 ↦ T` and `X 1 ↦ U = p / T`. Its kernel is the principal ideal `(X 0 * X 1 - p)`, yielding the
canonical presentation

```text
ℤ_p⟦T, U⟧ ⧸ (T U - p)  ≃ₐ[ℤ_p]  AnnularRing p
```

(`TauCeti.AnnularRing.quotientMvPowerSeriesEquiv`). Consequently `AnnularRing p` is a local ring
whose maximal ideal is `(T, U)` (`TauCeti.AnnularRing.maximalIdeal_eq_span_T_U`), with residue
field `𝔽_p` via `x ↦ x.coeff 0 mod p` (`TauCeti.AnnularRing.residueTU`) and unit criterion
`IsUnit x ↔ IsUnit (x.coeff 0)` (`TauCeti.AnnularRing.isUnit_iff`).

Extracting the `U`-coefficients `uCoeff x n = p ^ (-n) * x.coeff (-n) ∈ ℤ_p` shows two structural
features of `H`:
* The formal geometric inverse `(1 - U)⁻¹ = ∑_{n ≥ 0} U ^ n` has constant `U`-coefficients `1`,
  which do not tend to `0` (`TauCeti.AnnularRing.not_tendsto_uCoeff_ofPowerSeriesU_mk_one`), so `H`
  is strictly larger than the `p`-adic completion of `ℤ_p⟦T⟧[p/T]`.
* Reducing `uCoeff` modulo `p` defines a surjective ring homomorphism
  `modT : AnnularRing p →+* (ZMod p)⟦X⟧` (`T ↦ 0`, `U ↦ X`) with kernel `(T) = (p, T)`, giving the
  boundary isomorphism `AnnularRing p ⧸ (T) ≃+* (ZMod p)⟦X⟧`
  (`TauCeti.AnnularRing.quotientSpanTEquiv`) and primality of `(T)`.

## Main definitions

* `TauCeti.AnnularRing.evalTU`: substitution `X 0 ↦ T, X 1 ↦ U` on `MvPowerSeries (Fin 2) ℤ_p`.
* `TauCeti.AnnularRing.quotientMvPowerSeriesEquiv`: the `ℤ_p`-algebra isomorphism
  `MvPowerSeries (Fin 2) ℤ_p ⧸ (X 0 * X 1 - p) ≃ₐ[ℤ_p] AnnularRing p`.
* `TauCeti.AnnularRing.residueTU`: the residue homomorphism `AnnularRing p →+* ZMod p`.
* `TauCeti.AnnularRing.uCoeff`: the `U`-coefficient `b_n ∈ ℤ_p` of `T ^ (-n)` defined by
  `p ^ n * b_n = x.coeff (-n)`.
* `TauCeti.AnnularRing.modT` and `TauCeti.AnnularRing.quotientSpanTEquiv`: the boundary quotient
  `AnnularRing p ⧸ (T) ≃+* (ZMod p)⟦X⟧`.

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

private theorem zpow_p_pos (z : ℤ) : (0 : ℝ) < (p : ℝ) ^ z := zpow_pos p_pos z

private theorem zpow_p_nonneg (z : ℤ) : (0 : ℝ) ≤ (p : ℝ) ^ z := (zpow_p_pos z).le

private theorem p_ne_zero : (p : ℤ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

/-! ### Two-variable power-series evaluation `X 0 ↦ T, X 1 ↦ U` -/

/-- The monomial `T ^ i * U ^ j` is concentrated in degree `i - j` with coefficient `p ^ j`. -/
theorem coeff_T_pow_mul_U_pow (i j : ℕ) (m : ℤ) :
    ((T : AnnularRing p) ^ i * U ^ j).coeff m =
      if m = (i : ℤ) - j then (p : ℤ_[p]) ^ j else 0 := by
  rw [coeff_mul_of_coeff_eq_zero (k := (i : ℤ)) fun r hr ↦ by simp [coeff_T_pow, hr]]
  rw [coeff_T_pow, ite_eq_left rfl, one_mul, coeff_U_pow]
  by_cases hm : m = (i : ℤ) - j
  · rw [ite_eq_left hm, ite_eq_left (by omega)]
  · rw [ite_eq_right hm, ite_eq_right (by omega)]

/-- The `m`-th coefficient of `c • (T ^ d 0 * U ^ d 1)`. -/
private def evalTUTerm (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) (d : Fin 2 →₀ ℕ) : ℤ_[p] :=
  MvPowerSeries.coeff d F * ((T : AnnularRing p) ^ d 0 * U ^ d 1).coeff m

private theorem evalTUTerm_eq_zero_of_ne (F : MvPowerSeries (Fin 2) ℤ_[p]) {m : ℤ}
    {d : Fin 2 →₀ ℕ} (hd : m ≠ (d 0 : ℤ) - d 1) :
    evalTUTerm F m d = 0 := by
  simp [evalTUTerm, coeff_T_pow_mul_U_pow, hd]

private theorem norm_evalTUTerm_le_zpow_neg (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ)
    (d : Fin 2 →₀ ℕ) :
    ‖evalTUTerm F m d‖ ≤ (p : ℝ) ^ (-(d 1 : ℤ)) := by
  rw [evalTUTerm, coeff_T_pow_mul_U_pow]
  split_ifs
  · rw [norm_mul, PadicInt.norm_p_pow]
    exact mul_le_of_le_one_left (zpow_p_nonneg _) (PadicInt.norm_le_one _)
  · rw [mul_zero, norm_zero]
    exact zpow_p_nonneg _

private theorem norm_evalTUTerm_le (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) (d : Fin 2 →₀ ℕ) :
    ‖evalTUTerm F m d‖ ≤ (p : ℝ) ^ min 0 m := by
  by_cases hd : m = (d 0 : ℤ) - d 1
  · exact (norm_evalTUTerm_le_zpow_neg F m d).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega))
  · rw [evalTUTerm_eq_zero_of_ne F hd, norm_zero]
    exact zpow_p_nonneg _

private theorem finTwo_eq_single_add_single (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

private theorem summable_evalTUTerm (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    Summable (evalTUTerm F m) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (p : ℝ) ^ (-(N : ℤ)) < ε := by
    have hp : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hp
    exact ⟨N, by simpa [zpow_neg, zpow_natCast, inv_pow] using hN⟩
  rw [eventually_cofinite]
  refine (Set.finite_Iic (Finsupp.single (0 : Fin 2) (m + N).toNat + Finsupp.single 1 N)).subset
    fun d hd ↦ ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hd
  have hne : m = (d 0 : ℤ) - d 1 := by
    by_contra h
    rw [evalTUTerm_eq_zero_of_ne F h, norm_zero] at hd
    linarith
  have hd1 : d 1 < N := by
    by_contra! hle
    have := (norm_evalTUTerm_le_zpow_neg F m d).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (neg_le_neg (Nat.cast_le.2 hle)))
    linarith
  intro i
  fin_cases i <;> simp <;> omega

/-- The raw evaluation of a two-variable integral power series at `(T, U)`. -/
private def evalTUAux (F : MvPowerSeries (Fin 2) ℤ_[p]) : AnnularRing p :=
  ⟨fun m ↦ ∑' d : Fin 2 →₀ ℕ, evalTUTerm F m d, fun m ↦
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (zpow_p_nonneg _)
      (norm_evalTUTerm_le F m)⟩

private theorem coeff_evalTUAux (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    (evalTUAux F).coeff m = ∑' d : Fin 2 →₀ ℕ, evalTUTerm F m d := (rfl)

/-- Term of the triple convolution sum for `(evalTUAux F * evalTUAux G).coeff m`. -/
private def evalTUMulTerm (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m r : ℤ)
    (d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) : ℤ_[p] :=
  evalTUTerm F r d.1 * evalTUTerm G (m - r) d.2

private theorem summable_evalTUMulTerm (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    Summable (Function.uncurry (evalTUMulTerm F G m)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (p : ℝ) ^ (-(N : ℤ)) < ε := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
    exact ⟨N, by simpa [zpow_neg, zpow_natCast, inv_pow] using hN⟩
  rw [eventually_cofinite]
  let B : Fin 2 →₀ ℕ := Finsupp.single 0 (m + 2 * N).toNat + Finsupp.single 1 N
  refine ((Set.finite_Icc (-(N : ℤ)) (m + 2 * N)).prod
    ((Set.finite_Iic B).prod (Set.finite_Iic B))).subset fun ⟨r, d₁, d₂⟩ h ↦ ?_
  simp only [Set.mem_ofPred_eq, Function.uncurry_apply_pair, dist_zero_right, not_lt] at h
  have hr1 : r = (d₁ 0 : ℤ) - d₁ 1 := by
    by_contra hne
    rw [evalTUMulTerm, evalTUTerm_eq_zero_of_ne F hne, zero_mul, norm_zero] at h
    linarith
  have hr2 : m - r = (d₂ 0 : ℤ) - d₂ 1 := by
    by_contra hne
    rw [evalTUMulTerm, evalTUTerm_eq_zero_of_ne G hne, mul_zero, norm_zero] at h
    linarith
  have hd1 : d₁ 1 < N := by
    by_contra! hle
    have h1 : ‖evalTUMulTerm F G m r (d₁, d₂)‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
      rw [evalTUMulTerm, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans
        ((norm_evalTUTerm_le_zpow_neg F r d₁).trans
          (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (neg_le_neg (Nat.cast_le.2 hle))))
    linarith
  have hd2 : d₂ 1 < N := by
    by_contra! hle
    have h2 : ‖evalTUMulTerm F G m r (d₁, d₂)‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
      rw [evalTUMulTerm, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)).trans
        ((norm_evalTUTerm_le_zpow_neg G (m - r) d₂).trans
          (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (neg_le_neg (Nat.cast_le.2 hle))))
    linarith
  refine ⟨⟨by omega, by omega⟩, fun i ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, B, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp only [Fin.mk_one, Fin.isValue, B, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, B, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp only [Fin.mk_one, Fin.isValue, B, Finsupp.add_apply, Finsupp.single_eq_same]
      omega

private theorem tsum_evalTUMulTerm_col (F G : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ)
    (d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :
    (∑' r : ℤ, evalTUMulTerm F G m r d) =
      MvPowerSeries.coeff d.1 F * MvPowerSeries.coeff d.2 G *
        ((T : AnnularRing p) ^ (d.1 + d.2) 0 * U ^ (d.1 + d.2) 1).coeff m := by
  rw [tsum_eq_single ((d.1 0 : ℤ) - d.1 1) fun r hr ↦ by
    rw [evalTUMulTerm, evalTUTerm_eq_zero_of_ne F hr, zero_mul]]
  simp only [evalTUMulTerm, evalTUTerm, coeff_T_pow_mul_U_pow, ite_true, Finsupp.add_apply]
  by_cases hm : m - ((d.1 0 : ℤ) - d.1 1) = (d.2 0 : ℤ) - d.2 1
  · rw [ite_eq_left hm, ite_eq_left (by omega), pow_add]
    ring
  · rw [ite_eq_right hm, ite_eq_right (by omega)]
    simp

private theorem tsum_prod_eq_tsum_sum_antidiagonal {A : Type*} [AddCommMonoid A]
    [Finset.HasAntidiagonal A] {f : A × A → ℤ_[p]} (hf : Summable f) :
    (∑' x : A × A, f x) = ∑' d : A, ∑ kl ∈ Finset.antidiagonal d, f kl := by
  conv_rhs => enter [1, _]; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.2 hf).tsum_sigma'
    fun _ ↦ (hasSum_fintype _).summable

private theorem evalTUAux_mul (F G : MvPowerSeries (Fin 2) ℤ_[p]) :
    evalTUAux (F * G) = evalTUAux F * evalTUAux G := by
  classical
  ext m : 2
  rw [coeff_mul]
  have hΦ := summable_evalTUMulTerm F G m
  have hcomm : (∑' r : ℤ, (evalTUAux F).coeff r * (evalTUAux G).coeff (m - r)) =
      ∑' d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ), ∑' r : ℤ, evalTUMulTerm F G m r d := by
    rw [hΦ.tsum_comm]
    exact tsum_congr fun r ↦
      (summable_evalTUTerm F r).tsum_mul_tsum (summable_evalTUTerm G (m - r)) (hΦ.prod_factor r)
  have hpair : Summable fun d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦
      MvPowerSeries.coeff d.1 F * MvPowerSeries.coeff d.2 G *
        ((T : AnnularRing p) ^ (d.1 + d.2) 0 * U ^ (d.1 + d.2) 1).coeff m := by
    simpa only [Function.uncurry, Prod.swap_prod_mk, tsum_evalTUMulTerm_col] using hΦ.prod_symm.prod
  rw [hcomm]
  simp_rw [tsum_evalTUMulTerm_col]
  rw [tsum_prod_eq_tsum_sum_antidiagonal hpair, coeff_evalTUAux]
  refine tsum_congr fun d ↦ ?_
  rw [evalTUTerm, MvPowerSeries.coeff_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun kl hkl ↦ by rw [Finset.mem_antidiagonal.1 hkl]

/-- Substitution `X 0 ↦ T, X 1 ↦ U` on two-variable integral power series over `ℤ_p`. -/
def evalTU : MvPowerSeries (Fin 2) ℤ_[p] →ₐ[ℤ_[p]] AnnularRing p where
  toFun := evalTUAux
  map_one' := by
    ext m : 2
    rw [coeff_evalTUAux, tsum_eq_single 0 fun d hd ↦ by
      simp [evalTUTerm, MvPowerSeries.coeff_one, hd]]
    simp [evalTUTerm, coeff_one]
  map_mul' := evalTUAux_mul
  map_zero' := by ext m : 2; simp [coeff_evalTUAux, evalTUTerm]
  map_add' F G := by
    ext m : 2
    rw [coeff_evalTUAux, coeff_add, coeff_evalTUAux, coeff_evalTUAux,
      ← (summable_evalTUTerm F m).tsum_add (summable_evalTUTerm G m)]
    exact tsum_congr fun d ↦ by simp [evalTUTerm, add_mul]
  commutes' c := by
    ext m : 2
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      coeff_evalTUAux, tsum_eq_single 0 fun d hd ↦ by
        rw [evalTUTerm, MvPowerSeries.coeff_C_of_ne_zero hd, zero_mul]]
    rw [evalTUTerm, MvPowerSeries.coeff_zero_C]
    simp [coeff_algebraMap]

@[simp]
theorem evalTU_C (c : ℤ_[p]) : evalTU (MvPowerSeries.C c) = algebraMap ℤ_[p] (AnnularRing p) c :=
  evalTU.commutes c

@[simp]
theorem evalTU_X_zero : evalTU (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℤ_[p]) = T := by
  ext m : 2
  rw [evalTU, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_evalTUAux,
    tsum_eq_single (Finsupp.single 0 1) fun d hd ↦ by
      simp [evalTUTerm, MvPowerSeries.coeff_X, hd]]
  simp [evalTUTerm, MvPowerSeries.coeff_X, coeff_T]

@[simp]
theorem evalTU_X_one : evalTU (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℤ_[p]) = U := by
  ext m : 2
  rw [evalTU, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_evalTUAux,
    tsum_eq_single (Finsupp.single 1 1) fun d hd ↦ by
      simp [evalTUTerm, MvPowerSeries.coeff_X, hd]]
  simp [evalTUTerm, MvPowerSeries.coeff_X, coeff_U]

/-- Diagonal exponent `(m.toNat + k, (-m).toNat + k)` parameterising
`{d : Fin 2 →₀ ℕ | d 0 - d 1 = m}`. -/
def diagIdx (m : ℤ) (k : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m.toNat + k) + Finsupp.single 1 ((-m).toNat + k)

@[simp]
theorem diagIdx_apply_zero (m : ℤ) (k : ℕ) : diagIdx m k 0 = m.toNat + k := by
  simp [diagIdx]

@[simp]
theorem diagIdx_apply_one (m : ℤ) (k : ℕ) : diagIdx m k 1 = (-m).toNat + k := by
  simp [diagIdx]

private theorem diagIdx_injective (m : ℤ) : Function.Injective (diagIdx m) := fun k₁ k₂ h ↦ by
  have h0 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
  simp only [diagIdx_apply_zero] at h0
  omega

private theorem summable_pow_mul_coeff_diagIdx (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    Summable fun k : ℕ ↦ (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine tendsto_zero_of_norm_le_zpow (one_lt_p (p := p))
    (fun k : ℕ ↦ ?_) (f := fun k : ℕ ↦ (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F)
    (g := fun k : ℕ ↦ -(k : ℤ)) ?_
  · rw [norm_mul, PadicInt.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_p_nonneg _) (PadicInt.norm_le_one _)
  · rw [Nat.cofinite_eq_atTop]
    exact Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

/-- Explicit diagonal formula for the `m`-th coefficient of `evalTU F`. -/
theorem coeff_evalTU (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) :
    (evalTU F).coeff m = (p : ℤ_[p]) ^ (-m).toNat *
      ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F := by
  change (evalTUAux F).coeff m = _
  rw [coeff_evalTUAux,
    ← ((summable_pow_mul_coeff_diagIdx F m).hasSum.mul_left ((p : ℤ_[p]) ^ (-m).toNat)).tsum_eq,
    ← (diagIdx_injective m).tsum_eq]
  · refine tsum_congr fun k ↦ ?_
    simp only [evalTUTerm, diagIdx_apply_zero, diagIdx_apply_one, coeff_T_pow_mul_U_pow]
    rw [ite_eq_left (by omega), pow_add]
    ring
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    have hm : m = (d 0 : ℤ) - d 1 := by
      by_contra h
      exact hd (evalTUTerm_eq_zero_of_ne F h)
    refine ⟨min (d 0) (d 1), ?_⟩
    ext i
    fin_cases i <;> (simp [diagIdx]; omega)

@[simp]
theorem evalTU_toMvPowerSeries_zero (f : ℤ_[p]⟦X⟧) :
    evalTU (f.toMvPowerSeries (0 : Fin 2)) = ofPowerSeriesT f := by
  ext m : 2
  rw [coeff_evalTU]
  rcases lt_or_ge m 0 with hm | hm
  · have hzero (k : ℕ) :
        (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) (f.toMvPowerSeries 0) = 0 := by
      rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_right, mul_zero]
      intro h
      have h1 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
      simp at h1
      omega
    simp_rw [coeff_ofPowerSeriesT_of_neg _ hm, hzero, tsum_zero, mul_zero]
  · lift m to ℕ using hm
    rw [coeff_ofPowerSeriesT_natCast, show (-(m : ℤ)).toNat = 0 by omega, pow_zero, one_mul,
      tsum_eq_single 0]
    · rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_left]
      · simp
      · ext i
        fin_cases i <;> simp
    · intro k hk
      rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_right, mul_zero]
      intro h
      have h1 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
      simp at h1
      omega

@[simp]
theorem evalTU_toMvPowerSeries_one (g : ℤ_[p]⟦X⟧) :
    evalTU (g.toMvPowerSeries (1 : Fin 2)) = ofPowerSeriesU g := by
  ext m : 2
  rw [coeff_evalTU]
  rcases lt_or_ge 0 m with hm | hm
  · have hzero (k : ℕ) :
        (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) (g.toMvPowerSeries 1) = 0 := by
      rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_right, mul_zero]
      intro h
      have h0 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
      simp at h0
      omega
    simp_rw [coeff_ofPowerSeriesU_of_pos _ hm, hzero, tsum_zero, mul_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [coeff_ofPowerSeriesU_neg_natCast, show (- -(n : ℤ)).toNat = n by omega,
      tsum_eq_single 0]
    · rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_left]
      · simp
      · ext i
        fin_cases i <;> simp
    · intro k hk
      rw [PowerSeries.coeff_toMvPowerSeries, ite_eq_right, mul_zero]
      intro h
      have h0 := congr_arg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
      simp at h0
      omega

/-- Substitution `X 0 ↦ T, X 1 ↦ U` is surjective: every element is `f(T) + U g(U)`. -/
theorem evalTU_surjective : Function.Surjective (evalTU (p := p)) := fun x ↦ by
  obtain ⟨⟨f, g⟩, hfg⟩ := normalForm.surjective x
  refine ⟨f.toMvPowerSeries 0 + MvPowerSeries.X 1 * g.toMvPowerSeries 1, ?_⟩
  simpa [normalForm_apply] using hfg

/-! ### Kernel of `evalTU` and the presentation `ℤ_p⟦T, U⟧ ⧸ (T U - p)` -/

/-- The kernel of `evalTU` is the principal ideal `(X 0 * X 1 - p)`. -/
theorem ker_evalTU :
    RingHom.ker (evalTU (p := p)).toRingHom =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])} := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · intro F hF
    rw [RingHom.mem_ker] at hF
    have hdiag (m : ℤ) :
        ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (diagIdx m k) F = 0 := by
      have hm := congr_arg (coeff · m) hF
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_evalTU, coeff_zero] at hm
      exact (mul_eq_zero.1 hm).resolve_left (pow_ne_zero _ (p_ne_zero (p := p)))
    let e₁₁ : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
    have hQ_sum (d : Fin 2 →₀ ℕ) :
        Summable fun k : ℕ ↦ (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + (k + 1) • e₁₁) F := by
      refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
      refine tendsto_zero_of_norm_le_zpow (one_lt_p (p := p))
        (f := fun k : ℕ ↦ (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + (k + 1) • e₁₁) F)
        (g := fun k : ℕ ↦ -(k : ℤ)) (fun k ↦ ?_) ?_
      · rw [norm_mul, PadicInt.norm_p_pow]
        exact mul_le_of_le_one_right (zpow_p_nonneg _) (PadicInt.norm_le_one _)
      · rw [Nat.cofinite_eq_atTop]
        exact Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    let Q : MvPowerSeries (Fin 2) ℤ_[p] :=
      fun d ↦ ∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + (k + 1) • e₁₁) F
    rw [Ideal.mem_span_singleton]
    refine ⟨Q, MvPowerSeries.ext fun d ↦ ?_⟩
    have hX01 : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℤ_[p]) =
        MvPowerSeries.monomial e₁₁ 1 := by
      rw [MvPowerSeries.X_def 0, MvPowerSeries.X_def 1, MvPowerSeries.monomial_mul_monomial,
        one_mul]
    rw [sub_mul, map_sub, MvPowerSeries.coeff_C_mul, hX01, MvPowerSeries.coeff_monomial_mul]
    split_ifs with he
    · rw [one_mul]
      set d' := d - e₁₁
      have hd' : d = d' + e₁₁ := (tsub_add_cancel_of_le he).symm
      have hpeel : MvPowerSeries.coeff d' Q =
          MvPowerSeries.coeff d F + (p : ℤ_[p]) * MvPowerSeries.coeff d Q := by
        change (∑' k : ℕ, (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d' + (k + 1) • e₁₁) F) = _
        rw [(hQ_sum d').tsum_eq_zero_add]
        simp only [pow_zero, zero_add, one_nsmul, one_mul, ← hd']
        congr 1
        have hshift (k : ℕ) :
            (p : ℤ_[p]) ^ (k + 1) * MvPowerSeries.coeff (d' + (k + 1 + 1) • e₁₁) F =
              (p : ℤ_[p]) * ((p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + (k + 1) • e₁₁) F) := by
          rw [hd', show d' + (k + 1 + 1) • e₁₁ = d' + e₁₁ + (k + 1) • e₁₁ by
            rw [add_nsmul, one_nsmul, add_assoc, add_comm ((k + 1) • e₁₁) e₁₁, ← add_assoc],
            pow_succ']
          ring
        simp_rw [hshift]
        exact ((hQ_sum d).hasSum.mul_left (p : ℤ_[p])).tsum_eq
      rw [hpeel, add_sub_cancel_right]
    · rw [zero_sub]
      have h01 : d 0 = 0 ∨ d 1 = 0 := by
        by_contra h
        rw [not_or] at h
        refine he fun i ↦ ?_
        fin_cases i <;> simp [e₁₁] <;> omega
      have hd_eq : ∀ k : ℕ, diagIdx ((d 0 : ℤ) - d 1) k = d + k • e₁₁ := fun k ↦ by
        rw [finTwo_eq_single_add_single d]
        ext i
        rcases h01 with h0 | h1
        · fin_cases i <;> simp [diagIdx, e₁₁, h0]
        · fin_cases i <;> simp [diagIdx, e₁₁, h1]
      have h0 := hdiag ((d 0 : ℤ) - d 1)
      simp_rw [hd_eq] at h0
      have hsum : Summable fun k : ℕ ↦ (p : ℤ_[p]) ^ k * MvPowerSeries.coeff (d + k • e₁₁) F := by
        simpa [hd_eq] using summable_pow_mul_coeff_diagIdx F ((d 0 : ℤ) - d 1)
      rw [hsum.tsum_eq_zero_add] at h0
      simp only [pow_zero, zero_nsmul, add_zero, one_mul, pow_succ', mul_assoc] at h0
      rw [((hQ_sum d).hasSum.mul_left (p : ℤ_[p])).tsum_eq] at h0
      exact eq_neg_of_add_eq_zero_left h0
  · rintro _ rfl
    simp [RingHom.mem_ker]

/-- **Power-series presentation of the annular coefficient ring.** `AnnularRing p` is canonically
isomorphic as a `ℤ_p`-algebra to `ℤ_p⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p)`. -/
def quotientMvPowerSeriesEquiv :
    (MvPowerSeries (Fin 2) ℤ_[p] ⧸
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])}) ≃ₐ[ℤ_[p]]
      AnnularRing p :=
  (Ideal.quotientEquivAlgOfEq ℤ_[p] ker_evalTU.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective evalTU_surjective)

@[simp]
theorem quotientMvPowerSeriesEquiv_mk (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    quotientMvPowerSeriesEquiv (Ideal.Quotient.mk _ F) = evalTU F := (rfl)

@[simp]
theorem quotientMvPowerSeriesEquiv_symm_T :
    quotientMvPowerSeriesEquiv.symm (T : AnnularRing p) =
      Ideal.Quotient.mk _ (MvPowerSeries.X 0) := by
  apply quotientMvPowerSeriesEquiv.injective
  simp

@[simp]
theorem quotientMvPowerSeriesEquiv_symm_U :
    quotientMvPowerSeriesEquiv.symm (U : AnnularRing p) =
      Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by
  apply quotientMvPowerSeriesEquiv.injective
  simp

/-! ### Local ring structure, units, and the maximal ideal `(T, U)` -/

instance : IsLocalRing (AnnularRing p) :=
  IsLocalRing.of_surjective' evalTU.toRingHom evalTU_surjective

/-- The residue homomorphism `AnnularRing p →+* ZMod p` sending `x ↦ x.coeff 0 mod p`, killing
`T` and `U`. -/
def residueTU : AnnularRing p →+* ZMod p where
  toFun x := PadicInt.toZMod (x.coeff 0)
  map_one' := by simp [coeff_one]
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    rw [← sub_eq_zero, ← map_mul, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, ← pow_one (p : ℤ_[p]),
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have hsplit : (x * y).coeff 0 - x.coeff 0 * y.coeff 0 =
        ∑' i : ↥(({0} : Finset ℤ) : Set ℤ)ᶜ, x.coeff i * y.coeff (-i) := by
      rw [coeff_mul, ← (summable_coeff_mul_coeff x y 0).sum_add_tsum_compl (s := {0}),
        Finset.sum_singleton, zero_sub, neg_zero, add_sub_cancel_left]
      exact tsum_congr fun i ↦ by rw [zero_sub]
    rw [hsplit]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (zpow_p_nonneg _) fun ⟨i, hi⟩ ↦ ?_
    have hi' : i ≠ 0 := by simpa using hi
    have hexp : min 0 i + min 0 (-i) ≤ -((1 : ℕ) : ℤ) := by omega
    exact (norm_coeff_mul_coeff_le x y i (-i)).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le hexp)

theorem residueTU_apply (x : AnnularRing p) : residueTU x = PadicInt.toZMod (x.coeff 0) := (rfl)

@[simp]
theorem residueTU_T : residueTU (T : AnnularRing p) = 0 := by simp [residueTU_apply, coeff_T]

@[simp]
theorem residueTU_U : residueTU (U : AnnularRing p) = 0 := by simp [residueTU_apply, coeff_U]

@[simp]
theorem residueTU_algebraMap (c : ℤ_[p]) :
    residueTU (algebraMap ℤ_[p] (AnnularRing p) c) = PadicInt.toZMod c := by
  simp [residueTU_apply]

theorem residueTU_surjective : Function.Surjective (residueTU (p := p)) :=
  ZMod.ringHom_surjective residueTU

theorem ker_residueTU :
    RingHom.ker (residueTU (p := p)) = IsLocalRing.maximalIdeal (AnnularRing p) := by
  have : (RingHom.ker (residueTU (p := p))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective residueTU residueTU_surjective
  exact IsLocalRing.eq_maximalIdeal this

/-- **Unit criterion in `AnnularRing p`.** An element is a unit if and only if its constant
coefficient `x.coeff 0` is a `p`-adic unit. -/
theorem isUnit_iff {x : AnnularRing p} : IsUnit x ↔ IsUnit (x.coeff 0) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← ker_residueTU, RingHom.mem_ker, residueTU_apply,
    ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.notMem_maximalIdeal]

theorem not_isUnit_T : ¬ IsUnit (T : AnnularRing p) := by
  simp [isUnit_iff, coeff_T]

theorem not_isUnit_U : ¬ IsUnit (U : AnnularRing p) := by
  simp [isUnit_iff, coeff_U]

theorem not_isUnit_p : ¬ IsUnit (p : AnnularRing p) := by
  rw [isUnit_iff, coeff_natCast, ite_eq_left rfl]
  exact PadicInt.isUnit_iff.not.2 (by rw [PadicInt.norm_p]; exact ne_of_lt (inv_lt_one_of_one_lt₀
    (one_lt_p (p := p))))

/-- **The maximal ideal of `AnnularRing p` is `(T, U)`.** Note `p = T U ∈ (T, U)`. -/
theorem maximalIdeal_eq_span_T_U :
    IsLocalRing.maximalIdeal (AnnularRing p) = Ideal.span {T, U} := by
  rw [← ker_residueTU]
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · intro x hx
    rw [RingHom.mem_ker, residueTU_apply, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
    obtain ⟨c₀, hc₀⟩ := hx
    obtain ⟨⟨f, g⟩, rfl⟩ := normalForm.surjective x
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_normalForm_natCast] at hc₀
    have hf : f = algebraMap ℤ_[p] ℤ_[p]⟦X⟧ (PowerSeries.coeff 0 f) +
        PowerSeries.X * PowerSeries.mk fun n ↦ PowerSeries.coeff (n + 1) f := by
      ext n
      cases n <;> simp
    rw [normalForm_apply, hf, map_add, map_mul, ofPowerSeriesT_X, AlgHom.commutes, hc₀,
      map_mul, map_natCast, ← T_mul_U, mul_assoc]
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rintro y (rfl | rfl) <;> simp [RingHom.mem_ker]

/-! ### `U`-coefficients, formal tails, and the boundary quotient `AnnularRing p ⧸ (T)` -/

/-- The `n`-th `U`-coefficient of `x ∈ AnnularRing p`: the unique `b_n ∈ ℤ_p` such that
`p ^ n * b_n = x.coeff (-n)`. -/
def uCoeff (x : AnnularRing p) (n : ℕ) : ℤ_[p] :=
  (x.pow_dvd_coeff_neg n).choose

@[simp]
theorem pow_mul_uCoeff (x : AnnularRing p) (n : ℕ) :
    (p : ℤ_[p]) ^ n * uCoeff x n = x.coeff (-n) :=
  (x.pow_dvd_coeff_neg n).choose_spec.symm

@[simp]
theorem uCoeff_zero_right (x : AnnularRing p) : uCoeff x 0 = x.coeff 0 := by
  simpa using pow_mul_uCoeff x 0

@[simp]
theorem uCoeff_zero (n : ℕ) : uCoeff (0 : AnnularRing p) n = 0 :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) (by simp)

@[simp]
theorem uCoeff_one (n : ℕ) : uCoeff (1 : AnnularRing p) n = if n = 0 then 1 else 0 := by
  refine mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) ?_
  rw [pow_mul_uCoeff, coeff_one]
  by_cases hn : n = 0 <;> simp [hn]

@[simp]
theorem uCoeff_add (x y : AnnularRing p) (n : ℕ) :
    uCoeff (x + y) n = uCoeff x n + uCoeff y n :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p)))
    (by rw [mul_add, pow_mul_uCoeff, pow_mul_uCoeff, pow_mul_uCoeff, coeff_add])

@[simp]
theorem uCoeff_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) (n : ℕ) :
    uCoeff (ofPowerSeriesU g) n = PowerSeries.coeff n g :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p)))
    (by rw [pow_mul_uCoeff, coeff_ofPowerSeriesU_neg_natCast])

@[simp]
theorem uCoeff_T (n : ℕ) : uCoeff (T : AnnularRing p) n = 0 :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p)))
    (by rw [pow_mul_uCoeff, coeff_T, ite_eq_right (by omega), mul_zero])

@[simp]
theorem uCoeff_U (n : ℕ) : uCoeff (U : AnnularRing p) n = if n = 1 then 1 else 0 := by
  refine mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) ?_
  rw [pow_mul_uCoeff, coeff_U]
  by_cases hn : n = 1 <;> simp [hn]

/-- The `U`-coefficients of the formal inverse `(1 - U)⁻¹ = ∑_{n ≥ 0} U ^ n` are identically `1`
and therefore do not tend to `0`: `AnnularRing p` contains genuine formal tails in `U = p / T`,
unlike the `p`-adic completion of `ℤ_p⟦T⟧[p/T]`. -/
theorem not_tendsto_uCoeff_ofPowerSeriesU_mk_one :
    ¬ Tendsto (uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧))) atTop (𝓝 0) := by
  have h : uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧)) = fun _ ↦ (1 : ℤ_[p]) := by
    ext n
    simp
  rw [h, tendsto_const_nhds_iff]
  exact one_ne_zero

/-- `T` divides `x` in `AnnularRing p` if and only if `p ^ (n + 1) ∣ x.coeff (-n)` for every
`n : ℕ`, equivalently `p ∣ uCoeff x n` for every `n : ℕ`. -/
theorem T_dvd_iff {x : AnnularRing p} :
    (T : AnnularRing p) ∣ x ↔ ∀ n : ℕ, (p : ℤ_[p]) ∣ uCoeff x n := by
  constructor
  · rintro ⟨y, rfl⟩ n
    refine ⟨uCoeff y (n + 1), mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) ?_⟩
    calc (p : ℤ_[p]) ^ n * uCoeff (T * y) n
        = (T * y).coeff (-n) := pow_mul_uCoeff (T * y) n
      _ = y.coeff (-((n + 1 : ℕ) : ℤ)) := by rw [coeff_T_mul]; congr 1; push_cast; ring
      _ = (p : ℤ_[p]) ^ (n + 1) * uCoeff y (n + 1) := (pow_mul_uCoeff y (n + 1)).symm
      _ = (p : ℤ_[p]) ^ n * (p * uCoeff y (n + 1)) := by rw [pow_succ, mul_assoc]
  · intro h
    refine ⟨⟨fun m ↦ x.coeff (m + 1), fun m ↦ ?_⟩, ?_⟩
    · rcases le_or_gt 0 m with hm | hm
      · rw [min_eq_left hm, zpow_zero]
        exact PadicInt.norm_le_one _
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, m + 1 = -n := ⟨(-(m + 1)).toNat, by omega⟩
        obtain ⟨c, hc⟩ := h n
        have hcoeff : x.coeff (m + 1) = (p : ℤ_[p]) ^ (n + 1) * c := by
          rw [hn, ← pow_mul_uCoeff, hc, pow_succ, mul_assoc]
        rw [hcoeff, norm_mul, PadicInt.norm_p_pow, show min 0 m = -((n + 1 : ℕ) : ℤ) by omega]
        exact mul_le_of_le_one_right (zpow_p_nonneg _) (PadicInt.norm_le_one _)
    · ext m : 2
      rw [coeff_T_mul]
      simp

/-- The boundary reduction `AnnularRing p →+* (ZMod p)⟦X⟧` sending `T ↦ 0` and `U ↦ X`, defined
by reducing the `U`-coefficients `uCoeff x n` modulo `p`. -/
def modT : AnnularRing p →+* (ZMod p)⟦X⟧ where
  toFun x := PowerSeries.mk fun n ↦ PadicInt.toZMod (uCoeff x n)
  map_zero' := by ext n; simp
  map_one' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  map_add' x y := by ext n; simp
  map_mul' x y := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, ← sub_eq_zero]
    have hmap : ∑ jk ∈ Finset.antidiagonal n,
          PowerSeries.coeff jk.1 (PowerSeries.mk fun k ↦ PadicInt.toZMod (uCoeff x k)) *
            PowerSeries.coeff jk.2 (PowerSeries.mk fun k ↦ PadicInt.toZMod (uCoeff y k)) =
        PadicInt.toZMod (∑ jk ∈ Finset.antidiagonal n, uCoeff x jk.1 * uCoeff y jk.2) := by
      simp
    rw [hmap, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, ← pow_one (p : ℤ_[p]),
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
    suffices hmul : ‖(p : ℤ_[p]) ^ n *
        (uCoeff (x * y) n - ∑ jk ∈ Finset.antidiagonal n, uCoeff x jk.1 * uCoeff y jk.2)‖ ≤
        (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) by
      rw [norm_mul, PadicInt.norm_p_pow, show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + -((1 : ℕ) : ℤ) by
        omega, zpow_add₀ p_pos.ne'] at hmul
      exact le_of_mul_le_mul_left hmul (zpow_p_pos _)
    rw [mul_sub, pow_mul_uCoeff, Finset.mul_sum]
    have hfin : ∑ jk ∈ Finset.antidiagonal n,
          (p : ℤ_[p]) ^ n * (uCoeff x jk.1 * uCoeff y jk.2) =
        ∑ i ∈ Finset.Icc (-(n : ℤ)) 0, x.coeff i * y.coeff (-(n : ℤ) - i) := by
      symm
      refine Finset.sum_bij (fun i _ ↦ ((-i).toNat, n - (-i).toNat)) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        simp only [Finset.mem_antidiagonal]
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        simp only [Finset.mem_Icc] at hi₁ hi₂
        have h1 := congr_arg Prod.fst h
        simp only at h1
        omega
      · intro ⟨j, k⟩ hjk
        simp only [Finset.mem_antidiagonal] at hjk
        refine ⟨-(j : ℤ), Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
        ext
        · simp
        · simp; omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        dsimp only
        set j := (-i).toNat
        have hi_eq : i = -(j : ℤ) := by omega
        have hni_eq : -(n : ℤ) - -(j : ℤ) = -((n - j : ℕ) : ℤ) := by omega
        have hnj : j + (n - j) = n := by omega
        rw [hi_eq, hni_eq, ← pow_mul_uCoeff, ← pow_mul_uCoeff]
        calc (p : ℤ_[p]) ^ j * uCoeff x j * ((p : ℤ_[p]) ^ (n - j) * uCoeff y (n - j))
            = (p : ℤ_[p]) ^ j * (p : ℤ_[p]) ^ (n - j) * (uCoeff x j * uCoeff y (n - j)) := by ring
          _ = (p : ℤ_[p]) ^ n * (uCoeff x j * uCoeff y (n - j)) := by rw [← pow_add, hnj]
    rw [hfin, coeff_mul,
      ← (summable_coeff_mul_coeff x y (-(n : ℤ))).sum_add_tsum_compl, add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (zpow_p_nonneg _) fun ⟨i, hi⟩ ↦ ?_
    have hi' : i < -(n : ℤ) ∨ 0 < i := by
      rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le, not_le] at hi
      exact hi
    exact (norm_coeff_mul_coeff_le x y i (-(n : ℤ) - i)).trans
      (zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega))

@[simp]
theorem coeff_modT (x : AnnularRing p) (n : ℕ) :
    PowerSeries.coeff n (modT x) = PadicInt.toZMod (uCoeff x n) := by
  simp [modT]

@[simp]
theorem modT_T : modT (T : AnnularRing p) = 0 := by
  ext n
  simp

@[simp]
theorem modT_U : modT (U : AnnularRing p) = PowerSeries.X := by
  ext n
  rw [coeff_modT, PowerSeries.coeff_X, uCoeff_U]
  by_cases hn : n = 1 <;> simp [hn]

@[simp]
theorem modT_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) :
    modT (ofPowerSeriesU g) = PowerSeries.map PadicInt.toZMod g := by
  ext n
  simp

theorem modT_surjective : Function.Surjective (modT (p := p)) := fun φ ↦
  ⟨ofPowerSeriesU (PowerSeries.mk fun n ↦ ((PowerSeries.coeff n φ).val : ℤ_[p])), by
    ext n
    simp⟩

/-- The kernel of `modT : AnnularRing p →+* (ZMod p)⟦X⟧` is `(T)` (which equals `(p, T)`). -/
theorem ker_modT : RingHom.ker (modT (p := p)) = Ideal.span {T} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, T_dvd_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n ↦ ?_
  rw [coeff_modT, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- **Boundary quotient of the annular coefficient ring.** Killing `T` (equivalently `(p, T)`, since
`p = T U`) identifies `AnnularRing p ⧸ (T)` with `(ZMod p)⟦X⟧`, sending `U` to `X`. -/
def quotientSpanTEquiv : (AnnularRing p ⧸ Ideal.span {(T : AnnularRing p)}) ≃+* (ZMod p)⟦X⟧ :=
  (Ideal.quotEquivOfEq ker_modT.symm).trans
    (RingHom.quotientKerEquivOfSurjective modT_surjective)

@[simp]
theorem quotientSpanTEquiv_mk (x : AnnularRing p) :
    quotientSpanTEquiv (Ideal.Quotient.mk _ x) = modT x := (rfl)

/-- The ideal `(T) = (p, T)` in `AnnularRing p` is prime, with quotient `(ZMod p)⟦X⟧`. -/
theorem isPrime_span_T : (Ideal.span {(T : AnnularRing p)}).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).1 quotientSpanTEquiv.toMulEquiv.isDomain

end TauCeti.AnnularRing
