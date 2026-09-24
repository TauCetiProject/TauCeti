/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Cancellation
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
import TauCeti.NumberTheory.Chebotarev.Density.SplitsCompletely
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Surjective
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Orthogonality
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# The continued L-series of a cyclotomic Galois character

For a finite Galois extension `F / K` of number fields and a character `χ` of `Gal(F/K)`,
`cyclotomicCharacterSeriesC K F χ` is a holomorphic continuation of the `L`-series of the ideal
weight `galoisCharacterWeight χ` to the half-plane `Re s > 1 - 1 / [K : ℚ]` when one exists, and
the `L`-series itself otherwise. For every `χ` it agrees with the `L`-series on `Re s > 1`.

For a cyclotomic extension `F = K(μ_m)` and a nontrivial character `χ`, the continuation exists,
so the series is analytic at `s = 1`, and its value at `s = 1` is nonzero. For the trivial
character the series is the Dedekind zeta function of `K` with the Euler factors at the ramified
primes deleted, which continues across `Re s = 1` apart from a single simple pole at `s = 1`.

## Main definitions

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC`: the continued `L`-series of a Galois
  character.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries`: on `Re s > 1` it is the
  `L`-series of `galoisCharacterWeight χ`.
* `NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC`: for `F = K(μ_m)` and
  `χ` nontrivial it is holomorphic on `Re s > 1 - 1 / [K : ℚ]`.
* `NumberField.Chebotarev.analyticAt_cyclotomicCharacterSeriesC_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is analytic at `s = 1`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is nonzero at `s = 1`.
* `NumberField.Chebotarev.exists_differentiableOn_eq_cyclotomicCharacterSeriesC_one_sub`: for the
  trivial character, the series minus its polar part at `s = 1` extends holomorphically to
  `Re s > 1 - 1 / [K : ℚ]`.

## References

* The nonvanishing argument at `s = 1`, in which the logarithm of the product of the `L`-series
  over all characters is a series with nonnegative coefficients that is unbounded as `s → 1⁺`, is
  analogous to `Chebotarev.artinLSeries_one_ne_zero` in AINTLIB (`github.com/CBirkbeck/aintlib`
  at commit `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ZetaProduct.lean`, which proves the nonvanishing at
  `s = 1` of the Artin `L`-series of a nontrivial character of `Gal(K(μ_m)/K)`.
-/

public section

open Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

open scoped Classical in
/-- **The continued `L`-series of a Galois character.** If the `L`-series of
`galoisCharacterWeight χ` has a holomorphic continuation from `Re s > 1` to the half-plane
`Re s > 1 - 1 / [K : ℚ]`, this is a choice of one; otherwise it is the `L`-series itself.

In every case it is the `L`-series on `Re s > 1` (`cyclotomicCharacterSeriesC_eq_LSeries`). For
`F = K(μ_m)` and `χ ≠ 1` the continuation exists, and the function is analytic and nonzero at
`s = 1` (`analyticAt_cyclotomicCharacterSeriesC_one`, `cyclotomicCharacterSeriesC_ne_zero_at_one`).
-/
noncomputable def cyclotomicCharacterSeriesC (χ : (F ≃ₐ[K] F) →* ℂˣ) : ℂ → ℂ :=
  if h : ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
        ∀ s : ℂ, 1 < s.re →
          f s = LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s
  then h.choose
  else LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)

variable {K F}

variable (K F) in
/-- **The continued `L`-series is the `L`-series on `Re s > 1`.** This holds for every Galois
extension `F / K` and every character `χ`, with no cyclotomic hypothesis. -/
@[simp]
theorem cyclotomicCharacterSeriesC_eq_LSeries (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    cyclotomicCharacterSeriesC K F χ s =
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  rw [cyclotomicCharacterSeriesC]
  split_ifs with h
  exacts [h.choose_spec.2 s hs, rfl]

variable (K F) in
/-- **The trivial character: a single simple pole on `Re s = 1`.** For every finite Galois
extension `F / K`, there is a function holomorphic on `Re s > 1 - 1 / [K : ℚ]` that agrees on
`Re s > 1` with the series of the trivial character of `Gal(F/K)` minus `ρ_F / (s - 1)`, where
`ρ_F = dedekindZeta_residue K * ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - N(𝔭) ^ (-1))`. So that series
continues meromorphically to `Re s > 1 - 1 / [K : ℚ]` with a single pole, simple with residue `ρ_F`,
at `s = 1`: the pole of `ζ_K`, corrected by the Euler factors at the ramified primes. -/
theorem exists_differentiableOn_eq_cyclotomicCharacterSeriesC_one_sub : ∃ G : ℂ → ℂ,
    DifferentiableOn ℂ G {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = cyclotomicCharacterSeriesC K F 1 s -
        dedekindZeta_residue K *
          (∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))) / (s - 1) := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K (ramifiedPrimes K F)
  refine ⟨G, hG, fun s hs ↦ ?_⟩
  rw [cyclotomicCharacterSeriesC_eq_LSeries K F 1 hs, MonoidHom.galoisCharacterWeight_one, hGL s hs]

-- The continuation exists for a nontrivial ray class character: for `F = K(μ_m)` and a character
-- `χ` of `Gal(F/K)` with `χ ∘ cyclotomicArtin K F m` nontrivial, the `L`-series of the weight of
-- `χ` has a holomorphic continuation to `Re s > 1 - 1 / [K : ℚ]`.
private theorem exists_differentiableOn_eq_LSeries (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) : ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧ ∀ s : ℂ, 1 < s.re → f s =
        LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  set S := (cyclotomicModulus K m).support
  set w := χ.galoisCharacterUnitaryWeight
  have hcorr : Differentiable ℂ
      fun s : ℂ ↦ ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :=
    Differentiable.fun_finsetProd fun 𝔭 _ ↦ (differentiable_const 1).sub
      ((differentiable_const _).div (differentiable_id.const_cpow (.inl 𝔭.natCast_absNorm_ne_zero))
        fun s ↦ by simp [Complex.cpow_eq_zero_iff, 𝔭.natCast_absNorm_ne_zero])
  -- On `Re s > 0` each local factor `1 - w(𝔭) N(𝔭) ^ (-s)` is nonzero, since `‖w(𝔭)‖ ≤ 1`.
  have hne {s : ℂ} (hs : 0 < s.re) :
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔭 _ ↦ (isUnit_one_sub_of_norm_lt_one <| by
      rw [norm_div, div_lt_one (zero_lt_one.trans (𝔭.one_lt_norm_absNorm_cpow hs))]
      exact (w.norm_le_one _).trans_lt (𝔭.one_lt_norm_absNorm_cpow hs)).ne_zero
  -- The continued `L`-function with the Euler factors at the primes dividing `m` deleted has
  -- cancellation; dividing by those factors, which are nonzero on `Re s > 0`, restores them.
  refine ⟨fun s ↦ continuedLFunctionOfWeight (w.restrict (S : Set _) S.finite_toSet) s /
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s), ?_, fun s hs ↦ ?_⟩
  · refine (differentiableOn_continuedLFunctionOfWeight
      (MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight χ hχ)).div
        hcorr.differentiableOn fun s hs ↦ hne ?_
    -- The half-plane `Re s > 1 - 1 / [K : ℚ]` lies in `Re s > 0`.
    exact (sub_nonneg.mpr <| div_le_one_of_le₀ (Nat.one_le_cast.mpr Module.finrank_pos)
      (Nat.cast_nonneg _)).trans_lt hs
  · dsimp only
    rw [continuedLFunctionOfWeight_restrict_of_one_lt_re w S hs,
      mul_div_cancel_right₀ _ (hne (by linarith)), continuedLFunctionOfWeight_eq_LSeries _ hs,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      MonoidHom.val_galoisCharacterUnitaryWeight]

variable (K F) in
/-- **Holomorphy on `Re s > 1 - 1 / [K : ℚ]`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` is holomorphic on the half-plane
`Re s > 1 - 1 / [K : ℚ]`. -/
theorem differentiableOn_cyclotomicCharacterSeriesC (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (cyclotomicCharacterSeriesC K F χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  -- The Artin map is surjective, so `χ ∘ cyclotomicArtin K F m` is nontrivial.
  have h := exists_differentiableOn_eq_LSeries m χ <| by
    rwa [Ne, ← MonoidHom.one_comp (cyclotomicArtin K F m),
      MonoidHom.cancel_right (cyclotomicArtin_surjective K F m)]
  rw [cyclotomicCharacterSeriesC]
  split_ifs
  exact h.choose_spec.1

variable (K F) in
/-- **Analyticity at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` is analytic at `s = 1`, which lies in the half-plane of
`differentiableOn_cyclotomicCharacterSeriesC`. -/
theorem analyticAt_cyclotomicCharacterSeriesC_one (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F]
    (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) : AnalyticAt ℂ (cyclotomicCharacterSeriesC K F χ) 1 :=
  (differentiableOn_cyclotomicCharacterSeriesC K F m χ hχ).analyticAt <|
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simpa using cancellationExponent_lt_one (K := K))

-- As `s → 1⁺`, the prime sum over the primes of `K` that split completely in `F` tends to infinity.
private theorem tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop :
    Tendsto (fun σ : ℝ ↦ (frobeniusPrimeSet K F 1).primeIdealZetaSum σ) (𝓝[>] 1) atTop := by
  -- The completely split primes have positive density `1 / [F : K]`, and `log (1 / (σ - 1)) → ∞`.
  have hlog := Real.tendsto_log_one_div_sub_atTop 1
  exact (((Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
    (hasDirichletDensity_frobeniusPrimeSet_one K F)).pos_mul_atTop (by simp [Module.finrank_pos])
      hlog).congr' <| (hlog.eventually_gt_atTop 0).mono fun σ hσ ↦ div_mul_cancel₀ _ hσ.ne'

-- At a completely split prime the Frobenius class is trivial, so its chosen representative is `1`.
private theorem artinSymbol_out_eq_one_of_mem_frobeniusPrimeSet_one {P : HeightOneSpectrum (𝓞 K)}
    [P.asIdeal.IsMaximal]
    (hP : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver P.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (h : P ∈ frobeniusPrimeSet K F 1) : (artinSymbol P.asIdeal hP).out = 1 := by
  rw [← isConj_one_left, ← ConjClasses.mk_eq_mk_iff_isConj, ← ConjClasses.one_eq_mk_one,
    ← (mem_frobeniusPrimeSet_iff_artinSymbol_eq hP 1).mp h]
  exact Quotient.out_eq _

-- The character sum of a power of the Galois weights at a prime is a nonnegative real number, and
-- at a completely split prime the sum of the weights themselves is `#Gal(F/K)`.
private theorem exists_sum_galoisCharacterWeight_pow_eq [IsMulCommutative (F ≃ₐ[K] F)]
    (P : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ψ.galoisCharacterWeight P.asIdeal ^ (j + 1) = r ∧
      (P ∈ frobeniusPrimeSet K F 1 → j = 0 → r = Nat.card (F ≃ₐ[K] F)) := by
  classical
  by_cases hP : P ∈ ramifiedPrimes K F
  · -- At a ramified prime every weight vanishes.
    refine ⟨0, le_rfl, ?_, fun h _ ↦ absurd (Finset.mem_coe.mpr hP)
      (frobeniusPrimeSet_subset_compl_ramifiedPrimes 1 h)⟩
    simp [(MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ P).mpr hP]
  · -- At an unramified prime, orthogonality evaluates the sum to `#Gal(F/K)` or `0`.
    rw [mem_ramifiedPrimes_iff, not_not] at hP
    have : P.asIdeal.IsMaximal := P.isMaximal
    refine ⟨if (artinSymbol P.asIdeal hP).out ^ (j + 1) = 1 then Nat.card (F ≃ₐ[K] F) else 0,
      by positivity, by simpa [apply_ite] using
        AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified 1 P hP (j + 1),
      fun h1 hj ↦ ?_⟩
    simp [hj, artinSymbol_out_eq_one_of_mem_frobeniusPrimeSet_one hP h1]

-- For `Re s > 1` the ideal series of a Galois character weight converges absolutely.
private theorem summable_idealTerm_galoisCharacterWeight (ψ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (idealTerm K ψ.galoisCharacterWeight.toIdealArithmeticFunction s) := by
  simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    MonoidHom.val_galoisCharacterUnitaryWeight] using
    summable_idealTerm_of_unitary_of_one_lt_re ψ.galoisCharacterUnitaryWeight hs

-- For `σ > 1`, summing over the characters the Euler-product logarithm series of their `L`-series
-- gives the real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`, where `r(P, e)` is
-- the character sum of the `(e + 1)`-th powers of the weights at `P`.
private theorem hasSum_sum_taylorSeries_galoisCharacterWeight {r : HeightOneSpectrum (𝓞 K) → ℕ → ℝ}
    (hr : ∀ P j, ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ψ.galoisCharacterWeight P.asIdeal ^ (j + 1) = r P j)
    {σ : ℝ} (hσ : 1 < σ) : HasSum (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      ((r pe.1 pe.2 / ((Ideal.absNorm pe.1.asIdeal : ℝ) ^ σ) ^ (pe.2 + 1) / (pe.2 + 1) : ℝ) : ℂ))
      (∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (ψ.galoisCharacterWeight pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ : ℂ)) ^
          (pe.2 + 1) / ((pe.2 : ℂ) + 1)) := by
  have hs (ψ : (F ≃ₐ[K] F) →* ℂˣ) :=
    summable_idealTerm_galoisCharacterWeight ψ (s := σ) (by simpa using hσ)
  refine (hasSum_sum fun (ψ : (F ≃ₐ[K] F) →* ℂˣ) _ ↦ (Complex.summable_taylorSeries_neg_log
    (ψ.galoisCharacterWeight.summable_div_of_summable_idealTerm (hs ψ))
    (ψ.galoisCharacterWeight.norm_div_lt_one_of_summable_idealTerm (hs ψ))).hasSum).congr_fun
    fun pe ↦ ?_
  simp [div_pow, ← Finset.sum_div, hr, Complex.ofReal_cpow]

-- For `F / K` abelian, the product over all characters `ψ` of `Gal(F/K)` of the `L`-series of
-- `galoisCharacterWeight ψ` tends to infinity in norm as `s → 1⁺` along the reals.
private theorem tendsto_norm_prod_LSeries_atTop [IsMulCommutative (F ≃ₐ[K] F)] :
    Tendsto (fun σ : ℝ ↦ ‖∏ ψ : (F ≃ₐ[K] F) →* ℂˣ,
      LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ‖)
      (𝓝[>] 1) atTop := by
  -- The Euler-product logarithms of all the `L`-series sum to a series of nonnegative reals,
  -- which dominates `#Gal(F/K)` times the prime sum over the completely split primes.
  choose r hr0 hr hrn using exists_sum_galoisCharacterWeight_pow_eq (K := K) (F := F)
  -- The real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`.
  let ρ : ℝ → HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun σ pe ↦
    r pe.1 pe.2 / ((Ideal.absNorm pe.1.asIdeal : ℝ) ^ σ) ^ (pe.2 + 1) / (pe.2 + 1)
  have hρ0 (σ : ℝ) (pe) : 0 ≤ ρ σ pe := by
    have := hr0 pe.1 pe.2
    positivity
  refine tendsto_atTop_mono' _ ?_
    ((tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop (K := K) (F := F)).const_mul_atTop
      (Nat.cast_pos.mpr Nat.card_pos : (0 : ℝ) < Nat.card (F ≃ₐ[K] F)))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have hsum := hasSum_sum_taylorSeries_galoisCharacterWeight hr hσ
  -- The product of the `L`-series is the exponential of the real series.
  rw [← Finset.prod_congr rfl fun ψ _ ↦ MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries _
      (summable_idealTerm_galoisCharacterWeight ψ (s := σ) (by simpa using hσ)),
    ← Complex.exp_sum, ← hsum.tsum_eq, ← Complex.ofReal_tsum, Complex.norm_exp_ofReal,
    Set.primeIdealZetaSum_def, ← tsum_mul_left]
  refine le_trans ?_ ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  refine le_of_eq_of_le (tsum_congr fun P ↦ ?_) (tsum_comp_le_tsum_of_inj
    (Complex.summable_ofReal.mp hsum.summable) (hρ0 σ)
    (i := fun P : frobeniusPrimeSet K F 1 ↦ (P.1, 0)) fun P Q h ↦ Subtype.ext (congrArg Prod.fst h))
  simp [hrn P.1 0 P.2 rfl, Real.rpow_neg, div_eq_mul_inv]

open scoped Classical in
-- If the continued `L`-series of `χ ≠ 1` vanishes at `1`, then as `σ → 1⁺` the `L`-series of every
-- character converges after renormalising: that of the trivial character multiplied by `σ - 1`,
-- that of `χ` divided by `σ - 1`, and the others unchanged.
private theorem exists_tendsto_mulSingle_mul_LSeries (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] {χ : (F ≃ₐ[K] F) →* ℂˣ} (hχ : χ ≠ 1)
    (h0 : cyclotomicCharacterSeriesC K F χ 1 = 0) (ψ : (F ≃ₐ[K] F) →* ℂˣ) :
    ∃ z, Tendsto (fun σ : ℝ ↦ Pi.mulSingle (M := fun _ ↦ ℂ) 1 ((σ : ℂ) - 1) ψ *
      Pi.mulSingle (M := fun _ ↦ ℂ) χ ((σ : ℂ) - 1)⁻¹ ψ *
        LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ) (𝓝[>] 1)
      (𝓝 z) := by
  have hray : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    Complex.ofReal_one ▸ Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      fun σ (hσ : 1 < σ) ↦ Complex.ofReal_injective.ne hσ.ne'
  have hL : ∀ᶠ σ : ℝ in 𝓝[>] 1, cyclotomicCharacterSeriesC K F ψ σ =
      LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ :=
    eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦
      cyclotomicCharacterSeriesC_eq_LSeries K F ψ (by simpa using hσ)
  by_cases h1 : ψ = 1
  · -- The trivial character's `L`-series has a simple pole at `1`.
    subst h1
    exact ⟨_, (tendsto_sub_one_mul_LSeries_ofBadPrimes (ramifiedPrimes K F)).congr fun σ ↦ by
      simp [Ne.symm hχ]⟩
  have hana := analyticAt_cyclotomicCharacterSeriesC_one K F m ψ h1
  by_cases h2 : ψ = χ
  · -- The series of `χ` vanishes at `1`, so dividing by `σ - 1` gives a difference quotient.
    subst h2
    refine ⟨_, ((hasDerivAt_iff_tendsto_slope.mp hana.differentiableAt.hasDerivAt).comp
      hray).congr' ?_⟩
    filter_upwards [hL] with σ hσ
    simp [slope_def_field, h0, hσ, h1, div_eq_inv_mul]
  · -- Any other series is continuous at `1`.
    refine ⟨_, (hana.continuousAt.tendsto.comp (hray.mono_right nhdsWithin_le_nhds)).congr' ?_⟩
    filter_upwards [hL] with σ hσ
    simp [h1, h2, hσ]

variable (K F) in
/-- **Nonvanishing at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` does not vanish at `s = 1`. -/
theorem cyclotomicCharacterSeriesC_ne_zero_at_one (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F]
    (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) : cyclotomicCharacterSeriesC K F χ 1 ≠ 0 := by
  intro h0
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  -- The product of all the `L`-series is unbounded as `σ → 1⁺`. But the trivial character's
  -- series times `σ - 1` converges, the series of `χ` divided by `σ - 1` converges since it
  -- vanishes at `1`, and the other series converge, so the product converges.
  choose z hz using exists_tendsto_mulSingle_mul_LSeries m hχ h0
  refine not_tendsto_atTop_of_tendsto_nhds (tendsto_finsetProd Finset.univ fun ψ _ ↦ hz ψ).norm
    ((tendsto_norm_prod_LSeries_atTop (K := K) (F := F)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  -- The renormalising factors multiply to `(σ - 1) * (σ - 1)⁻¹ = 1`.
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hσ.ne')
  simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hσ1]

end NumberField.Chebotarev
