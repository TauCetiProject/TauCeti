/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Series
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Nonvanishing
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Nonvanishing
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.CharacterExpansion
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Partition
import TauCeti.NumberTheory.LSeries.WienerIkehara.SharpCutoff

/-!
# Weighted Chebotarev for cyclotomic extensions

Let `F = K(μ_m)` be a cyclotomic extension of a number field `K`, with group `G = Gal(F/K)`. This
file proves the prime-number-theorem form of Chebotarev's theorem for `F / K`: for every `σ ∈ G`,

```text
ψ_σ(x) = x / #G + o(x),
```

where `ψ_σ = frobeniusPsi K F (ConjClasses.mk σ)` counts the prime powers `𝔭 ^ j` of `K` with
`𝔭` unramified in `F` and `Frob(𝔭) ^ j = σ`, weighted by `log N𝔭`. Taking `F = K` gives the
prime ideal theorem `ψ_K(x) = x + o(x)` for every number field `K`.

The proof applies the Wiener--Ikehara theorem `TauCeti.LSeries.wienerIkehara` to the nonnegative
coefficients of `ψ_σ`. By the character expansion
`NumberField.Chebotarev.LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv`, their Dirichlet series
is `(1 / #G) ∑_χ χ(σ)⁻¹ (-L_χ'(s) / L_χ(s))` on `Re s > 1`, where `L_χ` is the `L`-series of the
Galois character weight of `χ`. The required boundary behaviour on `Re s ≥ 1` comes term by term:

* for `χ ≠ 1`, the continued series `cyclotomicCharacterSeriesC K F χ` is holomorphic across
  `Re s = 1` and nonzero on `Re s ≥ 1`, so `-L_χ'/L_χ` extends continuously to `Re s ≥ 1`;
* for `χ = 1`, `L_1` is the Dedekind zeta function of `K` with the Euler factors at the ramified
  primes deleted. The function `H(s) = (s - 1) L_1(s)` continues holomorphically across
  `Re s = 1`, takes the value `ρ = Res_{s=1} ζ_K · ∏_{𝔭 ramified} (1 - N𝔭⁻¹) ≠ 0` at `s = 1`, and
  does not vanish elsewhere on `Re s ≥ 1`. Hence `-L_1'/L_1 - 1/(s - 1) = -H'/H` extends
  continuously to `Re s ≥ 1`.

So the Frobenius von Mangoldt series of `σ` minus `(1 / #G) / (s - 1)` extends continuously to
`Re s ≥ 1`, which is exactly the Wiener--Ikehara hypothesis with residue `1 / #G`.

## Main results

* `NumberField.Chebotarev.logDeriv_cyclotomicCharacterSeriesC`: on `Re s > 1` the logarithmic
  derivative of the continued series is that of the `L`-series.
* `NumberField.Chebotarev.continuousOn_logDeriv_cyclotomicCharacterSeriesC`: for `F = K(μ_m)`
  and `χ ≠ 1`, the logarithmic derivative of the continued series is continuous on `Re s ≥ 1`.
* `NumberField.Chebotarev.exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub`:
  for every finite Galois `F / K`, `-L_1'(s) / L_1(s) - 1 / (s - 1)` extends continuously to
  `Re s ≥ 1`.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_isCyclotomicExtension`: for `F = K(μ_m)`,
  `ψ_σ(x) = x / #Gal(F/K) + o(x)`.
* `NumberField.Chebotarev.primePsi_univ_asymptotic`: the prime ideal theorem
  `ψ_K(x) = x + o(x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* The regularization of the trivial character by the entire function `(s - 1) L(s)` follows
  Mathlib's `DirichletCharacter.LFunctionTrivChar₁` and
  `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`
  (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`), used there for Dirichlet's theorem
  on primes in arithmetic progressions.
-/

public section

open Asymptotics Complex Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

namespace NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

-- The closed half-plane `Re s ≥ 1` lies in the open half-plane `Re s > 1 - 1 / [K : ℚ]` of the
-- continued series.
private theorem setOf_one_le_re_subset :
    {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := fun _ hs ↦
  (sub_lt_self (1 : ℝ) (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))).trans_le hs

variable (K F) in
/-- **The logarithmic derivative on `Re s > 1`.** For every finite Galois extension `F / K` and
every character `χ` of `Gal(F/K)`, the logarithmic derivative of the continued series
`cyclotomicCharacterSeriesC K F χ` is that of the `L`-series of `galoisCharacterWeight χ` on
`Re s > 1`, where the two functions agree on a neighbourhood. -/
theorem logDeriv_cyclotomicCharacterSeriesC (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (cyclotomicCharacterSeriesC K F χ) s =
      logDeriv (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)) s :=
  (logDeriv_congr_nhds <| eventually_of_mem
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)
      fun _ hz ↦ cyclotomicCharacterSeriesC_eq_LSeries K F χ hz).eq_of_nhds

variable (K F) in
/-- **Continuity of the logarithmic derivative on `Re s ≥ 1`.** For `F = K(μ_m)` and a nontrivial
character `χ` of `Gal(F/K)`, the logarithmic derivative of the continued series of `χ` is
continuous on the closed half-plane `Re s ≥ 1`: the series is holomorphic on a neighbourhood of it
and does not vanish on it. -/
theorem continuousOn_logDeriv_cyclotomicCharacterSeriesC (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    ContinuousOn (logDeriv (cyclotomicCharacterSeriesC K F χ)) {s | 1 ≤ s.re} := by
  have hd := differentiableOn_cyclotomicCharacterSeriesC K F m χ hχ
  refine ((hd.deriv (isOpen_lt continuous_const continuous_re)).continuousOn.mono
    setOf_one_le_re_subset).div (hd.continuousOn.mono setOf_one_le_re_subset)
      fun s (hs : 1 ≤ s.re) ↦ ?_
  rcases hs.lt_or_eq with hs | hs
  · rw [cyclotomicCharacterSeriesC_eq_LSeries K F χ hs]
    exact χ.LSeries_galoisCharacterWeight_ne_zero hs
  · exact cyclotomicCharacterSeriesC_ne_zero_of_re_eq_one m χ hχ hs.symm

variable (K F) in
/-- **The regularized boundary function of the trivial character.** Let `F / K` be a finite
Galois extension and `L_1` the `L`-series of the trivial character of `Gal(F/K)`, that is the
Dedekind zeta function of `K` with the Euler factors at the primes ramified in `F` deleted. Then
`-L_1'(s) / L_1(s) - 1 / (s - 1)` extends from `Re s > 1` to a function continuous on
`Re s ≥ 1`. -/
theorem exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub : ∃ G : ℂ → ℂ,
    ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      G s = -logDeriv (LSeries (normCoeff K
        (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)) s -
          1 / (s - 1) := by
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_cyclotomicCharacterSeriesC_one_sub K F
  set U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set ρ := (dedekindZeta_residue K : ℂ) *
    ∏ 𝔭 ∈ ramifiedPrimes K F, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-1 : ℂ))
  set L₁ := LSeries (normCoeff K
    (1 : (F ≃ₐ[K] F) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction)
  -- The residue `ρ` of `L₁` at `s = 1` is nonzero: every deleted Euler factor is nonzero at `1`.
  have hρ : ρ ≠ 0 := by
    refine mul_ne_zero (ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K))
      (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ ↦ ?_)
    rw [cpow_neg_one, sub_ne_zero, ne_comm, Ne, inv_eq_one, Nat.cast_eq_one,
      Ideal.absNorm_eq_one_iff]
    exact 𝔭.isPrime.ne_top
  -- `H(s) = (s - 1) L₁(s)` continues holomorphically to `U`, with value `ρ` at `s = 1`.
  set H : ℂ → ℂ := fun s ↦ (s - 1) * G s + ρ
  have hH : DifferentiableOn ℂ H U := ((differentiableOn_id.sub_const 1).mul hG).add_const ρ
  have hsub {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ by simp [h] at hs
  have hHL {s : ℂ} (hs : 1 < s.re) : H s = (s - 1) * L₁ s := by
    simp only [H, hGL s hs, cyclotomicCharacterSeriesC_eq_LSeries K F 1 hs, L₁]
    field_simp [hsub hs]
    ring
  -- `H` does not vanish on `Re s ≥ 1`.
  have hH0 {s : ℂ} (hs : 1 ≤ s.re) : H s ≠ 0 := by
    rcases hs.lt_or_eq with hs | hs
    · rw [hHL hs]
      exact mul_ne_zero (hsub hs) (MonoidHom.LSeries_galoisCharacterWeight_ne_zero 1 hs)
    rcases eq_or_ne s 1 with rfl | hs1
    · simpa [H] using hρ
    -- Elsewhere on the line, `H(s) / (s - 1)` is a continuation of `L₁` differentiable at `s`.
    have hne := ne_zero_of_eqOn_LSeries_galoisCharacterWeight_one (K := K) (F := F)
      (f := fun z ↦ H z / (z - 1)) hs.symm hs1
      ((hH.differentiableAt (hU.mem_nhds (setOf_one_le_re_subset hs.le))).div
        (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
      fun z (hz : 1 < z.re) ↦ by
        simp only [hHL hz, mul_div_cancel_left₀ _ (hsub hz), L₁]
    exact fun h ↦ hne (by simp [h])
  refine ⟨fun s ↦ -logDeriv H s, ?_, fun s hs ↦ ?_⟩
  · simp only [logDeriv_apply]
    exact (((hH.deriv hU).continuousOn.mono setOf_one_le_re_subset).div
      (hH.continuousOn.mono setOf_one_le_re_subset) fun _ hs ↦ hH0 hs).neg
  -- On `Re s > 1`, `L₁ = H / (s - 1)` near `s`, so `L₁'/L₁ = H'/H - 1 / (s - 1)`.
  have hHs : DifferentiableAt ℂ H s :=
    hH.differentiableAt (hU.mem_nhds (setOf_one_le_re_subset hs.le))
  have hL : logDeriv L₁ s = logDeriv (H / fun z ↦ z - 1) s :=
    (logDeriv_congr_nhds <| eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs) fun z (hz : 1 < z.re) ↦ by
        simp only [Pi.div_apply, hHL hz, mul_div_cancel_left₀ _ (hsub hz)]).eq_of_nhds
  dsimp only
  rw [hL, logDeriv_div (g := fun z ↦ z - 1) s (hH0 hs.le) (hsub hs) hHs
    (differentiableAt_id.sub_const 1), logDeriv_apply (· - 1), deriv_sub_const, deriv_id'']
  ring

variable (K F) in
/-- **Weighted Chebotarev for cyclotomic extensions.** For `F = K(μ_m)` and `σ ∈ Gal(F/K)`, the
Frobenius `ψ` function of `σ` satisfies `ψ_σ(x) = x / #Gal(F/K) + o(x)`.

This is the Wiener--Ikehara theorem for the nonnegative coefficients of `ψ_σ`, whose Dirichlet
series is a combination of the logarithmic derivatives of the character series of `Gal(F/K)`. -/
theorem frobeniusPsi_asymptotic_of_isCyclotomicExtension (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (σ : F ≃ₐ[K] F) :
    (fun x : ℝ ↦ frobeniusPsi K F (ConjClasses.mk σ) x -
      (1 / Nat.card (F ≃ₐ[K] F) : ℝ) * x) =o[atTop] fun x : ℝ ↦ x := by
  classical
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  obtain ⟨G₁, hG₁, hG₁L⟩ := exists_continuousOn_eq_neg_logDeriv_galoisCharacterWeight_one_sub K F
  -- The boundary function of the character `χ`: the regularized one for `χ = 1`, and the negative
  -- logarithmic derivative of the continued series otherwise.
  let Φ : ((F ≃ₐ[K] F) →* ℂˣ) → ℂ → ℂ := fun χ ↦
    if χ = 1 then G₁ else fun s ↦ -logDeriv (cyclotomicCharacterSeriesC K F χ) s
  have hΦ (χ : (F ≃ₐ[K] F) →* ℂˣ) : ContinuousOn (Φ χ) {s | 1 ≤ s.re} := by
    by_cases hχ : χ = 1
    · simpa [Φ, hχ] using hG₁
    · simp only [Φ, hχ, ↓reduceIte]
      exact (continuousOn_logDeriv_cyclotomicCharacterSeriesC K F m χ hχ).neg
  have hΦL (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) : Φ χ s =
      -logDeriv (LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)) s -
        if χ = 1 then 1 / (s - 1) else 0 := by
    by_cases hχ : χ = 1
    · subst hχ
      simp [Φ, hG₁L s hs]
    · simp [Φ, hχ, logDeriv_cyclotomicCharacterSeriesC K F χ hs]
  have hmain := LSeries.wienerIkehara (a := frobeniusVonMangoldtCoeff K F (ConjClasses.mk σ))
    (κ := 1 / Nat.card (F ≃ₐ[K] F))
    (G := fun s ↦ (Nat.card (F ≃ₐ[K] F) : ℂ)⁻¹ * ∑ χ, (((χ σ)⁻¹ : ℂˣ) : ℂ) * Φ χ s)
    (frobeniusVonMangoldtCoeff_nonneg _)
    (fun s hs ↦ (LSeriesSummable_frobeniusVonMangoldtCoeff _ hs).LSeriesHasSum)
    (continuousOn_const.mul (continuousOn_finsetSum _ fun χ _ ↦ continuousOn_const.mul (hΦ χ)))
    fun s hs ↦ by
      -- Only the trivial character contributes to the pole, with coefficient `1 / #G`.
      simp only [LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv σ hs, hΦL _ hs, mul_sub,
        Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      push_cast
      ring
  refine (isLittleO_iff_tendsto' ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦
    (hx hzero).elim)).2 ?_
  have h := hmain.sub_const (1 / Nat.card (F ≃ₐ[K] F) : ℝ)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  rw [frobeniusPsi_eq_sum_range, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊), Finset.sum_insert (by simp),
    frobeniusVonMangoldtCoeff_eq_zero_of_not_isPrimePow _ not_isPrimePow_zero, zero_add, zero_add]
  field_simp

open scoped Classical in
variable (K) in
/-- **The prime ideal theorem, for Chebyshev's `ψ`.** For every number field `K`, the von Mangoldt
summatory function `ψ_K(x) = ∑_{N𝔭^j ≤ x} log N𝔭` of `K` satisfies `ψ_K(x) = x + o(x)`.

This is the case `F = K = K(μ_1)` of `frobeniusPsi_asymptotic_of_isCyclotomicExtension`: the
trivial extension `K / K` has no ramified primes and a single Frobenius class, whose `ψ` function
is `ψ_K`. -/
theorem primePsi_univ_asymptotic :
    (fun x : ℝ ↦ primePsi K Set.univ x - x) =o[atTop] fun x : ℝ ↦ x := by
  have : IsCyclotomicExtension {1} K K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective fun x ↦ ⟨x, rfl⟩
  have hψ := frobeniusPsi_asymptotic_of_isCyclotomicExtension K K 1 1
  have hsum := (primePsi_univ_sub_sum_frobeniusPsi_isBigO_log K K).trans_isLittleO
    Real.isLittleO_log_id_atTop
  -- `Gal(K/K)` is trivial, so it has a single conjugacy class.
  have : Subsingleton (ConjClasses (K ≃ₐ[K] K)) := ⟨fun C D ↦ by
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
    obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective D
    rw [Subsingleton.elim a b]⟩
  refine (hsum.add hψ).congr (fun x ↦ ?_) fun _ ↦ rfl
  rw [Fintype.sum_subsingleton _ (ConjClasses.mk 1), Nat.card_unique]
  ring

end NumberField.Chebotarev
