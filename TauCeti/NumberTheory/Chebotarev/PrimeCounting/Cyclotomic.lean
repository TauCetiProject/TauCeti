/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Nonvanishing
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt
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

* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_isCyclotomicExtension`: for `F = K(μ_m)`,
  `ψ_σ(x) = x / #Gal(F/K) + o(x)`.
* `NumberField.Chebotarev.primePsi_univ_asymptotic`: the prime ideal theorem
  `ψ_K(x) = x + o(x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* The regularization `(s - 1) L(s)`, holomorphic near `Re s ≥ 1`, follows
  Mathlib's `DirichletCharacter.LFunctionTrivChar₁` and
  `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`
  (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`), used there for Dirichlet's theorem
  on primes in arithmetic progressions.
* The character-sum boundary function follows Mathlib's
  `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux` and its continuity and agreement
  theorems in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.
-/

public section

open Asymptotics Complex Filter IsDedekindDomain NumberField TauCeti
open scoped Topology

namespace NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

variable (K F) in
/-- **Weighted Chebotarev for cyclotomic extensions.** For `F = K(μ_m)` and `σ ∈ Gal(F/K)`, the
Frobenius `ψ` function of `σ` satisfies `ψ_σ(x) = x / #Gal(F/K) + o(x)`. -/
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
  rw [frobeniusPsi_eq_sum_Icc]
  field_simp

open scoped Classical in
variable (K) in
/-- **The prime ideal theorem, for Chebyshev's `ψ`.** For every number field `K`, the von Mangoldt
summatory function `ψ_K(x) = ∑_{N𝔭^j ≤ x} log N𝔭` of `K` satisfies `ψ_K(x) = x + o(x)`. -/
theorem primePsi_univ_asymptotic :
    (fun x : ℝ ↦ primePsi K Set.univ x - x) =o[atTop] fun x : ℝ ↦ x := by
  have : IsCyclotomicExtension {1} K K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective fun x ↦ ⟨x, rfl⟩
  have hψ := frobeniusPsi_asymptotic_of_isCyclotomicExtension K K 1 1
  have hsum := (primePsi_univ_sub_sum_frobeniusPsi_isBigO_log K K).trans_isLittleO
    Real.isLittleO_log_id_atTop
  -- `Gal(K/K)` is trivial, so it has a single conjugacy class.
  have : Subsingleton (ConjClasses (K ≃ₐ[K] K)) := Quot.Subsingleton
  refine (hsum.add hψ).congr (fun x ↦ ?_) fun _ ↦ rfl
  rw [Fintype.sum_subsingleton _ (ConjClasses.mk 1), Nat.card_unique]
  ring

end NumberField.Chebotarev
