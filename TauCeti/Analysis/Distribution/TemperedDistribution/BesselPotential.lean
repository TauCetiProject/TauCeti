/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Bessel potentials on Littlewood–Paley blocks

The Bessel potential `J^s = 𝓕⁻ (1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕` of order `s` acts on a function whose
Fourier transform lives at frequencies `‖ξ‖ ~ R` essentially as multiplication by `R ^ s`. This file
makes that precise at the level of convolution kernels, which is what gives the localized estimates

`‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖Δⱼ u‖_p`, `1 ≤ p ≤ ∞`,

for the inhomogeneous Littlewood–Paley blocks `Δⱼ` with a constant independent of `j` and `p`. These
estimates compare the Bessel-potential spaces `H^{s,p}` with the Besov spaces `B^s_{p,q}`, whose
norms are weighted sequence norms of the `‖Δⱼ u‖_p`.

* `TauCeti.exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le`: let `χ` be a smooth cutoff
  supported where `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`, with `‖D^k χ‖ ≤ B_k R ^ (-k)`. Then the kernel of the
  symbol `(1 + ‖ξ‖ ^ 2) ^ (s / 2) χ ξ` has `L¹` norm at most `C R ^ s`, with `C` independent of `R`
  and `χ`. Since the bracket power is a symbol of order `s`, the product is a band-limited symbol at
  scale `R` with constant `O(R ^ s)`, and the scale-invariant `L¹` bound
  `SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset` applies.
* `TemperedDistribution.exists_besselPotential_compL_littlewoodPaleyBlock_eq`: there is `C` such
  that for every `j` the operator `J^s Δⱼ` factors as `T_{σⱼ} Δⱼ`, where `T_{σⱼ}` is the Fourier
  multiplier by a Schwartz symbol `σⱼ` whose kernel satisfies `‖𝓕⁻ σⱼ‖₁ ≤ C 2^{js}`. The symbol
  is `σⱼ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) Ψⱼ` for the enlarged cutoff `Ψⱼ`
  (`ContDiffBump.enlargedLittlewoodPaley`), which equals `1` on the support of the piece `ψⱼ`.

A Fourier multiplier with Schwartz symbol `σ` is the convolution with `𝓕⁻ σ`, so Young's
inequality bounds it on every `Lᵖ` by `‖𝓕⁻ σ‖₁`. Applying that bound to `Δⱼ u` turns the
factorization into the localized estimates above; the `Lᵖ` bound itself is not proved here.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2.
-/

public section

open scoped FourierTransform SchwartzMap LineDeriv ContDiff
open FourierTransform MeasureTheory Metric Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

namespace TauCeti

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Where `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2`, every power `(1 + ‖ξ‖ ^ 2) ^ (u / 2)` of the Japanese
bracket is at most `max (a ^ (u / 2)) (b ^ (u / 2)) R ^ u`. -/
private theorem one_add_norm_sq_rpow_half_le {a b R : ℝ} (ha : 0 < a) (hR : 0 < R) {ξ : E}
    (hξ : a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) (u : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ max (a ^ (u / 2)) (b ^ (u / 2)) * R ^ u := by
  have hb : 0 < b := pos_of_mul_pos_left ((mul_pos ha (by positivity)).trans_le
    (hξ.1.trans hξ.2)) (by positivity)
  have hRu (c : ℝ) (hc : 0 < c) : (c * R ^ 2) ^ (u / 2) = c ^ (u / 2) * R ^ u := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 2
    push_cast
    ring
  rcases le_total 0 u with hu | hu
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (b * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow (by positivity) hξ.2 (by positivity)
      _ ≤ _ := by
          rw [hRu b hb]
          gcongr
          exact le_max_right _ _
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (a * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hξ.1 (by linarith)
      _ ≤ _ := by
          rw [hRu a ha]
          gcongr
          exact le_max_left _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Bessel-weighted dyadic cutoffs are symbols of order `s` at scale `R`.** Let `a > 0`, `b`,
`N` and `B : ℕ → ℝ`. There is a constant `K ≥ 0` with the following property. Let `R > 0` and let
`χ` be a smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and
`‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then `‖D^k ((1 + ‖·‖ ^ 2) ^ (s / 2) χ)‖ ≤ K R ^ s / R ^ k` for
`k ≤ N`. -/
private theorem exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le (s : ℝ) {a b : ℝ}
    (ha : 0 < a) (N : ℕ) (B : ℕ → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) → ∀ k ≤ N, ∀ ξ,
        ‖iteratedFDeriv ℝ k (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ) ξ‖ ≤ K * R ^ s / R ^ k := by
  -- Derivative bounds for the weight `w ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2)`, a symbol of order `s`.
  choose W hW using fun i : ℕ ↦ exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := E)
    (s / 2) i
  have hW0 (i : ℕ) : 0 ≤ W i := by simpa using (norm_nonneg _).trans (hW i 0)
  set P : ℕ → ℝ := fun i ↦ max (a ^ ((s - i) / 2)) (b ^ ((s - i) / 2))
  have hP0 (i : ℕ) : 0 ≤ P i := le_max_of_le_left (by positivity)
  -- The Leibniz constant of order `k`, and their sum over `k ≤ N`.
  set S : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ by
    have := hW0 i; have := hP0 i; positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), S k, Finset.sum_nonneg fun k _ ↦ hS0 k,
    fun R χ hR hχ hsupp hB k hk ξ ↦ ?_⟩
  set w : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
  have hw : ContDiff ℝ ∞ w :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity
  -- By the Leibniz rule, each term `D^i w D^(k-i) χ` is `O(R ^ (s - i) R ^ (-(k - i)))`, which is
  -- `O(R ^ s / R ^ k)`; it vanishes off the support of `χ`.
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w ξ‖ * ‖iteratedFDeriv ℝ (k - i) χ ξ‖ ≤
        (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0 * (R ^ s / R ^ k) := by
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have := hW0 i
    have := hP0 i
    by_cases hξ : ξ ∈ tsupport χ
    · have hwi : ‖iteratedFDeriv ℝ i w ξ‖ ≤ W i * (P i * R ^ (s - i)) := by
        refine (hW i ξ).trans ?_
        rw [← sub_div]
        exact mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_half_le ha hR (hsupp ξ hξ) (s - i))
          (hW0 i)
      have hχi : ‖iteratedFDeriv ℝ (k - i) χ ξ‖ ≤ max (B (k - i)) 0 / R ^ (k - i) :=
        (hB (k - i) ((Nat.sub_le k i).trans hk) ξ).trans (by gcongr; exact le_max_left _ _)
      have hpow : R ^ (s - i) * (1 / R ^ (k - i)) = R ^ s / R ^ k := by
        rw [Real.rpow_sub hR, Real.rpow_natCast, ← pow_sub_mul_pow R hik]
        field_simp
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w ξ‖ * ‖iteratedFDeriv ℝ (k - i) χ ξ‖
          ≤ (k.choose i : ℝ) * (W i * (P i * R ^ (s - i))) *
              (max (B (k - i)) 0 / R ^ (k - i)) := by
            gcongr
        _ = (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0 *
              (R ^ (s - i) * (1 / R ^ (k - i))) := by
            ring
        _ = _ := by rw [hpow]
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (tsupport_iteratedFDeriv_subset _ h)),
        norm_zero, mul_zero]
      positivity
  refine (norm_iteratedFDeriv_mul_le hw hχ ξ (by exact_mod_cast le_top)).trans
    ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul, mul_div_assoc]
  gcongr
  exact Finset.single_le_sum (fun k _ ↦ hS0 k) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- **Kernels of Bessel-weighted dyadic symbols.** Let `2N > n = dim E`, `a > 0`, `b` and
`B : ℕ → ℝ`. There is a constant `C` with the following property. Let `R > 0` and let `χ` be a
smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and
`‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then the kernel of the symbol `(1 + ‖ξ‖ ^ 2) ^ (s / 2) χ ξ`
satisfies

`∫ ‖𝓕⁻ ((1 + ‖·‖ ^ 2) ^ (s / 2) χ) x‖ dx ≤ C R ^ s`. -/
theorem exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le (s : ℝ) {a b : ℝ}
    (ha : 0 < a) {N : ℕ} (hN : finrank ℝ E < 2 * N) (B : ℕ → ℝ) :
    ∃ C, ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) →
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ)) x‖ ≤ C * R ^ s := by
  set e := stdOrthonormalBasis ℝ E
  obtain ⟨C₀, -, hC₀⟩ :=
    SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset (H := ℂ) e hN
  obtain ⟨K, hK, hKχ⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le (E := E) s
    (b := b) ha N B
  -- The symbol is a band-limited Schwartz function at the scale `t = (√b + 1) R`, with constant
  -- `A = K (√b + 1) ^ N R ^ s`.
  refine ⟨C₀ * (K * (√b + 1) ^ N), fun R χ hR hχ hsupp hB ↦ ?_⟩
  have hKχ := hKχ R χ hR hχ hsupp hB
  set g : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity).mul hχ
  -- On the support of `χ`, the frequencies are at most `√b R`.
  set t : ℝ := (√b + 1) * R
  have ht : 0 < t := by positivity
  have hball : tsupport χ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    have h := hsupp ξ hξ
    have hb : 0 ≤ b := nonneg_of_mul_nonneg_left ((by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2).trans
      h.2) (by positivity)
    have hξR : ‖ξ‖ ≤ √b * R := by
      rw [← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_sq hR.le, ← Real.sqrt_mul hb]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [mem_closedBall_zero_iff]
    nlinarith
  have hcs : HasCompactSupport χ :=
    (isCompact_closedBall (0 : E) t).of_isClosed_subset (isClosed_tsupport χ) hball
  set σ : 𝓢(E, ℂ) := (hcs.mul_left.comp_left Complex.ofReal_zero : HasCompactSupport
    fun ξ ↦ (g ξ : ℂ)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hσ : ⇑σ = fun ξ ↦ (g ξ : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hσD (k : ℕ) (ξ : E) : ‖iteratedFDeriv ℝ k σ ξ‖ = ‖iteratedFDeriv ℝ k g ξ‖ := by
    rw [hσ]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast le_top)
  have hσt : Function.support σ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    refine hball (subset_tsupport _ ?_)
    rw [Function.mem_support] at hξ ⊢
    rintro hχξ
    simp [hσ, g, hχξ] at hξ
  have hσA (ξ : E) : ‖σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ s := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), hσD]
    refine (hKχ 0 (Nat.zero_le _) ξ).trans ?_
    rw [pow_zero, div_one, mul_right_comm]
    exact le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ (le_add_of_nonneg_left (Real.sqrt_nonneg b)))
  have hσN (j : Fin (finrank ℝ E)) (ξ : E) :
      ‖(∂_{e j})^[N] σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ s / t ^ N := by
    rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ N σ ξ).le_opNorm _).trans ?_
    simp only [e.orthonormal.1 j, Finset.prod_const_one, mul_one]
    refine (hσD N ξ).trans_le ((hKχ N le_rfl ξ).trans_eq ?_)
    simp only [t, mul_pow]
    field_simp
  have hint := hC₀ σ ht hσt hσA hσN
  rwa [SchwartzMap.fourierInv_coe, hσ, ← mul_assoc] at hint

end TauCeti

namespace TemperedDistribution

variable [NormedSpace ℂ F] (φ : ContDiffBump (0 : E))

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the support of the enlarged cutoff `Ψⱼ`, the Japanese bracket is comparable to `2^j`:
`a 4^j ≤ 1 + ‖ξ‖ ^ 2 ≤ b 4^j` with `a > 0` and `b` independent of `j`. -/
private theorem exists_one_add_norm_sq_le_of_mem_tsupport_enlargedLittlewoodPaley (L : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ (j : ℕ), ∀ ξ ∈ tsupport (φ.enlargedLittlewoodPaley L j),
      a * (2 ^ j) ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * (2 ^ j) ^ 2 := by
  refine ⟨min 1 (φ.rIn ^ 2) / (2 ^ L) ^ 2, 1 + (2 ^ L * φ.rOut) ^ 2,
    div_pos (lt_min one_pos (pow_pos φ.rIn_pos 2)) (by positivity), fun j ξ hξ ↦ ⟨?_, ?_⟩⟩
  · rcases lt_or_ge j L with hjL | hLj
    · -- Low frequencies: `a 4^j ≤ 4^(j - L) ≤ 1`.
      have : min 1 (φ.rIn ^ 2) / (2 ^ L) ^ 2 * (2 ^ j) ^ 2 ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        calc min 1 (φ.rIn ^ 2) * (2 ^ j) ^ 2 ≤ 1 * (2 ^ L) ^ 2 := by
              gcongr
              · exact min_le_left _ _
              · exact one_le_two
          _ = (2 ^ L) ^ 2 := one_mul _
      nlinarith [sq_nonneg ‖ξ‖]
    · -- High frequencies: `‖ξ‖ ≥ 2^(j - L) φ.rIn` on the support.
      have hξ' : 2 ^ (j - L) * φ.rIn ≤ ‖ξ‖ := φ.tsupport_enlargedLittlewoodPaley_subset_of_le hLj hξ
      have hj : (2 : ℝ) ^ j = 2 ^ (j - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel hLj]
      calc min 1 (φ.rIn ^ 2) / (2 ^ L) ^ 2 * (2 ^ j) ^ 2
          ≤ φ.rIn ^ 2 / (2 ^ L) ^ 2 * (2 ^ j) ^ 2 := by
            gcongr
            exact min_le_right _ _
        _ = (2 ^ (j - L) * φ.rIn) ^ 2 := by
            rw [hj]
            field_simp
        _ ≤ ‖ξ‖ ^ 2 := by
            gcongr
            exact mul_nonneg (by positivity) φ.rIn_pos.le
        _ ≤ 1 + ‖ξ‖ ^ 2 := le_add_of_nonneg_left zero_le_one
  · have hξ' := mem_closedBall_zero_iff.1 (φ.tsupport_enlargedLittlewoodPaley_subset L j hξ)
    have h1 : (1 : ℝ) ≤ (2 ^ j) ^ 2 := one_le_pow₀ (one_le_pow₀ one_le_two)
    calc 1 + ‖ξ‖ ^ 2 ≤ (2 ^ j) ^ 2 + (2 ^ (j + L) * φ.rOut) ^ 2 := by gcongr
      _ = (1 + (2 ^ L * φ.rOut) ^ 2) * (2 ^ j) ^ 2 := by
          rw [pow_add]
          ring

/-- **Bessel potentials on Littlewood–Paley blocks.** There is a constant `C` such that for every
`j` the Bessel potential `J^s` of order `s`, applied after the Littlewood–Paley block `Δⱼ`, is the
Fourier multiplier by a Schwartz symbol `σⱼ` applied after `Δⱼ`, where the kernel of `σⱼ` satisfies

`∫ ‖𝓕⁻ σⱼ x‖ dx ≤ C 2^{js}`.

The symbol `σⱼ` is the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)` cut off to the frequencies of `Δⱼ`
by the enlarged cutoff `Ψⱼ`, and the factorization `J^s Δⱼ = T_{σⱼ} Δⱼ` holds because
`Ψⱼ ψⱼ = ψⱼ`. -/
theorem exists_besselPotential_compL_littlewoodPaleyBlock_eq (s : ℝ) :
    ∃ C, ∀ j : ℕ, ∃ σ : 𝓢(E, ℂ),
      besselPotential E F s ∘L littlewoodPaleyBlock F φ j =
          fourierMultiplierCLM F σ ∘L littlewoodPaleyBlock F φ j ∧
        ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ ≤ C * (2 ^ j) ^ s := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero
  choose B hB0 hB using fun k : ℕ ↦ φ.exists_norm_iteratedFDeriv_enlargedLittlewoodPaley_le L k
  obtain ⟨a, b, ha, hab⟩ := exists_one_add_norm_sq_le_of_mem_tsupport_enlargedLittlewoodPaley φ L
  obtain ⟨C, hC⟩ := TauCeti.exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le (E := E)
    s (b := b) ha (N := finrank ℝ E + 1) (by omega) B
  refine ⟨C, fun j ↦ ?_⟩
  -- The symbol `σⱼ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) Ψⱼ ξ`.
  set χ : E → ℝ := φ.enlargedLittlewoodPaley L j
  have hχ : ContDiff ℝ ∞ χ := φ.contDiff_enlargedLittlewoodPaley L j
  have hσs : ContDiff ℝ ∞ (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity).mul hχ)
  set σ : 𝓢(E, ℂ) := ((φ.hasCompactSupport_enlargedLittlewoodPaley L j).mul_left.comp_left
    Complex.ofReal_zero : HasCompactSupport _).toSchwartzMap hσs
  have hσ : ⇑σ = fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  refine ⟨σ, ?_, ?_⟩
  · -- Both sides are Fourier multipliers; their symbols agree since `Ψⱼ ψⱼ = ψⱼ`.
    rw [besselPotential, littlewoodPaleyBlock_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_compL_fourierMultiplierCLM
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) (by fun_prop),
      fourierMultiplierCLM_compL_fourierMultiplierCLM
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) σ.hasTemperateGrowth]
    congr 1
    funext ξ
    have h := φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j ξ
    have h' : φ.inhomogeneousLittlewoodPaley j ξ * (1 + ‖ξ‖ ^ 2) ^ (s / 2) =
        φ.inhomogeneousLittlewoodPaley j ξ * ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ) := by
      linear_combination (-(1 + ‖ξ‖ ^ 2) ^ (s / 2)) * h
    simp only [Pi.mul_apply, hσ]
    exact_mod_cast h'
  · rw [hσ]
    exact hC (2 ^ j) χ (by positivity) hχ (hab j) fun k _ ξ ↦ hB k j ξ

end TemperedDistribution
