/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.DyadicSymbol
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Fourier multipliers on Besov spaces

Let `g : E → ℂ` be a smooth function with the symbol estimates

`‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)`

of order `m ∈ ℝ`, so that `g` grows at most like `⟨ξ⟩ ^ m` and each derivative gains one power of
`⟨ξ⟩⁻¹`. The Fourier multiplier `g(D) = 𝓕⁻ g 𝓕` then maps the inhomogeneous Besov space
`B^s_{p,q}` to `B^{s-m}_{p,q}` for every real `s` and every `1 ≤ p, q ≤ ∞`: a symbol of order `m`
costs exactly `m` derivatives on the whole Besov scale, including the Hölder–Zygmund scale
`𝒞^s = B^s_{∞,∞}` and the endpoints `p = 1, ∞` where no Mihlin-type `Lᵖ` bound is available.

The reason is that `g(D)` commutes with the Littlewood–Paley blocks `Δⱼ`, and on the `j`-th block
it acts like multiplication by `2^{jm}`: the cut-off symbol `Ψⱼ g` has a convolution kernel of
`L¹` norm `O(2^{jm})`, so by Young's inequality
`‖Δⱼ g(D) u‖_p ≤ C W 2^{jm} ‖Δⱼ u‖_p`
(`TemperedDistribution.exists_fourierMultiplierCLM_littlewoodPaleyBlock_eq_and_norm_le`). Here `W`
is a constant in the symbol estimates of the derivatives of `g` of order at most `dim E + 1`, and
`C` does not depend on `g`, `W`, `p` or `q`, so the bound scales linearly with `W`. Weighting by
`2^{j(s-m)}` turns the `B^s_{p,q}` norm of `u` into a bound for the `B^{s-m}_{p,q}` norm of
`g(D) u`.

The main example is the Bessel potential `J^t = (1 + ‖ξ‖ ^ 2) ^ (t / 2)(D)` of order `t`. Since
`J^{-t}` inverts it, `J^t` is an isomorphism `B^s_{p,q} ≃ B^{s-t}_{p,q}`, the *lifting property*
of the Besov scale. It reduces statements about `B^s_{p,q}` to a single smoothness index, for
instance the mapping properties of operators of order `m` to those of order `0`.

## Main declarations

* `TemperedDistribution.MemBesov.fourierMultiplierCLM`: if `u ∈ B^s_{p,q}` then
  `g(D) u ∈ B^{s-m}_{p,q}`.
* `TauCeti.BesovSpace.fourierMultiplierCLM`: the bounded operator
  `g(D) : B^s_{p,q} → B^{s'}_{p,q}` for `s' = s - m`, with its tempered distribution
  `TauCeti.BesovSpace.toDistr_fourierMultiplierCLM`.
* `TauCeti.BesovSpace.exists_toDistr_eq_fourierMultiplierCLM_and_norm_le`,
  `TauCeti.BesovSpace.exists_norm_fourierMultiplierCLM_le`: the bound `C W` for the norm of
  `g(D) : B^s_{p,q} → B^{s-m}_{p,q}`, with `C` independent of `g`, `W`, `p` and `q`.
* `TemperedDistribution.MemBesov.besselPotential`,
  `TemperedDistribution.memBesov_besselPotential_iff`: `J^t u ∈ B^s_{p,q}` exactly when
  `u ∈ B^{t+s}_{p,q}`.
* `TauCeti.BesovSpace.besselPotentialEquiv`: the lifting isomorphism
  `J^t : B^s_{p,q} ≃L[ℂ] B^{s'}_{p,q}` for `s' = s - t`, with inverse `J^{-t}`
  (`TauCeti.BesovSpace.besselPotentialEquiv_symm`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2 and Proposition 2.78.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.8 (the lifting property).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {g : E → ℂ} {m s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

namespace TemperedDistribution

/-- The blocks of `g(D) u` for a symbol `g` of order `m`: there is `C ≥ 0` such that, if `g`
satisfies the symbol estimates of order `m` with constant `W` for derivatives of order at most
`n + 1` and the blocks `Δⱼ u` are `Lᵖ` functions `fⱼ`, then the blocks `Δⱼ g(D) u` are `Lᵖ`
functions `f'ⱼ` with `2^{j(s-m)} ‖f'ⱼ‖_p ≤ C W 2^{js} ‖fⱼ‖_p`. The constant does not depend on `g`,
`W`, `p`, `j` or `u`. -/
private theorem exists_littlewoodPaleyBlock_fourierMultiplierCLM_eq_and_le
    (φ : ContDiffBump (0 : E)) (m s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : E → ℂ} {W : ℝ}, g.HasTemperateGrowth →
      (∀ i ≤ Module.finrank ℝ E + 1, ∀ ξ,
        ‖iteratedFDeriv ℝ i g ξ‖ ≤ W * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)) →
      ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (f : ℕ → Lp F p (volume : Measure E)), (∀ j, littlewoodPaleyBlock F φ j u = f j) →
      ∃ f' : ℕ → Lp F p (volume : Measure E),
        (∀ j, littlewoodPaleyBlock F φ j (fourierMultiplierCLM F g u) = f' j) ∧
          ∀ j : ℕ, 2 ^ ((s - m) * j) * ‖f' j‖ ≤ C * W * (2 ^ (s * j) * ‖f j‖) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_fourierMultiplierCLM_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ m
  refine ⟨C, hC0, fun {g W} hg hgW {p} _ {u} f hf ↦ ?_⟩
  choose f' hf' hle using fun j ↦ hC hg hgW j u (f j) (hf j)
  refine ⟨f', fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [littlewoodPaleyBlock_fourierMultiplierCLM_comm φ hg, hf' j]
  · calc 2 ^ ((s - m) * j) * ‖f' j‖ ≤ 2 ^ ((s - m) * j) * (C * W * 2 ^ (m * j) * ‖f j‖) := by
          gcongr
          exact hle j
      _ = C * W * (2 ^ ((s - m) * j + m * j) * ‖f j‖) := by
          rw [Real.rpow_add two_pos]
          ring
      _ = C * W * (2 ^ (s * j) * ‖f j‖) := by ring_nf

/-- **Fourier multipliers on Besov spaces.** If `g` is a smooth symbol of order `m`,
`‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)`, then the Fourier multiplier `g(D)` maps
`B^s_{p,q}` to `B^{s-m}_{p,q}`. -/
theorem MemBesov.fourierMultiplierCLM (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) :
    (TemperedDistribution.fourierMultiplierCLM F g u).MemBesov φ (s - m) p q := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  obtain ⟨C, -, hC⟩ := exists_littlewoodPaleyBlock_fourierMultiplierCLM_eq_and_le (F := F) φ m s
  obtain ⟨W, hW⟩ :=
    TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_one_add_norm_sq_rpow fun i _ ↦ hgm i
  obtain ⟨f', hf', hle⟩ :=
    hC (.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgm) hW f hf
  refine memBesov_iff.2 ⟨f', hf', (hmem.const_mul (C * W)).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hle j

/-- The Bessel potential `J^t` maps `B^s_{p,q}` to `B^{s-t}_{p,q}`. -/
theorem MemBesov.besselPotential {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (t : ℝ) :
    (besselPotential E F t u).MemBesov φ (s - t) p q :=
  hu.fourierMultiplierCLM
    (TauCeti.contDiff_ofReal_one_add_norm_sq_rpow (t / 2))
    (TauCeti.exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le t)

/-- **The lifting property of Besov spaces.** `J^t u ∈ B^s_{p,q}` exactly when
`u ∈ B^{t+s}_{p,q}`. -/
@[simp]
theorem memBesov_besselPotential_iff {u : 𝓢'(E, F)} {t : ℝ} :
    (besselPotential E F t u).MemBesov φ s p q ↔ u.MemBesov φ (t + s) p q := by
  refine ⟨fun h ↦ ?_, fun hu ↦ by simpa using hu.besselPotential t⟩
  simpa [add_comm s t] using h.besselPotential (-t)

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable [Fact (1 ≤ q)]

/-- **The norm of a Fourier multiplier on Besov spaces.** For real `m` there is `C ≥ 0`,
depending only on `φ`, `m` and `s`, with the following property. If `g` is a function of temperate
growth with the symbol estimates `‖D^i g ξ‖ ≤ W (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of order `m` for
`i ≤ n + 1`, where `n = dim E`, then the Besov norm in `B^{s-m}_{p,q}` of `g(D) u` is at most
`C W` times the norm of `u` in `B^s_{p,q}`, for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_toDistr_eq_fourierMultiplierCLM_and_norm_le (φ : ContDiffBump (0 : E))
    (m : ℝ) {s s' : ℝ} (hs : s' = s - m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : E → ℂ} {W : ℝ}, g.HasTemperateGrowth →
      (∀ i ≤ Module.finrank ℝ E + 1, ∀ ξ,
        ‖iteratedFDeriv ℝ i g ξ‖ ≤ W * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F φ s p q),
      ∃ v : BesovSpace F φ s' p q,
        v.toDistr = TemperedDistribution.fourierMultiplierCLM F g u.toDistr ∧
          ‖v‖ ≤ C * W * ‖u‖ := by
  subst hs
  obtain ⟨C, hC0, hC⟩ := exists_littlewoodPaleyBlock_fourierMultiplierCLM_eq_and_le (F := F) φ m s
  refine ⟨C, hC0, fun {g W} hg hgW {p q} _ _ u ↦ ?_⟩
  have hW : 0 ≤ W := nonneg_of_forall_norm_le_mul_one_add_norm_sq_rpow (hgW 0 (Nat.zero_le _))
  obtain ⟨f', hf', hle⟩ := hC hg hgW u.block fun k ↦ (coe_block u k).symm
  have hu : (TemperedDistribution.fourierMultiplierCLM F g u.toDistr).MemBesov φ (s - m) p q :=
    memBesov_iff.2 ⟨f', hf', ((memBesov_iff_memℓp fun k ↦ (coe_block u k).symm).1
      u.memBesov_toDistr |>.const_mul (C * W)).mono fun j ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact (hle j).trans_eq (by ring)⟩
  refine ⟨hu.toBesovSpace, hu.toDistr_toBesovSpace, ?_⟩
  have hv (j : ℕ) : hu.toBesovSpace.block j = f' j :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block,
        MemBesov.toDistr_toBesovSpace, hf' j]
  rw [← norm_weightedBlocks, ← norm_weightedBlocks, ← Complex.norm_of_nonneg (by positivity :
    (0 : ℝ) ≤ C * W), ← norm_smul]
  refine lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ ?_
  rw [norm_weightedBlocks_apply, hv, lp.coeFn_smul, Pi.smul_apply, norm_smul,
    Complex.norm_of_nonneg (by positivity), norm_weightedBlocks_apply]
  exact (hle j).trans_eq (by ring)

variable (F φ p q) in
/-- **Fourier multipliers on Besov spaces.** A smooth symbol `g` of order `m`,
`‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)`, defines a bounded operator
`g(D) : B^s_{p,q} → B^{s'}_{p,q}` for `s' = s - m`. Its norm is controlled by the symbol estimates
of order at most `dim E + 1` (`TauCeti.BesovSpace.exists_norm_fourierMultiplierCLM_le`). -/
def fourierMultiplierCLM (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {s s' : ℝ} (hs : s' = s - m) : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u :=
        MemBesov.toBesovSpace (u := TemperedDistribution.fourierMultiplierCLM F g u.toDistr)
          (by subst hs; exact u.memBesov_toDistr.fourierMultiplierCLM hg hgm)
      map_add' u v := ext <| by simp only [MemBesov.toDistr_toBesovSpace, toDistr_add, map_add]
      map_smul' c u := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_smul, map_smul, RingHom.id_apply] } <| by
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_fourierMultiplierCLM_and_norm_le (F := F) φ m hs
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_one_add_norm_sq_rpow fun i _ ↦ hgm i
    refine ⟨C * W, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvC⟩ :=
      hC (.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgm)
        hW u
    convert hvC using 2
    exact ext (by simp [hv])

@[simp]
theorem toDistr_fourierMultiplierCLM (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {s' : ℝ} (hs : s' = s - m) (u : BesovSpace F φ s p q) :
    (fourierMultiplierCLM F φ p q hg hgm hs u).toDistr =
      TemperedDistribution.fourierMultiplierCLM F g u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

/-- **The norm of a Fourier multiplier on Besov spaces.** For real `m` there is `C ≥ 0`,
depending only on `φ`, `m` and `s`, such that `‖g(D)‖ ≤ C W` as an operator
`B^s_{p,q} → B^{s-m}_{p,q}` for all `1 ≤ p, q ≤ ∞`, whenever `W` is a constant in the symbol
estimates `‖D^i g ξ‖ ≤ W (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` for `i ≤ n + 1`, where `n = dim E`. -/
theorem exists_norm_fourierMultiplierCLM_le (φ : ContDiffBump (0 : E)) (m : ℝ) {s s' : ℝ}
    (hs : s' = s - m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {g : E → ℂ}
      (hg : ContDiff ℝ ∞ g)
      (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
      {W : ℝ}, (∀ i ≤ Module.finrank ℝ E + 1, ∀ ξ,
        ‖iteratedFDeriv ℝ i g ξ‖ ≤ W * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)) →
      ‖fourierMultiplierCLM F φ p q hg hgm hs‖ ≤ C * W := by
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_fourierMultiplierCLM_and_norm_le (F := F) φ m hs
  refine ⟨C, hC0, fun {p q} _ _ g hg hgm W hgW ↦ ?_⟩
  have hW : 0 ≤ W := nonneg_of_forall_norm_le_mul_one_add_norm_sq_rpow (hgW 0 (Nat.zero_le _))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  obtain ⟨v, hv, hvC⟩ := hC (.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgm) hgW u
  rw [show fourierMultiplierCLM F φ p q hg hgm hs u = v from
    ext (by rw [hv, toDistr_fourierMultiplierCLM])]
  exact hvC

variable (F φ p q) in
/-- **The lifting property of Besov spaces.** The Bessel potential `J^t` of order `t` is an
isomorphism of normed spaces `B^s_{p,q} ≃L[ℂ] B^{s'}_{p,q}` for `s' = s - t`, with inverse
`J^{-t}`. -/
def besselPotentialEquiv (t : ℝ) {s s' : ℝ} (hs : s' = s - t) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ s' p q :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (fourierMultiplierCLM F φ p q (contDiff_ofReal_one_add_norm_sq_rpow (t / 2))
      (exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le t) hs)
    (fourierMultiplierCLM F φ p q (contDiff_ofReal_one_add_norm_sq_rpow (-t / 2))
      (exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le (-t)) (by rw [hs]; ring))
    (ContinuousLinearMap.ext fun v ↦ ext <| by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        toDistr_fourierMultiplierCLM, toDistr_fourierMultiplierCLM, ← besselPotential,
        ← besselPotential, besselPotential_besselPotential_apply, neg_add_cancel,
        besselPotential_zero, ContinuousLinearMap.id_apply])
    (ContinuousLinearMap.ext fun u ↦ ext <| by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        toDistr_fourierMultiplierCLM, toDistr_fourierMultiplierCLM, ← besselPotential,
        ← besselPotential, besselPotential_besselPotential_apply, add_neg_cancel,
        besselPotential_zero, ContinuousLinearMap.id_apply])

@[simp]
theorem toDistr_besselPotentialEquiv (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    (u : BesovSpace F φ s p q) :
    (besselPotentialEquiv F φ p q t hs u).toDistr = besselPotential E F t u.toDistr := by
  rw [besselPotentialEquiv, ContinuousLinearEquiv.coe_ofContinuousLinearMap,
    toDistr_fourierMultiplierCLM, besselPotential]

/-- The inverse of the lifting isomorphism `J^t` is the lifting isomorphism `J^{-t}`. -/
@[simp]
theorem besselPotentialEquiv_symm (t : ℝ) {s' : ℝ} (hs : s' = s - t) :
    (besselPotentialEquiv F φ p q t hs).symm =
      besselPotentialEquiv F φ p q (-t) (by rw [hs, sub_neg_eq_add, sub_add_cancel]) :=
  ContinuousLinearEquiv.ext <| funext fun v ↦ ext <| by
    rw [toDistr_besselPotentialEquiv, besselPotentialEquiv,
      ContinuousLinearEquiv.symm_ofContinuousLinearMap,
      ContinuousLinearEquiv.coe_ofContinuousLinearMap, toDistr_fourierMultiplierCLM,
      besselPotential]

end TauCeti.BesovSpace
