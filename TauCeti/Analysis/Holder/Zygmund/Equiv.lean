/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Zygmund.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Identification of Hölder–Zygmund and classical Hölder spaces

The companion module `TauCeti.Analysis.Holder.Zygmund.Basic` constructs the forward continuous
inclusions `𝒞^α ⊆ C^{0,α}` and `𝒞^{k+α} ⊆ C_b^{k,α}` for non-integer orders `0 < α < 1`. This file
establishes the converse inclusions `C^{0,α} ⊆ 𝒞^α` and `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ`
and every `α : ℝ≥0` — including the integer endpoints `α = 0` (`C_b^k ⊆ 𝒞^k`) and `α = 1`
(`C_b^{k,1} ⊆ 𝒞^{k+1}`) — and combines both directions into continuous linear equivalences
`𝒞^α ≃L[ℝ] C^{0,α}` and `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` for `0 < α < 1`.

## The argument

By the kernel cancellation estimate
`TemperedDistribution.norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le`, a bounded continuous
function `f` satisfying `‖f (x - y) - f x‖ ≤ A ‖y‖^α + B ‖y‖` has dyadic blocks bounded by
`‖Δ_{j+1} f‖_∞ ≤ A 2^{-α j} M_α + B 2^{-j} M_1`, where `M_s = ∫ ‖y‖^s ‖𝓕⁻ ψ₁ y‖ dy`. With `B = 0`
this gives `2^{α j} ‖Δ_j f‖_∞ ≤ C ‖f‖_{C^{0,α}}`, so `C^{0,α} ⊆ 𝒞^α` continuously for every
`α : ℝ≥0`.

For higher order `k : ℕ`, the reverse Bernstein inequality
`TemperedDistribution.exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv` (via
`BoundedContinuousFunction.iteratedLineDerivOp_toLpTop_eq`) gives a weighted estimate
`2^{(k+s)(j+1)} ‖Δ_{j+1} f‖_∞ ≤ C^k ∑ᵢ 2^{s(j+1)} ‖Δ_{j+1} (D^k f · (b ∘ i))‖_∞` for any
orthonormal basis `b`
(`TauCeti.CkHolderSpace.exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional`).
Applying the order-zero cancellation bound to each directional `k`-th derivative yields
`2^{(k + α) j} ‖Δ_j f‖_∞ ≤ C ‖f‖_{C_b^{k,α}}`, giving `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ`
and `α : ℝ≥0`.

For `0 < α < 1`, both maps keep the underlying tempered distribution, and bounded continuous
functions are determined by their tempered distributions, so `toHolderSpace` and `toCkHolderSpace`
are inverse to `HolderSpace.toBesovSpace` and `CkHolderSpace.toBesovSpace`.

## Main declarations

* `TauCeti.HolderSpace.memBesov` and `TauCeti.HolderSpace.toBesovSpace`: the continuous inclusion
  `C^{0,α} ⊆ 𝒞^α` for every `α : ℝ≥0`.
* `TauCeti.BesovSpace.holderSpaceEquiv`: the continuous linear equivalence `𝒞^α ≃L[ℝ] C^{0,α}`
  for `0 < α < 1`, with unbundled characterisation
  `TemperedDistribution.memBesov_iff_exists_holderSpace`.
* `TauCeti.CkHolderSpace.exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional`:
  weighted reverse Bernstein estimate bounding `2^{(k+s)(j+1)} ‖Δ_{j+1} f‖_∞` by the weighted
  blocks of the directional `k`-th derivatives of `f`.
* `TauCeti.CkHolderSpace.memBesov` and `TauCeti.CkHolderSpace.toBesovSpace`: the continuous
  inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ` and `α : ℝ≥0`.
* `TauCeti.BesovSpace.ckHolderSpaceEquiv`: the continuous linear equivalence
  `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` for `0 < α < 1`, with unbundled characterisation
  `TemperedDistribution.memBesov_iff_exists_ckHolderSpace`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Theorem 2.36 and
  Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.5.7.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution BoundedContinuousFunction Module
open scoped ENNReal NNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

/-! ### Order-zero inclusion `C^{0,α} ⊆ 𝒞^α` and equivalence `𝒞^α ≃L[ℝ] C^{0,α}` -/

namespace HolderSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- Uniform weighted block bound for `C^{0,α}` functions, valid for every `α : ℝ≥0`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : HolderSpace α E F) (j : ℕ),
      ∃ v : Lp F ∞ (volume : Measure E),
        littlewoodPaleyBlock F φ j (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) =
          v ∧ 2 ^ ((α : ℝ) * j) * ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set Mα : ℝ :=
    ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set C : ℝ := max (max C₀ 0) (2 ^ (α : ℝ) * Mα)
  refine ⟨C, (le_max_right C₀ 0).trans (le_max_left _ _), fun f j ↦ ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC₀ j (toLpTop volume ℂ f.toBoundedContinuousFunction)
  refine ⟨v, hv, ?_⟩
  rcases j with _ | j
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
    calc ‖v‖ ≤ C₀ * ‖toLpTop volume ℂ f.toBoundedContinuousFunction‖ := hvC
      _ ≤ max C₀ 0 * ‖f‖ := mul_le_mul (le_max_left _ _)
            ((norm_toLpTop_le volume _).trans f.norm_toBoundedContinuousFunction_le)
            (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)
  · have hinc : ∀ x y, ‖f.toBoundedContinuousFunction (x - y) -
        f.toBoundedContinuousFunction x‖ ≤ ‖f‖ * ‖y‖ ^ (α : ℝ) + 0 * ‖y‖ := fun x y ↦ by
      rw [zero_mul, add_zero, toBoundedContinuousFunction_apply, toBoundedContinuousFunction_apply,
        ← dist_eq_norm]
      have h := f.holderWith_nnnorm.dist_le (x - y) x
      rwa [coe_nnNorm, dist_eq_norm (x - y) x, sub_sub_cancel_left, norm_neg] at h
    have hv_bound := norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ α.coe_nonneg
      (norm_nonneg f) le_rfl hinc hv
    rw [zero_mul, zero_mul, add_zero] at hv_bound
    have hpow : (2 : ℝ) ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) =
        2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.rpow_add two_pos, mul_comm]
    calc 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖v‖
        ≤ 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * (‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα) := by
          gcongr
      _ = (2 ^ (α : ℝ) * Mα) * ‖f‖ := by
          rw [hpow]
          have hpos : (2 : ℝ) ^ ((α : ℝ) * j) ≠ 0 := by positivity
          field_simp
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f)

/-- **Every bounded `α`-Hölder function lies in `𝒞^α = B^α_{∞,∞}`**, for every `α : ℝ≥0`. -/
theorem memBesov (f : HolderSpace α E F) :
    (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)).MemBesov φ α ∞ ∞ := by
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (α := α) φ
  choose g hg hgb using h f
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty ⟨C * ‖f‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgb j

/-- **The inclusion `C^{0,α} ⊆ 𝒞^α`** for every `α : ℝ≥0`, as a continuous linear map from the
bounded `α`-Hölder space to the Hölder–Zygmund space `B^α_{∞,∞}` built from `φ`. -/
def toBesovSpace : HolderSpace α E F →L[ℝ] BesovSpace F φ α ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := (f.memBesov φ).toBesovSpace
      map_add' f g := BesovSpace.ext <| by
        simp [HolderSpace.toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      map_smul' c f := BesovSpace.ext <| by
        simp only [RingHom.id_apply, MemBesov.toDistr_toBesovSpace,
          HolderSpace.toBoundedContinuousFunction_smul]
        rw [← Complex.coe_smul c f.toBoundedContinuousFunction, map_smul,
          Lp.toTemperedDistribution_smul, ← Complex.coe_smul c ((f.memBesov φ).toBesovSpace),
          BesovSpace.toDistr_smul, MemBesov.toDistr_toBesovSpace] } <| by
    obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (α := α) φ
    refine ⟨C, fun f ↦ ?_⟩
    set v := (f.memBesov φ).toBesovSpace
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgf⟩ := hC f j
    have hvg : v.block j = g := Lp.toTemperedDistribution_injective <| by
      simp only [BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
    rw [hvg]
    exact hgf

/-- The inclusion `HolderSpace.toBesovSpace` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_toBesovSpace (f : HolderSpace α E F) :
    (toBesovSpace φ f).toDistr =
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) := by
  simp [toBesovSpace]

end HolderSpace

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- `HolderSpace.toBesovSpace` is left inverse to `BesovSpace.toHolderSpace`. -/
@[simp]
theorem toBesovSpace_toHolderSpace (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    HolderSpace.toBesovSpace φ (toHolderSpace F φ hα0 hα1 u) = u :=
  ext <| by simp

/-- `BesovSpace.toHolderSpace` is left inverse to `HolderSpace.toBesovSpace`. -/
@[simp]
theorem toHolderSpace_toBesovSpace (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    toHolderSpace F φ hα0 hα1 (HolderSpace.toBesovSpace φ f) = f :=
  (toHolderSpace_eq_iff φ hα0 hα1).2 (by simp)

variable (F) in
/-- **Identification `𝒞^α ≃L[ℝ] C^{0,α}`** for `0 < α < 1`: the Hölder–Zygmund space `B^α_{∞,∞}`
is continuously linearly equivalent to the bounded `α`-Hölder space `C^{0,α}`. -/
def holderSpaceEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ α ∞ ∞ ≃L[ℝ] HolderSpace α E F :=
  ContinuousLinearEquiv.equivOfInverse
    (toHolderSpace F φ hα0 hα1) (HolderSpace.toBesovSpace φ)
    (toBesovSpace_toHolderSpace φ hα0 hα1) (toHolderSpace_toBesovSpace φ hα0 hα1)

/-- Forward evaluation of `BesovSpace.holderSpaceEquiv` is `BesovSpace.toHolderSpace`. -/
@[simp]
theorem holderSpaceEquiv_apply (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    holderSpaceEquiv F φ hα0 hα1 u = toHolderSpace F φ hα0 hα1 u :=
  (rfl)

/-- Inverse evaluation of `BesovSpace.holderSpaceEquiv` is `HolderSpace.toBesovSpace`. -/
@[simp]
theorem holderSpaceEquiv_symm_apply (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    (holderSpaceEquiv F φ hα0 hα1).symm f = HolderSpace.toBesovSpace φ f :=
  (rfl)

end BesovSpace

end TauCeti

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Unbundled identification `𝒞^α = C^{0,α}`** for `0 < α < 1`: a tempered distribution lies in
`B^α_{∞,∞}` exactly when it is the tempered distribution of a bounded `α`-Hölder function. -/
theorem memBesov_iff_exists_holderSpace (hα0 : 0 < α) (hα1 : α < 1) {u : 𝓢'(E, F)} :
    u.MemBesov φ α ∞ ∞ ↔
      ∃ f : TauCeti.HolderSpace α E F,
        (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u :=
  ⟨fun hu ↦ ⟨TauCeti.BesovSpace.toHolderSpace F φ hα0 hα1 hu.toBesovSpace, by simp⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ f.memBesov φ⟩

end TemperedDistribution

/-! ### Higher-order inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}` and equivalence `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` -/

namespace TauCeti

namespace CkHolderSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- **Weighted reverse Bernstein bound for `C_b^{k,α}` functions.** Given an orthonormal basis `b`
of `E`, there is `C ≥ 0` depending only on `φ` and `b` such that for every `k : ℕ`, `α : ℝ≥0`,
`f : CkHolderSpace k α E F`, real weight `s`, dyadic index `j : ℕ`, and `L^∞` representatives `v`
and `w i` of `Δ_{j+1} f` and `Δ_{j+1} (D^k f · (b ∘ i))`,
`2^{(k + s)(j + 1)} ‖v‖ ≤ C^k ∑ᵢ 2^{s(j + 1)} ‖w i‖`. -/
theorem exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {α : ℝ≥0} (f : CkHolderSpace k α E F) (s : ℝ) (j : ℕ)
      (v : Lp F ∞ (volume : Measure E)) (w : (Fin k → ι) → Lp F ∞ (volume : Measure E)),
      littlewoodPaleyBlock F φ (j + 1)
        (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = v →
      (∀ i, littlewoodPaleyBlock F φ (j + 1)
        (toLpTop volume ℂ (f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i)) : 𝓢'(E, F)) =
          w i) →
      2 ^ (((k : ℝ) + s) * ((j + 1 : ℕ) : ℝ)) * ‖v‖ ≤
        C ^ k * ∑ i, 2 ^ (s * ((j + 1 : ℕ) : ℝ)) * ‖w i‖ := by
  obtain ⟨Cr, hCr0, hrev⟩ := exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv
    (F := F) φ b
  have hIn : 0 < φ.rIn := φ.rIn_pos
  refine ⟨2 * Cr / φ.rIn, by positivity, fun k {α} f s j v w hv hw ↦ ?_⟩
  have hrev_j : ‖v‖ ≤ (Cr / (2 ^ j * φ.rIn)) ^ k * ∑ i, ‖w i‖ :=
    hrev k f.toBoundedContinuousFunction
      (fun i ↦ f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i)) j v w
      (by simpa only [coe_toBoundedContinuousFunction] using f.contDiff)
      (fun m hm ↦ ⟨‖f‖, fun x ↦ by
        simpa only [coe_toBoundedContinuousFunction] using
          f.norm_iteratedFDeriv_apply_le hm.le x⟩)
      (fun i x ↦ by
        rw [directionalIteratedFDeriv_apply, coe_toBoundedContinuousFunction]
        rfl)
      hv hw
  have hpow : (2 : ℝ) ^ (((k : ℝ) + s) * ((j + 1 : ℕ) : ℝ)) =
      (2 ^ (j + 1)) ^ k * 2 ^ (s * ((j + 1 : ℕ) : ℝ)) := by
    rw [add_mul, Real.rpow_add two_pos, mul_comm (k : ℝ), Real.rpow_mul_natCast zero_le_two,
      Real.rpow_natCast]
  calc 2 ^ (((k : ℝ) + s) * ((j + 1 : ℕ) : ℝ)) * ‖v‖
      ≤ 2 ^ (((k : ℝ) + s) * ((j + 1 : ℕ) : ℝ)) *
          ((Cr / (2 ^ j * φ.rIn)) ^ k * ∑ i, ‖w i‖) := by gcongr
    _ = (2 * Cr / φ.rIn) ^ k * ∑ i, 2 ^ (s * ((j + 1 : ℕ) : ℝ)) * ‖w i‖ := by
        rw [hpow, ← Finset.mul_sum]
        simp only [pow_succ, div_pow, mul_pow]
        field_simp

/-- Uniform weighted block bound for `C_b^{k,α}` functions, valid for every `k : ℕ` and
`α : ℝ≥0`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : CkHolderSpace k α E F) (j : ℕ),
      ∃ v : Lp F ∞ (volume : Measure E),
        littlewoodPaleyBlock F φ j (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) =
          v ∧ 2 ^ (((k : ℝ) + α) * j) * ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, hCr0, hrev⟩ :=
    exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional (F := F) φ b
  set Mα : ℝ :=
    ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set K : ℝ := Cr ^ k * (finrank ℝ E : ℝ) ^ k * (2 ^ (α : ℝ) * Mα)
  set C : ℝ := max (max C₀ 0) K
  refine ⟨C, (le_max_right C₀ 0).trans (le_max_left _ _), fun f j ↦ ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC₀ j (toLpTop volume ℂ f.toBoundedContinuousFunction)
  refine ⟨v, hv, ?_⟩
  rcases j with _ | j
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
    calc ‖v‖ ≤ C₀ * ‖toLpTop volume ℂ f.toBoundedContinuousFunction‖ := hvC
      _ ≤ max C₀ 0 * ‖f‖ := mul_le_mul (le_max_left _ _)
            ((norm_toLpTop_le volume _).trans f.norm_toBoundedContinuousFunction_le)
            (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)
  · have hnorm_b : ∀ (i : Fin k → Fin (finrank ℝ E)), ∏ r, ‖b (i r)‖ = 1 := fun i ↦
      Finset.prod_eq_one fun r _ ↦ b.orthonormal.1 (i r)
    choose w hw _ using fun i : Fin k → Fin (finrank ℝ E) ↦
      hC₀ (j + 1) (toLpTop volume ℂ (f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i)))
    have hw_le (i : Fin k → Fin (finrank ℝ E)) :
        2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i‖ ≤ (2 ^ (α : ℝ) * Mα) * ‖f‖ := by
      have hinc : ∀ x y,
          ‖f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) (x - y) -
              f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) x‖ ≤
            ‖f‖ * ‖y‖ ^ (α : ℝ) + 0 * ‖y‖ := fun x y ↦ by
        rw [zero_mul, add_zero]
        calc ‖f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) (x - y) -
                f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) x‖
            ≤ ‖_root_.iteratedFDeriv ℝ k f (x - y) - _root_.iteratedFDeriv ℝ k f x‖ *
                ∏ r, ‖b (i r)‖ :=
                f.norm_directionalIteratedFDeriv_sub_le (Fin.last k) (⇑b ∘ i) (x - y) x
          _ = dist (_root_.iteratedFDeriv ℝ k f (x - y)) (_root_.iteratedFDeriv ℝ k f x) := by
                rw [hnorm_b i, mul_one, dist_eq_norm]
          _ ≤ nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) * dist (x - y) x ^ (α : ℝ) :=
                f.memHolder_iteratedFDeriv.holderWith.dist_le (x - y) x
          _ ≤ ‖f‖ * ‖y‖ ^ (α : ℝ) := by
                rw [dist_eq_norm (x - y) x, sub_sub_cancel_left, norm_neg]
                exact mul_le_mul_of_nonneg_right f.nnHolderNorm_iteratedFDeriv_le (by positivity)
      have h := norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ α.coe_nonneg
        (norm_nonneg f) le_rfl hinc (hw i)
      rw [zero_mul, zero_mul, add_zero] at h
      have hpow : (2 : ℝ) ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) =
          2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j) := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.rpow_add two_pos, mul_comm]
      calc 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i‖
          ≤ 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * (‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα) := by
            gcongr
        _ = (2 ^ (α : ℝ) * Mα) * ‖f‖ := by
            rw [hpow]
            have hpos : (2 : ℝ) ^ ((α : ℝ) * j) ≠ 0 := by positivity
            field_simp
    have hsum : ∑ i : Fin k → Fin (finrank ℝ E),
          2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i‖ ≤
        (finrank ℝ E : ℝ) ^ k * ((2 ^ (α : ℝ) * Mα) * ‖f‖) := by
      refine (Finset.sum_le_sum fun i _ ↦ hw_le i).trans ?_
      simp [Finset.card_univ]
    calc 2 ^ (((k : ℝ) + α) * ((j + 1 : ℕ) : ℝ)) * ‖v‖
        ≤ Cr ^ k * ∑ i : Fin k → Fin (finrank ℝ E),
            2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i‖ := hrev k f (α : ℝ) j v w hv hw
      _ ≤ Cr ^ k * ((finrank ℝ E : ℝ) ^ k * ((2 ^ (α : ℝ) * Mα) * ‖f‖)) := by gcongr
      _ = K * ‖f‖ := by simp only [K]; ring
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f)

/-- **Every bounded `C^{k,α}` map lies in `𝒞^{k+α} = B^{k+α}_{∞,∞}`**, for every `k : ℕ` and
`α : ℝ≥0`. -/
theorem memBesov (f : CkHolderSpace k α E F) :
    (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)).MemBesov φ (k + α) ∞ ∞ := by
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (k := k) (α := α) φ
  choose g hg hgb using h f
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty ⟨C * ‖f‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgb j

/-- **The inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}`** for every `k : ℕ` and `α : ℝ≥0`, as a continuous
linear map from the bounded `C^{k,α}` space to the Hölder–Zygmund space `B^{k+α}_{∞,∞}` built from
`φ`. -/
def toBesovSpace : CkHolderSpace k α E F →L[ℝ] BesovSpace F φ (k + α) ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := (f.memBesov φ).toBesovSpace
      map_add' f g := BesovSpace.ext <| by
        simp [CkHolderSpace.toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      map_smul' c f := BesovSpace.ext <| by
        simp only [RingHom.id_apply, MemBesov.toDistr_toBesovSpace,
          CkHolderSpace.toBoundedContinuousFunction_smul]
        rw [← Complex.coe_smul c f.toBoundedContinuousFunction, map_smul,
          Lp.toTemperedDistribution_smul, ← Complex.coe_smul c ((f.memBesov φ).toBesovSpace),
          BesovSpace.toDistr_smul, MemBesov.toDistr_toBesovSpace] } <| by
    obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (k := k) (α := α) φ
    refine ⟨C, fun f ↦ ?_⟩
    set v := (f.memBesov φ).toBesovSpace
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgf⟩ := hC f j
    have hvg : v.block j = g := Lp.toTemperedDistribution_injective <| by
      simp only [BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
    rw [hvg]
    exact hgf

/-- The inclusion `CkHolderSpace.toBesovSpace` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_toBesovSpace (f : CkHolderSpace k α E F) :
    (toBesovSpace φ f).toDistr =
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) := by
  simp [toBesovSpace]

end CkHolderSpace

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- `CkHolderSpace.toBesovSpace` is left inverse to `BesovSpace.toCkHolderSpace`. -/
@[simp]
theorem toBesovSpace_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    CkHolderSpace.toBesovSpace φ (toCkHolderSpace F φ k hα0 hα1 u) = u :=
  ext <| by simp

/-- `BesovSpace.toCkHolderSpace` is left inverse to `CkHolderSpace.toBesovSpace`. -/
@[simp]
theorem toCkHolderSpace_toBesovSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    toCkHolderSpace F φ k hα0 hα1 (CkHolderSpace.toBesovSpace φ f) = f :=
  (toCkHolderSpace_eq_iff φ k hα0 hα1).2 (by simp)

variable (F) in
/-- **Identification `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}`** for `k : ℕ` and `0 < α < 1`: the Hölder–Zygmund
space `B^{k+α}_{∞,∞}` is continuously linearly equivalent to the bounded `C^{k,α}` space. -/
def ckHolderSpaceEquiv (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ (k + α) ∞ ∞ ≃L[ℝ] CkHolderSpace k α E F :=
  ContinuousLinearEquiv.equivOfInverse
    (toCkHolderSpace F φ k hα0 hα1) (CkHolderSpace.toBesovSpace φ)
    (toBesovSpace_toCkHolderSpace φ k hα0 hα1) (toCkHolderSpace_toBesovSpace φ k hα0 hα1)

/-- Forward evaluation of `BesovSpace.ckHolderSpaceEquiv` is `BesovSpace.toCkHolderSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_apply (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ckHolderSpaceEquiv F φ k hα0 hα1 u = toCkHolderSpace F φ k hα0 hα1 u :=
  (rfl)

/-- Inverse evaluation of `BesovSpace.ckHolderSpaceEquiv` is `CkHolderSpace.toBesovSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_symm_apply (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    (ckHolderSpaceEquiv F φ k hα0 hα1).symm f = CkHolderSpace.toBesovSpace φ f :=
  (rfl)

end BesovSpace

end TauCeti

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Unbundled identification `𝒞^{k+α} = C_b^{k,α}`** for `k : ℕ` and `0 < α < 1`: a tempered
distribution lies in `B^{k+α}_{∞,∞}` exactly when it is the tempered distribution of a bounded
`C^{k,α}` map. -/
theorem memBesov_iff_exists_ckHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) {u : 𝓢'(E, F)} :
    u.MemBesov φ (k + α) ∞ ∞ ↔
      ∃ f : TauCeti.CkHolderSpace k α E F,
        (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u :=
  ⟨fun hu ↦ ⟨TauCeti.BesovSpace.toCkHolderSpace F φ k hα0 hα1 hu.toBesovSpace, by simp⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ f.memBesov φ⟩

end TemperedDistribution
