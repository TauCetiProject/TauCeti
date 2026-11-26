/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import TauCeti.Analysis.Complex.Theta.Fourier
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Analysis.Complex.Theta.Vanishing
import TauCeti.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Characteristic theta basis and finite-dimensionality of level-`k` theta sections

Fix `k : ℕ`, `τ` in the upper half-plane and real characteristics `α, β`. An explicit basis of
`TauCeti.thetaSections k τ α β` consists of the theta functions with characteristics
`θ_r(z) = e^{2πi(r + α)z} θ(kz + (r + α)τ - β, kτ)` for `0 ≤ r < k`
(`TauCeti.characteristicTheta`), where `θ = jacobiTheta₂` is Mathlib's two-variable Jacobi theta
function. The coordinates of a section `s` in this basis are its twisted Fourier coefficients
`thetaFourierCoeff α s r` (`TauCeti.thetaSectionsBasis_repr_apply`).

For `k > 0` and `0 < τ.im`, integrating the theta series termwise
(`TauCeti.integral_cexp_mul_jacobiTheta₂_mul_add`) computes all twisted Fourier coefficients of
`θ_r`: they vanish off the congruence class `r + kℤ` and are explicit Gaussian exponentials on
`r + kℤ`, yielding `thetaFourierCoeff α θ_r r' = δ_{rr'}` for `r, r' : Fin k`. Combined with
the shift-by-`k` recurrence and Fourier uniqueness from `TauCeti.Analysis.Complex.Theta.Fourier`,
`s ↦ (thetaFourierCoeff α s 0, …, thetaFourierCoeff α s (k - 1))` is a linear isomorphism onto
`Fin k → ℂ`, giving the basis `TauCeti.thetaSectionsBasis` and the dimension formula
`TauCeti.finrank_thetaSections`. Outside the positive-level upper half-plane regime,
`TauCeti.finrank_thetaSections_of_im_nonpos` and `TauCeti.finrank_thetaSections_zero` record
the boundary and level-`0` dimension formulas.

## Main definitions

* `TauCeti.characteristicTheta k τ α β r`: the theta function `θ_r` with characteristics.
* `TauCeti.thetaSectionsBasis`: for `k > 0` and `im τ > 0`, the basis `(θ_r)_{0 ≤ r < k}` of
  `thetaSections k τ α β`.

## Main results

* `TauCeti.characteristicTheta_mem_thetaSections`: each `θ_r` is a section.
* `TauCeti.hasSum_characteristicTheta`, `TauCeti.thetaFourierCoeff_characteristicTheta_add_mul`,
  `TauCeti.thetaFourierCoeff_characteristicTheta_eq_zero`, and
  `TauCeti.thetaFourierCoeff_characteristicTheta_fin`: explicit Fourier series and twisted Fourier
  coefficients of `characteristicTheta`.
* `TauCeti.thetaSectionsBasis_apply`, `TauCeti.thetaSectionsBasis_repr_apply`, and
  `TauCeti.eq_sum_characteristicTheta_of_mem_thetaSections`: the basis vectors are the `θ_r`, the
  coordinates are `thetaFourierCoeff`, and every section of positive level is the finite linear
  combination of the `θ_r` weighted by its first `k` twisted Fourier coefficients.
* `TauCeti.finrank_thetaSections`: for `k > 0` and `im τ > 0`, `thetaSections k τ α β` has
  dimension `k`.
* `TauCeti.finrank_thetaSections_of_im_nonpos`: vanishing dimension for `0 < k` and `τ.im ≤ 0`.
* `TauCeti.finrank_thetaSections_zero`: complete dimension formula at level `k = 0` for `τ.im ≠ 0`.

## References

* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapters I and II.
-/

public section

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace TauCeti

variable {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}

/-- The theta function of level `k` with characteristics `(α, β)` and index `r`:
`θ_r(z) = e^{2πi(r + α)z} θ(kz + (r + α)τ - β, kτ)`, where `θ = jacobiTheta₂`. Its Fourier series is
`∑_n e^{πikn²τ + 2πin((r + α)τ - β)} e^{2πi(r + kn + α)z}`, supported on the frequencies `≡ r`
modulo `k`. -/
noncomputable def characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ)

/-- Unfolding `TauCeti.characteristicTheta`. -/
theorem characteristicTheta_apply (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r z =
      cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) :=
  (rfl)

/-- Each theta function with characteristics is a section of the level-`k` theta line. -/
theorem characteristicTheta_mem_thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    characteristicTheta k τ α β r ∈ thetaSections k τ α β := by
  refine mem_thetaSections_iff.mpr ⟨?_, fun z ↦ ?_, fun z ↦ ?_⟩
  · by_cases hτ : 0 < (k * τ).im
    · intro z
      exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ cexp (2 * π * I * (r + α) * z)) z).mul
        ((differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop))
    · have h0 : characteristicTheta k τ α β r = 0 := funext fun z ↦ by
        simp [characteristicTheta_apply, jacobiTheta₂_undef _ (not_lt.1 hτ)]
      rw [h0]
      exact differentiable_const 0
  · have hθ : jacobiTheta₂ (k * (z + 1) + (r + α) * τ - β) (k * τ) =
        jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) := by
      have hper : Function.Periodic (jacobiTheta₂ · (k * τ)) 1 :=
        fun w ↦ jacobiTheta₂_add_left w (k * τ)
      convert hper.nat_mul k (k * z + (r + α) * τ - β) using 2
      ring
    rw [characteristicTheta_apply, characteristicTheta_apply, hθ, ← mul_assoc, ← exp_add,
      show 2 * π * I * (r + α) * (z + 1) =
        2 * π * I * α + 2 * π * I * (r + α) * z + r * (2 * π * I) by ring,
      exp_add _ (r * (2 * π * I)), exp_int_mul_two_pi_mul_I, mul_one]
  · have hθ : jacobiTheta₂ (k * (z + τ) + (r + α) * τ - β) (k * τ) =
        cexp (-π * I * (k * τ + 2 * (k * z + (r + α) * τ - β))) *
          jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) := by
      rw [← jacobiTheta₂_add_left']
      ring_nf
    rw [characteristicTheta_apply, characteristicTheta_apply, hθ, ← mul_assoc, ← mul_assoc,
      ← exp_add, ← exp_add]
    ring_nf

/-- At level `k = 1`, zero characteristics, and `r = 0`, `characteristicTheta` reduces to
`jacobiTheta₂`. -/
@[simp]
theorem characteristicTheta_one_zero (τ z : ℂ) :
    characteristicTheta 1 τ 0 0 0 z = jacobiTheta₂ z τ := by
  simp [characteristicTheta_apply]

private lemma im_natCast_mul (k : ℕ) (τ : ℂ) : ((k : ℂ) * τ).im = k * τ.im := by
  rw [← ofReal_natCast, im_ofReal_mul]

private lemma im_natCast_mul_pos {k : ℕ} {τ : ℂ} (hk : 0 < k) (hτ : 0 < τ.im) :
    0 < ((k : ℂ) * τ).im := by
  rw [im_natCast_mul]
  exact mul_pos (Nat.cast_pos.mpr hk) hτ

/-- When `k = 0` or `τ.im ≤ 0`, `characteristicTheta` vanishes identically (inheriting the
junk-value convention `jacobiTheta₂_undef`). -/
theorem characteristicTheta_undef {k : ℕ} {τ : ℂ} (h : k = 0 ∨ τ.im ≤ 0) (α β : ℝ) (r : ℤ)
    (z : ℂ) : characteristicTheta k τ α β r z = 0 := by
  have him : (k * τ).im ≤ 0 := by
    rw [im_natCast_mul]
    rcases h with rfl | hτ
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hτ
  simp [characteristicTheta_apply, jacobiTheta₂_undef _ him]

/-- At level `k = 0`, `characteristicTheta` vanishes identically. -/
@[simp]
theorem characteristicTheta_zero (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta 0 τ α β r z = 0 :=
  characteristicTheta_undef (Or.inl rfl) α β r z

/-- When `τ.im ≤ 0`, `characteristicTheta` vanishes identically. -/
@[simp]
theorem characteristicTheta_of_im_nonpos (k : ℕ) {τ : ℂ} (hτ : τ.im ≤ 0) (α β : ℝ) (r : ℤ)
    (z : ℂ) : characteristicTheta k τ α β r z = 0 :=
  characteristicTheta_undef (Or.inr hτ) α β r z

/-- First generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_one (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + 1) =
      cexp (2 * π * I * α) * characteristicTheta k τ α β r z :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).right.left z

/-- Second generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_tau (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + τ) =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
        characteristicTheta k τ α β r z :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).right.right z

/-- Shifting the characteristic index `r` by the level `k` multiplies `characteristicTheta` by a
nonzero scalar depending only on `(k, τ, α, β, r)`. -/
theorem characteristicTheta_index_add_level (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β (r + k) z =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * (r + α) * τ) *
        characteristicTheta k τ α β r z := by
  have harg : k * z + ((r + k : ℤ) + α) * τ - β = (k * z + (r + α) * τ - β) + k * τ := by
    push_cast
    ring
  rw [characteristicTheta_apply, characteristicTheta_apply, harg, jacobiTheta₂_add_left',
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every `characteristicTheta k τ α β r` is an entire function of `z` (for all `k : ℕ` and
`τ : ℂ`). -/
theorem differentiable_characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    Differentiable ℂ (characteristicTheta k τ α β r) :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).left

/-- Mathlib's `jacobiTheta₂ · τ` is a level-`1` theta section with zero characteristics for every
`τ : ℂ`. -/
theorem jacobiTheta₂_mem_thetaSections (τ : ℂ) :
    (fun z => jacobiTheta₂ z τ) ∈ thetaSections 1 τ 0 0 := by
  have hfun : (fun z => jacobiTheta₂ z τ) = characteristicTheta 1 τ 0 0 0 :=
    funext fun z => (characteristicTheta_one_zero τ z).symm
  rw [hfun]
  exact characteristicTheta_mem_thetaSections 1 τ 0 0 0

/-- Explicit `ℤ`-indexed Fourier series of `characteristicTheta k τ α β r` supported on the
congruence class `r + kℤ`, for `0 < k` and `0 < τ.im`. -/
theorem hasSum_characteristicTheta {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : ℤ) (z : ℂ) :
    HasSum
      (fun n : ℤ =>
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) *
          cexp (2 * π * I * ((r + n * k : ℤ) + α) * z))
      (characteristicTheta k τ α β r z) := by
  have hsum := (hasSum_jacobiTheta₂_term (k * z + (r + α) * τ - β)
    (im_natCast_mul_pos hk hτ)).mul_left (cexp (2 * π * I * (r + α) * z))
  rw [← characteristicTheta_apply] at hsum
  refine hsum.congr_fun fun n => ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma thetaFourierCoeff_characteristicTheta_eq {k : ℕ} (hk : 0 < k) {τ : ℂ}
    (hτ : 0 < τ.im) (α β : ℝ) (r m : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m =
      if (k : ℤ) ∣ m - r then
        let n : ℤ := (m - r) / k
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ)
      else 0 := by
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hint := integral_cexp_mul_jacobiTheta₂_mul_add hk0 (r - m) ((r + α) * τ - β)
    (im_natCast_mul_pos hk hτ)
  have hcongr :
      thetaFourierCoeff α (characteristicTheta k τ α β r) m =
        ∫ x in (0 : ℝ)..1,
          cexp (2 * π * I * (r - m : ℤ) * x) *
            jacobiTheta₂ (((k : ℤ) : ℂ) * x + ((r + α) * τ - β)) (k * τ) := by
    rw [thetaFourierCoeff_eq_integral]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [characteristicTheta_apply, ← mul_assoc, ← Complex.exp_add]
    congr 2
    · push_cast; ring
    · push_cast; ring
  have hdvd : ((k : ℤ) ∣ r - m) ↔ ((k : ℤ) ∣ m - r) := by
    rw [← dvd_neg, neg_sub]
  rw [hcongr, hint]
  simp only [hdvd]
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    have hrm : r - m = (k : ℤ) * (-n) := by linarith
    rw [hn, hrm, Int.mul_ediv_cancel_left _ hk0, Int.mul_ediv_cancel_left _ hk0, neg_neg,
      jacobiTheta₂_term]
    congr 1
    ring
  · rfl

/-- On the congruence class `r + kℤ`, the twisted Fourier coefficients of `characteristicTheta`
are given by the explicit Gaussian exponentials. -/
theorem thetaFourierCoeff_characteristicTheta_add_mul {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r n : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) (r + n * k) =
      cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) := by
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hdvd : (k : ℤ) ∣ (r + n * k) - r := by
    rw [add_sub_cancel_left]
    exact dvd_mul_left (k : ℤ) n
  have hdiv : ((r + n * (k : ℤ)) - r) / (k : ℤ) = n := by
    rw [add_sub_cancel_left, Int.mul_ediv_cancel n hk0]
  rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r (r + n * k)]
  simp only [hdvd, ↓reduceIte, hdiv]

/-- Off the congruence class `r + kℤ`, all twisted Fourier coefficients of `characteristicTheta`
vanish. -/
theorem thetaFourierCoeff_characteristicTheta_eq_zero (k : ℕ) (τ : ℂ) (α β : ℝ) {r m : ℤ}
    (h : ¬ (k : ℤ) ∣ m - r) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hzero : characteristicTheta 0 τ α β r = 0 :=
      funext fun z => characteristicTheta_undef (Or.inl rfl) α β r z
    simp [hzero]
  · rcases le_or_gt τ.im 0 with hτ | hτ
    · have hzero : characteristicTheta k τ α β r = 0 :=
        funext fun z => characteristicTheta_undef (Or.inr hτ) α β r z
      simp [hzero]
    · rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r m, ite_eq_right h]

/-- Duality between the `k` characteristic theta functions and the first `k` twisted Fourier
coefficients. -/
@[simp]
theorem thetaFourierCoeff_characteristicTheta_fin {k : ℕ} {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r r' : Fin k) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) r' = if r' = r then 1 else 0 := by
  by_cases hrr : r' = r
  · subst hrr
    simpa using thetaFourierCoeff_characteristicTheta_add_mul r'.pos hτ α β (r' : ℤ) 0
  · rw [ite_eq_right hrr]
    refine thetaFourierCoeff_characteristicTheta_eq_zero k τ α β fun hdvd => hrr ?_
    have hr1 : (r : ℤ) < k := Int.ofNat_lt.mpr r.isLt
    have hr2 : (r' : ℤ) < k := Int.ofNat_lt.mpr r'.isLt
    have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
    exact Fin.ext (by omega)

/-! ### Basis construction and dimension formula -/

/-- The coefficient map `s ↦ (thetaFourierCoeff α s 0, …, thetaFourierCoeff α s (k - 1))` on
sections. -/
private noncomputable def thetaCoeffMap (k : ℕ) (τ : ℂ) (α β : ℝ) :
    thetaSections k τ α β →ₗ[ℂ] (Fin k → ℂ) where
  toFun s r := thetaFourierCoeff α (s : ℂ → ℂ) r
  map_add' s t := funext fun r => by
    have hs : IntervalIntegrable (fun x : ℝ => (s : ℂ → ℂ) x) volume 0 1 :=
      ((mem_thetaSections_iff.mp s.property).1.continuous.comp
        continuous_ofReal).intervalIntegrable 0 1
    have ht : IntervalIntegrable (fun x : ℝ => (t : ℂ → ℂ) x) volume 0 1 :=
      ((mem_thetaSections_iff.mp t.property).1.continuous.comp
        continuous_ofReal).intervalIntegrable 0 1
    exact thetaFourierCoeff_add hs ht r
  map_smul' c s := funext fun r => thetaFourierCoeff_smul α c (s : ℂ → ℂ) r

@[simp]
private lemma thetaCoeffMap_apply (s : thetaSections k τ α β) (r : Fin k) :
    thetaCoeffMap k τ α β s r = thetaFourierCoeff α (s : ℂ → ℂ) r :=
  (rfl)

private lemma thetaCoeffMap_characteristicTheta (hτ : 0 < τ.im) (r : Fin k) :
    thetaCoeffMap k τ α β ⟨_, characteristicTheta_mem_thetaSections k τ α β r⟩ =
      Pi.single r 1 := by
  funext m
  rw [thetaCoeffMap_apply, thetaFourierCoeff_characteristicTheta_fin hτ α β r m, Pi.single_apply]

private lemma thetaCoeffMap_bijective (hk : 0 < k) (hτ : 0 < τ.im) :
    Function.Bijective (thetaCoeffMap k τ α β) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ Subtype.ext ?_, fun v ↦ ?_⟩
  · refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α)
      (mem_thetaSections_iff.mp s.property).1 fun m ↦ ?_
    have hk' : (0 : ℤ) < k := Int.natCast_pos.mpr hk
    rw [← Int.emod_add_mul_ediv m k, mul_comm (k : ℤ),
      thetaFourierCoeff_add_int_mul_eq_zero_iff s.property]
    have hlt : (m % k).toNat < k := by
      have := Int.emod_nonneg m hk'.ne'
      have := Int.emod_lt_of_pos m hk'
      omega
    have hcongr := congr_fun hs ⟨(m % k).toNat, hlt⟩
    simpa [Int.toNat_of_nonneg (Int.emod_nonneg m hk'.ne')] using hcongr
  · refine ⟨∑ r, v r • ⟨_, characteristicTheta_mem_thetaSections k τ α β r⟩, ?_⟩
    simp only [map_sum, map_smul, thetaCoeffMap_characteristicTheta hτ]
    ext m
    simp [Pi.single_apply]

/-- The basis of the level-`k` theta sections given by the theta functions with characteristics
`θ_r`, `0 ≤ r < k` (`TauCeti.thetaSectionsBasis_apply`). The coordinate of a section `s` along
`θ_r` is its twisted Fourier coefficient `TauCeti.thetaFourierCoeff α s r`
(`TauCeti.thetaSectionsBasis_repr_apply`). -/
noncomputable def thetaSectionsBasis (hk : 0 < k) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.Basis (Fin k) ℂ (thetaSections k τ α β) :=
  .ofEquivFun (.ofBijective _ (thetaCoeffMap_bijective (α := α) (β := β) hk hτ))

/-- The basis vectors of `TauCeti.thetaSectionsBasis` are the theta functions with
characteristics. -/
@[simp]
theorem thetaSectionsBasis_apply (hk : 0 < k) (hτ : 0 < τ.im) (r : Fin k) :
    (thetaSectionsBasis hk hτ α β r : ℂ → ℂ) = characteristicTheta k τ α β (r : ℕ) := by
  have h : (LinearEquiv.ofBijective _ (thetaCoeffMap_bijective (α := α) (β := β) hk hτ)).symm
      (Pi.single r 1) = ⟨_, characteristicTheta_mem_thetaSections k τ α β (r : ℕ)⟩ :=
    (LinearEquiv.symm_apply_eq _).2 (thetaCoeffMap_characteristicTheta hτ r).symm
  rw [thetaSectionsBasis, Module.Basis.coe_ofEquivFun]
  exact congrArg Subtype.val h

/-- The coordinates of a section in `TauCeti.thetaSectionsBasis` are its twisted Fourier
coefficients `TauCeti.thetaFourierCoeff α s r`. -/
theorem thetaSectionsBasis_repr_apply (hk : 0 < k) (hτ : 0 < τ.im) (s : thetaSections k τ α β)
    (r : Fin k) :
    (thetaSectionsBasis hk hτ α β).repr s r = thetaFourierCoeff α (s : ℂ → ℂ) r := by
  rw [thetaSectionsBasis, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.ofBijective_apply,
    thetaCoeffMap_apply]

/-- **Kähler quantization of the degree-`k` torus.** For `k > 0` and `τ` in the upper half-plane,
the level-`k` theta line on `ℂ / (ℤ + τℤ)` has exactly `k` linearly independent holomorphic
sections, whatever the characteristics `(α, β)`. -/
theorem finrank_thetaSections (hk : 0 < k) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.finrank ℂ (thetaSections k τ α β) = k := by
  simp [Module.finrank_eq_card_basis (thetaSectionsBasis hk hτ α β)]

/-- For positive level `k > 0` and `τ.im ≤ 0`, `thetaSections k τ α β` has dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, finrank_bot]

open scoped Classical in
/-- **Complete dimension formula at level `k = 0`.** For any non-real period `τ` (`τ.im ≠ 0`), the
space `thetaSections 0 τ α β` has dimension `1` when both characteristics are integers (the
trivial flat line bundle) and dimension `0` otherwise. -/
theorem finrank_thetaSections_zero (τ : ℂ) (hτ : τ.im ≠ 0) (α β : ℝ) :
    Module.finrank ℂ (thetaSections 0 τ α β) =
      if (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β) then 1 else 0 := by
  by_cases h : (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β)
  · rw [ite_eq_left h]
    have h1 : (fun _ : ℂ => (1 : ℂ)) ∈ thetaSections 0 τ α β :=
      (mem_thetaSections_zero_iff_const hτ h.left h.right).mpr ⟨1, rfl⟩
    refine finrank_eq_one ⟨fun _ => 1, h1⟩ ?_ fun s => ?_
    · intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      exact one_ne_zero this
    · obtain ⟨c, hc⟩ := (mem_thetaSections_zero_iff_const hτ h.left h.right).mp s.property
      refine ⟨c, Subtype.ext ?_⟩
      ext z
      simp [hc]
  · rw [ite_eq_right h, thetaSections_zero_eq_bot_of_not_int hτ h, finrank_bot]

/-- Every level-`k` theta section (`0 < k`) is the finite linear combination of the `k`
characteristic theta functions weighted by its first `k` twisted Fourier coefficients. -/
theorem eq_sum_characteristicTheta_of_mem_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s z = ∑ r : Fin k, thetaFourierCoeff α s r * characteristicTheta k τ α β r z := by
  rcases lt_or_ge 0 τ.im with hτ | hτ
  · have hrepr := (thetaSectionsBasis hk hτ α β).sum_repr ⟨s, hs⟩
    have hval := congrFun (congrArg Subtype.val hrepr.symm) z
    rw [Submodule.coe_sum, Finset.sum_apply] at hval
    refine hval.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, thetaSectionsBasis_repr_apply,
      thetaSectionsBasis_apply]
  · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, Submodule.mem_bot] at hs
    simp [hs]

end TauCeti
