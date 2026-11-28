/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Heights of inverse ratios of Hecke values from test-form pairings

This file isolates the inner-product factorization and height-assembly steps for the inverse
ratios of twisted Hecke values along a regular family of twists, corresponding to §§6.5 and 6.6
of `ShortGRH / NormsOfThetaLiftsAndExchangeIdentities`.

First, orthogonal projection onto the line spanned by a vector `φ` satisfies the rank-one
factorization `‖φ‖² · ⟪pr Ξ, pr Ξ'⟫ = ⟪Ξ, φ⟫ · ⟪φ, Ξ'⟫` (with no nonvanishing assumption on `φ`).
Second, combining this factorization with an untwisted norm height, a projection-denominator
bound, an auxiliary ramified-ratio height, and two test-form pairing lower bounds produces the
four-factor height bound `c_untw + β_tot + 2 * c_ram + 2 * c_A + c_fin` for the inverse ratio.
Third, assembling squared products of main and ramified ratios (up to coprime integer powers)
produces the exchange-product inverse height bound of §6.6.

## Main results

* `norm_sq_mul_inner_starProjection_span_singleton`: rank-one orthogonal projection factorization.
* `inner_mul_inner_div_inner_starProjection_span_singleton`: quotient form when the projected
  pairing is nonzero.
* `heightLe_inv_ratio_of_testPairings`: the four-factor height bound for an inverse ratio from
  test-form pairings (§6.5).
* `heightLe_inv_heckeValueProd_div`: inverse height bound for a squared product of main and
  ramified ratios up to coprime integer powers (§6.6).
* `heightLe_inv_heckeValueProd_div_of_cutoff`: cutoff-partition specialization splitting a main
  factor range at a threshold `z_cut` together with two auxiliary ramified ranges.

## References

The statements follow [ShortProof](https://github.com/lsernau/grh-lean), `lsernau/grh-lean` at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`, file
`grh/src/New/OneLift/HeckeValues/TwistedValueHeights.lean` (`New.Data.heightLe_inv_ratio`,
`New.Data.heightLe_inv_heckeValueProd_div`). Directly reuses `TauCeti.PrimePadicIso.HeightLe`.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.ThetaLift

section RankOneProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Rank-one orthogonal projection factorization onto `𝕜 ∙ φ`:
`(‖φ‖ : 𝕜) ^ 2 * ⟪pr Ξ, pr Ξ'⟫_𝕜 = ⟪Ξ, φ⟫_𝕜 * ⟪φ, Ξ'⟫_𝕜`. -/
theorem norm_sq_mul_inner_starProjection_span_singleton (φ Ξ Ξ' : E) :
    let pr := (𝕜 ∙ φ).starProjection
    ((‖φ‖ : 𝕜) ^ 2) * ⟪pr Ξ, pr Ξ'⟫_𝕜 = ⟪Ξ, φ⟫_𝕜 * ⟪φ, Ξ'⟫_𝕜 := by
  intro pr
  by_cases hφ : φ = 0
  · subst hφ
    simp
  have hnorm : ((‖φ‖ : 𝕜) ^ 2) = ⟪φ, φ⟫_𝕜 := by
    rw [inner_self_eq_norm_sq_to_K]
  have hne : ⟪φ, φ⟫_𝕜 ≠ 0 := by
    rw [← hnorm]
    exact pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr hφ)
  have hpr (v : E) : pr v = (⟪φ, v⟫_𝕜 / ⟪φ, φ⟫_𝕜) • φ := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)
    · intro w hw
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [inner_sub_left, inner_smul_left, inner_smul_right, inner_smul_right,
        map_div₀, inner_conj_symm, inner_self_conj]
      field_simp [hne]
      ring
  rw [hpr Ξ, hpr Ξ', inner_smul_left, inner_smul_right, map_div₀, inner_conj_symm,
    inner_self_conj, hnorm]
  field_simp [hne]

/-- Quotient form of the rank-one projection factorization: when `⟪pr Ξ, pr Ξ'⟫_𝕜 ≠ 0`,
`⟪Ξ, φ⟫_𝕜 * ⟪φ, Ξ'⟫_𝕜 / ⟪pr Ξ, pr Ξ'⟫_𝕜 = (‖φ‖ : 𝕜) ^ 2`. -/
theorem inner_mul_inner_div_inner_starProjection_span_singleton {φ Ξ Ξ' : E}
    (h : ⟪(𝕜 ∙ φ).starProjection Ξ, (𝕜 ∙ φ).starProjection Ξ'⟫_𝕜 ≠ 0) :
    ⟪Ξ, φ⟫_𝕜 * ⟪φ, Ξ'⟫_𝕜 / ⟪(𝕜 ∙ φ).starProjection Ξ, (𝕜 ∙ φ).starProjection Ξ'⟫_𝕜 =
      (‖φ‖ : 𝕜) ^ 2 := by
  rw [← norm_sq_mul_inner_starProjection_span_singleton φ Ξ Ξ', mul_div_cancel_right₀ _ h]

end RankOneProjection

section HeckeValueHeights

open TauCeti.PrimePadicIso

/-- A local exponential bound `‖ι.iso (Q ι)‖ ≤ exp (γ ι.prime)` whose finite prime sums are
bounded by `β_tot` gives `HeightLe Q β_tot`. -/
theorem heightLe_of_norm_iso_le_exp {Q : TauCeti.PrimePadicIso → ℂ} {γ : ℕ → ℝ} {β_tot : ℝ}
    (hQ : ∀ ι : TauCeti.PrimePadicIso, ‖ι.iso (Q ι)‖ ≤ Real.exp (γ ι.prime))
    (hγ : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, γ ℓ ≤ β_tot) :
    HeightLe Q β_tot := by
  refine HeightLe.of_mul_le (H := 1) one_ne_zero (α := 0) (fun σ ↦ by simp) γ
    (fun ι ↦ by simpa using hQ ι) (fun S hS ↦ by simpa using hγ S hS)

/-- Two lower bounds `‖ι.iso (c₀ * r₂ ι)‖ * ι.prime ^ (-S_p ι.prime) ≤ ‖ι.iso (P_k ι)‖`
together with `‖σ c₀‖ ≤ exp c_A` and `2 * ∑_{ℓ ∈ S} S_p ℓ * log ℓ ≤ c_fin` give a height bound
for `ι ↦ (r₂ ι) ^ 2 / (P₁ ι * P₂ ι)`. -/
theorem heightLe_sq_div_mul_of_norm_lower_bounds
    {P₁ P₂ r₂ : TauCeti.PrimePadicIso → ℂ} {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    {c_A c_fin : ℝ} {S_p : ℕ → ℝ}
    (hc_arch : ∀ σ : ℂ ≃+* ℂ, ‖σ c₀‖ ≤ Real.exp c_A)
    (hP₁ : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) ≤ ‖ι.iso (P₁ ι)‖)
    (hP₂ : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) ≤ ‖ι.iso (P₂ ι)‖)
    (hS : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → 2 * ∑ ℓ ∈ S, S_p ℓ * Real.log ℓ ≤ c_fin) :
    HeightLe (fun ι ↦ (r₂ ι) ^ 2 / (P₁ ι * P₂ ι)) (2 * c_A + c_fin) := by
  refine HeightLe.of_mul_le (H := c₀ ^ 2) (pow_ne_zero 2 hc₀) (α := 2 * c_A) (fun σ ↦ ?_)
    (fun ℓ ↦ 2 * S_p ℓ * Real.log ℓ) (fun ι ↦ ?_) (fun S hSp ↦ ?_)
  · rw [map_pow, norm_pow, two_mul, Real.exp_add, sq]
    exact mul_le_mul (hc_arch σ) (hc_arch σ) (norm_nonneg _) (Real.exp_pos _).le
  · by_cases hP : P₁ ι * P₂ ι = 0
    · simp [hP, (Real.exp_pos _).le]
    have hpos : (0 : ℝ) < ι.prime := by exact_mod_cast ι.fact_prime.out.pos
    have hPnorm : 0 < ‖ι.iso (P₁ ι * P₂ ι)‖ := norm_pos_iff.mpr ((map_ne_zero ι.iso).mpr hP)
    have hmul : ‖ι.iso (c₀ ^ 2 * (r₂ ι) ^ 2)‖ * (ι.prime : ℝ) ^ (-(2 * S_p ι.prime)) ≤
        ‖ι.iso (P₁ ι * P₂ ι)‖ := by
      have h12 := mul_le_mul (hP₁ ι) (hP₂ ι) (by positivity) (norm_nonneg _)
      calc
        ‖ι.iso (c₀ ^ 2 * (r₂ ι) ^ 2)‖ * (ι.prime : ℝ) ^ (-(2 * S_p ι.prime))
            = (‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime)) *
                (‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime)) := by
              rw [mul_mul_mul_comm, ← Real.rpow_add hpos, ← sq, ← norm_pow, ← map_pow, mul_pow]
              ring_nf
        _ ≤ ‖ι.iso (P₁ ι)‖ * ‖ι.iso (P₂ ι)‖ := h12
        _ = ‖ι.iso (P₁ ι * P₂ ι)‖ := by rw [map_mul, norm_mul]
    rw [mul_div_assoc', map_div₀, norm_div, div_le_iff₀ hPnorm]
    have hexp : Real.exp (2 * S_p ι.prime * Real.log ι.prime) =
        (ι.prime : ℝ) ^ (2 * S_p ι.prime) := by
      rw [Real.rpow_def_of_pos hpos, mul_comm]
    rw [hexp]
    calc
      ‖ι.iso (c₀ ^ 2 * (r₂ ι) ^ 2)‖
          = (‖ι.iso (c₀ ^ 2 * (r₂ ι) ^ 2)‖ * (ι.prime : ℝ) ^ (-(2 * S_p ι.prime))) *
              (ι.prime : ℝ) ^ (2 * S_p ι.prime) := by
            rw [mul_assoc, ← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ ‖ι.iso (P₁ ι * P₂ ι)‖ * (ι.prime : ℝ) ^ (2 * S_p ι.prime) :=
            mul_le_mul_of_nonneg_right hmul (Real.rpow_pos_of_pos hpos _).le
      _ = (ι.prime : ℝ) ^ (2 * S_p ι.prime) * ‖ι.iso (P₁ ι * P₂ ι)‖ := mul_comm _ _
  · have hsum : ∑ ℓ ∈ S, 2 * S_p ℓ * Real.log ℓ = 2 * ∑ ℓ ∈ S, S_p ℓ * Real.log ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ ↦ by ring
    linarith [hS S hSp]

/-- Four-factor height bound for the inverse ratio of a main pair from test-form pairings (§6.5).
No nonvanishing hypotheses on `N₀`, `N`, `P₁`, `P₂`, `Q`, or `ratio` are needed beyond `c₀ ≠ 0`
and `∀ ι, r₂ ι ≠ 0`. -/
theorem heightLe_inv_ratio_of_testPairings
    {N₀ c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    {ratio N P₁ P₂ Q r₂ : TauCeti.PrimePadicIso → ℂ}
    {Nm : TauCeti.PrimePadicIso → ℕ} {e : TauCeti.PrimePadicIso → ℤ}
    {γ S_p : ℕ → ℝ} {c_untw β_tot c_ram c_A c_fin : ℝ}
    (hNm : ∀ ι : TauCeti.PrimePadicIso, ι.prime.Coprime (Nm ι))
    (hratio : ∀ ι, ratio ι = (Nm ι : ℂ) ^ (e ι) * (N ι / N₀))
    (hfactor : ∀ ι, N ι * Q ι = P₁ ι * P₂ ι)
    (hr₂ : ∀ ι, r₂ ι ≠ 0)
    (h_untw : HeightLe (fun _ ↦ N₀) c_untw)
    (hQ : ∀ ι : TauCeti.PrimePadicIso, ‖ι.iso (Q ι)‖ ≤ Real.exp (γ ι.prime))
    (hγ : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, γ ℓ ≤ β_tot)
    (h_ram : HeightLe (fun ι ↦ (r₂ ι)⁻¹) c_ram)
    (hc_arch : ∀ σ : ℂ ≃+* ℂ, ‖σ c₀‖ ≤ Real.exp c_A)
    (hP₁ : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) ≤ ‖ι.iso (P₁ ι)‖)
    (hP₂ : ∀ ι : TauCeti.PrimePadicIso,
      ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) ≤ ‖ι.iso (P₂ ι)‖)
    (hS : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → 2 * ∑ ℓ ∈ S, S_p ℓ * Real.log ℓ ≤ c_fin) :
    HeightLe (fun ι ↦ (ratio ι)⁻¹) (c_untw + β_tot + 2 * c_ram + 2 * c_A + c_fin) := by
  have h1 := heightLe_of_norm_iso_le_exp hQ hγ
  have h2 := h_ram.pow 2
  have h3 := heightLe_sq_div_mul_of_norm_lower_bounds hc₀ hc_arch hP₁ hP₂ hS
  have hprod := ((h_untw.mul h1).mul h2).mul h3
  refine hprod.mono (by push_cast; linarith) fun ι ↦ ?_
  by_cases hN : ratio ι = 0
  · simp only [hN, inv_zero, map_zero, norm_zero, norm_nonneg]
  have hpos : (0 : ℝ) < ι.prime := by exact_mod_cast ι.fact_prime.out.pos
  have hP₁_ne : P₁ ι ≠ 0 := by
    intro h0
    have hlt : 0 < ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) :=
      mul_pos (norm_pos_iff.mpr ((map_ne_zero ι.iso).mpr (mul_ne_zero hc₀ (hr₂ ι))))
        (Real.rpow_pos_of_pos hpos _)
    have hle := hP₁ ι
    rw [h0, map_zero, norm_zero] at hle
    linarith
  have hP₂_ne : P₂ ι ≠ 0 := by
    intro h0
    have hlt : 0 < ‖ι.iso (c₀ * r₂ ι)‖ * (ι.prime : ℝ) ^ (-S_p ι.prime) :=
      mul_pos (norm_pos_iff.mpr ((map_ne_zero ι.iso).mpr (mul_ne_zero hc₀ (hr₂ ι))))
        (Real.rpow_pos_of_pos hpos _)
    have hle := hP₂ ι
    rw [h0, map_zero, norm_zero] at hle
    linarith
  have hN_ne : N ι ≠ 0 := by
    intro h0
    apply hN
    simp [hratio ι, h0]
  have hN₀_ne : N₀ ≠ 0 := by
    intro h0
    apply hN
    simp [hratio ι, h0]
  have hNm_norm : ‖ι.iso ((Nm ι : ℂ) ^ (e ι))‖ = 1 := by
    rw [map_zpow₀, norm_zpow, norm_natCast_eq_one ι (hNm ι), one_zpow]
  have hEq : (ratio ι)⁻¹ = ((Nm ι : ℂ) ^ (e ι))⁻¹ *
      (N₀ * Q ι * (r₂ ι)⁻¹ ^ 2 * ((r₂ ι) ^ 2 / (P₁ ι * P₂ ι))) := by
    have hfac := hfactor ι
    have hP_ne : P₁ ι * P₂ ι ≠ 0 := mul_ne_zero hP₁_ne hP₂_ne
    rw [hratio ι, mul_inv, inv_div]
    congr 1
    field_simp [hN_ne, hN₀_ne, hr₂ ι, hP_ne]
    rw [hfac]
  rw [hEq, map_mul, map_inv₀, norm_mul, norm_inv, hNm_norm, inv_one, one_mul]
  simp only [Pi.mul_apply, Pi.pow_apply]
  exact le_rfl

/-- Inverse height bound for a squared product of main and ramified ratios up to coprime integer
powers (§6.6). -/
theorem heightLe_inv_heckeValueProd_div {α β : Type*} [Fintype α] [Fintype β]
    {main : α → TauCeti.PrimePadicIso → ℂ} {ram : β → TauCeti.PrimePadicIso → ℂ}
    {Γ_ratio : TauCeti.PrimePadicIso → ℂ}
    {Nm : TauCeti.PrimePadicIso → ℕ} {e : TauCeti.PrimePadicIso → ℤ}
    {c_main c_ram : ℝ}
    (hNm : ∀ ι : TauCeti.PrimePadicIso, ι.prime.Coprime (Nm ι))
    (hΓ : ∀ ι, Γ_ratio ι = (Nm ι : ℂ) ^ (e ι) * ((∏ a, main a ι) * (∏ b, ram b ι)) ^ 2)
    (hmain : ∀ a, HeightLe (fun ι ↦ (main a ι)⁻¹) c_main)
    (hram : ∀ b, HeightLe (fun ι ↦ (ram b ι)⁻¹) c_ram) :
    HeightLe (fun ι ↦ (Γ_ratio ι)⁻¹)
      (2 * (Fintype.card β : ℝ) * c_ram + 2 * (Fintype.card α : ℝ) * c_main) := by
  have hM : HeightLe (∏ a : α, fun ι ↦ (main a ι)⁻¹) ((Fintype.card α : ℝ) * c_main) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      HeightLe.prod (s := (Finset.univ : Finset α)) fun a _ ↦ hmain a
  have hR : HeightLe (∏ b : β, fun ι ↦ (ram b ι)⁻¹) ((Fintype.card β : ℝ) * c_ram) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      HeightLe.prod (s := (Finset.univ : Finset β)) fun b _ ↦ hram b
  have hsq := (hR.mul hM).pow 2
  refine hsq.mono (by push_cast; linarith) fun ι ↦ ?_
  have hNm_norm : ‖ι.iso ((Nm ι : ℂ) ^ (e ι))‖ = 1 := by
    rw [map_zpow₀, norm_zpow, norm_natCast_eq_one ι (hNm ι), one_zpow]
  rw [hΓ ι, mul_inv, map_mul, map_inv₀, norm_mul, norm_inv, hNm_norm, inv_one, one_mul]
  have hinv : (((∏ a, main a ι) * (∏ b, ram b ι)) ^ 2)⁻¹ =
      ((∏ b, (ram b ι)⁻¹) * (∏ a, (main a ι)⁻¹)) ^ 2 := by
    rw [← inv_pow, mul_inv, mul_comm, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  rw [hinv]
  simp only [Pi.pow_apply, Pi.mul_apply, Finset.prod_apply]
  exact le_rfl

/-- Cutoff-partition specialization for three exchange factors (`p_*`, `p_+`, `p_-`): splitting
`Fin z_star` at `z_cut ≤ z_star` into `z_cut` ramified points and `z_star - z_cut` main points
yields the §6.6(b) height bound
`2 * (z_cut + z_plus + z_minus) * c_ram + 2 * (z_star - z_cut) * c_main`. -/
theorem heightLe_inv_heckeValueProd_div_of_cutoff {z_cut z_star z_plus z_minus : ℕ}
    (hcut : z_cut ≤ z_star)
    {r_star : Fin z_star → TauCeti.PrimePadicIso → ℂ}
    {r_plus : Fin z_plus → TauCeti.PrimePadicIso → ℂ}
    {r_minus : Fin z_minus → TauCeti.PrimePadicIso → ℂ}
    {Γ_ratio : TauCeti.PrimePadicIso → ℂ}
    {Nm : TauCeti.PrimePadicIso → ℕ} {e : TauCeti.PrimePadicIso → ℤ}
    {c_main c_ram : ℝ}
    (hNm : ∀ ι : TauCeti.PrimePadicIso, ι.prime.Coprime (Nm ι))
    (hΓ : ∀ ι, Γ_ratio ι = (Nm ι : ℂ) ^ (e ι) *
      ((∏ i : Fin z_star, r_star i ι) * (∏ i : Fin z_plus, r_plus i ι) *
        (∏ i : Fin z_minus, r_minus i ι)) ^ 2)
    (hmain : ∀ i : Fin z_star, z_cut ≤ i.val → HeightLe (fun ι ↦ (r_star i ι)⁻¹) c_main)
    (hram_star : ∀ i : Fin z_star, i.val < z_cut → HeightLe (fun ι ↦ (r_star i ι)⁻¹) c_ram)
    (hram_plus : ∀ i : Fin z_plus, HeightLe (fun ι ↦ (r_plus i ι)⁻¹) c_ram)
    (hram_minus : ∀ i : Fin z_minus, HeightLe (fun ι ↦ (r_minus i ι)⁻¹) c_ram) :
    HeightLe (fun ι ↦ (Γ_ratio ι)⁻¹)
      (2 * ((z_cut + z_plus + z_minus : ℕ) : ℝ) * c_ram +
        2 * ((z_star - z_cut : ℕ) : ℝ) * c_main) := by
  let mainIdx := {i : Fin z_star // z_cut ≤ i.val}
  let ramStarIdx := {i : Fin z_star // i.val < z_cut}
  let ramIdx := ramStarIdx ⊕ Fin z_plus ⊕ Fin z_minus
  have hcard_ramStar : Fintype.card ramStarIdx = z_cut := by
    have hbij : Function.Bijective (fun i : Fin z_cut ↦
        (⟨⟨i.val, lt_of_lt_of_le i.isLt hcut⟩, i.isLt⟩ : ramStarIdx)) := by
      refine ⟨fun a b hab ↦ ?_, fun ⟨⟨k, hk⟩, hk'⟩ ↦ ⟨⟨k, hk'⟩, rfl⟩⟩
      exact Fin.ext (by simpa using congrArg (fun x : ramStarIdx ↦ x.val.val) hab)
    exact (Fintype.card_of_bijective hbij).symm.trans (Fintype.card_fin z_cut)
  have hcard_main : Fintype.card mainIdx = z_star - z_cut := by
    have hbij : Function.Bijective (fun i : Fin (z_star - z_cut) ↦
        (⟨⟨z_cut + i.val, by omega⟩, Nat.le_add_right z_cut i.val⟩ : mainIdx)) := by
      refine ⟨fun a b hab ↦ ?_, fun ⟨⟨k, hk⟩, hk'⟩ ↦ ?_⟩
      · have h := congrArg (fun x : mainIdx ↦ x.val.val) hab
        exact Fin.ext (by dsimp at h; omega)
      · dsimp at hk'
        refine ⟨⟨k - z_cut, by omega⟩, Subtype.ext (Fin.ext ?_)⟩
        dsimp
        omega
    exact (Fintype.card_of_bijective hbij).symm.trans (Fintype.card_fin (z_star - z_cut))
  have hcard_ram : Fintype.card ramIdx = z_cut + z_plus + z_minus := by
    simp [ramIdx, hcard_ramStar, add_assoc]
  have hsplit (ι : TauCeti.PrimePadicIso) :
      ∏ i : Fin z_star, r_star i ι =
        (∏ a : mainIdx, r_star a.val ι) * (∏ b : ramStarIdx, r_star b.val ι) := by
    classical
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : Fin z_star ↦ z_cut ≤ i.val)]
    congr 1
    · rw [Finset.prod_subtype (p := fun i : Fin z_star ↦ z_cut ≤ i.val)
        (Finset.univ.filter fun i : Fin z_star ↦ z_cut ≤ i.val) (fun _ ↦ by simp)]
    · rw [Finset.prod_subtype (p := fun i : Fin z_star ↦ i.val < z_cut)
        (Finset.univ.filter fun i : Fin z_star ↦ ¬z_cut ≤ i.val) (fun _ ↦ by simp [not_le])]
  have h := heightLe_inv_heckeValueProd_div
    (main := fun a : mainIdx ↦ r_star a.val)
    (ram := Sum.elim (fun b : ramStarIdx ↦ r_star b.val) (Sum.elim r_plus r_minus))
    (Γ_ratio := Γ_ratio) (e := e) hNm
    (fun ι ↦ by
      rw [hΓ ι, hsplit ι]
      simp [Fintype.prod_sum_type, mul_assoc, mul_left_comm, mul_comm])
    (fun a ↦ hmain a.val a.property)
    (fun b ↦ by
      rcases b with b | b | b
      · exact hram_star b.val b.property
      · exact hram_plus b
      · exact hram_minus b)
  rwa [hcard_ram, hcard_main] at h

end HeckeValueHeights

end TauCeti.ThetaLift
