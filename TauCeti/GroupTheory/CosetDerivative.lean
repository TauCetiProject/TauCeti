/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Coset.Basic

/-!
# Coset-derivative congruences for finite-group logarithms

For a finite group `Γ`, a subgroup `H ≤ Γ`, a multiplicative map `ρ : Γ →* R`, a ring homomorphism
`σ : R →+* S` killing `m`, and an additive map `B : (ZMod m → ℤ) →+ R` whose right multiplication
by `p ∈ H` shifts the weight by a homomorphism `a : H →* Multiplicative (ZMod m)`, this file proves
that the coset derivative `∂ = -(∑ η, ρ η.out) * B ZMod.valMinAbs * (∑ η, ρ η.out⁻¹)` satisfies
`n • (∂ * (ρ g - 1)) ≡ (∑ k : Γ, ρ k) * Z` modulo `σ` for some `Z` annihilated by a left-invariant
operator `L` with `L * B 1 = 0`.

## Main definitions and results

* `TauCeti.cosetDerivative`: `-(∑ η : Γ ⧸ H, ρ η.out) * B ZMod.valMinAbs * (∑ η, ρ η.out⁻¹)`.
* `TauCeti.map_eq_of_weights_modEq`: an additive map on integer weights preserves congruence mod `m`
  under any ring homomorphism killing `m`.
* `TauCeti.exists_map_valMinAbs_mul_sub_one`: right multiplication of
  `B valMinAbs * (∑ η, ρ η.out⁻¹)` by `ρ g - 1` factors through `B 1` modulo `σ`.
* `TauCeti.exists_map_nsmul_mul_sub_one_eq_sum_mul`: `n • (cosetDerivative * (ρ g - 1))` factors
  through the global norm `∑ k : Γ, ρ k` modulo `σ` with cofactor annihilated by `L`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/OnePrime.lean` (`New.Patching.map_eq_of_weights_modEq`,
`New.Patching.exists_map_valMinAbs_mul_sub_one`,
`New.Patching.exists_map_nsmul_mul_sub_one_eq_sum_mul`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset MulAction ZMod

variable {Γ R S : Type*} [Group Γ] [Fintype Γ] [Ring R] [Ring S] {m : ℕ}

open scoped Classical in
/-- The coset derivative `-(∑ η, ρ η.out) * B valMinAbs * (∑ η, ρ η.out⁻¹)` attached to a subgroup
`H ≤ Γ` and an additive map `B : (ZMod m → ℤ) →+ R`. -/
noncomputable def cosetDerivative (ρ : Γ →* R) (H : Subgroup Γ) (B : (ZMod m → ℤ) →+ R) : R :=
  -((∑ η : Γ ⧸ H, ρ η.out) * B valMinAbs * (∑ η : Γ ⧸ H, ρ η.out⁻¹))

/-- If `(m : S) = 0`, an additive map `B : (ι → ℤ) →+ R` sends pointwise `ZMod m`-congruent
weights to elements with the same image under `σ : R →+* S`. -/
theorem map_eq_of_weights_modEq {σ : R →+* S} (hm : (m : S) = 0) {ι : Type*}
    (B : (ι → ℤ) →+ R) (f g : ι → ℤ) (h_congr : ∀ x : ι, (g x : ZMod m) = f x) :
    σ (B f) = σ (B g) := by
  choose d hd using fun x ↦ (intCast_eq_intCast_iff_dvd_sub (g x) (f x) m).mp (h_congr x)
  have h_sub : f = m • d + g := funext fun x ↦ by simp [← hd x]
  rw [h_sub, map_add, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, hm, zero_mul, zero_add]

open scoped Classical in
/-- If `B : (ZMod m → ℤ) →+ R` satisfies `B f * ρ p = B (fun x ↦ f (x - (a p).toAdd))` for all
`p : H`, then modulo `σ` killing `m`, `B valMinAbs * (∑ η, ρ η.out⁻¹) * (ρ g - 1)` equals
`B 1 * Q` for some `Q : R`. -/
theorem exists_map_valMinAbs_mul_sub_one (ρ : Γ →* R) {σ : R →+* S} (hm : (m : S) = 0)
    {H : Subgroup Γ} (a : H →* Multiplicative (ZMod m)) (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd))
    (g : Γ) :
    ∃ Q : R, σ (B valMinAbs * (∑ η : Γ ⧸ H, ρ η.out⁻¹) * (ρ g - 1)) = σ (B 1 * Q) := by
  let comp (η : Γ ⧸ H) : H :=
    ⟨(g • η).out⁻¹ * (g * η.out),
      QuotientGroup.eq.mp ((g • η).out_eq.trans (by
        conv_lhs => rw [← η.out_eq]
        rfl))⟩
  let k (η : Γ ⧸ H) : ZMod m := (a (comp η)).toAdd
  have permute : (∑ η : Γ ⧸ H, ρ η.out⁻¹) * ρ g = ∑ η : Γ ⧸ H, ρ (comp η) * ρ η.out⁻¹ := by
    have term_eq (η : Γ ⧸ H) : ρ (comp η) * ρ η.out⁻¹ = ρ (toPerm g η).out⁻¹ * ρ g := by
      simp [comp, mul_assoc, ← map_mul]
    rw [sum_mul]
    exact (Fintype.sum_equiv (toPerm g) _ _ term_eq).symm
  have shift (y : ZMod m) :
      σ (B fun x ↦ valMinAbs (x - y)) = σ (B valMinAbs - valMinAbs y • B 1) := by
    rw [← map_zsmul, ← map_sub]
    exact map_eq_of_weights_modEq hm B _ _ (by simp)
  have term_congr (η : Γ ⧸ H) :
      σ (B valMinAbs * (ρ (comp η) * ρ η.out⁻¹ - ρ η.out⁻¹)) =
        σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) :=
    calc σ (B valMinAbs * (ρ (comp η) * ρ η.out⁻¹ - ρ η.out⁻¹))
        = (σ (B fun x ↦ valMinAbs (x - k η)) - σ (B valMinAbs)) * σ (ρ η.out⁻¹) := by
          rw [mul_sub, ← mul_assoc, hB, ← sub_mul, map_mul, map_sub]
      _ = σ (-(valMinAbs (k η) • B 1) * ρ η.out⁻¹) := by
          rw [shift, ← map_sub, sub_sub_cancel_left, map_mul]
      _ = σ (B 1 * -(valMinAbs (k η) • ρ η.out⁻¹)) := by
          rw [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  refine ⟨∑ η : Γ ⧸ H, -(valMinAbs (k η) • ρ η.out⁻¹), ?_⟩
  rw [mul_assoc, mul_sub_one, permute, ← sum_sub_distrib, mul_sum, mul_sum, map_sum, map_sum]
  exact sum_congr rfl fun η _ ↦ term_congr η

/-- Under the hypotheses of `exists_map_valMinAbs_mul_sub_one`, if `ρ p * B 1 = B 1` for `p : H`,
`∑ p : H, ρ p⁻¹ * Ψ * ρ p = n`, `L * ρ g = L` for all `g : Γ`, `L * B 1 = 0`, and `R` has no
`#H`-torsion, then `n • (cosetDerivative ρ H B * (ρ g - 1))` factors through `∑ k : Γ, ρ k`
modulo `σ` with cofactor `Z` satisfying `L * Z = 0`. -/
theorem exists_map_nsmul_mul_sub_one_eq_sum_mul (ρ : Γ →* R) {σ : R →+* S} (hm : (m : S) = 0)
    {H : Subgroup Γ} [Fintype H] (a : H →* Multiplicative (ZMod m)) (B : (ZMod m → ℤ) →+ R)
    (hB : ∀ (f : ZMod m → ℤ) (p : H), B f * ρ p = B fun x : ZMod m ↦ f (x - (a p).toAdd))
    (hB_fixed : ∀ p : H, ρ p * B 1 = B 1) {Ψ L : R} {n : ℕ}
    (hΨ : ∑ p : H, ρ ↑p⁻¹ * Ψ * ρ p = n) (hL : ∀ g : Γ, L * ρ g = L) (hLB : L * B 1 = 0)
    (h_regular : IsSMulRegular R (Fintype.card H)) (g : Γ) :
    ∃ Z : R,
      σ (n • (cosetDerivative ρ H B * (ρ g - 1))) = σ ((∑ k : Γ, ρ k) * Z) ∧
      L * Z = 0 := by
  classical
  obtain ⟨Q, hQ⟩ := exists_map_valMinAbs_mul_sub_one ρ (σ := σ) hm a B hB g
  have sum_inv : ∑ p : H, ρ ↑p⁻¹ = ∑ p : H, ρ p :=
    Equiv.sum_comp (.inv H) (fun p : H ↦ ρ p)
  have nsmul_B_one : n • B 1 = (∑ p : H, ρ p) * Ψ * B 1 :=
    calc n • B 1 = (∑ p : H, ρ ↑p⁻¹ * Ψ * ρ p) * B 1 := by rw [hΨ, nsmul_eq_mul]
      _ = (∑ p : H, ρ ↑p⁻¹) * Ψ * B 1 := by simp only [sum_mul, mul_assoc, hB_fixed]
      _ = (∑ p : H, ρ p) * Ψ * B 1 := by rw [sum_inv]
  have h_coset : (∑ η : Γ ⧸ H, ρ η.out) * (∑ p : H, ρ p) = ∑ k : Γ, ρ k := by
    rw [sum_mul_sum, ← sum_product']
    refine sum_nbij' (fun (η, p) ↦ η.out * p)
      (fun k ↦ (↑k, ⟨(k : Γ ⧸ H).out⁻¹ * k, QuotientGroup.eq.mp (k : Γ ⧸ H).out_eq⟩))
      (by simp) (by simp) ?_ (by simp) (fun ⟨η, p⟩ _ ↦ by simp [map_mul])
    rintro ⟨η, p⟩ -
    simp [QuotientGroup.mk_mul_of_mem _ p.property]
  refine ⟨-(Ψ * B 1 * Q), ?_, ?_⟩
  · calc σ (n • (cosetDerivative ρ H B * (ρ g - 1)))
        = -(σ (∑ η : Γ ⧸ H, ρ η.out) *
            n • σ (B valMinAbs * (∑ η : Γ ⧸ H, ρ η.out⁻¹) * (ρ g - 1))) := by
          simp only [cosetDerivative, neg_mul, smul_neg, map_neg, map_nsmul, map_mul,
            mul_smul_comm, mul_assoc]
      _ = σ (-((∑ η : Γ ⧸ H, ρ η.out) * (n • B 1 * Q))) := by
          simp only [hQ, map_neg, map_nsmul, map_mul, smul_mul_assoc]
      _ = σ ((∑ k : Γ, ρ k) * -(Ψ * B 1 * Q)) := by
          simp only [nsmul_B_one, ← h_coset, mul_neg, mul_assoc]
  · have L_mul_eq_zero : L * (Ψ * B 1) = 0 := h_regular <|
      calc Fintype.card H • (L * (Ψ * B 1)) = L * ((∑ p : H, ρ p) * Ψ * B 1) := by
            simp only [sum_mul, mul_sum, ← mul_assoc, hL, sum_const, card_univ]
        _ = Fintype.card H • 0 := by rw [← nsmul_B_one, mul_smul_comm, hLB, smul_zero, smul_zero]
    rw [mul_neg, ← mul_assoc, L_mul_eq_zero, zero_mul, neg_zero]

end TauCeti
