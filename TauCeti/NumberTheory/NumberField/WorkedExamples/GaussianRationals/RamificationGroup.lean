/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Ramification
public import TauCeti.RingTheory.Ideal.RamificationGroup
import TauCeti.RingTheory.Ideal.Inertia

/-!
# The dyadic ramification groups of `ℚ(i)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`, let `𝔭` be
the prime of `𝓞 K` above `2`, and let `G_i` be its ramification groups in `Gal(K/ℚ)`, the
elements acting trivially on `𝓞 K ⧸ 𝔭 ^ (i + 1)`. This file computes the whole filtration:

`G_0 = G_1 = Gal(K/ℚ) ≅ ℤ/2`, and `G_i = 1` for `i ≥ 2`.

Every automorphism sends `θ` to a square root of `−1`, so to `θ` or `−θ`
(`TauCeti.NumberField.smul_gen_eq_or_eq_neg`), and `𝓞 K = ℤ[θ]`, so
by Serre's criterion (`TauCeti.Ideal.mem_inertia_iff_of_adjoin_singleton_eq_top`) an
automorphism `σ` lies in `G_i` exactly when `σ θ − θ ∈ 𝔭 ^ (i + 1)`. For the conjugation
`σ θ − θ = −2θ` generates `(2) = 𝔭²`, which lies in `𝔭²` but not in `𝔭³`.

The two nontrivial groups `G_0` and `G_1` contribute `1` each to Hilbert's formula
`v_𝔭(𝔡) = Σ_{i ≥ 0} (#G_i − 1)`, which gives back the different exponent `v_𝔭(𝔡) = 2`
(`TauCeti.NumberField.GaussianRationals.multiplicity_differentIdeal_eq_two`). The jump of the
filtration is at `1`, not `0`: the prime is wildly ramified, so `G_1`, a `2`-group, is not
trivial.

## Main results

* `TauCeti.NumberField.GaussianRationals.mem_ramificationGroup_iff`: `σ ∈ G_i` exactly when
  `σ = 1` or `i ≤ 1`.
* `TauCeti.NumberField.GaussianRationals.ramificationGroup_eq_top` and
  `ramificationGroup_eq_bot`: `G_i = Gal(K/ℚ)` for `i ≤ 1`, and `G_i = 1` for `i ≥ 2`.
* `TauCeti.NumberField.GaussianRationals.card_ramificationGroup_of_le_one`: `#G_0 = #G_1 = 2`.
* `TauCeti.NumberField.GaussianRationals.finsum_card_ramificationGroup_sub_one`: the sum
  `Σ_{i ≥ 0} (#G_i − 1)` of Hilbert's formula equals `2`, the known different exponent.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1.
-/

public section

open Polynomial NumberField Ideal
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
  (hmin : minpoly ℤ θ = X ^ 2 + 1) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
  (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [𝔭.LiesOver (span {(2 : ℤ)})]

include hmin hgen

/-- `2` lies in `𝔭 ^ n` exactly when `n ≤ 2`, since `(2) = 𝔭²`. -/
private theorem two_mem_pow_iff {n : ℕ} : (2 : 𝓞 K) ∈ 𝔭 ^ n ↔ n ≤ 2 := by
  have hsq : 𝔭 ^ 2 = span {2} := by
    rw [← map_span_two_eq_sq hmin hgen 𝔭, map_span, Set.image_singleton, map_ofNat]
  have h2 : (2 : 𝓞 K) ∈ 𝔭 ^ 2 := hsq ▸ mem_span_singleton_self 2
  have htwo : span {(2 : ℤ)} ≠ ⊥ := span_singleton_eq_bot.not.mpr two_ne_zero
  have h𝔭 : 𝔭 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot htwo 𝔭
  refine ⟨fun h ↦ ?_, fun h ↦ pow_le_pow_right h h2⟩
  by_contra hn
  have hle : 𝔭 ^ 2 ≤ 𝔭 ^ 3 := by
    rw [hsq, span_singleton_le_iff_mem]
    exact pow_le_pow_right (by omega) h
  exact (pow_succ_lt_pow h𝔭 2).not_ge hle

/-- **The dyadic ramification filtration of `ℚ(i)`.** An automorphism `σ` lies in the `i`-th
ramification group of the prime above `2` exactly when `σ = 1` or `i ≤ 1`. -/
theorem mem_ramificationGroup_iff {i : ℕ} {σ : K ≃ₐ[ℚ] K} :
    σ ∈ 𝔭.ramificationGroup (K ≃ₐ[ℚ] K) i ↔ σ = 1 ∨ i ≤ 1 := by
  rw [ramificationGroup_def,
    TauCeti.Ideal.mem_inertia_iff_of_adjoin_singleton_eq_top (R := ℤ) (adjoin_eq_top hmin hgen)]
  rcases smul_gen_eq_or_eq_neg (minpoly_eq_X_sq_sub_C hmin) σ with h | h
  · -- `σ` fixes the generator `θ` of `K`, so it is the identity
    have hθ : σ (θ : K) = θ := congrArg ((↑) : 𝓞 K → K) h
    have hσ : σ = 1 := AlgEquiv.ext <| AlgHom.congr_fun <|
      AlgHom.ext_of_adjoin_eq_top (φ₁ := σ.toAlgHom) (φ₂ := AlgHom.id ℚ K) hgen fun x hx ↦ by
        rw [Set.mem_singleton_iff.1 hx]
        exact hθ
    rw [h, sub_self]
    simp only [zero_mem, hσ, true_or]
  · -- `σ θ - θ = -2θ`, and `θ` is a unit, so this is a question about `2`
    have hσ : σ ≠ 1 := by
      rintro rfl
      have h2 : (2 : 𝓞 K) * θ = 0 := by linear_combination h - one_smul (K ≃ₐ[ℚ] K) θ
      exact (isUnit hmin).ne_zero ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
    have hsub : -θ - θ = (-θ) * 2 := by ring
    rw [h, hsub, unit_mul_mem_iff_mem _ (isUnit hmin).neg,
      two_mem_pow_iff hmin hgen 𝔭]
    simp only [hσ, false_or]
    omega

/-- **The ramification groups `G_0` and `G_1` of the prime above `2` are the whole Galois group
of `ℚ(i)`.** -/
theorem ramificationGroup_eq_top {i : ℕ} (hi : i ≤ 1) :
    𝔭.ramificationGroup (K ≃ₐ[ℚ] K) i = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ (mem_ramificationGroup_iff hmin hgen 𝔭).2 (.inr hi)

/-- **The ramification groups `G_i` of the prime above `2` in `ℚ(i)` are trivial for
`i ≥ 2`.** -/
theorem ramificationGroup_eq_bot {i : ℕ} (hi : 2 ≤ i) :
    𝔭.ramificationGroup (K ≃ₐ[ℚ] K) i = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hσ ↦
    ((mem_ramificationGroup_iff hmin hgen 𝔭).1 hσ).resolve_right (by omega)

/-- **`G_0 = G_1 ≅ ℤ/2`**: the ramification groups `G_0` and `G_1` of the prime above `2` in
`ℚ(i)` have order `2`. -/
theorem card_ramificationGroup_of_le_one {i : ℕ} (hi : i ≤ 1) :
    Nat.card (𝔭.ramificationGroup (K ≃ₐ[ℚ] K) i) = 2 := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_eq_two hmin hgen⟩
  rw [ramificationGroup_eq_top hmin hgen 𝔭 hi, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
    finrank_eq_two hmin hgen]

/-- **Hilbert's different formula, checked in `ℚ(i)`**: the sum `Σ_{i ≥ 0} (#G_i − 1)` over the
ramification groups of the prime above `2` is the different exponent `v_𝔭(𝔡) = 2`, as the
general `multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` predicts. -/
theorem finsum_card_ramificationGroup_sub_one :
    ∑ᶠ i : ℕ, (Nat.card (𝔭.ramificationGroup (K ≃ₐ[ℚ] K) i) - 1) = 2 := by
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2) _ fun i hi ↦ ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_one,
      card_ramificationGroup_of_le_one hmin hgen 𝔭 zero_le_one,
      card_ramificationGroup_of_le_one hmin hgen 𝔭 le_rfl]
  · by_contra hi2
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hi2
    rw [Function.mem_support, ramificationGroup_eq_bot hmin hgen 𝔭 hi2, Subgroup.card_bot] at hi
    exact hi rfl

end TauCeti.NumberField.GaussianRationals
