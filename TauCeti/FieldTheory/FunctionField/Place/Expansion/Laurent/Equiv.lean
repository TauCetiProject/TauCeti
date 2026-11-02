/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Equiv
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic

/-!
# Laurent expansions under semilinear field isomorphisms

Let `τ : F ≃+* F'` carry the constants `k` of `F` onto the constants `k'` of `F'` along
`σ : k ≃+* k'`, and let `P'` be the transport of a place `P` of `F` along `τ`
(`TauCeti.Place.equivOfRingEquiv`). If `t` is a uniformizer at a rational place `P`, then `τ t`
is a uniformizer at `P'`, and `τ` acts on Laurent expansions coefficientwise by `σ`:

`laurentCoeff_{P', τ t} n (τ z) = σ (laurentCoeff_{P, t} n z)`.

The proof reads both sides off a truncated expansion
(`TauCeti.Place.sub_sum_laurentCoeff_mem_filtration`), which `τ` carries to a truncated
expansion at `P'` since it preserves the order filtrations
(`TauCeti.Place.apply_mem_filtration_equivOfRingEquiv_iff`). No completion has to be transported.

## Main results

* `TauCeti.Place.laurentCoeff_equivOfRingEquiv`: `τ` acts on Laurent coefficients
  by `σ`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

public section

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F'] [Algebra k F]
  [Algebra k' F'] (σ : k ≃+* k') (τ : F ≃+* F')
  (h : ∀ c, τ (algebraMap k F c) = algebraMap k' F' (σ c))

/-- **Semilinear isomorphisms act on Laurent coefficients through the constants.** Let `τ`
carry the constants along `σ`, and the rational place `P` with uniformizer `t` to the place `Q`
with uniformizer `t' = τ t`. Then the Laurent coefficients of `τ z` at `Q` in `t'` are the images
under `σ` of those of `z` at `P` in `t`. -/
theorem laurentCoeff_equivOfRingEquiv {P : Place k F} (hP : P.degree = 1) {t : F}
    (ht : P.ord t = 1) {Q : Place k' F'} (hQ : equivOfRingEquiv σ τ h P = Q)
    (hQ₁ : Q.degree = 1) {t' : F'} (htt' : τ t = t') (ht' : Q.ord t' = 1) (n : ℤ) (z : F) :
    Q.laurentCoeff hQ₁ ht' n (τ z) = σ (P.laurentCoeff hP ht n z) := by
  subst hQ htt'
  -- Transport the expansion of `z` truncated after degree `n` along `τ`.
  have hz := P.sub_sum_laurentCoeff_mem_filtration hP ht (n + 1) z
  rw [← P.apply_mem_filtration_equivOfRingEquiv_iff σ τ h] at hz
  simp only [map_sub, map_sum, map_mul, map_zpow₀, h] at hz
  rw [laurentCoeff_apply, coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration _ hQ₁ ht' _
    (fun j ↦ σ (P.laurentCoeff hP ht j z)) hz (lt_add_one n)]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_Ico] at hn
    rw [P.laurentCoeff_eq_zero_of_lt_ord hP ht (by omega), map_zero]

end TauCeti.Place
