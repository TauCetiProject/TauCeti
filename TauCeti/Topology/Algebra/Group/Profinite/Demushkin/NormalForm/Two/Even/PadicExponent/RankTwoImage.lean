/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.PadicExponent.Character
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Orientation images of rank-two dyadic presentations

For the presentation `⟨x₁, x₂ ∣ x₁^{2+α}(x₁,x₂)⟩`, with `α ∈ 4ℤ₂`, a character with the
prescription property has image generated topologically by its value `-(1+α)⁻¹` on `x₂`.
This file identifies that image with the twisted subgroup `U^[g]` exactly when `α` has
valuation `g ≥ 2`, and with `{±1}` exactly when `α = 0`. These characterizations recover
the exact divisibility depth of the parameter of a marked rank-two presentation from its
orientation image, with a separate zero endpoint.

The statements use the prescription property directly, so they also apply before choosing
a proof that the presentation is Demushkin. The character exists by
`TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_demushkinWordTwoEvenPadic`.
The unused third-generator exponent `q` is arbitrary at rank two.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967),
  Theorem 4 and its corollary.
-/

public section

namespace TauCeti

open Subgroup

variable {α : ℤ_[2]} {q : ℕ}
  {χ : presentedProP 2 (Fin 2)
    {demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin 2)) α q 2 (freeProPGen 2 2)} →ₜ* ℤ_[2]ˣ}

/-- The orientation image of the rank-two dyadic presentation is `U^[g]` exactly when
the `2`-adic exponent `α` has exact divisibility depth `g ≥ 2`. -/
theorem
    range_eq_topologicalClosure_zpowers_iff_dvd_and_not_dvd_demushkinWordTwoEvenPadic_two
    (hα : 4 ∣ α) {g : ℕ} (hg : 2 ≤ g) {w : ℤ_[2]ˣ}
    (hw : (w : ℤ_[2]) = -1 + (2 : ℤ_[2]) ^ g) (hχ : HasPrescriptionProperty χ) :
    χ.toMonoidHom.range = (zpowers w).topologicalClosure ↔
      (2 : ℤ_[2]) ^ g ∣ α ∧ ¬ (2 : ℤ_[2]) ^ (g + 1) ∣ α := by
  have hα₂ : 2 ∣ α := (Dvd.intro 2 (by norm_num)).trans hα
  obtain ⟨hv, -, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEvenPadic_iff α q χ hα₂
      (by omega) even_two one_lt_two).1 hχ
  have hr :=
    range_eq_topologicalClosure_zpowers_of_hasPrescriptionProperty_demushkinWordTwoEvenPadic_two
      hα₂ hχ
  refine ⟨fun h ↦ ?_, fun ⟨hdiv, hnot⟩ ↦ ?_⟩
  · have hmem : χ (presentedProPGen 2 2 _ 1) ∈ (zpowers w).topologicalClosure := by
      rw [← h]
      exact ⟨_, rfl⟩
    have hneg : -χ (presentedProPGen 2 2 _ 1) ∈ unitsPrincipal 2 2 :=
      (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one hv).2 (by norm_num; exact hα)
    obtain ⟨hdiv, hnot⟩ :=
      neg_mem_unitsPrincipal_and_notMem_succ_of_mem_topologicalClosure_zpowers_two hg
        (neg_mem_unitsPrincipal_two_of_val_eq hw)
        (neg_notMem_unitsPrincipal_two_succ_of_val_eq hw) hmem
        (notMem_unitsPrincipal_two_of_neg_mem le_rfl hneg)
    exact ⟨(neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one hv).1 hdiv,
      fun h ↦ hnot ((neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one hv).2 h)⟩
  · rw [hr]
    exact topologicalClosure_zpowers_eq_of_val_mul_one_add_eq_neg_one hg hdiv hnot hv hw

/-- The orientation image of the rank-two dyadic presentation is the endpoint `{±1}`
exactly when its `2`-adic exponent `α` is zero. -/
theorem
    range_eq_zpowers_neg_one_iff_eq_zero_demushkinWordTwoEvenPadic_two
    (hα : 4 ∣ α) (hχ : HasPrescriptionProperty χ) :
    χ.toMonoidHom.range = zpowers (-1) ↔ α = 0 := by
  have hα₂ : 2 ∣ α := (Dvd.intro 2 (by norm_num)).trans hα
  obtain ⟨hv, -, -⟩ :=
    (hasPrescriptionProperty_presentedProP_demushkinWordTwoEvenPadic_iff α q χ hα₂
      (by omega) even_two one_lt_two).1 hχ
  refine ⟨fun h ↦ ?_, fun h ↦
    range_eq_zpowers_neg_one_of_hasPrescriptionProperty_demushkinWordTwoEvenPadic h
      (by omega) even_two one_lt_two hχ⟩
  have hmem : χ (presentedProPGen 2 2 _ 1) ∈ zpowers (-1) := by
    rw [← h]
    exact ⟨_, rfl⟩
  have hneg : -χ (presentedProPGen 2 2 _ 1) ∈ unitsPrincipal 2 2 :=
    (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one hv).2 (by norm_num; exact hα)
  rcases (Subgroup.mem_zpowers_neg_one_iff PadicInt.units_neg_one_ne_one).1 hmem with hOne | hNeg
  · exact False.elim (notMem_unitsPrincipal_two_of_neg_mem le_rfl hneg
      (hOne ▸ one_mem _))
  · rw [hNeg, Units.val_neg, Units.val_one] at hv
    linear_combination -hv

end TauCeti
