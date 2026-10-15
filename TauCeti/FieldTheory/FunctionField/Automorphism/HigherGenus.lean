/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Automorphism.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Differential.Weierstrass.Count
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Finite

/-!
# Finiteness of the automorphism group in genus at least two

Let `k` be an algebraically closed field and `F / k` a function field of genus `g ≥ 2` with exact
constants, such that the Weierstrass gaps at every place are pairwise distinct in `k`; in
characteristic zero the last condition always holds, as `fun _ ↦ Nat.cast_injective.injOn`. Then
the automorphism group `Aut(F / k)` is finite. The proof splits into two cases.

* If `F` is not hyperelliptic, it has at least `2g + 3` Weierstrass points
  (`TauCeti.two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero`). Automorphisms
  preserve Weierstrass weights, so they permute this finite set of rational places, and an
  automorphism fixing all of them is the identity by rigidity. Hence `Aut(F / k)` embeds in the
  symmetric group of the Weierstrass points, of order at most `(g³ - g)!`.
* If `F` is hyperelliptic, `Aut(F / k)` is finite by
  `TauCeti.finite_algEquiv_of_finrank_adjoin_eq_two`, through its action on the branch places of
  the index-two rational subfield. That argument needs `2 ≠ 0` in `k`, which the gap hypothesis
  supplies: the gaps at a Weierstrass point of a hyperelliptic field are `1, 3, …, 2g - 1`, and
  `1` and `3` are distinct in `k`.

The genus hypothesis cannot be dropped: `Aut(k(x) / k) ≅ PGL₂(k)` is infinite
(`RatFunc.pglEquivAlgEquiv`), and so is the automorphism group of an elliptic function field over
an algebraically closed field.

## Main results

* `TauCeti.finite_algEquiv_of_not_isHyperellipticFunctionField` and
  `TauCeti.card_algEquiv_le_factorial_of_not_isHyperellipticFunctionField`: the automorphism group
  of a non-hyperelliptic function field of genus `g ≥ 2` is finite, of order at most `(g³ - g)!`.
* `TauCeti.finite_algEquiv_of_two_le_genus`: **the automorphism group of a function field of genus
  at least two is finite.**

## References

* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9.
* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Section V.1, for
  the Weierstrass-point proof of finiteness.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]

/-- **The automorphism group of a non-hyperelliptic function field of genus `g ≥ 2` is finite**,
over an algebraically closed field, if the gaps at every place are pairwise distinct in `k`: it
permutes the at least `2g + 3` Weierstrass points, and an automorphism fixing them all is the
identity. -/
theorem finite_algEquiv_of_not_isHyperellipticFunctionField (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) (hhyp : ¬ IsHyperellipticFunctionField k F) :
    Finite (F ≃ₐ[k] F) := by
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  refine finite_algEquiv_of_invariant_rational_places hF hex hfin.toFinset
    (fun σ P hP ↦ by simpa using hP)
    (fun P _ ↦ P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) ?_
  rw [← Set.ncard_eq_toFinset_card _ hfin]
  exact two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero hF hex hgaps hg hhyp

/-- **The automorphism group of a non-hyperelliptic function field of genus `g ≥ 2` has order at
most `(g³ - g)!`**, over an algebraically closed field, if the gaps at every place are pairwise
distinct in `k`: it embeds in the symmetric group of the at most `g³ - g` Weierstrass points. -/
theorem card_algEquiv_le_factorial_of_not_isHyperellipticFunctionField (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) (hhyp : ¬ IsHyperellipticFunctionField k F) :
    Nat.card (F ≃ₐ[k] F) ≤ (genus k F ^ 3 - genus k F).factorial := by
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  have hcard := two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero hF hex hgaps hg
    hhyp
  have hle := ncard_setOf_weierstrassWeight_ne_zero_le_genus_pow_three_sub_genus hF hex hgaps
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard hle
  exact (card_algEquiv_le_factorial_of_invariant_rational_places hF hex hfin.toFinset
    (fun σ P hP ↦ by simpa using hP)
    (fun P _ ↦ P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hcard).trans
    (Nat.factorial_le hle)

/-- If the gaps at every place are pairwise distinct in `k`, a hyperelliptic function field
forces `2 ≠ 0` in `k`: its Weierstrass points have gaps `1, 3, …, 2g - 1`. -/
private theorem two_ne_zero_of_isHyperellipticFunctionField (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hhyp : IsHyperellipticFunctionField k F) : (2 : k) ≠ 0 := by
  have hg := hhyp.two_le_genus
  have hcard :=
    (isHyperellipticFunctionField_iff_ncard_setOf_weierstrassWeight_ne_zero_eq hF hex hgaps
      hg).mp hhyp
  obtain ⟨P, hP⟩ := Set.nonempty_of_ncard_ne_zero
    (s := {P : Place k F | P.weierstrassWeight ≠ 0}) (by omega)
  have hP₁ := P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF
  have hgapsP := P.weierstrassGaps_eq_image_range_of_isPoleNumber_two hF hex hP₁
    ((P.weierstrassWeight_eq_genus_choose_two_iff hF hex hP₁).mp
      (weierstrassWeight_eq_genus_choose_two_of_isHyperellipticFunctionField hF hex hhyp hP₁ hP))
  -- `1` and `3` are gaps at `P`, so their images in `k` differ.
  have h1 : 1 ∈ P.weierstrassGaps := hgapsP ▸ Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have h3 : 3 ∈ P.weierstrassGaps := hgapsP ▸ Finset.mem_image.mpr
    ⟨1, Finset.mem_range.mpr (by omega), rfl⟩
  intro h2
  have hcast : ((3 : ℕ) : k) = ((1 : ℕ) : k) + 2 := by push_cast; ring
  have h13 : ((1 : ℕ) : k) = ((3 : ℕ) : k) := by rw [hcast, h2, add_zero]
  exact absurd (hgaps P (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h3) h13) (by norm_num)

/-- **The automorphism group of a function field of genus at least two is finite**, over an
algebraically closed field, if the gaps at every place are pairwise distinct in `k`. In
characteristic zero the gap hypothesis is `fun _ ↦ Nat.cast_injective.injOn`. A non-hyperelliptic
field is handled by `TauCeti.finite_algEquiv_of_not_isHyperellipticFunctionField`, a hyperelliptic
one by `TauCeti.finite_algEquiv_of_finrank_adjoin_eq_two`. -/
theorem finite_algEquiv_of_two_le_genus (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) : Finite (F ≃ₐ[k] F) := by
  by_cases hhyp : IsHyperellipticFunctionField k F
  · have : NeZero (2 : k) := ⟨two_ne_zero_of_isHyperellipticFunctionField hF hex hgaps hhyp⟩
    obtain ⟨x, hx, hdeg, hsep⟩ := hhyp.exists_separable_finrank_adjoin_eq_two
    have : FiniteDimensional k⟮x⟯ F := Module.finite_of_finrank_pos (by omega)
    exact finite_algEquiv_of_finrank_adjoin_eq_two hF hex hg hx hdeg
  · exact finite_algEquiv_of_not_isHyperellipticFunctionField hF hex hgaps hg hhyp

end TauCeti
