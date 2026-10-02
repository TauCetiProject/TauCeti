/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Automorphism.Finite
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.BranchPlaces

/-!
# Finiteness of the automorphism group of a hyperelliptic function field

Let `k` be an algebraically closed field of characteristic other than two and `F / k` a function
field of genus `g ≥ 2` with a rational subfield `k(x)` of index two. Every `k`-automorphism of `F`
preserves `k(x)` and permutes the `2g + 2 ≥ 6` branch places of `k(x)`; an automorphism whose
restriction to `k(x)` fixes all of them fixes `k(x)` pointwise, by rigidity in genus zero, so it
is the identity or the hyperelliptic involution. Hence `Aut(F / k)` is finite, of order at most
`2 · (2g + 2)!`. This is the hyperelliptic case of the finiteness of the automorphism group of a
function field of genus at least two.

## Main results

* `TauCeti.branchPermHom`: the action of `Aut(F / k)` on the branch places of `k(x)`, evaluated by
  `TauCeti.branchPermHom_apply` and `TauCeti.branchPermHom_symm_apply`.
* `TauCeti.ker_branchPermHom`: its kernel is the group of automorphisms over `k(x)`.
* `TauCeti.finite_algEquiv_of_finrank_adjoin_eq_two`: **`Aut(F / k)` is finite**, and
  `TauCeti.card_algEquiv_le_of_finrank_adjoin_eq_two`: of order at most `2 · (2g + 2)!`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 3.17 and Proposition 6.2.4.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F)
  [NeZero (2 : k)] {x : F} (hx : Transcendental k x) (hdeg : Module.finrank k⟮x⟯ F = 2)
  [FiniteDimensional k⟮x⟯ F] [Algebra.IsSeparable k⟮x⟯ F]

/-- **The action of `Aut(F / k)` on the branch places of `k(x)`**, through the restriction of
automorphisms to `k(x)`. -/
noncomputable def branchPermHom : (F ≃ₐ[k] F) →* Equiv.Perm (branchPlaces hx) :=
  placePermHomOfInvariant (restrictAdjoinHom hF hex hg hx hdeg)
    fun σ _ hP ↦ smul_mem_branchPlaces hF hex hx hdeg hg σ hP

/-- The action of an automorphism on a branch place is the action of its restriction to `k(x)`. -/
@[simp]
theorem branchPermHom_apply (σ : F ≃ₐ[k] F) (P : branchPlaces hx) :
    ((branchPermHom hF hex hg hx hdeg σ) P : Place k k⟮x⟯) =
      restrictAdjoinHom hF hex hg hx hdeg σ • (P : Place k k⟮x⟯) :=
  placePermHomOfInvariant_apply _ _ σ P

/-- The inverse action of an automorphism on a branch place. -/
@[simp]
theorem branchPermHom_symm_apply (σ : F ≃ₐ[k] F) (P : branchPlaces hx) :
    (((branchPermHom hF hex hg hx hdeg σ).symm) P : Place k k⟮x⟯) =
      (restrictAdjoinHom hF hex hg hx hdeg σ)⁻¹ • (P : Place k k⟮x⟯) :=
  placePermHomOfInvariant_symm_apply _ _ σ P

/-- **The kernel of the action on the branch places is the group of automorphisms over `k(x)`**,
when `k` is algebraically closed: an automorphism acting trivially on the branch places restricts
to an automorphism of the genus-zero field `k(x)` fixing `2g + 2 ≥ 3` of its rational places, so it
fixes `k(x)` pointwise by rigidity; conversely an automorphism fixing `k(x)` pointwise restricts to
the identity. -/
theorem ker_branchPermHom [IsAlgClosed k] :
    (branchPermHom hF hex hg hx hdeg).ker = k⟮x⟯.fixingSubgroup := by
  rw [← ker_restrictAdjoinHom hF hex hg hx hdeg]
  refine le_antisymm ?_ (fun σ hσ ↦ ?_)
  · refine ker_placePermHomOfInvariant_le _ hx.isFunctionField_adjoin
      (isIntegrallyClosedIn_intermediateField hex k⟮x⟯) (branchPlaces hx) _
      (fun P hP ↦ P.degree_eq_one_of_isAlgClosed_of_isFunctionField hx.isFunctionField_adjoin) ?_
    rw [genus_adjoin_simple_eq_zero hx, card_branchPlaces hF hex hx hdeg]
    omega
  · rw [MonoidHom.mem_ker] at hσ ⊢
    refine Equiv.ext fun P ↦ Subtype.ext ?_
    rw [branchPermHom_apply, hσ, one_smul]
    rfl

include hF hex hg hx hdeg in
/-- **The automorphism group of a hyperelliptic function field is finite** over an algebraically
closed field of characteristic other than two: the action on the branch places has finite image,
and its kernel is the group of automorphisms over `k(x)`, of order two. -/
theorem finite_algEquiv_of_finrank_adjoin_eq_two [IsAlgClosed k] : Finite (F ≃ₐ[k] F) := by
  set φ := branchPermHom hF hex hg hx hdeg with hφ
  have hfix : Finite k⟮x⟯.fixingSubgroup :=
    Nat.finite_of_card_ne_zero (by
      rw [IntermediateField.natCard_fixingSubgroup_of_finrank_eq_two k⟮x⟯ hdeg]
      exact two_ne_zero)
  have hker : Finite φ.ker := by
    rw [hφ, ker_branchPermHom hF hex hg hx hdeg]
    exact hfix
  have hquot : Finite ((F ≃ₐ[k] F) ⧸ φ.ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := φ.ker)).symm

include hF hex hg hx hdeg in
/-- **The order of the automorphism group is at most `2 · (2g + 2)!`**: the quotient by the
hyperelliptic involution embeds in the symmetric group of the `2g + 2` branch places. -/
theorem card_algEquiv_le_of_finrank_adjoin_eq_two [IsAlgClosed k] :
    Nat.card (F ≃ₐ[k] F) ≤ 2 * (2 * genus k F + 2).factorial := by
  have hfin := finite_algEquiv_of_finrank_adjoin_eq_two hF hex hg hx hdeg
  set φ := branchPermHom hF hex hg hx hdeg with hφ
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hquot : Nat.card ((F ≃ₐ[k] F) ⧸ φ.ker) ≤ (2 * genus k F + 2).factorial := by
    classical
    refine (Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective φ)).trans ?_
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (branchPlaces hx)), Fintype.card_perm,
      Fintype.card_coe, card_branchPlaces hF hex hx hdeg]
  have hsub : Nat.card φ.ker = 2 := by
    rw [hφ, ker_branchPermHom hF hex hg hx hdeg,
      IntermediateField.natCard_fixingSubgroup_of_finrank_eq_two k⟮x⟯ hdeg]
  rw [hcard, hsub, mul_comm]
  exact Nat.mul_le_mul_left 2 hquot

end TauCeti
