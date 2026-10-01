/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.BranchPlaces
-- Proof-only: rigidity of automorphisms, and the order of the fixing subgroup of `k(x)`.
import TauCeti.FieldTheory.FunctionField.Automorphism.Rigidity

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

* `TauCeti.branchPermHom`: the action of `Aut(F / k)` on the branch places of `k(x)`.
* `TauCeti.ker_branchPermHom_le_fixingSubgroup`: an automorphism acting trivially on the branch
  places fixes `k(x)` pointwise.
* `TauCeti.finite_algEquiv_of_finrank_adjoin_eq_two`: **`Aut(F / k)` is finite.**

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
noncomputable def branchPermHom : (F ≃ₐ[k] F) →* Equiv.Perm (branchPlaces hx) where
  toFun σ :=
    { toFun P := ⟨restrictAdjoinHom hF hex hg hx hdeg σ • P,
        smul_mem_branchPlaces hF hex hx hdeg hg σ P.2⟩
      invFun P := ⟨restrictAdjoinHom hF hex hg hx hdeg σ⁻¹ • P,
        smul_mem_branchPlaces hF hex hx hdeg hg σ⁻¹ P.2⟩
      left_inv P := Subtype.ext (by simp [map_inv, inv_smul_smul])
      right_inv P := Subtype.ext (by simp [map_inv, smul_inv_smul]) }
  map_one' := Equiv.ext fun P ↦ Subtype.ext (by simp)
  map_mul' σ τ := Equiv.ext fun P ↦ Subtype.ext (by simp [mul_smul])

@[simp]
theorem coe_branchPermHom_apply (σ : F ≃ₐ[k] F) (P : branchPlaces hx) :
    ((branchPermHom hF hex hg hx hdeg σ P : Place k k⟮x⟯)) =
      restrictAdjoinHom hF hex hg hx hdeg σ • (P : Place k k⟮x⟯) := by rfl

/-- **An automorphism acting trivially on the branch places fixes `k(x)` pointwise**, when `k` is
algebraically closed: its restriction fixes `2g + 2 ≥ 3` rational places of the genus-zero field
`k(x)`, so it is the identity by rigidity. -/
theorem ker_branchPermHom_le_fixingSubgroup [IsAlgClosed k] :
    (branchPermHom hF hex hg hx hdeg).ker ≤ k⟮x⟯.fixingSubgroup := by
  intro σ hσ
  rw [← ker_restrictAdjoinHom hF hex hg hx hdeg, MonoidHom.mem_ker]
  refine eq_one_of_two_mul_genus_add_three_le_card hx.isFunctionField_adjoin
    (isIntegrallyClosedIn_intermediateField hex k⟮x⟯) (S := branchPlaces hx) (fun P hP ↦ ⟨?_, ?_⟩)
    ?_
  · have : FiniteDimensional k P.ResidueField :=
      Place.finiteDimensional_residueField P hx.isFunctionField_adjoin
    exact Place.degree_eq_one_of_isAlgClosed_of_isIntegral P
  · have h := congrArg (fun e : Equiv.Perm (branchPlaces hx) ↦ (e ⟨P, hP⟩ : Place k k⟮x⟯))
      (MonoidHom.mem_ker.mp hσ)
    simpa using h
  · rw [genus_adjoin_simple_eq_zero hx, card_branchPlaces hF hex hx hdeg]
    omega

include hF hex hg hx hdeg in
/-- **The automorphism group of a hyperelliptic function field is finite** over an algebraically
closed field of characteristic other than two: the action on the branch places has finite image,
and its kernel lies in the fixing subgroup of `k(x)`, of order two. -/
theorem finite_algEquiv_of_finrank_adjoin_eq_two [IsAlgClosed k] : Finite (F ≃ₐ[k] F) := by
  set φ := branchPermHom hF hex hg hx hdeg with hφ
  have hfix : Finite k⟮x⟯.fixingSubgroup :=
    Nat.finite_of_card_ne_zero (by
      rw [IntermediateField.natCard_fixingSubgroup_of_finrank_eq_two k⟮x⟯ hdeg]
      exact two_ne_zero)
  have hker : Finite φ.ker :=
    Finite.of_injective _
      (Subgroup.inclusion_injective (ker_branchPermHom_le_fixingSubgroup hF hex hg hx hdeg))
  have hquot : Finite ((F ≃ₐ[k] F) ⧸ φ.ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := φ.ker)).symm

end TauCeti
