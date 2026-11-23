/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Action

/-!
# Inversion quotient conjugation action for index-two normal subgroups

When `N` is an abelian normal subgroup of `G` with `G ⧸ N` identified with
`C₂ = Multiplicative (ZMod 2)` via `eG` and elements outside `N` act on `N` by inversion, the
quotient conjugation action `Subgroup.quotientConjugationAction` agrees with
`TauCeti.invMulDistribMulAction`
(`Subgroup.invMulDistribMulAction_smul_eq_quotientConjugationAction`), and transports along any
kernel equivalence `eN : M ≃* N` (`Subgroup.quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo`).
-/

public section

namespace Subgroup

open scoped IsMulCommutative

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

attribute [local instance] quotientConjugationAction TauCeti.invMulDistribMulAction

/-- If `G ⧸ N` is identified with `Multiplicative (ZMod 2)` and elements outside `N` conjugate
`N` by inversion, then the quotient conjugation action on `N` equals
`TauCeti.invMulDistribMulAction` pulled back along `eG`. -/
theorem invMulDistribMulAction_smul_eq_quotientConjugationAction
    (eG : G ⧸ N ≃* Multiplicative (ZMod 2))
    (hinv : ∀ g ∉ N, ∀ x : N, MulAut.conjNormal g x = x⁻¹)
    (q : G ⧸ N) (x : N) :
    eG q • x = q • x := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  by_cases hg : g ∈ N
  · have h1 : (g : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hg
    rw [h1, map_one, one_smul, one_smul]
  · have hne : eG (g : G ⧸ N) ≠ 1 := fun h ↦
      hg ((QuotientGroup.eq_one_iff _).1 (eG.injective (h.trans (map_one eG).symm)))
    rw [TauCeti.invMulDistribMulAction_smul, ite_eq_right_iff.mpr (fun h ↦ absurd h hne),
      quotientConjugationAction_mk_smul, hinv g hg x]

/-- Identifying `N` with `M` via `eN` and `G ⧸ N` with `C₂` via `eG` intertwines
`TauCeti.invMulDistribMulAction` on `M` with the quotient conjugation action on `N` whenever
elements outside `N` conjugate `N` by inversion. -/
theorem quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo {M : Type*} [CommGroup M]
    (eN : M ≃* N) (eG : G ⧸ N ≃* Multiplicative (ZMod 2))
    (hinv : ∀ g ∉ N, ∀ x : N, MulAut.conjNormal g x = x⁻¹)
    (q : G ⧸ N) (m : M) :
    eN (eG q • m) = q • eN m :=
  (eN.toMonoidHom.map_invMulDistribMulAction_smul (eG q) m).trans
    (N.invMulDistribMulAction_smul_eq_quotientConjugationAction eG hinv q (eN m))

end Subgroup
