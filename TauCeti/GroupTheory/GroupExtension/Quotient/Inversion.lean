/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.GroupTheory.GroupExtension.Quotient.Action
public import TauCeti.RepresentationTheory.Cyclic.Automorphism
import TauCeti.Data.ZMod.Two
import TauCeti.GroupTheory.Index.Two

/-!
# Quotient modules of index two acting by inversion

Let `N` be an abelian normal subgroup of index two in `G`, and suppose that some element `s` of
`G` outside `N` inverts `N` by conjugation, as a reflection of a dihedral group and an element
`xa i` of a generalized quaternion group invert their cyclic subgroup of rotations. Then every
element outside `N` inverts `N` (`TauCeti.conj_eq_inv_of_notMem_of_index_two`), so `G ⧸ N` has
order two and acts on `N` through the conjugation module `Subgroup.quotientConjugationAction`
with its identity acting trivially and its other element acting by `x ↦ x⁻¹`
(`Subgroup.quotientConjugationAction_smul_eq_inv`).

Read through the unique isomorphism `G ⧸ N ≃* C₂`, with `C₂ = Multiplicative (ZMod 2)`, and an
identification `φ : N ≃* Multiplicative T`, the conjugation module is therefore the cyclic
representation of `C₂` on `T` in which the generator acts by negation
(`Subgroup.toAdditiveLeft_smul_eq_cyclicRepresentation_neg`), and
`Subgroup.quotientGroupCohomologyIsoNeg` identifies the cohomology of `G ⧸ N` with coefficients in
`N` with that of `C₂` with coefficients in `T`. In this form the classes of the quotient
extensions of different groups, with isomorphic kernels and the same action, lie in one cohomology
group and can be compared. The cohomology of the action by negation is computed in
`TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicAutomorphism`: in positive even
degree it is the `2`-torsion of `T` (`TauCeti.groupCohomologyEvenNegEquivTorsionBy`).

## Main definitions

* `Subgroup.quotientGroupCohomologyIsoNeg`: the identification of `Hⁿ(G ⧸ N, N)` with
  `Hⁿ(C₂, T)` for the action by negation, the isomorphism `groupCohomology.mapIso` induced by
  `G ⧸ N ≃* C₂` and `φ`.

## Main results

* `Subgroup.quotientConjugationAction_smul_eq_inv`: the non-trivial coset acts by inversion.
* `Subgroup.toAdditiveLeft_smul_eq_cyclicRepresentation_neg`: read through any `G ⧸ N ≃* C₂` and
  `φ`, the conjugation module is the action of `C₂` on `T` by negation.
-/

public section

open CategoryTheory

namespace Subgroup

open scoped IsMulCommutative

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] [IsMulCommutative N]

attribute [local instance] quotientConjugationAction

/-- If `N` has index two and some `s ∉ N` inverts `N` by conjugation, then the coset of `N`
other than `N` itself acts on `N` by inversion. -/
theorem quotientConjugationAction_smul_eq_inv (hN : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) {y : G ⧸ N} (hy : y ≠ 1) (x : N) :
    y • x = x⁻¹ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∉ N := fun hg ↦ hy ((QuotientGroup.eq_one_iff g).2 hg)
    rw [quotientConjugationAction_mk_smul]
    exact Subtype.ext <| (MulAut.conjNormal_apply g x).trans <|
      (TauCeti.conj_eq_inv_of_notMem_of_index_two hN hs hinv hg x.property).trans
        (InvMemClass.coe_inv x).symm

variable {T : Type} [AddCommGroup T]

/-- The conjugation module of `G ⧸ N` on `N`, read through any `e : G ⧸ N ≃* C₂` and
`φ : N ≃* Multiplicative T`, is the action of `C₂` on `T` by negation, when `N` has index two and
some `s ∉ N` inverts `N`. -/
theorem toAdditiveLeft_smul_eq_cyclicRepresentation_neg (hN : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) (e : G ⧸ N ≃* Multiplicative (ZMod 2))
    (φ : N ≃* Multiplicative T) (y : G ⧸ N) (x : N) :
    MulEquiv.toAdditiveLeft φ (Additive.ofMul (y • x)) =
      (AddEquiv.neg T).cyclicRepresentation (AddEquiv.iterate_neg_two T) (e y)
        (MulEquiv.toAdditiveLeft φ (Additive.ofMul x)) := by
  by_cases hy : y = 1
  · simp [hy]
  · -- The coset `y` is not trivial, so `e y` is the generator of `C₂`.
    rw [(Multiplicative.eq_one_or_eq_ofAdd_one (e y)).resolve_left
        ((map_ne_one_iff e e.injective).2 hy), AddEquiv.cyclicRepresentation_ofAdd_one_apply,
      quotientConjugationAction_smul_eq_inv hN hs hinv hy]
    simp

/-- **The quotient module of an index-two subgroup acting by inversion.** Let `N` be abelian and
normal of index two in `G`, and let some `s ∉ N` invert `N` by conjugation. Then
`φ : N ≃* Multiplicative T` identifies the cohomology of `G ⧸ N` with coefficients in `N` with the
cohomology of `C₂` with coefficients in `T`, the generator of `C₂` acting by negation, in every
degree `n`. The two groups of order two `G ⧸ N` and `C₂` are identified by their unique
isomorphism. -/
noncomputable def quotientGroupCohomologyIsoNeg (hN : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) (φ : N ≃* Multiplicative T) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (G ⧸ N) N) n ≅
      groupCohomology ((AddEquiv.neg T).cyclicRep (AddEquiv.iterate_neg_two T)) n :=
  let e : G ⧸ N ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) (by rw [← index_eq_card, hN]) (by simp)
  groupCohomology.mapIso e (MulEquiv.toAdditiveLeft φ).toIntLinearEquiv
    (fun y ↦ LinearMap.ext fun (x : Additive N) ↦
      toAdditiveLeft_smul_eq_cyclicRepresentation_neg hN hs hinv e φ y x.toMul) n

end Subgroup
