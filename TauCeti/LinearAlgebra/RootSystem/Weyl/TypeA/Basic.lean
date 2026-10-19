/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic

/-!
# Weyl groups of type A

The roots of the pinned datum of type `Aₙ` are indexed by the ordered pairs `(a, b)` of distinct
elements of `Fin (n + 1)`. A permutation of these `n + 1` coordinates therefore acts diagonally
on the root indices. The explicit reflection formula for the pinned datum says that every root
reflection is the diagonal action of a transposition. Conversely, transpositions generate the
symmetric group. Faithfulness of the action on roots then identifies the Weyl group with the full
symmetric group.

The comparison only uses the reflection permutations and the faithfulness of the action on root
indices, so it applies verbatim to the pinned integral datum and to the pinned rational root
system, which share their reflection permutations. Cartan-type rigidity transports the rational
result to every finite reduced crystallographic root system of type `Aₙ`.

## Main definitions

* `TauCeti.DynkinType.typeARootPermHom`: the diagonal action of permutations of `Fin (n + 1)` on
  the pinned root indices of type `Aₙ`.
* `TauCeti.DynkinType.typeAWeylGroupEquiv`: the explicit equivalence between the Weyl group of the
  pinned integral datum and `Equiv.Perm (Fin (n + 1))`.
* `TauCeti.DynkinType.typeARationalWeylGroupEquiv`: the corresponding equivalence for the pinned
  rational root system.

## Main results

* `RootPairing.weylGroup_equiv_perm_of_typeA`: **the Weyl group of every finite
  reduced crystallographic root system of type `Aₙ` is the symmetric group on `n + 1` letters.**
* `RootPairing.card_weylGroup_of_hasCartanType_A`: its order is `(n + 1)!`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Section 2.10.
-/

public section

open Function Set

namespace TauCeti.DynkinType

open RootPairing

noncomputable section

variable (n : ℕ)

/-- The diagonal action of a permutation of the `n + 1` classical coordinates on the ordered
pairs indexing the roots of type `Aₙ`, transported to the pinned root enumeration. This is
`TauCeti.SplitTorus.coordinatePermRootIndexHom` read through `TauCeti.DynkinType.typeAIndexEquiv`.
-/
def typeARootPermHom : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n * (n + 1))) :=
  (typeAIndexEquiv n).permCongrHom.toMonoidHom.comp SplitTorus.coordinatePermRootIndexHom

/-- The diagonal action applies the same coordinate permutation to both entries of a root index. -/
@[simp]
theorem typeAIndexEquiv_symm_typeARootPermHom_apply (σ : Equiv.Perm (Fin (n + 1)))
    (p : TypeAIndex n) :
    ((typeAIndexEquiv n).symm (typeARootPermHom n σ (typeAIndexEquiv n p))).val =
      (σ p.val.1, σ p.val.2) := by
  rw [typeARootPermHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    SplitTorus.coordinatePermRootIndexHom_apply, SplitTorus.coordinatePermRootIndex_coe]

/-- The diagonal action on type-`Aₙ` root indices is faithful. -/
theorem typeARootPermHom_injective : Function.Injective (typeARootPermHom n) :=
  (typeAIndexEquiv n).permCongrHom.injective.comp SplitTorus.coordinatePermRootIndexHom_injective

private theorem typeARootPermHom_swap (p : TypeAIndex n) :
    typeARootPermHom n (Equiv.swap p.val.1 p.val.2) =
      (typeASimplyConnectedRootDatum n).reflectionPerm (typeAIndexEquiv n p) := by
  apply Equiv.ext
  intro k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv n).surjective k
  apply (typeAIndexEquiv n).symm.injective
  apply Subtype.ext
  rw [typeAIndexEquiv_symm_typeARootPermHom_apply, typeAIndexEquiv_symm_reflectionPerm]

/-- The integral type-`Aₙ` datum permutes its roots by exactly the
diagonal actions of coordinate permutations: reflections are transpositions, and transpositions
generate the symmetric group. -/
private theorem range_weylGroupToPerm_eq_range_typeARootPermHom :
    (typeASimplyConnectedRootDatum n).weylGroupToPerm.range = (typeARootPermHom n).range := by
  rw [range_weylGroupToPerm]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective k
    exact ⟨Equiv.swap p.val.1 p.val.2, typeARootPermHom_swap n p⟩
  · rintro _ ⟨σ, rfl⟩
    induction σ using Equiv.Perm.swap_induction_on with
    | one =>
        rw [map_one]
        exact Subgroup.one_mem _
    | swap_mul σ a b hab ih =>
        rw [map_mul]
        refine Subgroup.mul_mem _ ?_ ih
        rw [typeARootPermHom_swap n ⟨(a, b), hab⟩]
        exact Subgroup.subset_closure ⟨_, rfl⟩

private theorem weylGroupToPerm_typeASimplyConnectedRootDatum_injective :
    Function.Injective (typeASimplyConnectedRootDatum n).weylGroupToPerm :=
  (RootPairing.Equiv.indexHom_injective_of_corootSpan_eq_top
    (typeASimplyConnectedRootDatum n) (corootSpan_typeASimplyConnectedRootDatum_eq_top n)).comp
      Subtype.val_injective

/-- **The Weyl group of the pinned integral datum of type `Aₙ` is the symmetric group on
`n + 1` letters.** Under this equivalence the reflection in `e_a - e_b` is the transposition
of `a` and `b`; see `typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv`. -/
noncomputable def typeAWeylGroupEquiv :
    (typeASimplyConnectedRootDatum n).weylGroup ≃* Equiv.Perm (Fin (n + 1)) :=
  (MonoidHom.ofInjective (weylGroupToPerm_typeASimplyConnectedRootDatum_injective n)).trans <|
    (MulEquiv.subgroupCongr (range_weylGroupToPerm_eq_range_typeARootPermHom n)).trans
      (MonoidHom.ofInjective (typeARootPermHom_injective n)).symm

/-- The coordinate permutation attached to a Weyl-group element induces its permutation of the
type-`A` roots by the diagonal action. -/
theorem typeARootPermHom_typeAWeylGroupEquiv
    (w : (typeASimplyConnectedRootDatum n).weylGroup) :
    typeARootPermHom n (typeAWeylGroupEquiv n w) =
      (typeASimplyConnectedRootDatum n).weylGroupToPerm w := by
  rw [typeAWeylGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- Under the type-`A` Weyl-group equivalence, reflection in the root `e_a - e_b` is the
transposition of the two coordinate indices. -/
@[simp]
theorem typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv (p : TypeAIndex n) :
    typeAWeylGroupEquiv n
        (weylGroup.ofIdx (typeASimplyConnectedRootDatum n) (typeAIndexEquiv n p)) =
      Equiv.swap p.val.1 p.val.2 := by
  apply typeARootPermHom_injective n
  rw [typeARootPermHom_typeAWeylGroupEquiv, typeARootPermHom_swap]
  exact Equiv.ext fun k ↦ weylGroupToPerm_ofIdx_apply _ (typeAIndexEquiv n p) k

/-- The `i`-th simple reflection of type `Aₙ` is the adjacent transposition `(i, i + 1)`. -/
@[simp]
theorem typeAWeylGroupEquiv_ofIdx_typeASimpleIndex (i : Fin n) :
    typeAWeylGroupEquiv n
        (weylGroup.ofIdx (typeASimplyConnectedRootDatum n) (typeASimpleIndex n i)) =
      Equiv.swap i.castSucc i.succ := by
  rw [← (typeAIndexEquiv n).apply_symm_apply (typeASimpleIndex n i),
    typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv, typeAIndexEquiv_symm_typeASimpleIndex]
  rfl

/-- The Weyl group of the pinned integral type-`Aₙ` datum has order `(n + 1)!`. -/
theorem card_weylGroup_typeASimplyConnectedRootDatum :
    Nat.card (typeASimplyConnectedRootDatum n).weylGroup = Nat.factorial (n + 1) := by
  rw [Nat.card_congr (typeAWeylGroupEquiv n).toEquiv, Nat.card_perm, Nat.card_fin]

section Realization

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (Q : RootPairing (Fin (n * (n + 1))) R M N)
  (hQ : Q.reflectionPerm = (typeASimplyConnectedRootDatum n).reflectionPerm)
  (hinj : Function.Injective Q.weylGroupToPerm)

include hQ

include hinj in
/-- Compare a faithful realization with the integral type-`Aₙ` datum through their common
reflection permutations, then use its coordinate-permutation model. -/
private noncomputable def typeAWeylGroupEquivOf : Q.weylGroup ≃* Equiv.Perm (Fin (n + 1)) :=
  (weylGroupEquivOfReflectionPermEq Q (typeASimplyConnectedRootDatum n) hQ hinj
    (weylGroupToPerm_typeASimplyConnectedRootDatum_injective n)).trans (typeAWeylGroupEquiv n)

include hinj in
private theorem typeARootPermHom_typeAWeylGroupEquivOf (w : Q.weylGroup) :
    typeARootPermHom n (typeAWeylGroupEquivOf n Q hQ hinj w) = Q.weylGroupToPerm w := by
  rw [typeAWeylGroupEquivOf, MulEquiv.trans_apply, typeARootPermHom_typeAWeylGroupEquiv,
    weylGroupToPerm_weylGroupEquivOfReflectionPermEq]

include hinj in
private theorem typeAWeylGroupEquivOf_ofIdx_typeAIndexEquiv (p : TypeAIndex n) :
    typeAWeylGroupEquivOf n Q hQ hinj (weylGroup.ofIdx Q (typeAIndexEquiv n p)) =
      Equiv.swap p.val.1 p.val.2 := by
  rw [typeAWeylGroupEquivOf, MulEquiv.trans_apply,
    weylGroupEquivOfReflectionPermEq_ofIdx, typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv]

include hinj in
private theorem typeAWeylGroupEquivOf_ofIdx_typeASimpleIndex (i : Fin n) :
    typeAWeylGroupEquivOf n Q hQ hinj (weylGroup.ofIdx Q (typeASimpleIndex n i)) =
      Equiv.swap i.castSucc i.succ := by
  rw [← (typeAIndexEquiv n).apply_symm_apply (typeASimpleIndex n i),
    typeAWeylGroupEquivOf_ofIdx_typeAIndexEquiv, typeAIndexEquiv_symm_typeASimpleIndex]
  -- The entries of the explicit pair are `i.castSucc` and `i.succ` by definition of `Fin`.
  rfl

end Realization

variable {n} in
private theorem reflectionPerm_rationalRootSystem_A (hn : 1 ≤ n) :
    ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).reflectionPerm =
      (typeASimplyConnectedRootDatum n).reflectionPerm := by
  rw [reflectionPerm_rationalRootSystem, simplyConnectedRootDatum_A]

/-- The pinned rational root system of type `Aₙ` has Weyl group the symmetric group on
`n + 1` letters. It has the same reflection permutations as the integral datum, so the same
comparison of permutation actions on root indices applies. -/
noncomputable def typeARationalWeylGroupEquiv (hn : 1 ≤ n) :
    ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroup ≃*
      Equiv.Perm (Fin (n + 1)) :=
  typeAWeylGroupEquivOf n _ (reflectionPerm_rationalRootSystem_A hn)
    (weylGroupToPerm_injective ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)))

/-- The coordinate permutation attached to a rational Weyl-group element induces its permutation
of the type-`A` roots by the diagonal action. -/
theorem typeARootPermHom_typeARationalWeylGroupEquiv (hn : 1 ≤ n)
    (w : ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroup) :
    typeARootPermHom n (typeARationalWeylGroupEquiv n hn w) =
      ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroupToPerm w :=
  typeARootPermHom_typeAWeylGroupEquivOf n _ _ _ w

/-- Under the rational type-`A` Weyl-group equivalence, reflection in the root `e_a - e_b` is the
transposition of the two coordinate indices. -/
@[simp]
theorem typeARationalWeylGroupEquiv_ofIdx_typeAIndexEquiv (hn : 1 ≤ n) (p : TypeAIndex n) :
    typeARationalWeylGroupEquiv n hn
        (weylGroup.ofIdx ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn))
          (typeAIndexEquiv n p)) =
      Equiv.swap p.val.1 p.val.2 :=
  typeAWeylGroupEquivOf_ofIdx_typeAIndexEquiv n _ _ _ p

/-- The `i`-th simple reflection of the rational root system of type `Aₙ` is the adjacent
transposition `(i, i + 1)`. -/
@[simp]
theorem typeARationalWeylGroupEquiv_ofIdx_typeASimpleIndex (hn : 1 ≤ n) (i : Fin n) :
    typeARationalWeylGroupEquiv n hn
        (weylGroup.ofIdx ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn))
          (typeASimpleIndex n i)) =
      Equiv.swap i.castSucc i.succ :=
  typeAWeylGroupEquivOf_ofIdx_typeASimpleIndex n _ _ _ i

end

end TauCeti.DynkinType

namespace TauCeti

noncomputable section

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N) [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- **A root system of type `Aₙ` has Weyl group the symmetric group on `n + 1` letters.**

The equivalence is noncanonical for an arbitrary root system because `HasCartanType` records only
the existence of a labelling of the simple roots. It is obtained by transporting the explicit
coordinate equivalence for the pinned rational root system through Cartan-type rigidity. -/
theorem _root_.RootPairing.weylGroup_equiv_perm_of_typeA {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.A n)) :
    Nonempty (P.weylGroup ≃* Equiv.Perm (Fin (n + 1))) := by
  let ht : (DynkinType.A n).Valid := DynkinType.valid_A.mpr hn
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b
    ((DynkinType.A n).rationalBase ht) (.A n) h
    (DynkinType.hasCartanType_rationalRootSystem (.A n) ht)
  exact ⟨e.trans (DynkinType.typeARationalWeylGroupEquiv n hn)⟩

/-- The Weyl group of a root system of type `Aₙ` has order `(n + 1)!`. -/
theorem _root_.RootPairing.card_weylGroup_of_hasCartanType_A {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.A n)) :
    Nat.card P.weylGroup = Nat.factorial (n + 1) := by
  obtain ⟨e⟩ := P.weylGroup_equiv_perm_of_typeA b hn h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

end

end TauCeti
