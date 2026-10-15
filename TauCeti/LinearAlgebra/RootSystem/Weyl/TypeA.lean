/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType

/-!
# Weyl groups of type A

The roots of the pinned datum of type `Aₙ` are indexed by the ordered pairs `(a, b)` of distinct
elements of `Fin (n + 1)`. A permutation of these `n + 1` coordinates therefore acts diagonally
on the root indices. The explicit reflection formula for the pinned datum says that every root
reflection is the diagonal action of a transposition. Conversely, transpositions generate the
symmetric group. Faithfulness of the action on roots then identifies the Weyl group with the full
symmetric group.

The computation is first made on the pinned integral datum. Entrywise base change carries it to
the pinned rational root system, and Cartan-type rigidity transports the result to every finite
reduced crystallographic root system of type `Aₙ`.

## Main definitions

* `TauCeti.DynkinType.typeARootPermHom`: the diagonal action of permutations of `Fin (n + 1)` on
  the pinned root indices of type `Aₙ`.
* `TauCeti.DynkinType.typeAWeylGroupEquiv`: the explicit equivalence between the Weyl group of the
  pinned integral datum and `Equiv.Perm (Fin (n + 1))`.
* `TauCeti.DynkinType.typeARationalWeylGroupEquiv`: the corresponding equivalence for the pinned
  rational root system.

## Main results

* `TauCeti.weylGroup_equiv_perm_of_typeA`: **the Weyl group of every finite
  reduced crystallographic root system of type `Aₙ` is the symmetric group on `n + 1` letters.**
* `TauCeti.card_weylGroup_of_hasCartanType_A`: its order is `(n + 1)!`.

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
pairs indexing the roots of type `Aₙ`, transported to the pinned root enumeration. -/
def typeARootPermHom : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n * (n + 1))) where
  toFun σ := ((typeAIndexEquiv n).symm.trans
    ((σ.prodCongr σ).subtypeEquiv
      (p := fun p ↦ p.1 ≠ p.2) (q := fun p ↦ p.1 ≠ p.2)
      (fun p ↦ σ.injective.ne_iff.symm))).trans (typeAIndexEquiv n)
  map_one' := by
    apply Equiv.ext
    intro k
    obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective k
    simp only [ne_eq, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq,
      EmbeddingLike.apply_eq_iff_eq]
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro k
    obtain ⟨p, rfl⟩ := (typeAIndexEquiv n).surjective k
    simp only [ne_eq, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_mul,
      Equiv.coe_trans, comp_apply, EmbeddingLike.apply_eq_iff_eq]
    apply Subtype.ext
    rfl

/-- The diagonal action applies the same coordinate permutation to both entries of a root index. -/
@[simp]
theorem typeAIndexEquiv_symm_typeARootPermHom_apply (σ : Equiv.Perm (Fin (n + 1)))
    (p : TypeAIndex n) :
    ((typeAIndexEquiv n).symm (typeARootPermHom n σ (typeAIndexEquiv n p))).val =
      (σ p.val.1, σ p.val.2) := by
  simp only [typeARootPermHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rfl

/-- The diagonal action on type-`Aₙ` root indices is faithful. -/
theorem typeARootPermHom_injective : Function.Injective (typeARootPermHom n) := by
  intro σ τ hστ
  apply Equiv.ext
  intro i
  by_cases hn : n = 0
  · apply Fin.ext
    omega
  · have hcard : 1 < Fintype.card (Fin (n + 1)) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    let p : TypeAIndex n := ⟨(i, j), hji.symm⟩
    have h := congrArg (fun e : Equiv.Perm (Fin (n * (n + 1))) ↦
      ((typeAIndexEquiv n).symm (e (typeAIndexEquiv n p))).val.1) hστ
    simpa [p] using h

private theorem typeARootPermHom_swap (p : TypeAIndex n) :
    typeARootPermHom n (Equiv.swap p.val.1 p.val.2) =
      (typeASimplyConnectedRootDatum n).reflectionPerm (typeAIndexEquiv n p) := by
  apply Equiv.ext
  intro k
  obtain ⟨q, rfl⟩ := (typeAIndexEquiv n).surjective k
  apply (typeAIndexEquiv n).symm.injective
  apply Subtype.ext
  simpa using typeAIndexEquiv_symm_reflectionPerm p q |>.symm

private theorem exists_typeARootPermHom_eq_weylGroupToPerm
    (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ w : (typeASimplyConnectedRootDatum n).weylGroup,
      typeARootPermHom n σ = (typeASimplyConnectedRootDatum n).weylGroupToPerm w := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, (map_one (typeARootPermHom n)).trans (map_one _).symm⟩
  | swap_mul σ a b hab ih =>
      obtain ⟨w, hw⟩ := ih
      let p : TypeAIndex n := ⟨(a, b), hab⟩
      refine ⟨weylGroup.ofIdx (typeASimplyConnectedRootDatum n) (typeAIndexEquiv n p) * w, ?_⟩
      change typeARootPermHom n (Equiv.swap p.val.1 p.val.2 * σ) = _
      rw [map_mul, map_mul, hw, typeARootPermHom_swap]
      exact congrArg (fun e : Equiv.Perm (Fin (n * (n + 1))) ↦
        e * (typeASimplyConnectedRootDatum n).weylGroupToPerm w)
        (Equiv.ext fun k ↦ (weylGroupToPerm_ofIdx_apply
          (typeASimplyConnectedRootDatum n) (typeAIndexEquiv n p) k).symm)

private theorem exists_typeARootPermHom_of_weylGroup
    (w : (typeASimplyConnectedRootDatum n).weylGroup) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      typeARootPermHom n σ = (typeASimplyConnectedRootDatum n).weylGroupToPerm w := by
  obtain ⟨w, hw⟩ := w
  induction hw using weylGroup.induction with
  | mem k =>
      let p := (typeAIndexEquiv n).symm k
      refine ⟨Equiv.swap p.val.1 p.val.2, ?_⟩
      have hk : typeAIndexEquiv n p = k := (typeAIndexEquiv n).apply_symm_apply k
      rw [typeARootPermHom_swap, hk]
      exact Equiv.ext fun j ↦ (weylGroupToPerm_ofIdx_apply
        (typeASimplyConnectedRootDatum n) k j).symm
  | one => exact ⟨1, (map_one (typeARootPermHom n)).trans (map_one _).symm⟩
  | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      obtain ⟨σ₁, hσ₁⟩ := ih₁
      obtain ⟨σ₂, hσ₂⟩ := ih₂
      refine ⟨σ₁ * σ₂, ?_⟩
      change typeARootPermHom n (σ₁ * σ₂) =
        (typeASimplyConnectedRootDatum n).weylGroupToPerm
          (⟨w₁, hw₁⟩ * ⟨w₂, hw₂⟩)
      rw [map_mul, map_mul, hσ₁, hσ₂]

private theorem weylGroupToPerm_typeASimplyConnectedRootDatum_injective :
    Function.Injective (typeASimplyConnectedRootDatum n).weylGroupToPerm :=
  (RootPairing.Equiv.indexHom_injective_of_corootSpan_eq_top
    (typeASimplyConnectedRootDatum n) (corootSpan_typeASimplyConnectedRootDatum_eq_top n)).comp
      Subtype.val_injective

/-- Recover the coordinate permutation represented by a Weyl-group element of the pinned type-`A`
datum. Existence comes from induction on root reflections, and faithfulness of the diagonal action
makes the choice multiplicative. -/
private noncomputable def typeAWeylGroupToPerm :
    (typeASimplyConnectedRootDatum n).weylGroup →* Equiv.Perm (Fin (n + 1)) where
  toFun w := (exists_typeARootPermHom_of_weylGroup n w).choose
  map_one' := by
    apply typeARootPermHom_injective n
    calc
      typeARootPermHom n (exists_typeARootPermHom_of_weylGroup n 1).choose =
          (typeASimplyConnectedRootDatum n).weylGroupToPerm 1 :=
        (exists_typeARootPermHom_of_weylGroup n 1).choose_spec
      _ = 1 := map_one _
      _ = typeARootPermHom n 1 := (map_one _).symm
  map_mul' w₁ w₂ := by
    apply typeARootPermHom_injective n
    calc
      typeARootPermHom n (exists_typeARootPermHom_of_weylGroup n (w₁ * w₂)).choose =
          (typeASimplyConnectedRootDatum n).weylGroupToPerm (w₁ * w₂) :=
        (exists_typeARootPermHom_of_weylGroup n (w₁ * w₂)).choose_spec
      _ = (typeASimplyConnectedRootDatum n).weylGroupToPerm w₁ *
          (typeASimplyConnectedRootDatum n).weylGroupToPerm w₂ := map_mul _ _ _
      _ = typeARootPermHom n (exists_typeARootPermHom_of_weylGroup n w₁).choose *
          typeARootPermHom n (exists_typeARootPermHom_of_weylGroup n w₂).choose :=
        congrArg₂ (fun x y ↦ x * y)
          (exists_typeARootPermHom_of_weylGroup n w₁).choose_spec.symm
          (exists_typeARootPermHom_of_weylGroup n w₂).choose_spec.symm
      _ = typeARootPermHom n
          ((exists_typeARootPermHom_of_weylGroup n w₁).choose *
            (exists_typeARootPermHom_of_weylGroup n w₂).choose) := (map_mul _ _ _).symm

private theorem typeARootPermHom_typeAWeylGroupToPerm
    (w : (typeASimplyConnectedRootDatum n).weylGroup) :
    typeARootPermHom n (typeAWeylGroupToPerm n w) =
      (typeASimplyConnectedRootDatum n).weylGroupToPerm w := by
  change typeARootPermHom n (exists_typeARootPermHom_of_weylGroup n w).choose = _
  exact (exists_typeARootPermHom_of_weylGroup n w).choose_spec

private theorem typeAWeylGroupToPerm_injective :
    Function.Injective (typeAWeylGroupToPerm n) := by
  intro w₁ w₂ h
  apply weylGroupToPerm_typeASimplyConnectedRootDatum_injective n
  rw [← typeARootPermHom_typeAWeylGroupToPerm,
    ← typeARootPermHom_typeAWeylGroupToPerm, h]

private theorem typeAWeylGroupToPerm_surjective :
    Function.Surjective (typeAWeylGroupToPerm n) := by
  intro σ
  obtain ⟨w, hw⟩ := exists_typeARootPermHom_eq_weylGroupToPerm n σ
  refine ⟨w, typeARootPermHom_injective n ?_⟩
  rw [typeARootPermHom_typeAWeylGroupToPerm, ← hw]

/-- **The Weyl group of the pinned integral datum of type `Aₙ` is the symmetric group on
`n + 1` letters.** Under this equivalence the reflection in `e_a - e_b` is the transposition
of `a` and `b`; see `typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv`. -/
noncomputable def typeAWeylGroupEquiv :
    (typeASimplyConnectedRootDatum n).weylGroup ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective (typeAWeylGroupToPerm n)
    ⟨typeAWeylGroupToPerm_injective n, typeAWeylGroupToPerm_surjective n⟩

/-- The coordinate permutation attached to a Weyl-group element induces its permutation of the
type-`A` roots by the diagonal action. -/
theorem typeARootPermHom_typeAWeylGroupEquiv
    (w : (typeASimplyConnectedRootDatum n).weylGroup) :
    typeARootPermHom n (typeAWeylGroupEquiv n w) =
      (typeASimplyConnectedRootDatum n).weylGroupToPerm w := by
  change typeARootPermHom n (typeAWeylGroupToPerm n w) = _
  exact typeARootPermHom_typeAWeylGroupToPerm n w

/-- Under the type-`A` Weyl-group equivalence, reflection in the root `e_a - e_b` is the
transposition of the two coordinate indices. -/
@[simp]
theorem typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv (p : TypeAIndex n) :
    typeAWeylGroupEquiv n
        (weylGroup.ofIdx (typeASimplyConnectedRootDatum n) (typeAIndexEquiv n p)) =
      Equiv.swap p.val.1 p.val.2 := by
  apply typeARootPermHom_injective n
  rw [typeARootPermHom_typeAWeylGroupEquiv, typeARootPermHom_swap]
  exact Equiv.ext fun k ↦
    weylGroupToPerm_ofIdx_apply (typeASimplyConnectedRootDatum n) (typeAIndexEquiv n p) k

/-- The `i`-th simple reflection of type `Aₙ` is the adjacent transposition `(i, i + 1)`. -/
@[simp]
theorem typeAWeylGroupEquiv_ofIdx_typeASimpleIndex (i : Fin n) :
    typeAWeylGroupEquiv n
        (weylGroup.ofIdx (typeASimplyConnectedRootDatum n) (typeASimpleIndex n i)) =
      Equiv.swap i.castSucc i.succ := by
  let p := (typeAIndexEquiv n).symm (typeASimpleIndex n i)
  have hp : typeAIndexEquiv n p = typeASimpleIndex n i :=
    (typeAIndexEquiv n).apply_symm_apply _
  rw [← hp, typeAWeylGroupEquiv_ofIdx_typeAIndexEquiv]
  have hp' := typeAIndexEquiv_symm_typeASimpleIndex i
  change Equiv.swap p.val.1 p.val.2 = _
  dsimp only [p]
  rw [hp']
  congr 2

/-- The Weyl group of the pinned integral type-`Aₙ` datum has order `(n + 1)!`. -/
theorem card_weylGroup_typeASimplyConnectedRootDatum :
    Nat.card (typeASimplyConnectedRootDatum n).weylGroup = Nat.factorial (n + 1) := by
  rw [Nat.card_congr (typeAWeylGroupEquiv n).toEquiv, Nat.card_perm, Nat.card_fin]

/-- The pinned rational root system of type `Aₙ` has Weyl group the symmetric group on
`n + 1` letters. This is the integral computation transported through entrywise base change. -/
noncomputable def typeARationalWeylGroupEquiv (hn : 1 ≤ n) :
    ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroup ≃*
      Equiv.Perm (Fin (n + 1)) := by
  let hdot : ∀ x y : Fin n → ℤ,
      (typeASimplyConnectedRootDatum n).toLinearMap x y = x ⬝ᵥ y :=
    fun x y ↦ toLinearMap_typeASimplyConnectedRootDatum x y
  have hQ : (DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn) =
      rootPairingBaseChange ℚ (typeASimplyConnectedRootDatum n) hdot := by
    rw [rationalRootSystem_def]
    congr
    exact simplyConnectedRootDatum_A n _
  rw [hQ]
  exact (weylGroupBaseChangeEquiv ℚ (typeASimplyConnectedRootDatum n) hdot).symm.trans
    (typeAWeylGroupEquiv n)

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
theorem weylGroup_equiv_perm_of_typeA {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.A n)) :
    Nonempty (P.weylGroup ≃* Equiv.Perm (Fin (n + 1))) := by
  let ht : (DynkinType.A n).Valid := DynkinType.valid_A.mpr hn
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b
    ((DynkinType.A n).rationalBase ht) (.A n) h
    (DynkinType.hasCartanType_rationalRootSystem (.A n) ht)
  exact ⟨e.trans (DynkinType.typeARationalWeylGroupEquiv n hn)⟩

/-- The Weyl group of a root system of type `Aₙ` has order `(n + 1)!`. -/
theorem card_weylGroup_of_hasCartanType_A {n : ℕ} (hn : 1 ≤ n)
    (h : HasCartanType P b (.A n)) :
    Nat.card P.weylGroup = Nat.factorial (n + 1) := by
  obtain ⟨e⟩ := weylGroup_equiv_perm_of_typeA P b hn h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

end


end TauCeti
