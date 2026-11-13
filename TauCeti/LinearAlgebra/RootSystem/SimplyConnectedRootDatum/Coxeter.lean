/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Action
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# The Bourbaki-numbered Coxeter system of the pinned simply connected root datum

Tits' theorem (`TauCeti.weylCoxeterSystem`) makes the Weyl group of a finite reduced
crystallographic root pairing into a Coxeter system indexed by the support of a base. For a
valid Dynkin type `t`, the pinned root datum `t.simplyConnectedRootDatum ht` carries a
numbered base `t.simplyConnectedBase ht` whose support is matched with `Fin t.rank` by
`t.simpleSupportEquivSimplyConnectedBase ht`, matching the base's Cartan matrix with
`t.cartanMatrix` and hence its Coxeter matrix with `t.coxeterMatrix`.

This file transports `TauCeti.weylCoxeterSystem` along that Bourbaki node numbering, giving a
canonical `CoxeterSystem t.coxeterMatrix (t.simplyConnectedRootDatum ht).weylGroup` whose
`i`-th simple reflection is `ofIdx (t.simpleIndex ht i)` and whose word product is
`t.geckWeylWordProd ht`.

## Main definitions

* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem`: the Weyl group of
  `t.simplyConnectedRootDatum ht` as a Coxeter system for `t.coxeterMatrix`.

## Main results

* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem_simple`: the `i`-th simple reflection
  is `RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)`.
* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem_wordProd`: the Coxeter word product
  agrees with `t.geckWeylWordProd ht`.
* `TauCeti.DynkinType.length_simplyConnectedWeylCoxeterSystem_eq` and
  `TauCeti.DynkinType.isReduced_simplyConnectedWeylCoxeterSystem_iff`: the Coxeter length is
  the inversion count with respect to `t.simplyConnectedBase ht`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1, no. 5.
* R. W. Carter, *Simple Groups of Lie Type*, §2.2 and §7.2.
-/

public noncomputable section

namespace TauCeti.DynkinType

private def coxeterSystemOfMatrixEq {B W : Type*} [Group W] {M₁ M₂ : CoxeterMatrix B}
    (h : M₁ = M₂) (cs : CoxeterSystem M₁ W) : CoxeterSystem M₂ W :=
  h ▸ cs

private theorem coxeterSystemOfMatrixEq_simple {B W : Type*} [Group W] {M₁ M₂ : CoxeterMatrix B}
    (h : M₁ = M₂) (cs : CoxeterSystem M₁ W) (i : B) :
    (coxeterSystemOfMatrixEq h cs).simple i = cs.simple i := by
  subst h
  rfl

variable (t : DynkinType) (ht : t.Valid)

/-- The Coxeter matrix of the pinned simply connected base, reindexed by the Bourbaki nodes,
is `t.coxeterMatrix`. -/
theorem reindex_coxeterMatrixOfBase_simplyConnectedBase :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
        (t.simpleSupportEquivSimplyConnectedBase ht).symm =
      t.coxeterMatrix := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm, coxeterMatrixOfBase_apply,
    coxeterMatrix_apply, t.cartanMatrix_simplyConnectedBase_apply ht,
    t.cartanMatrix_simplyConnectedBase_apply ht]

/-- **The Bourbaki-numbered Coxeter system of the pinned Weyl group.** By Tits' theorem, the
Weyl group of `t.simplyConnectedRootDatum ht` is a Coxeter system for `t.coxeterMatrix` whose
`i`-th simple reflection is the reflection in `t.simpleIndex ht i`. -/
def simplyConnectedWeylCoxeterSystem :
    CoxeterSystem t.coxeterMatrix (t.simplyConnectedRootDatum ht).weylGroup :=
  letI := t.isReduced_simplyConnectedRootDatum ht
  coxeterSystemOfMatrixEq (t.reindex_coxeterMatrixOfBase_simplyConnectedBase ht)
    ((weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
      (t.simpleSupportEquivSimplyConnectedBase ht).symm)

/-- The `i`-th simple reflection of `t.simplyConnectedWeylCoxeterSystem ht` is the reflection
in the `i`-th Bourbaki simple root `t.simpleIndex ht i`. -/
@[simp]
theorem simplyConnectedWeylCoxeterSystem_simple (i : Fin t.rank) :
    (t.simplyConnectedWeylCoxeterSystem ht).simple i =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  rw [simplyConnectedWeylCoxeterSystem, coxeterSystemOfMatrixEq_simple]
  simp

/-- Evaluating a word in `Fin t.rank` through `t.simplyConnectedWeylCoxeterSystem ht` gives
`t.geckWeylWordProd ht`. -/
@[simp]
theorem simplyConnectedWeylCoxeterSystem_wordProd (l : List (Fin t.rank)) :
    (t.simplyConnectedWeylCoxeterSystem ht).wordProd l = t.geckWeylWordProd ht l := by
  induction l with
  | nil => simp
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, simplyConnectedWeylCoxeterSystem_simple,
      ih, geckWeylWordProd_cons]

/-- The Coxeter length in `t.simplyConnectedWeylCoxeterSystem ht` is the number of positive
roots of `t.simplyConnectedBase ht` inverted by `w`. -/
@[simp]
theorem length_simplyConnectedWeylCoxeterSystem_eq
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (t.simplyConnectedWeylCoxeterSystem ht).length w =
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w).ncard := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let cs := (weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
    (t.simpleSupportEquivSimplyConnectedBase ht).symm
  rw [(t.simplyConnectedWeylCoxeterSystem ht).length_eq_of_simple_eq cs (fun i => by simp [cs]),
    CoxeterSystem.length_reindex, length_weylCoxeterSystem_eq]

/-- A node word is reduced for `t.simplyConnectedWeylCoxeterSystem ht` if and only if the
element `t.geckWeylWordProd ht l` it spells has `l.length` inversions. -/
theorem isReduced_simplyConnectedWeylCoxeterSystem_iff (l : List (Fin t.rank)) :
    (t.simplyConnectedWeylCoxeterSystem ht).IsReduced l ↔
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (t.geckWeylWordProd ht l)).ncard = l.length := by
  rw [CoxeterSystem.IsReduced, simplyConnectedWeylCoxeterSystem_wordProd,
    length_simplyConnectedWeylCoxeterSystem_eq]

end TauCeti.DynkinType
