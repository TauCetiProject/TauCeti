/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Word
import TauCeti.GroupTheory.Coxeter.Matrix

/-!
# The Coxeter matrix and Bourbaki-numbered Coxeter system of the pinned simply connected root datum

In the pinned datum `TauCeti.DynkinType.simplyConnectedRootDatum`, simple roots are numbered by
`Fin t.rank` in the Bourbaki order. This file records that, read through that numbering, the Coxeter
matrix of the pinned base is the standard Coxeter matrix `t.coxeterMatrix` of the type
(`TauCeti.DynkinType.coxeterMatrixOfBase_simplyConnectedBase`).

Tits' theorem (`TauCeti.weylCoxeterSystem`) makes the Weyl group of a finite reduced
crystallographic root pairing into a Coxeter system indexed by the support of a base. Transporting
`TauCeti.weylCoxeterSystem` along `t.simpleSupportEquivSimplyConnectedBase ht` gives a canonical
`CoxeterSystem t.coxeterMatrix (t.simplyConnectedRootDatum ht).weylGroup` whose `i`-th simple
reflection is `ofIdx (t.simpleIndex ht i)` and whose word product is
`t.simplyConnectedWeylWordProd ht`.

## Main definitions

* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem`: the Weyl group of
  `t.simplyConnectedRootDatum ht` as a Coxeter system for `t.coxeterMatrix`.

## Main results

* `TauCeti.DynkinType.coxeterMatrixOfBase_simplyConnectedBase` and
  `TauCeti.DynkinType.coxeterMatrixOfBase_simplyConnectedBase_apply`: the Coxeter matrix of the
  pinned base is `t.coxeterMatrix`, reindexed by `t.simpleSupportEquivSimplyConnectedBase ht`.
* `TauCeti.DynkinType.reindex_coxeterMatrixOfBase_simplyConnectedBase`: inverse reindexing form.
* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem_simple`: the `i`-th simple reflection
  is `RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)`.
* `TauCeti.DynkinType.simplyConnectedWeylCoxeterSystem_wordProd`: the Coxeter word product
  agrees with `t.simplyConnectedWeylWordProd ht`.
* `TauCeti.DynkinType.length_simplyConnectedWeylCoxeterSystem_eq` and
  `TauCeti.DynkinType.isReduced_simplyConnectedWeylCoxeterSystem_iff`: the Coxeter length is
  the inversion count with respect to `t.simplyConnectedBase ht`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1, no. 5.
* R. W. Carter, *Simple Groups of Lie Type*, §2.2 and §7.2.
-/

public noncomputable section

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The Coxeter matrix of the numbered base is the Bourbaki-numbered Coxeter matrix of the type. -/
theorem coxeterMatrixOfBase_simplyConnectedBase :
    coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) =
      t.coxeterMatrix.reindex (t.simpleSupportEquivSimplyConnectedBase ht) := by
  rw [coxeterMatrixOfBase_eq_coxeterMatrix_reindex
    (t.simpleSupportEquivSimplyConnectedBase ht).symm, Equiv.symm_symm]
  intro i j
  simpa using t.cartanMatrix_simplyConnectedBase_apply ht
    ((t.simpleSupportEquivSimplyConnectedBase ht).symm i)
    ((t.simpleSupportEquivSimplyConnectedBase ht).symm j)

/-- The entries of the Coxeter matrix of the numbered base are those of the Bourbaki-numbered
Coxeter matrix of the type. -/
theorem coxeterMatrixOfBase_simplyConnectedBase_apply (i j : Fin t.rank) :
    coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (t.simpleSupportEquivSimplyConnectedBase ht i)
        (t.simpleSupportEquivSimplyConnectedBase ht j) =
      t.coxeterMatrix i j := by
  rw [coxeterMatrixOfBase_simplyConnectedBase, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- The Coxeter matrix of the pinned simply connected base, reindexed by the Bourbaki nodes,
is `t.coxeterMatrix`. -/
theorem reindex_coxeterMatrixOfBase_simplyConnectedBase :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
        (t.simpleSupportEquivSimplyConnectedBase ht).symm =
      t.coxeterMatrix := by
  rw [coxeterMatrixOfBase_simplyConnectedBase, CoxeterMatrix.reindex_reindex, Equiv.self_trans_symm,
    CoxeterMatrix.reindex_refl]

/-- **The Bourbaki-numbered Coxeter system of the pinned Weyl group.** By Tits' theorem, the
Weyl group of `t.simplyConnectedRootDatum ht` is a Coxeter system for `t.coxeterMatrix` whose
`i`-th simple reflection is the reflection in `t.simpleIndex ht i`. -/
def simplyConnectedWeylCoxeterSystem :
    CoxeterSystem t.coxeterMatrix (t.simplyConnectedRootDatum ht).weylGroup :=
  letI := t.isReduced_simplyConnectedRootDatum ht
  ((weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
      (t.simpleSupportEquivSimplyConnectedBase ht).symm).castMatrix
    (t.reindex_coxeterMatrixOfBase_simplyConnectedBase ht)

/-- The `i`-th simple reflection of `t.simplyConnectedWeylCoxeterSystem ht` is the reflection
in the `i`-th Bourbaki simple root `t.simpleIndex ht i`. -/
@[simp]
theorem simplyConnectedWeylCoxeterSystem_simple (i : Fin t.rank) :
    (t.simplyConnectedWeylCoxeterSystem ht).simple i =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  simp [simplyConnectedWeylCoxeterSystem]

/-- Evaluating a word in `Fin t.rank` through `t.simplyConnectedWeylCoxeterSystem ht` gives
`t.simplyConnectedWeylWordProd ht`. -/
@[simp]
theorem simplyConnectedWeylCoxeterSystem_wordProd (l : List (Fin t.rank)) :
    (t.simplyConnectedWeylCoxeterSystem ht).wordProd l = t.simplyConnectedWeylWordProd ht l := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  have hmap :
      l.map
          ((weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).reindex
            (t.simpleSupportEquivSimplyConnectedBase ht).symm).simple =
        (l.map (t.simpleSupportEquivSimplyConnectedBase ht)).map
          (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
            (t.simplyConnectedBase ht)).simple := by
    simp [Function.comp_def]
  rw [simplyConnectedWeylCoxeterSystem, CoxeterSystem.wordProd_castMatrix,
    CoxeterSystem.wordProd, hmap]
  simpa only [CoxeterSystem.wordProd, wordProd_map_simpleSupportEquiv] using
    weylCoxeterSystem_wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
      (l.map (t.simpleSupportEquivSimplyConnectedBase ht))

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
element `t.simplyConnectedWeylWordProd ht l` it spells has `l.length` inversions. -/
theorem isReduced_simplyConnectedWeylCoxeterSystem_iff (l : List (Fin t.rank)) :
    (t.simplyConnectedWeylCoxeterSystem ht).IsReduced l ↔
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (t.simplyConnectedWeylWordProd ht l)).ncard = l.length := by
  rw [CoxeterSystem.IsReduced, simplyConnectedWeylCoxeterSystem_wordProd,
    length_simplyConnectedWeylCoxeterSystem_eq]

end TauCeti.DynkinType
