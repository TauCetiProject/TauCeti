/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Partrec.Code
public import TauCeti.Computability.SingleOracle.Domain

/-!
# Uniform domain compilers for ordinary program codes

This file specializes the uniform oracle-program domain compilers from
`TauCeti.Computability.SingleOracle.Domain` to ordinary Mathlib program codes `Nat.Partrec.Code`
at the constant-zero oracle via `toSingleOracleCode` and `toPartrecCode`, without duplicating the
search or semantic proofs.

Direct domain combinators (`interList`, `restrictId`) live alongside the basic code equations in
`TauCeti.Computability.Partrec.Code`.

## Main definitions

* `Nat.Partrec.Code.unionList`, `Nat.Partrec.Code.union`: uniform finite-union compilers.
* `Nat.Partrec.Code.rangeDom`: uniform range-to-domain compiler.
* `Nat.Partrec.Code.imageDom`: uniform partial-image compiler.
* `Nat.Partrec.Code.projDom`: uniform projection compiler.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and
  III.1.
-/

public section

namespace Nat.Partrec.Code

/-- Finite-union compiler on lists of ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def unionList (cs : List Code) : Code :=
  (TauCeti.Oracle.Single.Code.unionList (cs.map toSingleOracleCode)).toPartrecCode

/-- Specialization equation identifying `unionList` with the constant-zero-oracle `unionList`
compiler. -/
theorem unionList_def (cs : List Code) :
    unionList cs =
      (TauCeti.Oracle.Single.Code.unionList (cs.map toSingleOracleCode)).toPartrecCode :=
  (rfl)

/-- Finite union of ordinary code lists is primitive recursive. -/
theorem primrec_unionList : _root_.Primrec unionList :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_unionList.comp <|
      _root_.Primrec.list_map _root_.Primrec.id
        (_root_.Primrec₂.mk (primrec_toSingleOracleCode.comp _root_.Primrec.snd))

/-- The domain of `unionList cs` is the union of the domains of its entries. -/
@[simp]
theorem dom_eval_unionList (cs : List Code) :
    (unionList cs).eval.Dom = ⋃ c ∈ cs, c.eval.Dom := by
  ext x
  simp [unionList]

/-- Binary-union compiler on ordinary codes, specialized from the uniform oracle-program compiler
at the constant-zero oracle. -/
noncomputable def union (cf cg : Code) : Code :=
  (TauCeti.Oracle.Single.Code.union cf.toSingleOracleCode cg.toSingleOracleCode).toPartrecCode

/-- Specialization equation identifying `union` with the constant-zero-oracle `union` compiler. -/
theorem union_def (cf cg : Code) :
    union cf cg =
      (TauCeti.Oracle.Single.Code.union
        cf.toSingleOracleCode cg.toSingleOracleCode).toPartrecCode :=
  (rfl)

/-- Binary union of ordinary codes is primitive recursive. -/
theorem primrec₂_union : Primrec₂ union :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec₂_union.comp
      (primrec_toSingleOracleCode.comp _root_.Primrec.fst)
      (primrec_toSingleOracleCode.comp _root_.Primrec.snd)

/-- The domain of `union cf cg` is the union of the domains of `cf` and `cg`. -/
@[simp]
theorem dom_eval_union (cf cg : Code) :
    (union cf cg).eval.Dom = cf.eval.Dom ∪ cg.eval.Dom := by
  simp [union]

/-- Range-to-domain compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def rangeDom (f : Code) : Code :=
  (TauCeti.Oracle.Single.Code.rangeDom f.toSingleOracleCode).toPartrecCode

/-- Specialization equation identifying `rangeDom` with the constant-zero-oracle `rangeDom`
compiler. -/
theorem rangeDom_def (f : Code) :
    rangeDom f = (TauCeti.Oracle.Single.Code.rangeDom f.toSingleOracleCode).toPartrecCode :=
  (rfl)

/-- Range-to-domain compilation is primitive recursive on ordinary codes. -/
theorem primrec_rangeDom : _root_.Primrec rangeDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_rangeDom.comp primrec_toSingleOracleCode

/-- The domain of `rangeDom f` is the range of `f`. -/
@[simp]
theorem dom_eval_rangeDom (f : Code) :
    (rangeDom f).eval.Dom = f.eval.ran := by
  simp [rangeDom]

/-- Partial-image compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def imageDom (f c : Code) : Code :=
  (TauCeti.Oracle.Single.Code.imageDom f.toSingleOracleCode c.toSingleOracleCode).toPartrecCode

/-- Specialization equation identifying `imageDom` with the constant-zero-oracle `imageDom`
compiler. -/
theorem imageDom_def (f c : Code) :
    imageDom f c =
      (TauCeti.Oracle.Single.Code.imageDom
        f.toSingleOracleCode c.toSingleOracleCode).toPartrecCode :=
  (rfl)

/-- Partial-image compilation is primitive recursive on ordinary codes. -/
theorem primrec₂_imageDom : Primrec₂ imageDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec₂_imageDom.comp
      (primrec_toSingleOracleCode.comp _root_.Primrec.fst)
      (primrec_toSingleOracleCode.comp _root_.Primrec.snd)

/-- The domain of `imageDom f c` is the partial image of `c.eval.Dom` under `f`. -/
@[simp]
theorem dom_eval_imageDom (f c : Code) :
    (imageDom f c).eval.Dom = f.eval.image c.eval.Dom := by
  simp [imageDom]

/-- Existential-projection compiler on ordinary codes, specialized from the uniform oracle-program
compiler at the constant-zero oracle. -/
noncomputable def projDom (c : Code) : Code :=
  (TauCeti.Oracle.Single.Code.projDom c.toSingleOracleCode).toPartrecCode

/-- Specialization equation identifying `projDom` with the constant-zero-oracle `projDom`
compiler. -/
theorem projDom_def (c : Code) :
    projDom c = (TauCeti.Oracle.Single.Code.projDom c.toSingleOracleCode).toPartrecCode :=
  (rfl)

/-- Existential projection on ordinary codes is primitive recursive. -/
theorem primrec_projDom : _root_.Primrec projDom :=
  TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
    TauCeti.Oracle.Single.Code.primrec_projDom.comp primrec_toSingleOracleCode

/-- The domain of `projDom c` is the first-coordinate projection of `c.eval.Dom` under Mathlib's
`Nat.pair`. -/
@[simp]
theorem dom_eval_projDom (c : Code) :
    (projDom c).eval.Dom = {x | ∃ y, Nat.pair x y ∈ c.eval.Dom} := by
  simp [projDom]

end Nat.Partrec.Code
