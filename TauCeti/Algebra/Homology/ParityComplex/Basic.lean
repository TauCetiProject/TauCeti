/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.ZMod.Defs
public import TauCeti.Algebra.Homology.Embedding.Restriction.Shift
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Complexes with independent parity

A *complex with independent parity* is an integer-graded cochain complex whose terms also carry a
`ℤ/2`-grading, with a differential of degree `+1` that is odd for the `ℤ/2`-grading, and whose
chain maps are even. The `ℤ/2`-grading `σ` of a term is often, but not always, its degree `q`
modulo `2`; the *independent parity* of a term of degree `q` and parity `σ` is `τ = σ - q`.
Signs governed by the independent parity, rather than by the degree alone, are those of
Pardon's virtual fundamental cycles, where orientation lines of vector spaces of dimension `d`
are complexes of parity `d` concentrated in degree `0`.

The differential raises both the degree and the parity by one, so it preserves the independent
parity. A complex with independent parity is therefore the same as its two parts of independent
parity `τ = 0` and `τ = 1`, each an ordinary cochain complex, and this is how it is recorded:
`TauCeti.ParityComplex C` is the category of families, indexed by `τ : ZMod 2`, of cochain
complexes in `C`, whose morphisms are families of cochain maps, the even chain maps. The term of
degree `q` and parity `σ` is the term of degree `q` of the part of independent parity `σ - q`
(`TauCeti.ParityComplex.term`), and the differential `TauCeti.ParityComplex.d` sends it to the term
of degree `q + 1` and parity `σ + 1`.

Three operations change gradings.

* The **parity change** `Π^k`, for `k : ZMod 2`, keeps degrees and differentials and adds `k` to
  every parity (`TauCeti.ParityComplex.parityShift`).
* The **native shift** by `k : ℤ` shifts the underlying cochain complex as Mathlib's
  `CategoryTheory.shiftFunctor` does: the term of degree `q` is the old term of degree `q + k`,
  with the same parity, and the differential is multiplied by `(-1)^k`
  (`TauCeti.ParityComplex.shift`).
* The **raw reindexing** by `k : ℤ` moves the term of degree `q + k` to degree `q` without changing
  the differential or the independent parity, so that the parity of every term changes by `k`
  (`TauCeti.ParityComplex.reindex`).

Raw reindexing and the native shift differ by the parity change `Π^k` and by the sign
`(-1)^(q k)` in degree `q`: `TauCeti.ParityComplex.parityShiftCompReindexIsoShift` is an
isomorphism `Π^k ⋙ reindex k ≅ shift k`, built from `CochainComplex.restrictionAddIsoShift`.

Every sign exponent here is read in `ZMod 2`, including for negative degrees: the parity of an
integer `n` is `(n : ZMod 2)`, so that for instance a virtual dimension `d = -1` has odd parity.
An exponent computed with `Int.toNat` would instead give `0` there.

## Main definitions

* `TauCeti.ParityComplex C`: complexes with independent parity in `C`, recorded by their parts of
  independent parity `0` and `1`.
* `TauCeti.ParityComplex.term X q σ`: the term of degree `q` and parity `σ`.
* `TauCeti.ParityComplex.d X q σ`: the differential, from degree `q` and parity `σ` to degree
  `q + 1` and parity `σ + 1`.
* `TauCeti.ParityComplex.parityShift C k`: the parity change `Π^k`.
* `TauCeti.ParityComplex.shift C k` and `TauCeti.ParityComplex.reindex C k`: the native shift and
  the raw reindexing by `k : ℤ`.

## Main results

* `TauCeti.ParityComplex.d_comp_d`: the differential squares to zero.
* `TauCeti.ParityComplex.termMap_comp_d`: even chain maps commute with the differentials.
* `TauCeti.ParityComplex.term_parityShift`, `TauCeti.ParityComplex.term_shift` and
  `TauCeti.ParityComplex.term_reindex`: the terms of `Π^k X`, of the native shift and of the raw
  reindexing.
* `TauCeti.ParityComplex.d_parityShift`, `TauCeti.ParityComplex.d_shift` and
  `TauCeti.ParityComplex.d_reindex`: the differentials of `Π^k X`, of the native shift, multiplied
  by `(-1)^k`, and of the raw reindexing.
* `TauCeti.ParityComplex.parityShiftCompReindexIsoShift`: the raw reindexing after the parity
  change `Π^k` is the native shift, up to the degreewise sign `(-1)^(q k)`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. **20** (2016), 779–1034, Convention A.0.3.
-/

public section

open CategoryTheory Limits

namespace TauCeti

section

variable (C : Type*) [Category* C] [HasZeroMorphisms C]

/-- A **complex with independent parity** in `C`: an integer-graded cochain complex whose terms
carry a parity in `ZMod 2`, with odd differential of degree `+1`. Since the differential
preserves the independent parity `τ = σ - q` of a term of degree `q` and parity `σ`, it is
recorded by its parts of independent parity `τ : ZMod 2`, each an ordinary cochain complex.
Morphisms are families of cochain maps, the even chain maps. -/
abbrev ParityComplex : Type _ :=
  GradedObject (ZMod 2) (CochainComplex C ℤ)

end

namespace ParityComplex

section General

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- The term of degree `q` and parity `σ` of a complex with independent parity: the term of
degree `q` of its part of independent parity `σ - q`. -/
def term (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) : C :=
  (X (σ - q)).X q

/-- The term of degree `q` and parity `σ` is the term of degree `q` of the part of independent
parity `τ = σ - q`. -/
theorem term_eq (X : ParityComplex C) {q : ℤ} {σ τ : ZMod 2} (h : σ - q = τ) :
    X.term q σ = (X τ).X q := by
  rw [term, h]

/-- The identification of the term of degree `q` and parity `σ` with the term of degree `q` of
the part of independent parity `τ = σ - q`. -/
def termIso (X : ParityComplex C) {q : ℤ} {σ τ : ZMod 2} (h : σ - q = τ) :
    X.term q σ ≅ (X τ).X q :=
  eqToIso (X.term_eq h)

/-- The differential of a complex with independent parity, from the term of degree `q` and parity
`σ` to the term of degree `q + 1` and parity `σ + 1`: the differential of the part of independent
parity `σ - q`. -/
def d (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) : X.term q σ ⟶ X.term (q + 1) (σ + 1) :=
  (X.termIso rfl).hom ≫ (X (σ - q)).d q (q + 1) ≫
    (X.termIso (by push_cast; ring)).inv

/-- The differential is the differential of the part of independent parity `σ - q`, under the
identifications of terms. -/
theorem d_def (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    X.d q σ = (X.termIso rfl).hom ≫ (X (σ - q)).d q (q + 1) ≫
      (X.termIso (by push_cast; ring)).inv := (rfl)

/-- The differential is the differential, into any degree `q' = q + 1`, of the part of any
independent parity `τ = σ - q`, under the identifications of terms. -/
theorem d_eq (X : ParityComplex C) {q q' : ℤ} {σ τ : ZMod 2} (h : σ - q = τ) (hq : q + 1 = q') :
    X.d q σ = (X.termIso h).hom ≫ (X τ).d q q' ≫
      eqToHom (by subst h hq; exact (X.term_eq (by push_cast; ring)).symm) := by
  subst h hq
  rfl

/-- The differential of a complex with independent parity squares to zero. -/
@[reassoc (attr := simp)]
theorem d_comp_d (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    X.d q σ ≫ X.d (q + 1) (σ + 1) = 0 := by
  simp only [d_def, termIso, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc]
  rw [← eqToHom_naturality_assoc (fun τ ↦ (X τ).d (q + 1) (q + 1 + 1))
      (by push_cast; ring : σ - q = σ + 1 - ((q + 1 : ℤ) : ZMod 2)),
    HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

/-- The component of an even chain map on the term of degree `q` and parity `σ`. -/
def termMap {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ) (σ : ZMod 2) :
    X.term q σ ⟶ Y.term q σ :=
  (X.termIso rfl).hom ≫ (f (σ - q)).f q ≫ (Y.termIso rfl).inv

/-- The component of an even chain map is the component of its part of independent parity
`σ - q`, under the identifications of terms. -/
theorem termMap_def {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ) (σ : ZMod 2) :
    termMap f q σ = (X.termIso rfl).hom ≫ (f (σ - q)).f q ≫ (Y.termIso rfl).inv := (rfl)

/-- The component of an even chain map is the component of its part of any independent parity
`τ = σ - q`, under the identifications of terms. -/
theorem termMap_eq {X Y : ParityComplex C} (f : X ⟶ Y) {q : ℤ} {σ τ : ZMod 2} (h : σ - q = τ) :
    termMap f q σ = (X.termIso h).hom ≫ (f τ).f q ≫ (Y.termIso h).inv := by
  subst h
  rfl

/-- The component of the identity is the identity. -/
@[simp]
theorem termMap_id (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) : termMap (𝟙 X) q σ = 𝟙 _ := by
  simp [termMap_def, termIso]

/-- The components of even chain maps compose. -/
@[reassoc, simp]
theorem termMap_comp {X Y Z : ParityComplex C} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℤ) (σ : ZMod 2) :
    termMap (f ≫ g) q σ = termMap f q σ ≫ termMap g q σ := by
  simp [termMap_def, termIso]

/-- Even chain maps commute with the differentials. -/
@[reassoc (attr := simp)]
theorem termMap_comp_d {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ) (σ : ZMod 2) :
    termMap f q σ ≫ Y.d q σ = X.d q σ ≫ termMap f (q + 1) (σ + 1) := by
  simp only [termMap_def, d_def, termIso, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, HomologicalComplex.Hom.comm_assoc]
  rw [← eqToHom_naturality_assoc (fun τ ↦ (f τ).f (q + 1))
      (by push_cast; ring : σ - q = σ + 1 - ((q + 1 : ℤ) : ZMod 2)),
    eqToHom_trans]

variable (C)

/-- The **parity change** `Π^k`: the same degrees and differentials, with every parity raised by
`k`. Its part of independent parity `τ` is the part of independent parity `τ + k`. The functor
body is exposed so that the parts of `Π^k X` reduce to parts of `X`. -/
@[expose]
def parityShift (k : ZMod 2) : ParityComplex C ⥤ ParityComplex C :=
  GradedObject.comap (CochainComplex C ℤ) (· + k)

variable {C}

@[simp]
theorem parityShift_obj_apply (k : ZMod 2) (X : ParityComplex C) (τ : ZMod 2) :
    (parityShift C k).obj X τ = X (τ + k) := (rfl)

@[simp]
theorem parityShift_map_apply (k : ZMod 2) {X Y : ParityComplex C} (f : X ⟶ Y) (τ : ZMod 2) :
    (parityShift C k).map f τ = f (τ + k) := (rfl)

/-- The term of degree `q` and parity `σ` of `Π^k X` is the term of `X` of degree `q` and parity
`σ + k`. -/
theorem term_parityShift (k : ZMod 2) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((parityShift C k).obj X).term q σ = X.term q (σ + k) := by
  rw [term, term, parityShift_obj_apply, sub_add_eq_add_sub]

/-- The parity change `Π^k` keeps the differential: the differential of `Π^k X` from parity `σ` is
the differential of `X` from parity `σ + k`. -/
theorem d_parityShift (k : ZMod 2) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((parityShift C k).obj X).d q σ =
      eqToHom (term_parityShift k X q σ) ≫ X.d q (σ + k) ≫
        eqToHom (by rw [term_parityShift, add_right_comm]) := by
  rw [d_def, X.d_eq (sub_add_eq_add_sub σ (q : ZMod 2) k).symm rfl]
  simp only [termIso, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  -- The remaining sides agree since the parts of `Π^k X` are parts of `X` by definition.
  rfl

/-- The parity change `Π^k` keeps the components of even chain maps: the component of `Π^k f` on
parity `σ` is the component of `f` on parity `σ + k`. -/
theorem termMap_parityShift (k : ZMod 2) {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ)
    (σ : ZMod 2) :
    termMap ((parityShift C k).map f) q σ =
      eqToHom (term_parityShift k X q σ) ≫ termMap f q (σ + k) ≫
        eqToHom (term_parityShift k Y q σ).symm := by
  rw [termMap_def, termMap_eq f (sub_add_eq_add_sub σ (q : ZMod 2) k).symm]
  simp only [termIso, eqToIso.hom, eqToIso.inv, parityShift_map_apply, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc]
  -- The remaining sides agree since the parts of `Π^k f` are parts of `f` by definition.
  rfl

/-- The parity change `Π^0` is the identity. -/
def parityShiftZeroIso : parityShift C 0 ≅ 𝟭 (ParityComplex C) :=
  GradedObject.comapEq (CochainComplex C ℤ) (funext add_zero) ≪≫ Pi.comapId _ _

/-- The component of `Π^0 X ≅ X` on the part of independent parity `τ` is the identification
`X (τ + 0) = X τ`. -/
@[simp]
theorem parityShiftZeroIso_hom_app_apply (X : ParityComplex C) (τ : ZMod 2) :
    (parityShiftZeroIso (C := C)).hom.app X τ = eqToHom (congrArg X (add_zero τ)) := by
  -- The second factor `Pi.comapId` has identity components.
  exact Category.comp_id (obj := CochainComplex C ℤ) _

/-- The component of `X ≅ Π^0 X` on the part of independent parity `τ` is the identification
`X τ = X (τ + 0)`. -/
@[simp]
theorem parityShiftZeroIso_inv_app_apply (X : ParityComplex C) (τ : ZMod 2) :
    (parityShiftZeroIso (C := C)).inv.app X τ = eqToHom (congrArg X (add_zero τ).symm) := by
  -- The first factor, the inverse of `Pi.comapId`, has identity components.
  exact Category.id_comp (obj := CochainComplex C ℤ) _

/-- Parity changes compose additively: `Π^k ⋙ Π^l ≅ Π^(k + l)`. Since `k + k = 0` in `ZMod 2`,
together with `TauCeti.ParityComplex.parityShiftZeroIso` this shows that `Π^k` is an
involution. -/
def parityShiftCompIso (k l : ZMod 2) :
    parityShift C k ⋙ parityShift C l ≅ parityShift C (k + l) :=
  Pi.comapComp _ _ _ ≪≫
    GradedObject.comapEq (CochainComplex C ℤ) (funext fun τ ↦ by
      simp only [Function.comp_apply]
      rw [add_assoc, add_comm l])

/-- The component of `Π^l (Π^k X) ≅ Π^(k + l) X` on the part of independent parity `τ` is the
identification `X ((τ + l) + k) = X (τ + (k + l))`. -/
@[simp]
theorem parityShiftCompIso_hom_app_apply (k l : ZMod 2) (X : ParityComplex C) (τ : ZMod 2) :
    (parityShiftCompIso (C := C) k l).hom.app X τ =
      eqToHom (congrArg X (show τ + l + k = τ + (k + l) by rw [add_assoc, add_comm l])) := by
  -- The first factor `Pi.comapComp` has identity components.
  exact Category.id_comp (obj := CochainComplex C ℤ) _

/-- The component of `Π^(k + l) X ≅ Π^l (Π^k X)` on the part of independent parity `τ` is the
identification `X (τ + (k + l)) = X ((τ + l) + k)`. -/
@[simp]
theorem parityShiftCompIso_inv_app_apply (k l : ZMod 2) (X : ParityComplex C) (τ : ZMod 2) :
    (parityShiftCompIso (C := C) k l).inv.app X τ =
      eqToHom (congrArg X (show τ + (k + l) = τ + l + k by rw [add_assoc, add_comm l])) := by
  -- The second factor, the inverse of `Pi.comapComp`, has identity components.
  exact Category.comp_id (obj := CochainComplex C ℤ) _

variable (C)

/-- The **raw reindexing** by `k : ℤ`: the term of degree `q + k` moves to degree `q` with the
same differential and the same independent parity, so that its parity is raised by `k`. Each part
is restricted along `i ↦ i + k`. The functor body is exposed so that the parts of the reindexing
reduce to restrictions of parts. -/
@[expose]
def reindex (k : ℤ) : ParityComplex C ⥤ ParityComplex C :=
  Functor.pi fun _ ↦ (ComplexShape.embeddingUp'Add (1 : ℤ) k).restrictionFunctor C

variable {C}

@[simp]
theorem reindex_obj_apply (k : ℤ) (X : ParityComplex C) (τ : ZMod 2) :
    (reindex C k).obj X τ =
      ((ComplexShape.embeddingUp'Add (1 : ℤ) k).restrictionFunctor C).obj (X τ) := (rfl)

@[simp]
theorem reindex_map_apply (k : ℤ) {X Y : ParityComplex C} (f : X ⟶ Y) (τ : ZMod 2) :
    (reindex C k).map f τ =
      ((ComplexShape.embeddingUp'Add (1 : ℤ) k).restrictionFunctor C).map (f τ) := (rfl)

/-- The raw reindexing keeps independent parities: the term of degree `q` and parity `σ` of the
reindexing by `k` is the term of degree `q + k` and parity `σ + k`. -/
theorem term_reindex (k : ℤ) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((reindex C k).obj X).term q σ = X.term (q + k) (σ + k) := by
  rw [term, term, reindex_obj_apply, Int.cast_add, add_sub_add_right_eq_sub]
  -- Mathlib's restriction uses the shape `up' 1` whereas the parts use `up ℤ`, so the simp lemmas
  -- of `restrictionFunctor` and `restriction` do not fire; the terms of the restriction along
  -- `i ↦ i + k` are the terms of degree `q + k` by definition.
  rfl

/-- The raw reindexing keeps the differential: the differential of the reindexing by `k` from
degree `q` and parity `σ` is the differential of `X` from degree `q + k` and parity `σ + k`. -/
theorem d_reindex (k : ℤ) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((reindex C k).obj X).d q σ =
      eqToHom (term_reindex k X q σ) ≫ X.d (q + k) (σ + k) ≫
        eqToHom (by rw [term_reindex, add_right_comm q, add_right_comm σ]) := by
  rw [d_def, X.d_eq (τ := σ - q) (by push_cast; ring) (add_right_comm q k 1)]
  simp only [termIso, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  -- The remaining sides agree since the differentials of the restriction along `i ↦ i + k`
  -- are those of degree `q + k` by definition.
  rfl

/-- The raw reindexing keeps the components of even chain maps: the component of the reindexing
of `f` by `k` in degree `q` and parity `σ` is the component of `f` in degree `q + k` and parity
`σ + k`. -/
theorem termMap_reindex (k : ℤ) {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ) (σ : ZMod 2) :
    termMap ((reindex C k).map f) q σ =
      eqToHom (term_reindex k X q σ) ≫ termMap f (q + k) (σ + k) ≫
        eqToHom (term_reindex k Y q σ).symm := by
  rw [termMap_def, termMap_eq f (by push_cast; ring : σ + k - ((q + k : ℤ) : ZMod 2) = σ - q)]
  simp only [termIso, eqToIso.hom, eqToIso.inv, reindex_map_apply, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  -- The remaining sides agree since the components of the restriction along `i ↦ i + k`
  -- are those of degree `q + k` by definition.
  rfl

end General

section Shift

variable (C : Type*) [Category* C] [Preadditive C]

/-- The **native shift** by `k : ℤ`: the term of degree `q` and parity `σ` is the old term of
degree `q + k` and parity `σ`, and the differential is multiplied by `(-1)^k`, as for Mathlib's
shift of cochain complexes. The part of independent parity `τ` is the shift of the part of
independent parity `τ + k`; note that `-k = k` in `ZMod 2`. The functor body is exposed so that
the parts of the shift reduce to shifts of parts. -/
@[expose]
def shift (k : ℤ) : ParityComplex C ⥤ ParityComplex C :=
  parityShift C k ⋙ Functor.pi fun _ ↦ CategoryTheory.shiftFunctor (CochainComplex C ℤ) k

variable {C}

@[simp]
theorem shift_obj_apply (k : ℤ) (X : ParityComplex C) (τ : ZMod 2) :
    (shift C k).obj X τ = (X (τ + k))⟦k⟧ := (rfl)

@[simp]
theorem shift_map_apply (k : ℤ) {X Y : ParityComplex C} (f : X ⟶ Y) (τ : ZMod 2) :
    (shift C k).map f τ = (f (τ + k))⟦k⟧' := (rfl)

/-- The native shift keeps parities: the term of degree `q` and parity `σ` of the shift by `k` is
the term of degree `q + k` and parity `σ`. -/
theorem term_shift (k : ℤ) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((shift C k).obj X).term q σ = X.term (q + k) σ := by
  rw [term, term, shift_obj_apply, CochainComplex.shiftFunctor_obj_X', Int.cast_add,
    CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_assoc]

/-- The native shift by `k` multiplies the differential by `(-1)^k`: the differential of the shift
from degree `q` and parity `σ` is `(-1)^k` times the differential of `X` from degree `q + k` and
parity `σ`. -/
theorem d_shift (k : ℤ) (X : ParityComplex C) (q : ℤ) (σ : ZMod 2) :
    ((shift C k).obj X).d q σ =
      k.negOnePow • (eqToHom (term_shift k X q σ) ≫ X.d (q + k) σ ≫
        eqToHom (by rw [term_shift, add_right_comm])) := by
  rw [d_def, X.d_eq (τ := σ - q + k) (by push_cast; rw [← sub_sub, CharTwo.sub_eq_add (σ - q)])
    (add_right_comm q k 1)]
  -- The differential of the shift of a cochain complex is the signed differential
  -- (`CochainComplex.shiftFunctor_obj_d'`, true by `rfl`), here read on the part `X (σ - q + k)`.
  -- It cannot be rewritten in: the part `(shift C k).obj X (σ - q)` occurs in the types of the
  -- surrounding `eqToHom` casts, so `rw [shift_obj_apply]` fails (motive is not type correct),
  -- and a restated `rw [show ... from CochainComplex.shiftFunctor_obj_d' ..]` leaves the sign on
  -- a morphism between the unreduced terms, where neither `Linear.comp_smul` nor
  -- `Preadditive.comp_zsmul` matches. `change` restates the whole composite between the reduced
  -- terms instead.
  simp only [termIso, eqToIso.hom, eqToIso.inv]
  change eqToHom _ ≫ (k.negOnePow • (X (σ - q + k)).d (q + k) (q + 1 + k)) ≫ eqToHom _ = _
  simp only [Units.smul_def, Linear.smul_comp, Linear.comp_smul, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- The native shift keeps the components of even chain maps: the component of the shift of `f`
by `k` in degree `q` and parity `σ` is the component of `f` in degree `q + k` and parity `σ`. -/
theorem termMap_shift (k : ℤ) {X Y : ParityComplex C} (f : X ⟶ Y) (q : ℤ) (σ : ZMod 2) :
    termMap ((shift C k).map f) q σ =
      eqToHom (term_shift k X q σ) ≫ termMap f (q + k) σ ≫ eqToHom (term_shift k Y q σ).symm := by
  rw [termMap_def,
    termMap_eq f (τ := σ - q + k) (by push_cast; rw [← sub_sub, CharTwo.sub_eq_add (σ - q)])]
  simp only [termIso, eqToIso.hom, eqToIso.inv, shift_map_apply, CochainComplex.shiftFunctor_map_f',
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  -- The remaining sides agree since the components of the shift by `k` are those of degree
  -- `q + k` by definition.
  rfl

variable (C) in
/-- **Raw reindexing and the native shift.** Reindexing by `k : ℤ` after the parity change
`Π^k` is the native shift by `k`, through multiplication by `(-1)^(q k)` in degree `q`
(`CochainComplex.restrictionAddIsoShift`). -/
noncomputable def parityShiftCompReindexIsoShift (k : ℤ) :
    parityShift C k ⋙ reindex C k ≅ shift C k :=
  Functor.isoWhiskerLeft (parityShift C k)
    (NatIso.pi fun _ ↦ CochainComplex.restrictionAddIsoShift C k)

/-- In degree `q`, the comparison between raw reindexing and the native shift is multiplication
by `(-1)^(q k)`. -/
@[simp]
theorem parityShiftCompReindexIsoShift_hom_app_apply_f (k : ℤ) (X : ParityComplex C) (τ : ZMod 2)
    (q : ℤ) :
    (((parityShiftCompReindexIsoShift C k).hom.app X) τ).f q =
      (q * k).negOnePow • 𝟙 ((X (τ + k)).X (q + k)) :=
  CochainComplex.restrictionAddIsoShift_hom_app_f C k (X (τ + k)) q

/-- The inverse comparison between raw reindexing and the native shift has the same degreewise
sign `(-1)^(q k)`. -/
@[simp]
theorem parityShiftCompReindexIsoShift_inv_app_apply_f (k : ℤ) (X : ParityComplex C) (τ : ZMod 2)
    (q : ℤ) :
    (((parityShiftCompReindexIsoShift C k).inv.app X) τ).f q =
      (q * k).negOnePow • 𝟙 ((X (τ + k)).X (q + k)) :=
  CochainComplex.restrictionAddIsoShift_inv_app_f C k (X (τ + k)) q

end Shift

end ParityComplex

end TauCeti
