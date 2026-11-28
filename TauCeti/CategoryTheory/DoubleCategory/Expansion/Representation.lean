/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Expansion.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Representations in an expanded double category

In the expansion of a strict double category, a path is represented by its composite in the
original edge category. The binary and nullary comparison cells are the original identity
cells, transported along path evaluation. Evaluation of horizontal globular cells is fully
faithful, so equal evaluated boundaries supply canonical comparison isomorphisms. Transposition
provides the vertical construction, giving chosen representations in both directions.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Definition 3.12.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory DoubleCategoryStruct

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O H V)

/-- Evaluate horizontal paths and their globular cells in the original double category.
The cell itself is unchanged. Its body is exposed so that evaluated boundary objects compute
in the types of cell formulas. -/
@[expose]
def expandHorizontalEval (a b : O) :
    D.expand.HorizontalGlobular a b ⥤ D.HorizontalGlobular a b where
  obj p := ⟨@composePath O H _ _ p.edge⟩
  map α := ⟨α.cell⟩
  map_id p := by rfl
  map_comp α β := by
    ext
    rw [HorizontalGlobular.comp_cell]
    -- Evaluation is semireducible, so transport must unfold it when matching cell types.
    erw [D.expand_cast]
    rw [D.expand_vComp]
    simp only [Cell.cast_cast]
    rfl

@[simp]
theorem expandHorizontalEval_obj_edge {a b : O} (p : D.expand.HorizontalGlobular a b) :
    ((D.expandHorizontalEval a b).obj p).edge = @composePath O H _ _ p.edge :=
  (rfl)

@[simp]
theorem expandHorizontalEval_map_cell {a b : O} {p q : D.expand.HorizontalGlobular a b}
    (α : p ⟶ q) : ((D.expandHorizontalEval a b).map α).cell = α.cell :=
  (rfl)

/-- Evaluation changes only the boundary indexing, and induces bijections on globular cells. -/
def fullyFaithfulExpandHorizontalEval (a b : O) :
    (D.expandHorizontalEval a b).FullyFaithful where
  preimage α := ⟨α.cell⟩

instance (a b : O) : (D.expandHorizontalEval a b).Full :=
  (D.fullyFaithfulExpandHorizontalEval a b).full

instance (a b : O) : (D.expandHorizontalEval a b).Faithful :=
  (D.fullyFaithfulExpandHorizontalEval a b).faithful

/-- Paths with the same composite are canonically isomorphic in the expanded horizontal
globular category. The isomorphism evaluates to the equality isomorphism of their composites. -/
def expandHorizontalIso {a b : O} {p q : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q) : D.expand.HorizontalIso p q :=
  (D.fullyFaithfulExpandHorizontalEval a b).preimageIso
    (eqToIso (congrArg HorizontalGlobular.mk hpq))

@[simp]
theorem expandHorizontalIso_hom_cell {a b : O}
    {p q : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q) :
    (D.expandHorizontalIso hpq).hom.cell =
      (D.vId (@composePath O H _ _ p)).cast rfl hpq rfl rfl := by
  dsimp only [expandHorizontalIso, Functor.FullyFaithful.preimageIso,
    fullyFaithfulExpandHorizontalEval]
  dsimp only [expandHorizontalEval, eqToIso]
  rw [HorizontalGlobular.eqToHom_cell]

@[simp]
theorem expandHorizontalIso_inv_cell {a b : O}
    {p q : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q) :
    (D.expandHorizontalIso hpq).inv.cell =
      (D.vId (@composePath O H _ _ q)).cast rfl hpq.symm rfl rfl := by
  dsimp only [expandHorizontalIso, Functor.FullyFaithful.preimageIso,
    fullyFaithfulExpandHorizontalEval]
  dsimp only [expandHorizontalEval, eqToIso]
  rw [HorizontalGlobular.eqToHom_cell]

/-- Evaluation sends a canonical path comparison to the equality isomorphism of composites. -/
@[simp]
theorem expandHorizontalEval_mapIso {a b : O}
    {p q : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q) :
    (D.expandHorizontalEval a b).mapIso (D.expandHorizontalIso hpq) =
      eqToIso (congrArg HorizontalGlobular.mk hpq) := by
  ext
  rfl

@[simp]
theorem expandHorizontalIso_refl {a b : O} (p : Edge (pathCategory O H.toQuiver) a b) :
    D.expandHorizontalIso (p := p) rfl = Iso.refl _ := by
  apply (D.expandHorizontalEval a b).mapIso_injective
  simp only [expandHorizontalEval_mapIso, Functor.mapIso_refl, eqToIso_refl]
  rfl

@[simp]
theorem expandHorizontalIso_symm {a b : O}
    {p q : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q) :
    (D.expandHorizontalIso hpq).symm = D.expandHorizontalIso hpq.symm := by
  apply (D.expandHorizontalEval a b).mapIso_injective
  simp only [Functor.mapIso_symm, expandHorizontalEval_mapIso]
  rfl

/-- Canonical comparisons compose along equality of evaluated boundaries. -/
@[simp]
theorem expandHorizontalIso_trans {a b : O}
    {p q r : Edge (pathCategory O H.toQuiver) a b}
    (hpq : @composePath O H _ _ p = @composePath O H _ _ q)
    (hqr : @composePath O H _ _ q = @composePath O H _ _ r) :
    D.expandHorizontalIso hpq ≪≫ D.expandHorizontalIso hqr =
      D.expandHorizontalIso (hpq.trans hqr) := by
  apply (D.expandHorizontalEval a b).mapIso_injective
  simp only [Functor.mapIso_trans, expandHorizontalEval_mapIso]
  dsimp only [expandHorizontalEval]
  rw [eqToIso_trans]

/-- The horizontal generators in an expansion compose and have identities as in the original
edge category. The comparison cells evaluate to identity globular cells. Its body is exposed
so that the chosen generators compute in the types of the comparison formulas. -/
@[expose]
def expandHorizontalRepresentation : D.expand.HorizontalRepresentation where
  unit a := edgeId H a
  mul f g := edgeComp H f g
  unitIso a := D.expandHorizontalIso (by simp)
  mulIso f g := D.expandHorizontalIso (by simp [edgeComp])

@[simp]
theorem expandHorizontalRepresentation_unit (a : O) :
    D.expandHorizontalRepresentation.unit a = edgeId H a :=
  (rfl)

@[simp]
theorem expandHorizontalRepresentation_mul {a b c : O} (f : Edge H a b) (g : Edge H b c) :
    D.expandHorizontalRepresentation.mul f g = edgeComp H f g :=
  (rfl)

/-- Folding a path after an initial generator is composition with its evaluated composite. -/
@[simp]
theorem expandHorizontalRepresentation_foldRep {a b c : O} (f : Edge H a b)
    (p : Edge (pathCategory O H.toQuiver) b c) :
    D.expandHorizontalRepresentation.foldRep f p = edgeComp H f (@composePath O H _ _ p) := by
  induction p with
  | nil => exact (Category.comp_id (self := H) f).symm
  | cons p g ih =>
    simp only [HorizontalRepresentation.foldRep_cons, expandHorizontalRepresentation_mul, ih,
      composePath_cons, edgeComp, Category.assoc (self := H)]

/-- Recursive path representation in the expansion is the original path evaluation. -/
@[simp]
theorem expandHorizontalRepresentation_rep {a b : O}
    (p : Edge (pathCategory O H.toQuiver) a b) :
    D.expandHorizontalRepresentation.rep p = @composePath O H _ _ p := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    cases p with
    | nil => simp only [HorizontalRepresentation.rep_cons_nil, composePath_cons,
        composePath_nil, Category.id_comp (self := H)]
    | cons p g =>
      simp only [HorizontalRepresentation.rep_cons_cons, expandHorizontalRepresentation_mul,
        ih, composePath_cons, edgeComp]

/-- The nullary comparison is the canonical comparison between the empty path and the
singleton containing the original identity arrow. -/
theorem expandHorizontalRepresentation_unitIso (a : O) :
    D.expandHorizontalRepresentation.unitIso a = D.expandHorizontalIso
      (p := @Quiver.Path.nil O H.toQuiver a)
      (q := @Quiver.Hom.toPath O H.toQuiver a a (edgeId H a)) (by simp) :=
  (rfl)

/-- The binary comparison is the canonical comparison between a two-arrow path and the
singleton containing its original composite. -/
theorem expandHorizontalRepresentation_mulIso {a b c : O} (f : Edge H a b) (g : Edge H b c) :
    D.expandHorizontalRepresentation.mulIso f g = D.expandHorizontalIso
      (p := edgeComp (pathCategory O H.toQuiver) (@Quiver.Hom.toPath O H.toQuiver a b f)
        (@Quiver.Hom.toPath O H.toQuiver b c g))
      (q := @Quiver.Hom.toPath O H.toQuiver a c (edgeComp H f g)) (by simp [edgeComp]) :=
  (rfl)

/-- The representation of an expansion uses the original composition and identity arrows
in each direction. -/
def expandRepresentation : D.expand.Representation where
  horizontal := D.expandHorizontalRepresentation
  vertical := D.expand_transpose ▸ D.transpose.expandHorizontalRepresentation

/-- Every path boundary of an expanded double category is represented by a generator. -/
theorem expand_representable : D.expand.Representable :=
  D.expand.representable_of_representation D.expandRepresentation

@[simp]
theorem expandRepresentation_horizontal :
    D.expandRepresentation.horizontal = D.expandHorizontalRepresentation :=
  (rfl)

/-- The vertical representation is the horizontal representation of the transposed original
category, transported through commutation of expansion and transposition. -/
theorem expandRepresentation_vertical :
    D.expandRepresentation.vertical =
      D.expand_transpose ▸ D.transpose.expandHorizontalRepresentation :=
  (rfl)

@[simp]
theorem expandRepresentation_vertical_unit (a : O) :
    D.expandRepresentation.vertical.unit a = edgeId V a :=
  (rfl)

@[simp]
theorem expandRepresentation_vertical_mul {a b c : O} (f : Edge V a b) (g : Edge V b c) :
    D.expandRepresentation.vertical.mul f g = edgeComp V f g :=
  (rfl)

end TauCeti.StrictDoubleCategory
