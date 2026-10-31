/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Twisted.Triangle

/-!
# The homotopy category of twisted objects is pretriangulated

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects of the additive closure of the shift closure of `C`, with the shift of
`TauCeti/CategoryTheory/DG/Twisted/HomotopyShift.lean` and the cone triangles
`P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of `TauCeti/CategoryTheory/DG/Twisted/Triangle.lean` as distinguished
triangles.  That file proves every axiom of a pretriangulated category except the converse half of
the rotation axiom.  This file proves it, by showing that the inverse rotation of a cone triangle
is isomorphic to a cone triangle, and so makes `H⁰` a pretriangulated category in the sense of
Mathlib (`CategoryTheory.Pretriangulated`).

The inverse rotation of the cone triangle of a closed degree-zero morphism `u : P ⟶ Q` is
`(cone u)⟦-1⟧ ⟶ P ⟶ Q ⟶ (cone u)⟦-1⟧⟦1⟧`, whose first morphism is minus the shift of the projection
`cone u ⟶ P⟦1⟧` followed by `P⟦1⟧⟦-1⟧ ≅ P`, and whose last morphism is the inclusion
`Q ⟶ cone u` followed by `cone u ≅ (cone u)⟦-1⟧⟦1⟧`.  The isomorphisms `P⟦1⟧⟦-1⟧ ≅ P` and
`cone u ≅ (cone u)⟦-1⟧⟦1⟧` of the shift of `H⁰` are the classes of closed degree-zero morphisms
built from the comparison morphisms `TauCeti.DGTwistedObject.fromShift` and
`TauCeti.DGTwistedObject.toShift` (`TauCeti.DGTwistedObject.shiftShiftNeg_hom_of` and
`TauCeti.DGTwistedObject.shiftNegShift_inv_of` in
`TauCeti/CategoryTheory/DG/Twisted/HomotopyShift.lean`).

Write `α : (cone u)⟦-1⟧ ⟶ P` for a closed representative of the first morphism
(`TauCeti.DGTwistedObject.coneInvRotateMorphism`).  As a graded object,
`cone α = P ⊕ (cone u)⟦-1⟧⟦1⟧ ≅ P ⊕ Q ⊕ P⟦1⟧`, and its twisting matrix pairs the summands `P` and
`P⟦1⟧` through the comparison morphism `P⟦1⟧ ⟶ P`.  Contracting this pair leaves `Q`:

* `Q ⟶ cone α` (`TauCeti.DGTwistedObject.coneInvRotateHom`) is the inclusion of `Q` into `cone u`,
  followed by `cone u ≅ (cone u)⟦-1⟧⟦1⟧` and the inclusion into `cone α`;
* `cone α ⟶ Q` (`TauCeti.DGTwistedObject.coneInvRotateInv`) is the projection onto
  `(cone u)⟦-1⟧⟦1⟧`, followed by `(cone u)⟦-1⟧⟦1⟧ ≅ cone u` and the projection onto `Q`, plus the
  projection onto `P` followed by `u`; the second term corrects the projection `cone u ⟶ Q`, which
  is not closed.

The composite `Q ⟶ cone α ⟶ Q` is the identity, and `cone α ⟶ Q ⟶ cone α` is homotopic to the
identity through the projection onto `P`, followed by the comparison morphism `P ⟶ P⟦1⟧`, the
inclusion of `P⟦1⟧` into `cone u` and the map `cone u ⟶ cone α` above.  The same homotopy without
the projection onto `P` shows that `u` followed by `Q ⟶ cone α` is homotopic to the inclusion of
`P` into `cone α`, which is the second square of the isomorphism of triangles.

## Main definitions

* `TauCeti.DGTwistedObject.coneInvRotateMorphism`: the closed morphism `(cone u)⟦-1⟧ ⟶ P`
  representing the first morphism of the inverse rotation of the cone triangle of `u`.
* `TauCeti.DGTwistedObject.coneInvRotateIso` and `TauCeti.DGTwistedObject.coneTriangleInvRotateIso`:
  the isomorphism `Q ≅ cone α` in `H⁰` and the induced isomorphism between the inverse rotation of
  the cone triangle of `u` and the cone triangle of `α`.
* `TauCeti.DGTwistedObject.pretriangulatedHomotopyCategory`: `H⁰` is pretriangulated.

## Main results

* `TauCeti.DGTwistedObject.invRotate_mem_distinguishedTriangles`: the inverse rotation of a
  distinguished triangle is distinguished.
* `TauCeti.DGTwistedObject.rotate_distinguished_triangle`: a triangle is distinguished exactly
  when its rotation is.
* `TauCeti.DGTwistedObject.coneTriangle_distinguished`: cone triangles are distinguished triangles
  of the pretriangulated category `H⁰`.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace TauCeti

universe v u

namespace DGTwistedObject

open DGHomotopyCategory

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The inverse rotation of a cone triangle -/

section invRotate

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
  {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)

/-- The closed degree-zero morphism `(cone u)⟦-1⟧ ⟶ P` representing the first morphism of the
inverse rotation of the cone triangle of `u`: minus the shift by `-1` of the projection
`cone u ⟶ P⟦1⟧`, followed by `P⟦1⟧⟦-1⟧ ⟶ P`. -/
noncomputable def coneInvRotateMorphism :
    DGHom R 0 ((shiftFunctor R (-1)).obj (cone u hu)) P :=
  -dgComp R ((shiftFunctor R (-1)).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
    (shiftShiftNegHom R P) (add_zero 0)

theorem coneInvRotateMorphism_def :
    coneInvRotateMorphism hu =
      -dgComp R ((shiftFunctor R (-1)).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
        (shiftShiftNegHom R P) (add_zero 0) :=
  (rfl)

/-- The morphism `(cone u)⟦-1⟧ ⟶ P` is closed. -/
theorem dgDifferential_coneInvRotateMorphism :
    dgDifferential R 0 (coneInvRotateMorphism hu) = 0 := by
  rw [coneInvRotateMorphism_def, map_neg, dgDifferential_dgComp,
    ← EnrichedFunctor.dgMap_dgDifferential, dgDifferential_extensionSnd,
    dgDifferential_shiftShiftNegHom, map_zero, zero_dgComp, dgComp_zero, smul_zero, add_zero,
    neg_zero]

/-- The degree-one morphism `(cone u)⟦-1⟧⟦1⟧ ⟶ P` underlying `(cone u)⟦-1⟧ ⟶ P` is minus
`(cone u)⟦-1⟧⟦1⟧ ⟶ cone u`, followed by the projection onto `P⟦1⟧` and the comparison morphism
`P⟦1⟧ ⟶ P`: by the Koszul-sign naturality of the comparison morphisms, the shift by `-1` of the
degree-one morphism `cone u ⟶ P` acquires the sign `(-1)^((-1) * 1)`. -/
theorem coneMorphism_coneInvRotateMorphism :
    coneMorphism R (coneInvRotateMorphism hu) =
      -dgComp R (shiftNegShiftHom R (cone u hu))
        (dgComp R (extensionSnd R (dgDifferential_coneMorphism hu)) (fromShift P 1) (zero_add 1))
        (zero_add 1) := by
  rw [coneMorphism_def, coneInvRotateMorphism_def, dgComp_neg, shiftShiftNegHom_def,
    ← dgComp_assoc R (p := 0) (q := 1) (r := -1) _ _ _ (zero_add 1) (add_neg_cancel 1)
      (by omega),
    ← EnrichedFunctor.dgMap_dgComp, dgComp_fromShift (-1) _ (by omega), shiftNegShiftHom_def,
    neg_dgComp, neg_neg, dgComp_units_smul, mul_one, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, neg_neg, dgComp_assoc]
  omega

/-- `TauCeti.DGTwistedObject.coneMorphism_coneInvRotateMorphism`, followed by `k`; unlike that
lemma, this rewrites the degree-one morphism only where it is composed, not where it is the twist
of `cone α`. -/
private theorem dgComp_coneMorphism_coneInvRotateMorphism
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {q n : ℤ} (k : DGHom R q P Z)
    (h : 1 + q = n) :
    dgComp R (coneMorphism R (coneInvRotateMorphism hu)) k h =
      -dgComp R (shiftNegShiftHom R (cone u hu))
        (dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R (fromShift P 1) k h) (zero_add n)) (zero_add n) := by
  rw [coneMorphism_coneInvRotateMorphism, neg_dgComp, dgComp_assoc, dgComp_assoc]
  all_goals omega

/-- `cone u ⟶ (cone u)⟦-1⟧⟦1⟧`, followed by the degree-one morphism `(cone u)⟦-1⟧⟦1⟧ ⟶ P`, is minus
the projection onto `P⟦1⟧` followed by the comparison morphism `P⟦1⟧ ⟶ P`. -/
private theorem dgComp_shiftNegShiftInv_coneMorphism_coneInvRotateMorphism :
    dgComp R (shiftNegShiftInv R (cone u hu)) (coneMorphism R (coneInvRotateMorphism hu))
        (zero_add 1) =
      -dgComp R (extensionSnd R (dgDifferential_coneMorphism hu)) (fromShift P 1) (zero_add 1) := by
  rw [coneMorphism_coneInvRotateMorphism, dgComp_neg, ← dgComp_assoc R _ _ _ (add_zero 0)
    (zero_add 1) (by omega), dgComp_shiftNegShiftInv_shiftNegShiftHom, dgId_dgComp]

/-- The comparison morphism `Q ⟶ cone α` from the third object of the inverse rotation of the cone
triangle of `u` to the cone of `α = TauCeti.DGTwistedObject.coneInvRotateMorphism`: the inclusion
of `Q` into `cone u`, followed by `cone u ⟶ (cone u)⟦-1⟧⟦1⟧` and the inclusion of
`(cone u)⟦-1⟧⟦1⟧` into `cone α`.  It is a homotopy equivalence with inverse
`TauCeti.DGTwistedObject.coneInvRotateInv`. -/
noncomputable def coneInvRotateHom :
    DGHom R 0 Q (cone (coneInvRotateMorphism hu) (dgDifferential_coneInvRotateMorphism hu)) :=
  dgComp R (extensionInl R (dgDifferential_coneMorphism hu))
    (dgComp R (shiftNegShiftInv R (cone u hu))
      (extensionInr R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
      (add_zero 0)) (add_zero 0)

/-- The comparison morphism `cone α ⟶ Q`: the projection onto `(cone u)⟦-1⟧⟦1⟧`, followed by
`(cone u)⟦-1⟧⟦1⟧ ⟶ cone u` and the projection onto `Q`, plus the projection onto `P` followed by
`u`. -/
noncomputable def coneInvRotateInv :
    DGHom R 0 (cone (coneInvRotateMorphism hu) (dgDifferential_coneInvRotateMorphism hu)) Q :=
  dgComp R (extensionSnd R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
      (dgComp R (shiftNegShiftHom R (cone u hu)) (extensionFst R (dgDifferential_coneMorphism hu))
        (add_zero 0)) (add_zero 0) +
    dgComp R
      (extensionFst R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu))) u
      (add_zero 0)

theorem coneInvRotateHom_def :
    coneInvRotateHom hu =
      dgComp R (extensionInl R (dgDifferential_coneMorphism hu))
        (dgComp R (shiftNegShiftInv R (cone u hu))
          (extensionInr R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
          (add_zero 0)) (add_zero 0) :=
  (rfl)

theorem coneInvRotateInv_def :
    coneInvRotateInv hu =
      dgComp R
          (extensionSnd R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
          (dgComp R (shiftNegShiftHom R (cone u hu))
            (extensionFst R (dgDifferential_coneMorphism hu)) (add_zero 0)) (add_zero 0) +
        dgComp R
          (extensionFst R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
          u (add_zero 0) :=
  (rfl)

/-- The comparison morphism `Q ⟶ cone α` is closed. -/
theorem dgDifferential_coneInvRotateHom : dgDifferential R 0 (coneInvRotateHom hu) = 0 := by
  rw [coneInvRotateHom_def, dgDifferential_dgComp, dgDifferential_dgComp]
  simp -proj only [dgDifferential_extensionInl, dgDifferential_shiftNegShiftInv,
    dgDifferential_extensionInr, zero_dgComp, zero_add, Int.negOnePow_zero, one_smul]
  rw [← dgComp_assoc R (shiftNegShiftInv R (cone u hu)) _ _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_shiftNegShiftInv_coneMorphism_coneInvRotateMorphism, neg_dgComp, dgComp_neg,
    dgComp_assoc R _ (fromShift P 1) _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_extensionInl_extensionSnd_assoc, neg_zero]

/-- The comparison morphism `cone α ⟶ Q` is closed: the differential of the projection
`cone u ⟶ Q` is cancelled by that of the projection `cone α ⟶ P` followed by `u`. -/
theorem dgDifferential_coneInvRotateInv : dgDifferential R 0 (coneInvRotateInv hu) = 0 := by
  rw [coneInvRotateInv_def, map_add, dgDifferential_dgComp, dgDifferential_dgComp,
    dgDifferential_dgComp]
  simp -proj only [dgDifferential_extensionSnd, dgDifferential_shiftNegShiftHom,
    dgDifferential_extensionFst, hu, zero_dgComp, dgComp_zero, zero_add, add_zero, smul_zero,
    Int.negOnePow_zero, one_smul, dgComp_neg, coneMorphism_coneInvRotateMorphism, neg_neg]
  rw [dgComp_assoc, dgComp_assoc, dgComp_assoc, ← coneMorphism_def, neg_add_cancel]
  all_goals omega

/-- The comparison morphism `Q ⟶ cone α` followed by its inverse `cone α ⟶ Q` is the
identity. -/
@[simp↓]
theorem dgComp_coneInvRotateHom_coneInvRotateInv :
    dgComp R (coneInvRotateHom hu) (coneInvRotateInv hu) (add_zero 0) = dgId R Q := by
  simp only [coneInvRotateHom_def, coneInvRotateInv_def, dgComp_add,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInr_extensionSnd_assoc, dgComp_extensionInr_extensionFst_assoc,
    dgComp_shiftNegShiftInv_shiftNegShiftHom_assoc, add_zero,
    dgComp_extensionInl_extensionFst]

/-- The comparison morphism `P ⟶ P⟦1⟧`, followed by the inclusion of `P⟦1⟧` into `cone u` and by
`cone u ⟶ cone α`: this degree `-1` morphism is a homotopy from `u` followed by `Q ⟶ cone α` to
the inclusion of `P` into `cone α`. -/
private theorem dgDifferential_toShift_dgComp_coneInvRotateHom :
    dgDifferential R (-1)
        (dgComp R (toShift P 1) (dgComp R (extensionInr R (dgDifferential_coneMorphism hu))
          (dgComp R (shiftNegShiftInv R (cone u hu))
            (extensionInr R (dgDifferential_coneMorphism
              (dgDifferential_coneInvRotateMorphism hu))) (add_zero 0)) (add_zero 0))
          (add_zero (-1))) =
      extensionInl R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)) -
        dgComp R u (coneInvRotateHom hu) (add_zero 0) := by
  rw [dgDifferential_dgComp, dgDifferential_dgComp, dgDifferential_dgComp]
  simp -proj only [dgDifferential_toShift, dgDifferential_shiftNegShiftInv,
    dgDifferential_extensionInr, zero_dgComp, zero_add, Int.negOnePow_zero, one_smul,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, dgComp_add]
  rw [← dgComp_assoc R (shiftNegShiftInv R (cone u hu)) _ _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_shiftNegShiftInv_coneMorphism_coneInvRotateMorphism, neg_dgComp, dgComp_neg,
    dgComp_neg, dgComp_assoc R _ (fromShift P 1) _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_extensionInr_extensionSnd_assoc, dgComp_toShift_fromShift_assoc,
    dgComp_assoc R (coneMorphism R u) _ _ (add_zero 1) (zero_add 0) (by omega),
    dgComp_coneMorphism, dgComp_toShift_fromShift_assoc, coneInvRotateHom_def]
  abel

/-- The comparison morphism `cone α ⟶ Q` followed by `Q ⟶ cone α` is homotopic to the identity,
through the projection onto `P` followed by the homotopy of
`dgDifferential_toShift_dgComp_coneInvRotateHom`. -/
private theorem dgDifferential_extensionFst_toShift_dgComp :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism
            (dgDifferential_coneInvRotateMorphism hu)))
          (dgComp R (toShift P 1) (dgComp R (extensionInr R (dgDifferential_coneMorphism hu))
            (dgComp R (shiftNegShiftInv R (cone u hu))
              (extensionInr R (dgDifferential_coneMorphism
                (dgDifferential_coneInvRotateMorphism hu))) (add_zero 0)) (add_zero 0))
            (add_zero (-1))) (zero_add (-1))) =
      dgId R _ - dgComp R (coneInvRotateInv hu) (coneInvRotateHom hu) (add_zero 0) := by
  -- The projection onto `cone u⟦-1⟧⟦1⟧` followed by the inclusion is, through `cone u`, the sum
  -- of the two summands of `cone u`.
  have h : dgComp R (extensionSnd R (dgDifferential_coneMorphism
        (dgDifferential_coneInvRotateMorphism hu)))
        (extensionInr R (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)))
        (add_zero 0) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism
        (dgDifferential_coneInvRotateMorphism hu)))
        (dgComp R (shiftNegShiftHom R (cone u hu))
          (dgComp R (dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
              (extensionInl R (dgDifferential_coneMorphism hu)) (add_zero 0) +
            dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
              (extensionInr R (dgDifferential_coneMorphism hu)) (add_zero 0))
            (dgComp R (shiftNegShiftInv R (cone u hu))
              (extensionInr R (dgDifferential_coneMorphism
                (dgDifferential_coneInvRotateMorphism hu))) (add_zero 0)) (add_zero 0))
          (add_zero 0)) (add_zero 0) := by
    rw [dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr, dgId_dgComp,
      dgComp_shiftNegShiftHom_shiftNegShiftInv_assoc]
  rw [dgDifferential_dgComp, dgDifferential_toShift_dgComp_coneInvRotateHom,
    dgDifferential_extensionFst, neg_dgComp, dgComp_assoc R _ _ _ (zero_add 1) (add_neg_cancel 1)
      (by omega), dgComp_coneMorphism_coneInvRotateMorphism, dgComp_fromShift_toShift_assoc,
    ← dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr R
      (dgDifferential_coneMorphism (dgDifferential_coneInvRotateMorphism hu)), h]
  simp only [coneInvRotateInv_def, coneInvRotateHom_def, dgComp_neg, neg_neg, Int.negOnePow_zero,
    one_smul, sub_eq_add_neg, add_dgComp, dgComp_add,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0)]
  abel

/-- **The inverse rotation isomorphism**: in the homotopy category, `Q` is isomorphic to the cone
of `α = TauCeti.DGTwistedObject.coneInvRotateMorphism`, through the comparison morphisms
`TauCeti.DGTwistedObject.coneInvRotateHom` and `TauCeti.DGTwistedObject.coneInvRotateInv`. -/
noncomputable def coneInvRotateIso :
    DGHomotopyCategory.of R Q ≅
      DGHomotopyCategory.of R
        (cone (coneInvRotateMorphism hu) (dgDifferential_coneInvRotateMorphism hu)) where
  hom := homOf R (coneInvRotateHom hu)
    ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateHom hu))
  inv := homOf R (coneInvRotateInv hu)
    ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateInv hu))
  hom_inv_id :=
    homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_coneInvRotateHom_coneInvRotateInv hu)
  inv_hom_id := by
    rw [homOf_comp, ← homOf_dgId, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def]
    exact ⟨-_, by rw [map_neg, dgDifferential_extensionFst_toShift_dgComp, neg_sub]⟩

@[simp]
theorem coneInvRotateIso_hom :
    (coneInvRotateIso hu).hom =
      homOf R (coneInvRotateHom hu) ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateHom hu)) :=
  (rfl)

@[simp]
theorem coneInvRotateIso_inv :
    (coneInvRotateIso hu).inv =
      homOf R (coneInvRotateInv hu) ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateInv hu)) :=
  (rfl)

/-- **The inverse rotation of a cone triangle is a cone triangle**: the inverse rotation
`(cone u)⟦-1⟧ ⟶ P ⟶ Q ⟶ (cone u)⟦-1⟧⟦1⟧` of the cone triangle of `u` is isomorphic to the cone
triangle of `α = TauCeti.DGTwistedObject.coneInvRotateMorphism`, by the identities and the inverse
rotation isomorphism. -/
noncomputable def coneTriangleInvRotateIso :
    (coneTriangle u hu).invRotate ≅
      coneTriangle (coneInvRotateMorphism hu) (dgDifferential_coneInvRotateMorphism hu) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneInvRotateIso hu)
    (by
      have h : (coneTriangle u hu).invRotate.mor₁ =
          homOf R (coneInvRotateMorphism hu)
            ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateMorphism hu)) := by
        -- `Triangle.invRotate` is stated with the unit of `shiftEquiv`, which is
        -- `shiftShiftNeg` by definition, and the objects of the cone triangle are those of `u`
        -- by `rfl`; neither identification is available as a rewrite inside the composite.
        change -((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
            (homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
              ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _))) ≫
            (shiftShiftNeg (DGHomotopyCategory.of R P) (1 : ℤ)).hom) = _
        rw [shiftFunctor_map_homOf, shiftShiftNeg_hom_of]
        exact (congrArg Neg.neg (homOf_comp_eq_homOf_of_dgComp_eq R _ _
          (neg_mem_iff.mp ((mem_dgCycles R).mpr (dgDifferential_coneInvRotateMorphism hu)))
            rfl)).trans (homOf_neg R _ _).symm
      exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))
    (by
      have h : homOf R u ((mem_dgCycles R).mpr hu) ≫ (coneInvRotateIso hu).hom =
          homOf R (extensionInl R (dgDifferential_coneMorphism
              (dgDifferential_coneInvRotateMorphism hu)))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
        rw [coneInvRotateIso_hom, homOf_comp, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def]
        exact ⟨_, by rw [map_neg, dgDifferential_toShift_dgComp_coneInvRotateHom, neg_sub]⟩
      exact h.trans (Category.id_comp _).symm)
    (by
      have h : (coneTriangle u hu).invRotate.mor₃ =
          (coneInvRotateIso hu).hom ≫ homOf R (extensionSnd R (dgDifferential_coneMorphism
              (dgDifferential_coneInvRotateMorphism hu)))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        -- As above: the counit of `shiftEquiv` is `shiftNegShift` by definition.
        change homOf R (extensionInl R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) ≫
          (shiftNegShift (DGHomotopyCategory.of R (cone u hu)) (1 : ℤ)).inv = _
        have hk : dgComp R (extensionInl R (dgDifferential_coneMorphism hu))
            (shiftNegShiftInv R (cone u hu)) (add_zero 0) ∈ dgCycles R _ _ :=
          (mem_dgCycles R).mpr (by
            simp -proj only [dgDifferential_dgComp, dgDifferential_extensionInl,
              dgDifferential_shiftNegShiftInv, zero_dgComp, dgComp_zero, smul_zero, add_zero])
        rw [shiftNegShift_inv_of, coneInvRotateIso_hom]
        refine (homOf_comp_eq_homOf_of_dgComp_eq R _ _ hk rfl).trans
          (homOf_comp_eq_homOf_of_dgComp_eq R _ _ hk ?_).symm
        simp only [coneInvRotateHom_def,
          dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
          dgComp_extensionInr_extensionSnd, dgComp_dgId]
      refine (congrArg (fun f ↦ _ ≫ f) ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans h))

@[simp]
theorem coneTriangleInvRotateIso_hom_hom₁ : (coneTriangleInvRotateIso hu).hom.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleInvRotateIso_hom_hom₂ : (coneTriangleInvRotateIso hu).hom.hom₂ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleInvRotateIso_hom_hom₃ :
    (coneTriangleInvRotateIso hu).hom.hom₃ = (coneInvRotateIso hu).hom :=
  (rfl)

@[simp]
theorem coneTriangleInvRotateIso_inv_hom₁ : (coneTriangleInvRotateIso hu).inv.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleInvRotateIso_inv_hom₂ : (coneTriangleInvRotateIso hu).inv.hom₂ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleInvRotateIso_inv_hom₃ :
    (coneTriangleInvRotateIso hu).inv.hom₃ = (coneInvRotateIso hu).inv :=
  (rfl)

end invRotate

/-! ### The pretriangulated structure -/

section distinguished

/-- **The inverse rotation of a distinguished triangle is distinguished**: the inverse rotation of
a cone triangle is isomorphic to a cone triangle. -/
theorem invRotate_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) : T.invRotate ∈ distinguishedTriangles R C := by
  obtain ⟨P, Q, u, hu, ⟨e⟩⟩ := mem_distinguishedTriangles_iff.mp hT
  exact mem_distinguishedTriangles_iff.mpr
    ⟨_, _, _, _, ⟨(invRotate _).mapIso e ≪≫ coneTriangleInvRotateIso hu⟩⟩

/-- **The rotation axiom**: a triangle is distinguished exactly when its rotation is. -/
theorem rotate_distinguished_triangle
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))) :
    T ∈ distinguishedTriangles R C ↔ T.rotate ∈ distinguishedTriangles R C :=
  ⟨rotate_mem_distinguishedTriangles T, fun hT ↦ isomorphic_distinguished _
    (invRotate_mem_distinguishedTriangles _ hT) _ ((triangleRotation _).unitIso.app T)⟩

/-- **The homotopy category of twisted objects is pretriangulated**, with the triangles isomorphic
to cone triangles as distinguished triangles. -/
noncomputable instance pretriangulatedHomotopyCategory :
    Pretriangulated
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) where
  distinguishedTriangles := distinguishedTriangles R C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

/-- The cone triangle `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of a closed degree-zero morphism is a
distinguished triangle of the pretriangulated homotopy category of twisted objects. -/
theorem coneTriangle_distinguished
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} (u : DGHom R 0 P Q)
    (hu : dgDifferential R 0 u = 0) :
    coneTriangle u hu ∈ distTriang
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  coneTriangle_mem_distinguishedTriangles u hu

end distinguished

end DGTwistedObject

end TauCeti
