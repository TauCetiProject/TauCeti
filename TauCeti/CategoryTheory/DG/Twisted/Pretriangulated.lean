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
triangles.  This file proves the remaining axiom, the converse half of the rotation axiom, and so
makes `H⁰` a pretriangulated category.

The converse rotation follows, as for the homotopy category of cochain complexes, from the
stability of distinguished triangles under the shift functors of the category of triangles: the
inverse rotation of a triangle is isomorphic to the shift by `-1` of its double rotation.  The
shift by `n` of the cone triangle of `u : P ⟶ Q` is the triangle
`P⟦n⟧ ⟶ Q⟦n⟧ ⟶ (cone u)⟦n⟧ ⟶ P⟦n⟧⟦1⟧` whose morphisms are `(-1)^n` times the shifts of those of
the cone triangle, the last one followed by the isomorphism `P⟦1⟧⟦n⟧ ≅ P⟦n⟧⟦1⟧`.  It is
isomorphic to the cone triangle of `u⟦n⟧` by the identity of `P⟦n⟧`, `(-1)^n` times the identity
of `Q⟦n⟧`, and a closed degree-zero isomorphism of twisted objects
`(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` (`TauCeti.DGTwistedObject.shiftConeHom`), which is the shift of the
projection onto `Q` on the summand `Q⟦n⟧`, and `(-1)^n` times the comparison
`P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` of `TauCeti.DGTwistedObject.shiftCommHom` on the summand `P⟦1⟧⟦n⟧`.  It is
closed because the shift by `n` of the twisting entry `P⟦1⟧ ⟶ P ⟶ Q` of `cone u` is `(-1)^n`
times this comparison followed by the twisting entry `P⟦n⟧⟦1⟧ ⟶ P⟦n⟧ ⟶ Q⟦n⟧` of `cone (u⟦n⟧)`
(`TauCeti.DGTwistedObject.dgMap_coneMorphism`).

## Main definitions

* `TauCeti.DGTwistedObject.shiftConeHom` and `TauCeti.DGTwistedObject.shiftConeInv`: the mutually
  inverse closed degree-zero morphisms `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` and
  `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧`.
* `TauCeti.DGTwistedObject.shiftConeIso`: the induced isomorphism `(cone u)⟦n⟧ ≅ cone (u⟦n⟧)` in
  `H⁰`.
* `TauCeti.DGTwistedObject.coneTriangleShiftIso`: the isomorphism between the shift by `n` of the
  cone triangle of `u` and the cone triangle of `u⟦n⟧`.
* `TauCeti.DGTwistedObject.pretriangulated`: the pretriangulated structure on `H⁰`.

## Main results

* `TauCeti.DGTwistedObject.dgMap_coneMorphism`: the shift of the twisting entry of a cone.
* `TauCeti.DGTwistedObject.dgComp_shiftConeHom_shiftConeInv` and
  `TauCeti.DGTwistedObject.dgComp_shiftConeInv_shiftConeHom`: the comparisons of cones are
  inverse.
* `TauCeti.DGTwistedObject.shift_mem_distinguishedTriangles` and
  `TauCeti.DGTwistedObject.invRotate_mem_distinguishedTriangles`: the shift and the inverse
  rotation of a distinguished triangle are distinguished.
* `TauCeti.DGTwistedObject.rotate_mem_distinguishedTriangles_iff`: a triangle is distinguished
  exactly when its rotation is.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, whose isomorphism
  `CochainComplex.mappingCone.shiftTriangleIso` between shifted mapping cone triangles and mapping
  cone triangles of shifted morphisms, and whose deduction of the converse rotation from it, are
  followed here.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace TauCeti

universe v u

namespace DGTwistedObject

open DGHomotopyCategory

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Shifts of cones -/

section shiftCone

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

/-- **The shift of the twisting entry of a cone**: the shift by `n` of the degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q` underlying `u` is `(-1)^n` times the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` followed by
the degree-one morphism `P⟦n⟧⟦1⟧ ⟶ P⟦n⟧ ⟶ Q⟦n⟧` underlying the shift of `u`. -/
theorem dgMap_coneMorphism (u : DGHom R 0 P Q) (n : ℤ) :
    (shiftFunctor R n).dgMap 1 (coneMorphism R u) =
      n.negOnePow • dgComp R (shiftCommHom P 1 n)
        (coneMorphism R ((shiftFunctor R n).dgMap 0 u)) (zero_add 1) := by
  rw [coneMorphism_def, coneMorphism_def, EnrichedFunctor.dgMap_dgComp, dgMap_fromShift,
    one_mul, units_smul_dgComp, dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega)]

variable {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) (n : ℤ)

/-- The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)`: the shift of the projection onto `Q` followed by
the inclusion of `Q⟦n⟧`, plus `(-1)^n` times the shift of the projection onto `P⟦1⟧` followed by
the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` and the inclusion of `P⟦n⟧⟦1⟧`.  It is a closed isomorphism
with inverse `TauCeti.DGTwistedObject.shiftConeInv`. -/
noncomputable def shiftConeHom :
    DGHom R 0 ((shiftFunctor R n).obj (cone u hu))
      (cone ((shiftFunctor R n).dgMap 0 u) ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) :=
  dgComp R ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
      (extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) +
    n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
        (extensionSnd R (dgDifferential_coneMorphism hu)))
      (dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0)) (add_zero 0)

/-- The comparison `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧`: the projection onto `Q⟦n⟧` followed by the shift
of the inclusion of `Q`, plus `(-1)^n` times the projection onto `P⟦n⟧⟦1⟧` followed by the
comparison `P⟦n⟧⟦1⟧ ⟶ P⟦1⟧⟦n⟧` and the shift of the inclusion of `P⟦1⟧`. -/
noncomputable def shiftConeInv :
    DGHom R 0
      (cone ((shiftFunctor R n).dgMap 0 u) ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))
      ((shiftFunctor R n).obj (cone u hu)) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism
      ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
      ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu))) (add_zero 0) +
    n.negOnePow • dgComp R (extensionSnd R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
      (dgComp R (shiftCommHom P n 1)
        ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (add_zero 0)) (add_zero 0)

theorem shiftConeHom_def :
    shiftConeHom hu n =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
          (extensionInl R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) +
        n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
            (extensionSnd R (dgDifferential_coneMorphism hu)))
          (dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0)) (add_zero 0) :=
  (rfl)

theorem shiftConeInv_def :
    shiftConeInv hu n =
      dgComp R (extensionFst R (dgDifferential_coneMorphism
          ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
          ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
          (add_zero 0) +
        n.negOnePow • dgComp R (extensionSnd R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
          (dgComp R (shiftCommHom P n 1)
            ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
            (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The shifts of degree-zero morphisms composing to the identity compose to the identity, in
front of any further morphism `x`. -/
private theorem dgMap_dgComp_dgMap_assoc_of_eq_dgId
    {X Y Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y X} (hfg : dgComp R f g (add_zero 0) = dgId R X) {m : ℤ}
    (x : DGHom R m ((shiftFunctor R n).obj X) Z) :
    dgComp R ((shiftFunctor R n).dgMap 0 f) (dgComp R ((shiftFunctor R n).dgMap 0 g) x
      (zero_add m)) (zero_add m) = x := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add m) (by omega), ← EnrichedFunctor.dgMap_dgComp,
    hfg, EnrichedFunctor.dgMap_dgId, dgId_dgComp]

/-- The shifts of degree-zero morphisms composing to zero compose to zero, in front of any
further morphism `x`. -/
private theorem dgMap_dgComp_dgMap_assoc_of_eq_zero
    {X Y Y' Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Y'} (hfg : dgComp R f g (add_zero 0) = 0) {m : ℤ}
    (x : DGHom R m ((shiftFunctor R n).obj Y') Z) :
    dgComp R ((shiftFunctor R n).dgMap 0 f) (dgComp R ((shiftFunctor R n).dgMap 0 g) x
      (zero_add m)) (zero_add m) = 0 := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add m) (by omega), ← EnrichedFunctor.dgMap_dgComp,
    hfg, map_zero, zero_dgComp]

/-- The shift of the inclusion of `Q` into `cone u` followed by the comparison
`(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is the inclusion of `Q⟦n⟧`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInl_shiftConeHom :
    dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (shiftConeHom hu n) (add_zero 0) =
      extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) := by
  simp only [shiftConeHom_def, dgComp_add, dgComp_units_smul,
    dgMap_dgComp_dgMap_assoc_of_eq_dgId n (dgComp_extensionInl_extensionFst R _),
    dgMap_dgComp_dgMap_assoc_of_eq_zero n (dgComp_extensionInl_extensionSnd R _), smul_zero,
    add_zero]

/-- The shift of the inclusion of `P⟦1⟧` into `cone u` followed by the comparison
`(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is `(-1)^n` times the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` followed by
the inclusion of `P⟦n⟧⟦1⟧`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInr_shiftConeHom :
    dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (shiftConeHom hu n) (add_zero 0) =
      n.negOnePow • dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) := by
  simp only [shiftConeHom_def, dgComp_add, dgComp_units_smul,
    dgMap_dgComp_dgMap_assoc_of_eq_zero n (dgComp_extensionInr_extensionFst R _),
    dgMap_dgComp_dgMap_assoc_of_eq_dgId n (dgComp_extensionInr_extensionSnd R _), zero_add]

/-- The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` followed by the projection onto `P⟦n⟧⟦1⟧` is
`(-1)^n` times the shift of the projection onto `P⟦1⟧` followed by the comparison
`P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧`. -/
@[simp↓]
theorem dgComp_shiftConeHom_extensionSnd :
    dgComp R (shiftConeHom hu n) (extensionSnd R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) =
      n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
        (extensionSnd R (dgDifferential_coneMorphism hu))) (shiftCommHom P 1 n) (add_zero 0) := by
  simp only [shiftConeHom_def, add_dgComp, units_smul_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, dgComp_dgId,
    zero_add]

/-- The inclusion of `Q⟦n⟧` into `cone (u⟦n⟧)` followed by the comparison
`cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is the shift of the inclusion of `Q`. -/
@[simp↓]
theorem dgComp_extensionInl_shiftConeInv :
    dgComp R (extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (shiftConeInv hu n) (add_zero 0) =
      (shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)) := by
  simp only [shiftConeInv_def, dgComp_add, dgComp_units_smul,
    dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc, smul_zero,
    add_zero]

/-- The inclusion of `P⟦n⟧⟦1⟧` into `cone (u⟦n⟧)` followed by the comparison
`cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is `(-1)^n` times the comparison `P⟦n⟧⟦1⟧ ⟶ P⟦1⟧⟦n⟧` followed by the
shift of the inclusion of `P⟦1⟧`. -/
@[simp↓]
theorem dgComp_extensionInr_shiftConeInv :
    dgComp R (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (shiftConeInv hu n) (add_zero 0) =
      n.negOnePow • dgComp R (shiftCommHom P n 1)
        ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (add_zero 0) := by
  simp only [shiftConeInv_def, dgComp_add, dgComp_units_smul,
    dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- Morphisms out of `(cone u)⟦n⟧` are determined by their composites with the shifts of the
inclusions of `Q` and of `P⟦1⟧`. -/
private theorem shiftFunctor_cone_dgHom_ext
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {m : ℤ}
    {f f' : DGHom R m ((shiftFunctor R n).obj (cone u hu)) Z}
    (hl : dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
      f (zero_add m) =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        f' (zero_add m))
    (hr : dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
      f (zero_add m) =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        f' (zero_add m)) :
    f = f' := by
  rw [← dgId_dgComp R f, ← dgId_dgComp R f', ← EnrichedFunctor.dgMap_dgId,
    ← dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr R
      (dgDifferential_coneMorphism hu),
    map_add, EnrichedFunctor.dgMap_dgComp, EnrichedFunctor.dgMap_dgComp, add_dgComp, add_dgComp,
    dgComp_assoc R _ _ f (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add m) (by omega), hl, hr]

/-- The comparisons `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftConeHom_shiftConeInv :
    dgComp R (shiftConeHom hu n) (shiftConeInv hu n) (add_zero 0) = dgId R _ := by
  refine shiftFunctor_cone_dgHom_ext hu n ?_ ?_ <;>
    rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0), dgComp_dgId]
  · rw [dgComp_dgMap_extensionInl_shiftConeHom, dgComp_extensionInl_shiftConeInv]
  · rw [dgComp_dgMap_extensionInr_shiftConeHom, units_smul_dgComp,
      dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInr_shiftConeInv, dgComp_units_smul, smul_smul, Int.units_mul_self,
      one_smul, ← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_shiftCommHom_shiftCommHom, dgId_dgComp]

/-- The comparisons `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftConeInv_shiftConeHom :
    dgComp R (shiftConeInv hu n) (shiftConeHom hu n) (add_zero 0) = dgId R _ := by
  refine extension_dgHom_ext ?_ ?_ <;>
    rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0), dgComp_dgId]
  · rw [dgComp_extensionInl_shiftConeInv, dgComp_dgMap_extensionInl_shiftConeHom]
  · rw [dgComp_extensionInr_shiftConeInv, units_smul_dgComp,
      dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_dgMap_extensionInr_shiftConeHom, dgComp_units_smul, smul_smul, Int.units_mul_self,
      one_smul, ← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_shiftCommHom_shiftCommHom, dgId_dgComp]

/-- **The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is closed.** -/
theorem dgDifferential_shiftConeHom : dgDifferential R 0 (shiftConeHom hu n) = 0 := by
  -- Both terms are the shift of the projection onto `P⟦1⟧`, followed by the comparison
  -- `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧`, the twisting entry of `cone (u⟦n⟧)` and the inclusion of `Q⟦n⟧`,
  -- with opposite signs.
  have hfst : dgDifferential R 0
      ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu))) =
      -(n.negOnePow • dgComp R
        ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
        (dgComp R (shiftCommHom P 1 n) (coneMorphism R ((shiftFunctor R n).dgMap 0 u))
          (zero_add 1)) (zero_add 1)) := by
    rw [← EnrichedFunctor.dgMap_dgDifferential, dgDifferential_extensionFst, map_neg,
      EnrichedFunctor.dgMap_dgComp, dgMap_coneMorphism, dgComp_units_smul]
  have hsnd : dgDifferential R 0
      ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu))) = 0 :=
    (shiftFunctor R n).dgDifferential_dgMap_eq_zero (dgDifferential_extensionSnd R _)
  simp -proj only [shiftConeHom_def, map_add, map_zsmul_unit, dgDifferential_dgComp, hfst, hsnd,
    dgDifferential_extensionInl, dgDifferential_shiftCommHom, dgDifferential_extensionInr,
    zero_dgComp, dgComp_zero, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul]
  rw [neg_dgComp, units_smul_dgComp, dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega), neg_add_cancel]

/-- The comparison `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is closed, as the inverse of a closed
morphism. -/
theorem dgDifferential_shiftConeInv : dgDifferential R 0 (shiftConeInv hu n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_shiftConeHom hu n) (add_zero 0)
    (dgComp_shiftConeHom_shiftConeInv hu n) (dgComp_shiftConeInv_shiftConeHom hu n)

/-- **The shift of a cone is the cone of the shift**: in the homotopy category, `(cone u)⟦n⟧` is
isomorphic to `cone (u⟦n⟧)`, through the comparisons `TauCeti.DGTwistedObject.shiftConeHom` and
`TauCeti.DGTwistedObject.shiftConeInv`. -/
noncomputable def shiftConeIso :
    DGHomotopyCategory.of R ((shiftFunctor R n).obj (cone u hu)) ≅
      DGHomotopyCategory.of R (cone ((shiftFunctor R n).dgMap 0 u)
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) where
  hom := homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n))
  inv := homOf R (shiftConeInv hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeInv hu n))
  hom_inv_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftConeHom_shiftConeInv hu n)
  inv_hom_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftConeInv_shiftConeHom hu n)

@[simp]
theorem shiftConeIso_hom :
    (shiftConeIso hu n).hom =
      homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) :=
  (rfl)

@[simp]
theorem shiftConeIso_inv :
    (shiftConeIso hu n).inv =
      homOf R (shiftConeInv hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeInv hu n)) :=
  (rfl)

/-- **The shift of a cone triangle is a cone triangle**: the shift by `n` of the cone triangle of
`u`, whose morphisms are `(-1)^n` times the shifts of those of the cone triangle, is isomorphic to
the cone triangle of `u⟦n⟧`, by the identity of `P⟦n⟧`, `(-1)^n` times the identity of `Q⟦n⟧`, and
the isomorphism `(cone u)⟦n⟧ ≅ cone (u⟦n⟧)`. -/
noncomputable def coneTriangleShiftIso :
    (Triangle.shiftFunctor _ n).obj (coneTriangle u hu) ≅
      coneTriangle ((shiftFunctor R n).dgMap 0 u)
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu) :=
  -- The squares are first proved for general morphisms of the homotopy category; the objects of
  -- the shifted triangle agree with those of the DG shifts by `rfl`, but cannot be rewritten
  -- inside the implicit objects of the composites.
  Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftConeIso hu n)
    (by
      have key : ∀ {X Y : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {a : X ⟶ Y}
          {b : X⟦n⟧ ⟶ Y⟦n⟧}, a⟦n⟧' = b →
          (n.negOnePow • a⟦n⟧') ≫ (n.negOnePow • 𝟙 (Y⟦n⟧)) = 𝟙 (X⟦n⟧) ≫ b := by
        rintro X Y a b rfl
        simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp, smul_smul,
          Int.units_mul_self, one_smul]
      exact key (shiftFunctor_map_homOf n u _))
    (by
      have key : ∀ {X Y W : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {a : X ⟶ Y}
          {c : Y⟦n⟧ ⟶ W} {b : X⟦n⟧ ⟶ W}, a⟦n⟧' ≫ c = b →
          (n.negOnePow • a⟦n⟧') ≫ c = (n.negOnePow • 𝟙 (X⟦n⟧)) ≫ b := by
        rintro X Y W a c b rfl
        simp only [Linear.units_smul_comp, Category.id_comp]
      have h : (homOf R (extensionInl R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)))⟦n⟧' ≫
          homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) =
          homOf R (extensionInl R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
        simp only [shiftFunctor_map_homOf]
        exact homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (dgComp_dgMap_extensionInl_shiftConeHom hu n)
      exact key h)
    (by
      have key : ∀ {X Y : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {m m' : X ⟶ Y⟦n⟧⟦(1 : ℤ)⟧},
          m = m' → m ≫ (𝟙 (Y⟦n⟧))⟦(1 : ℤ)⟧' = m' := by
        rintro X Y m m' rfl
        simp only [CategoryTheory.Functor.map_id, Category.comp_id]
      have h₀ : n.negOnePow • (homOf R
          ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
          ((shiftFunctor R n).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _))) ≫
          homOf R (shiftCommHom P 1 n) ((mem_dgCycles R).mpr (dgDifferential_shiftCommHom P 1 n))) =
          homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) ≫
            homOf R (extensionSnd R (dgDifferential_coneMorphism
              ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
              ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        simp only [homOf_comp, dgCompZero_def, dgComp_shiftConeHom_extensionSnd]
        exact (homOf_units_smul R _ _ _).symm
      have h : n.negOnePow • ((homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)))⟦n⟧' ≫
          (shiftFunctorComm _ 1 n).hom.app (DGHomotopyCategory.of R P)) =
          homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) ≫
            homOf R (extensionSnd R (dgDifferential_coneMorphism
              ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
              ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        simp only [shiftFunctor_map_homOf, shiftFunctorComm_hom_app_of]
        exact h₀
      exact key h)

end shiftCone

/-! ### The pretriangulated structure -/

section pretriangulated

/-- **The shift of a distinguished triangle is distinguished**: the shift by `n` of a cone triangle
is isomorphic to the cone triangle of the shifted morphism. -/
theorem shift_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles R C := by
  obtain ⟨P, Q, u, hu, ⟨e⟩⟩ := mem_distinguishedTriangles_iff.mp hT
  exact mem_distinguishedTriangles_iff.mpr
    ⟨_, _, _, _, ⟨(Triangle.shiftFunctor _ n).mapIso e ≪≫ coneTriangleShiftIso hu n⟩⟩

/-- **The inverse rotation of a distinguished triangle is distinguished**: it is isomorphic to the
shift by `-1` of the double rotation. -/
theorem invRotate_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) : T.invRotate ∈ distinguishedTriangles R C :=
  isomorphic_distinguished _
    (shift_mem_distinguishedTriangles _
      (rotate_mem_distinguishedTriangles _ (rotate_mem_distinguishedTriangles _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

/-- **The rotation axiom**: a triangle of the homotopy category of twisted objects is
distinguished exactly when its rotation is. -/
theorem rotate_mem_distinguishedTriangles_iff
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))) :
    T ∈ distinguishedTriangles R C ↔ T.rotate ∈ distinguishedTriangles R C :=
  ⟨rotate_mem_distinguishedTriangles T, fun hT ↦ isomorphic_distinguished _
    (invRotate_mem_distinguishedTriangles _ hT) _ ((triangleRotation _).unitIso.app T)⟩

/-- **The homotopy category of twisted objects is pretriangulated**, with the triangles isomorphic
to cone triangles `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` as distinguished triangles.  Since `distTriang _`
unfolds to `TauCeti.DGTwistedObject.distinguishedTriangles`, the lemmas
`TauCeti.DGTwistedObject.mem_distinguishedTriangles_iff` and
`TauCeti.DGTwistedObject.coneTriangle_mem_distinguishedTriangles` describe its distinguished
triangles. -/
noncomputable instance pretriangulated :
    Pretriangulated
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) where
  distinguishedTriangles := distinguishedTriangles R C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_mem_distinguishedTriangles_iff
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end pretriangulated

end DGTwistedObject

end TauCeti
