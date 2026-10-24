/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Twisted.Extension
public import TauCeti.CategoryTheory.DG.Twisted.Shift

/-!
# The cone of a closed morphism of twisted objects

Let `C` be a differential graded category and let `u : P ⟶ Q` be a closed degree-zero morphism
of twisted objects of the additive closure of the shift closure of `C`.  Its **cone**
`TauCeti.DGTwistedObject.cone u` is the twisted object `(Q ⊕ P⟦1⟧, δ)` whose twisting matrix
has the twists of `Q` and of the shift `P⟦1⟧` on the diagonal and, in the block from `P⟦1⟧` to
`Q`, the degree-one morphism `P⟦1⟧ ⟶ P ⟶ Q` obtained by composing `u` with the comparison
morphism `TauCeti.DGTwistedObject.fromShift` (`TauCeti.DGTwistedObject.coneMorphism`).  It is the
extension of `P⟦1⟧` by `Q` along this morphism (see
`TauCeti/CategoryTheory/DG/Twisted/Extension.lean`), which supplies its Maurer–Cartan equation,
the closed degree-zero morphisms `Q ⟶ cone u ⟶ P⟦1⟧` with zero composite, and their graded
splitting.  In particular, a closed morphism `f : X ⟶ Y` of `C`, viewed as a morphism of one-term
twisted objects `X[0] ⟶ Y[0]`, has a cone whose underlying object is `Y[0] ⊕ X[1]`.

These maps give the candidate triangle `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of the pretriangulated envelope.
In the homotopy category both remaining consecutive composites vanish: `u` followed by the
inclusion of `Q` is the differential of minus the comparison morphism `P ⟶ P⟦1⟧` followed by the
inclusion of `P⟦1⟧`, and the projection onto `P⟦1⟧` followed by the shift of `u` is the
differential of minus the projection onto `Q` followed by the comparison morphism `Q ⟶ Q⟦1⟧`.
The second computation uses the Koszul-sign naturality of the comparison morphisms
(`TauCeti.DGTwistedObject.dgComp_toShift`), whose sign is trivial in degree zero.

The cone depends only on the homotopy class of `u`: if `u - u' = d k` for a degree `-1`
morphism `k : P ⟶ Q`, then `cone u` and `cone u'` are isomorphic in the homotopy category, by the
isomorphism of extensions along homotopic morphisms applied to minus `P⟦1⟧ ⟶ P` followed by `k`.

The cone of the zero morphism is the extension along zero, the direct sum `Q ⊕ P⟦1⟧` of twisted
objects.  If `u` has an inverse `u' : Q ⟶ P` of degree zero, then `u'` followed by the comparison
morphism `P ⟶ P⟦1⟧` is a degree `-1` inverse of the twisting entry `P⟦1⟧ ⟶ Q`, so the cone of an
isomorphism, and in particular `Cone(id_P)`, is contractible: it is a zero object of the
homotopy category.

## Main definitions

* `TauCeti.DGTwistedObject.coneMorphism`: a degree-zero morphism `P ⟶ Q` as the degree-one
  morphism `P⟦1⟧ ⟶ Q`.
* `TauCeti.DGTwistedObject.cone`: the cone of a closed degree-zero morphism.
* `TauCeti.DGTwistedObject.coneIsoOfHomotopy`: the isomorphism in the homotopy category between
  the cones of homotopic morphisms.

## Main results

* `TauCeti.DGTwistedObject.dgDifferential_coneMorphism`: the degree-one morphism underlying a
  closed morphism is closed.
* `TauCeti.DGTwistedObject.dgDifferential_dgComp_toShift_extensionInr_cone` and
  `TauCeti.DGTwistedObject.homOf_comp_homOf_extensionInl_cone_eq_zero`: `u` followed by the
  inclusion of `Q` into the cone is a boundary, so it vanishes in the homotopy category.
* `TauCeti.DGTwistedObject.dgDifferential_dgComp_extensionFst_toShift_cone` and
  `TauCeti.DGTwistedObject.homOf_extensionSnd_cone_comp_map_homOf_eq_zero`: the projection of the
  cone onto `P⟦1⟧` followed by the shift of `u` is a boundary, so it vanishes in the homotopy
  category.
* `TauCeti.DGTwistedObject.dgDifferential_neg_dgComp_fromShift`: a homotopy from `u` to `u'`
  gives a homotopy between the twisting entries of their cones.
* `TauCeti.DGTwistedObject.cone_zero`: the cone of the zero morphism is the direct sum
  `Q ⊕ P⟦1⟧`.
* `TauCeti.DGTwistedObject.isZero_of_cone`: the cone of an isomorphism is a zero object of the
  homotopy category.
* `TauCeti.DGTwistedObject.isZero_of_cone_dgId`: `Cone(id_P)` is contractible.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

namespace DGTwistedObject

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]
  {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

variable (R) in
/-- A degree-zero morphism `u : P ⟶ Q` of twisted objects, as the degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q`: the comparison morphism `TauCeti.DGTwistedObject.fromShift` followed by `u`. -/
noncomputable def coneMorphism (u : DGHom R 0 P Q) : DGHom R 1 ((shiftFunctor R 1).obj P) Q :=
  dgComp R (fromShift P 1) u (add_zero 1)

/-- The degree-one morphism underlying `u` is `P⟦1⟧ ⟶ P` followed by `u`. -/
theorem coneMorphism_def (u : DGHom R 0 P Q) :
    coneMorphism R u = dgComp R (fromShift P 1) u (add_zero 1) :=
  (rfl)

/-- The degree-one morphism `P⟦1⟧ ⟶ Q` underlying a closed morphism `u : P ⟶ Q` is closed. -/
theorem dgDifferential_coneMorphism {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) :
    dgDifferential R 1 (coneMorphism R u) = 0 := by
  rw [coneMorphism_def, dgDifferential_dgComp, dgDifferential_fromShift, hu, zero_dgComp,
    dgComp_zero, smul_zero, add_zero]

/-- The morphism `P⟦1⟧ ⟶ Q` underlying `u` followed by `k` is `P⟦1⟧ ⟶ P` followed by `u` and `k`;
unlike `TauCeti.DGTwistedObject.coneMorphism_def`, this rewrites `coneMorphism R u` only where it
is composed, not where it is the twist of a cone. -/
private theorem dgComp_coneMorphism {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {q n : ℤ} (u : DGHom R 0 P Q) (k : DGHom R q Q Z) (h : 1 + q = n) :
    dgComp R (coneMorphism R u) k h = dgComp R (fromShift P 1) (dgComp R u k (zero_add q)) h :=
  dgComp_assoc R _ _ _ (add_zero 1) (zero_add q) (by omega)

/-- The **cone** of a closed degree-zero morphism `u : P ⟶ Q` of twisted objects: the twisted
object `(Q ⊕ P⟦1⟧, δ)` whose twisting matrix has the twists of `Q` and `P⟦1⟧` on the diagonal
and the morphism `P⟦1⟧ ⟶ P ⟶ Q` underlying `u` in the block from `P⟦1⟧` to `Q`. -/
-- This is reducible so that the cone is reducibly an extension, whose API then applies.
noncomputable abbrev cone (u : DGHom R 0 P Q) (hu : dgDifferential R 0 u = 0) :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)) :=
  extension Q ((shiftFunctor R 1).obj P) (coneMorphism R u) (dgDifferential_coneMorphism hu)

/-! ### The triangle of a cone -/

section triangle

variable {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)

/-- **The composite `P ⟶ Q ⟶ cone u` is null-homotopic**: the comparison morphism `P ⟶ P⟦1⟧`
followed by the inclusion of `P⟦1⟧` into the cone has differential minus `u` followed by the
inclusion of `Q`. -/
theorem dgDifferential_dgComp_toShift_extensionInr_cone :
    dgDifferential R (-1)
        (dgComp R (toShift P 1) (extensionInr R (dgDifferential_coneMorphism hu))
          (add_zero (-1))) =
      -dgComp R u (extensionInl R (dgDifferential_coneMorphism hu)) (add_zero 0) := by
  rw [dgDifferential_dgComp, dgDifferential_toShift, zero_dgComp, zero_add,
    dgDifferential_extensionInr, dgComp_coneMorphism, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul,
    ← dgComp_assoc R (toShift P 1) (fromShift P 1) _ (neg_add_cancel 1) (add_zero 1) (by omega),
    dgComp_toShift_fromShift, dgId_dgComp]

/-- **The composite `P ⟶ Q ⟶ cone u` vanishes in the homotopy category.** -/
theorem homOf_comp_homOf_extensionInl_cone_eq_zero :
    DGHomotopyCategory.homOf R u ((mem_dgCycles R).mpr hu) ≫
        DGHomotopyCategory.homOf R (extensionInl R (dgDifferential_coneMorphism hu))
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) =
      0 :=
  DGHomotopyCategory.homOf_comp_eq_zero_of_dgDifferential_eq_neg R _ _
    (dgDifferential_dgComp_toShift_extensionInr_cone hu)

/-- **The composite `cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` is null-homotopic**: the projection of the cone onto
`Q` followed by the comparison morphism `Q ⟶ Q⟦1⟧` has differential minus the projection onto
`P⟦1⟧` followed by the shift of `u`. -/
theorem dgDifferential_dgComp_extensionFst_toShift_cone :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu)) (toShift Q 1)
          (zero_add (-1))) =
      -dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((shiftFunctor R 1).dgMap 0 u) (add_zero 0) := by
  rw [dgDifferential_dgComp, dgDifferential_toShift, dgComp_zero, smul_zero, add_zero,
    dgDifferential_extensionFst, neg_dgComp,
    dgComp_assoc R _ (coneMorphism R u) _ (zero_add 1) (add_neg_cancel 1) (by omega),
    dgComp_coneMorphism,
    dgComp_toShift 1 u (zero_add (-1)), mul_zero, Int.negOnePow_zero, one_smul,
    ← dgComp_assoc R (fromShift P 1) (toShift P 1) _ (add_neg_cancel 1) (add_zero (-1))
      (by omega),
    dgComp_fromShift_toShift, dgId_dgComp]

/-- **The composite `cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` vanishes in the homotopy category.** -/
theorem homOf_extensionSnd_cone_comp_map_homOf_eq_zero :
    DGHomotopyCategory.homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
        (shiftFunctor R 1).mapDGHomotopyCategory.map (X := DGHomotopyCategory.of R P)
          (Y := DGHomotopyCategory.of R Q)
          (DGHomotopyCategory.homOf R u ((mem_dgCycles R).mpr hu)) =
      0 := by
  have h : DGHomotopyCategory.homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
      DGHomotopyCategory.homOf R ((shiftFunctor R 1).dgMap 0 u)
        ((shiftFunctor R 1).dgMap_mem_dgCycles ((mem_dgCycles R).mpr hu)) = 0 :=
    DGHomotopyCategory.homOf_comp_eq_zero_of_dgDifferential_eq_neg R _ _
      (dgDifferential_dgComp_extensionFst_toShift_cone hu)
  rw [(shiftFunctor R 1).mapDGHomotopyCategory_map_homOf u]
  -- `h` is the claim up to `TauCeti.EnrichedFunctor.mapDGHomotopyCategory_obj_of`, which holds by
  -- `rfl` but cannot be rewritten inside the implicit object of the composite.
  exact h

end triangle

variable (P Q) in
/-- **The cone of the zero morphism is the direct sum** `Q ⊕ P⟦1⟧`: the extension along the zero
morphism, whose twisting matrix has the twists of `Q` and `P⟦1⟧` on the diagonal and vanishes
off it. -/
@[simp]
theorem cone_zero :
    cone (0 : DGHom R 0 P Q) (map_zero _) =
      extension Q ((shiftFunctor R 1).obj P) 0 (map_zero _) := by
  have h : coneMorphism R (0 : DGHom R 0 P Q) = 0 := dgComp_zero R _ _
  simp only [cone, h]

/-! ### Cones of homotopic morphisms -/

/-- If `u - u' = d k` for a degree `-1` morphism `k : P ⟶ Q`, then the twisting entries of the
cones of `u` and `u'` differ by the differential of minus `P⟦1⟧ ⟶ P` followed by `k`. -/
theorem dgDifferential_neg_dgComp_fromShift {u u' : DGHom R 0 P Q} {k : DGHom R (-1) P Q}
    (hk : dgDifferential R (-1) k = u - u') :
    dgDifferential R 0 (-dgComp R (fromShift P 1) k (add_neg_cancel 1)) =
      coneMorphism R u - coneMorphism R u' := by
  rw [map_neg, dgDifferential_dgComp, dgDifferential_fromShift, zero_dgComp, hk]
  simp only [zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg, coneMorphism_def,
    sub_eq_add_neg, dgComp_add, dgComp_neg]

/-- **Cones of homotopic morphisms are isomorphic**: if `u - u' = d k` for a degree `-1`
morphism `k : P ⟶ Q`, then `cone u` and `cone u'` are isomorphic in the homotopy category.  The
isomorphism is the identity on `Q` and on `P⟦1⟧`, together with minus `P⟦1⟧ ⟶ P` followed by `k`
in the block from `P⟦1⟧` to `Q`. -/
-- This is reducible so that the API of `TauCeti.DGTwistedObject.extensionIsoOfHomotopy` applies.
noncomputable abbrev coneIsoOfHomotopy {u u' : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)
    (hu' : dgDifferential R 0 u' = 0) {k : DGHom R (-1) P Q}
    (hk : dgDifferential R (-1) k = u - u') :
    DGHomotopyCategory.of R (cone u hu) ≅ DGHomotopyCategory.of R (cone u' hu') :=
  extensionIsoOfHomotopy R (dgDifferential_neg_dgComp_fromShift hk)

/-! ### Cones of isomorphisms are contractible -/

section contractible

variable {u : DGHom R 0 P Q} {u' : DGHom R 0 Q P}

/-- **The cone of an isomorphism is contractible**: if the closed degree-zero morphism
`u : P ⟶ Q` has a two-sided inverse `u' : Q ⟶ P` of degree zero, then its cone is a zero object
of the homotopy category of twisted objects. -/
theorem isZero_of_cone (hu : dgDifferential R 0 u = 0)
    (huu' : dgComp R u u' (add_zero 0) = dgId R P) (hu'u : dgComp R u' u (add_zero 0) = dgId R Q) :
    Limits.IsZero (DGHomotopyCategory.of R (cone u hu)) := by
  refine isZero_of_extension R _ (g' := dgComp R u' (toShift P 1) (zero_add (-1))) ?_ ?_
  · rw [coneMorphism_def, dgComp_assoc R (fromShift P 1) u _ (add_zero 1) (zero_add (-1))
        (by omega),
      ← dgComp_assoc R u u' _ (add_zero 0) (zero_add (-1)) (by omega), huu', dgId_dgComp,
      dgComp_fromShift_toShift]
  · rw [coneMorphism_def, dgComp_assoc R u' (toShift P 1) _ (zero_add (-1)) (neg_add_cancel 1)
        (by omega),
      ← dgComp_assoc R (toShift P 1) (fromShift P 1) u (neg_add_cancel 1) (add_zero 1)
        (by omega),
      dgComp_toShift_fromShift, dgId_dgComp, hu'u]

variable (R P) in
/-- **The cone of an identity is contractible**: `Cone(id_P)` is a zero object of the homotopy
category of twisted objects. -/
theorem isZero_of_cone_dgId :
    Limits.IsZero (DGHomotopyCategory.of R (cone (dgId R P) (dgDifferential_dgId R P))) :=
  isZero_of_cone _ (dgComp_dgId R _) (dgComp_dgId R _)

end contractible

end DGTwistedObject

end TauCeti
