/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Extending homotopies and homotopy equivalences by zero

An embedding of complex shapes extends complexes and their morphisms by zero.  Mathlib proves
that this construction also extends homotopies (`Homotopy.extend`).  This file records that the
extension preserves the compatibility of two homotopies with a pair of morphisms of complexes,
and packages the extension of homotopies into the corresponding operation on homotopy
equivalences.

## Main definition

* `HomotopyEquiv.extend`: extend a homotopy equivalence along an embedding of complex shapes.

## Main result

* `Homotopy.extend_hom_comm`: if the components of two homotopies commute with morphisms `u`
  and `v`, so do the components of their extensions with the extensions of `u` and `v`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Homotopy

open HomologicalComplex

variable {C ι ι' : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L K' L' : HomologicalComplex C c} {f g : K ⟶ L} {f' g' : K' ⟶ L'}

/-- If the components of homotopies `h` and `h'` commute with morphisms `u : K ⟶ K'` and
`v : L ⟶ L'`, then so do the components of their extensions along an embedding of complex shapes
with the extensions of `u` and `v`. -/
@[reassoc]
lemma extend_hom_comm (h : Homotopy f g) (h' : Homotopy f' g') (u : K ⟶ K') (v : L ⟶ L')
    (e : c.Embedding c') [e.IsRelIff] (huv : ∀ i j, u.f i ≫ h'.hom i j = h.hom i j ≫ v.f j)
    (i' j' : ι') :
    (extendMap u e).f i' ≫ (h'.extend e).hom i' j' =
      (h.extend e).hom i' j' ≫ (extendMap v e).f j' := by
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj
      simp [extendMap_f _ e rfl, extend_hom_eq _ e rfl rfl, reassoc_of% huv i j]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

end Homotopy

namespace HomotopyEquiv

open HomologicalComplex

variable {C ι ι' : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex C c}

/-- Extending both complexes by zero along an embedding of complex shapes preserves a homotopy
equivalence. -/
noncomputable def extend (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := extendMap h.hom e
  inv := extendMap h.inv e
  homotopyHomInvId := by
    simpa only [extendMap_comp, extendMap_id] using h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    simpa only [extendMap_comp, extendMap_id] using h.homotopyInvHomId.extend e

/-- The forward map of an extended homotopy equivalence is the extension of the forward map. -/
@[simp] theorem extend_hom (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).hom = extendMap h.hom e :=
  (rfl)

/-- The inverse map of an extended homotopy equivalence is the extension of the inverse map. -/
@[simp] theorem extend_inv (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).inv = extendMap h.inv e :=
  (rfl)

end HomotopyEquiv
