/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

import Mathlib.CategoryTheory.Abelian.Refinements
import TauCeti.CategoryTheory.Abelian.ImageSubobject

/-!
# Subcomplexes from subobjects of the terms

Let `K` be a homological complex and let `S i` be a subobject of `K.X i` for every index `i`,
such that every differential `K.d i j` maps `S i` into `S j`. Then
`HomologicalComplex.ofSubobjects K S hS` is the complex with terms `S i` and the restricted
differentials, and `HomologicalComplex.ofSubobjectsι K S hS` is its inclusion into `K`, a
monomorphism of complexes. A morphism of complexes into `K` whose components factor through the
subobjects `S i` lifts uniquely to this subcomplex (`HomologicalComplex.ofSubobjectsLift`).

In an abelian category, this subcomplex is exact in degree `j` exactly when the intersection of
`S j` with the cycles of `K` is contained in the image of `S i` under the differential
(`HomologicalComplex.exactAt_ofSubobjects_iff`). In terms of generalized elements, every cycle of
`K` in `S j` is the differential of an element of `S i` up to an epimorphic refinement. This is
how acyclic subcomplexes are built degree by degree.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] {c : ComplexShape ι}

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K : HomologicalComplex C c) (S : ∀ i, Subobject (K.X i))
  (hS : ∀ i j, c.Rel i j → (S j).Factors ((S i).arrow ≫ K.d i j))

include hS

private lemma factors_arrow_comp_d_of_subobjects (i j : ι) :
    (S j).Factors ((S i).arrow ≫ K.d i j) := by
  by_cases h : c.Rel i j
  · exact hS i j h
  · rw [K.shape i j h, comp_zero]
    exact Subobject.factors_zero

/-- The subcomplex of `K` whose terms are the subobjects `S i`, when every differential `K.d i j`
maps `S i` into `S j`. -/
noncomputable def ofSubobjects : HomologicalComplex C c where
  X i := S i
  d i j := (S j).factorThru _ (K.factors_arrow_comp_d_of_subobjects S hS i j)
  shape i j h := by
    ext
    simp [K.shape i j h]
  d_comp_d' i j k _ _ := by
    ext
    simp

/-- The terms of `K.ofSubobjects S hS` are the subobjects `S i`. -/
noncomputable def ofSubobjectsXIso (i : ι) : (K.ofSubobjects S hS).X i ≅ (S i : C) :=
  Iso.refl _

/-- The inclusion of the subcomplex `K.ofSubobjects S hS` into `K`. -/
noncomputable def ofSubobjectsι : K.ofSubobjects S hS ⟶ K where
  f i := (S i).arrow
  comm' i j _ := by simp [ofSubobjects]

@[reassoc (attr := simp)]
lemma ofSubobjectsXIso_inv_ofSubobjectsι_f (i : ι) :
    (K.ofSubobjectsXIso S hS i).inv ≫ (K.ofSubobjectsι S hS).f i = (S i).arrow :=
  Category.id_comp _

@[reassoc (attr := simp)]
lemma ofSubobjectsXIso_hom_arrow (i : ι) :
    (K.ofSubobjectsXIso S hS i).hom ≫ (S i).arrow = (K.ofSubobjectsι S hS).f i :=
  Category.id_comp _

instance (i : ι) : Mono ((K.ofSubobjectsι S hS).f i) := by
  rw [← ofSubobjectsXIso_hom_arrow]
  infer_instance

instance : Mono (K.ofSubobjectsι S hS) :=
  mono_of_mono_f _ inferInstance

variable {K S} in
/-- A morphism of complexes `f : L ⟶ K` whose components factor through the subobjects `S i`
lifts to the subcomplex `K.ofSubobjects S hS`. -/
noncomputable def ofSubobjectsLift {L : HomologicalComplex C c} (f : L ⟶ K)
    (hf : ∀ i, (S i).Factors (f.f i)) : L ⟶ K.ofSubobjects S hS where
  f i := (S i).factorThru _ (hf i) ≫ (K.ofSubobjectsXIso S hS i).inv
  comm' i j _ := by
    rw [← cancel_mono ((K.ofSubobjectsι S hS).f j)]
    simp [← Hom.comm]

@[reassoc (attr := simp)]
lemma ofSubobjectsLift_ofSubobjectsι {L : HomologicalComplex C c} (f : L ⟶ K)
    (hf : ∀ i, (S i).Factors (f.f i)) :
    ofSubobjectsLift hS f hf ≫ K.ofSubobjectsι S hS = f := by
  ext i
  simp [ofSubobjectsLift]

/-- The lift `ofSubobjectsLift hS f hf` is the unique morphism whose composite with the
inclusion `K.ofSubobjectsι S hS` is `f`. -/
lemma ofSubobjectsLift_unique {L : HomologicalComplex C c} (f : L ⟶ K)
    (hf : ∀ i, (S i).Factors (f.f i)) (g : L ⟶ K.ofSubobjects S hS)
    (hg : g ≫ K.ofSubobjectsι S hS = f) : g = ofSubobjectsLift hS f hf := by
  rw [← cancel_mono (K.ofSubobjectsι S hS), hg, ofSubobjectsLift_ofSubobjectsι]

lemma isZero_ofSubobjects_X [HasZeroObject C] (i : ι) (h : S i = ⊥) :
    IsZero ((K.ofSubobjects S hS).X i) := by
  refine IsZero.of_iso ?_ (K.ofSubobjectsXIso S hS i)
  rw [h]
  exact IsZero.of_iso (Limits.isZero_zero C) Subobject.botCoeIsoZero

end HasZeroMorphisms

variable [Abelian C] (K : HomologicalComplex C c) (S : ∀ i, Subobject (K.X i))
  (hS : ∀ i j, c.Rel i j → (S j).Factors ((S i).arrow ≫ K.d i j))

/-- The subcomplex `K.ofSubobjects S hS` is exact in degree `j` if and only if the intersection
of `S j` with the cycles of `K` is contained in the image of `S i` under the differential. -/
lemma exactAt_ofSubobjects_iff {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) :
    (K.ofSubobjects S hS).ExactAt j ↔
      S j ⊓ kernelSubobject (K.d j k) ≤ (Subobject.exists (K.d i j)).obj (S i) := by
  rw [exactAt_iff' _ i j k (c.prev_eq' hij) (c.next_eq' hjk),
    ShortComplex.exact_iff_exact_up_to_refinements, Subobject.exists_eq_imageSubobject]
  constructor
  · intro hN
    let y : ((S j ⊓ kernelSubobject (K.d j k) : Subobject (K.X j)) : C) ⟶
        (K.ofSubobjects S hS).X j :=
      Subobject.ofLE _ _ inf_le_left ≫ (K.ofSubobjectsXIso S hS j).inv
    have hy : y ≫ (K.ofSubobjectsι S hS).f j = (S j ⊓ kernelSubobject (K.d j k)).arrow := by
      simp [y]
    obtain ⟨A', π, hπ, x₁, hx₁⟩ := hN y (by
      rw [← cancel_mono ((K.ofSubobjectsι S hS).f k), zero_comp]
      have : y ≫ (K.ofSubobjects S hS).d j k ≫ (K.ofSubobjectsι S hS).f k = 0 := by
        rw [← Hom.comm, reassoc_of% hy, ← Subobject.factorThru_arrow _ _
          (Subobject.inf_arrow_factors_right _ _), Category.assoc, kernelSubobject_arrow_comp,
          comp_zero]
      simpa using this)
    refine Subobject.le_of_factors ((imageSubobject_factors_iff_up_to_refinements _ _).2
      ⟨A', π, hπ, x₁ ≫ (K.ofSubobjectsXIso S hS i).hom, ?_⟩)
    have := hx₁ =≫ (K.ofSubobjectsι S hS).f j
    simp only [Category.assoc, hy] at this
    simpa using this
  · intro h A x₂ hx₂
    have hx₂' : (S j ⊓ kernelSubobject (K.d j k)).Factors (x₂ ≫ (K.ofSubobjectsι S hS).f j) := by
      refine (Subobject.inf_factors _).2 ⟨?_, kernelSubobject_factors _ _ ?_⟩
      · rw [← ofSubobjectsXIso_hom_arrow, ← Category.assoc]
        exact Subobject.factors_comp_arrow _
      · simpa using hx₂ =≫ (K.ofSubobjectsι S hS).f k
    obtain ⟨A', π, hπ, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements _ _).1
      (Subobject.factors_of_le _ h hx₂')
    refine ⟨A', π, hπ, x ≫ (K.ofSubobjectsXIso S hS i).inv, ?_⟩
    rw [← K.ofSubobjectsXIso_inv_ofSubobjectsι_f_assoc S hS, Hom.comm] at hx
    rw [← cancel_mono ((K.ofSubobjectsι S hS).f j)]
    simpa using hx

end HomologicalComplex
