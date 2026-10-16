/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Basic
public import TauCeti.Algebra.Homology.Periodic.Shift

/-!
# Compression and shifts

Periodic compression commutes with the cohomological shift. In residue degree `r`, the comparison
reindexes the summand in integer degree `i` as the summand in degree `i + k`; the signs on the two
differentials then agree. This compatibility is the shift datum needed to compare mapping-cone
triangles before compression with periodic mapping-cone triangles.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Complex

variable (n : ℕ) (K : CochainComplex C ℤ) (k : ℤ) [HasCompression n K]

/-- A shift of a complex with an `n`-periodic compression again has an `n`-periodic
compression. -/
instance hasCompression_shift : HasCompression n (K⟦k⟧) := fun r =>
  hasCoproduct_of_equiv_of_iso
    (GradedObject.mapObjFun K.X (fun i : ℤ ↦ (i : ZMod n)) (r + k))
    (GradedObject.mapObjFun (K⟦k⟧).X (fun i : ℤ ↦ (i : ZMod n)) r)
    ((Equiv.addRight k).subtypeEquiv (fun i => by simp))
    (fun i => CochainComplex.shiftFunctorObjXIso K k i.1 (i.1 + k) rfl)

private lemma XIsoOfEq_hom_comp_ιCompression {L : CochainComplex C ℤ} [HasCompression n L]
    {i j : ℤ} (hij : i = j) (r : ZMod n) (hi : (i : ZMod n) = r)
    (hj : (j : ZMod n) = r) :
    (L.XIsoOfEq hij).hom ≫ ιCompression n L j r hj = ιCompression n L i r hi := by
  subst hij
  simp

/-- The degreewise isomorphism which reindexes the compression of a shifted complex by
`i ↦ i + k`. -/
noncomputable def compressionShiftXIso (r : ZMod n) :
    (compression n (K⟦k⟧)).X r ≅ ((compression n K)⟦k⟧).X r where
  hom := compressionDesc n (K⟦k⟧) fun i hi ↦
    (CochainComplex.shiftFunctorObjXIso K k i (i + k) rfl).hom ≫
      ιCompression n K (i + k) (r + k) (by simp [hi])
  inv := compressionDesc n K fun j hj ↦
    (CochainComplex.shiftFunctorObjXIso K k (j - k) j (by omega)).inv ≫
      ιCompression n (K⟦k⟧) (j - k) r (by
        have h := congrArg (fun x : ZMod n ↦ x - k) hj
        simpa using h)
  hom_inv_id := by
    apply compression_hom_ext
    intro i hi
    dsimp
    simp only [ιCompression_compressionDesc_assoc, CochainComplex.shiftFunctor_obj_X',
      ιCompression_compressionDesc, Category.id_comp, Category.comp_id]
    exact XIsoOfEq_hom_comp_ιCompression (L := K⟦k⟧) n
      (Int.add_sub_cancel i k).symm r _ _
  inv_hom_id := by
    apply compression_hom_ext
    intro j hj
    dsimp
    simp only [ιCompression_compressionDesc_assoc, Category.assoc,
      ιCompression_compressionDesc, Category.id_comp, Category.comp_id]
    exact XIsoOfEq_hom_comp_ιCompression (L := K) n
      (Int.sub_add_cancel j k).symm (r + k) _ _

/-- On a summand, the shift comparison is the inclusion whose degree has been translated by the
shift. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionShiftXIso_hom (i : ℤ) (r : ZMod n)
    (hi : (i : ZMod n) = r) :
    ιCompression n (K⟦k⟧) i r hi ≫ (compressionShiftXIso n K k r).hom =
      (CochainComplex.shiftFunctorObjXIso K k i (i + k) rfl).hom ≫
        ιCompression n K (i + k) (r + k) (by simp [hi]) := by
  simp [compressionShiftXIso]

/-- On a summand, the inverse shift comparison is the inclusion whose degree has been translated
back by the shift. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionShiftXIso_inv (j : ℤ) (r : ZMod n)
    (hj : (j : ZMod n) = r + k) :
    ιCompression n K j (r + k) hj ≫ (compressionShiftXIso n K k r).inv =
      (CochainComplex.shiftFunctorObjXIso K k (j - k) j (by omega)).inv ≫
        ιCompression n (K⟦k⟧) (j - k) r (by
          have h := congrArg (fun x : ZMod n ↦ x - k) hj
          simpa using h) := by
  simp [compressionShiftXIso]

/-- Compression of a shifted complex is canonically isomorphic to the shift of its compression.
The comparison reindexes the summands by translation and introduces no additional sign. -/
noncomputable def compressionShiftIso :
    compression n (K⟦k⟧) ≅ (compression n K)⟦k⟧ :=
  HomologicalComplex.Hom.isoOfComponents (compressionShiftXIso n K k) (fun r s hrs ↦ by
    ext i hi
    have hi₁ : ((i + 1 : ℤ) : ZMod n) = s := by
      rw [ComplexShape.up_Rel] at hrs
      simpa [← hi] using hrs
    simp only [CochainComplex.shiftFunctor_obj_X', shiftFunctor_obj_X', shiftFunctor_obj_d',
      Linear.comp_units_smul, ιCompression_d_assoc n (K⟦k⟧) i (i + 1) rfl r s hi hi₁,
      CochainComplex.shiftFunctor_obj_d', Linear.units_smul_comp, smul_left_cancel_iff]
    simp only [ιCompression_compressionShiftXIso_hom_assoc,
      ιCompression_compressionShiftXIso_hom,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom]
    simp only [ιCompression_d n K (i + k) (i + 1 + k) (by omega) (r + k) (s + k)
        (by simp [hi]) (by simp [hi₁])]
    simp)

/-- The component in residue degree `r` of the shift comparison is the reindexing
isomorphism. -/
@[simp]
lemma compressionShiftIso_hom_f (r : ZMod n) :
    (compressionShiftIso n K k).hom.f r = (compressionShiftXIso n K k r).hom :=
  (rfl)

/-- The inverse component in residue degree `r` is the inverse reindexing map. -/
@[simp]
lemma compressionShiftIso_inv_f (r : ZMod n) :
    (compressionShiftIso n K k).inv.f r = (compressionShiftXIso n K k r).inv :=
  (rfl)

/-- The shift comparison is natural in the complex. -/
@[reassoc]
lemma compressionShiftIso_hom_naturality {L : CochainComplex C ℤ} [HasCompression n L]
    (f : K ⟶ L) :
    compressionMap n (f⟦k⟧') ≫ (compressionShiftIso n L k).hom =
      (compressionShiftIso n K k).hom ≫ (compressionMap n f)⟦k⟧' := by
  ext r i hi
  simp only [CochainComplex.shiftFunctor_obj_X', shiftFunctor_obj_X',
    HomologicalComplex.comp_f, ιCompression_compressionMap_f_assoc,
    CochainComplex.shiftFunctor_map_f', shiftFunctor_map_f',
    compressionShiftIso_hom_f, ιCompression_compressionShiftXIso_hom_assoc,
    ιCompression_compressionShiftXIso_hom, ιCompression_compressionMap_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp]
  simp

section Bounded

variable [HasFiniteCoproducts C]

/-- Compression of bounded complexes commutes naturally with the shift by `k`. -/
noncomputable def compressionFunctorShiftIso :
    CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙ compressionFunctor n ≅
      compressionFunctor n ⋙
        CategoryTheory.shiftFunctor (HomologicalComplex C (.up (ZMod n))) k :=
  NatIso.ofComponents (fun K ↦
    let : HasCompression n
        ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙
          CochainComplex.Bounded.ι C).obj K) :=
      hasCompression_of_bounded n (K⟦k⟧).property
    have hK : CochainComplex.bounded C (K.obj⟦k⟧) :=
      (CochainComplex.bounded C).prop_of_iso
        (((CochainComplex.Bounded.ι C).commShiftIso k).app K) (K⟦k⟧).property
    let : HasCompression n
        ((CochainComplex.Bounded.ι C ⋙
          CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj K) :=
      hasCompression_of_bounded n hK
    let : HasCompression n (K.obj⟦k⟧) := hasCompression_of_bounded n hK
    eqToIso (compressionFunctor_obj n (K⟦k⟧)) ≪≫
      compressionMapIso n (((CochainComplex.Bounded.ι C).commShiftIso k).app K) ≪≫
      compressionShiftIso n K.obj k ≪≫
      eqToIso (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)).symm)
    (fun {K L} f ↦ by
      let : HasCompression n
          ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙
            CochainComplex.Bounded.ι C).obj K) :=
        hasCompression_of_bounded n (K⟦k⟧).property
      let : HasCompression n
          ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙
            CochainComplex.Bounded.ι C).obj L) :=
        hasCompression_of_bounded n (L⟦k⟧).property
      have hK : CochainComplex.bounded C (K.obj⟦k⟧) :=
        (CochainComplex.bounded C).prop_of_iso
          (((CochainComplex.Bounded.ι C).commShiftIso k).app K) (K⟦k⟧).property
      have hL : CochainComplex.bounded C (L.obj⟦k⟧) :=
        (CochainComplex.bounded C).prop_of_iso
          (((CochainComplex.Bounded.ι C).commShiftIso k).app L) (L⟦k⟧).property
      let : HasCompression n
          ((CochainComplex.Bounded.ι C ⋙
            CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj K) :=
        hasCompression_of_bounded n hK
      let : HasCompression n
          ((CochainComplex.Bounded.ι C ⋙
            CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj L) :=
        hasCompression_of_bounded n hL
      let : HasCompression n (K.obj⟦k⟧) := hasCompression_of_bounded n hK
      let : HasCompression n (L.obj⟦k⟧) := hasCompression_of_bounded n hL
      let : HasCompression n K.obj := hasCompression_of_bounded n K.property
      let : HasCompression n L.obj := hasCompression_of_bounded n L.property
      let : HasCompression n ((CochainComplex.Bounded.ι C).obj K) :=
        hasCompression_of_bounded n K.property
      let : HasCompression n ((CochainComplex.Bounded.ι C).obj L) :=
        hasCompression_of_bounded n L.property
      rw [← cancel_epi (eqToHom (compressionFunctor_obj n (K⟦k⟧)).symm)]
      rw [← cancel_mono (eqToHom
        (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n L)))]
      have hcomp :
          compressionMap n ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k).map f).hom ≫
              compressionMap n (((CochainComplex.Bounded.ι C).commShiftIso k).app L).hom =
            compressionMap n (((CochainComplex.Bounded.ι C).commShiftIso k).app K).hom ≫
              compressionMap n (f.hom⟦k⟧') := by
        rw [← compressionMap_comp, ← compressionMap_comp]
        congr 1
        exact Functor.commShiftIso_hom_naturality (CochainComplex.Bounded.ι C) f k
      simp only [Functor.comp_map, compressionFunctor_map, Iso.trans_hom, eqToIso.hom,
        compressionMapIso_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Functor.map_comp, eqToHom_map]
      rw [← Category.assoc, hcomp]
      simp only [Category.assoc]
      rw [compressionShiftIso_hom_naturality_assoc]
      rfl)

/-- The forward component of bounded shift compatibility is the composite of the underlying
bounded-complex comparison with the shift comparison for compression. -/
@[simp]
lemma compressionFunctorShiftIso_hom_app (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n k).hom.app K =
      let _ : HasCompression n
          ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙
            CochainComplex.Bounded.ι C).obj K) :=
        hasCompression_of_bounded n (K⟦k⟧).property
      let hK : CochainComplex.bounded C (K.obj⟦k⟧) :=
        (CochainComplex.bounded C).prop_of_iso
          (((CochainComplex.Bounded.ι C).commShiftIso k).app K) (K⟦k⟧).property
      let _ : HasCompression n
          ((CochainComplex.Bounded.ι C ⋙
            CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj K) :=
        hasCompression_of_bounded n hK
      (eqToIso (compressionFunctor_obj n (K⟦k⟧))).hom ≫
          (compressionMapIso n (((CochainComplex.Bounded.ι C).commShiftIso k).app K)).hom ≫
            (compressionShiftIso n K.obj k).hom ≫
              (eqToIso
                (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)).symm).hom :=
  (rfl)

/-- The inverse component of bounded shift compatibility is the reverse composite of the
underlying shift comparison and the inverse compression comparison. -/
@[simp]
lemma compressionFunctorShiftIso_inv_app (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n k).inv.app K =
      let _ : HasCompression n
          ((CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙
            CochainComplex.Bounded.ι C).obj K) :=
        hasCompression_of_bounded n (K⟦k⟧).property
      let hK : CochainComplex.bounded C (K.obj⟦k⟧) :=
        (CochainComplex.bounded C).prop_of_iso
          (((CochainComplex.Bounded.ι C).commShiftIso k).app K) (K⟦k⟧).property
      let _ : HasCompression n
          ((CochainComplex.Bounded.ι C ⋙
            CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj K) :=
        hasCompression_of_bounded n hK
      ((eqToIso (compressionFunctor_obj n (K⟦k⟧))) ≪≫
        compressionMapIso n (((CochainComplex.Bounded.ι C).commShiftIso k).app K) ≪≫
          compressionShiftIso n K.obj k ≪≫
            eqToIso
              (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)).symm).inv :=
  (rfl)

end Bounded

end Complex

end TauCeti.PeriodicComplex
