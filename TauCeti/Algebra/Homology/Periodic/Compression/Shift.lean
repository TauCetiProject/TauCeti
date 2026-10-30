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

The comparisons are coherent with the identifications `X⟦0⟧ ≅ X` and `X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧`, so
compression of bounded complexes commutes with the shift
(`TauCeti.PeriodicComplex.commShiftCompressionFunctor`). Since the quotient functor from bounded
complexes to their homotopy category is a localization functor, this compatibility descends to the
compression functor `K^b(C) ⥤ K_n(C)` on homotopy categories
(`TauCeti.PeriodicComplex.commShiftHomotopyCompressionFunctor`), compatibly with the quotient
functors.

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
    exact XIsoOfEq_hom_comp_ιCompression (K := K⟦k⟧) n
      (Int.add_sub_cancel i k).symm r _
  inv_hom_id := by
    apply compression_hom_ext
    intro j hj
    dsimp
    simp only [ιCompression_compressionDesc_assoc, Category.assoc,
      ιCompression_compressionDesc, Category.id_comp, Category.comp_id]
    exact XIsoOfEq_hom_comp_ιCompression (K := K) n
      (Int.sub_add_cancel j k).symm (r + k) _

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

/-- The shift comparison for the shift by zero is induced by the identifications `X⟦0⟧ ≅ X`. -/
lemma compressionShiftIso_zero_hom :
    (compressionShiftIso n K 0).hom =
      compressionMap (L := K) n ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) ≫
        (shiftFunctorZero _ ℤ).inv.app (compression n K) := by
  ext r i hi
  simp [CochainComplex.shiftFunctorZero_hom_app_f]

/-- The shift comparison for the shift by `a + b` is the composite of the comparisons for the
shifts by `a` and by `b`, through the identifications `X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧`. -/
lemma compressionShiftIso_add_hom (a b : ℤ) :
    (compressionShiftIso n K (a + b)).hom =
      compressionMap (L := K⟦a⟧⟦b⟧) n ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K) ≫
        (compressionShiftIso n (K⟦a⟧) b).hom ≫ (compressionShiftIso n K a).hom⟦b⟧' ≫
          (shiftFunctorAdd _ a b).inv.app (compression n K) := by
  ext r i hi
  simp [CochainComplex.shiftFunctorAdd_hom_app_f]

/-- The additivity of the shift comparison, precomposed with a factorization of a map into
`K⟦a + b⟧` through comparison maps into `K⟦a⟧` and its shift by `b`. -/
@[reassoc]
private lemma compressionMap_comp_compressionShiftIso_add_hom {L M N : CochainComplex C ℤ}
    [HasCompression n L] [HasCompression n M] [HasCompression n N]
    (a b : ℤ) (e : L ⟶ K⟦a + b⟧) (g : L ⟶ M) (eb : M ⟶ N⟦b⟧) (ea : N ⟶ K⟦a⟧)
    (h : e ≫ (shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K = g ≫ eb ≫ ea⟦b⟧') :
    compressionMap n e ≫ (compressionShiftIso n K (a + b)).hom =
      compressionMap n g ≫ compressionMap n eb ≫ (compressionShiftIso n N b).hom ≫
        (compressionMap n ea)⟦b⟧' ≫ (compressionShiftIso n K a).hom⟦b⟧' ≫
          (shiftFunctorAdd _ a b).inv.app (compression n K) := by
  rw [compressionShiftIso_add_hom, ← compressionMap_comp_assoc, h]
  simp only [Category.assoc, compressionMap_comp]
  rw [compressionShiftIso_hom_naturality_assoc]

section Bounded

variable [HasFiniteCoproducts C]

/-- The compression of the shift by `k` of the underlying complex, as a functor on bounded
complexes. -/
noncomputable def shiftCompressionFunctor :
    CochainComplex.Bounded C ⥤ HomologicalComplex C (ComplexShape.up (ZMod n)) where
  obj K := compression n (K.obj⟦k⟧)
  map f := compressionMap n (f.hom⟦k⟧')
  map_id K := by simp
  map_comp f g := by simp

/-- The functor `shiftCompressionFunctor` sends a bounded complex to the compression of the shift
of its underlying complex. -/
@[simp]
lemma shiftCompressionFunctor_obj (K : CochainComplex.Bounded C) :
    (shiftCompressionFunctor n k).obj K = compression n (K.obj⟦k⟧) :=
  (rfl)

/-- The functor `shiftCompressionFunctor` acts on a morphism by compressing the shift of the
underlying chain map, after transporting along the object equations. -/
@[simp]
lemma shiftCompressionFunctor_map {K L : CochainComplex.Bounded C} (f : K ⟶ L) :
    (shiftCompressionFunctor n k).map f =
      eqToHom (shiftCompressionFunctor_obj n k K) ≫ compressionMap n (f.hom⟦k⟧') ≫
        eqToHom (shiftCompressionFunctor_obj n k L).symm := by
  -- Unfold the map field and identify the transports along its definitional object equations
  -- with identities.
  change compressionMap n (f.hom⟦k⟧') = 𝟙 _ ≫ compressionMap n (f.hom⟦k⟧') ≫ 𝟙 _
  simp

/-- Compressing the shift of a bounded complex agrees, naturally in the complex, with compressing
the shift of its underlying complex. -/
noncomputable def shiftCompCompressionFunctorIso :
    CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙ compressionFunctor n ≅
      shiftCompressionFunctor n k :=
  NatIso.ofComponents (fun K ↦
    eqToIso (compressionFunctor_obj n (K⟦k⟧)) ≪≫
      compressionMapIso (K := (K⟦k⟧).obj) (L := K.obj⟦k⟧) n
        (((CochainComplex.Bounded.ι C).commShiftIso k).app K) ≪≫
      eqToIso (shiftCompressionFunctor_obj n k K).symm)
    (fun {K L} f ↦ by
      have hcomp :
          compressionMap (K := (K⟦k⟧).obj) (L := (L⟦k⟧).obj) n (f⟦k⟧').hom ≫
              compressionMap (K := (L⟦k⟧).obj) (L := L.obj⟦k⟧) n
                (((CochainComplex.Bounded.ι C).commShiftIso k).hom.app L) =
            compressionMap (K := (K⟦k⟧).obj) (L := K.obj⟦k⟧) n
                (((CochainComplex.Bounded.ι C).commShiftIso k).hom.app K) ≫
              compressionMap n (f.hom⟦k⟧') := by
        rw [← compressionMap_comp, ← compressionMap_comp]
        congr 1
        exact Functor.commShiftIso_hom_naturality (CochainComplex.Bounded.ι C) f k
      simp only [Functor.comp_map, compressionFunctor_map, shiftCompressionFunctor_map,
        Iso.trans_hom, eqToIso.hom, compressionMapIso_hom, Iso.app_hom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% hcomp])

/-- The forward component of `shiftCompCompressionFunctorIso` compresses the comparison between
the underlying complex of the shift and the shift of the underlying complex. -/
@[simp]
lemma shiftCompCompressionFunctorIso_hom_app (K : CochainComplex.Bounded C) :
    (shiftCompCompressionFunctorIso n k).hom.app K =
      eqToHom (compressionFunctor_obj n (K⟦k⟧)) ≫
        compressionMap (K := (K⟦k⟧).obj) (L := K.obj⟦k⟧) n
          (((CochainComplex.Bounded.ι C).commShiftIso k).hom.app K) ≫
          eqToHom (shiftCompressionFunctor_obj n k K).symm := by
  simp only [shiftCompCompressionFunctorIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    eqToIso.hom, compressionMapIso_hom, Iso.app_hom]

/-- The inverse component of `shiftCompCompressionFunctorIso` compresses the inverse comparison
between the underlying complex of the shift and the shift of the underlying complex. -/
@[simp]
lemma shiftCompCompressionFunctorIso_inv_app (K : CochainComplex.Bounded C) :
    (shiftCompCompressionFunctorIso n k).inv.app K =
      eqToHom (shiftCompressionFunctor_obj n k K) ≫
        compressionMap (K := K.obj⟦k⟧) (L := (K⟦k⟧).obj) n
          (((CochainComplex.Bounded.ι C).commShiftIso k).inv.app K) ≫
          eqToHom (compressionFunctor_obj n (K⟦k⟧)).symm := by
  simp only [shiftCompCompressionFunctorIso, NatIso.ofComponents_inv_app, Iso.trans_inv,
    eqToIso.inv, compressionMapIso_inv, Iso.app_inv, Category.assoc]

/-- Compression of bounded complexes commutes naturally with the shift by `k`. -/
noncomputable def compressionFunctorShiftIso :
    CategoryTheory.shiftFunctor (CochainComplex.Bounded C) k ⋙ compressionFunctor n ≅
      compressionFunctor n ⋙
        CategoryTheory.shiftFunctor (HomologicalComplex C (.up (ZMod n))) k :=
  shiftCompCompressionFunctorIso n k ≪≫
    NatIso.ofComponents (fun K ↦
      eqToIso (shiftCompressionFunctor_obj n k K) ≪≫ compressionShiftIso n K.obj k ≪≫
        eqToIso (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)).symm)
      (fun {K L} f ↦ by
        simp [eqToHom_map, compressionShiftIso_hom_naturality_assoc])

/-- The forward component of bounded shift compatibility is the composite of the underlying
bounded-complex comparison with the shift comparison for compression. -/
@[simp]
lemma compressionFunctorShiftIso_hom_app (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n k).hom.app K =
      eqToHom (compressionFunctor_obj n (K⟦k⟧)) ≫
        compressionMap (K := (K⟦k⟧).obj) (L := K.obj⟦k⟧) n
          (((CochainComplex.Bounded.ι C).commShiftIso k).hom.app K) ≫
          (compressionShiftIso n K.obj k).hom ≫
            eqToHom (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)).symm := by
  simp only [compressionFunctorShiftIso, Iso.trans_hom, NatTrans.comp_app,
    shiftCompCompressionFunctorIso_hom_app, NatIso.ofComponents_hom_app, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The inverse component of bounded shift compatibility is the reverse composite of the
underlying shift comparison and the inverse compression comparison. -/
@[simp]
lemma compressionFunctorShiftIso_inv_app (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n k).inv.app K =
      eqToHom (congrArg (fun X ↦ X⟦k⟧) (compressionFunctor_obj n K)) ≫
        (compressionShiftIso n K.obj k).inv ≫
          compressionMap (K := K.obj⟦k⟧) (L := (K⟦k⟧).obj) n
            (((CochainComplex.Bounded.ι C).commShiftIso k).inv.app K) ≫
            eqToHom (compressionFunctor_obj n (K⟦k⟧)).symm := by
  simp only [compressionFunctorShiftIso, Iso.trans_inv, NatTrans.comp_app,
    shiftCompCompressionFunctorIso_inv_app, NatIso.ofComponents_inv_app, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The shift compatibility of bounded compression for the shift by zero is induced by the
identifications `X⟦0⟧ ≅ X`. -/
lemma compressionFunctorShiftIso_zero_hom_app (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n 0).hom.app K =
      (compressionFunctor n).map ((shiftFunctorZero _ ℤ).hom.app K) ≫
        (shiftFunctorZero _ ℤ).inv.app ((compressionFunctor n).obj K) := by
  have h : ((CochainComplex.Bounded.ι C).commShiftIso 0).hom.app K ≫
      (shiftFunctorZero _ ℤ).hom.app K.obj = ((shiftFunctorZero _ ℤ).hom.app K).hom := by
    simp [Functor.commShiftIso_zero]
  simp only [compressionFunctorShiftIso_hom_app, compressionShiftIso_zero_hom, Category.assoc]
  rw [← compressionMap_comp_assoc, h]
  simp

/-- The shift compatibility of bounded compression for the shift by `a + b` is the composite of
the compatibilities for the shifts by `a` and by `b`, through the identifications
`X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧`. -/
lemma compressionFunctorShiftIso_add_hom_app (a b : ℤ) (K : CochainComplex.Bounded C) :
    (compressionFunctorShiftIso n (a + b)).hom.app K =
      (compressionFunctor n).map ((shiftFunctorAdd _ a b).hom.app K) ≫
        (compressionFunctorShiftIso n b).hom.app (K⟦a⟧) ≫
          ((compressionFunctorShiftIso n a).hom.app K)⟦b⟧' ≫
            (shiftFunctorAdd _ a b).inv.app ((compressionFunctor n).obj K) := by
  have h : ((CochainComplex.Bounded.ι C).commShiftIso (a + b)).hom.app K ≫
      (shiftFunctorAdd _ a b).hom.app K.obj =
        ((shiftFunctorAdd _ a b).hom.app K).hom ≫
          ((CochainComplex.Bounded.ι C).commShiftIso b).hom.app (K⟦a⟧) ≫
            (((CochainComplex.Bounded.ι C).commShiftIso a).hom.app K)⟦b⟧' := by
    simp [Functor.commShiftIso_add]
  simp only [compressionFunctorShiftIso_hom_app, Category.assoc]
  rw [compressionMap_comp_compressionShiftIso_add_hom_assoc (L := (K⟦a + b⟧).obj)
    (M := (K⟦a⟧⟦b⟧).obj) (N := (K⟦a⟧).obj) n K.obj a b _ _ _ _ h]
  simp [eqToHom_map]

/-- Compression of bounded complexes commutes with the shift: the comparisons
`compressionFunctorShiftIso` are coherent with the identifications `X⟦0⟧ ≅ X` and
`X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧`. -/
noncomputable instance commShiftCompressionFunctor :
    (compressionFunctor (C := C) n).CommShift ℤ where
  commShiftIso k := compressionFunctorShiftIso n k
  commShiftIso_zero := by
    refine Iso.ext (NatTrans.ext (funext fun L ↦ ?_))
    rw [Functor.CommShift.isoZero_hom_app, compressionFunctorShiftIso_zero_hom_app]
  commShiftIso_add a b := by
    refine Iso.ext (NatTrans.ext (funext fun L ↦ ?_))
    rw [Functor.CommShift.isoAdd_hom_app, compressionFunctorShiftIso_add_hom_app]

/-- The shift compatibility of bounded compression is `compressionFunctorShiftIso`. -/
@[simp]
lemma compressionFunctor_commShiftIso :
    (compressionFunctor (C := C) n).commShiftIso k = compressionFunctorShiftIso n k :=
  (rfl)

end Bounded

end Complex

section Homotopy

variable [HasFiniteCoproducts C] (n : ℕ)

open HomotopyCategory.Bounded

/-- The descended compression is induced, along the localization functor
`HomotopyCategory.Bounded.quotient C`, by compression of bounded complexes. -/
noncomputable instance : Localization.Lifting (quotient C)
    ((HomologicalComplex.homotopyEquivalences C (.up ℤ)).inverseImage
      (CochainComplex.Bounded.ι C))
    (compressionFunctor n ⋙ HomotopyCategory.quotient C _) (homotopyCompressionFunctor n) :=
  ⟨quotientCompHomotopyCompressionFunctorIso n⟩

/-- The compression functor `K^b(C) ⥤ K_n(C)` commutes with the shift. Its shift compatibility
is induced by that of compression of bounded complexes, along the localization functor
`HomotopyCategory.Bounded.quotient C`. -/
noncomputable instance commShiftHomotopyCompressionFunctor :
    (homotopyCompressionFunctor (C := C) n).CommShift ℤ :=
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  Functor.commShiftOfLocalization (quotient C)
    ((HomologicalComplex.homotopyEquivalences C (.up ℤ)).inverseImage
      (CochainComplex.Bounded.ι C))
    ℤ (compressionFunctor n ⋙ HomotopyCategory.quotient C _) (homotopyCompressionFunctor n)

/-- The identification of the descended compression on the classes of bounded complexes with
the classes of their compressions is compatible with the shifts. -/
instance : NatTrans.CommShift (quotientCompHomotopyCompressionFunctorIso (C := C) n).hom ℤ :=
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  NatTrans.commShift_iso_hom_of_localization (quotient C)
    ((HomologicalComplex.homotopyEquivalences C (.up ℤ)).inverseImage
      (CochainComplex.Bounded.ι C))
    ℤ (compressionFunctor n ⋙ HomotopyCategory.quotient C _) (homotopyCompressionFunctor n)

end Homotopy

end TauCeti.PeriodicComplex
