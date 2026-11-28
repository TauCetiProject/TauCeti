/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.TotalComplex.UpNat
public import TauCeti.Topology.Sheaves.Godement.Basic

/-!
# Totalized Godement resolutions

Apply the Godement resolution to each term of a cochain complex and totalize the resulting
bicomplex. The first index is the resolution degree, so the total differential is the Godement
differential plus the internal differential multiplied by `(-1) ^ p` in resolution degree `p`.
For an integer-graded complex vanishing below `b`, reindex from `b` before totalizing. Each
diagonal is finite, and the total is a complex of flasque sheaves with the same lower bound.
The augmentation is a quasi-isomorphism whenever the canonical morphism from each sheaf to
its Godement sheaf is monic, as it is for sheaves of modules. More generally, it suffices
that each coaugmented row is a quasi-isomorphism.

The construction follows the Stacks Project, Lemma 20.30.2 (tag 0FKT), using the successive
cokernel model `TauCeti.Topology.godementResolution` for each row. The theorem
`HomologicalComplex₂.quasiIso_totalCoaugmentation` turns their exactness into the
quasi-isomorphism of the total augmentation.

## Main definitions

* `TauCeti.Topology.godementBicomplex`: resolve a nonnegatively graded complex degreewise.
* `TauCeti.Topology.godementTotal`: the total complex, augmented by
  `TauCeti.Topology.toGodementTotal`.
* `TauCeti.Topology.godementTotalAt`: the total complex in the original integer grading.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open HomologicalComplex HomologicalComplex₂

universe u

namespace TauCeti.Topology

variable (C : Type*) [Category.{u} C] [Abelian C] [HasColimits C] [HasProducts.{u} C]
  (X : TopCat.{u}) [HasSheafify (Opens.grothendieckTopology X) C]

/-- The Godement bicomplex has the Godement resolution of `K.X q` in row `q`. -/
abbrev godementBicomplex :
    CochainComplex (X.Sheaf C) ℕ ⥤ HomologicalComplex₂ (X.Sheaf C) (.up ℕ) (.up ℕ) :=
  (godementResolution C X).mapHomologicalComplex (.up ℕ) ⋙ flipFunctor _ _ _

/-- The row at internal degree `q` is the Godement resolution of the original term in degree
`q`, with its Godement differentials. -/
lemma godementBicomplex_row (K : CochainComplex (X.Sheaf C) ℕ) (q : ℕ) :
    (((eval (X.Sheaf C) (.up ℕ) q).mapHomologicalComplex (.up ℕ)).obj
        ((godementBicomplex C X).obj K)) = (godementResolution C X).obj (K.X q) :=
  (rfl)

/-- The totalized degreewise Godement resolution of a nonnegative cochain complex. -/
abbrev godementTotal : CochainComplex (X.Sheaf C) ℕ ⥤ CochainComplex (X.Sheaf C) ℕ :=
  godementBicomplex C X ⋙ totalFunctor _ _ _ _

/-- On the summand in bidegree `(p, q)`, the total differential is the Godement
differential plus `(-1)^p` times the internal differential. -/
-- The functor abbreviations in these formulas are not simp normal forms.
@[reassoc]
lemma ι_godementTotal_d (K : CochainComplex (X.Sheaf C) ℕ) (p q : ℕ) :
    ((godementBicomplex C X).obj K).ιTotal (.up ℕ) p q (p + q) rfl ≫
        ((godementTotal C X).obj K).d (p + q) (p + q + 1) =
      ((godementResolution C X).obj (K.X q)).d p (p + 1) ≫
        ((godementBicomplex C X).obj K).ιTotal (.up ℕ) (p + 1) q (p + q + 1)
          (by simp [add_assoc, add_comm, add_left_comm]) +
      (-1 : ℤˣ) ^ p •
        (((godementResolution C X).map (K.d q (q + 1))).f p ≫
          ((godementBicomplex C X).obj K).ιTotal (.up ℕ) p (q + 1) (p + q + 1)
            (by simp [add_assoc])) := by
  dsimp only [godementTotal, Functor.comp_obj, totalFunctor]
  rw [total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    d₁_eq _ _ (ComplexShape.up_mk p (p + 1) rfl) q (p + q + 1)
      (by simp [add_assoc, add_comm, add_left_comm]),
    d₂_eq _ _ p (ComplexShape.up_mk q (q + 1) rfl) (p + q + 1)
      (by simp [add_assoc])]
  simp

/-- The map of Godement totals acts on a summand by the corresponding degree of the
Godement resolution map. -/
@[reassoc]
lemma ι_godementTotal_map {K L : CochainComplex (X.Sheaf C) ℕ} (f : K ⟶ L) (p q : ℕ) :
    ((godementBicomplex C X).obj K).ιTotal (.up ℕ) p q (p + q) rfl ≫
        ((godementTotal C X).map f).f (p + q) =
      ((godementResolution C X).map (f.f q)).f p ≫
        ((godementBicomplex C X).obj L).ιTotal (.up ℕ) p q (p + q) rfl := by
  exact ιTotal_map _ _ ((godementBicomplex C X).map f) (.up ℕ) p q (p + q) rfl

variable {C X}

private def toGodementColumn (K : CochainComplex (X.Sheaf C) ℕ) :
    K ⟶ ((godementBicomplex C X).obj K).X 0 :=
  ((Functor.mapHomologicalComplexIdIso (X.Sheaf C) (.up ℕ)).inv ≫
    (toGodement C X).mapHomologicalComplex (.up ℕ)).app K

private lemma toGodementColumn_comp_d (K : CochainComplex (X.Sheaf C) ℕ) :
    toGodementColumn K ≫ ((godementBicomplex C X).obj K).d 0 1 = 0 := by
  ext1 q
  dsimp only [godementBicomplex, godementResolution, Functor.comp_obj,
    HomologicalComplex₂.flipFunctor, HomologicalComplex₂.flip, Functor.mapHomologicalComplex]
  simpa only [comp_f, zero_f, toGodementColumn, NatTrans.comp_app, comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Category.id_comp] using
      (toGodement C X).app_comp_resolution_obj_d_zero_one (K.X q)

variable (C X)

/-- The augmentation into the totalized Godement resolution, induced by the canonical map
from each term to its Godement sheaf in resolution degree zero. -/
def toGodementTotal : 𝟭 (CochainComplex (X.Sheaf C) ℕ) ⟶ godementTotal C X where
  app K := ((godementBicomplex C X).obj K).totalCoaugmentation
    (toGodementColumn K) (toGodementColumn_comp_d K)
  naturality K L f := by
    dsimp only [godementTotal, Functor.comp_obj, Functor.id_obj, Functor.id_map,
      Functor.comp_map, totalFunctor]
    rw [comp_totalCoaugmentation, totalCoaugmentation_total_map]
    congr 1
    exact ((Functor.mapHomologicalComplexIdIso (X.Sheaf C) (.up ℕ)).inv ≫
      (toGodement C X).mapHomologicalComplex (.up ℕ)).naturality f

/-- In each degree the augmentation is the map to the Godement sheaf followed by the inclusion
of the resolution-degree-zero summand. -/
@[simp]
lemma toGodementTotal_app_f (K : CochainComplex (X.Sheaf C) ℕ) (q : ℕ) :
    ((toGodementTotal C X).app K).f q =
      (toGodement C X).app (K.X q) ≫
        ((godementBicomplex C X).obj K).ιTotal (.up ℕ) 0 q q (zero_add q) := by
  rw [toGodementTotal, totalCoaugmentation_f]
  congr 1
  simp [toGodementColumn]

/-- A term of the Godement total is the coproduct of its finite diagonal of Godement terms. -/
def godementTotalXIsoCoproduct (K : CochainComplex (X.Sheaf C) ℕ) (n : ℕ) :
    ((godementTotal C X).obj K).X n ≅
      ∐ (((godementBicomplex C X).obj K).toGradedObject.mapObjFun
        (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) :=
  IsColimit.coconePointUniqueUpToIso
    (((godementBicomplex C X).obj K).toGradedObject.isColimitCofanMapObj _ n)
    (coproductIsCoproduct _)

/-- Each term of a totalized Godement resolution is flasque. Its degree `n` term is a finite
coproduct of Godement terms with indices `p + q = n`. -/
instance isFlasque_godementTotal_obj_X (K : CochainComplex (X.Sheaf C) ℕ) (n : ℕ) :
    (((godementTotal C X).obj K).X n).IsFlasque := by
  let I := ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) ⁻¹' {n}
  let F (i : I) := (((godementBicomplex C X).obj K).X i.val.1).X i.val.2
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have : HasFiniteBiproducts (X.Sheaf C) := Abelian.hasFiniteBiproducts
  have (i : I) : (F i).IsFlasque :=
    isFlasque_godementResolution_obj_X C X (K.X i.val.2) i.val.1
  exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _ _ _
    ((sheafToPresheaf _ C).mapIso
      (biproductIso F ≪≫ (godementTotalXIsoCoproduct C X K n).symm))
    (TopCat.Sheaf.isFlasque_piObj F)

/-- Exact coaugmented Godement rows make the total augmentation a quasi-isomorphism. -/
lemma quasiIso_toGodementTotal_app (K : CochainComplex (X.Sheaf C) ℕ)
    (hrows : ∀ q, QuasiIso ((toGodementResolution C X).app (K.X q))) :
    QuasiIso ((toGodementTotal C X).app K) := by
  apply quasiIso_totalCoaugmentation
  intro q
  have h : ((godementBicomplex C X).obj K).rowCoaugmentation
      (toGodementColumn K) (toGodementColumn_comp_d K) q =
        (toGodementResolution C X).app (K.X q) := by
    apply from_single_hom_ext
    simp [toGodementColumn]
  rw [h]
  exact hrows q

section BoundedBelow

variable (b : ℤ)

/-- The totalized Godement resolution starting in degree `b`. The input is restricted to
degrees at least `b`, resolved using the first-quadrant total, then placed back in the original
integer grading. In degree `n ≥ b` the summands have indices `p + q = n`, where `p ≥ 0` is
the Godement degree and `q ≥ b` is the original degree. Use
`HomologicalComplex.extendXIso` on the first-quadrant total of the restricted complex
to identify terms; `HomologicalComplex.extendMap_f` and `HomologicalComplex.extend_d_eq`
transport maps and differentials through these identifications. -/
abbrev godementTotalAt : CochainComplex (X.Sheaf C) ℤ ⥤ CochainComplex (X.Sheaf C) ℤ :=
  (ComplexShape.embeddingUpIntGE b).restrictionFunctor _ ⋙ godementTotal C X ⋙
    (ComplexShape.embeddingUpIntGE b).extendFunctor _

/-- The natural augmentation from the stupid truncation in degrees at least `b` into the
totalized Godement resolution at the same bound. -/
def toGodementTotalAt :
    (ComplexShape.embeddingUpIntGE b).stupidTruncFunctor (X.Sheaf C) ⟶ godementTotalAt C X b :=
  Functor.whiskerLeft ((ComplexShape.embeddingUpIntGE b).restrictionFunctor _)
    (Functor.whiskerRight (toGodementTotal C X)
      ((ComplexShape.embeddingUpIntGE b).extendFunctor _))

/-- The integer-graded augmentation is extension of the first-quadrant augmentation. -/
lemma toGodementTotalAt_app (K : CochainComplex (X.Sheaf C) ℤ) :
    (toGodementTotalAt C X b).app K =
      extendMap ((toGodementTotal C X).app
        (K.restriction (ComplexShape.embeddingUpIntGE b))) (ComplexShape.embeddingUpIntGE b) :=
  (rfl)

/-- At degree `b + q`, the truncation augmentation is the map to the Godement sheaf followed
by inclusion of the resolution-degree-zero summand, under the degreewise isomorphisms. -/
@[simp]
lemma toGodementTotalAt_app_f (K : CochainComplex (X.Sheaf C) ℤ) (q : ℕ) :
    let e := ComplexShape.embeddingUpIntGE b
    ((toGodementTotalAt C X b).app K).f (b + q) =
      (K.stupidTruncXIso e (ComplexShape.embeddingUpIntGE_f b q)).hom ≫
        (toGodement C X).app (K.X (b + q)) ≫
        ((godementBicomplex C X).obj (K.restriction e)).ιTotal (.up ℕ) 0 q q (zero_add q) ≫
        (((godementTotal C X).obj (K.restriction e)).extendXIso e
          (ComplexShape.embeddingUpIntGE_f b q)).inv := by
  dsimp only
  rw [toGodementTotalAt_app, extendMap_f _ _ (ComplexShape.embeddingUpIntGE_f b q),
    toGodementTotal_app_f, stupidTruncXIso_rfl]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- The Godement total vanishes below its starting degree. -/
instance isStrictlyGE_godementTotalAt (K : CochainComplex (X.Sheaf C) ℤ) :
    ((godementTotalAt C X b).obj K).IsStrictlyGE b := by
  let e := ComplexShape.embeddingUpIntGE b
  let L := (godementTotal C X).obj (K.restriction e)
  exact inferInstanceAs ((L.extend e).IsStrictlySupported e)

/-- Each term of the bounded-below totalized resolution is flasque. Below the chosen bound it
is zero, and in the remaining degrees it is a finite sum of flasque Godement terms. -/
instance isFlasque_godementTotalAt_obj_X (K : CochainComplex (X.Sheaf C) ℤ) (n : ℤ) :
    (((godementTotalAt C X b).obj K).X n).IsFlasque := by
  let e := ComplexShape.embeddingUpIntGE b
  by_cases hn : ∃ q, e.f q = n
  · obtain ⟨q, hq⟩ := hn
    exact @TopCat.Presheaf.IsFlasque.of_iso _ _ _ _ _
      ((sheafToPresheaf _ C).mapIso
        (((godementTotal C X).obj (K.restriction e)).extendXIso e hq).symm)
      (isFlasque_godementTotal_obj_X C X (K.restriction e) q)
  · have hz := isZero_extend_X ((godementTotal C X).obj (K.restriction e)) e n
      (fun q hq ↦ hn ⟨q, hq⟩)
    have hF : IsZero (((godementTotalAt C X b).obj K).X n).obj :=
      (sheafToPresheaf _ C).map_isZero hz
    exact ⟨fun _ ↦ (hF.obj _).epi _⟩

/-- The augmentation of the truncated complex into the Godement total is a quasi-isomorphism
when the coaugmented Godement rows of its restriction are quasi-isomorphisms.
For a complex already vanishing below `b`, `HomologicalComplex.ιStupidTrunc` identifies the
source with the original complex. -/
lemma quasiIso_toGodementTotalAt_app (K : CochainComplex (X.Sheaf C) ℤ)
    (hrows : ∀ q, QuasiIso ((toGodementResolution C X).app
      ((K.restriction (ComplexShape.embeddingUpIntGE b)).X q))) :
    QuasiIso ((toGodementTotalAt C X b).app K) := by
  let e := ComplexShape.embeddingUpIntGE b
  rw [toGodementTotalAt_app]
  exact (quasiIso_extendMap_iff _ _).2
    (quasiIso_toGodementTotal_app C X (K.restriction e) hrows)

/-- The totalized Godement resolution at a fixed bound takes values in the category of
bounded-below complexes. -/
abbrev godementTotalAtPlus : CochainComplex (X.Sheaf C) ℤ ⥤ CochainComplex.Plus (X.Sheaf C) :=
  (CochainComplex.plus _).lift (godementTotalAt C X b)
    (fun _ ↦ ⟨b, inferInstance⟩)

/-- For a complex vanishing below the chosen bound, the augmentation starts at the original
complex. The stupid truncation inclusion is invertible in this case. -/
def toGodementTotalAtPlus (K : CochainComplex.Plus (X.Sheaf C)) [K.obj.IsStrictlyGE b] :
    K ⟶ (godementTotalAtPlus C X b).obj K.obj :=
  ObjectProperty.homMk (inv (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE b)) ≫
    (toGodementTotalAt C X b).app K.obj)

/-- The bounded-below augmentation agrees with the truncation augmentation on its source. -/
@[reassoc (attr := simp)]
lemma ιStupidTrunc_comp_toGodementTotalAtPlus_hom (K : CochainComplex.Plus (X.Sheaf C))
    [K.obj.IsStrictlyGE b] :
    K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE b) ≫
      (toGodementTotalAtPlus C X b K).hom = (toGodementTotalAt C X b).app K.obj := by
  simp [toGodementTotalAtPlus]

/-- The augmentation commutes with maps between complexes sharing the chosen lower bound. -/
@[reassoc]
lemma toGodementTotalAtPlus_naturality {K L : CochainComplex.Plus (X.Sheaf C)}
    [K.obj.IsStrictlyGE b] [L.obj.IsStrictlyGE b] (f : K ⟶ L) :
    f ≫ toGodementTotalAtPlus C X b L =
      toGodementTotalAtPlus C X b K ≫ (godementTotalAtPlus C X b).map f.hom := by
  let e := ComplexShape.embeddingUpIntGE b
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  dsimp only [godementTotalAtPlus, ObjectProperty.lift, ObjectProperty.homMk]
  apply (cancel_epi (K.obj.ιStupidTrunc e)).1
  rw [← ιStupidTrunc_naturality_assoc f.hom e,
    ιStupidTrunc_comp_toGodementTotalAtPlus_hom,
    ιStupidTrunc_comp_toGodementTotalAtPlus_hom_assoc]
  exact (toGodementTotalAt C X b).naturality f.hom

/-- Exact coaugmented Godement rows make the augmentation from the original complex,
whose terms vanish below `b`, to its Godement total a quasi-isomorphism. -/
lemma quasiIso_toGodementTotalAtPlus_hom (K : CochainComplex.Plus (X.Sheaf C))
    [K.obj.IsStrictlyGE b]
    (hrows : ∀ q, QuasiIso ((toGodementResolution C X).app
      ((K.obj.restriction (ComplexShape.embeddingUpIntGE b)).X q))) :
    QuasiIso (toGodementTotalAtPlus C X b K).hom := by
  have := quasiIso_toGodementTotalAt_app C X b K.obj hrows
  rw [← quasiIso_iff_comp_left (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE b))]
  simpa only [ιStupidTrunc_comp_toGodementTotalAtPlus_hom] using this

end BoundedBelow

end TauCeti.Topology
