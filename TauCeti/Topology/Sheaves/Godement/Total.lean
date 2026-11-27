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
its Godement sheaf is monic, as it is for sheaves of modules.

The construction follows the Stacks Project, Lemma 20.30.2 (tag 0FKT), using the successive
cokernel model of the Godement resolution.

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

variable {C X}

private def toGodementColumn (K : CochainComplex (X.Sheaf C) ℕ) :
    K ⟶ ((godementBicomplex C X).obj K).X 0 where
  f q := (toGodement C X).app (K.X q)
  comm' q q' _ := ((toGodement C X).naturality (K.d q q')).symm

private lemma toGodementColumn_comp_d (K : CochainComplex (X.Sheaf C) ℕ) :
    toGodementColumn K ≫ ((godementBicomplex C X).obj K).d 0 1 = 0 := by
  ext1 q
  exact (toGodement C X).app_comp_resolution_obj_d_zero_one (K.X q)

variable (C X)

/-- The augmentation into the totalized Godement resolution, induced by the canonical map
from each term to its Godement sheaf in resolution degree zero. -/
def toGodementTotal : 𝟭 (CochainComplex (X.Sheaf C) ℕ) ⟶ godementTotal C X where
  app K := ((godementBicomplex C X).obj K).totalCoaugmentation
    (toGodementColumn K) (toGodementColumn_comp_d K)
  naturality K L f := by
    -- Write the two composite functors in their native total-complex form.
    change f ≫ _ = _ ≫ total.map ((godementBicomplex C X).map f) (.up ℕ)
    rw [comp_totalCoaugmentation, totalCoaugmentation_total_map]
    congr 1
    apply HomologicalComplex.hom_ext
    intro q
    simp only [comp_f, toGodementColumn, Functor.comp_map, flipFunctor_map_f_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.resolution_map_f,
      NatTrans.cosyzygyFunctor_zero_map]
    exact (toGodement C X).naturality (f.f q)

/-- In each degree the augmentation is the map to the Godement sheaf followed by the inclusion
of the resolution-degree-zero summand. -/
@[simp]
lemma toGodementTotal_app_f (K : CochainComplex (X.Sheaf C) ℕ) (q : ℕ) :
    ((toGodementTotal C X).app K).f q =
      (toGodement C X).app (K.X q) ≫
        ((godementBicomplex C X).obj K).ιTotal (.up ℕ) 0 q q (zero_add q) := by
  rw [toGodementTotal, totalCoaugmentation_f]
  rfl

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
    ((sheafToPresheaf _ C).mapIso ((biproduct.isoProduct F).symm ≪≫ biproduct.isoCoproduct F))
    (TopCat.Sheaf.isFlasque_piObj F)

/-- The augmentation into the Godement total is a quasi-isomorphism when the canonical map
from each sheaf to its Godement sheaf is monic. -/
lemma quasiIso_toGodementTotal_app [∀ F : X.Sheaf C, Mono ((toGodement C X).app F)]
    (K : CochainComplex (X.Sheaf C) ℕ) :
    QuasiIso ((toGodementTotal C X).app K) := by
  apply quasiIso_totalCoaugmentation
  intro q
  have h : ((godementBicomplex C X).obj K).rowCoaugmentation
      (toGodementColumn K) (toGodementColumn_comp_d K) q =
        (toGodementResolution C X).app (K.X q) := by
    apply from_single_hom_ext
    simp [toGodementColumn]
  rw [h]
  infer_instance

section BoundedBelow

variable (b : ℤ)

/-- The totalized Godement resolution starting in degree `b`. The input is restricted to
degrees at least `b`, resolved using the first-quadrant total, then placed back in the original
integer grading. In degree `n ≥ b` the summands have indices `p + q = n`, where `p ≥ 0` is
the Godement degree and `q ≥ b` is the original degree. -/
abbrev godementTotalAt : CochainComplex (X.Sheaf C) ℤ ⥤ CochainComplex (X.Sheaf C) ℤ :=
  (ComplexShape.embeddingUpIntGE b).restrictionFunctor _ ⋙ godementTotal C X ⋙
    (ComplexShape.embeddingUpIntGE b).extendFunctor _

/-- In degree `n = b + q`, the Godement total at bound `b` is the degree `q` term of the
first-quadrant Godement total of the restricted complex. -/
def godementTotalAtXIso (K : CochainComplex (X.Sheaf C) ℤ) {q : ℕ} {n : ℤ}
    (h : (ComplexShape.embeddingUpIntGE b).f q = n) :
    ((godementTotalAt C X b).obj K).X n ≅
      ((godementTotal C X).obj (K.restriction (ComplexShape.embeddingUpIntGE b))).X q :=
  extendXIso _ _ h

/-- The natural augmentation from the stupid truncation in degrees at least `b` into the
totalized Godement resolution at the same bound. -/
def toGodementTotalAt :
    (ComplexShape.embeddingUpIntGE b).stupidTruncFunctor (X.Sheaf C) ⟶ godementTotalAt C X b where
  app K := extendMap ((toGodementTotal C X).app (K.restriction (ComplexShape.embeddingUpIntGE b)))
    (ComplexShape.embeddingUpIntGE b)
  naturality K L f := by
    let e := ComplexShape.embeddingUpIntGE b
    -- The truncation map is restriction followed by extension.
    change extendMap (restrictionMap f e) e ≫ _ =
      _ ≫ extendMap ((godementTotal C X).map (restrictionMap f e)) e
    rw [← extendMap_comp, ← extendMap_comp]
    exact congrArg (extendMap · e) ((toGodementTotal C X).naturality (restrictionMap f e))

/-- At degree `b + q`, the truncation augmentation is the map to the Godement sheaf followed
by inclusion of the resolution-degree-zero summand, under the degreewise isomorphisms. -/
@[simp]
lemma toGodementTotalAt_app_f (K : CochainComplex (X.Sheaf C) ℤ) (q : ℕ) :
    let e := ComplexShape.embeddingUpIntGE b
    ((toGodementTotalAt C X b).app K).f (b + q) =
      (K.stupidTruncXIso e (ComplexShape.embeddingUpIntGE_f b q)).hom ≫
        (toGodement C X).app (K.X (b + q)) ≫
        ((godementBicomplex C X).obj (K.restriction e)).ιTotal (.up ℕ) 0 q q (zero_add q) ≫
        (godementTotalAtXIso C X b K (ComplexShape.embeddingUpIntGE_f b q)).inv := by
  dsimp only
  rw [toGodementTotalAt, extendMap_f _ _ (ComplexShape.embeddingUpIntGE_f b q),
    toGodementTotal_app_f, stupidTruncXIso_rfl, godementTotalAtXIso]
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
      ((sheafToPresheaf _ C).mapIso (godementTotalAtXIso C X b K hq).symm)
      (isFlasque_godementTotal_obj_X C X (K.restriction e) q)
  · have hz := isZero_extend_X ((godementTotal C X).obj (K.restriction e)) e n
      (fun q hq ↦ hn ⟨q, hq⟩)
    have hF : IsZero (((godementTotalAt C X b).obj K).X n).obj :=
      (sheafToPresheaf _ C).map_isZero hz
    exact ⟨fun _ ↦ (hF.obj _).epi _⟩

/-- The augmentation of the truncated complex into the Godement total is a quasi-isomorphism
when the canonical map from each sheaf to its Godement sheaf is monic.
For a complex already vanishing below `b`, `HomologicalComplex.ιStupidTrunc` identifies the
source with the original complex. -/
lemma quasiIso_toGodementTotalAt_app [∀ F : X.Sheaf C, Mono ((toGodement C X).app F)]
    (K : CochainComplex (X.Sheaf C) ℤ) :
    QuasiIso ((toGodementTotalAt C X b).app K) := by
  let e := ComplexShape.embeddingUpIntGE b
  -- The augmentation is obtained by extension of the first-quadrant augmentation.
  change QuasiIso (extendMap ((toGodementTotal C X).app (K.restriction e)) e)
  exact (quasiIso_extendMap_iff _ _).2 (quasiIso_toGodementTotal_app C X (K.restriction e))

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
  -- Compare the underlying maps after cancelling the truncation isomorphism.
  change f.hom ≫ inv (L.obj.ιStupidTrunc e) ≫ (toGodementTotalAt C X b).app L.obj =
    (inv (K.obj.ιStupidTrunc e) ≫ (toGodementTotalAt C X b).app K.obj) ≫
      (godementTotalAt C X b).map f.hom
  apply (cancel_epi (K.obj.ιStupidTrunc e)).1
  rw [← ιStupidTrunc_naturality_assoc f.hom e]
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc,
    ComplexShape.Embedding.stupidTruncFunctor_obj, ComplexShape.Embedding.stupidTruncFunctor_map]
    using (toGodementTotalAt C X b).naturality f.hom

/-- If the canonical map from each sheaf to its Godement sheaf is monic, the augmentation
from the original bounded-below complex to its Godement total is a quasi-isomorphism. -/
lemma quasiIso_toGodementTotalAtPlus_hom [∀ F : X.Sheaf C, Mono ((toGodement C X).app F)]
    (K : CochainComplex.Plus (X.Sheaf C))
    [K.obj.IsStrictlyGE b] : QuasiIso (toGodementTotalAtPlus C X b K).hom := by
  have := quasiIso_toGodementTotalAt_app C X b K.obj
  rw [← quasiIso_iff_comp_left (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE b))]
  simpa only [ιStupidTrunc_comp_toGodementTotalAtPlus_hom] using this

end BoundedBelow

end TauCeti.Topology
