/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections

/-!
# Local cohomology sheaves with module coefficients

Sheafifying the module-valued presheaf `W ↦ Extⁿ(Q_S(W), F)` defines the local
cohomology sheaf `𝓗_Sⁿ(F)`. In degree zero this is canonically the supported-section
sheaf `Γ_S(F)`, naturally in the coefficient sheaf. Local cohomology has zero stalks
outside `S`. These constructions keep the scalar action on local cohomology, rather
than replacing its coefficients by abelian groups.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)

noncomputable section

/-- The local cohomology sheaf `𝓗_Sⁿ(F)`, defined by sheafifying the module-valued supported
cohomology presheaf. -/
abbrev supportedModuleHSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
    (F.supportedModuleHPresheaf S n)

/-- The functor of module-valued local cohomology in degree `n`.

The body is exposed so its objects are definitionally the local cohomology sheaves;
its action on morphisms is characterized by `supportedModuleHPresheafFunctor_map_toSheafify`. -/
@[expose]
def supportedModuleHSheafFunctor (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  supportedModuleHPresheafFunctor S n ⋙ presheafToSheaf _ _

@[simp]
lemma supportedModuleHSheafFunctor_obj (n : ℕ) :
    (supportedModuleHSheafFunctor S n).obj F = F.supportedModuleHSheaf S n :=
  (rfl)

/-- The local cohomology map is induced by the supported cohomology presheaf map through
sheafification, in every degree. -/
@[simp, reassoc]
lemma supportedModuleHPresheafFunctor_map_toSheafify (n : ℕ)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) :
    (supportedModuleHPresheafFunctor S n).map f ≫
        toSheafify (Opens.grothendieckTopology X) (G.supportedModuleHPresheaf S n) =
      toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf S n) ≫
        ((supportedModuleHSheafFunctor S n).map f).hom :=
  toSheafify_naturality _ _

/-- The degree-zero local cohomology sheaf is the sheaf of supported sections. -/
def supportedModuleHSheafZeroIso : F.supportedModuleHSheaf S 0 ≅ F.supportedSubmoduleSheaf S :=
  (presheafToSheaf _ _).mapIso (F.supportedModuleHPresheafZeroIso S) ≪≫
    (sheafificationIso (F.supportedSubmoduleSheaf S)).symm

/-- The degree-zero comparison is induced by the sectionwise Ext-Hom equivalences through the
canonical sheafification map. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedModuleHSheafZeroIso_hom :
    toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf S 0) ≫
        (F.supportedModuleHSheafZeroIso S).hom.hom =
      (F.supportedModuleHPresheafZeroIso S).hom := by
  simp [supportedModuleHSheafZeroIso]

/-- The degree-zero comparison is natural in the coefficient sheaf. -/
@[reassoc]
lemma supportedModuleHSheafZeroIso_hom_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) :
    (supportedModuleHSheafFunctor S 0).map f ≫ (G.supportedModuleHSheafZeroIso S).hom =
      (F.supportedModuleHSheafZeroIso S).hom ≫ (supportedSubmoduleFunctor S).map f := by
  let α : F.supportedModuleHPresheaf S 0 ⟶ G.supportedModuleHPresheaf S 0 :=
    (supportedModuleHPresheafFunctor S 0).map f
  let β : F.supportedSubmoduleSheaf S ⟶ G.supportedSubmoduleSheaf S :=
    (supportedSubmoduleFunctor S).map f
  -- Give the maps their concrete source objects before using sheafification's
  -- universal property; the functor object identifications are definitional.
  change (presheafToSheaf _ _).map α ≫ (G.supportedModuleHSheafZeroIso S).hom =
    (F.supportedModuleHSheafZeroIso S).hom ≫ β
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (G.supportedSubmoduleSheaf S).property
  -- Normalize the source objects and the forgetful functor's composition to
  -- apply the unit's naturality without unfolding the comparison isomorphisms.
  change toSheafify _ (F.supportedModuleHPresheaf S 0) ≫
      ((presheafToSheaf _ _).map α).hom ≫ (G.supportedModuleHSheafZeroIso S).hom.hom =
    toSheafify _ (F.supportedModuleHPresheaf S 0) ≫
      (F.supportedModuleHSheafZeroIso S).hom.hom ≫ β.hom
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, toSheafify_supportedModuleHSheafZeroIso_hom,
    toSheafify_supportedModuleHSheafZeroIso_hom_assoc]
  ext W x
  apply Subtype.ext
  change ((G.supportedModuleHPresheafZeroIso S).hom.app W
      (((supportedModuleHPresheafFunctor S 0).map f).app W x)).val =
    (((supportedSubmoduleFunctor S).map f).hom.app W
      ((F.supportedModuleHPresheafZeroIso S).hom.app W x)).val
  calc
    _ = (G.supportedModuleHZeroEquiv S W.unop
        (((supportedModuleHPresheafFunctor S 0).map f).app W x)).val :=
      coe_supportedModuleHPresheafZeroIso_hom_app_apply S G W _
    _ = f.hom.app W (F.supportedModuleHZeroEquiv S W.unop x) :=
      (congrArg (fun y ↦ (G.supportedModuleHZeroEquiv S W.unop y).val)
        (supportedModuleHPresheafFunctor_map_app_apply S 0 f W x)).trans
          (coe_supportedModuleHZeroEquiv_naturality_right S W.unop f x)
    _ = f.hom.app W ((F.supportedModuleHPresheafZeroIso S).hom.app W x).val :=
      congrArg (f.hom.app W) (coe_supportedModuleHPresheafZeroIso_hom_app_apply S F W x).symm
    _ = _ := (coe_supportedSubmoduleFunctor_map_hom_app_apply S f W _).symm

/-- Local cohomology with supports in `S` has zero stalks outside `S`. -/
theorem isZero_stalk_supportedModuleHSheaf_of_notMem {x : X} (hx : x ∉ S) (n : ℕ) :
    IsZero (TopCat.Presheaf.stalk (F.supportedModuleHSheaf S n).obj x) := by
  rw [TopCat.Presheaf.isZero_stalk_sheafify_iff, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  obtain ⟨W, hxW, c, rfl⟩ := (F.supportedModuleHPresheaf S n).exists_germ_eq t
  have hxV : x ∈ W ⊓ S.compl := ⟨hxW, hx⟩
  have : Subsingleton ((F.supportedModuleHPresheaf S n).obj (op (W ⊓ S.compl))) := by
    rw [F.supportedModuleHPresheaf_obj]
    exact F.subsingleton_supportedModuleH_of_le_compl S
      (inf_le_right : W ⊓ S.compl ≤ S.compl) n
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) x hxV]
  rw [Subsingleton.elim ((F.supportedModuleHPresheaf S n).map
    (homOfLE (inf_le_left : W ⊓ S.compl ≤ W)).op c) 0, map_zero]

end

end CategoryTheory.Sheaf
