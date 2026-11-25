/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra.Pullback
public import TauCeti.AlgebraicGeometry.NormalCone.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeSpec.ClosedImmersion

/-!
# Normal cones under base change

Let `i : X ⟶ Y` be a closed immersion with ideal sheaf `I`, let `f : Y' ⟶ Y` be any morphism, and
let `i' : X' ⟶ Y'` be the base change of `i` along `f`, with projection `g : X' ⟶ X`. The ideal
sheaf of `i'` is the inverse image `I.comap f` (`IdealSheafData.ker_eq_comap_of_isPullback`), so
the comparison `f^* (⨁ₙ Iⁿ) ⟶ ⨁ₙ (I.comap f)ⁿ` of Rees algebras
(`IdealSheafData.reesAlgebraPullbackHom`), pulled back along `i'`, is a morphism

`g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹`

from the pullback of the normal cone algebra of `i` to the normal cone algebra of `i'`, using
`g^* i^* ≅ (g ≫ i)^* = (i' ≫ f)^* ≅ i'^* f^*`. It is an epimorphism in every degree, since the Rees
comparison is. Taking relative spectra and using that relative spectra commute with base change
(`isPullback_relativeSpecPullbackFst`) gives the closed immersion of normal cones

`C_{X'} Y' ⟶ X' ×_X C_X Y`

over `X'` (Fulton, *Intersection Theory*, §6.1). For a regular immersion, `C_X Y` is the normal
bundle and this is the embedding of the normal cone into the pulled-back normal bundle used by
refined Gysin maps.

Normal cones in Tau Ceti are defined for immersions through the closed immersion `i.liftCoborder`
into the open `i.coborderRange`; for a closed immersion this open is all of `Y`
(`coborderRange_eq_top`), and the comparison is stated for closed immersions.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.reesAlgebraPullbackHomOfIsPullback h`: for a pullback square `h` of
  a closed immersion `j : X ⟶ U` along `fU : U' ⟶ U`, with base change `j' : X' ⟶ U'` and
  projection `g : X' ⟶ X`, the morphism of graded quasi-coherent algebras
  `g^* j^* (⨁ₙ (ker j)ⁿ) ⟶ j'^* (⨁ₙ (ker j')ⁿ)`, an epimorphism in every degree
  (`epi_reesAlgebraPullbackHomOfIsPullback_hom_hom_hom`).
* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebraPullbackHom h`: for a pullback square `h` of a
  closed immersion `i` along `f`, the comparison `g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹` of normal cone
  algebras, an epimorphism in every degree
  (`epi_normalConeAlgebraPullbackHom_hom_hom_hom`).
* `AlgebraicGeometry.Scheme.Hom.normalConeToPullback h`: the morphism of normal cones
  `C_{X'} Y' ⟶ X' ×_X C_X Y`, over `X'` (`normalConeToPullback_snd`), with
  `isClosedImmersion_normalConeToPullback`: it is a closed immersion.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §6.1.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

noncomputable section

section Rees

variable {X X' U U' : Scheme.{u}} {j : X ⟶ U} {j' : X' ⟶ U'} {g : X' ⟶ X} {fU : U' ⟶ U}
  [IsClosedImmersion j]

/-- For a pullback square `h` exhibiting `j' : X' ⟶ U'` as the base change of a closed immersion
`j : X ⟶ U` along `fU : U' ⟶ U`, with projection `g : X' ⟶ X`, the morphism of graded
quasi-coherent algebras `g^* j^* (⨁ₙ (ker j)ⁿ) ⟶ j'^* (⨁ₙ (ker j')ⁿ)`: the composite
`g^* j^* ≅ (g ≫ j)^* = (j' ≫ fU)^* ≅ j'^* fU^*` followed by the pullback along `j'` of the Rees
algebra comparison `fU^* (⨁ₙ (ker j)ⁿ) ⟶ ⨁ₙ ((ker j).comap fU)ⁿ`, and the identification
`(ker j).comap fU = ker j'` (`IdealSheafData.ker_eq_comap_of_isPullback`). -/
def reesAlgebraPullbackHomOfIsPullback (h : IsPullback j' g fU j) :
    (GradedQuasicoherentAlgebra.pullback g).obj
        ((GradedQuasicoherentAlgebra.pullback j).obj j.ker.reesAlgebra) ⟶
      (GradedQuasicoherentAlgebra.pullback j').obj j'.ker.reesAlgebra :=
  (GradedQuasicoherentAlgebra.pullbackComp g j).hom.app _ ≫ eqToHom (by rw [h.w]) ≫
    (GradedQuasicoherentAlgebra.pullbackComp j' fU).inv.app _ ≫
      (GradedQuasicoherentAlgebra.pullback j').map (j.ker.reesAlgebraPullbackHom fU) ≫
        eqToHom (by rw [IdealSheafData.ker_eq_comap_of_isPullback j h])

/-- The comparison `reesAlgebraPullbackHomOfIsPullback h` is the pullback along `j'` of the Rees
algebra comparison, between the identifications of the pullbacks and of the ideal sheaves. -/
theorem reesAlgebraPullbackHomOfIsPullback_def (h : IsPullback j' g fU j) :
    reesAlgebraPullbackHomOfIsPullback h =
      (GradedQuasicoherentAlgebra.pullbackComp g j).hom.app _ ≫ eqToHom (by rw [h.w]) ≫
        (GradedQuasicoherentAlgebra.pullbackComp j' fU).inv.app _ ≫
          (GradedQuasicoherentAlgebra.pullback j').map (j.ker.reesAlgebraPullbackHom fU) ≫
            eqToHom (by rw [IdealSheafData.ker_eq_comap_of_isPullback j h]) :=
  (rfl)

/-- The comparison `reesAlgebraPullbackHomOfIsPullback h` is an epimorphism in every degree: the
Rees algebra comparison is, pullback of modules preserves epimorphisms, and the other factors
are isomorphisms. -/
instance epi_reesAlgebraPullbackHomOfIsPullback_hom_hom_hom (h : IsPullback j' g fU j) (n : ℕ) :
    Epi ((reesAlgebraPullbackHomOfIsPullback h).hom.hom.hom n) := by
  have hmap : Epi (((GradedQuasicoherentAlgebra.pullback j').map
      (j.ker.reesAlgebraPullbackHom fU)).hom.hom.hom n) := by
    rw [GradedQuasicoherentAlgebra.pullback_map_hom_hom_hom]
    have : Epi ((j.ker.reesAlgebraPullbackHom fU).hom.hom.hom n) :=
      IdealSheafData.epi_reesAlgebraPullbackHom_hom_hom_hom j.ker fU n
    exact epi_comp'
      (IsIso.epi_of_iso (eqToIso (GradedQuasicoherentAlgebra.pullback_obj_obj_X j' _ n)).hom)
      (epi_comp' (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback j') _ _ _ _ this)
        (IsIso.epi_of_iso
          (eqToIso (GradedQuasicoherentAlgebra.pullback_obj_obj_X j' _ n).symm).hom))
  rw [reesAlgebraPullbackHomOfIsPullback_def]
  simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom,
    GradedObject.categoryOfGradedObjects_comp]
  infer_instance

end Rees

section ClosedImmersion

variable {X Y X' Y' : Scheme.{u}} {i : X ⟶ Y} {i' : X' ⟶ Y'} {g : X' ⟶ X} {f : Y' ⟶ Y}
  [IsClosedImmersion i] [IsClosedImmersion i']

/-- **Normal cone algebras under base change.** For a pullback square `h` exhibiting the closed
immersion `i' : X' ⟶ Y'` as the base change of the closed immersion `i : X ⟶ Y` along
`f : Y' ⟶ Y`, with projection `g : X' ⟶ X`, the morphism `g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹` from
the pullback of the normal cone algebra of `i` to that of `i'`, induced by the comparison of
Rees algebras (`reesAlgebraPullbackHomOfIsPullback`). -/
def normalConeAlgebraPullbackHom (h : IsPullback i' g f i) :
    (GradedQuasicoherentAlgebra.pullback g).obj i.normalConeAlgebra ⟶ i'.normalConeAlgebra :=
  eqToHom (by rw [normalConeAlgebra_def]) ≫
    reesAlgebraPullbackHomOfIsPullback (isPullback_liftCoborder h) ≫
      eqToHom (by rw [normalConeAlgebra_def])

/-- The comparison of normal cone algebras is the comparison of Rees algebras for the closed
immersions `liftCoborder`. -/
theorem normalConeAlgebraPullbackHom_def (h : IsPullback i' g f i) :
    normalConeAlgebraPullbackHom h =
      eqToHom (by rw [normalConeAlgebra_def]) ≫
        reesAlgebraPullbackHomOfIsPullback (isPullback_liftCoborder h) ≫
          eqToHom (by rw [normalConeAlgebra_def]) :=
  (rfl)

/-- The comparison of normal cone algebras is an epimorphism in every degree. -/
instance epi_normalConeAlgebraPullbackHom_hom_hom_hom (h : IsPullback i' g f i) (n : ℕ) :
    Epi ((normalConeAlgebraPullbackHom h).hom.hom.hom n) := by
  rw [normalConeAlgebraPullbackHom_def]
  simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom,
    GradedObject.categoryOfGradedObjects_comp]
  infer_instance

/-- The comparison of normal cone algebras on the underlying quasi-coherent algebras
`g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹`, where the pullback of the direct sum is identified with the
direct sum of the pullbacks. -/
def normalConeQuasicoherentAlgebraPullbackHom (h : IsPullback i' g f i) :
    (QuasicoherentAlgebra.pullback g).obj
        (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra) ⟶
      GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i'.normalConeAlgebra :=
  (GradedQuasicoherentAlgebra.pullbackToQuasicoherentAlgebraIso g).hom.app i.normalConeAlgebra ≫
    GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.map (normalConeAlgebraPullbackHom h)

/-- The comparison on the underlying quasi-coherent algebras is the direct sum of the graded
comparison, preceded by `g^* (⨁ₙ Aₙ) ≅ ⨁ₙ g^* Aₙ`. -/
theorem normalConeQuasicoherentAlgebraPullbackHom_def (h : IsPullback i' g f i) :
    normalConeQuasicoherentAlgebraPullbackHom h =
      (GradedQuasicoherentAlgebra.pullbackToQuasicoherentAlgebraIso g).hom.app
          i.normalConeAlgebra ≫
        GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.map (normalConeAlgebraPullbackHom h) :=
  (rfl)

/-- The comparison of normal cone algebras is a surjection of quasi-coherent algebras. -/
instance epi_normalConeQuasicoherentAlgebraPullbackHom (h : IsPullback i' g f i) :
    Epi (normalConeQuasicoherentAlgebraPullbackHom h).hom.hom.hom := by
  have : Epi (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.map
      (normalConeAlgebraPullbackHom h)).hom.hom.hom :=
    GradedQuasicoherentAlgebra.epi_toQuasicoherentAlgebra_map _ fun n _ ↦ inferInstance
  rw [normalConeQuasicoherentAlgebraPullbackHom_def]
  simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom]
  infer_instance

/-- **Normal cones under base change.** For a pullback square `h` exhibiting the closed immersion
`i' : X' ⟶ Y'` as the base change of the closed immersion `i : X ⟶ Y` along `f : Y' ⟶ Y`, with
projection `g : X' ⟶ X`, the morphism `C_{X'} Y' ⟶ X' ×_X C_X Y` of normal cones: the relative
spectrum of the comparison `g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹`, followed by the identification of
the relative spectrum of the pullback with the fibre product. It is a closed immersion
(`isClosedImmersion_normalConeToPullback`) over `X'` (`normalConeToPullback_snd`). -/
def normalConeToPullback (h : IsPullback i' g f i) :
    i'.normalCone ⟶ pullback i.normalConeToBase g :=
  CommMon.relativeSpecMap (normalConeQuasicoherentAlgebraPullbackHom h).hom ≫
    (isPullback_relativeSpecPullbackFst _ g).isoPullback.hom

/-- The morphism of normal cones is the relative spectrum of the comparison of algebras, followed
by the identification of the relative spectrum of the pullback with the fibre product. -/
theorem normalConeToPullback_def (h : IsPullback i' g f i) :
    normalConeToPullback h =
      CommMon.relativeSpecMap (normalConeQuasicoherentAlgebraPullbackHom h).hom ≫
        (isPullback_relativeSpecPullbackFst _ g).isoPullback.hom :=
  (rfl)

/-- The morphism of normal cones, followed by the projection to `C_X Y`, is the relative
spectrum of the comparison of algebras followed by the projection
`Spec_{X'} (g^* (⨁ₙ Iⁿ/Iⁿ⁺¹)) ⟶ C_X Y`. -/
@[reassoc]
theorem normalConeToPullback_fst (h : IsPullback i' g f i) :
    normalConeToPullback h ≫ pullback.fst _ _ =
      CommMon.relativeSpecMap (normalConeQuasicoherentAlgebraPullbackHom h).hom ≫
        relativeSpecPullbackFst _ g := by
  exact (Category.assoc _ _ _).trans (congrArg _ (IsPullback.isoPullback_hom_fst _))

/-- The morphism of normal cones lies over `X'`: followed by the projection to `X'` it is the
projection `C_{X'} Y' ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem normalConeToPullback_snd (h : IsPullback i' g f i) :
    normalConeToPullback h ≫ pullback.snd _ _ = i'.normalConeToBase := by
  exact (Category.assoc _ _ _).trans ((congrArg _ (IsPullback.isoPullback_hom_snd _)).trans
    (CommMon.relativeSpecMap_relativeSpecToBase _))

/-- **The normal cone of a base change embeds in the base change of the normal cone.** For a
pullback square of closed immersions, `C_{X'} Y' ⟶ X' ×_X C_X Y` is a closed immersion, since
`g^* (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ ⨁ₙ I'ⁿ/I'ⁿ⁺¹` is surjective. -/
instance isClosedImmersion_normalConeToPullback (h : IsPullback i' g f i) :
    IsClosedImmersion (normalConeToPullback h) := by
  rw [normalConeToPullback_def]
  have := CommMon.isClosedImmersion_relativeSpecMap_of_epi
    (normalConeQuasicoherentAlgebraPullbackHom h).hom
  -- Instance search fails on the iso factor of the unfolded composite, so both factors are named.
  have hI : IsClosedImmersion (isPullback_relativeSpecPullbackFst
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra)
        g).isoPullback.hom :=
    inferInstance
  exact @IsClosedImmersion.comp _ _ _ _ _ this hI

end ClosedImmersion

end

end AlgebraicGeometry.Scheme.Hom
