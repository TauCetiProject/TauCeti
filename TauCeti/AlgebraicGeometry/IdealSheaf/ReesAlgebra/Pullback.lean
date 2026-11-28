/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Pullback of the Rees algebra of an ideal sheaf

Let `f : X ⟶ Y` be a morphism of schemes and `I ⊆ 𝒪_Y` an ideal sheaf. Pulling back the Rees
algebra `⨁ₙ Iⁿ` of `I` along `f` gives the graded quasi-coherent `𝒪_X`-algebra `f^* (⨁ₙ Iⁿ)`
with components `f^* Iⁿ`. In each degree, the comparison `f^* Iⁿ ⟶ Iⁿ.comap f` of
`Scheme.IdealSheafData.pullbackSheafHom`, followed by `Iⁿ.comap f = (I.comap f)ⁿ`
(`Scheme.IdealSheafData.comap_pow`), maps `f^* Iⁿ` to the degree-`n` component of the Rees
algebra of the inverse image ideal sheaf `I.comap f`. These maps preserve the unit and the
multiplication, since both are restrictions of those of the structure sheaves and `f^*` carries
the multiplication of `𝒪_Y` to that of `𝒪_X`. They therefore assemble into a morphism of graded
quasi-coherent algebras

`f^* (⨁ₙ Iⁿ) ⟶ ⨁ₙ (I.comap f)ⁿ`,

which is an epimorphism in every degree (`epi_reesAlgebraPullbackHom_hom_hom_hom`), since each
`pullbackSheafHom` is.

For a closed immersion `i : Z ⟶ Y` with ideal sheaf `I` and its base change `i' : Z' ⟶ Y'` along
`f : Y' ⟶ Y`, the ideal sheaf of `i'` is `I.comap f`. Pulling this morphism back along `i'` is the
algebra side of the comparison `C_{Z'} Y' ⟶ Z' ×_Z C_Z Y` of normal cones, and its surjectivity
in each degree is what makes that comparison a closed immersion.

## Main declarations

* `Scheme.IdealSheafData.reesPullbackComponent I f n`: the degree-`n` comparison
  `f^* Iⁿ ⟶ (I.comap f)ⁿ`, characterized by `reesPullbackComponent_sheafι`;
* `Scheme.IdealSheafData.reesAlgebraPullbackHom I f`: the morphism of graded quasi-coherent
  algebras `f^* (⨁ₙ Iⁿ) ⟶ ⨁ₙ (I.comap f)ⁿ`, with components computed by
  `reesAlgebraPullbackHom_hom_hom_hom`;
* `Scheme.IdealSheafData.epi_reesAlgebraPullbackHom_hom_hom_hom`: it is an epimorphism in each
  degree.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1 and Appendix B.6.
-/

public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)

/-- The degree-`n` comparison `f^* Iⁿ ⟶ (I.comap f)ⁿ` between the pullback of the Rees algebra of
`I` and the Rees algebra of `I.comap f`: the comparison `f^* Iⁿ ⟶ Iⁿ.comap f` of
`pullbackSheafHom`, followed by `Iⁿ.comap f = (I.comap f)ⁿ`. -/
def reesPullbackComponent (n : ℕ) :
    (Scheme.Modules.pullback f).obj (I ^ n).sheaf ⟶ (I.comap f ^ n).sheaf :=
  (I ^ n).pullbackSheafHom f ≫ eqToHom (congrArg sheaf (comap_pow I f n))

/-- The degree-`n` comparison is `pullbackSheafHom` for `Iⁿ`, followed by
`Iⁿ.comap f = (I.comap f)ⁿ`. -/
theorem reesPullbackComponent_def (n : ℕ) :
    I.reesPullbackComponent f n =
      (I ^ n).pullbackSheafHom f ≫ eqToHom (congrArg sheaf (comap_pow I f n)) :=
  (rfl)

/-- The degree-`n` comparison, followed by the inclusion `(I.comap f)ⁿ ⟶ 𝒪_X`, is the pullback of
the inclusion `Iⁿ ⟶ 𝒪_Y`, followed by `f^* 𝒪_Y ≅ 𝒪_X`. -/
@[reassoc, simp]
theorem reesPullbackComponent_sheafι (n : ℕ) :
    I.reesPullbackComponent f n ≫ (I.comap f ^ n).sheafι =
      (Scheme.Modules.pullback f).map (I ^ n).sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (eqToHom_sheafι (comap_pow I f n))).trans
      ((I ^ n).pullbackSheafHom_sheafι f))

/-- `reesPullbackComponent_sheafι`, stated with the inclusions read as morphisms to the monoidal
unit and with `f^* 𝒪_Y ≅ 𝒪_X` written as the unit comparison `η` of `f^*`. -/
@[reassoc]
private lemma reesPullbackComponent_sheafιUnit (n : ℕ) :
    I.reesPullbackComponent f n ≫ (I.comap f ^ n).sheafιUnit =
      (Scheme.Modules.pullback f).map (I ^ n).sheafιUnit ≫ η (Scheme.Modules.pullback f) := by
  rw [sheafιUnit_def, sheafιUnit_def, reesPullbackComponent_sheafι, Scheme.Modules.pullback_η]

/-- The degree-`n` comparison is an epimorphism. -/
instance epi_reesPullbackComponent (n : ℕ) : Epi (I.reesPullbackComponent f n) := by
  rw [reesPullbackComponent_def]
  infer_instance

/-- The degree-zero comparison carries the pulled-back unit of the Rees algebra of `I` to the unit
of the Rees algebra of `I.comap f`. -/
private lemma reesOne_reesPullbackComponent :
    ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map I.reesOne) ≫
        I.reesPullbackComponent f 0 = (I.comap f).reesOne := by
  rw [← cancel_mono (I.comap f ^ 0).sheafιUnit, reesOne_sheafιUnit]
  -- Pass the inclusion into `𝒪_X` through the comparison, onto the pulled-back unit `reesOne`.
  rw [Category.assoc, Category.assoc, reesPullbackComponent_sheafιUnit, ← Functor.map_comp_assoc,
    reesOne_sheafιUnit]
  -- What remains is `𝒪_X ≅ f^* 𝒪_Y` followed by its inverse `η`.
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Scheme.Modules.pullback_η, Iso.inv_hom_id]

/-- The comparisons carry the pulled-back multiplication of the Rees algebra of `I` to the
multiplication of the Rees algebra of `I.comap f`. -/
private lemma reesPullbackComponent_reesMul (i j : ℕ) :
    (I.reesPullbackComponent f i ⊗ₘ I.reesPullbackComponent f j) ≫ (I.comap f).reesMul i j =
      (inv (δ (Scheme.Modules.pullback f) (I ^ i).sheaf (I ^ j).sheaf) ≫
        (Scheme.Modules.pullback f).map (I.reesMul i j)) ≫ I.reesPullbackComponent f (i + j) := by
  rw [← cancel_mono (I.comap f ^ (i + j)).sheafιUnit, ← cancel_epi
    (δ (Scheme.Modules.pullback f) (I ^ i).sheaf (I ^ j).sheaf), Category.assoc, Category.assoc,
    reesMul_sheafιUnit, Category.assoc, IsIso.hom_inv_id_assoc]
  -- Right side: the pullback of `reesMul ≫ sheafιUnit`, followed by `η`.
  rw [reesPullbackComponent_sheafιUnit, ← Functor.map_comp_assoc, reesMul_sheafιUnit]
  -- Left side: the pulled-back inclusions, followed by `η ⊗ η`.
  rw [tensorHom_comp_tensorHom_assoc, reesPullbackComponent_sheafιUnit,
    reesPullbackComponent_sheafιUnit, ← tensorHom_comp_tensorHom_assoc]
  -- Naturality of `δ`, and compatibility of `η` with the multiplication of the unit.
  rw [δ_natural_assoc, Functor.map_comp_assoc, δ_comp_η_tensorHom_comp_leftUnitor_hom]

/-- The components of the pullback of the Rees algebra of `I` are the pullbacks `f^* Iⁿ`. -/
theorem pullback_obj_reesAlgebra_obj_X :
    ((GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra).obj.X =
      fun n ↦ (Scheme.Modules.pullback f).obj (I ^ n).sheaf := by
  funext n
  rw [GradedQuasicoherentAlgebra.pullback_obj_obj_X, reesAlgebra_obj_X]

/-- The unit of the pullback of the Rees algebra of `I` is the pullback of `reesOne`, preceded by
`𝒪_X ≅ f^* 𝒪_Y`. -/
private lemma one_pullback_reesAlgebra :
    ((GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra).obj.toMon.one =
      ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map I.reesOne) ≫
        eqToHom (congrFun (pullback_obj_reesAlgebra_obj_X I f) 0).symm := by
  rw [GradedQuasicoherentAlgebra.pullback_obj_one, one_reesAlgebra, Category.assoc]
  -- `one_reesAlgebra` transports into `reesAlgebra.obj.X 0`, while the pulled-back unit expects
  -- `reesAlgebra.obj.toMon.X 0`; these agree only by definition, so `rw` needs `erw` here.
  erw [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans]

/-- The homogeneous multiplication of the pullback of the Rees algebra of `I` is the pullback of
`reesMul`, preceded by the inverse tensor comparison of `f^*`. -/
private lemma mul_pullback_reesAlgebra (i j : ℕ) :
    ((GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra).obj.toMon.mul i j =
      (eqToHom (by rw [pullback_obj_reesAlgebra_obj_X]) :
        ((GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra).obj.X i ⊗
          ((GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra).obj.X j ⟶ _) ≫
        (inv (δ (Scheme.Modules.pullback f) (I ^ i).sheaf (I ^ j).sheaf) ≫
          (Scheme.Modules.pullback f).map (I.reesMul i j)) ≫
          eqToHom (congrFun (pullback_obj_reesAlgebra_obj_X I f) (i + j)).symm := by
  rw [GradedQuasicoherentAlgebra.pullback_obj_mul,
    ← Functor.eqToHom_conjugate_inv_δ_comp_map (Scheme.Modules.pullback f)
      (congrFun I.reesAlgebra_obj_X i).symm (congrFun I.reesAlgebra_obj_X j).symm
      (congrFun I.reesAlgebra_obj_X (i + j)).symm (I.reesMul i j)
      (I.reesAlgebra.obj.toMon.mul i j)
      (by rw [mul_reesAlgebra, TauCeti.eqToHom_tensorHom_eqToHom])]
  simp only [Category.assoc, eqToHom_trans, TauCeti.eqToHom_tensorHom_eqToHom, eqToHom_trans_assoc]
  -- The two sides differ only in writing the components as `obj.X` or as `obj.toMon.X`, which
  -- agree by definition.
  rfl

/-- **Pullback of the Rees algebra.** For a morphism of schemes `f : X ⟶ Y` and an ideal sheaf
`I` on `Y`, the morphism of graded quasi-coherent algebras `f^* (⨁ₙ Iⁿ) ⟶ ⨁ₙ (I.comap f)ⁿ` from
the pullback of the Rees algebra of `I` to the Rees algebra of the inverse image `I.comap f`,
given in degree `n` by `reesPullbackComponent` (`reesAlgebraPullbackHom_hom_hom_hom`). -/
def reesAlgebraPullbackHom :
    (GradedQuasicoherentAlgebra.pullback f).obj I.reesAlgebra ⟶ (I.comap f).reesAlgebra :=
  GradedQuasicoherentAlgebra.homMkOfEq (pullback_obj_reesAlgebra_obj_X I f)
    (I.comap f).reesAlgebra_obj_X (one_pullback_reesAlgebra I f) (I.comap f).one_reesAlgebra
    (mul_pullback_reesAlgebra I f) (I.comap f).mul_reesAlgebra (I.reesPullbackComponent f)
    (reesOne_reesPullbackComponent I f) (reesPullbackComponent_reesMul I f)

/-- In degree `n`, the morphism `reesAlgebraPullbackHom` is the comparison
`reesPullbackComponent`, up to the identifications of the components with `f^* Iⁿ` and
`(I.comap f)ⁿ`. -/
@[simp]
theorem reesAlgebraPullbackHom_hom_hom_hom (n : ℕ) :
    (I.reesAlgebraPullbackHom f).hom.hom.hom n =
      eqToHom (congrFun (pullback_obj_reesAlgebra_obj_X I f) n) ≫
        I.reesPullbackComponent f n ≫
          eqToHom (congrFun (I.comap f).reesAlgebra_obj_X n).symm :=
  GradedQuasicoherentAlgebra.homMkOfEq_hom_hom_hom _ _ _ _ _ _ _ _ _ n

/-- The morphism `reesAlgebraPullbackHom` is an epimorphism in every degree. -/
instance epi_reesAlgebraPullbackHom_hom_hom_hom (n : ℕ) :
    Epi ((I.reesAlgebraPullbackHom f).hom.hom.hom n) := by
  rw [reesAlgebraPullbackHom_hom_hom_hom]
  -- The transports `eqToHom` are stated in the category of graded components, where instance
  -- search does not find `IsIso (eqToHom _)`, so they are supplied through `eqToIso`.
  exact epi_comp' (IsIso.epi_of_iso (eqToIso (congrFun (pullback_obj_reesAlgebra_obj_X I f) n)).hom)
    (epi_comp' inferInstance
      (IsIso.epi_of_iso (eqToIso (congrFun (I.comap f).reesAlgebra_obj_X n).symm).hom))

end

end AlgebraicGeometry.Scheme.IdealSheafData
