/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveMap.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.AlgebraicGeometry.LineBundle.LocalBasis
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Over

/-!
# Recovery of a line bundle from its morphism to projective space

The morphism defined by a generating family of sections pulls the twisting sheaf `𝒪(1)`
back to the original line bundle. The comparison carries every homogeneous coordinate
section to the section defining that coordinate.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Theorem 7.1.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (L : InvertibleSheaf X) {I R : Type u} [CommRing R]
  (s : I → Γ(L.obj, ⊤)) (c : R →+* Γ(X, ⊤))
  (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤)

private abbrev grading := MvPolynomial.homogeneousSubmodule I R

private theorem coordinate_mem (i : I) : MvPolynomial.X i ∈ grading (I := I) (R := R) 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i)

private abbrev coordinateOpen (i : I) : (Proj (grading (I := I) (R := R))).Opens :=
  Proj.basicOpen (grading (I := I) (R := R)) (MvPolynomial.X i)

private abbrev twist : (Proj (grading (I := I) (R := R))).Modules :=
  Proj.twistingSheaf (grading (I := I) (R := R)) 1

private abbrev target : (Proj (grading (I := I) (R := R))).Modules :=
  (pushforward (L.projectiveMap s c hcover)).obj L.obj

private def coordinateSection (V : (Proj (grading (I := I) (R := R))).Opens) (i : I) :
    Γ(twist (I := I) (R := R), V) :=
  Proj.toTwistingSheaf (grading (I := I) (R := R)) rfl V
    ⟨MvPolynomial.X i, coordinate_mem i⟩

private def sectionOver (V : (Proj (grading (I := I) (R := R))).Opens) (i : I) :
    Γ(L.target s c hcover, V) :=
  L.obj.presheaf.map (homOfLE le_top).op (s i)

private theorem map_sectionOver {V W : (Proj (grading (I := I) (R := R))).Opens}
    (j : V ⟶ W) (i : I) :
    (L.target s c hcover).presheaf.map j.op (L.sectionOver s c hcover W i) =
      L.sectionOver s c hcover V i := by
  -- Pushforward restrictions are the ambient module-sheaf restrictions.
  change L.obj.presheaf.map _ (L.obj.presheaf.map _ (s i)) = L.obj.presheaf.map _ (s i)
  calc
    _ = L.obj.presheaf.map (_ ≫ _) (s i) := (Functor.map_comp_apply _ _ _ (s i)).symm
    _ = _ := congrArg (fun f : _ ⟶ _ ↦ L.obj.presheaf.map f (s i))
      (Subsingleton.elim _ _)

private theorem map_coordinateSection {V W : (Proj (grading (I := I) (R := R))).Opens}
    (j : V ⟶ W) (i : I) :
    (twist (I := I) (R := R)).presheaf.map j.op (coordinateSection W i) =
      coordinateSection V i :=
  Proj.res_toTwistingSheaf (𝒜 := grading (I := I) (R := R)) rfl j _

private theorem coordinateSection_self (i : I)
    (V : (Proj (grading (I := I) (R := R))).Opens) (hi : V ≤ coordinateOpen i) :
    coordinateSection V i =
      Proj.twistingSheaf.chartGenerator 1 (MvPolynomial.X i) (coordinate_mem i) V hi := by
  apply Proj.twistingSheaf.ext
  intro x
  rw [coordinateSection, Proj.toTwistingSheaf_apply_apply,
    Proj.twistingSheaf.chartGenerator_apply]
  simp only [Int.toNat_one, Int.reduceNeg, pow_one]
  congr 1

private def localTwistMap (i : I) :
    (twist (I := I) (R := R)).over (coordinateOpen i) ⟶
    (L.target s c hcover).over (coordinateOpen i) :=
  (Proj.twistingSheaf.chartIso 1 (MvPolynomial.X i) (coordinate_mem i)
    (coordinateOpen i) le_rfl).inv ≫
    ((L.target s c hcover).over (coordinateOpen i)).unitHomEquiv.symm
      ((SheafOfModules.overSectionsEquiv (L.target s c hcover) (coordinateOpen i)).symm
        (L.sectionOver s c hcover (coordinateOpen i) i))

private theorem localTwistMap_app (i : I)
    (V : (Proj (grading (I := I) (R := R))).Opens) (hi : V ≤ coordinateOpen i)
    (m : Γ(twist (I := I) (R := R), V)) :
    (L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi))) m =
      (Proj.twistingSheaf.chartSectionsLinearEquiv 1 (MvPolynomial.X i)
        (coordinate_mem i) V hi).symm m • L.sectionOver s c hcover V i := by
  let W : Over (coordinateOpen (R := R) i) := Over.mk (homOfLE hi)
  let a := (Proj.twistingSheaf.chartIso 1 (MvPolynomial.X i) (coordinate_mem (R := R) i)
    (coordinateOpen i) le_rfl).inv
  let t := ((SheafOfModules.overSectionsEquiv (L.target s c hcover) (coordinateOpen i)).symm
    (L.sectionOver s c hcover (coordinateOpen i) i))
  let b := ((L.target s c hcover).over (coordinateOpen i)).unitHomEquiv.symm t
  let r := (Proj.twistingSheaf.chartSectionsLinearEquiv 1 (MvPolynomial.X i)
    (coordinate_mem i) V hi).symm m
  let rOver : ((Proj (grading (I := I) (R := R))).ringCatSheaf.over
      (coordinateOpen i)).obj.obj (op W) := r
  have hEval : t.eval (op W) = L.sectionOver s c hcover V i :=
    (SheafOfModules.overSectionsEquiv_symm_apply_eval (L.target s c hcover) (coordinateOpen i)
      (L.sectionOver s c hcover (coordinateOpen i) i) W).trans
      (L.map_sectionOver s c hcover (homOfLE hi) i)
  refine Eq.trans (b := rOver • t.eval (op W)) ?_ ?_
  · calc
      _ = b.val.app (op W) (a.val.app (op W) m) :=
        SheafOfModules.comp_val_app_apply a b (op W) m
      _ = b.val.app (op W) r :=
        congrArg (fun x ↦ b.val.app (op W) x) (Proj.twistingSheaf.chartIso_inv_app_apply
          1 (MvPolynomial.X i) (coordinate_mem i) (coordinateOpen i) le_rfl W m)
      _ = rOver • t.eval (op W) :=
        TauCeti.SheafOfModules.unitHomEquiv_symm_val_app t (op W) rOver
  · exact congrArg (fun z : Γ(L.target s c hcover, V) ↦ r • z) hEval

private theorem localTwistMap_self (i : I)
    (V : (Proj (grading (I := I) (R := R))).Opens) (hi : V ≤ coordinateOpen i) :
    (L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi)))
        (coordinateSection V i) = L.sectionOver s c hcover V i := by
  rw [L.localTwistMap_app, coordinateSection_self i V hi]
  have hgen : Proj.twistingSheaf.chartGenerator 1 (MvPolynomial.X i) (coordinate_mem i) V hi =
      Proj.twistingSheaf.chartSectionsLinearEquiv 1 (MvPolynomial.X i)
        (coordinate_mem i) V hi 1 := by
    rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
  rw [hgen, LinearEquiv.symm_apply_apply, one_smul]

private def coordinateRatio (i j : I) :
    Γ(Proj (grading (I := I) (R := R)), coordinateOpen i) :=
  Proj.awayToSection (grading (I := I) (R := R)) (MvPolynomial.X i)
    (HomogeneousLocalization.Away.mk (grading (I := I) (R := R)) (coordinate_mem i) 1
      (MvPolynomial.X j)
      (by simpa only [smul_eq_mul, mul_one] using coordinate_mem (R := R) j))

private theorem coordinateSection_eq_ratio_smul (i j : I) :
    coordinateSection (coordinateOpen (R := R) i) j = coordinateRatio (R := R) i j •
      Proj.twistingSheaf.chartGenerator 1 (MvPolynomial.X i) (coordinate_mem i)
        (coordinateOpen i) le_rfl :=
  Proj.twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator 1
    ⟨MvPolynomial.X j, coordinate_mem j⟩ (coordinate_mem i)

private theorem image_coordinateRatio (i j : I) :
    coordinateRatio (R := R) i j • L.sectionOver s c hcover (coordinateOpen i) i =
      L.sectionOver s c hcover (coordinateOpen i) j := by
  -- Scalars on the pushforward act through pullback along the morphism to projective space.
  change (L.projectiveMap s c hcover).app (coordinateOpen i) (coordinateRatio i j) •
    L.obj.presheaf.map (homOfLE (le_top :
      L.projectiveMap s c hcover ⁻¹ᵁ coordinateOpen i ≤ ⊤)).op (s i) = _
  simpa only [coordinateRatio, TauCeti.MvPolynomial.awayXRatio_def, sectionOver,
    coordinateOpen, grading] using
    L.projectiveMap_app_awayToSection_smul s c hcover i j

private theorem localTwistMap_coordinate (i j : I)
    (V : (Proj (grading (I := I) (R := R))).Opens) (hi : V ≤ coordinateOpen i) :
    (L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi)))
        (coordinateSection V j) = L.sectionOver s c hcover V j := by
  have h := congrArg ((L.target s c hcover).presheaf.map (homOfLE hi).op)
    (L.image_coordinateRatio s c hcover i j)
  have hc := congrArg ((twist (I := I) (R := R)).presheaf.map (homOfLE hi).op)
    (coordinateSection_eq_ratio_smul (R := R) i j)
  have hc' : coordinateSection V j =
      (Proj (grading (I := I) (R := R))).presheaf.map (homOfLE hi).op
        (coordinateRatio i j) •
        Proj.twistingSheaf.chartGenerator 1 (MvPolynomial.X i) (coordinate_mem i) V hi := by
    exact (map_coordinateSection (homOfLE hi) j).symm.trans
      (hc.trans ((Scheme.Modules.map_smul _ _ _ _).trans
        (congrArg (_ • ·) (Proj.twistingSheaf.res_chartGenerator _ _ _ _ _ (homOfLE hi)))))
  rw [L.localTwistMap_app, hc']
  rw [← Proj.twistingSheaf.chartSectionsLinearEquiv_apply,
    LinearEquiv.symm_apply_apply]
  exact (congrArg (fun z : Γ(L.target s c hcover, V) ↦
    (Proj (grading (I := I) (R := R))).presheaf.map (homOfLE hi).op
      (coordinateRatio i j) • z) (L.map_sectionOver s c hcover (homOfLE hi) i).symm).trans
    ((Scheme.Modules.map_smul _ _ _ _).symm.trans
      (h.trans (L.map_sectionOver s c hcover _ _)))

private theorem localTwistMap_compatible (i j : I)
    (V : (Proj (grading (I := I) (R := R))).Opens)
    (hi : V ≤ coordinateOpen i) (hj : V ≤ coordinateOpen j)
    (m : Γ(twist (I := I) (R := R), V)) :
    (L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi))) m =
      (L.localTwistMap s c hcover j).val.app (op (Over.mk (homOfLE hj))) m := by
  let e := Proj.twistingSheaf.chartSectionsLinearEquiv 1 (MvPolynomial.X i)
    (coordinate_mem i) V hi
  have hm : e.symm m • coordinateSection V i = m := by
    rw [coordinateSection_self i V hi]
    exact (Proj.twistingSheaf.chartSectionsLinearEquiv_apply ..).symm.trans
      (e.apply_symm_apply m)
  let f : Γ(twist (I := I) (R := R), V) →ₗ[Γ(Proj (grading (I := I) (R := R)), V)]
      Γ(L.target s c hcover, V) :=
    ((L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi)))).hom
  let g : Γ(twist (I := I) (R := R), V) →ₗ[Γ(Proj (grading (I := I) (R := R)), V)]
      Γ(L.target s c hcover, V) :=
    ((L.localTwistMap s c hcover j).val.app (op (Over.mk (homOfLE hj)))).hom
  -- The two slice morphisms act on the same sections over the common open.
  change f m = g m
  rw [← hm, _root_.map_smul, _root_.map_smul]
  exact congrArg (e.symm m • ·)
    ((L.localTwistMap_self s c hcover i V hi).trans
      (L.localTwistMap_coordinate s c hcover j i V hj).symm)

private def twistMap : twist (I := I) (R := R) ⟶ L.target s c hcover :=
  SheafOfModules.glueOfOpenCover (X := (Proj (grading (I := I) (R := R))).toTopCat)
    (twist (I := I) (R := R)) (L.target s c hcover) coordinateOpen
    (Proj.iSup_basicOpen_X_eq_top R I) (L.localTwistMap s c hcover)
    (L.localTwistMap_compatible s c hcover)

private theorem twistMap_app (i : I)
    (V : (Proj (grading (I := I) (R := R))).Opens) (hi : V ≤ coordinateOpen i)
    (m : Γ(twist (I := I) (R := R), V)) :
    (L.twistMap s c hcover).app V m =
      (L.localTwistMap s c hcover i).val.app (op (Over.mk (homOfLE hi))) m :=
  SheafOfModules.glueOfOpenCover_app (X := (Proj (grading (I := I) (R := R))).toTopCat)
    (twist (I := I) (R := R)) (L.target s c hcover) coordinateOpen
    (Proj.iSup_basicOpen_X_eq_top R I) (L.localTwistMap s c hcover)
    (L.localTwistMap_compatible s c hcover) i V hi m

private theorem twistMap_coordinate
    (V : (Proj (grading (I := I) (R := R))).Opens) (j : I) :
    (L.twistMap s c hcover).app V (coordinateSection V j) =
      L.sectionOver s c hcover V j := by
  apply (L.target s c hcover).isSheaf.section_ext
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((Proj.iSup_basicOpen_X_eq_top R I).ge
    (Opens.mem_top x))
  let W := V ⊓ coordinateOpen (R := R) i
  let p : W ⟶ V := homOfLE inf_le_left
  refine ⟨W, inf_le_left, ⟨hx, hi⟩, ?_⟩
  have hn : (L.target s c hcover).presheaf.map p.op
      ((L.twistMap s c hcover).app V (coordinateSection V j)) =
      (L.twistMap s c hcover).app W
        ((twist (I := I) (R := R)).presheaf.map p.op (coordinateSection V j)) :=
    ((L.twistMap s c hcover).mapPresheaf.naturality_apply p.op (coordinateSection V j)).symm
  rw [hn, map_coordinateSection, L.map_sectionOver,
    L.twistMap_app s c hcover i W inf_le_right,
    L.localTwistMap_coordinate s c hcover i j W inf_le_right]

private def pullbackTwistMap :
    (Scheme.Modules.pullback (L.projectiveMap s c hcover)).obj (twist (I := I) (R := R)) ⟶ L.obj :=
  ((pullbackPushforwardAdjunction (L.projectiveMap s c hcover)).homEquiv _ _).symm
    (L.twistMap s c hcover)

private theorem pullbackTwistMap_coordinate
    (V : (Proj (grading (I := I) (R := R))).Opens) (j : I) :
    (L.pullbackTwistMap s c hcover).app (L.projectiveMap s c hcover ⁻¹ᵁ V)
        ((L.projectiveMap s c hcover).pullbackSections (twist (I := I) (R := R)) V
          (coordinateSection V j)) =
      L.obj.presheaf.map (homOfLE le_top).op (s j) := by
  rw [← Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply]
  have he : (pullbackPushforwardAdjunction (L.projectiveMap s c hcover)).homEquiv _ _
      (L.pullbackTwistMap s c hcover) = L.twistMap s c hcover :=
    Equiv.apply_symm_apply _ _
  exact (congrArg (fun f : twist (I := I) (R := R) ⟶ L.target s c hcover ↦
    f.app V (coordinateSection V j)) he).trans (L.twistMap_coordinate s c hcover V j)

private theorem isIso_pullbackTwistMap : IsIso (L.pullbackTwistMap s c hcover) := by
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (Proj (grading (I := I) (R := R))) (twist (I := I) (R := R)) :=
    Proj.isInvertible_twistingSheaf_of_iSup_eq_top MvPolynomial.X
      coordinate_mem (Proj.iSup_basicOpen_X_eq_top R I) 1
  refine Scheme.Modules.isIso_of_forall_exists_bijective_smul
    (L.pullbackTwistMap s c hcover) fun x ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
  let V := L.projectiveMap s c hcover ⁻¹ᵁ coordinateOpen (R := R) i
  have hV : V = L.obj.nonvanishingLocus (s i) := L.projectiveMap_preimage_basicOpen s c hcover i
  refine ⟨V, hV.symm ▸ hi,
    (L.projectiveMap s c hcover).pullbackSections (twist (I := I) (R := R))
      (coordinateOpen i) (coordinateSection (coordinateOpen i) i), fun W j ↦ ?_⟩
  rw [L.pullbackTwistMap_coordinate]
  have h := (Scheme.Modules.le_nonvanishingLocus_iff (s i) V.leTop).mp hV.le W j
  simpa only [← Functor.map_comp_apply, ← op_comp,
    Subsingleton.elim (j ≫ V.leTop) (j ≫ homOfLE (le_top : V ≤ ⊤))] using h

/-- Pulling `𝒪(1)` back along the morphism defined by a generating family of sections
recovers the original line bundle. -/
def projectiveMapPullbackTwistingSheafIso :
    (Scheme.Modules.pullback (L.projectiveMap s c hcover)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I R) 1) ≅ L.obj :=
  have := L.isIso_pullbackTwistMap s c hcover
  asIso (L.pullbackTwistMap s c hcover)

/-- The recovery isomorphism sends each pulled-back homogeneous coordinate to its defining
section, restricted to the inverse image of the open subset in question. -/
@[simp]
theorem projectiveMapPullbackTwistingSheafIso_hom_coordinate
    (V : (Proj (MvPolynomial.homogeneousSubmodule I R)).Opens) (j : I) :
    (L.projectiveMapPullbackTwistingSheafIso s c hcover).hom.app
        (L.projectiveMap s c hcover ⁻¹ᵁ V)
        ((L.projectiveMap s c hcover).pullbackSections
          (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I R) 1) V
          (Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule I R)
            (n := (1 : ℤ)) (j := 1) rfl V ⟨MvPolynomial.X j,
            (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
              (MvPolynomial.isHomogeneous_X R j)⟩)) =
      L.obj.presheaf.map (homOfLE (le_top : L.projectiveMap s c hcover ⁻¹ᵁ V ≤ ⊤)).op
        (s j) := by
  exact L.pullbackTwistMap_coordinate s c hcover V j

end TauCeti.AlgebraicGeometry.InvertibleSheaf
