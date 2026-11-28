/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.TateModule.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic

/-!
# Scheme-theoretic torsion levels of an abelian variety

The points of the scheme-theoretic torsion over the separable closure form the corresponding
torsion subgroup of the abelian variety's geometric points. These identifications intertwine
the multiplication transitions and maps of abelian varieties.
They use the group of points of a scheme-theoretic kernel via
`TauCeti.GroupScheme.torsionPointsMulEquiv`.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K]

/-- The points of the scheme-theoretic `ℓ ^ n`-torsion over the separable closure form the
`n`-th torsion level of the Tate module. -/
noncomputable def tateModuleLevelEquiv (A : AbelianVariety K) (ℓ n : ℕ) :
    Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) ⟶
      (GroupScheme.torsion (CommGrp.mk A.toOver) ((ℓ : ℤ) ^ n)).X) ≃+
        TateModuleLevel ℓ A.geometricPoints n := by
  let Z := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))
  have h : (zpowGroupHom ((ℓ : ℤ) ^ n) : (Z ⟶ A.toOver) →* _).ker =
      (AddSubgroup.torsionBy A.geometricPoints ((ℓ ^ n : ℕ) : ℤ)).toSubgroup' := by
    rw [Int.natCast_pow]
    ext x
    -- Integer scalar multiplication on the additive point group is exponentiation on points.
    simp only [MonoidHom.mem_ker, zpowGroupHom_apply, AddSubgroup.mem_toSubgroup']
    exact Additive.ofMul.injective.eq_iff.symm
  exact ((GroupScheme.torsionPointsMulEquiv (CommGrp.mk A.toOver) ((ℓ : ℤ) ^ n) Z).trans
    (MulEquiv.subgroupCongr h)).toAdditive

/-- The comparison sends each torsion point to its image in the abelian variety. -/
@[simp]
theorem coe_tateModuleLevelEquiv_apply (A : AbelianVariety K) (ℓ n : ℕ)
    (x : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) ⟶
      (GroupScheme.torsion (CommGrp.mk A.toOver) ((ℓ : ℤ) ^ n)).X)) :
    (A.tateModuleLevelEquiv ℓ n x : A.geometricPoints).toMul =
      x.toMul ≫ GroupScheme.torsionι (CommGrp.mk A.toOver) ((ℓ : ℤ) ^ n) := by
  unfold tateModuleLevelEquiv
  exact GroupScheme.coe_torsionPointsMulEquiv_apply (CommGrp.mk A.toOver)
    ((ℓ : ℤ) ^ n) _ x.toMul

/-- The point of the torsion scheme corresponding to a Tate level element maps to that
element in the abelian variety. -/
@[simp]
theorem tateModuleLevelEquiv_symm_apply_torsionι (A : AbelianVariety K) (ℓ n : ℕ)
    (x : TateModuleLevel ℓ A.geometricPoints n) :
    ((A.tateModuleLevelEquiv ℓ n).symm x).toMul ≫
      GroupScheme.torsionι (CommGrp.mk A.toOver) ((ℓ : ℤ) ^ n) =
        (x : A.geometricPoints).toMul := by
  rw [← coe_tateModuleLevelEquiv_apply, AddEquiv.apply_symm_apply]

/-- The transition on Tate levels is the map on points induced by multiplication by `ℓ` on
the torsion schemes. -/
theorem tateModuleLevelEquiv_symm_transition (A : AbelianVariety K) (ℓ n : ℕ)
    (x : TateModuleLevel ℓ A.geometricPoints (n + 1)) :
    ((A.tateModuleLevelEquiv ℓ n).symm (tateModuleTransition ℓ A.geometricPoints n x)).toMul =
      ((A.tateModuleLevelEquiv ℓ (n + 1)).symm x).toMul ≫
        eqToHom (congrArg (fun m : ℤ ↦ (GroupScheme.torsion (CommGrp.mk A.toOver) m).X)
          (pow_succ' (ℓ : ℤ) n)) ≫
        GroupScheme.torsionMulBy (CommGrp.mk A.toOver) (ℓ : ℤ) ((ℓ : ℤ) ^ n) := by
  apply GroupScheme.torsion_hom_ext (CommGrp.mk A.toOver)
  simp only [Category.assoc, GroupScheme.torsionMulBy_torsionι, GrpObj.comp_zpow,
    GroupScheme.eqToHom_torsionι _ (pow_succ' (ℓ : ℤ) n), tateModuleLevelEquiv_symm_apply_torsionι]
  simp only [tateModuleTransition_apply, toMul_nsmul, zpow_natCast]

/-- Projection of an induced Tate map is the point map of the induced morphism between
scheme-theoretic torsion levels. -/
theorem tateModuleLevelEquiv_symm_proj_tateMap {A B : AbelianVariety K}
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (f : A ⟶ B) (x : A.tateModule ℓ) :
    ((B.tateModuleLevelEquiv ℓ n).symm (TateModule.proj n (tateMap ℓ f x))).toMul =
      ((A.tateModuleLevelEquiv ℓ n).symm (TateModule.proj n x)).toMul ≫
        GroupScheme.torsionMap f.hom ((ℓ : ℤ) ^ n) := by
  apply GroupScheme.torsion_hom_ext (CommGrp.mk B.toOver)
  rw [Category.assoc, GroupScheme.torsionMap_ι, ← Category.assoc]
  simp only [tateModuleLevelEquiv_symm_apply_torsionι, coe_proj_tateMap]
  rfl

end TauCeti.AlgebraicGeometry.AbelianVariety
