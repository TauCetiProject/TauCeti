/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Point actions on the scalar extension of finite comodules

An `A`-valued point `g` of a bialgebra `H` over a commutative semiring `R` acts on the scalar
extension `A ⊗[R] M` of every comodule `M` by `TauCeti.Comodule.endOfPoint`. On finite comodules
these actions are natural in `M` and compatible with tensor products, so they form a monoidal
natural endomorphism of scalar extension (`TauCeti.FGComoduleCat.endOfPointNatTrans`). No antipode
is required.

A monoidal natural transformation between strong monoidal functors is compatible with the
comparisons of duals, through both the evaluation
(`CategoryTheory.NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate`) and the coevaluation
(`CategoryTheory.NatTrans.rightAdjointMate_comp_mapRightDualIso_inv_comp_app`). So on an object
`M` with a left dual `ᘁM`, the mate of the action on `ᘁM` is a two-sided inverse of the action on
`M`, and every point acts bijectively on `A ⊗[R] M`
(`TauCeti.FGComoduleCat.bijective_endOfPoint_of_hasLeftDual`). This is how rigidity of finite
comodules makes point actions invertible before any antipode is known.

## Main declarations

* `TauCeti.FGComoduleCat.endOfPointNatTrans`: the action of a point as a natural endomorphism of
  scalar extension of finite comodules, monoidal by
  `TauCeti.FGComoduleCat.isMonoidal_endOfPointNatTrans`.
* `TauCeti.FGComoduleCat.bijective_endOfPoint_of_hasLeftDual`: every point acts bijectively on a
  finite comodule with a left dual.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), Proposition 1.13 and the proof of
  Theorem 2.11.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v w x

section NatTrans

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- An `A`-valued point `g` of a bialgebra acts on the scalar extension of every finite comodule
by `TauCeti.Comodule.endOfPoint`; these actions form a natural endomorphism of scalar extension.
For a Hopf algebra this is the underlying natural transformation of the automorphism
`TauCeti.Tannaka.fgPointNatIsoHom R H A g`; here no antipode is required. -/
noncomputable def endOfPointNatTrans (g : H →ₐ[R] A) :
    scalarExtensionFunctor.{u, v, w, x} R H A ⟶ scalarExtensionFunctor R H A where
  app M := eqToHom (scalarExtensionFunctor_obj R H A M) ≫
    SemimoduleCat.ofHom (Comodule.endOfPoint M g) ≫
      eqToHom (scalarExtensionFunctor_obj R H A M).symm
  naturality M N f := by
    rw [scalarExtensionFunctor_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [← SemimoduleCat.ofHom_comp]
    exact congrArg SemimoduleCat.ofHom (Comodule.baseChange_comp_endOfPoint f.hom g).symm

/-- The components of `TauCeti.FGComoduleCat.endOfPointNatTrans` are the point actions,
transported to the objects chosen by the scalar-extension functor. -/
theorem endOfPointNatTrans_app (g : H →ₐ[R] A) (M : FGComoduleCat.{u, v, w} R H) :
    (endOfPointNatTrans R H A g).app M =
      eqToHom (scalarExtensionFunctor_obj R H A M) ≫
        SemimoduleCat.ofHom (Comodule.endOfPoint M g) ≫
          eqToHom (scalarExtensionFunctor_obj R H A M).symm :=
  (rfl)

variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The action of a point is a monoidal natural endomorphism of scalar extension: it is the
identity on the tensor unit and acts diagonally on tensor products. -/
instance isMonoidal_endOfPointNatTrans (g : H →ₐ[R] A) :
    NatTrans.IsMonoidal (endOfPointNatTrans.{u, v, u, u} R H A g) := by
  have hunit : (endOfPointNatTrans.{u, v, u, u} R H A g).app (𝟙_ (FGComoduleCat R H)) = 𝟙 _ := by
    rw [endOfPointNatTrans_app]
    -- The tensor unit carries the trivial coaction, on which every point acts as the identity.
    have h : Comodule.endOfPoint (𝟙_ (FGComoduleCat.{u, v, u} R H)) g = LinearMap.id :=
      Comodule.endOfPoint_trivial (V := R) g
    rw [h]
    simp
  have : Epi ((endOfPointNatTrans.{u, v, u, u} R H A g).app (𝟙_ (FGComoduleCat R H))) := by
    rw [hunit]
    infer_instance
  exact isMonoidal_of_endomorphism_components R H A (fun M ↦ Comodule.endOfPoint M g) _
    (endOfPointNatTrans_app R H A g) fun _ _ ↦ Comodule.endOfPoint_tensor g

end NatTrans

/-- Every point of a bialgebra acts bijectively on the scalar extension of a finite comodule with a
left dual. By compatibility of monoidal natural transformations with duals, through the
evaluation and through the coevaluation, the mate of the action on the left dual is a two-sided
inverse. -/
theorem bijective_endOfPoint_of_hasLeftDual {R : Type u} [CommSemiring R] {H : Type v}
    [Semiring H] [Bialgebra R H] {A : Type u} [CommSemiring A] [Algebra R A]
    (M : FGComoduleCat.{u, v, u} R H) [HasLeftDual M] (g : H →ₐ[R] A) :
    Function.Bijective (Comodule.endOfPoint M g) := by
  let F := scalarExtensionFunctor.{u, v, u, u} R H A
  let τ := endOfPointNatTrans.{u, v, u, u} R H A g
  let _ : HasRightDual (F.obj (ᘁM)) := F.mapHasRightDual (ᘁM)
  -- `M` is the right dual of `ᘁM` by definition (`CategoryTheory.rightDual_leftDual` is `rfl`),
  -- so compatibility with duals at `ᘁM` exhibits an inverse `r` of the component of `τ` at `M`.
  let r : F.obj M ⟶ F.obj M :=
    (F.mapRightDualIso (ᘁM)).hom ≫ (τ.app (ᘁM))ᘁ ≫ (F.mapRightDualIso (ᘁM)).inv
  have hr : τ.app M ≫ r = 𝟙 _ := by
    have key : τ.app M ≫ (F.mapRightDualIso (ᘁM)).hom ≫ (τ.app (ᘁM))ᘁ =
        (F.mapRightDualIso (ᘁM)).hom :=
      NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate τ (ᘁM)
    simp only [r, ← Category.assoc]
    rw [Category.assoc (τ.app M), key, Iso.hom_inv_id]
  have hr₂ : r ≫ τ.app M = 𝟙 _ := by
    have key : (τ.app (ᘁM))ᘁ ≫ (F.mapRightDualIso (ᘁM)).inv ≫ τ.app M =
        (F.mapRightDualIso (ᘁM)).inv :=
      NatTrans.rightAdjointMate_comp_mapRightDualIso_inv_comp_app τ (ᘁM)
    simp only [r, Category.assoc]
    rw [key, Iso.hom_inv_id]
  -- Transport the inverse to the explicit scalar extension `A ⊗[R] M`.
  let hM := scalarExtensionFunctor_obj R H A M
  let r' : A ⊗[R] M →ₗ[A] A ⊗[R] M := (eqToHom hM.symm ≫ r ≫ eqToHom hM).hom
  have transport {φ ψ : F.obj M ⟶ F.obj M} (h : φ ≫ ψ = 𝟙 _) (y : A ⊗[R] M) :
      (eqToHom hM.symm ≫ ψ ≫ eqToHom hM).hom ((eqToHom hM.symm ≫ φ ≫ eqToHom hM).hom y) = y := by
    have h' : (eqToHom hM.symm ≫ φ ≫ eqToHom hM) ≫ (eqToHom hM.symm ≫ ψ ≫ eqToHom hM) = 𝟙 _ := by
      simp [reassoc_of% h]
    simpa only [SemimoduleCat.hom_comp, LinearMap.comp_apply, SemimoduleCat.hom_id,
      LinearMap.id_apply] using LinearMap.congr_fun (congrArg SemimoduleCat.Hom.hom h') y
  have hτ : (eqToHom hM.symm ≫ τ.app M ≫ eqToHom hM).hom = Comodule.endOfPoint M g := by
    simp [τ, endOfPointNatTrans_app]
  have hleft (y : A ⊗[R] M) : r' (Comodule.endOfPoint M g y) = y := by
    simpa only [hτ] using transport hr y
  have hright (y : A ⊗[R] M) : Comodule.endOfPoint M g (r' y) = y := by
    simpa only [hτ] using transport hr₂ y
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

end TauCeti.FGComoduleCat
