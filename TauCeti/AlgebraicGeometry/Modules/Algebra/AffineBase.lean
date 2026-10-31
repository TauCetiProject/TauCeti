/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality

/-!
# Regular functions over an affine base as a module

For a scheme `q : T ⟶ Spec R`, the global sections of the function algebra `q_* 𝒪_T`, as an
`R`-module through Mathlib's `AlgebraicGeometry.moduleSpecΓFunctor`, are the global functions on
`T`, on which `R` acts through `q` (`moduleSpecΓPushforwardIso`). The identification is natural
in the scheme over `Spec R` (`moduleSpecΓPushforwardIso_hom_naturality`).

## Main declarations

* `TauCeti.AlgebraicGeometry.moduleSpecΓPushforwardIso`: the global sections of `q_* 𝒪_T`, as an
  `R`-module, are the global functions on `T`.

## References

* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ).
-/

public section

open CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The identification of the global sections of `q_* 𝒪_T` with the global functions on `T` is
`R`-linear, where `R` acts on global functions through `q : T ⟶ Spec R`. -/
private def moduleSpecΓPushforwardLinearEquiv (T : Over (Spec R)) :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) ≃ₗ[R]
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) where
  toFun x := T.hom.pushforwardStructureAlgebraΓRingEquiv.symm x
  map_add' := map_add T.hom.pushforwardStructureAlgebraΓRingEquiv.symm
  map_smul' r x := by
    -- `r` acts on global sections of `q_* 𝒪_T` through the structure map of the function
    -- algebra, which is pullback of functions along `q`. The two carriers agree only up to
    -- unfolding `moduleSpecΓFunctor`, so `x` is read as a section of the function algebra.
    have h : r • x = algebraMap Γ(Spec R, ⊤) Γ(T.hom.pushforwardStructureAlgebra.X, ⊤)
        ((Scheme.ΓSpecIso R).inv r) * (show Γ(T.hom.pushforwardStructureAlgebra.X, ⊤) from x) :=
      Algebra.smul_def ((Scheme.ΓSpecIso R).inv r)
        (show Γ(T.hom.pushforwardStructureAlgebra.X, ⊤) from x)
    erw [h]
    rw [map_mul, Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_algebraMap]
    exact (ModuleCat.restrictScalars.smul_def' ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom
      (M := ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) r _).symm
  invFun y := T.hom.pushforwardStructureAlgebraΓRingEquiv y
  left_inv := T.hom.pushforwardStructureAlgebraΓRingEquiv.apply_symm_apply
  right_inv := T.hom.pushforwardStructureAlgebraΓRingEquiv.symm_apply_apply

/-- For a scheme `q : T ⟶ Spec R`, the `R`-module of global sections of `q_* 𝒪_T` is the
module of global functions on `T`, on which `R` acts through `q`. The isomorphism is the
identification of the global sections of `q_* 𝒪_T` with the global functions on `T`. -/
def moduleSpecΓPushforwardIso (T : Over (Spec R)) :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) ≅
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) :=
  (moduleSpecΓPushforwardLinearEquiv T).toModuleIso

/-- The identification `moduleSpecΓPushforwardIso` is the identification of the global sections
of `q_* 𝒪_T` with the global functions on `T`. -/
lemma moduleSpecΓPushforwardIso_hom_apply (T : Over (Spec R))
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules))) :
    (moduleSpecΓPushforwardIso T).hom x = T.hom.pushforwardStructureAlgebraΓRingEquiv.symm x :=
  (rfl)

/-- The inverse of `moduleSpecΓPushforwardIso` is the identification of the global functions on
`T` with the global sections of `q_* 𝒪_T`. -/
lemma moduleSpecΓPushforwardIso_inv_apply (T : Over (Spec R))
    (y : (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :
    (moduleSpecΓPushforwardIso T).inv y = T.hom.pushforwardStructureAlgebraΓRingEquiv y :=
  (rfl)

/-- The identification `moduleSpecΓPushforwardIso` turns pullback of regular functions along a
morphism `g : T' ⟶ T` over `Spec R` into pullback of global functions along `g`. -/
lemma moduleSpecΓPushforwardIso_hom_naturality {T' T : Over (Spec R)} (g : T' ⟶ T)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules))) :
    (moduleSpecΓPushforwardIso T').hom (moduleSpecΓFunctor.map
        (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)).hom.hom x) =
      g.left.appTop ((moduleSpecΓPushforwardIso T).hom x) :=
  (congrArg T'.hom.pushforwardStructureAlgebraΓRingEquiv.symm
    (CommMon.sectionsAlgHom_apply
      (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)) ⊤ x).symm).trans
      (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom g.left (Over.w g) x)

end TauCeti.AlgebraicGeometry
