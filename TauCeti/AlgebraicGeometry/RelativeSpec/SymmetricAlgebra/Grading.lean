/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.GlobalSectionsSmul
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Module

/-!
# The zero section and scalar multiplication of `Spec_X (Sym F)` on homogeneous functions

For a quasicoherent sheaf `F` on a scheme `X`, the regular functions of `𝕍(F) = Spec_X (Sym F)`
form the graded algebra `Sym F = ⨁ₙ Symⁿ F`. A point `t : T ⟶ 𝕍(F)` over `X`, for a scheme
`q : T ⟶ X`, pulls regular functions back along an algebra map `Sym F ⟶ q_* 𝒪_T`
(`relativeSpecHomIso`), and this algebra map extends the module map `F ⟶ q_* 𝒪_T` of `t`
(`relativeSpecHomIso_hom_app_app_eq_symmetricAlgebraLift`). This file computes the zero section
and the scalar multiplication of `𝕍(F)` (`addGrpObjRelativeSpecSymmetricAlgebra`,
`modObjRelativeSpecSymmetricAlgebra`) on the homogeneous summands `Symⁿ F`:

* pulling back along the scalar multiple `a • t` of `t` by a function `a : T ⟶ 𝔸¹_X` is, on
  `Symⁿ F`, pulling back along `t` and then multiplying by `aⁿ`
  (`ιTotal_relativeSpecHomIso_lift_comp_smul`);
* pulling back along the zero point `T ⟶ X ⟶ 𝕍(F)` vanishes on `Symⁿ F` for every `n ≥ 1`
  (`ιTotal_relativeSpecHomIso_zero`).

Over an affine open `Spec R ⊆ X` with `F = M~`, these are the classical formulas for the
comorphisms of the zero section and of the scalar multiplication of `Spec (Sym_R M)`: the
augmentation `Sym_R M → R`, which kills the elements of positive degree, and the coaction
`Sym_R M → R[t] ⊗_R Sym_R M` sending a homogeneous element `s` of degree `n` to `tⁿ ⊗ s`. In
particular, scalar multiplication by `𝔸¹_X` determines the grading of the regular functions of
`𝕍(F)`.

Both computations come from the algebra-level statement
`ιTotal_symmetricAlgebraLift_comp_globalSectionsSmul`: multiplying a module map
`φ : F ⟶ q_* 𝒪_T` by a global function `c` on `T` multiplies the algebra map `Sym F ⟶ q_* 𝒪_T`
extending it by `cⁿ` on `Symⁿ F`.

## Main declarations

* `TauCeti.AlgebraicGeometry.ιTotal_relativeSpecHomIso_lift_comp_smul`: scalar multiplication
  acts on regular functions of degree `n` by the `n`-th power of the scalar;
* `TauCeti.AlgebraicGeometry.ιTotal_relativeSpecHomIso_zero`: the zero section kills regular
  functions of positive degree.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Opposite MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

universe u

noncomputable section

variable {X : Scheme.{u}} {F : QuasicoherentSheaf X}

/-- **Scalar multiplication on homogeneous functions.** For a scheme `q : T ⟶ X` over `X`, a
function `a : T ⟶ 𝔸¹_X` and a point `t : T ⟶ Spec_X (Sym F)`, pulling a regular function of
degree `n`, that is a section of `Symⁿ F`, back along the scalar multiple `a • t` is pulling it
back along `t` and multiplying by `aⁿ`. -/
theorem ιTotal_relativeSpecHomIso_lift_comp_smul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) (n : ℕ) :
    ιTotal ((gradedSymmetricAlgebra X).obj F) n ≫
        (((relativeSpecHomIso X).hom.app (op ((symmetricAlgebra X).obj F))).app (op T)
          (lift a t ≫ relativeSpecSymmetricAlgebraSMul F)).hom.hom =
      ιTotal ((gradedSymmetricAlgebra X).obj F) n ≫
        (((relativeSpecHomIso X).hom.app (op ((symmetricAlgebra X).obj F))).app (op T)
          t).hom.hom ≫
          (Scheme.Modules.pushforward T.hom).map (Scheme.Modules.globalSectionsSmul _
            (AffineSpace.homAsOverEquiv T a .unit ^ n)) := by
  rw [relativeSpecHomIso_hom_app_app_eq_symmetricAlgebraLift,
    relativeSpecHomIso_hom_app_app_eq_symmetricAlgebraLift,
    relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul]
  exact ιTotal_symmetricAlgebraLift_comp_globalSectionsSmul T.hom _ _ n

open scoped AddMonObj in
/-- **The zero section on homogeneous functions.** For a scheme `q : T ⟶ X` over `X`, pulling a
regular function of positive degree `n + 1`, that is a section of `Symⁿ⁺¹ F`, back along the zero
point `T ⟶ X ⟶ Spec_X (Sym F)` gives zero. -/
theorem ιTotal_relativeSpecHomIso_zero (T : Over X) (n : ℕ) :
    ιTotal ((gradedSymmetricAlgebra X).obj F) (n + 1) ≫
        (((relativeSpecHomIso X).hom.app (op ((symmetricAlgebra X).obj F))).app (op T)
          (0 : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
            ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))))).hom.hom = 0 := by
  -- The module map of the zero point is zero, so it is unchanged by multiplication by the
  -- function `0`, which acts by `0ⁿ⁺¹ = 0` in degree `n + 1`.
  have hm : (Scheme.Modules.pushforward T.hom).map
      (Scheme.Modules.globalSectionsSmul (𝟙_ T.left.Modules) 0) = 0 := by
    rw [Scheme.Modules.globalSectionsSmul_zero, (Scheme.Modules.pushforward T.hom).map_zero]
  have h : relativeSpecSymmetricAlgebraHomEquiv F T 0 =
      relativeSpecSymmetricAlgebraHomEquiv F T 0 ≫ (Scheme.Modules.pushforward T.hom).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ T.left.Modules) 0) := by
    rw [hm, ← relativeSpecSymmetricAlgebraHomAddEquiv_apply, map_zero]
    -- the zero of the group of module maps `F ⟶ q_* 𝒪_T` is the zero morphism of `X.Modules`
    exact (zero_comp (C := X.Modules)).symm
  rw [relativeSpecHomIso_hom_app_app_eq_symmetricAlgebraLift]
  refine ((congrArg (fun φ ↦ ιTotal ((gradedSymmetricAlgebra X).obj F) (n + 1) ≫
    (symmetricAlgebraLift (B := T.hom.pushforwardStructureAlgebra) φ).hom.hom) h).trans
      (ιTotal_symmetricAlgebraLift_comp_globalSectionsSmul T.hom _ 0 (n + 1))).trans ?_
  refine (congrArg (fun a ↦ ιTotal ((gradedSymmetricAlgebra X).obj F) (n + 1) ≫
    (symmetricAlgebraLift (B := T.hom.pushforwardStructureAlgebra)
      (relativeSpecSymmetricAlgebraHomEquiv F T 0)).hom.hom ≫ (Scheme.Modules.pushforward T.hom).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ T.left.Modules) a))
          (zero_pow n.succ_ne_zero)).trans ?_
  -- `rw [hm]` cannot build its motive here, as the goal mixes the `X.Modules` and
  -- `SheafOfModules` category instances, so `hm` is applied as a term
  exact (congrArg (fun f ↦ ιTotal ((gradedSymmetricAlgebra X).obj F) (n + 1) ≫
    (symmetricAlgebraLift (B := T.hom.pushforwardStructureAlgebra)
      (relativeSpecSymmetricAlgebraHomEquiv F T 0)).hom.hom ≫ f) hm).trans
        ((congrArg (ιTotal ((gradedSymmetricAlgebra X).obj F) (n + 1) ≫ ·)
          (comp_zero (C := X.Modules))).trans (comp_zero (C := X.Modules)))

end

end TauCeti.AlgebraicGeometry
