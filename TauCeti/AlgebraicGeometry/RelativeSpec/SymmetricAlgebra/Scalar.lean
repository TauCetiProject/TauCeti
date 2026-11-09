/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Tilde
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Module
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Scalar

/-!
# Affine coordinates of scalar multiplication on a linear spectrum

The affine comparison `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` identifies the scalar action
constructed on relative spectra with the polynomial scalar coaction of the symmetric algebra.
On a test scheme, the affine coordinate belonging to `m : M` is multiplied by the function
representing the scalar. This calculation connects the geometric action with the grading on
`Sym_R M`; it applies to arbitrary modules, not only finite free ones.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The affine linear functional associated with a scalar multiple of a point is the scalar
function times the original functional. The test scheme need not be affine. -/
-- Apply before simp normalizes the semilinear map's scalar homomorphism.
@[simp↓]
theorem relativeSpecSymmetricAlgebraTildeHomEquiv_lift_comp_smul {T : Over (Spec R)}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
      (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) (m : M) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M T
        (lift a t ≫ relativeSpecSymmetricAlgebraSMul _) m =
      AffineSpace.homAsOverEquiv T a .unit * relativeSpecSymmetricAlgebraTildeHomEquiv M T t m := by
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_apply,
    relativeSpecSymmetricAlgebraTildeHomEquiv_apply,
    relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul]
  exact T.hom.tildeHomPushforwardEquiv_globalSectionsSmul M
    (relativeSpecSymmetricAlgebraHomEquiv _ T t) (AffineSpace.homAsOverEquiv T a .unit) m

/-- In affine coordinates, scalar multiplication on the relative spectrum multiplies every
linear generator by the corresponding global function. -/
-- Apply before simp expands the underlying morphism of the product lift.
@[simp↓]
theorem relativeSpecSymmetricAlgebraTildeIso_lift_comp_smul_appTop_ι {T : Over (Spec R)}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
      (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) (m : M) :
    ((lift a t ≫ relativeSpecSymmetricAlgebraSMul _).left ≫
        (relativeSpecSymmetricAlgebraTildeIso M).hom.left).appTop
        ((Scheme.ΓSpecIso _).inv (SymmetricAlgebra.ι R M m)) =
      AffineSpace.homAsOverEquiv T a .unit *
        (t.left ≫ (relativeSpecSymmetricAlgebraTildeIso M).hom.left).appTop
          ((Scheme.ΓSpecIso _).inv (SymmetricAlgebra.ι R M m)) := by
  rw [← relativeSpecSymmetricAlgebraTildeHomEquiv_eq_appTop,
    relativeSpecSymmetricAlgebraTildeHomEquiv_lift_comp_smul,
    relativeSpecSymmetricAlgebraTildeHomEquiv_eq_appTop]

/-- Under the affine comparison, the comorphism of a scalar multiple is obtained by
specializing the polynomial scalar coaction at the scalar function. This identity holds on the
entire symmetric algebra, not just its degree-one generators. -/
theorem relativeSpecSymmetricAlgebraTildeIso_lift_comp_smul_appTop {T : Over (Spec R)}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
      (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) :
    ((Scheme.ΓSpecIso _).inv ≫
      ((lift a t ≫ relativeSpecSymmetricAlgebraSMul _).left ≫
        (relativeSpecSymmetricAlgebraTildeIso M).hom.left).appTop).hom =
      (Polynomial.eval₂RingHom
        ((Scheme.ΓSpecIso _).inv ≫
          (t.left ≫ (relativeSpecSymmetricAlgebraTildeIso M).hom.left).appTop).hom
        (AffineSpace.homAsOverEquiv T a .unit)).comp
          (SymmetricAlgebra.scalarCoaction R M).toRingHom := by
  let F := (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
    (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))
  let e : F ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver M) :=
    (MorphismProperty.Over.forget _ _ _).map (relativeSpecSymmetricAlgebraTildeIso M).hom
  have scalars (s : T ⟶ F) (r : R) :
      ((Scheme.ΓSpecIso _).inv ≫ (s.left ≫ e.left).appTop).hom
          (algebraMap R (SymmetricAlgebra R M) r) =
        ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom r := by
    have hs : (s.left ≫ e.left) ≫ (specSymmetricAlgebraOver M).hom = T.hom :=
      Over.w (s ≫ e)
    have hs' : (s.left ≫ e.left) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))) = T.hom := hs
    have hc := (Scheme.Hom.comp_appTop (s.left ≫ e.left)
      (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))))).symm.trans
        (congrArg Scheme.Hom.appTop hs')
    have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)))) r
    exact (congrArg (s.left ≫ e.left).appTop hn).trans
      (ConcreteCategory.congr_hom hc ((Scheme.ΓSpecIso R).inv r))
  apply SymmetricAlgebra.ringHom_ext
  · ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
    exact (scalars (lift a t ≫ relativeSpecSymmetricAlgebraSMul _) r).trans (scalars t r).symm
  · intro m
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      SymmetricAlgebra.scalarCoaction_ι, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_monomial, pow_one]
    exact (relativeSpecSymmetricAlgebraTildeIso_lift_comp_smul_appTop_ι M a t m).trans
      (mul_comm _ _)

end

end TauCeti.AlgebraicGeometry
