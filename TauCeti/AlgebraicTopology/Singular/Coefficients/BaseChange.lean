/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Flat base change of singular homology

Let `S` be a flat `R`-algebra. Extension of scalars `M ↦ S ⊗[R] M` is then an exact functor
`ModuleCat R ⥤ ModuleCat S` which preserves coproducts, so it commutes with singular homology
(`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`). Since it sends the coefficient
module `R` to `S ⊗[R] R ≅ S` (the unit isomorphism of the monoidal functor
`ModuleCat.extendScalars`), this gives the universal coefficient isomorphism for flat
coefficients,

`S ⊗[R] Hₙ(X; R) ≃ₗ[S] Hₙ(X; S)`

(`TopCat.singularHomologyBaseChangeEquiv`), natural in the space `X`: it intertwines the base
change of `f_* : Hₙ(X; R) → Hₙ(Y; R)` with `f_* : Hₙ(X; S) → Hₙ(Y; S)`
(`TopCat.singularHomologyBaseChangeEquiv_baseChange`). The simplicial version with coefficient
object `ULift R`, without the naturality, is `SSet.homologyExtendScalarsIso`.

The main example is `ℤ → k` for a field `k` of characteristic zero, which is flat because `k`
is torsion-free. If `Hₙ(X; ℤ)` is free of finite rank, then `Hₙ(X; k)` is finite-dimensional, and
the determinant over `k` of `𝟙 - f_*` for a self-map `f` of `X` is the image of the integral
determinant (`TopCat.det_id_sub_singularHomologyMap_eq_algebraMap`). Since `ℤ → k` is
injective, the two determinants vanish together. This is how an integral determinant condition
on the monodromy of a mapping torus is compared with its rational or real first Betti number.

## Main declarations

* `TopCat.singularHomologyBaseChangeEquiv`: `S ⊗[R] Hₙ(X; R) ≃ₗ[S] Hₙ(X; S)` for a flat
  `R`-algebra `S`.
* `TopCat.singularHomologyBaseChangeEquiv_baseChange`: its naturality in `X`.
* `TopCat.det_id_sub_singularHomologyMap_eq_algebraMap`: for a self-map `f` and `Hₙ(X; R)` free
  of finite rank, `det (𝟙 - f_*)` over `S` is the image of `det (𝟙 - f_*)` over `R`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A, the universal coefficient theorem for homology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped TensorProduct

universe w

namespace TopCat

variable {R S : Type w} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The isomorphism `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` in `ModuleCat S`, natural in `X`. -/
private def singularHomologyBaseChangeIso (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R) ⋙
        ModuleCat.extendScalars.{w, w, w} (algebraMap R S) ≅
      (singularHomologyFunctor (ModuleCat.{w} S) n).obj (ModuleCat.of S S) :=
  -- Extension of scalars along a flat algebra is exact, so it preserves homology.
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.flat_algebraMap_iff.2 ‹_›)
  Functor.singularHomologyFunctorObjCompIso _ _ n ≪≫
    (singularHomologyFunctor (ModuleCat.{w} S) n).mapIso
      (Functor.Monoidal.εIso (ModuleCat.extendScalars.{w, w, w} (algebraMap R S))).symm

variable (R S) in
/-- **Flat base change of singular homology**: for a flat `R`-algebra `S`, the universal
coefficient isomorphism `S ⊗[R] Hₙ(X; R) ≃ₗ[S] Hₙ(X; S)`. It is natural in `X`
(`TopCat.singularHomologyBaseChangeEquiv_baseChange`). -/
def singularHomologyBaseChangeEquiv (X : TopCat.{w}) (n : ℕ) :
    S ⊗[R] (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).obj X) ≃ₗ[S]
      ((singularHomologyFunctor (ModuleCat.{w} S) n).obj (ModuleCat.of S S)).obj X :=
  ((ModuleCat.extendScalarsAlgebraMapIso _).symm ≪≫
    (singularHomologyBaseChangeIso n).app X).toLinearEquiv

/-- **Naturality of flat base change**: for a continuous map `f : X ⟶ Y`, the isomorphism
`S ⊗[R] Hₙ(-; R) ≃ Hₙ(-; S)` carries the base change of `f_*` over `R` to `f_*` over `S`. -/
@[simp]
theorem singularHomologyBaseChangeEquiv_baseChange {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (x : S ⊗[R] (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).obj X)) :
    singularHomologyBaseChangeEquiv R S Y n
        ((((singularHomologyFunctor (ModuleCat.{w} R) n).obj
          (ModuleCat.of R R)).map f).hom.baseChange S x) =
      (((singularHomologyFunctor (ModuleCat.{w} S) n).obj (ModuleCat.of S S)).map f).hom
        (singularHomologyBaseChangeEquiv R S X n x) := by
  set g := ((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).map f
  have h₁ : (ModuleCat.extendScalarsAlgebraMapIso _).inv (g.hom.baseChange S x) =
      (ModuleCat.extendScalars (algebraMap R S)).map g
        ((ModuleCat.extendScalarsAlgebraMapIso _).inv x) := by
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      simp only [LinearMap.baseChange_tmul]
      rw [ModuleCat.extendScalarsAlgebraMapIso_inv_tmul,
        ModuleCat.extendScalarsAlgebraMapIso_inv_tmul]
      exact (ModuleCat.ExtendScalars.map_tmul _ g s m).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ := ConcreteCategory.congr_hom
    ((singularHomologyBaseChangeIso (S := S) n).hom.naturality f)
    ((ModuleCat.extendScalarsAlgebraMapIso _).inv x)
  rw [singularHomologyBaseChangeEquiv, singularHomologyBaseChangeEquiv, Iso.toLinearEquiv_apply,
    Iso.toLinearEquiv_apply]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h₁]
  exact h₂

/-- **Determinants under flat base change**: for a self-map `f` of `X` and `Hₙ(X; R)` free of
finite rank, the determinant of `𝟙 - f_*` on `Hₙ(X; S)` is the image in `S` of the determinant
of `𝟙 - f_*` on `Hₙ(X; R)`. -/
theorem det_id_sub_singularHomologyMap_eq_algebraMap {X : TopCat.{w}} (f : X ⟶ X) (n : ℕ)
    [Module.Free R (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).obj X)]
    [Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).obj X)] :
    (LinearMap.id -
        (((singularHomologyFunctor (ModuleCat.{w} S) n).obj (ModuleCat.of S S)).map f).hom).det =
      algebraMap R S (LinearMap.id -
        (((singularHomologyFunctor (ModuleCat.{w} R) n).obj
          (ModuleCat.of R R)).map f).hom).det := by
  set e := singularHomologyBaseChangeEquiv R S X n
  set g := ((singularHomologyFunctor (ModuleCat.{w} R) n).obj (ModuleCat.of R R)).map f
  have h : LinearMap.id -
      (((singularHomologyFunctor (ModuleCat.{w} S) n).obj (ModuleCat.of S S)).map f).hom =
      e.toLinearMap ∘ₗ (LinearMap.id - g.hom).baseChange S ∘ₗ e.symm.toLinearMap := by
    ext y
    simp [LinearMap.baseChange_sub, e, g, singularHomologyBaseChangeEquiv_baseChange]
  rw [h, LinearMap.det_conj, LinearMap.det_baseChange]

end TopCat
