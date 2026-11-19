/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Flat base change of singular homology

Let `S` be a flat algebra over a commutative ring `R`. Extension of scalars `M ↦ S ⊗[R] M` is
then exact, and as a left adjoint it preserves coproducts, so it commutes with singular homology
(`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`). Since it carries the coefficients
`R` to `S ⊗[R] R ≅ S`, this identifies singular homology with coefficients in `S` with the base
change of singular homology with coefficients in `R`:

`Hₙ(X; S) ≃ₗ[S] S ⊗[R] Hₙ(X; R)`

(`TopCat.singularHomologyBaseChangeEquiv`). The identification is natural in `X`: a continuous
map acts on the right-hand side by the base change of its action on `Hₙ(X; R)`
(`TopCat.singularHomologyBaseChangeEquiv_naturality`). So for a continuous self-map `g`, the
determinant of `𝟙 - g_*` over `S` is the image of its determinant over `R` when `Hₙ(X; R)` is free
(`TopCat.det_id_sub_singularHomologyMap_baseChange`). The main example is `R = ℤ` and `S` a field
of characteristic zero, such as `ℚ` or `ℝ`, which is flat over `ℤ` because it is torsion-free.
Through it, linear-algebra invariants of the action of a map on rational or real homology, such
as determinants, are computed from its action on integral homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (homology with coefficients and the universal coefficient theorem for homology).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology ModuleCat
open scoped TensorProduct

universe u

namespace TopCat

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- **Flat base change of singular homology**, as an isomorphism of functors: for a flat
`R`-algebra `S`, singular homology with coefficients in `S` is the extension of scalars of singular
homology with coefficients in `R`, `Hₙ(X; S) ≅ S ⊗[R] Hₙ(X; R)`, naturally in `X`. -/
def singularHomologyBaseChangeIso (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S) ≅
      (singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R) ⋙
        extendScalars (algebraMap R S) :=
  -- The coefficients `S ⊗[R] R ≅ S`.
  let c : (extendScalars (algebraMap R S)).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
    extendScalarsAlgebraMapIso _ ≪≫
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
  (singularHomologyFunctor (ModuleCat.{u} S) n).mapIso c.symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (extendScalars (algebraMap R S)) (ModuleCat.of R R) n).symm

/-- **Flat base change of singular homology**: for a flat `R`-algebra `S`, singular homology with
coefficients in `S` is the base change of singular homology with coefficients in `R`,
`Hₙ(X; S) ≃ₗ[S] S ⊗[R] Hₙ(X; R)`. -/
def singularHomologyBaseChangeEquiv (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).obj X ≃ₗ[S]
      S ⊗[R] ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X :=
  ((singularHomologyBaseChangeIso R S n).app X ≪≫ extendScalarsAlgebraMapIso _).toLinearEquiv

/-- `TopCat.singularHomologyBaseChangeEquiv` is the component of
`TopCat.singularHomologyBaseChangeIso`, followed by the identification of extension of scalars with
the tensor product `S ⊗[R] -`. -/
lemma singularHomologyBaseChangeEquiv_apply (X : TopCat.{u}) (n : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).obj X) :
    singularHomologyBaseChangeEquiv R S X n x =
      (extendScalarsAlgebraMapIso _).hom ((singularHomologyBaseChangeIso R S n).hom.app X x) :=
  (rfl)

variable {R S} in
/-- **Naturality of flat base change of singular homology**: under
`Hₙ(X; S) ≃ₗ[S] S ⊗[R] Hₙ(X; R)`, a continuous map `g : X ⟶ Y` acts on `S ⊗[R] Hₙ(X; R)` by the
base change of its action on `Hₙ(X; R)`. -/
theorem singularHomologyBaseChangeEquiv_naturality {X Y : TopCat.{u}} (g : X ⟶ Y) (n : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).obj X) :
    singularHomologyBaseChangeEquiv R S Y n
        ((((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).map g).hom x) =
      ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map g).hom.baseChange
        S) (singularHomologyBaseChangeEquiv R S X n x) := by
  have h₁ := ConcreteCategory.congr_hom ((singularHomologyBaseChangeIso R S n).hom.naturality g) x
  have h₂ := ConcreteCategory.congr_hom (extendScalars_map_comp_extendScalarsAlgebraMapIso_hom
    (S := S) (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map g))
      ((singularHomologyBaseChangeIso R S n).hom.app X x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁ h₂
  rw [singularHomologyBaseChangeEquiv_apply, singularHomologyBaseChangeEquiv_apply]
  exact (congrArg _ h₁).trans h₂

variable {R S} in
/-- **Wang-type determinants under flat base change.** If `S` is a flat `R`-algebra and
`Hₙ(X; R)` is free, then for a continuous self-map `g : X ⟶ X` the determinant of `𝟙 - g_*` on
`Hₙ(X; S)` is the image in `S` of its determinant on `Hₙ(X; R)`. (When `Hₙ(X; R)` has infinite
rank, both determinants are `1` by convention.) -/
theorem det_id_sub_singularHomologyMap_baseChange {X : TopCat.{u}} (g : X ⟶ X) (n : ℕ)
    [Module.Free R (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X)] :
    (LinearMap.id -
        (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).map g).hom).det =
      algebraMap R S (LinearMap.id -
        (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
          g).hom).det := by
  let e := singularHomologyBaseChangeEquiv R S X n
  nontriviality S
  by_cases hfin :
      Module.Finite R (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X)
  · -- Under `Hₙ(X; S) ≃ S ⊗[R] Hₙ(X; R)` the endomorphism `𝟙 - g_*` becomes its base change.
    rw [← LinearMap.det_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_id]
    refine LinearMap.det_eq_of_comp_eq e (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      map_sub, singularHomologyBaseChangeEquiv_naturality, e]
  · -- A free module whose base change to the nontrivial ring `S` is finite is finite.
    rw [LinearMap.det_eq_one_of_not_module_finite hfin, map_one]
    refine LinearMap.det_eq_one_of_not_module_finite (fun hS ↦ hfin ?_) _
    let b := Module.Free.chooseBasis R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X)
    have := Module.Finite.equiv e
    have := Module.Finite.finite_basis (Algebra.TensorProduct.basis S b)
    exact Module.Finite.of_basis b

end TopCat
