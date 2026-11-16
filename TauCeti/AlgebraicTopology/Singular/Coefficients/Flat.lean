/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Module.Torsion.BaseChange
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Localization

/-!
# Flat change of coefficients for singular homology

Extension of scalars `ModuleCat.extendScalars f : ModuleCat R ⥤ ModuleCat S` along a flat
homomorphism `f : R →+* S` of commutative rings preserves all colimits (being a left adjoint) and
finite limits (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`), hence preserves homology
(`ModuleCat.preservesHomology_extendScalars_of_flat`). By
`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`, it therefore commutes with singular
homology naturally in the space (`TauCeti.singularHomologyExtendScalarsIso`):

`S ⊗[R] Hₙ(X; M) ≅ Hₙ(X; S ⊗[R] M)`.

For a flat `R`-algebra `S` and coefficients `M = R`, identifying `S ⊗[R] R` with `S` yields a
natural isomorphism `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` (`TopCat.singularHomologyTensorIso`), under
which the map `Hₙ(f; S)` induced by a continuous map `f : X ⟶ Y` corresponds to the base change
`Hₙ(f; R).baseChange S` (`TauCeti.singularHomologyTensorIso_hom_naturality`).

When `A` is a localization of `R` at a submonoid `M`, `A` is flat over `R` and tensoring with `A`
detects `M`-torsion (`Submonoid.isTorsion'_iff_subsingleton_tensorProduct`). Thus:

* `TopCat.isTorsion'_singularHomology_iff_subsingleton`: `Hₙ(X; R)` is `M`-torsion if and only if
  `Hₙ(X; A)` is trivial.
* `TauCeti.isIso_singularHomologyMap_localization_iff`: `Hₙ(f; A)` is an isomorphism if and only
  if the kernel and cokernel of `Hₙ(f; R)` are `M`-torsion.
* `TopCat.isAddTorsion_singularHomology_iff_subsingleton_rat`: integral singular homology
  `Hₙ(X; ℤ)` is torsion if and only if rational singular homology `Hₙ(X; ℚ)` is trivial.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (universal coefficient theorem for homology).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped TensorProduct

universe u

namespace ModuleCat

/-- Extension of scalars along a flat homomorphism of commutative rings preserves homology. -/
theorem preservesHomology_extendScalars_of_flat {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Flat) : (extendScalars.{u, u, u} f).PreservesHomology :=
  have := preservesFiniteLimits_extendScalars_of_flat hf
  inferInstance

/-- Extension of scalars along the structure map of a flat algebra preserves homology. -/
instance preservesHomology_extendScalars_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] :
    (extendScalars.{u, u, u} (algebraMap R S)).PreservesHomology :=
  preservesHomology_extendScalars_of_flat (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The identification `ModuleCat.extendScalarsAlgebraMapIso` is natural with respect to
`LinearMap.baseChange`. -/
@[reassoc]
lemma extendScalarsAlgebraMapIso_inv_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    ofHom (g.hom.baseChange S) ≫ (extendScalarsAlgebraMapIso N).inv =
      (extendScalarsAlgebraMapIso M).inv ≫ (extendScalars (algebraMap R S)).map g := by
  apply hom_ext
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
    change (extendScalarsAlgebraMapIso N).inv (s ⊗ₜ[R] g m) =
      (extendScalars (algebraMap R S)).map g ((extendScalarsAlgebraMapIso M).inv (s ⊗ₜ[R] m))
    exact (extendScalarsAlgebraMapIso_inv_tmul N s (g m)).trans
      ((ExtendScalars.map_tmul (algebraMap R S) g s m).symm.trans
        (congrArg ((extendScalars (algebraMap R S)).map g)
          (extendScalarsAlgebraMapIso_inv_tmul M s m).symm))
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end ModuleCat

namespace TauCeti

/-- **Flat extension of scalars commutes with singular homology**: for a flat ring homomorphism
`f : R →+* S` and any `R`-module `M`, `S ⊗[R] Hₙ(X; M) ≅ Hₙ(X; S ⊗[R] M)` naturally in `X`.
-/
def singularHomologyExtendScalarsIso {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Flat) (M : ModuleCat.{u} R) (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{u} R) n).obj M ⋙ ModuleCat.extendScalars.{u, u, u} f ≅
      (singularHomologyFunctor (ModuleCat.{u} S) n).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  have := ModuleCat.preservesHomology_extendScalars_of_flat hf
  Functor.singularHomologyFunctorObjCompIso (ModuleCat.extendScalars.{u, u, u} f) M n

end TauCeti

namespace TopCat

section FlatAlgebra

/-- The canonical isomorphism `(ModuleCat.extendScalars (algebraMap R S)).obj R ≅ S`. -/
private def extendScalarsSelfIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj (ModuleCat.of R R) ≅
      ModuleCat.of S S :=
  ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R R) ≪≫
    (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- **Singular homology commutes with flat base change of the coefficient ring**: for a flat
`R`-algebra `S`, `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`. -/
def singularHomologyTensorIso (X : TopCat.{u}) (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (n : ℕ) :
    ModuleCat.of S
        (S ⊗[R]
          (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).obj X :=
  (ModuleCat.extendScalarsAlgebraMapIso _).symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) (ModuleCat.of R R) n).app X ≪≫
    ((singularHomologyFunctor (ModuleCat.{u} S) n).mapIso (extendScalarsSelfIso R S)).app X

/-- `Hₙ(X; S)` is trivial if and only if `S ⊗[R] Hₙ(X; R)` is trivial. -/
theorem subsingleton_singularHomology_iff_subsingleton_tensorProduct (X : TopCat.{u})
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] (n : ℕ) :
    Subsingleton (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).obj X) ↔
      Subsingleton
        (S ⊗[R]
          (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X)) :=
  (X.singularHomologyTensorIso R S n).toLinearEquiv.toEquiv.subsingleton_congr.symm

end FlatAlgebra

/-- For a localization `A` of `R` at a submonoid `M`, `Hₙ(X; R)` is `M`-torsion if and only if
`Hₙ(X; A)` is trivial. -/
theorem isTorsion'_singularHomology_iff_subsingleton (X : TopCat.{u}) {R : Type u} [CommRing R]
    (M : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A] (n : ℕ) :
    Module.IsTorsion'
        (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X) M ↔
      Subsingleton
        (((singularHomologyFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)).obj X) := by
  have : Module.Flat R A := IsLocalization.flat A M
  rw [M.isTorsion'_iff_subsingleton_tensorProduct A,
    X.subsingleton_singularHomology_iff_subsingleton_tensorProduct R A n]

/-- Integral singular homology `Hₙ(X; ℤ)` is `S`-torsion if and only if `Hₙ(X; A)` is trivial,
for any localization `A` of `ℤ` at `S`. -/
theorem isTorsion'_singularHomology_int_iff_subsingleton (X : TopCat.{0}) (S : Submonoid ℤ)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] (n : ℕ) :
    Module.IsTorsion'
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X) S ↔
      Subsingleton
        (((singularHomologyFunctor (ModuleCat.{0} A) n).obj (ModuleCat.of A A)).obj X) := by
  convert X.isTorsion'_singularHomology_iff_subsingleton S A n
  exact congrArg (fun m : Module ℤ _ ↦ m.toSMul)
    (Subsingleton.elim (AddCommGroup.toIntModule _) _)

/-- Integral singular homology `Hₙ(X; ℤ)` is torsion if and only if rational singular homology
`Hₙ(X; ℚ)` is trivial. -/
theorem isAddTorsion_singularHomology_iff_subsingleton_rat (X : TopCat.{0}) (n : ℕ) :
    IsAddTorsion
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X) ↔
      Subsingleton
        (((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj (ModuleCat.of ℚ ℚ)).obj X) := by
  rw [← X.isTorsion'_singularHomology_iff_subsingleton (nonZeroDivisors ℤ) ℚ n]
  convert isAddTorsion_iff_isTorsion_int
  exact Subsingleton.elim _ _

end TopCat

namespace TauCeti

/-- Naturality of the base-change isomorphism `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`: under it, the map
`Hₙ(f; S)` induced by `f : X ⟶ Y` corresponds to `Hₙ(f; R).baseChange S`. -/
@[reassoc]
theorem singularHomologyTensorIso_hom_naturality (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom
        ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map f).hom.baseChange S) ≫
        (Y.singularHomologyTensorIso R S n).hom =
      (X.singularHomologyTensorIso R S n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).map f := by
  dsimp only [TopCat.singularHomologyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [ModuleCat.extendScalarsAlgebraMapIso_inv_naturality_assoc]
  have h₁ := (Functor.singularHomologyFunctorObjCompIso
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) (ModuleCat.of R R) n).hom.naturality f
  have h₂ := ((singularHomologyFunctor (ModuleCat.{u} S) n).map
    (TopCat.extendScalarsSelfIso R S).hom).naturality f
  dsimp only [Functor.comp_map] at h₁
  rw [Category.assoc, reassoc_of% h₁, h₂, Category.assoc]

/-- The base-changed homology map `Hₙ(f; R).baseChange S` is bijective if and only if `Hₙ(f; S)`
is an isomorphism. -/
theorem bijective_singularHomologyMap_baseChange_iff_isIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    Function.Bijective
        ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map f).hom.baseChange S) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)).map f) := by
  have hbij :
      Function.Bijective
          ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
            (ModuleCat.of R R)).map f).hom.baseChange S) ↔
        IsIso (ModuleCat.ofHom
          ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
            (ModuleCat.of R R)).map f).hom.baseChange S)) :=
    (ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom _)).symm
  rw [hbij, ← isIso_comp_right_iff _ (Y.singularHomologyTensorIso R S n).hom,
    singularHomologyTensorIso_hom_naturality, isIso_comp_left_iff]

/-- A continuous map `f : X ⟶ Y` induces an isomorphism on `Hₙ(-; A)`, for a localization `A` of
`R` at `M`, if and only if the kernel and cokernel of `Hₙ(f; R)` are `M`-torsion. -/
theorem isIso_singularHomologyMap_localization_iff {R : Type u} [CommRing R] (M : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A] {X Y : TopCat.{u}} (f : X ⟶ Y)
    (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)).map f) ↔
      Module.IsTorsion'
          (LinearMap.ker
            (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
              (ModuleCat.of R R)).map f).hom) M ∧
        Module.IsTorsion'
          ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj Y) ⧸
            LinearMap.range
              (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map f).hom)
          M := by
  have : Module.Flat R A := IsLocalization.flat A M
  rw [← bijective_singularHomologyMap_baseChange_iff_isIso R A f n,
    LinearMap.bijective_baseChange_iff _ M A]

end TauCeti
