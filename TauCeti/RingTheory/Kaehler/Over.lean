/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.RingTheory.Kaehler.BaseChange

/-!
# Kähler differentials with coefficients in a fixed algebra

For an object `P → B` over a commutative `A`-algebra `B`, extending scalars on
`Ω[P⁄A]` along the structure map gives a `B`-module. A map over `B` acts by
`b ⊗ dx ↦ b ⊗ d(f x)`. Applying this functor to a polynomial resolution over
`B` gives the simplicial module used in the cotangent complex.

## References

* The Stacks Project, Definition 92.3.2 (Tag 08PN).
* Mathlib's square-induced map `KaehlerDifferential.map` and scalar extension
  `LinearMap.liftBaseChange`.
-/

public noncomputable section

open CategoryTheory TensorProduct KaehlerDifferential

universe u v

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : CommAlgCat.{v} A}

/-- The module of Kähler differentials of the source, extended along its structure map to `B`.
The carrier computes to a tensor product using that map's algebra structure. -/
abbrev kaehlerDifferentialOverObj (P : Over B) : ModuleCat.{v} B :=
  letI : Algebra P.left B := P.hom.hom.toAlgebra
  ModuleCat.of B (B ⊗[P.left] Ω[P.left⁄A])

/-- A morphism over `B` induces a `B`-linear map of the extended differential modules. -/
def kaehlerDifferentialOverMap {P Q : Over B} (f : P ⟶ Q) :
    kaehlerDifferentialOverObj P →ₗ[B] kaehlerDifferentialOverObj Q := by
  letI : Algebra P.left B := P.hom.hom.toAlgebra
  letI : Algebra Q.left B := Q.hom.hom.toAlgebra
  letI : Algebra P.left Q.left := f.left.hom.toAlgebra
  haveI : IsScalarTower A P.left Q.left :=
    .of_algebraMap_eq' f.left.hom.comp_algebraMap.symm
  haveI : IsScalarTower P.left Q.left B :=
    .of_algebraMap_eq' (congrArg (fun g : P.left ⟶ B ↦ g.hom.toRingHom) (Over.w f)).symm
  -- Give scalar extension the concrete tensor product as its target for instance search.
  refine (LinearMap.liftBaseChange B ?_ :
    B ⊗[P.left] Ω[P.left⁄A] →ₗ[B] B ⊗[Q.left] Ω[Q.left⁄A])
  exact
    (TensorProduct.mk Q.left B Ω[Q.left⁄A] 1).restrictScalars P.left ∘ₗ
      KaehlerDifferential.map A A P.left Q.left

/-- The map on extended differentials takes the differential of a source element to
the differential of its image. -/
@[simp] lemma kaehlerDifferentialOverMap_tmul_D {P Q : Over B} (f : P ⟶ Q)
    (b : B) (x : P.left) :
    letI : Algebra P.left B := P.hom.hom.toAlgebra
    letI : Algebra Q.left B := Q.hom.hom.toAlgebra
    kaehlerDifferentialOverMap f (b ⊗ₜ[P.left] D A P.left x) =
      b ⊗ₜ[Q.left] D A Q.left (f.left x) := by
  let : Algebra Q.left B := Q.hom.hom.toAlgebra
  unfold kaehlerDifferentialOverMap
  rw [LinearMap.liftBaseChange_tmul]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_D,
    TensorProduct.mk_apply, RingHom.algebraMap_toAlgebra]
  rw [TensorProduct.smul_tmul' (R := Q.left), smul_eq_mul, mul_one]
  rfl

/-- Extend the Kähler differentials of each commutative `A`-algebra over `B` to `B`.
The object projection computes to a module of tensors so that these can be used in map formulas. -/
@[expose] def kaehlerDifferentialOver (B : CommAlgCat.{v} A) : Over B ⥤ ModuleCat.{v} B where
  obj := kaehlerDifferentialOverObj
  map f := ModuleCat.ofHom (kaehlerDifferentialOverMap f)
  map_id P := by
    let : Algebra P.left B := P.hom.hom.toAlgebra
    apply ModuleCat.hom_ext
    -- Reduce the bundled identity and the constructed module morphism to linear maps.
    change kaehlerDifferentialOverMap (𝟙 P) = LinearMap.id
    apply TauCeti.kaehlerBaseChange_linearMap_ext
    intro x
    rw [kaehlerDifferentialOverMap_tmul_D]
    simp
  map_comp {P Q S} f g := by
    let : Algebra P.left B := P.hom.hom.toAlgebra
    let : Algebra Q.left B := Q.hom.hom.toAlgebra
    let : Algebra S.left B := S.hom.hom.toAlgebra
    apply ModuleCat.hom_ext
    -- Reduce the bundled composite to the composition of the two linear maps.
    change kaehlerDifferentialOverMap (f ≫ g) =
      kaehlerDifferentialOverMap g ∘ₗ kaehlerDifferentialOverMap f
    apply TauCeti.kaehlerBaseChange_linearMap_ext
    intro x
    rw [LinearMap.comp_apply, kaehlerDifferentialOverMap_tmul_D,
      kaehlerDifferentialOverMap_tmul_D, kaehlerDifferentialOverMap_tmul_D]
    simp

/-- The object part of `kaehlerDifferentialOver` uses extension of scalars along the
structure map of the object over `B`. -/
@[simp] lemma kaehlerDifferentialOver_obj (P : Over B) :
    (kaehlerDifferentialOver B).obj P = kaehlerDifferentialOverObj P := (rfl)

/-- The functor sends a morphism over the coefficient algebra to its induced linear map. -/
@[simp] lemma kaehlerDifferentialOver_map_hom {P Q : Over B} (f : P ⟶ Q) :
    ((kaehlerDifferentialOver B).map f).hom = kaehlerDifferentialOverMap f := (rfl)

end CommAlgCat

namespace CategoryTheory.SimplicialObject.Augmented

variable {A : Type u} [CommRing A]

/-- Apply Kähler differentials to a simplicial algebra and extend scalars along its augmentation. -/
abbrev kaehlerDifferential (P : SimplicialObject.Augmented (CommAlgCat.{v} A)) :
    SimplicialObject (ModuleCat.{v} P.right) :=
  Over.lift P.left P.hom ⋙ P.right.kaehlerDifferentialOver

end CategoryTheory.SimplicialObject.Augmented
