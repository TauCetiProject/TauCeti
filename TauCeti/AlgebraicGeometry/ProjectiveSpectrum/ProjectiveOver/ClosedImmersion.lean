/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# Closed immersions of projective schemes into projective space

A surjective `R`-linear map `g : N →ₗ[R] M` induces a surjective graded homomorphism of symmetric
algebras `Sym_R N →+* Sym_R M`, hence a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over
`Spec R`. Consequently, every scheme projective over `R` admits a closed immersion over `Spec R`
into `Proj (Sym_R (Fin n → R))` for some `n : ℕ`.

## Main results

* `TauCeti.SymmetricAlgebra.projMap_projToSpec` and `TauCeti.SymmetricAlgebra.isOver_projMap`: the
  morphism `Proj (Sym_R M) ⟶ Proj (Sym_R N)` induced by a linear map `N →ₗ[R] M` is a morphism over
  `Spec R`.
* `TauCeti.SymmetricAlgebra.isClosedImmersion_projMap_of_surjective`: a surjective `R`-linear map
  `N →ₗ[R] M` induces a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)`.
* `TauCeti.SymmetricAlgebra.projMapOfSurjective`: the closed immersion
  `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over `Spec R` induced by a surjective `R`-linear map.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_pi`: a scheme projective
  over `R` admits a closed immersion over `Spec R` into `Proj (Sym_R (Fin n → R))` for some `n`.
-/

public section

open CategoryTheory

namespace TauCeti.SymmetricAlgebra

universe u

variable (R : Type u) [CommRing R] {M N : Type u} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The morphism `Proj (Sym_R M) ⟶ Proj (Sym_R N)` induced by a linear map `g : N →ₗ[R] M`
commutes with the structural morphisms to `Spec R`. -/
@[reassoc (attr := simp)]
theorem projMap_projToSpec (g : N →ₗ[R] M)
    (hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R N)).map
        (_root_.SymmetricAlgebra.gradedMap R g)) :
    AlgebraicGeometry.Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hg ≫ projToSpec R N =
      projToSpec R M := by
  rw [projToSpec_def, AlgebraicGeometry.Proj.map_toSpecZero_assoc,
    ← AlgebraicGeometry.Spec.map_comp, projToSpec_def]
  congr 2
  ext r
  simp

/-- The morphism `Proj (Sym_R M) ⟶ Proj (Sym_R N)` induced by a linear map `g : N →ₗ[R] M`
is a morphism over `Spec R`. -/
theorem isOver_projMap (g : N →ₗ[R] M)
    (hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R N)).map
        (_root_.SymmetricAlgebra.gradedMap R g)) :
    (AlgebraicGeometry.Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hg).IsOver
      (AlgebraicGeometry.Spec (.of R)) :=
  ⟨projMap_projToSpec R g hg⟩

/-- A surjective `R`-linear map `g : N →ₗ[R] M` induces a surjective graded map of symmetric
algebras. -/
theorem gradedMap_surjective (g : N →ₗ[R] M) (hg : Function.Surjective g) :
    Function.Surjective (_root_.SymmetricAlgebra.gradedMap R g) := fun a ↦ by
  simpa [_root_.SymmetricAlgebra.gradedMap_apply] using
    _root_.SymmetricAlgebra.map_surjective R g hg a

/-- For a surjective `R`-linear map `g : N →ₗ[R] M`, the irrelevant ideal of `Sym_R M` lies in
the image of the irrelevant ideal of `Sym_R N` under `gradedMap R g`. -/
theorem irrelevant_le_map_gradedMap_of_surjective (g : N →ₗ[R] M) (hg : Function.Surjective g) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R N)).map
        (_root_.SymmetricAlgebra.gradedMap R g) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _ (gradedMap_surjective R g hg)

/-- A surjective `R`-linear map `g : N →ₗ[R] M` induces a surjective graded map of symmetric
algebras, hence a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)`. -/
theorem isClosedImmersion_projMap_of_surjective (g : N →ₗ[R] M) (hg : Function.Surjective g)
    (hirr : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R N)).map
        (_root_.SymmetricAlgebra.gradedMap R g) :=
      irrelevant_le_map_gradedMap_of_surjective R g hg) :
    AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hirr) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map _ hirr (gradedMap_surjective R g hg)

/-- The closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over `Spec R` induced by a
surjective `R`-linear map `g : N →ₗ[R] M`. -/
@[expose]
noncomputable def projMapOfSurjective (g : N →ₗ[R] M) (hg : Function.Surjective g) :
    AlgebraicGeometry.Proj (homogeneousSubmodule R M) ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule R N) :=
  AlgebraicGeometry.Proj.map (_root_.SymmetricAlgebra.gradedMap R g)
    (irrelevant_le_map_gradedMap_of_surjective R g hg)

/-- `projMapOfSurjective` is a closed immersion. -/
instance isClosedImmersion_projMapOfSurjective (g : N →ₗ[R] M) (hg : Function.Surjective g) :
    AlgebraicGeometry.IsClosedImmersion (projMapOfSurjective R g hg) :=
  isClosedImmersion_projMap_of_surjective R g hg _

/-- `projMapOfSurjective` is a morphism over `Spec R`. -/
instance isOver_projMapOfSurjective (g : N →ₗ[R] M) (hg : Function.Surjective g) :
    (projMapOfSurjective R g hg).IsOver (AlgebraicGeometry.Spec (.of R)) :=
  isOver_projMap R g _

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- Every scheme projective over `R` admits a closed immersion over `Spec R` into the projective
space `Proj (Sym_R (Fin n → R))` for some `n : ℕ`. -/
theorem IsProjectiveOver.exists_isClosedImmersion_pi [X.IsProjectiveOver R] :
    ∃ (n : ℕ) (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin n → R))),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of R)) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  exact ⟨n, i ≫ TauCeti.SymmetricAlgebra.projMapOfSurjective R g hg, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
