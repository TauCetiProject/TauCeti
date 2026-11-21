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
algebras, hence a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)`. -/
theorem isClosedImmersion_projMap_of_surjective (g : N →ₗ[R] M) (hg : Function.Surjective g)
    (hirr : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R N)).map
        (_root_.SymmetricAlgebra.gradedMap R g) :=
      HomogeneousIdeal.irrelevant_le_map_of_surjective _ (by
        intro a
        obtain ⟨b, hb⟩ := _root_.SymmetricAlgebra.map_surjective R g hg a
        exact ⟨b, (_root_.SymmetricAlgebra.gradedMap_apply R g b).trans hb⟩)) :
    AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hirr) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map _ hirr fun a ↦ by
    obtain ⟨b, hb⟩ := _root_.SymmetricAlgebra.map_surjective R g hg a
    exact ⟨b, (_root_.SymmetricAlgebra.gradedMap_apply R g b).trans hb⟩

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
  have hsurj : Function.Surjective (_root_.SymmetricAlgebra.gradedMap R g) := fun a ↦ by
    obtain ⟨b, hb⟩ := _root_.SymmetricAlgebra.map_surjective R g hg a
    exact ⟨b, (_root_.SymmetricAlgebra.gradedMap_apply R g b).trans hb⟩
  let j := Proj.map (_root_.SymmetricAlgebra.gradedMap R g)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj)
  have : IsClosedImmersion j :=
    TauCeti.SymmetricAlgebra.isClosedImmersion_projMap_of_surjective R g hg
  have : j.IsOver (Spec (.of R)) := TauCeti.SymmetricAlgebra.isOver_projMap R g _
  exact ⟨n, i ≫ j, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
