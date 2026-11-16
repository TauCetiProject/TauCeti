/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# Projective schemes over a ring

A scheme `X` over `Spec R` is *projective over `R`* if it is a closed subscheme, over `R`, of the
projective spectrum `Proj (Sym_R M)` of the symmetric algebra of a finite `R`-module `M`. Mathlib
has no class of projective morphisms, so this file records projectivity over an affine base as a
predicate on schemes over `Spec R`.

Over an affine base this is the usual notion: a finite `R`-module `M` is a quotient of some `Rⁿ`,
so `Proj (Sym_R M)` is itself a closed subscheme of `Proj (Sym_R Rⁿ) = ℙⁿ⁻¹_R`, and the definition
agrees with Hartshorne's (a closed subscheme of some `ℙⁿ_R`). Over a field `k` every finite module
is a finite-dimensional vector space, so `Proj (Sym_k M)` is a projective space over `k`.

A projective scheme over `R` is proper over `R`, because closed immersions are proper and
`Proj (Sym_R M)` is proper over `R` for finite `M`
(`TauCeti.SymmetricAlgebra.instIsProperProjToSpec`).

## Main definitions

* `AlgebraicGeometry.Scheme.IsProjectiveOver R X`: the scheme `X` over `Spec R` is a closed
  subscheme, over `R`, of `Proj (Sym_R M)` for some finite `R`-module `M`.

## Main results

* `AlgebraicGeometry.Scheme.IsProjectiveOver.of_isClosedImmersion`: a closed subscheme over `R` of
  a projective scheme over `R` is projective over `R`.
* the instance `(Proj (Sym_R M)).IsProjectiveOver R` for a finite `R`-module `M`.
* the instance `IsProper (X ↘ Spec R)` for `X` projective over `R`.
* `TauCeti.SymmetricAlgebra.projMap_projToSpec` and
  `TauCeti.SymmetricAlgebra.isClosedImmersion_projMap_of_surjective`: a surjective `R`-linear map
  `N →ₗ[R] M` induces a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over `Spec R`.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_pi`: a scheme projective
  over `R` admits a closed immersion over `Spec R` into `Proj (Sym_R (Fin n → R))` for some `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.4 (definition of a
  projective morphism before Theorem II.4.9).
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

/-- A scheme `X` over `Spec R` is *projective over `R`* if it is a closed subscheme, over `R`, of
the projective spectrum `Proj (Sym_R M)` of the symmetric algebra of a finite `R`-module `M`. -/
class IsProjectiveOver : Prop where
  /-- There is a closed immersion over `R` into `Proj (Sym_R M)` for a finite `R`-module `M`. -/
  exists_isClosedImmersion : ∃ (M : Type u) (_ : AddCommMonoid M) (_ : Module R M)
    (_ : Module.Finite R M) (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)),
    IsClosedImmersion f ∧ f.IsOver (Spec (.of R))

/-- The projective spectrum of the symmetric algebra of a finite `R`-module is projective
over `R`. -/
instance isProjectiveOver_proj (M : Type u) [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)).IsProjectiveOver R :=
  ⟨⟨M, inferInstance, inferInstance, inferInstance, 𝟙 _, inferInstance, inferInstance⟩⟩

/-- A closed subscheme over `R` of a projective scheme over `R` is projective over `R`. -/
theorem IsProjectiveOver.of_isClosedImmersion {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    [Y.IsProjectiveOver R] (f : X ⟶ Y) [IsClosedImmersion f] [f.IsOver (Spec (.of R))] :
    X.IsProjectiveOver R := by
  obtain ⟨M, _, _, _, g, hg, hgR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := Y)
  exact ⟨⟨M, inferInstance, inferInstance, inferInstance, f ≫ g, inferInstance, inferInstance⟩⟩

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

/-- **A projective scheme is proper**: a scheme projective over `R` is proper over `R`. -/
instance IsProjectiveOver.isProper [X.IsProjectiveOver R] : IsProper (X ↘ Spec (.of R)) := by
  obtain ⟨M, _, _, _, f, hf, hfR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  rw [← comp_over f (Spec (.of R))]
  infer_instance

end AlgebraicGeometry.Scheme
