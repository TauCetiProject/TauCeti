/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.FiniteSet
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

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
* `AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_pi`: a scheme projective over
  `R` is a closed subscheme, over `R`, of the projective space `Proj (Sym_R R^{n+2})` of positive
  dimension `n + 1`, for some `n`.
* the instance `(Proj (Sym_R M)).IsProjectiveOver R` for a finite `R`-module `M`.
* the instance `IsProper (X ↘ Spec R)` for `X` projective over `R`.
* `AlgebraicGeometry.Scheme.exists_isAffineOpen_superset_of_isProjectiveOver`: a finite set
  in a scheme projective over `R` lies in a common affine open inside a prescribed open.
* `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isAffineHom_isProjectiveOver`:
  the same conclusion for affine morphisms to a scheme projective over `R`.
* `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isImmersion_isProjectiveOver`:
  the same conclusion for immersions into a scheme projective over `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.4 (definition of a
  projective morphism before Theorem II.4.9).
-/

public section

open CategoryTheory

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

/-- **A projective scheme is a closed subscheme of a projective space.** A scheme projective over
`R` admits a closed immersion over `R` into `ℙⁿ⁺¹_R = Proj (Sym_R R^{n+2})` for some `n`. The
finite module `M` of the definition is a quotient of some `Rⁿ`, hence of `R^{n+2}`, and the
induced surjection `Sym_R R^{n+2} → Sym_R M` of graded algebras embeds `Proj (Sym_R M)` as a closed
subscheme. The two extra coordinates make the projective space positive-dimensional, as the
cohomology computations on projective space over `R` require. -/
theorem IsProjectiveOver.exists_isClosedImmersion_pi [X.IsProjectiveOver R] :
    ∃ (n : ℕ) (f : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n + 2) → R))),
      IsClosedImmersion f ∧ f.IsOver (Spec (.of R)) := by
  obtain ⟨M, _, _, _, f, _, _⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  -- The surjection `R^{n+2} → Rⁿ → M` forgets the last two coordinates.
  let q : (Fin (n + 2) → R) →ₗ[R] M := p ∘ₗ LinearMap.funLeft R R (Fin.castAdd 2)
  have hq : Function.Surjective q :=
    hp.comp (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castAdd_injective n 2))
  let ι₁ : M →ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M 1 :=
    (SymmetricAlgebra.ι R M).codRestrict _ (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule R M)
  let g :=
    SymmetricAlgebra.gradedLift R (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) (ι₁ ∘ₗ q)
  have hg : Function.Surjective g := by
    refine SymmetricAlgebra.gradedLift_surjective R _ ?_
    -- The generators of the lift are the images `ι (q x)` of the generators of `Sym_R M`.
    have : (fun x ↦ ((ι₁ ∘ₗ q) x : SymmetricAlgebra R M)) = SymmetricAlgebra.ι R M ∘ q :=
      funext fun _ ↦ by simp [ι₁]
    rw [this, hq.range_comp, SymmetricAlgebra.adjoin_range_ι]
  have hirr := HomogeneousIdeal.irrelevant_le_map_of_surjective g hg
  have := Proj.isClosedImmersion_map g hirr hg
  exact ⟨n, f ≫ Proj.map g hirr, inferInstance, inferInstance⟩

/-- **A projective scheme is proper**: a scheme projective over `R` is proper over `R`. -/
instance IsProjectiveOver.isProper [X.IsProjectiveOver R] : IsProper (X ↘ Spec (.of R)) := by
  obtain ⟨M, _, _, _, f, hf, hfR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  rw [← comp_over f (Spec (.of R))]
  infer_instance

/-- An affine morphism to a scheme projective over an affine base admits affine
neighbourhoods of finite sets inside any prescribed source open. -/
theorem Hom.exists_isAffineOpen_superset_of_isAffineHom_isProjectiveOver
    [X.IsProjectiveOver R] {Z : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    {s : Set Z} {W : Z.Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨M, _, _, _, g, _, _⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  exact (f ≫ g).exists_isAffineOpen_superset_of_isAffineHom_proj hs hsW

/-- A finite subset of a scheme projective over an affine base has a common affine
neighbourhood inside any prescribed open containing it. -/
theorem exists_isAffineOpen_superset_of_isProjectiveOver [X.IsProjectiveOver R]
    {s : Set X} {W : X.Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W :=
  Hom.exists_isAffineOpen_superset_of_isAffineHom_isProjectiveOver R (𝟙 X) hs hsW

/-- A finite subset of a scheme immersed in a scheme projective over an affine base has a
common affine neighbourhood inside any prescribed open containing it. -/
theorem Hom.exists_isAffineOpen_superset_of_isImmersion_isProjectiveOver
    [X.IsProjectiveOver R] {Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f]
    {s : Set Z} {W : Z.Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨M, _, _, _, g, _, _⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  exact (f ≫ g).exists_isAffineOpen_superset_of_isImmersion_proj hs hsW

end AlgebraicGeometry.Scheme
