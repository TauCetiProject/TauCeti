/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# Higher direct images on projective schemes over a Noetherian affine base

Combining the affine-base identification `Hⁿ(X, M)~ ≅ Rⁿ f_* M`
(`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage` in
`TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent`) with Serre's finiteness
(`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite`) and vanishing
(`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre`) theorems, this file proves:
* coherence (finite presentation) of `R^q f_* F` for every projective scheme `X` over a Noetherian
  ring `R`, every quasi-coherent `𝒪_X`-module `F` of finite type, and every `q : ℕ`;
* vanishing of `R^q f_* (i^* 𝒪(n) ⊗ F)` for every closed subscheme `i : X ⟶ Proj (Sym_R M)` over
  `Spec R` (with `R` Noetherian and `M` finite), every `q > 0`, and all sufficiently large `n : ℤ`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_of_isProjectiveOver`:
  higher direct images of quasi-coherent modules of finite type on a projective scheme over a
  Noetherian ring are finitely presented.
* `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_pullback_twistingSheaf_tensor`:
  higher direct images of sufficiently positive twists vanish in positive degrees.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5 and Theorem
  III.5.2.
* [The Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5) (coherence of higher
  direct images).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Coherence of projective higher direct images over a Noetherian affine base.** Let `X` be a
projective scheme over a Noetherian commutative ring `R` and `F` a quasi-coherent `𝒪_X`-module of
finite type. Then every higher direct image `R^q (X ↘ Spec R)_* F` is finitely presented. -/
theorem isFinitePresentation_higherDirectImage_of_isProjectiveOver (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage q).obj F).IsFinitePresentation := by
  let M : ModuleCat.{u} (CommRingCat.of R) := ModuleCat.of (CommRingCat.of R) (Cohomology F q)
  have : Module.Finite (CommRingCat.of R) M :=
    finite_cohomology_of_isProjectiveOver R F q
  have : Module.FinitePresentation (CommRingCat.of R) M :=
    Module.finitePresentation_of_finite (CommRingCat.of R) M
  exact (SheafOfModules.isFinitePresentation (Spec (.of R)).ringCatSheaf).prop_of_iso
    (tildeCohomologyIsoHigherDirectImage R F q)
    (isFinitePresentation_tilde M)

/-- **Serre vanishing for higher direct images.** Let `R` be a Noetherian commutative ring, `M` a
finite `R`-module, `i : X ⟶ Proj (Sym_R M)` a closed immersion over `Spec R`, and `F` a
quasi-coherent `𝒪_X`-module of finite type. Then there exists `n₀ : ℤ` such that
`R^q (X ↘ Spec R)_* (i^* 𝒪(n) ⊗ F) = 0` for every `n ≥ n₀` and every `q > 0`. -/
theorem exists_isZero_higherDirectImage_pullback_twistingSheaf_tensor
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}} [X.Over (Spec (.of R))]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M))
    [IsClosedImmersion i] [i.IsOver (Spec (.of R))] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      IsZero (((X ↘ Spec (.of R)).higherDirectImage q).obj
        ((pullback i).obj (Proj.twistingSheaf
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) n) ⊗ F)) := by
  have : X.IsProjectiveOver R :=
    Scheme.IsProjectiveOver.of_isClosedImmersion R i
  obtain ⟨n₀, hn₀⟩ := F.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor i
  refine ⟨n₀, fun n hn q hq ↦ ?_⟩
  let G : X.Modules := (pullback i).obj
    (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) n) ⊗ F
  have : G.IsQuasicoherent := isQuasicoherent_tensorObj X _ F
  have : Subsingleton (Cohomology G q) := hn₀ n hn q hq
  -- Synthesize `PreservesZeroMorphisms` before specializing to `.of R` so Lean's discrimination
  -- tree matches `tilde.functor _`.
  let _ : (tilde.functor (.of R)).PreservesZeroMorphisms :=
    (inferInstance : (tilde.functor _).PreservesZeroMorphisms)
  exact ((tilde.functor (.of R)).map_isZero
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of (CommRingCat.of R) (Cohomology G q)))).of_iso
    (tildeCohomologyIsoHigherDirectImage R G q).symm

end AlgebraicGeometry.Scheme.Modules

end
