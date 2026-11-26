/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Spec
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# Coherence and Serre vanishing for higher direct images on projective schemes

Let `R` be a Noetherian commutative ring, `X` a scheme projective over `R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R X`), and `M` a quasi-coherent `𝒪_X`-module of finite
type. Combining Serre's cohomology finiteness theorem
(`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`) and Serre's vanishing
theorem
(`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor`)
with the `Spec R` higher-direct-image characterization
(`AlgebraicGeometry.Scheme.Modules.tildeCohomologyIsoHigherDirectImage` and
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_Spec_iff`) shows:
* coherence: every higher direct image `Rⁿ (X ↘ Spec R)_* M` is finitely presented
  (`AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`), the
  projective-over-`Spec R` case of Hartshorne, Theorem III.8.8(b) and Stacks Tag 02O5;
* Serre vanishing for higher direct images: for every closed immersion
  `i : X ⟶ Proj (Sym_R M₀)` over `Spec R` with `M₀` finite,
  `R^q (X ↘ Spec R)_* (i^* 𝒪(n) ⊗ F) = 0` for every `q > 0` and all sufficiently large `n : ℤ`
  (`exists_isZero_higherDirectImage_pullback_twistingSheaf_tensor`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.5,
  Theorem III.5.2, and Theorem III.8.8(b).
* [The Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

/-- **Coherence of higher direct images for projective schemes over a Noetherian ring** (the
projective-over-`Spec R` case of Hartshorne, Theorem III.8.8(b), and of the proper theorem in
Stacks Tag 02O5): if `X` is projective over a Noetherian ring `R` and `M` is a quasi-coherent
`𝒪_X`-module of finite type, then every higher direct image `Rⁿ (X ↘ Spec R)_* M` is finitely
presented (hence coherent). -/
instance IsProjectiveOver.isFinitePresentation_higherDirectImage (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    (((X ↘ Spec (.of R)).higherDirectImage n).obj M).IsFinitePresentation :=
  (M.isFinitePresentation_higherDirectImage_Spec_iff R n).mpr
    (Module.finitePresentation_of_finite R (Cohomology M n))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

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
    (G.tildeCohomologyIsoHigherDirectImage R q).symm

end AlgebraicGeometry.Scheme.Modules

end
