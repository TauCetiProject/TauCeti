/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Spec
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Serre
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# Coherent higher direct images and asymptotic vanishing for projective schemes

Let `R` be a Noetherian commutative ring, `X` a scheme projective over `R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R X`), and `M` a quasi-coherent `𝒪_X`-module of finite
type. Combining Serre's cohomology finiteness theorem
(`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`) with the `Spec R`
higher-direct-image characterization
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_Spec_iff`) shows that
every higher direct image `Rⁿ (X ↘ Spec R)_* M` is finitely presented (hence coherent)
(`AlgebraicGeometry.Scheme.IsProjectiveOver.isFinitePresentation_higherDirectImage`). This is the
projective-over-`Spec R` case of the coherence of higher direct images for projective morphisms
over Noetherian bases (Hartshorne, Theorem III.8.8(b)) and for proper morphisms over locally
Noetherian bases (Stacks Tag 02O5).

Combining Serre's vanishing theorem for closed subschemes of projective space
(`AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`)
with the affine-base global-sections comparison
(`AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_of_subsingleton_cohomology`) yields the
asymptotic vanishing of `R^q (i ≫ projToSpec R M)_* (F ⊗ i^* 𝒪(m))` for closed immersions
`i : X ⟶ Proj (Sym_R M)` over a Noetherian ring `R`
(`AlgebraicGeometry.Scheme.Hom.exists_isZero_higherDirectImage_tensor_pullback_twistingSheaf`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2,
  Proposition III.8.5, and Theorem III.8.8(b) (the projective-over-`Spec R` case).
* [The Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT).
* [The Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5) (the
  projective-over-`Spec R` case of the proper theorem).
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

namespace Hom

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` to an affine scheme and a
quasi-coherent `𝒪_X`-module `M`, if `H^q(X, M)` is subsingleton then `R^q f_* M` is zero. -/
theorem isZero_higherDirectImage_of_subsingleton_cohomology {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    [Subsingleton (Cohomology M q)] :
    IsZero ((f.higherDirectImage q).obj M) := by
  have : Subsingleton (cohomologyOn M q ⊤) :=
    (cohomologyOnTopIso M q).addCommGroupIsoToAddEquiv.injective.subsingleton
  have : Subsingleton (cohomologyOn M q (f ⁻¹ᵁ ⊤)) :=
    (eqToIso (congrArg (cohomologyOn M q) f.preimage_top)).addCommGroupIsoToAddEquiv
      |>.injective.subsingleton
  have : Subsingleton Γ((f.higherDirectImage q).obj M, ⊤) :=
    (f.higherDirectImageSectionsAddEquiv M q (isAffineOpen_top Y)).symm.injective.subsingleton
  exact ((f.higherDirectImage q).obj M).isZero_of_subsingleton_sections_top

/-- **Higher direct image vanishing for twists on projective schemes.** Let `R` be a Noetherian
ring, `M` a finitely generated `R`-module, and `i : X ⟶ Proj (Sym_R M)` a closed immersion. For
every quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such that
`R^q (i ≫ projToSpec R M)_* (F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem exists_isZero_higherDirectImage_tensor_pullback_twistingSheaf {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M] {X : Scheme.{u}}
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      IsZero (((i ≫ TauCeti.SymmetricAlgebra.projToSpec R M).higherDirectImage q).obj
        (F ⊗ (Scheme.Modules.pullback i).obj
          (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m))) := by
  obtain ⟨m₀, hm₀⟩ := i.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf F
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let Om := Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m
  have : Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj Om) q) := hm₀ m hm q hq
  exact isZero_higherDirectImage_of_subsingleton_cohomology
    (i ≫ TauCeti.SymmetricAlgebra.projToSpec R M) (F ⊗ (Scheme.Modules.pullback i).obj Om) q

end Hom

end AlgebraicGeometry.Scheme

end
