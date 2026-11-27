/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Spec
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite

/-!
# Coherence of higher direct images for projective schemes over a Noetherian ring

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

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.8.8(b) (the
  projective-over-`Spec R` case).
* [The Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5) (the
  projective-over-`Spec R` case of the proper theorem).
-/

public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

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

end
