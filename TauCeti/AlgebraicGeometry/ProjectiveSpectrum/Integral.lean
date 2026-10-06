/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Properties
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Reducedness and integrality of `Proj`

For an `ℕ`-graded ring `A`, this file shows that `Proj A` is a reduced scheme when `A` is a reduced
ring, and that it is an integral scheme when `A` is an integral domain whose irrelevant ideal is
nonzero, that is, when `A` has a nonzero homogeneous element of positive degree.

## Main results

* `AlgebraicGeometry.Proj.isReduced`: `Proj A` is reduced if `A` is reduced.
* `AlgebraicGeometry.Proj.isIntegral_of_isDomain`: `Proj A` is integral if `A` is a domain with
  nonzero irrelevant ideal.

## References

* Stacks Project, Tag 01M3 (Proj of a graded ring).

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/ForMathlib/ProjIntegral.lean`, declaration
`AlgebraicGeometry.Proj.isIntegral_of_isDomain`. Here reducedness is a separate instance for `Proj`
of any reduced graded ring rather than of a domain, and the positivity hypothesis is phrased as
the nonvanishing of the irrelevant ideal.
-/

public section

open HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- `Proj A` of a reduced graded ring `A` is a reduced scheme. -/
instance isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) :=
  -- each standard chart `Spec A_{(f)}` is reduced
  have (i : _) : IsReduced ((affineOpenCover 𝒜).openCover.X i) :=
    inferInstanceAs (IsReduced (Spec (.of (Away 𝒜 _))))
  .of_openCover _ (affineOpenCover 𝒜).openCover

-- `Proj A` of a graded domain `A` with nonzero irrelevant ideal, that is, with a nonzero
-- homogeneous element of positive degree, is irreducible.
private theorem irreducibleSpace_of_isDomain [IsDomain A]
    (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) : IrreducibleSpace (Proj 𝒜) :=
  -- the zero ideal is a relevant homogeneous prime lying below every point, hence a generic point
  (irreducibleSpace_def _).mpr <| IsGenericPoint.isIrreducible <| Set.eq_univ_of_forall fun y ↦
    (ProjectiveSpectrum.le_iff_mem_closure 𝒜 ⟨⊥, Ideal.isPrime_bot, mt le_bot_iff.mp h⟩ y).mp
      (bot_le (a := y.asHomogeneousIdeal))

/-- `Proj A` of a graded domain `A` with nonzero irrelevant ideal, that is, with a nonzero
homogeneous element of positive degree, is an integral scheme. -/
theorem isIntegral_of_isDomain [IsDomain A] (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IsIntegral (Proj 𝒜) :=
  -- an irreducible reduced scheme is integral; reducedness is the instance `Proj.isReduced`
  have := irreducibleSpace_of_isDomain 𝒜 h
  isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Proj
