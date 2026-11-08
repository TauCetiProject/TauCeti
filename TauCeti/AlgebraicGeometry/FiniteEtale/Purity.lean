/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Purity

/-!
# Purity for regular local rings of dimension two

A regular local ring `A` of dimension two is pure: every finite étale cover of its punctured
spectrum extends to a finite étale scheme over `Spec A`.

A regular local ring is a Noetherian integrally closed domain, so purity for `A` is equivalent to
the algebraic statement that every finite normal torsion-free `A`-algebra which is étale at every
prime not lying over the maximal ideal is étale over `A`
(`TauCeti.IsLocalRing.purityHolds_iff_forall_etale`). In dimension two, such an algebra is free
over `A` by miracle flatness, and a finite free algebra over a Noetherian local ring of dimension
at least two which is unramified away from the closed point is étale by the discriminant criterion
(`TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`).

## Main results

* `TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`: purity holds for a regular local ring
  of dimension two.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), part (1), in
  the case of dimension two.
* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Théorème 3.4.
-/

public section

universe u

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Purity for a two-dimensional regular local ring.** If `A` is a regular local ring of
dimension two, every finite étale cover of the punctured spectrum of `A` extends to a finite étale
scheme over `Spec A`. -/
@[stacks 0BMA "(1) in dimension two"]
theorem purityHolds_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) : PurityHolds A := by
  refine (purityHolds_iff_forall_etale hdim.ge).mpr fun B ↦ ?_
  obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
  exact TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two hdim (fun 𝔮 _ ↦ hnormal 𝔮)
    fun q _ hq ↦ have := het q hq; inferInstance

end TauCeti.IsLocalRing
