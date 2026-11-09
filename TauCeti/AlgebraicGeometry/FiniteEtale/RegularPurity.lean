/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal
import TauCeti.RingTheory.RegularLocalRing.Purity
import TauCeti.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Purity for regular local rings of dimension two

Let `A` be a regular local ring of dimension two. Every finite étale cover of the punctured
spectrum `Spec A ∖ {𝔪}` extends to a finite étale scheme over `Spec A`, that is, purity holds for
`A` (`TauCeti.IsLocalRing.PurityHolds A`).

A regular local ring of dimension two is a unique factorization domain, hence an integrally closed
domain, so purity for `A` is equivalent to its algebraic form
(`TauCeti.IsLocalRing.purityHolds_iff_forall_etale`): every finite normal torsion-free `A`-algebra
which is étale at every prime not lying over `𝔪` is étale over `A`. In dimension two this algebraic
form holds (`TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`): such an algebra is
free over `A` by miracle flatness, and its discriminant is a unit because a nonunit would lie in a
prime of height at most one, where the algebra is étale.

This is the base case of the induction on the dimension in Stacks, Lemma 58.21.3 (0BMA), part (1).

## Main results

* `TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`: purity holds for a regular local ring
  of dimension two.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA).
* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Théorème 3.4.
-/

public section

namespace TauCeti.IsLocalRing

variable {A : Type*} [CommRing A] [IsRegularLocalRing A]

/-- **Purity for a regular local ring of dimension two.** Every finite étale cover of the
punctured spectrum of a two-dimensional regular local ring extends to a finite étale scheme over
its spectrum. -/
@[stacks 0BMA "(1) in dimension two"]
theorem purityHolds_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) : PurityHolds A := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid hdim.le
  refine (purityHolds_iff_forall_etale hdim.ge).mpr fun B ↦ ?_
  obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
  exact Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two hdim (fun 𝔮 _ ↦ hnormal 𝔮)
    fun q _ hq ↦ have := het q hq; inferInstance

end TauCeti.IsLocalRing
