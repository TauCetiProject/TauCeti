/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Purity
public import TauCeti.RingTheory.RegularLocalRing.MiracleFlatness

/-!
# Purity for regular local rings of dimension two

Let `A` be a regular local ring of dimension two and `B` a finite `A`-algebra which is torsion
free as an `A`-module and whose localizations at maximal ideals are normal domains. If `B` is
unramified at every prime not lying over the closed point of `Spec A`, then `B` is étale over
`A`. This is the dimension-two case of purity for regular local rings in its algebraic form.

The proof combines two results. Normality makes `B` free over `A`
(`TauCeti.Algebra.free_of_normal_dim_two`). For a finite free algebra over a Noetherian local ring
of dimension at least two, a nonunit discriminant would lie in a prime of height at most one,
hence a prime other than the closed point, contradicting unramifiedness there
(`TauCeti.Algebra.etale_of_isUnramifiedAt_of_two_le_ringKrullDim`).

Torsion-freeness cannot be dropped: the algebra `A × κ(A)` is finite and normal and is étale at
every prime not lying over the closed point, but it is not flat over `A`
(`TauCeti.IsLocalRing.not_flat_prod_residueField`).

## Main results

* `TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`: a finite torsion-free algebra
  with normal localizations over a two-dimensional regular local ring, unramified away from the
  closed point, is étale.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), part (2), whose
  statement needs `B` torsion free over `A`, in the case of dimension two.
-/

public section

open IsLocalRing

namespace TauCeti.Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsRegularLocalRing A]
  [Module.Finite A B] [Module.IsTorsionFree A B]

/-- **Purity for a two-dimensional regular local ring.** A finite torsion-free algebra over a
two-dimensional regular local ring whose localizations at maximal ideals are normal domains is
étale, provided it is unramified at every prime not lying over the closed point. -/
@[stacks 0BMA "(2) in dimension two, with B torsion free over A"]
theorem etale_of_finiteNormal_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hunram : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsUnramifiedAt A q) : Algebra.Etale A B := by
  have := free_of_normal_dim_two hdim hnormal
  exact etale_of_isUnramifiedAt_of_two_le_ringKrullDim hdim.ge hunram

end TauCeti.Algebra
