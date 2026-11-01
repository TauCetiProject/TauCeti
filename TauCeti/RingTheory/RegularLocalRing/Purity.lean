/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Purity
public import TauCeti.RingTheory.RegularLocalRing.MiracleFlatness
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import TauCeti.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.RegularLocalRing.UniqueFactorization
import TauCeti.RingTheory.Unramified.Normal

/-!
# Purity for regular local rings of small dimension

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

Over a regular local ring `A` of dimension one or two, the same algebras `B` satisfy purity of the
branch locus: if `B` is unramified over `A` at every prime of height one, it is étale over `A`.
This is the finite algebraic form of Stacks, Lemma 58.21.4 (0BMB), the case to which that lemma
is reduced by étale localization. In dimension two, a prime of `B` not lying over the closed
point lies over a prime of height at most one, so it has height at most one by going down and
the previous result applies. In dimension one, `A` is a discrete valuation ring, so `B` is flat
over `A`, and every prime of `B` has height at most one. The hypothesis that `A` is not a field
cannot be dropped: a purely inseparable field extension has no prime of height one and is not
étale.

## Main results

* `TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`: a finite torsion-free algebra
  with normal localizations over a two-dimensional regular local ring, unramified away from the
  closed point, is étale.
* `TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_ringKrullDim_le_two`: a finite
  torsion-free algebra with normal localizations over a regular local ring of dimension one or
  two, unramified at every prime of height one, is étale.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), part (2), whose
  statement needs `B` torsion free over `A`, in the case of dimension two.
* [The Stacks Project, Lemma 58.21.4](https://stacks.math.columbia.edu/tag/0BMB), purity of the
  branch locus, for finite algebras over a regular local ring of dimension one or two.
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

/-- **Purity of the branch locus over a regular local ring of dimension one or two.** Let `A` be
a regular local ring of dimension one or two and `B` a finite torsion-free `A`-algebra whose
localizations at maximal ideals are normal domains. If `B` is unramified over `A` at every prime
of height one, then `B` is étale over `A`. -/
@[stacks 0BMB "finite algebras over a regular local ring of dimension one or two"]
theorem etale_of_isUnramifiedAt_height_eq_one_of_ringKrullDim_le_two
    (hdim₁ : 1 ≤ ringKrullDim A) (hdim₂ : ringKrullDim A ≤ 2)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hunram : ∀ (q : Ideal B) [q.IsPrime], q.height = 1 → Algebra.IsUnramifiedAt A q) :
    Algebra.Etale A B := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid hdim₂
  have hA : ¬IsField A := fun h ↦ absurd (ringKrullDim_eq_zero_of_isField h ▸ hdim₁) (by decide)
  -- `B` is unramified at every prime lying over a prime of `A` of height at most one.
  have key (q : Ideal B) [q.IsPrime] (hq : (q.under A).height ≤ 1) : Algebra.IsUnramifiedAt A q :=
    .of_forall_height_eq_one hA hunram q
      ((q.height_eq_height_under_of_isIntegral_of_hasGoingDown (R := A)).trans_le hq)
  rcases hdim₂.lt_or_eq with hlt | h2
  · -- Dimension one: `A` is a discrete valuation ring, so `B` is flat over `A`, and every prime
    -- of `B` lies over a prime of height at most one.
    have h1 : ringKrullDim A = 1 := le_antisymm (Order.le_of_lt_succ hlt) hdim₁
    have := IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr h1
    have : Algebra.FormallyUnramified A B := Algebra.formallyUnramified_iff_forall.mpr fun q ↦
      key q.1 (by exact_mod_cast h1 ▸ Ideal.height_le_ringKrullDim_of_isPrime)
    have := Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType A B)
    exact Algebra.Etale.of_formallyUnramified_of_flat
  · -- Dimension two: a prime not lying over the closed point lies over a prime of height at
    -- most one, and purity for `A` applies.
    refine etale_of_finiteNormal_of_ringKrullDim_eq_two h2 hnormal fun q _ hq ↦ key q ?_
    exact not_lt.mp ((Ideal.lt_height_iff_eq_maximalIdeal (n := 1) h2).not.mpr hq)

end TauCeti.Algebra
