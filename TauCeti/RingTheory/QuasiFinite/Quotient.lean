/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic

import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finiteness from fibre quotients

Let `S` be an `R`-algebra of finite type and `q` a prime ideal of `S` lying over `p = q.under R`.
By Zariski's main theorem (`Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`), `S` is quasi-finite over
`R` at `q` as soon as the quotient `S ⧸ p S` is quasi-finite over `R` at the image of `q`. More
generally, if `J ≤ p S` is an ideal of `S` such that `S ⧸ J` is quasi-finite over `R` at the image
of `q` (`Algebra.QuasiFiniteAt.of_quasiFiniteAt_quotient`) or globally over `R`
(`Algebra.QuasiFiniteAt.of_quasiFinite_quotient`), then `S` is quasi-finite over `R` at `q`.

Both hypotheses are needed:
* Without `J ≤ (q.under R).map (algebraMap R S)`, take `R = k`, `S = k[X]`, and `J = q = (X)`:
  `S ⧸ J ≃ k` is finite over `k`, whereas `k[X]` is not quasi-finite over `k` at `(X)`.
* Without `Algebra.FiniteType R S`, let `R` be a discrete valuation ring with uniformizer `π` and
  fraction field `K`, and let `S = R + X K[X] ⊆ K[X]`. Then `π S = π R + X K[X]` is a maximal ideal
  `q` of `S` lying over `(π)` with `S ⧸ π S ≃ R ⧸ (π)` finite over `R`, yet
  `K ⊗[R] S_q ≃ K[X]_{(X)}` has dimension `1`, so `S` is not quasi-finite over `R` at `q`.

## Main results

* `Algebra.QuasiFiniteAt.of_quasiFinite_quotient`: quasi-finiteness from a globally quasi-finite
  quotient by an ideal `I ≤ (q.under R) A`.
* `Algebra.QuasiFiniteAt.of_quasiFiniteAt_quotient`: for finite-type `S` over `R` and
  `J ≤ (q.under R).map (algebraMap R S)`, `Algebra.QuasiFiniteAt R p` at the image `p` of `q` in
  `S ⧸ J` implies `Algebra.QuasiFiniteAt R q`.

## References

* [Stacks Project, Tag 00Q9](https://stacks.math.columbia.edu/tag/00Q9), Zariski's main theorem.
-/

public section

namespace Algebra.QuasiFiniteAt

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite type algebra is quasi-finite at a prime `q` if its quotient by an ideal
contained in the extension of `q.under R` is quasi-finite over the base. -/
theorem of_quasiFinite_quotient [Algebra.FiniteType R A] (q : Ideal A) [q.IsPrime]
    (I : Ideal A) [Algebra.QuasiFinite R (A ⧸ I)]
    (hI : I ≤ (q.under R).map (algebraMap R A)) : Algebra.QuasiFiniteAt R q := by
  have : Algebra.QuasiFinite R (A ⧸ (q.under R).map (algebraMap R A)) :=
    .of_surjective_algHom (Ideal.Quotient.factorₐ R hI) (Ideal.Quotient.factor_surjective hI)
  have : Algebra.WeaklyQuasiFiniteAt R q := inferInstance
  exact .of_weaklyQuasiFiniteAt q

variable {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-- If `S` is of finite type over `R`, `J` is an ideal of `S` contained in `(q.under R) S`, and
`S ⧸ J` is quasi-finite over `R` at the prime `p` corresponding to `q`, then `S` is quasi-finite
over `R` at `q`. -/
theorem of_quasiFiniteAt_quotient {J : Ideal S} {q : Ideal S} [q.IsPrime]
    (hJ : J ≤ (q.under R).map (algebraMap R S)) (p : Ideal (S ⧸ J)) [p.IsPrime]
    [Algebra.QuasiFiniteAt R p] (hp : p.comap (Ideal.Quotient.mk J) = q) :
    Algebra.QuasiFiniteAt R q := by
  have : Algebra.WeaklyQuasiFiniteAt R q := by
    delta Algebra.WeaklyQuasiFiniteAt
    have : (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime Ideal.map_comap_le
    refine .of_surjectiveOnStalks p (Ideal.Quotient.factorₐ R hJ)
      (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.factor_surjective hJ)) _ ?_
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hfac : (Ideal.Quotient.factorₐ R hJ).toRingHom.comp (Ideal.Quotient.mk J) =
        Ideal.Quotient.mk ((q.under R).map (algebraMap R S)) := by
      ext x
      exact Ideal.Quotient.factorₐ_apply_mk R hJ x
    rw [hp, Ideal.comap_comap, hfac, Ideal.comap_map_mk Ideal.map_comap_le]
  exact .of_weaklyQuasiFiniteAt q

end Algebra.QuasiFiniteAt
