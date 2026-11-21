/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.ZariskisMainTheorem
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.QuasiFinite.ZariskisMainTheorem

/-!
# Quasi-finiteness from fibre quotients

Let `S` be an `R`-algebra of finite type and `q` a prime ideal of `S` lying over `p = q.under R`.
By Zariski's main theorem (`Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`), `S` is quasi-finite over
`R` at `q` as soon as the quotient `S ⧸ p S` is quasi-finite over `R` at the image of `q`. More
generally, if `J ≤ p S` is an ideal of `S` such that `S ⧸ J` is quasi-finite over `R` at the image
of `q` (or globally, see `Algebra.QuasiFiniteAt.of_quasiFinite_quotient`), then `S` is quasi-finite
over `R` at `q`.

Both hypotheses are needed:
* Without `J ≤ (q.under R).map (algebraMap R S)`, take `R = k`, `S = k[X]`, and `J = q = (X)`:
  `S ⧸ J ≃ k` is finite over `k`, whereas `k[X]` is not quasi-finite over `k` at `(X)`.
* Without `Algebra.FiniteType R S`, let `R` be a discrete valuation ring with uniformizer `π` and
  fraction field `K`, and let `S = R + X K[X] ⊆ K[X]`. Then `π S = π R + X K[X]` is a maximal ideal
  `q` of `S` lying over `(π)` with `S ⧸ π S ≃ R ⧸ (π)` finite over `R`, yet
  `K ⊗[R] S_q ≃ K[X]_{(X)}` has dimension `1`, so `S` is not quasi-finite over `R` at `q`.

Combining `Algebra.QuasiFiniteAt.of_quasiFinite_quotient` with one-dimensional Noether normalization
(`TauCeti.exists_finite_aeval_of_krullDimLE_one`) yields a quasi-finite polynomial parameter lift
modulo a maximal ideal `𝔪` of `R`: when `A` is of finite type over `R` and `A ⧸ 𝔪 A` has Krull
dimension at most `1`, there exists `a : A` such that for every `x : A` congruent to `a` modulo
`𝔪 A`, `A` is quasi-finite over `R[X]` (via `X ↦ x`) at every prime containing `𝔪 A`.

## Main results

* `Algebra.QuasiFiniteAt.of_quasiFiniteAt_quotient`: for finite-type `S` over `R` and
  `J ≤ (q.under R).map (algebraMap R S)`, `Algebra.QuasiFiniteAt R p` at the image `p` of `q` in
  `S ⧸ J` implies `Algebra.QuasiFiniteAt R q`.
* `TauCeti.exists_forall_quasiFiniteAt_of_krullDimLE_one_quotient`: lifting a Noether
  normalization parameter modulo `𝔪 A` produces `a : A` making every `x ≡ a (mod 𝔪 A)` quasi-finite
  over `R[X]` at all primes above `𝔪`.

## References

* [Stacks Project, Lemma 55.8.3 (0C2U)](https://stacks.math.columbia.edu/tag/0C2U), choosing a
  parameter `x ∈ A` modulo `𝔪_R A` that is quasi-finite along the special fibre.
-/

public section

open Polynomial

namespace Algebra.QuasiFiniteAt

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

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
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact Ideal.map_comap_le)
    refine .of_surjectiveOnStalks p (Ideal.Quotient.factorₐ R hJ)
      (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.factor_surjective hJ)) _ ?_
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hfac : (Ideal.Quotient.factorₐ R hJ).toRingHom.comp (Ideal.Quotient.mk J) =
        Ideal.Quotient.mk ((q.under R).map (algebraMap R S)) := rfl
    rw [hp, Ideal.comap_comap, hfac,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr Ideal.map_comap_le]
  exact .of_weaklyQuasiFiniteAt q

end Algebra.QuasiFiniteAt

namespace TauCeti

/-- Let `A` be a finite-type `R`-algebra and `𝔪` a maximal ideal of `R` such that `A ⧸ 𝔪 A` has
Krull dimension at most `1`. Then there exists `a : A` such that for every `x : A` with
`x - a ∈ 𝔪 A` and every prime `q` of `A` containing `𝔪 A`, `A` is quasi-finite over `R[X]` (via
`X ↦ x`) at `q`. -/
@[stacks 0C2U]
theorem exists_forall_quasiFiniteAt_of_krullDimLE_one_quotient {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (𝔪 : Ideal R) [𝔪.IsMaximal]
    [Ring.KrullDimLE 1 (A ⧸ 𝔪.map (algebraMap R A))] :
    ∃ a : A, ∀ x : A, x - a ∈ 𝔪.map (algebraMap R A) →
      ∀ q : Ideal A, [q.IsPrime] → 𝔪.map (algebraMap R A) ≤ q →
        letI : Algebra R[X] A := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
        Algebra.QuasiFiniteAt R[X] q := by
  let J := 𝔪.map (algebraMap R A)
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let : Algebra (R ⧸ 𝔪) (A ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (R ⧸ 𝔪) (A ⧸ J) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType (R ⧸ 𝔪) (A ⧸ J) := .of_restrictScalars_finiteType R (R ⧸ 𝔪) (A ⧸ J)
  obtain ⟨x₀, hx₀⟩ := exists_finite_aeval_of_krullDimLE_one (R ⧸ 𝔪) (A ⧸ J)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := J) x₀
  refine ⟨a, fun x hxa q _ hq ↦ ?_⟩
  let : Algebra R[X] A := (Polynomial.aeval (R := R) x).toRingHom.toAlgebra
  have : IsScalarTower R R[X] A := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.FiniteType R[X] A := .of_restrictScalars_finiteType R R[X] A
  have hx_mk : Ideal.Quotient.mk J x = x₀ := by
    rw [← ha, Ideal.Quotient.eq]
    exact hxa
  have hfin_quot : (algebraMap R[X] (A ⧸ J)).Finite := by
    have hfac : algebraMap R[X] (A ⧸ J) =
        (Polynomial.aeval (R := R ⧸ 𝔪) x₀).toRingHom.comp
          (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) := by
      rw [IsScalarTower.algebraMap_eq R[X] A (A ⧸ J), RingHom.algebraMap_toAlgebra]
      ext r
      · simpa using IsScalarTower.algebraMap_apply R (R ⧸ 𝔪) (A ⧸ J) r
      · simpa using hx_mk
    rw [hfac]
    exact hx₀.comp
      (RingHom.Finite.of_surjective _ (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective))
  have : Module.Finite R[X] (A ⧸ J) := hfin_quot
  have hJ : J ≤ (q.under R[X]).map (algebraMap R[X] A) := by
    dsimp only [J]
    rw [IsScalarTower.algebraMap_eq R R[X] A, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr ?_)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R R[X] A]
    exact Ideal.map_le_iff_le_comap.mp hq
  exact Algebra.QuasiFiniteAt.of_quasiFinite_quotient q J hJ

end TauCeti
