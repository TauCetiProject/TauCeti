/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.FiniteGaloisIntermediateField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.LinearMap.JointlyInjective
import TauCeti.NumberTheory.Chebotarev.Density.ResidueDegree

/-!
# Chebotarev selection of primes with injective joint localization

Let `F` be a number field, `H` a finite-dimensional vector space and `loc v : H →ₗ[k] M v` a
family of linear maps indexed by the height-one primes `v` of `𝓞 F`, together with a set of
*admissible* primes. In Taylor–Wiles arguments `H` is a dual Selmer group, `loc v` is
localization at `v`, and admissibility encodes congruence and eigenvalue conditions at `v`.

Suppose that every nonzero `c : H` is *detected* by a Frobenius class: a finite Galois
subextension `L / F` and a conjugacy class `C` of `Gal(L/F)` such that, outside a finite set,
every prime with Frobenius class `C` in `L` is admissible and does not kill `c`. Suppose also that
some Frobenius class consists, outside a finite set, of admissible primes. Then for every finite
set `B` of primes to avoid and every `q ≥ dim H` there are exactly `q` admissible primes outside
`B`, all of residue degree one over `ℚ`, on which the joint localization `c ↦ (loc v c)_{v ∈ Q}`
is injective. The second hypothesis supplies the padding primes; it is needed when `H = 0`.

By the Chebotarev density theorem each Frobenius class contains infinitely many primes of
residue degree one, which is
`NumberField.Chebotarev.infinite_frobeniusPrimeSet_inter_setOf_inertiaDeg_eq_one`; the primes are
then chosen by `LinearMap.exists_finset_card_eq_injective`.

## Main results

* `NumberField.Chebotarev.exists_primes_jointly_injective`: the selection theorem.

## References

* P. B. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  897–1113, proof of Lemma 6.2.32.
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace NumberField.Chebotarev

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- A set of primes containing a Frobenius class of a finite Galois subextension, up to finitely
many primes, has infinitely many primes of residue degree one over `ℚ`. -/
private theorem infinite_inter_setOf_inertiaDeg_eq_one_of_frobeniusPrimeSet_subset
    {S : Set (HeightOneSpectrum (𝓞 F))}
    (h : ∃ (L : FiniteGaloisIntermediateField F Ω) (C : ConjClasses (L ≃ₐ[F] L))
      (E : Finset (HeightOneSpectrum (𝓞 F))), ∀ v ∈ frobeniusPrimeSet F L C, v ∉ E → v ∈ S) :
    (S ∩ {v | v.asIdeal.inertiaDeg ℤ = 1}).Infinite := by
  obtain ⟨L, C, E, h⟩ := h
  refine ((infinite_frobeniusPrimeSet_inter_setOf_inertiaDeg_eq_one F L C).sdiff
    E.finite_toSet).mono ?_
  rintro v ⟨⟨hC, hdeg⟩, hE⟩
  exact ⟨h v hC hE, hdeg⟩

/-- **Shared Chebotarev selection for Selmer detection.** Let `loc v : H →ₗ[k] M v` be linear maps
out of a finite-dimensional space, indexed by the primes of a number field `F`. Suppose every
nonzero `c : H` has a detecting Frobenius class in a finite Galois subextension of `Ω / F`, all of
whose primes outside a finite set are admissible with `loc v c ≠ 0`, and that some Frobenius class
consists of admissible primes outside a finite set. Then for every finite set `B` and every
`q ≥ dim H` there are exactly `q` admissible primes outside `B`, all of residue degree one over
`ℚ`, whose joint localization `c ↦ (loc v c)_{v ∈ Q}` is injective. -/
theorem exists_primes_jointly_injective
    {k H : Type*} [DivisionRing k] [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    {M : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, AddCommGroup (M v)] [∀ v, Module k (M v)]
    (loc : ∀ v, H →ₗ[k] M v) (admissible : Set (HeightOneSpectrum (𝓞 F)))
    (detect : ∀ c : H, c ≠ 0 →
      ∃ (L : FiniteGaloisIntermediateField F Ω) (C : ConjClasses (L ≃ₐ[F] L))
        (E : Finset (HeightOneSpectrum (𝓞 F))),
        ∀ v ∈ frobeniusPrimeSet F L C, v ∉ E → v ∈ admissible ∧ loc v c ≠ 0)
    (padding : ∃ (L : FiniteGaloisIntermediateField F Ω) (C : ConjClasses (L ≃ₐ[F] L))
      (E : Finset (HeightOneSpectrum (𝓞 F))),
      ∀ v ∈ frobeniusPrimeSet F L C, v ∉ E → v ∈ admissible)
    (B : Finset (HeightOneSpectrum (𝓞 F))) (q : ℕ) (hq : Module.finrank k H ≤ q) :
    ∃ Q : Finset (HeightOneSpectrum (𝓞 F)), Q.card = q ∧ Disjoint Q B ∧
      (∀ v ∈ Q, v ∈ admissible ∧ v.asIdeal.inertiaDeg ℤ = 1) ∧
      Function.Injective fun c : H ↦ fun v : Q ↦ loc v c := by
  have hdetect (c : H) (hc : c ≠ 0) :
      {v ∈ admissible ∩ {v | v.asIdeal.inertiaDeg ℤ = 1} | loc v c ≠ 0}.Infinite := by
    refine (infinite_inter_setOf_inertiaDeg_eq_one_of_frobeniusPrimeSet_subset
      (S := {v | v ∈ admissible ∧ loc v c ≠ 0}) (detect c hc)).mono ?_
    rintro v ⟨⟨hv, hvc⟩, hdeg⟩
    exact ⟨⟨hv, hdeg⟩, hvc⟩
  obtain ⟨Q, hcard, hQB, hQP, hQ⟩ := LinearMap.exists_finset_card_eq_injective loc
    (infinite_inter_setOf_inertiaDeg_eq_one_of_frobeniusPrimeSet_subset padding) hdetect B hq
  exact ⟨Q, hcard, hQB, fun v hv ↦ hQP hv, hQ⟩

end NumberField.Chebotarev
