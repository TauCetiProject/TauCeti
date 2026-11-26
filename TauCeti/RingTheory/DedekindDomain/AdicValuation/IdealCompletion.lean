/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CofinalLimit
public import TauCeti.RingTheory.AdicCompletion.Coprime
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
import TauCeti.RingTheory.Valuation.AdicSeparated

/-!
# Ideal-adic completions of a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K`. This file identifies the ideal-adic
completions `lim R ⧸ Iⁿ` of the ring `R` with products of the valuation rings `𝒪_v` of the
completions `K_v`.

For a height-one prime `v`, the `v`-adic completion of `R` is `𝒪_v`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionAsIdealAlgEquivIntegers`). Indeed
`R ⧸ vⁿ → 𝒪_v ⧸ 𝔪ⁿ` is bijective for every `n`
(`IsDedekindDomain.HeightOneSpectrum.quotientMap_maximalIdeal_pow_bijective`): both ideal
filtrations are cut out by the valuation, and `R` is dense in `𝒪_v`. Since `𝒪_v` is `𝔪`-adically
complete, the completions agree.

For a nonzero ideal `I`, only finitely many height-one primes contain `I`. They are pairwise
comaximal, and their intersection, the radical of `I`, has a power inside `I`. So the Chinese
remainder theorem decomposes the `I`-adic completion as an `R`-algebra
(`Ideal.adicCompletionAlgEquivPi`):

`lim R ⧸ Iⁿ ≃ ∏_{v ⊇ I} 𝒪_v`.

The exponents of the primes in `I` play no role, since only cofinality of powers matters; for
instance the `2`-adic completion of `ℤ[i]` is the single complete discrete valuation ring at
`1 + i`. For `I = (2)` in a Dedekind domain whose fraction field has characteristic different from
two, this is the decomposition of the dyadic completion of `R` into the complete discrete
valuation rings at its dyadic primes, with residue fields `R ⧸ v`
(`IsDedekindDomain.HeightOneSpectrum.residueFieldEquivAdicCompletionIntegers`). For the unit
ideal, as for `(2)` in `ℤ[1/2]` or in a field, the product is empty and both sides are zero rings.
Inverting a nonzero element `r ∈ v` in `𝒪_v` gives the completed field `K_v`
(`IsDedekindDomain.HeightOneSpectrum.isLocalization_away_adicCompletion`), so inverting `2` in a
dyadic factor gives its fraction field.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionAsIdealAlgEquivIntegers`: the `R`-algebra
  isomorphism `AdicCompletion v.asIdeal R ≃ₐ[R] 𝒪_v`.
* `Ideal.adicCompletionAlgEquivPi`: for `I ≠ ⊥`, the `R`-algebra isomorphism
  `AdicCompletion I R ≃ₐ[R] ∏_{v ⊇ I} 𝒪_v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.mk_adicCompletionAsIdealAlgEquivIntegers`: modulo `𝔪ⁿ`,
  the isomorphism `adicCompletionAsIdealAlgEquivIntegers` is the projection of the completion to
  `R ⧸ vⁿ`.
* `Ideal.adicCompletionAlgEquivPi_apply`: each coordinate of `adicCompletionAlgEquivPi` is the
  canonical map `lim R ⧸ Iⁿ → lim R ⧸ vⁿ` followed by `adicCompletionAsIdealAlgEquivIntegers`.
  With `AdicCompletion.ofPowLe_of` and `adicCompletionAsIdealAlgEquivIntegers_of`, `simp` reduces
  each coordinate on `R` to the canonical map `R → 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.isLocalization_away_adicCompletion`: `𝒪_v[1/r] = K_v` for
  a nonzero `r ∈ v`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 13, Proposition 18.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
* B. Calmès, E. Dotto, Y. Harpaz, F. Hebestreit, M. Land, K. Moi, D. Nardin, T. Nikolaus and
  W. Steimle, *Hermitian K-theory for stable ∞-categories III: Grothendieck–Witt groups of rings*,
  arXiv:2009.07225v4, proofs of Proposition 2.3.9 and Corollary 2.3.10, where the dyadic
  completion of a Dedekind domain is decomposed in this way.
-/

public section

open AdicCompletion IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- `under_maximalIdeal_adicCompletionIntegers` in the form taken by `AdicCompletion.mapₐ`. -/
private theorem asIdeal_le_comap_maximalIdeal :
    v.asIdeal ≤ (maximalIdeal (v.adicCompletionIntegers K)).comap
      (Algebra.ofId R (v.adicCompletionIntegers K)) :=
  (v.under_maximalIdeal_adicCompletionIntegers (K := K)).ge

/-- The `v`-adic completion `lim R ⧸ vⁿ` of a Dedekind domain is the ring of integers `𝒪_v` of
the completion of its fraction field at `v`. -/
noncomputable def adicCompletionAsIdealAlgEquivIntegers :
    AdicCompletion v.asIdeal R ≃ₐ[R] v.adicCompletionIntegers K :=
  (AlgEquiv.ofBijective (mapₐ (Algebra.ofId R (v.adicCompletionIntegers K))
      (v.asIdeal_le_comap_maximalIdeal K))
    (mapₐ_bijective _ _ fun n ↦ v.quotientMap_maximalIdeal_pow_bijective (K := K) n)).trans
    ((ofAlgEquiv (maximalIdeal (v.adicCompletionIntegers K))).symm.restrictScalars R)

/-- Modulo the `n`-th power of the maximal ideal of `𝒪_v`, `adicCompletionAsIdealAlgEquivIntegers`
is the projection of the completion to `R ⧸ v ^ n`. This characterizes
`adicCompletionAsIdealAlgEquivIntegers`, as `𝒪_v` is `𝔪`-adically separated. -/
@[simp]
theorem mk_adicCompletionAsIdealAlgEquivIntegers (n : ℕ) (x : AdicCompletion v.asIdeal R) :
    Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (v.adicCompletionAsIdealAlgEquivIntegers K x) =
      Ideal.quotientMap _ (algebraMap R (v.adicCompletionIntegers K))
        (v.under_maximalIdeal_pow_adicCompletionIntegers (K := K) n).ge
        (evalₐ v.asIdeal n x) := by
  rw [adicCompletionAsIdealAlgEquivIntegers, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    mk_ofAlgEquiv_symm, AlgEquiv.ofBijective_apply, evalₐ_mapₐ]
  -- `(Algebra.ofId R _).toRingHom` is `algebraMap R _` by definition.
  rfl

/-- `adicCompletionAsIdealAlgEquivIntegers` extends the canonical map `R → 𝒪_v`. -/
@[simp]
theorem adicCompletionAsIdealAlgEquivIntegers_of (r : R) :
    v.adicCompletionAsIdealAlgEquivIntegers K (of v.asIdeal R r) =
      algebraMap R (v.adicCompletionIntegers K) r :=
  (v.adicCompletionAsIdealAlgEquivIntegers K).commutes r

/-- Inverting a nonzero element `r ∈ v` of `R` in `𝒪_v` gives the completion `K_v`. For instance
`𝒪_v[1/2] = K_v` at a prime `v` containing `2`. The hypothesis `r ∈ v` is needed: an element
outside `v` is already a unit of `𝒪_v`. -/
theorem isLocalization_away_adicCompletion {r : R} (hr0 : r ≠ 0) (hr : r ∈ v.asIdeal) :
    IsLocalization.Away (algebraMap R (v.adicCompletionIntegers K) r) (v.adicCompletion K) := by
  have : IsHausdorff (Ideal.span {algebraMap R (v.adicCompletionIntegers K) r})
      (v.adicCompletionIntegers K) :=
    .of_isLocalRing _ _ <| Ideal.span_singleton_eq_top.not.mpr <|
      (v.isUnit_algebraMap_adicCompletionIntegers_iff r).not.mpr (not_not.mpr hr)
  exact TauCeti.PreValuationRing.isLocalization_away_of_isFractionRing
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R _)).mpr hr0) _

end IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain HeightOneSpectrum

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] {I : Ideal R}

/-- Distinct height-one primes are comaximal. -/
private theorem pairwise_isCoprime_heightOneSpectrum :
    Pairwise fun v w : {v : HeightOneSpectrum R // I ≤ v.asIdeal} ↦
      IsCoprime v.val.asIdeal w.val.asIdeal :=
  fun _ _ hvw ↦ isCoprime_of_isMaximal fun h ↦ hvw (Subtype.ext (HeightOneSpectrum.ext h))

/-- **Decomposition of an ideal-adic completion of a Dedekind domain.** For a nonzero ideal `I`
of a Dedekind domain `R` with fraction field `K`, the `I`-adic completion `lim R ⧸ Iⁿ` is the
product of the rings of integers `𝒪_v` of the completions of `K` at the finitely many height-one
primes `v ⊇ I`.

For `I = (2)` and `K` of characteristic different from two, this is the decomposition of the
dyadic completion of `R` over its dyadic primes. -/
noncomputable def adicCompletionAlgEquivPi (hI : I ≠ ⊥) :
    AdicCompletion I R ≃ₐ[R]
      ∀ v : {v : HeightOneSpectrum R // I ≤ v.asIdeal}, v.val.adicCompletionIntegers K :=
  haveI := finite_heightOneSpectrum_le hI
  (equivOfPowLe ⟨1, (pow_one I).le.trans (le_iInf fun v ↦ v.property)⟩
      (exists_iInf_heightOneSpectrum_pow_le hI)).trans <|
    (coprimeEquiv _ pairwise_isCoprime_heightOneSpectrum).trans <|
      AlgEquiv.piCongrRight fun v ↦ v.val.adicCompletionAsIdealAlgEquivIntegers K

/-- The coordinate of `adicCompletionAlgEquivPi` at `v ⊇ I` is the canonical map
`lim R ⧸ Iⁿ → lim R ⧸ vⁿ` followed by `adicCompletionAsIdealAlgEquivIntegers`. -/
@[simp]
theorem adicCompletionAlgEquivPi_apply (hI : I ≠ ⊥) (x : AdicCompletion I R)
    (v : {v : HeightOneSpectrum R // I ≤ v.asIdeal}) :
    adicCompletionAlgEquivPi K hI x v =
      v.val.adicCompletionAsIdealAlgEquivIntegers K
        (ofPowLe ⟨1, (pow_one I).le.trans v.property⟩ x) := by
  rw [adicCompletionAlgEquivPi, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.piCongrRight_apply, coprimeEquiv_apply, equivOfPowLe_apply]
  congr 1
  -- The coordinate of `coprimeEquiv` is a `mapₐ` along the identity, which is an `ofPowLe`.
  have hv : ∃ k : ℕ, (⨅ w : {w : HeightOneSpectrum R // I ≤ w.asIdeal}, w.val.asIdeal) ^ k ≤
      v.val.asIdeal := ⟨1, (pow_one _).le.trans (iInf_le _ v)⟩
  generalize_proofs h₁ h₂ h₃
  rw [← ofPowLe_eq_mapₐ_id (A := R) hv h₂, AlgHom.restrictScalars_apply, ofPowLe_ofPowLe]

end Ideal
