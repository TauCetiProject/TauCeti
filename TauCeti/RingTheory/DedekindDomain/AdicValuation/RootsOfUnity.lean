/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.RootsOfUnity.Henselian

/-!
# Roots of unity of an adic completion and of its residue field

Let `v` be a height-one prime of a Dedekind domain `R` containing the prime `p`, and let `𝒪_v` be
the ring of integers of the completion at `v`. For `n` prime to `p`, reduction modulo the maximal
ideal is an isomorphism from the `n`-th roots of unity of `𝒪_v` onto those of its residue field.
This is Hensel's lemma for the complete, hence Henselian, local ring `𝒪_v`
(`TauCeti.rootsOfUnityEquivResidueField`), since `n` is a unit of `𝒪_v`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.rootsOfUnityAdicCompletionIntegersEquiv`: reduction of
  roots of unity of order prime to `p` at a height-one prime over `p`.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Lemma 10.1.1, p. 170, for the
  bijection of roots of unity of order prime to `p` in a `p`-modular system.
-/

public section

noncomputable section

open IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- At a height-one prime `v` containing the prime `p`, reduction is an isomorphism from the
`n`-th roots of unity of the completed integers onto those of the residue field, for `n` prime
to `p` (Webb, Lemma 10.1.1). -/
def rootsOfUnityAdicCompletionIntegersEquiv (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ v.asIdeal)
    {n : ℕ} (hn : n.Coprime p) :
    rootsOfUnity n (v.adicCompletionIntegers K) ≃*
      rootsOfUnity n (ResidueField (v.adicCompletionIntegers K)) :=
  TauCeti.rootsOfUnityEquivResidueField (v.isUnit_natCast_adicCompletionIntegers p hp hn)

/-- The isomorphism `rootsOfUnityAdicCompletionIntegersEquiv` is reduction modulo the maximal
ideal. -/
@[simp]
theorem coe_rootsOfUnityAdicCompletionIntegersEquiv (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ v.asIdeal) {n : ℕ} (hn : n.Coprime p)
    (ζ : rootsOfUnity n (v.adicCompletionIntegers K)) :
    ((v.rootsOfUnityAdicCompletionIntegersEquiv p hp hn ζ :
        (ResidueField (v.adicCompletionIntegers K))ˣ) : ResidueField (v.adicCompletionIntegers K)) =
      residue _ ((ζ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :=
  TauCeti.coe_rootsOfUnityEquivResidueField _ ζ

end IsDedekindDomain.HeightOneSpectrum
