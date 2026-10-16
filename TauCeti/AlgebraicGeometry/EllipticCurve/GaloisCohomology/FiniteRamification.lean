/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere

/-!
# A finite ramification set for Selmer classes

Let `R` be a Dedekind domain with fraction field `K` and finite residue fields. For an elliptic
curve over `K` and an invertible multiplier `m`, there is a single finite set of primes outside
which every `m`-Selmer class is unramified. The Selmer group here uses the completions at the
height-one primes of `R`.

The exceptional set excludes the denominators of the equation, the divisors of its discriminant,
and the primes dividing `m`. At every remaining prime the integral model is elliptic, and the
local Kummer condition is unramified. This supplies the finite ramification set used in the
arithmetic finiteness argument for Selmer groups; finiteness of the Selmer group itself is a
separate assertion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1.5 and X.4.2.
-/

public section

namespace TauCeti

open ContCohomology IsDedekindDomain _root_.ValuativeRel WeierstrassCurve

/-- All Selmer classes are unramified outside a common finite set of primes. This set can be
chosen to contain any given finite set. The local fields are the completions at the height-one
primes of a Dedekind domain with finite residue fields. -/
theorem exists_finset_torsionRes_mem_unramifiedTorsionCohomology
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (τ : ∀ v : HeightOneSpectrum R,
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    {m : ℕ} (hm : (m : K) ≠ 0) (S : Finset (HeightOneSpectrum R)) :
    ∃ T : Finset (HeightOneSpectrum R), S ⊆ T ∧
      ∀ c ∈ W.selmerGroup τ m, ∀ v ∉ T,
        W.torsionRes (τ v) m c ∈
          (W.baseChange (v.adicCompletion K)).unramifiedTorsionCohomology m := by
  obtain ⟨T, hST, hgood, hprime⟩ :=
    exists_finset_isElliptic_integralModel_adicCompletion R W hm S
  refine ⟨T, hST, fun c hc v hv => ?_⟩
  obtain ⟨_, _⟩ := hgood v hv
  apply W.torsionRes_mem_unramifiedTorsionCohomology_of_mem_selmerGroup τ v _ hc
  rw [Ne, ringChar.spec, v.ringChar_residueField_adicCompletion_dvd_iff]
  exact hprime v hv

end TauCeti
