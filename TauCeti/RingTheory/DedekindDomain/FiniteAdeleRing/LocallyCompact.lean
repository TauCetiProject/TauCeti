/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Local compactness of finite adele rings

The finite adele ring of a Dedekind domain with finite residue fields is locally compact.  Each
adic completion is a nonarchimedean local field, and its integer ring is compact and open.  The
result then follows from the local-compactness theorem for restricted products.

The finite-residue-field hypothesis is stated directly, rather than specialized to rings of
integers, so this applies to every Dedekind domain for which the same local compactness argument is
valid.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.instCompactSpaceAdicCompletionIntegers`: the integers in an
  adic completion are compact when the residue field is finite.
* `IsDedekindDomain.FiniteAdeleRing.instLocallyCompactSpace`: the finite adele ring is locally
  compact when all residue fields are finite.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The integer ring in an adic completion is compact when its residue field is finite. -/
instance instCompactSpaceAdicCompletionIntegers (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] : CompactSpace (v.adicCompletionIntegers K) := by
  let _ : IsNonarchimedeanLocalField (v.adicCompletion K) := inferInstance
  apply isCompact_iff_compactSpace.mp
  -- Expose the underlying subring so the comparison with the valuative integer ring rewrites it.
  change IsCompact ((v.adicCompletionIntegers K).toSubring : Set (v.adicCompletion K))
  rw [← v.integer_eq_adicCompletionIntegers (K := K)]
  exact IsNonarchimedeanLocalField.isCompact_closedBall (v.adicCompletion K) 1

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adele ring of a Dedekind domain with finite residue fields is locally compact. -/
instance instLocallyCompactSpace [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs <| LocallyCompactSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

end IsDedekindDomain.FiniteAdeleRing
