/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Finite sets of elements are `S`-integral for almost all `S`

Every finite subset of the fraction field `K` of a Dedekind domain `R` lies in the `S`-integers
for all `S` containing a suitable finite set of places
(`Finset.exists_finset_forall_subset_integer`), since each element of `K` is integral away from
finitely many places (`IsDedekindDomain.HeightOneSpectrum.Support.finite`).
-/

public section

namespace Finset

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Every finite set of elements of `K` lies in the `S`-integers for all `S` containing a suitable
finite set of places. -/
theorem exists_finset_forall_subset_integer (F : Finset K) :
    ∃ S₀ : Finset (HeightOneSpectrum R), ∀ S : Set (HeightOneSpectrum R), (S₀ : Set _) ⊆ S →
      (F : Set K) ⊆ S.integer K := by
  classical
  refine ⟨F.biUnion fun f ↦ (HeightOneSpectrum.Support.finite R f).toFinset, fun S hS f hf ↦ ?_⟩
  rw [SetLike.mem_coe, Set.mem_integer_iff]
  intro v hv
  by_contra h
  exact hv (hS (Finset.mem_biUnion.mpr ⟨f, hf, by simpa [HeightOneSpectrum.Support] using h⟩))

end Finset
