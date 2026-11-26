/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Dedekind domains and ring isomorphisms

Being a Dedekind domain is invariant under ring isomorphisms
(`IsDedekindDomain.of_ringEquiv`), as each of its conditions is: being a domain, being Noetherian,
having Krull dimension at most one and being integrally closed. This transports the Dedekind
property of a ring of integers `𝓞 K` to an explicit model of it, such as `ℤ[√d]`.
-/

public section

/-- A ring isomorphic to a Dedekind domain is a Dedekind domain. -/
theorem IsDedekindDomain.of_ringEquiv {R A : Type*} [CommRing R] [CommRing A]
    [IsDedekindDomain R] (e : R ≃+* A) : IsDedekindDomain A := by
  have := e.symm.toMulEquiv.isDomain
  have := isNoetherianRing_of_ringEquiv R e
  have := Ring.DimensionLEOne.of_ringEquiv e.symm
  exact (isDedekindDomain_iff A (FractionRing A)).2 ⟨inferInstance, inferInstance, inferInstance,
    (isIntegrallyClosed_iff _).1 (IsIntegrallyClosed.of_equiv e)⟩
