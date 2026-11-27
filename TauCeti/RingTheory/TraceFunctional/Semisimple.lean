/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TraceFunctional.Radical
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Semisimplicity of trace quotients

An Artinian trace quotient is semisimple if its induced trace vanishes on square-zero elements.
This applies in particular to finite-dimensional trace quotients over fields. The scalar ring
need not be a field, and no characteristic assumption is required.

## Provenance

`LinearMap.isSemisimpleRing_quotient_traceRadical` adapts the radical argument of
`New.exists_wedderburn` in `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`
in grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The formulation for arbitrary algebras and Artinian trace
quotients is new here.

## References

* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

namespace LinearMap

/-- An Artinian quotient by the trace radical is semisimple if the quotient trace vanishes on
square-zero elements. -/
theorem isSemisimpleRing_quotient_traceRadical
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (τ : A →ₗ[R] R) (hτ : ∀ x y, τ (x * y) = τ (y * x))
    [IsArtinianRing (A ⧸ τ.traceRadical hτ)]
    (hsq : ∀ x : A ⧸ τ.traceRadical hτ, x * x = 0 → τ.quotientTrace hτ x = 0) :
    IsSemisimpleRing (A ⧸ τ.traceRadical hτ) := by
  classical
  let I := τ.traceRadical hτ
  have hzero (x : A ⧸ I) (hx : ∀ y, x * y * x = 0) : x = 0 := by
    refine τ.quotientTrace_nondegenerate hτ x fun y ↦ hsq (x * y) ?_
    rw [← mul_assoc, hx y, zero_mul]
  have hrad : Ring.jacobson (A ⧸ I) = ⊥ := by
    refine (eq_bot_or_exists_atom_le (Ring.jacobson (A ⧸ I))).resolve_right
      fun ⟨J, hatom, hJ⟩ ↦ ?_
    have kills : Ring.jacobson (A ⧸ I) • J = ⊥ :=
      hatom.lt_iff.1 (Submodule.FG.of_finite.jacobson_smul_lt hatom.ne_bot)
    apply hatom.ne_bot
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    exact hzero x fun y ↦ kills.le (Submodule.smul_mem_smul
      (Ideal.mul_mem_right y _ (hJ hx)) hx)
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hrad

end LinearMap
