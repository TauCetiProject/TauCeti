/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Group actions on the height-one spectrum

A group `G` acting on a commutative ring `R` by ring automorphisms acts on its height-one spectrum,
the nonzero prime ideals of `R` (the finite places, when `R` is a Dedekind domain):
`σ • w` is the place whose ideal is the pointwise image `σ • w.asIdeal`, which is the preimage of
`w.asIdeal` under `σ⁻¹`. This file defines the action, available in the `Pointwise` scope like
Mathlib's pointwise action on ideals and on valuation subrings, and records its basic properties.

* The stabilizer of a place is the stabilizer of its ideal, Mathlib's decomposition group
  `MulAction.stabilizer G w.asIdeal`.
* Contraction to `A` is unchanged by the action when `R` is an `A`-algebra on which `G` acts
  `A`-linearly. When moreover `G` is finite and `A` is its ring of invariants (for instance
  `Gal(L/K)` acting on `𝓞 L` over `𝓞 K`), the orbit of a place is exactly the set of places with
  the same contraction.

## Main declarations

* `IsDedekindDomain.HeightOneSpectrum.pointwiseMulAction`: the action of `G` on the places of `R`.
* `IsDedekindDomain.HeightOneSpectrum.asIdeal_smul`, `asIdeal_smul_eq_comap`: its effect on ideals.
* `IsDedekindDomain.HeightOneSpectrum.stabilizer_eq_stabilizer_asIdeal`: stabilizers.
* `IsDedekindDomain.HeightOneSpectrum.under_smul`: contraction is invariant.
* `IsDedekindDomain.HeightOneSpectrum.mem_orbit_iff_under_eq`: orbits are the fibres of
  contraction.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open scoped Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R]

variable {G : Type*} [Group G] [MulSemiringAction G R]

/-- A group acting on a commutative ring by ring automorphisms acts on its height-one spectrum,
by the pointwise action on ideals. This is available as an instance in the `Pointwise` scope. -/
@[instance_reducible]
def pointwiseMulAction : MulAction G (HeightOneSpectrum R) where
  smul σ w := ⟨σ • w.asIdeal, inferInstance, fun h ↦ w.ne_bot <| by
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact smul_zero σ⁻¹⟩
  one_smul w := HeightOneSpectrum.ext (one_smul G w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

scoped[Pointwise] attribute [instance] IsDedekindDomain.HeightOneSpectrum.pointwiseMulAction

@[simp]
theorem asIdeal_smul (σ : G) (w : HeightOneSpectrum R) : (σ • w).asIdeal = σ • w.asIdeal := by
  rfl

/-- The ideal of `σ • w` is the preimage of the ideal of `w` under `σ⁻¹`. -/
theorem asIdeal_smul_eq_comap (σ : G) (w : HeightOneSpectrum R) :
    (σ • w).asIdeal = w.asIdeal.comap (MulSemiringAction.toRingHom G R σ⁻¹) :=
  Ideal.pointwise_smul_eq_comap w.asIdeal

/-- The stabilizer of a place is the stabilizer of its ideal. -/
theorem stabilizer_eq_stabilizer_asIdeal (w : HeightOneSpectrum R) :
    MulAction.stabilizer G w = MulAction.stabilizer G w.asIdeal := by
  ext σ
  simp [HeightOneSpectrum.ext_iff]

/-- A group acting on `R` over `A` does not change the contraction of a place to `A`. -/
theorem under_smul {A : Type*} [CommSemiring A] [Algebra A R] [SMulCommClass G A R] (σ : G)
    (w : HeightOneSpectrum R) :
    (σ • w).asIdeal.under A = w.asIdeal.under A :=
  Ideal.under_smul A w.asIdeal σ

variable {A : Type*} [CommRing A] [Algebra A R]

/-- For a finite group `G` acting on `R` with invariants `A`, two places of `R` lie in one orbit
exactly when they have the same contraction to `A`. -/
theorem mem_orbit_iff_under_eq [Finite G] [SMulCommClass G A R] [Algebra.IsInvariant A R G]
    {w w' : HeightOneSpectrum R} :
    w' ∈ MulAction.orbit G w ↔ w'.asIdeal.under A = w.asIdeal.under A := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨σ, rfl⟩
    exact under_smul σ w
  · obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A R G w.asIdeal w'.asIdeal h.symm
    exact ⟨σ, HeightOneSpectrum.ext hσ.symm⟩

end IsDedekindDomain.HeightOneSpectrum
