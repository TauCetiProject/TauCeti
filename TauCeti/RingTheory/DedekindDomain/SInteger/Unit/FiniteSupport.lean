/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# Finitely generated unit groups lie in `S`-units for a finite `S`

Let `R` be a Dedekind domain with fraction field `K`. A nonzero element of `K` has valuation `1`
at all but finitely many height-one primes of `R`. Collecting these finite supports over a finite
generating set shows that a finitely generated subgroup of `Kˣ` lies in the `S`-units for one
finite set `S` of primes, and likewise for a finitely generated subgroup of a finite product of
copies of `Kˣ`, coordinatewise.

## Main results

* `Subgroup.FG.exists_finset_le_unit`: a finitely generated subgroup of `Kˣ` is contained in
  `S.unit K` for some finite set `S` of height-one primes of `R`.
* `Subgroup.FG.exists_finset_le_pi_unit`: a finitely generated subgroup of `ι → Kˣ`, for finite
  `ι`, is contained in the product of copies of `S.unit K` for one finite `S`.
* `Subgroup.fg_of_le_unit`: conversely, when `Rˣ` is finitely generated, every subgroup of `Kˣ`
  contained in `S.unit K` for a finite `S` is finitely generated.
* `Subgroup.fg_iff_exists_finset_le_unit`: when `Rˣ` is finitely generated, a subgroup of `Kˣ` is
  finitely generated exactly when it lies in the `S`-units for some finite `S`.
-/

public section

open IsDedekindDomain

namespace Subgroup.FG

variable (R : Type*) {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A finitely generated subgroup of the units of a fraction field is contained in the `S`-units
for one finite set `S` of height-one primes. -/
theorem exists_finset_le_unit {Γ : Subgroup Kˣ} (hΓ : Γ.FG) :
    ∃ S : Finset (HeightOneSpectrum R), Γ ≤ (S : Set (HeightOneSpectrum R)).unit K := by
  classical
  obtain ⟨s, hs, hsf⟩ := (Subgroup.fg_iff Γ).mp hΓ
  have hfin := hsf.biUnion fun x _ ↦
    HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := R) x.ne_zero
  refine ⟨hfin.toFinset, ?_⟩
  rw [← hs, Subgroup.closure_le]
  intro x hx
  refine (Set.mem_unit_iff _ _).mpr fun v hv ↦ ?_
  by_contra hvx
  exact hv (hfin.mem_toFinset.mpr (Set.mem_biUnion hx hvx))

/-- A finitely generated group of tuples in the units of a fraction field is contained in a
product of `S`-unit groups for one finite set `S` of height-one primes. -/
theorem exists_finset_le_pi_unit {ι : Type*} [Finite ι] {Γ : Subgroup (ι → Kˣ)} (hΓ : Γ.FG) :
    ∃ S : Finset (HeightOneSpectrum R),
      Γ ≤ Subgroup.pi Set.univ (fun _ : ι ↦ (S : Set (HeightOneSpectrum R)).unit K) := by
  obtain ⟨s, hs, hsf⟩ := (Subgroup.fg_iff Γ).mp hΓ
  obtain ⟨S, hS⟩ := exists_finset_le_unit R ((Subgroup.fg_iff _).mpr
    ⟨_, rfl, hsf.biUnion fun x _ ↦ Set.finite_range fun i ↦ x i⟩)
  refine ⟨S, ?_⟩
  rw [← hs, Subgroup.closure_le]
  intro x hx
  exact (Subgroup.mem_pi Set.univ).mpr fun i _ ↦
    hS (Subgroup.subset_closure (Set.mem_biUnion hx (Set.mem_range_self i)))

end Subgroup.FG

namespace Subgroup

variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **A subgroup of `S`-units is finitely generated** when `S` is finite and `Rˣ` is finitely
generated: it is a subgroup of the finitely generated commutative group `S.unit K`
(`Set.unit_fg_of_units`). -/
theorem fg_of_le_unit [Monoid.FG Rˣ] {S : Set (HeightOneSpectrum R)} [Finite S]
    {Γ : Subgroup Kˣ} (h : Γ ≤ S.unit K) : Γ.FG :=
  ((Group.fg_iff_subgroup_fg _).mp (Set.unit_fg_of_units S K)).of_le h

variable (R) in
/-- **Finitely generated subgroups of `Kˣ` are the subgroups of `S`-units for finite `S`**, when
`Rˣ` is finitely generated (for instance for the ring of integers of a number field, by
Dirichlet's unit theorem). -/
theorem fg_iff_exists_finset_le_unit [Monoid.FG Rˣ] {Γ : Subgroup Kˣ} :
    Γ.FG ↔ ∃ S : Finset (HeightOneSpectrum R), Γ ≤ (S : Set (HeightOneSpectrum R)).unit K :=
  ⟨FG.exists_finset_le_unit R, fun ⟨_, h⟩ ↦ fg_of_le_unit h⟩

end Subgroup
