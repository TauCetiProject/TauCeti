/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Group.FundamentalDomain.Discrete

/-!
# Finite covolume forces unimodularity

Let `Λ` be a countable subgroup of a locally compact group `T`, acting on `T` by left
multiplication, and let `μ` be a regular left Haar measure on `T`. If some fundamental domain `D`
of this action has finite measure, then `T` is unimodular: its modular character is trivial, and
`μ` is also right invariant.

Right multiplication by `t` commutes with the left action of `Λ` and preserves `μ`-null sets, so
the preimage `D t⁻¹` of `D` under `x ↦ x * t` is again a fundamental domain and has the measure of
`D`. By Mathlib's convention for `MeasureTheory.Measure.modularCharacter`, the same preimage has
measure `Δ(t) μ D`. As `Λ` is countable, the translates of `D` cover `T` up to a null set, so
`0 < μ D`; with `μ D < ∞` this forces `Δ(t) = 1`. A discrete subgroup of a second countable group
is countable (`countable_of_Lindelof_of_discrete`).

A discrete subgroup of a second countable locally compact Hausdorff group has a measurable
fundamental domain for its left action, supplied by
`TauCeti.MeasureTheory.Group.FundamentalDomain.Discrete`. When the quotient `Λ\T` is compact,
a compact set `K` meets every orbit, and the fundamental domain has
measure at most `μ K`. So a second countable locally compact Hausdorff group with a cocompact
discrete subgroup is unimodular.

## Main statements

* `MeasureTheory.IsFundamentalDomain.modularCharacter_eq_one_of_measure_ne_top`: a countable
  subgroup acting on the left with a fundamental domain of finite regular Haar measure forces the
  modular character to be trivial.
* `MeasureTheory.IsFundamentalDomain.isMulRightInvariant_of_measure_ne_top`: under the same
  hypotheses the Haar measure is right invariant.
* `Subgroup.modularCharacter_eq_one_of_compactSpace`: a second countable locally compact
  Hausdorff group with a discrete subgroup of compact quotient is unimodular.

## Provenance

The statements of `MeasureTheory.IsFundamentalDomain.modularCharacter_eq_one_of_measure_ne_top` and
`MeasureTheory.IsFundamentalDomain.isMulRightInvariant_of_measure_ne_top` are adapted from
`New.isMulRightInvariant_of_finite_covolume`
(file `src/Lib/Adelic/QuotientMeasure/Basic.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There the
covolume is the total mass of a quotient measure built from a cutoff weight; here the hypothesis is
a null-measurable fundamental domain in the sense of `MeasureTheory.IsFundamentalDomain`, and the
proofs, by right translation of the fundamental domain, are new here.

## References

* Dave Witte Morris, *Introduction to Arithmetic Groups*, Deductive Press, 2015,
  Proposition 4.1.18.
-/

public section

open MeasureTheory Measure Set
open scoped NNReal ENNReal Pointwise

variable {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]

namespace MeasureTheory.IsFundamentalDomain

variable [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [μ.IsHaarMeasure] [μ.Regular]
  {Λ : Subgroup T} [Countable Λ] {D : Set T}

/-- **Finite covolume forces unimodularity.** If a countable subgroup `Λ`, acting on `T` by left
multiplication, has a fundamental domain of finite measure for a regular Haar measure, then the
modular character of `T` is trivial. -/
theorem modularCharacter_eq_one_of_measure_ne_top (hD : IsFundamentalDomain Λ D μ)
    (hDμ : μ D ≠ ∞) : (modularCharacter : T →* ℝ≥0) = 1 := by
  ext t
  -- Right translation commutes with the left action and preserves null sets.
  have hDt : IsFundamentalDomain Λ ((· * t) ⁻¹' D) μ :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right_of_regular μ t) Function.bijective_id
      fun g x ↦ smul_mul_assoc g x t
  have h := hDt.measure_eq hD
  rw [measure_preimage_mul_right_eq_modularCharacter_mul_of_regular,
    ENNReal.mul_eq_right (hD.measure_ne_zero (NeZero.ne μ)) hDμ] at h
  exact_mod_cast h

/-- If a countable subgroup, acting on `T` by left multiplication, has a fundamental domain of
finite measure for a regular Haar measure `μ`, then `μ` is also right invariant. -/
theorem isMulRightInvariant_of_measure_ne_top (hD : IsFundamentalDomain Λ D μ)
    (hDμ : μ D ≠ ∞) : μ.IsMulRightInvariant :=
  ⟨fun t ↦ by
    rw [map_right_mul_eq_modularCharacter_smul_of_regular,
      hD.modularCharacter_eq_one_of_measure_ne_top hDμ, MonoidHom.one_apply, one_smul]⟩

end MeasureTheory.IsFundamentalDomain

namespace Subgroup

variable [SecondCountableTopology T] [T2Space T] (Λ : Subgroup T) [DiscreteTopology Λ]

variable [CompactSpace (MulAction.orbitRel.Quotient Λ T)]

include Λ in
/-- **A cocompact discrete subgroup forces unimodularity.** A second countable locally compact
Hausdorff group with a discrete subgroup of compact quotient has trivial modular character. -/
theorem modularCharacter_eq_one_of_compactSpace : (modularCharacter : T →* ℝ≥0) = 1 := by
  borelize T
  have : Countable Λ := countable_of_Lindelof_of_discrete
  obtain ⟨D, -, hD, hDμ⟩ := Λ.exists_isFundamentalDomain_measure_lt_top (haar : Measure T)
  exact hD.modularCharacter_eq_one_of_measure_ne_top hDμ.ne

end Subgroup
