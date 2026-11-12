/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.FieldDivision
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete

/-!
# Examples: rational covers of a discrete adic spectrum

`TauCeti.ValuationSpectrum.span_eq_top_of_rationalSubset_subset_iUnion` needs the covering
hypothesis. Over the discrete ring `k[X]` with plus ring `k`, the single rational subset
`R(1, X/X) = {|X| ≥ 1}` does not cover `R(1/1) = Spa(k[X], k)`: the trivial valuation with support
`(X)` lies in the second and not in the first. Correspondingly, `X` does not generate the unit ideal
of `k[X]`, the localization of `k[X]` at `1`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.28, case (c).
-/

open Polynomial TauCeti.ValuationSpectrum

variable {k : Type*} [Field k] [DecidableEq k] [TopologicalSpace k[X]] [DiscreteTopology k[X]]

-- The trivial valuation with support `(X)` is a point of `R(1/1)` outside `R(1, X/X)`.
example (p : PrimeSpectrum k[X]) (hp : p.asIdeal = Ideal.span {X}) :
    trivialSection p ∈ rationalSubset (algebraMap k k[X]).range {1} 1 ∧
      trivialSection p ∉ rationalSubset (algebraMap k k[X]).range ({1, X} : Finset k[X]) X := by
  rw [trivialSection_mem_rationalSubset_iff, trivialSection_mem_rationalSubset_iff, hp,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact ⟨⟨isOpen_discrete _, fun h ↦ not_isUnit_X (isUnit_of_dvd_one h)⟩,
    fun h ↦ h.2 dvd_rfl⟩

-- The denominator `X` does not generate the unit ideal of the localization of `k[X]` at `1`.
example : Ideal.span (Set.range fun _ : Unit ↦ algebraMap k[X] (Localization.Away (1 : k[X])) X) ≠
    ⊤ := by
  rw [Set.range_const, Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h := hu.map (IsLocalization.atOne k[X] (Localization.Away (1 : k[X]))).symm
  rw [AlgEquiv.commutes, Algebra.algebraMap_self_apply] at h
  exact not_isUnit_X h
