/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Roots of a polynomial in an intermediate field

For an intermediate field `L` of `E / K` and a polynomial `p` over `K`, the roots of `p` in `L`,
with multiplicities, are the roots of `p` in `E` that lie in `L`. This is Mathlib's
`Polynomial.filter_roots_map_range_eq_map_roots` for the inclusion `L → E`, whose range is `L`.
It lets root counts in different subfields of one ambient field be compared inside that field.

A monic polynomial of degree `n` over `K` is its coefficient vector `a : Fin n → K`, through
`TauCeti.Polynomial.monicOfCoeff`. The root count `L.rootCount a` is the number of roots of that
polynomial lying in `L`, counted with multiplicity. When that polynomial is irreducible of
degree `n` and `[L : K] = n`, a root `x` in `E` lies in `L` exactly when `K⟮x⟯ = L`, so the roots
in `L` are the roots generating `L`.

## Main definitions

* `IntermediateField.rootCount L a`: the number of roots, with multiplicity, of the monic
  polynomial with coefficient vector `a` that lie in `L`.

## Main results

* `IntermediateField.filter_aroots_eq_map_aroots`: the roots in `E` that lie in `L` are the roots
  in `L`, with multiplicities.
* `IntermediateField.rootCount_eq_card_filter_adjoin_eq`: for an irreducible `monicOfCoeff a` and
  `[L : K] = n`, the roots in `L` are the roots `x` in `E` with `K⟮x⟯ = L`.
-/

public section
noncomputable section

open Polynomial
open scoped IntermediateField

namespace IntermediateField

open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff)

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The roots in `E` of a polynomial over `K` that lie in an intermediate field `L` are its roots
in `L`, with the same multiplicities. -/
theorem filter_aroots_eq_map_aroots (L : IntermediateField K E) (p : K[X])
    [DecidablePred (· ∈ L)] :
    (p.aroots E).filter (· ∈ L) = (p.aroots L).map (↑) := by
  classical
  have h := filter_roots_map_range_eq_map_roots (algebraMap L E).injective
    (p.map (algebraMap K L))
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, ← aroots_def, ← aroots_def] at h
  convert h using 1
  · exact Multiset.filter_congr fun x _ ↦ ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  · exact Multiset.map_congr rfl fun x _ ↦ (algebraMap_apply L x).symm

/-- The root count of a coefficient vector `a : Fin n → K` in a subextension `L`: the number of
roots of the monic polynomial `monicOfCoeff a` lying in `L`, counted with multiplicity. -/
def rootCount (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) : ℕ :=
  ((monicOfCoeff a).aroots L).card

/-- The defining equation of `IntermediateField.rootCount`. -/
theorem rootCount_def (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) :
    L.rootCount a = ((monicOfCoeff a).aroots L).card := by
  rw [rootCount]

open Classical in
/-- **The roots in a degree-`n` subextension are its generators.** If the monic polynomial
`monicOfCoeff a` with coefficient vector `a : Fin n → K` is irreducible, then for an intermediate
field `L` of `E / K` with `[L : K] = n` the roots of `monicOfCoeff a` in `L` correspond, with
multiplicities, to the roots `x` in `E` with `K⟮x⟯ = L`. -/
theorem rootCount_eq_card_filter_adjoin_eq {n : ℕ} {a : Fin n → K}
    (ha : Irreducible (monicOfCoeff a)) {L : IntermediateField K E}
    (hL : Module.finrank K L = n) :
    L.rootCount a = (((monicOfCoeff a).aroots E).filter fun x ↦ K⟮x⟯ = L).card := by
  classical
  rw [L.rootCount_def, ← Multiset.card_map, ← L.filter_aroots_eq_map_aroots]
  congr 1
  refine Multiset.filter_congr fun x hx ↦ ⟨fun hxL ↦ ?_, fun h ↦ h ▸ mem_adjoin_simple_self K x⟩
  -- `K⟮x⟯ ≤ L`, and both have degree `n`, which is positive as `K⟮x⟯` is finite over `K`.
  have hroot := (mem_aroots.mp hx).2
  have hint : IsIntegral K x := ⟨_, monic_monicOfCoeff a, hroot⟩
  have hdeg : Module.finrank K K⟮x⟯ = n := by
    rw [adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic ha hroot (monic_monicOfCoeff a),
      natDegree_monicOfCoeff]
  have := adjoin.finiteDimensional hint
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hL ▸ hdeg ▸ Module.finrank_pos)
  exact eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hxL) (hdeg.trans hL.symm)

end IntermediateField
