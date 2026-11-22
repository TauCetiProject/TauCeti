/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.FieldTheory.IsAlgClosed.Units

/-!
# Injectivity of root subgroup parametrizations over fields

Over every field `k` and for every Chevalley datum `D`, every root subgroup parametrization
`D.rootSubgroupPoints γ k` is injective. No assumption on the characteristic, the field size, or
the character lattice is needed.

The proof passes to an algebraic closure, uses the nonvanishing of the coordinate root
`D.coordinateRoot γ` (recovered from `ChevalleyDatum.sum_coordinateRoot_smul` and
`RootPairing.ne_zero`) to realize a nonzero root parameter as a torus character via
`TauCeti.torusCharacter_surjective`, and conjugates by that torus point to reach the
nontriviality theorem `ChevalleyDatum.rootSubgroupPoints_ofAdd_one_ne_one`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: injectivity of every root
  subgroup parametrization over a field.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_eq_iff` and
  `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_eq_one_iff`: `@[simp]` cancellation and
  identity lemmas for root subgroup parameters over a field.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

-- Match the coefficient structure used by `D.points`, including on an algebraic closure.
attribute [local instance high] Ring.toIntAlgebra
attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Over any field, every root subgroup parametrization of a Chevalley datum is injective.
No assumption on the characteristic, the field size, or the character lattice is needed. -/
theorem rootSubgroupPoints_injective (k : Type v) [Field k] (γ : Fin t.numRoots) :
    Function.Injective (D.rootSubgroupPoints γ k) := by
  classical
  rw [injective_iff_map_eq_one]
  intro u hu
  by_contra hne
  have ha : Multiplicative.toAdd u ≠ 0 := fun h0 =>
    hne (by simpa [h0] using (ofAdd_toAdd u).symm)
  have hcoord : D.coordinateRoot γ ≠ 0 := fun h0 => by
    have hsum := D.sum_coordinateRoot_smul γ
    simp only [h0, Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hsum
    exact (t.simplyConnectedRootDatum ht).ne_zero γ hsum.symm
  let ι := algebraMap k (AlgebraicClosure k)
  let c : (AlgebraicClosure k)ˣ := Units.mk0 (ι (Multiplicative.toAdd u)) (by simpa [ι] using ha)
  obtain ⟨s, hchar⟩ := torusCharacter_surjective (R := AlgebraicClosure k) hcoord c⁻¹
  dsimp only at hchar
  have hmap : D.rootSubgroupPoints γ (AlgebraicClosure k)
      (Multiplicative.ofAdd (ι (Multiplicative.toAdd u))) = 1 := by
    have h := congrArg ((D.pointsPresentation k).map
      (D.pointsPresentation (AlgebraicClosure k)) ι) hu
    simpa only [D.map_rootSubgroupPoints, map_one] using h
  have hconj := D.torusPoints_conj_rootSubgroupPoints γ (AlgebraicClosure k) s
    (ι (Multiplicative.toAdd u))
  rw [hmap, mul_one, mul_inv_cancel, hchar] at hconj
  have hmul : ((c⁻¹ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) *
      ι (Multiplicative.toAdd u) = 1 := by
    simpa [c] using Units.inv_mul c
  rw [hmul] at hconj
  exact D.rootSubgroupPoints_ofAdd_one_ne_one (AlgebraicClosure k) γ hconj.symm

/-- Equality of two values of the same root subgroup parametrization over a field reduces to
equality of their parameters. -/
@[simp]
theorem rootSubgroupPoints_eq_iff (k : Type v) [Field k] (γ : Fin t.numRoots)
    (u v : Multiplicative k) :
    D.rootSubgroupPoints γ k u = D.rootSubgroupPoints γ k v ↔ u = v :=
  (D.rootSubgroupPoints_injective k γ).eq_iff

/-- A root subgroup element over a field is `1` if and only if its parameter is `1`. -/
@[simp]
theorem rootSubgroupPoints_eq_one_iff (k : Type v) [Field k] (γ : Fin t.numRoots)
    (u : Multiplicative k) :
    D.rootSubgroupPoints γ k u = 1 ↔ u = 1 :=
  map_eq_one_iff (D.rootSubgroupPoints γ k) (D.rootSubgroupPoints_injective k γ)

end TauCeti.DynkinType.ChevalleyDatum
