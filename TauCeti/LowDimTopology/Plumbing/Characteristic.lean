/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.ModEq
public import TauCeti.LowDimTopology.Plumbing.IntersectionForm

/-!
# Characteristic covectors of a plumbing lattice

This file adds the characteristic-covector parity condition for the integral lattice attached
to a plumbing graph. For a plumbing graph `P`, a covector `k : V → ℤ` is characteristic when its
value on each basis sphere is congruent modulo two to the sphere's self-intersection, namely
`P.weight v`.

This is the first parity layer used in Némethi's lattice homology: the chain groups are indexed
by lattice points together with characteristic covectors, and later weight functions are built
from these covectors and the plumbing intersection form.

## Main definitions

* `TauCeti.PlumbingGraph.IsCharacteristicVector`: the vertex-wise parity condition
  `k v ≡ P.weight v [ZMOD 2]`.
* `TauCeti.PlumbingGraph.characteristicVectors`: the subtype of characteristic covectors.
* `TauCeti.PlumbingGraph.canonicalCharacteristic`: the canonical covector whose coordinates are
  the vertex weights.

## Main results

* `TauCeti.PlumbingGraph.isCharacteristicVector_iff_intersection_single`: the parity condition
  can be read from the self-pairing of each basis vector.
* Characteristic covectors are stable under adding twice an integral covector, and the
  difference of two characteristic covectors is pointwise even.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), which asks for plumbing graphs and their lattices together with lattice
points and weight functions. The characteristic-covector convention follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} (P : PlumbingGraph V)

/-- A covector of the plumbing lattice is characteristic when its value on every basis sphere is
congruent modulo two to that sphere's self-intersection. For the plumbing basis this is the
usual condition `k(v) ≡ v · v (mod 2)`, since `v · v = P.weight v`. -/
def IsCharacteristicVector (k : V → ℤ) : Prop :=
  ∀ v : V, k v ≡ P.weight v [ZMOD 2]

/-- The subtype of characteristic covectors of the plumbing lattice. -/
def characteristicVectors :=
  { k : V → ℤ // P.IsCharacteristicVector k }

/-- Characteristic covectors are exactly the covectors satisfying the vertex-wise parity
condition. -/
theorem isCharacteristicVector_iff (k : V → ℤ) :
    P.IsCharacteristicVector k ↔ ∀ v : V, k v ≡ P.weight v [ZMOD 2] :=
  Iff.rfl

/-- The canonical characteristic covector whose coordinates are the vertex weights. -/
abbrev canonicalCharacteristic : V → ℤ :=
  P.weight

/-- The canonical covector is characteristic. -/
theorem isCharacteristicVector_canonicalCharacteristic :
    P.IsCharacteristicVector P.canonicalCharacteristic := by
  intro v
  rfl

/-- The canonical characteristic covector has coordinates the vertex weights. -/
@[simp]
theorem canonicalCharacteristic_apply (v : V) : P.canonicalCharacteristic v = P.weight v :=
  rfl

section Form

variable [DecidableEq V] [Fintype V]

/-- Characteristicness can be read from the self-pairing of the plumbing basis vectors. -/
theorem isCharacteristicVector_iff_intersection_single (k : V → ℤ) :
    P.IsCharacteristicVector k ↔
      ∀ v : V, k v ≡ P.intersectionForm (Pi.single v 1) (Pi.single v 1) [ZMOD 2] := by
  constructor
  · intro hk v
    simpa using hk v
  · intro hk v
    simpa using hk v

/-- The canonical characteristic covector evaluated on a basis vector is that basis vector's
self-pairing. -/
theorem canonicalCharacteristic_apply_eq_intersection_single (v : V) :
    P.canonicalCharacteristic v =
      P.intersectionForm (Pi.single v 1) (Pi.single v 1) := by
  simp [canonicalCharacteristic]

end Form

/-- Adding twice an integral covector preserves characteristicness. -/
theorem IsCharacteristicVector.add_two_mul {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) : P.IsCharacteristicVector fun v => k v + 2 * l v := by
  intro v
  have htwo : (2 * l v : ℤ) ≡ 0 [ZMOD 2] := by
    exact Int.modEq_zero_iff_dvd.mpr ⟨l v, by ring⟩
  simpa using (hk v).add htwo

/-- Adding an even-valued covector preserves characteristicness. -/
theorem IsCharacteristicVector.add_of_forall_even {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : ∀ v : V, Even (l v)) :
    P.IsCharacteristicVector fun v => k v + l v := by
  intro v
  simpa using (hk v).add (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp (hl v)))

/-- Negating a characteristic covector preserves characteristicness. -/
theorem IsCharacteristicVector.neg {k : V → ℤ}
    (hk : P.IsCharacteristicVector k) : P.IsCharacteristicVector fun v => -k v := by
  intro v
  have hweight : -P.weight v ≡ P.weight v [ZMOD 2] :=
    Int.modEq_iff_dvd.mpr ⟨P.weight v, by ring⟩
  exact (hk v).neg.trans hweight

/-- The pointwise difference of two characteristic covectors is even. -/
theorem IsCharacteristicVector.even_sub {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : P.IsCharacteristicVector l) (v : V) :
    Even (k v - l v) := by
  have hmod : k v - l v ≡ 0 [ZMOD 2] := by
    simpa using (hk v).sub (hl v)
  exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)

/-- The pointwise difference of two characteristic covectors is congruent to zero modulo two. -/
theorem IsCharacteristicVector.sub_modEq_zero {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : P.IsCharacteristicVector l) (v : V) :
    k v - l v ≡ 0 [ZMOD 2] := by
  simpa using (hk v).sub (hl v)

/-- A covector obtained from the canonical characteristic covector by adding twice another
covector is characteristic. -/
theorem isCharacteristicVector_canonical_add_two_mul (l : V → ℤ) :
    P.IsCharacteristicVector fun v => P.canonicalCharacteristic v + 2 * l v :=
  P.isCharacteristicVector_canonicalCharacteristic.add_two_mul

/-- A characteristic covector differs from the canonical characteristic covector by an
even-valued covector. -/
theorem IsCharacteristicVector.even_sub_canonical {k : V → ℤ}
    (hk : P.IsCharacteristicVector k) (v : V) :
    Even (k v - P.canonicalCharacteristic v) :=
  PlumbingGraph.IsCharacteristicVector.even_sub (P := P) hk
    P.isCharacteristicVector_canonicalCharacteristic v

end PlumbingGraph

end TauCeti
