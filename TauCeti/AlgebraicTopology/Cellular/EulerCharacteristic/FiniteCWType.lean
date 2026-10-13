/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ULift
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# The Euler characteristic of a space of finite CW type

The Euler characteristic of a finite CW complex is the alternating count of its cells
(`TauCeti.cwEulerChar`).  By singular Euler--Poincaré it is the alternating sum of the dimensions
of the singular homology over any division ring, and singular homology is a homotopy invariant, so
it depends only on the homotopy type of the complex.  This file transports it to spaces of finite
CW type.

* `TauCeti.finite_singularHomology_of_finiteCWType` and
  `TauCeti.eventually_isZero_singularHomology_of_finiteCWType`: the singular homology of a space of
  finite CW type is finitely generated in every degree over a noetherian ring, and vanishes in all
  large degrees.
* `TauCeti.eulerChar X`: the Euler characteristic of a space `X` of finite CW type, the
  alternating cell count of a finite CW complex homotopy equivalent to `X`.
* `TauCeti.eulerChar_eq_cwEulerChar`: **independence of the model**; every finite CW complex
  homotopy equivalent to `X` has alternating cell count `eulerChar X`.
* `TauCeti.eulerChar_eq_finsum_finrank_singularHomology`: `eulerChar X` is the alternating sum of
  the dimensions of the singular homology of `X` over any division ring.
* `ContinuousMap.HomotopyEquiv.eulerChar_eq`: **homotopy invariance** of the Euler characteristic.
* `TauCeti.eulerChar_of_discreteTopology` and `TauCeti.eulerChar_of_contractibleSpace`: a finite
  discrete space has Euler characteristic its cardinality, and a contractible space has Euler
  characteristic one.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Module Topology Topology.RelCWComplex Set AlgebraicTopology

universe w

namespace TauCeti

section CWComplex

variable {Y : Type w} [TopologicalSpace Y] [T2Space Y] (C : Set Y) [CWComplex C]
  [RelCWComplex.Finite C]

/-- The alternating cell count of a finite CW complex is the alternating sum of the dimensions of
the singular homology, over any division ring, of any space homotopy equivalent to the complex. -/
theorem cwEulerChar_eq_finsum_finrank_singularHomology {X : Type w} [TopologicalSpace X]
    (e : ContinuousMap.HomotopyEquiv X C) (k : Type w) [DivisionRing k] :
    cwEulerChar C = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
      (((singularHomologyFunctor (ModuleCat.{w} k) i).obj (ModuleCat.of k k)).obj (TopCat.of X)) :=
  calc
    _ = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
        (((singularHomologyFunctor (ModuleCat.{w} k) i).obj (ModuleCat.of k k)).obj
          (TopCat.of C)) := by
      simp [finsum_finrank_singularHomology_of_finite_cwComplex C (ModuleCat.of k k)]
    _ = _ := finsum_congr fun i ↦ by
      rw [(e.singularHomologyIso (ModuleCat.of k k) i).toLinearEquiv.finrank_eq]

/-- The discrete CW structure on a finite discrete space has Euler characteristic the number of
points. -/
@[simp]
theorem cwEulerChar_univ_of_discreteTopology {X : Type w} [TopologicalSpace X]
    [DiscreteTopology X] : cwEulerChar (univ : Set X) = Nat.card X := by
  rw [cwEulerChar_def, finsum_eq_single _ 0 fun n hn ↦ by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [Nat.card_of_isEmpty]]
  simp [nat_card_cell_univ_zero]

end CWComplex

section Finiteness

variable (X : Type w) [TopologicalSpace X] [h : FiniteCWType X] {k : Type w} [Ring k]
  (M : ModuleCat.{w} k)

/-- Over a noetherian ring, the singular homology of a space of finite CW type with finitely
generated coefficients is finitely generated in every degree. -/
theorem finite_singularHomology_of_finiteCWType [IsNoetherianRing k] [Module.Finite k M]
    (n : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj M).obj (TopCat.of X)) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := finite_singularHomology_of_cwComplex C M n
  exact Module.Finite.equiv (e.singularHomologyIso M n).symm.toLinearEquiv

/-- The singular homology of a space of finite CW type vanishes in all sufficiently large
degrees. -/
theorem eventually_isZero_singularHomology_of_finiteCWType :
    ∀ᶠ n in Filter.atTop,
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{w} k) n).obj M).obj (TopCat.of X)) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  exact (eventually_isZero_singularHomology_complexBasePair C M).mono fun n hn ↦
    (hn.of_iso (asIso ((complexBasePair C).singularHomologyπ M n))).of_iso
      (e.singularHomologyIso M n)

end Finiteness

/-- Some finite CW complex homotopy equivalent to `X` has alternating cell count equal to a given
integer. -/
private theorem exists_cwEulerChar_eq (X : Type w) [TopologicalSpace X] [h : FiniteCWType X] :
    ∃ n : ℤ, ∃ (Y : Type w) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y)
      (_ : CWComplex C) (_ : RelCWComplex.Finite C),
      Nonempty (ContinuousMap.HomotopyEquiv X C) ∧ cwEulerChar C = n := by
  obtain ⟨Y, _, _, C, _, _, he⟩ := h.exists_homotopyEquiv
  exact ⟨_, Y, _, ‹_›, C, ‹_›, ‹_›, he, rfl⟩

/-- The **Euler characteristic** of a space of finite CW type: the alternating count of the cells
of a finite CW complex homotopy equivalent to it.  It does not depend on the chosen complex
(`TauCeti.eulerChar_eq_cwEulerChar`). -/
def eulerChar (X : Type w) [TopologicalSpace X] [FiniteCWType X] : ℤ :=
  (exists_cwEulerChar_eq X).choose

section

variable {X : Type w} [TopologicalSpace X] [FiniteCWType X]

variable (X) in
/-- **Euler--Poincaré** for a space of finite CW type: its Euler characteristic is the alternating
sum of the dimensions of its singular homology over any division ring. -/
theorem eulerChar_eq_finsum_finrank_singularHomology (k : Type w) [DivisionRing k] :
    eulerChar X = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
      (((singularHomologyFunctor (ModuleCat.{w} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of X)) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩, h⟩ := (exists_cwEulerChar_eq X).choose_spec
  rw [eulerChar, ← h]
  exact cwEulerChar_eq_finsum_finrank_singularHomology C e k

/-- **Independence of the model.**  Every finite CW complex homotopy equivalent to a space has
alternating cell count equal to the Euler characteristic of the space. -/
theorem eulerChar_eq_cwEulerChar {Y : Type w} [TopologicalSpace Y] [T2Space Y] {C : Set Y}
    [CWComplex C] [RelCWComplex.Finite C] (e : ContinuousMap.HomotopyEquiv X C) :
    eulerChar X = cwEulerChar C := by
  rw [eulerChar_eq_finsum_finrank_singularHomology X (ULift.{w} ℚ),
    cwEulerChar_eq_finsum_finrank_singularHomology C e (ULift.{w} ℚ)]

/-- The Euler characteristic of a finite CW complex is its alternating cell count. -/
@[simp]
theorem eulerChar_cwComplex {Y : Type w} [TopologicalSpace Y] [T2Space Y] (C : Set Y)
    [CWComplex C] [RelCWComplex.Finite C] : eulerChar C = cwEulerChar C :=
  eulerChar_eq_cwEulerChar (.refl C)

/-- **Homotopy invariance** of the Euler characteristic: homotopy equivalent spaces of finite CW
type have the same Euler characteristic. -/
theorem _root_.ContinuousMap.HomotopyEquiv.eulerChar_eq {Y : Type w} [TopologicalSpace Y]
    [h : FiniteCWType Y] (e : ContinuousMap.HomotopyEquiv X Y) : eulerChar X = eulerChar Y := by
  obtain ⟨Z, _, _, C, _, _, ⟨e'⟩⟩ := h.exists_homotopyEquiv
  rw [eulerChar_eq_cwEulerChar (e.trans e'), eulerChar_eq_cwEulerChar e']

/-- Homeomorphic spaces of finite CW type have the same Euler characteristic. -/
theorem _root_.Homeomorph.eulerChar_eq {Y : Type w} [TopologicalSpace Y] [FiniteCWType Y]
    (e : X ≃ₜ Y) : eulerChar X = eulerChar Y :=
  e.toHomotopyEquiv.eulerChar_eq

end

section Examples

variable {X : Type w} [TopologicalSpace X]

/-- A finite discrete space has Euler characteristic its number of points. -/
theorem eulerChar_of_discreteTopology [DiscreteTopology X] [_root_.Finite X] :
    eulerChar X = Nat.card X := by
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ X).symm.toHomotopyEquiv,
    cwEulerChar_univ_of_discreteTopology]

/-- A contractible space has Euler characteristic one. -/
theorem eulerChar_of_contractibleSpace [ContractibleSpace X] : eulerChar X = 1 := by
  rw [eulerChar_eq_cwEulerChar (ContractibleSpace.hequiv X (univ : Set PUnit.{w + 1})).some,
    cwEulerChar_univ_of_discreteTopology, Nat.card_unique, Nat.cast_one]

end Examples

end TauCeti
