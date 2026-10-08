/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Relations associated to a side pairing

A side pairing of a hyperbolic polygon determines a homomorphism from the free group on its
sides to `PSL(2, ℝ)`. Two families of words are intrinsic to the pairing. The side word at
`i` says that the maps attached to `i` and its paired side are inverse. The cycle word at a
vertex is the ordered product of side generators encountered while following the vertex cycle.

This file defines those words and proves their exact evaluations. Thus every side word is a
relation, while the `t`-th power of a cycle word is a relation exactly when the corresponding
cycle transformation has order dividing `t`. These are the algebraic relators used in the
presentation part of the Poincaré polygon theorem.

## Main definitions

* `SidePairing.pairingHom`: evaluation of free side words by the side-pairing maps.
* `SidePairing.sideRelator`: the inverse-pair relation for a side.
* `SidePairing.partialCycleWord` and `SidePairing.cycleWord`: the words read along a vertex cycle.
* `SidePairing.cycleRelator`: a prescribed power of a cycle word.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (sigma : P.SidePairing)

/-- Evaluate a word in the free group on the sides by the corresponding side-pairing maps. -/
def pairingHom : FreeGroup (Fin n) →* PSL(2, ℝ) :=
  FreeGroup.lift sigma.map

/-- A free side generator evaluates to its side-pairing map. -/
@[simp]
theorem pairingHom_of (i : Fin n) : sigma.pairingHom (FreeGroup.of i) = sigma.map i :=
  FreeGroup.lift_apply_of

/-- The side relation says that the generator of the paired side followed by the original
generator is trivial. -/
def sideRelator (i : Fin n) : FreeGroup (Fin n) :=
  FreeGroup.of (sigma.pair i) * FreeGroup.of i

/-- Every side relator evaluates to the identity. -/
@[simp]
theorem pairingHom_sideRelator (i : Fin n) : sigma.pairingHom (sigma.sideRelator i) = 1 := by
  simp [sideRelator]

/-- Every side relator belongs to the kernel of the side-pairing evaluation. -/
theorem sideRelator_mem_ker (i : Fin n) : sigma.sideRelator i ∈ sigma.pairingHom.ker := by
  rw [MonoidHom.mem_ker, pairingHom_sideRelator]

/-- The word in side generators encountered during the first `m` steps of the vertex cycle
starting at `j`. Its multiplication order matches `partialCycleMap`. -/
def partialCycleWord (sigma : P.SidePairing) (j : Fin n) : ℕ → FreeGroup (Fin n)
  | 0 => 1
  | m + 1 => FreeGroup.of (sigma.next^[m] j) * partialCycleWord sigma j m

/-- The empty partial cycle word is the identity. -/
@[simp]
theorem partialCycleWord_zero (j : Fin n) : sigma.partialCycleWord j 0 = 1 :=
  (rfl)

/-- A partial cycle word grows by adjoining the next side generator on the left. -/
theorem partialCycleWord_succ (j : Fin n) (m : ℕ) :
    sigma.partialCycleWord j (m + 1) =
      FreeGroup.of (sigma.next^[m] j) * sigma.partialCycleWord j m :=
  (rfl)

/-- A partial cycle word can instead be read after removing its first side generator. -/
theorem partialCycleWord_succ' (j : Fin n) (m : ℕ) :
    sigma.partialCycleWord j (m + 1) =
      sigma.partialCycleWord (sigma.next j) m * FreeGroup.of j := by
  induction m with
  | zero => simp [partialCycleWord_succ]
  | succ m ih =>
    rw [partialCycleWord_succ, ih, partialCycleWord_succ, Function.iterate_succ_apply, mul_assoc]

/-- Evaluating a partial cycle word gives the corresponding partial cycle transformation. -/
@[simp]
theorem pairingHom_partialCycleWord (j : Fin n) (m : ℕ) :
    sigma.pairingHom (sigma.partialCycleWord j m) = sigma.partialCycleMap j m := by
  induction m with
  | zero => simp
  | succ m ih => simp only [partialCycleWord_succ, map_mul, pairingHom_of, ih,
      partialCycleMap_succ]

/-- The cycle word at `j`, obtained by reading the side generators through one minimal vertex
cycle. -/
def cycleWord (j : Fin n) : FreeGroup (Fin n) :=
  sigma.partialCycleWord j (sigma.cycleLength j)

/-- Evaluating the cycle word gives the cycle transformation. -/
@[simp]
theorem pairingHom_cycleWord (j : Fin n) :
    sigma.pairingHom (sigma.cycleWord j) = sigma.cycleMap j := by
  rw [cycleWord, pairingHom_partialCycleWord, cycleMap_def]

/-- The cycle relator with exponent `t` is the `t`-th power of the cycle word. For a finite
vertex cycle, `t` is the prescribed order of its elliptic cycle transformation. -/
def cycleRelator (j : Fin n) (t : ℕ) : FreeGroup (Fin n) :=
  sigma.cycleWord j ^ t

/-- A cycle relator evaluates to the corresponding power of the cycle transformation. -/
@[simp]
theorem pairingHom_cycleRelator (j : Fin n) (t : ℕ) :
    sigma.pairingHom (sigma.cycleRelator j t) = sigma.cycleMap j ^ t := by
  simp [cycleRelator]

/-- A cycle relator belongs to the evaluation kernel exactly when the corresponding cycle
transformation has order dividing its exponent. -/
theorem cycleRelator_mem_ker_iff (j : Fin n) (t : ℕ) :
    sigma.cycleRelator j t ∈ sigma.pairingHom.ker ↔ sigma.cycleMap j ^ t = 1 := by
  rw [MonoidHom.mem_ker, pairingHom_cycleRelator]

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
