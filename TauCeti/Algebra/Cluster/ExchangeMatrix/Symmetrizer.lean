/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Rat.Cast.Order

import Mathlib.Tactic.LinearCombination

/-!
# Symmetrizers on connected components

The support graph of an exchange matrix is Mathlib's `SimpleGraph.fromRel` applied to
its nonzero entries. A chosen positive skew-symmetrizer makes this relation symmetric and
irreflexive. Every other skew-symmetrizing family is proportional to it on each connected
component. For integral positive families the factors are positive rationals, independently
on different components.

If `d` satisfies the opposite weighted skew equations `B i j * d j = -B j i * d i`,
then `s i * d i` is constant on connected components. This is the weight constraint used
to compare lattice and Fomin–Zelevinsky seed presentations.

## References

* M. Gross, P. Hacking and S. Keel, *Birational geometry of cluster algebras*, §2.
-/

public section

namespace Matrix.IsSkewSymmetrizer

variable {I : Type*} {B : Matrix I I ℤ} {s t : I → ℤ}

/-- On a skew-symmetrizable matrix the usual symmetrized support graph has exactly the
nonzero entries as its adjacency relation. -/
theorem fromRel_adj_iff (hs : B.IsSkewSymmetrizer s) (i j : I) :
    (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).Adj i j ↔ B i j ≠ 0 := by
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact hs.apply_eq_zero_iff.not.mpr h
  · intro h
    exact ⟨fun hij ↦ h (hij ▸ hs.apply_self i), Or.inl h⟩

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Comparing two skew-symmetrizing equations along a nonzero entry gives cross-proportional
weights. Only this edge equation is required; the scalars need not be positive or integral. -/
theorem mul_eq_mul_of_ne_zero (hs : B.IsSkewSymmetrizer s) {i j : I} {a b : R}
    (hab : a * (B i j : R) = -(b * (B j i : R)))
    (hij : B i j ≠ 0) : a * (s j : R) = b * (s i : R) := by
  have hji : (B j i : R) ≠ 0 :=
    Int.cast_ne_zero.mpr (hs.apply_eq_zero_iff.not.mp hij)
  have hd : (s i : R) * (B i j : R) = -((s j : R) * (B j i : R)) := by
    exact_mod_cast hs.mul_apply i j
  apply mul_right_cancel₀ hji
  linear_combination a * hd - (s i : R) * hab

/-- Skew-symmetrizing families are proportional on every connected component of the
nonzero-entry graph. This needs no finiteness or connectedness assumption on the whole matrix. -/
theorem mul_eq_mul_of_reachable (hs : B.IsSkewSymmetrizer s) {x : I → R}
    (hx : ∀ i j, x i * (B i j : R) = -(x j * (B j i : R))) {i j : I}
    (hij : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).Reachable i j) :
    x i * (s j : R) = x j * (s i : R) := by
  let r (i j : I) := x i * (s j : R) = x j * (s i : R)
  have hr : Equivalence r := by
    refine ⟨fun _ ↦ rfl, fun h ↦ h.symm, ?_⟩
    intro i j k hij hjk
    apply mul_left_cancel₀ (Int.cast_ne_zero.mpr (hs.pos j).ne' : (s j : R) ≠ 0)
    linear_combination (s k : R) * hij + (s i : R) * hjk
  have edge : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).Adj ≤ r := fun i j h ↦
    hs.mul_eq_mul_of_ne_zero (hx i j) ((hs.fromRel_adj_iff i j).mp h)
  exact Relation.reflTransGen_le_of_equivalence_of_le hr edge i j
    ((SimpleGraph.reachable_iff_reflTransGen i j).mp hij)

/-- The products of a row symmetrizer and opposite column weights agree on each connected
component. In lattice-seed notation these are the products `s i * d i`. -/
theorem intCast_mul_eq_intCast_mul_of_reachable (hs : B.IsSkewSymmetrizer s) {d : I → R}
    (hd : ∀ i j, (B i j : R) * d j = -((B j i : R) * d i)) {i j : I}
    (hij : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).Reachable i j) :
    (s i : R) * d i = (s j : R) * d j := by
  have edge {i j : I} (h : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).Adj i j) :
      (s i : R) * d i = (s j : R) * d j := by
    have hab : d j * (B i j : R) = -(d i * (B j i : R)) := by
      simpa only [mul_comm] using hd i j
    simpa only [mul_comm] using
      (hs.mul_eq_mul_of_ne_zero hab ((hs.fromRel_adj_iff i j).mp h)).symm
  have h := Relation.ReflTransGen.lift (p := Eq) (fun i ↦ (s i : R) * d i)
    (fun _ _ h ↦ edge h) i j ((SimpleGraph.reachable_iff_reflTransGen i j).mp hij)
  simpa only [Relation.reflTransGen_eq_self] using h

/-- The weight products descend to a function on the actual connected-component quotient. -/
theorem exists_forall_connectedComponentMk_eq_intCast_mul (hs : B.IsSkewSymmetrizer s) {d : I → R}
    (hd : ∀ i j, (B i j : R) * d j = -((B j i : R) * d i)) :
    ∃ c : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).ConnectedComponent → R,
      ∀ i, c ((SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).connectedComponentMk i) =
        (s i : R) * d i := by
  exact ⟨SimpleGraph.ConnectedComponent.lift (fun i ↦ (s i : R) * d i)
    (fun _ _ p _ ↦ hs.intCast_mul_eq_intCast_mul_of_reachable hd p.reachable), fun _ ↦ by simp⟩

end Domain

/-- Two positive integral skew-symmetrizers differ by independent positive rational factors
on the connected components, including isolated vertices and disconnected matrices. -/
theorem exists_pos_and_intCast_eq_connectedComponentMk_mul (hs : B.IsSkewSymmetrizer s)
    (ht : B.IsSkewSymmetrizer t) :
    ∃ c : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).ConnectedComponent → ℚ,
      (∀ C, 0 < c C) ∧ ∀ i, (t i : ℚ) =
        c ((SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).connectedComponentMk i) * (s i : ℚ) := by
  have hq (i j : I) : (t i : ℚ) * (B i j : ℚ) = -((t j : ℚ) * (B j i : ℚ)) := by
    exact_mod_cast ht.mul_apply i j
  let c := SimpleGraph.ConnectedComponent.lift (fun i ↦ (t i : ℚ) / (s i : ℚ))
    (fun i j p _ ↦ (div_eq_div_iff
      (Int.cast_ne_zero.mpr (hs.pos i).ne') (Int.cast_ne_zero.mpr (hs.pos j).ne')).mpr
        (hs.mul_eq_mul_of_reachable hq p.reachable))
  refine ⟨c, ?_, ?_⟩
  · exact SimpleGraph.ConnectedComponent.forall.mpr fun i ↦ by
      simpa [c] using div_pos (Int.cast_pos.mpr (ht.pos i) : (0 : ℚ) < t i)
        (Int.cast_pos.mpr (hs.pos i))
  · intro i
    simp only [c, SimpleGraph.ConnectedComponent.lift_mk]
    exact (div_mul_cancel₀ _ (Int.cast_ne_zero.mpr (hs.pos i).ne')).symm

/-- Positive rational scaling independently on the support components characterizes all
integral skew-symmetrizers of a fixed skew-symmetrizable matrix. -/
theorem isSkewSymmetrizer_iff_exists_pos_and_intCast_eq_connectedComponentMk_mul
    (hs : B.IsSkewSymmetrizer s) :
    B.IsSkewSymmetrizer t ↔
      ∃ c : (SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).ConnectedComponent → ℚ,
        (∀ C, 0 < c C) ∧ ∀ i, (t i : ℚ) =
          c ((SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).connectedComponentMk i) * (s i : ℚ) := by
  refine ⟨hs.exists_pos_and_intCast_eq_connectedComponentMk_mul, ?_⟩
  rintro ⟨c, hc, ht⟩
  refine ⟨fun i ↦ ?_, fun i j ↦ ?_⟩
  · have h : (0 : ℚ) < t i := by
      rw [ht i]
      exact mul_pos (hc _) (Int.cast_pos.mpr (hs.pos i))
    exact_mod_cast h
  · by_cases hij : B i j = 0
    · simp [hij, hs.apply_eq_zero_iff.mp hij]
    · have hadj := (hs.fromRel_adj_iff i j).mpr hij
      have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hsym : (s i : ℚ) * (B i j : ℚ) = -((s j : ℚ) * (B j i : ℚ)) := by
        exact_mod_cast hs.mul_apply i j
      have h : (t i : ℚ) * (B i j : ℚ) = -((t j : ℚ) * (B j i : ℚ)) := by
        rw [ht i, ht j, ← heq]
        linear_combination
          c ((SimpleGraph.fromRel (fun i j ↦ B i j ≠ 0)).connectedComponentMk i) * hsym
      exact_mod_cast h

end Matrix.IsSkewSymmetrizer
