/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Coefficient reflections and stuck vectors

A coefficient reflection at a vertex replaces its coefficient by the sum of the neighbouring
coefficients minus itself. The operation is defined on signed vectors: even a nonnegative input
can acquire a negative coefficient. A vector is stuck when no reflection increases the reflected
coordinate; a vertex is precarious when its reflection strictly decreases that coordinate.

These conditions are expressed by the nonnegativity and positivity of coordinates of the graph
Cartan matrix `2I - A`. In particular, stuck vectors without precarious vertices are precisely
null vectors. The companion module `TauCeti.Combinatorics.SimpleGraph.AdditiveFunction` proves
zero propagation and positivity for nonzero nonnegative vectors with nonnegative Cartan image
on a preconnected graph; see `SimpleGraph.Preconnected.pos_of_graphCartanMatrix_mulVec_nonneg`.
In particular, nonzero nonnegative null vectors are strictly positive, allowing the
positive-additive-function theory to be applied.

All constructions commute with actual graph isomorphisms. Integer vectors give the coefficient
game. The Cartan criteria require only a partial order compatible with addition; the
no-precarious-vertices criterion additionally requires a linear order.
-/

public section

namespace SimpleGraph

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

section Reflection

variable {R : Type*} [AddCommGroup R]

/-- Reflect the coefficient at `i`, leaving all other coefficients unchanged. This uses signed
subtraction, not truncated subtraction on natural numbers. -/
def coefficientReflection (i : V) (a : V → R) : V → R :=
  Function.update a i ((∑ j ∈ G.neighborFinset i, a j) - a i)

/-- The reflected coordinate is the neighbour sum minus the original coefficient. -/
@[simp]
theorem coefficientReflection_apply_same (i : V) (a : V → R) :
    G.coefficientReflection i a i = (∑ j ∈ G.neighborFinset i, a j) - a i := by
  simp [coefficientReflection]

/-- Reflection fixes every coordinate other than the chosen vertex. -/
@[simp]
theorem coefficientReflection_apply_of_ne {i j : V} (h : j ≠ i) (a : V → R) :
    G.coefficientReflection i a j = a j := by
  simp [coefficientReflection, h]

/-- Coefficient reflection is involutive, since a vertex is not its own neighbour. -/
@[simp]
theorem coefficientReflection_coefficientReflection (i : V) (a : V → R) :
    G.coefficientReflection i (G.coefficientReflection i a) = a := by
  ext j
  by_cases h : j = i
  · subst j
    rw [coefficientReflection_apply_same, coefficientReflection_apply_same]
    have hs : ∑ j ∈ G.neighborFinset i, G.coefficientReflection i a j =
        ∑ j ∈ G.neighborFinset i, a j := by
      simpa only [coefficientReflection] using
        Finset.sum_update_of_notMem (G.notMem_neighborFinset_self i) a
          ((∑ j ∈ G.neighborFinset i, a j) - a i)
    rw [hs]
    abel
  · simp [h]

variable [Preorder R]

/-- A vector is stuck if reflecting any vertex does not increase its coefficient. Nonnegativity
and nonzeroness, when required of a game position, are separate hypotheses. -/
def IsStuck (a : V → R) : Prop :=
  ∀ i, G.coefficientReflection i a i ≤ a i

/-- A vertex is precarious for a vector if reflecting it strictly decreases its coefficient. -/
def IsPrecarious (a : V → R) (i : V) : Prop :=
  G.coefficientReflection i a i < a i

/-- The neighbour-sum criterion for being stuck. -/
theorem isStuck_iff_sum_sub_le (a : V → R) :
    G.IsStuck a ↔ ∀ i, (∑ j ∈ G.neighborFinset i, a j) - a i ≤ a i := by
  simp [IsStuck]

/-- The neighbour-sum criterion for a precarious vertex. -/
theorem isPrecarious_iff_sum_sub_lt (a : V → R) (i : V) :
    G.IsPrecarious a i ↔ (∑ j ∈ G.neighborFinset i, a j) - a i < a i := by
  simp [IsPrecarious]

end Reflection

section Cartan

variable {R : Type*} [Ring R]

/-- Reflection subtracts the corresponding Cartan coordinate. -/
theorem coefficientReflection_apply_same_eq_sub_mulVec (i : V) (a : V → R) :
    G.coefficientReflection i a i = a i - (G.graphCartanMatrix R *ᵥ a) i := by
  rw [coefficientReflection_apply_same, graphCartanMatrix_mulVec_apply, two_mul]
  abel

section PartialOrder

variable [PartialOrder R] [IsOrderedAddMonoid R]

/-- A vector is stuck exactly when its Cartan image is coordinatewise nonnegative. -/
theorem isStuck_iff_graphCartanMatrix_mulVec_nonneg (a : V → R) :
    G.IsStuck a ↔ 0 ≤ G.graphCartanMatrix R *ᵥ a := by
  simp only [IsStuck, coefficientReflection_apply_same_eq_sub_mulVec, sub_le_self_iff,
    Pi.le_def, Pi.zero_apply]

/-- A precarious vertex has a strictly positive Cartan coordinate. This equivalence does not
require the vector to be stuck. -/
theorem isPrecarious_iff_graphCartanMatrix_mulVec_pos (a : V → R) (i : V) :
    G.IsPrecarious a i ↔ 0 < (G.graphCartanMatrix R *ᵥ a) i := by
  simp only [IsPrecarious, coefficientReflection_apply_same_eq_sub_mulVec, sub_lt_self_iff]

end PartialOrder

variable [LinearOrder R] [IsOrderedAddMonoid R]

/-- Stuck vectors without precarious vertices are exactly the null vectors of `2I - A`. -/
theorem isStuck_and_forall_not_isPrecarious_iff_graphCartanMatrix_mulVec_eq_zero (a : V → R) :
    (G.IsStuck a ∧ ∀ i, ¬ G.IsPrecarious a i) ↔ G.graphCartanMatrix R *ᵥ a = 0 := by
  rw [isStuck_iff_graphCartanMatrix_mulVec_nonneg]
  simp only [isPrecarious_iff_graphCartanMatrix_mulVec_pos, not_lt]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ le_antisymm (Pi.le_def.mpr h₂) h₁,
    fun h ↦ ⟨h.ge, Pi.le_def.mp h.le⟩⟩

end Cartan

section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj] {R : Type*} [AddCommGroup R]

/-- Pulling a coefficient vector back along a graph isomorphism commutes with reflection. -/
theorem Iso.coefficientReflection_comp (e : G ≃g H) (i : V) (a : W → R) :
    G.coefficientReflection i (a ∘ e) = H.coefficientReflection (e i) a ∘ e := by
  ext j
  by_cases h : j = i
  · subst j
    simp [e.sum_neighborFinset_comp]
  · simp [coefficientReflection_apply_of_ne, h, e.injective.ne h]

variable [Preorder R]

/-- Stuckness is invariant under graph relabelling. -/
@[simp]
theorem Iso.isStuck_comp_iff (e : G ≃g H) (a : W → R) :
    G.IsStuck (a ∘ e) ↔ H.IsStuck a := by
  simp only [IsStuck, e.coefficientReflection_comp, Function.comp_apply]
  exact (e.surjective.forall (p := fun i ↦ H.coefficientReflection i a i ≤ a i)).symm

/-- Precarious vertices are carried to the corresponding vertices by a graph isomorphism. -/
@[simp]
theorem Iso.isPrecarious_comp_iff (e : G ≃g H) (a : W → R) (i : V) :
    G.IsPrecarious (a ∘ e) i ↔ H.IsPrecarious a (e i) := by
  simp only [IsPrecarious, e.coefficientReflection_comp, Function.comp_apply]

end Relabel

end SimpleGraph
