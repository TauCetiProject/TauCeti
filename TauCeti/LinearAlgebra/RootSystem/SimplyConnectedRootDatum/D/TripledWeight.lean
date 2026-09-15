/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic

/-!
# The tripled minuscule weight table of type D4

The three eight-dimensional representations of type `D₄`, the natural representation `V(ϖ₁)` and
the two half-spin representations `V(ϖ₃)` and `V(ϖ₄)`, are minuscule: every pairing of one of
their weights with a simple coroot is `-1`, `0` or `1`. This file enumerates their twenty-four
weights in the fundamental-weight basis `Fin 4 → ℤ`, eight per summand, beginning each block at
its fundamental weight, and records the structure a Chevalley carrier built on this weight family
needs.

The table is closed under the four Bourbaki-numbered simple reflections through explicit
permutations of `Fin 24`, with the reflection equation `s_i μ = μ - ⟨μ, αᵢ∨⟩ αᵢ`. Its weights
generate the full character lattice of `D₄`: the three blocks represent the three nonzero cosets
of the root lattice in the weight lattice, and their weights together generate the whole of it.
What makes all three blocks necessary is not that generation but stability under triality, which
cycles the blocks, so that no one block and no pair of blocks is stable.

Triality, the order-three symmetry `TauCeti.trialityPermD4` of the `D₄` diagram, fixes the central
node and cycles the three outer nodes, so it cycles the three fundamental weights `ϖ₁`, `ϖ₃`, `ϖ₄`
and with them the three summands. The table is stable under it: `d4TripledTrialityPerm` is the
permutation of `Fin 24` carrying each weight `μ` to `μ ∘ σ⁻¹`, which is the equivariance
`wt (π a) (σ k) = wt a k` under which a numbered permutation of the coordinates of a Kostant
toral-closure carrier extends to an automorphism of the carrier. It has order three.

No representation or group scheme is constructed here. This is the weight-diagram input for the
tripled type-`D₄` Chevalley carrier, the carrier on which triality acts.

## Main declarations

* `TauCeti.DynkinType.d4TripledWeight`: the twenty-four weights in fundamental coordinates.
* `TauCeti.DynkinType.d4TripledReflection`: the permutation induced by a simple reflection, with
  `TauCeti.DynkinType.d4TripledWeight_reflection` the simple-reflection equation.
* `TauCeti.DynkinType.span_range_d4TripledWeight_eq_top`: the weights span the character lattice.
* `TauCeti.DynkinType.d4TripledTrialityPerm`: the permutation of the table realizing triality,
  with `TauCeti.DynkinType.d4TripledWeight_d4TripledTrialityPerm` its equivariance and
  `TauCeti.DynkinType.d4TripledTrialityPerm_pow_three` its order relation, whose pointwise forms
  for the permutation and its inverse are
  `TauCeti.DynkinType.d4TripledTrialityPerm_apply_apply_apply` and
  `TauCeti.DynkinType.d4TripledTrialityPerm_symm_apply_symm_apply_symm_apply`.

## References

The node numbering and the identification of the three minuscule weights follow Bourbaki, *Lie
Groups and Lie Algebras, Chapters 4--6*, Plate IV. The minuscule-orbit description of the
representations follows J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
§13.4. That triality permutes the three eight-dimensional representations, and the conventions
for `³D₄(q)` that make this relevant, are R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti.DynkinType

open Set

/-! ## The weight table -/

/-- **The twenty-four weights of the type-`D₄` representation `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)`.**

Coordinates are pairings with the four Bourbaki-numbered simple coroots. Indices `0` to `7` carry
the weights of the natural representation, beginning at `ϖ₁ = (1, 0, 0, 0)`; indices `8` to `15`
those of the half-spin representation `V(ϖ₃)`, beginning at `ϖ₃`; and indices `16` to `23` those
of `V(ϖ₄)`, beginning at `ϖ₄`. Within each block every weight after the first is a simple
reflection of an earlier weight of the block; no mathematical structure depends on the ordering. -/
def d4TripledWeight : Fin 24 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![-1, 1, 0, 0], ![0, -1, 1, 1], ![0, 0, -1, 1],
  ![0, 0, 1, -1], ![0, 1, -1, -1], ![1, -1, 0, 0], ![-1, 0, 0, 0],
  ![0, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 0, 1], ![-1, 0, 0, 1],
  ![1, 0, 0, -1], ![-1, 1, 0, -1], ![0, -1, 1, 0], ![0, 0, -1, 0],
  ![0, 0, 0, 1], ![0, 1, 0, -1], ![1, -1, 1, 0], ![-1, 0, 1, 0],
  ![1, 0, -1, 0], ![-1, 1, -1, 0], ![0, -1, 0, 1], ![0, 0, 0, -1]]

/-- The twenty-four tripled weights are pairwise distinct. -/
theorem d4TripledWeight_injective : Function.Injective d4TripledWeight := by
  decide +kernel +revert

/-- The first weight of the natural block is the first fundamental weight `ϖ₁`. -/
@[simp]
theorem d4TripledWeight_zero : d4TripledWeight 0 = Pi.single 0 1 := by
  decide

/-- The first weight of the second block is the fundamental weight `ϖ₃`. -/
@[simp]
theorem d4TripledWeight_eight : d4TripledWeight 8 = Pi.single 2 1 := by
  decide

/-- The first weight of the third block is the fundamental weight `ϖ₄`. -/
@[simp]
theorem d4TripledWeight_sixteen : d4TripledWeight 16 = Pi.single 3 1 := by
  decide

/-- Every pairing of a tripled weight with a simple coroot is `-1`, `0`, or `1`: the three
summands are minuscule. -/
theorem d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (a : Fin 24) (i : Fin 4) :
    d4TripledWeight a i = -1 ∨ d4TripledWeight a i = 0 ∨ d4TripledWeight a i = 1 := by
  fin_cases a <;> fin_cases i <;> decide

/-- Every simple-coroot coordinate takes the value `-1` on some tripled weight. Equivalently,
every positive simple-root operator has a nonzero step on the tripled weight graph. -/
theorem exists_d4TripledWeight_apply_eq_neg_one (i : Fin 4) :
    ∃ a : Fin 24, d4TripledWeight a i = -1 := by
  fin_cases i <;> decide +kernel

/-! ## Simple reflections -/

private def d4TripledReflectionIndex : Fin 4 → Fin 24 → Fin 24 := ![
  ![1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 16, 17, 19, 18, 21, 20, 22, 23],
  ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15, 16, 18, 17, 19, 20, 22, 21, 23],
  ![0, 1, 3, 2, 5, 4, 6, 7, 9, 8, 10, 11, 12, 13, 15, 14, 16, 17, 20, 21, 18, 19, 22, 23],
  ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 17, 16, 18, 19, 20, 21, 23, 22]]

private theorem d4TripledReflectionIndex_involutive (i : Fin 4) :
    Function.Involutive (d4TripledReflectionIndex i) := by
  fin_cases i <;> intro a <;> fin_cases a <;> decide

/-- **The permutation of the twenty-four tripled weights induced by the `i`-th simple
reflection.** It preserves each of the three blocks. -/
def d4TripledReflection (i : Fin 4) : Equiv.Perm (Fin 24) :=
  (d4TripledReflectionIndex_involutive i).toPerm

/-- Applying the same simple reflection twice fixes every index in the weight table. -/
@[simp]
theorem d4TripledReflection_apply_apply (i : Fin 4) (a : Fin 24) :
    d4TripledReflection i (d4TripledReflection i a) = a :=
  d4TripledReflectionIndex_involutive i a

/-- **The coordinate equation for a simple reflection on the tripled weights.** Reflection in the
`i`-th simple root subtracts the pairing with the `i`-th simple coroot times that root, the root
being the `i`-th row of the type-`D₄` Cartan matrix. -/
theorem d4TripledWeight_reflection (i : Fin 4) (a : Fin 24) :
    d4TripledWeight (d4TripledReflection i a) =
      d4TripledWeight a - d4TripledWeight a i • CartanMatrix.D 4 i := by
  rw [CartanMatrix.D_four]
  decide +kernel +revert

/-- The simple-reflection equation, with the root read in the pinned simply connected type-`D₄`
root datum. -/
theorem d4TripledWeight_reflection_typeDSimpleIndex (i : Fin 4) (a : Fin 24) :
    d4TripledWeight (d4TripledReflection i a) =
      d4TripledWeight a -
        d4TripledWeight a i •
          (typeDSimplyConnectedRootDatum 4 le_rfl).root (typeDSimpleIndex 4 le_rfl i) := by
  rw [root_typeDSimpleIndex]
  exact d4TripledWeight_reflection i a

/-- A simple reflection negates the corresponding simple-coroot coordinate of every tripled
weight. -/
@[simp]
theorem d4TripledWeight_reflection_apply_self (i : Fin 4) (a : Fin 24) :
    d4TripledWeight (d4TripledReflection i a) i = -d4TripledWeight a i := by
  rw [d4TripledWeight_reflection]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CartanMatrix.D_diag]
  omega

/-- The coordinate change under a simple reflection, entry by entry. -/
theorem d4TripledWeight_reflection_apply (i : Fin 4) (a : Fin 24) (j : Fin 4) :
    d4TripledWeight (d4TripledReflection i a) j =
      d4TripledWeight a j - d4TripledWeight a i * CartanMatrix.D 4 i j := by
  rw [d4TripledWeight_reflection]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- A simple reflection fixes a tripled weight exactly when its simple-coroot coordinate is
zero. -/
@[simp]
theorem d4TripledReflection_eq_self_iff (i : Fin 4) (a : Fin 24) :
    d4TripledReflection i a = a ↔ d4TripledWeight a i = 0 := by
  constructor
  · intro h
    have hi := d4TripledWeight_reflection_apply_self i a
    rw [h] at hi
    omega
  · intro h
    apply d4TripledWeight_injective
    rw [d4TripledWeight_reflection, h, zero_smul, sub_zero]

/-- Simple reflections at two orthogonal nodes commute on the tripled weight table. -/
theorem d4TripledReflection_comm_of_cartan_eq_zero (i j : Fin 4) (a : Fin 24)
    (hij : CartanMatrix.D 4 i j = 0) :
    d4TripledReflection i (d4TripledReflection j a) =
      d4TripledReflection j (d4TripledReflection i a) := by
  rw [CartanMatrix.D_four] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> fin_cases a <;> decide

/-! ## Generation of the character lattice -/

/-- **The tripled weights span the full type-`D₄` character lattice.** Each fundamental weight is
a weight of the table or a sum of two of them: `ϖ₁`, `ϖ₃` and `ϖ₄` head their blocks, and
`ϖ₂ = ϖ₁ + (ϖ₂ - ϖ₁)` is the sum of the first two weights of the natural block. -/
theorem span_range_d4TripledWeight_eq_top :
    Submodule.span ℤ (Set.range d4TripledWeight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range d4TripledWeight)
  have h (a : Fin 24) : d4TripledWeight a ∈ S :=
    Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  -- In each branch `Pi.basisFun` is definitionally the corresponding `Pi.single`, while `S`
  -- unfolds to the span in the goal. The displayed equalities are explicit identities from the
  -- weight table, after which submodule closure proves membership.
  · change Pi.single (0 : Fin 4) 1 ∈ S
    rw [show Pi.single (0 : Fin 4) 1 = d4TripledWeight 0 by decide +kernel]
    exact h 0
  · change Pi.single (1 : Fin 4) 1 ∈ S
    rw [show Pi.single (1 : Fin 4) 1 = d4TripledWeight 0 + d4TripledWeight 1 by decide +kernel]
    exact S.add_mem (h 0) (h 1)
  · change Pi.single (2 : Fin 4) 1 ∈ S
    rw [show Pi.single (2 : Fin 4) 1 = d4TripledWeight 8 by decide +kernel]
    exact h 8
  · change Pi.single (3 : Fin 4) 1 ∈ S
    rw [show Pi.single (3 : Fin 4) 1 = d4TripledWeight 16 by decide +kernel]
    exact h 16

/-! ## Triality on the weight table -/

/-- The node table of `TauCeti.trialityPermD4`. The permutation itself lives in another module,
so the kernel cannot evaluate it while checking the weight table below; this table can be
evaluated and is identified with it by `trialityPermD4_apply_eq_d4TrialityNode`. -/
private def d4TrialityNode : Fin 4 → Fin 4 := ![2, 1, 3, 0]

private theorem trialityPermD4_apply_eq_d4TrialityNode (i : Fin 4) :
    trialityPermD4 i = d4TrialityNode i := by
  fin_cases i <;> simp [d4TrialityNode]

/-- The index table of `d4TripledTrialityPerm`. It carries the natural block onto the `V(ϖ₃)`
block, that block onto the `V(ϖ₄)` block, and the `V(ϖ₄)` block back onto the natural block. -/
private def d4TripledTrialityIndex : Fin 24 → Fin 24 :=
  ![8, 9, 10, 12, 11, 13, 14, 15, 16, 17, 18, 20, 19, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7]

private theorem d4TripledTrialityIndex_apply_apply_apply (a : Fin 24) :
    d4TripledTrialityIndex (d4TripledTrialityIndex (d4TripledTrialityIndex a)) = a := by
  fin_cases a <;> decide

/-- **The permutation of the twenty-four tripled weights realizing triality.** It carries the
weight `μ` to `μ ∘ σ⁻¹`, where `σ = TauCeti.trialityPermD4`, so it cycles the three blocks
`V(ϖ₁) → V(ϖ₃) → V(ϖ₄) → V(ϖ₁)`. Its inverse is its own square. -/
def d4TripledTrialityPerm : Equiv.Perm (Fin 24) where
  toFun := d4TripledTrialityIndex
  invFun a := d4TripledTrialityIndex (d4TripledTrialityIndex a)
  left_inv := d4TripledTrialityIndex_apply_apply_apply
  right_inv := d4TripledTrialityIndex_apply_apply_apply

private theorem d4TripledTrialityPerm_apply (a : Fin 24) :
    d4TripledTrialityPerm a = d4TripledTrialityIndex a :=
  (rfl)

/-- Triality carries the highest weight `ϖ₁` of the natural block to the highest weight `ϖ₃` of
the second block. -/
@[simp]
theorem d4TripledTrialityPerm_zero : d4TripledTrialityPerm 0 = 8 := by
  decide +kernel

/-- Triality carries the highest weight `ϖ₃` of the second block to the highest weight `ϖ₄` of
the third block. -/
@[simp]
theorem d4TripledTrialityPerm_eight : d4TripledTrialityPerm 8 = 16 := by
  decide +kernel

/-- Triality carries the highest weight `ϖ₄` of the third block back to `ϖ₁`. -/
@[simp]
theorem d4TripledTrialityPerm_sixteen : d4TripledTrialityPerm 16 = 0 := by
  decide +kernel

/-- **The triality permutation of the weight table has order dividing three.** -/
@[simp]
theorem d4TripledTrialityPerm_pow_three : d4TripledTrialityPerm ^ 3 = 1 := by
  ext a
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    d4TripledTrialityPerm_apply]
  revert a
  decide +kernel

/-- Applying the triality permutation of the weight table three times is the identity. -/
@[simp]
theorem d4TripledTrialityPerm_apply_apply_apply (a : Fin 24) :
    d4TripledTrialityPerm (d4TripledTrialityPerm (d4TripledTrialityPerm a)) = a := by
  have h := congrArg (fun π : Equiv.Perm (Fin 24) => π a) d4TripledTrialityPerm_pow_three
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h

/-- Applying the inverse of the triality permutation of the weight table three times is the
identity, the inverse having order three with the permutation itself. -/
@[simp]
theorem d4TripledTrialityPerm_symm_apply_symm_apply_symm_apply (a : Fin 24) :
    d4TripledTrialityPerm.symm (d4TripledTrialityPerm.symm (d4TripledTrialityPerm.symm a)) =
      a := by
  have h := d4TripledTrialityPerm_apply_apply_apply
    (d4TripledTrialityPerm.symm (d4TripledTrialityPerm.symm (d4TripledTrialityPerm.symm a)))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

private theorem d4TripledWeight_d4TripledTrialityIndex_apply (a : Fin 24) (i : Fin 4) :
    d4TripledWeight (d4TripledTrialityIndex a) (d4TrialityNode i) = d4TripledWeight a i := by
  decide +kernel +revert

/-- **The tripled weight family is equivariant for triality**: the weight at the image index,
read at the image node, is the weight at the original index read at the original node. This is
the hypothesis `wt (π a) (σ k) = wt a k` under which a numbered permutation of the coordinates of a
Kostant toral-closure carrier extends to an automorphism of the carrier. -/
@[simp]
theorem d4TripledWeight_d4TripledTrialityPerm (a : Fin 24) (i : Fin 4) :
    d4TripledWeight (d4TripledTrialityPerm a) (trialityPermD4 i) = d4TripledWeight a i := by
  rw [trialityPermD4_apply_eq_d4TrialityNode, d4TripledTrialityPerm_apply]
  exact d4TripledWeight_d4TripledTrialityIndex_apply a i

/-- The functional form of `d4TripledWeight_d4TripledTrialityPerm`: triality carries the weight
`μ` to `μ ∘ σ⁻¹`. -/
theorem d4TripledWeight_d4TripledTrialityPerm_eq (a : Fin 24) :
    d4TripledWeight (d4TripledTrialityPerm a) = d4TripledWeight a ∘ trialityPermD4.symm := by
  funext j
  rw [Function.comp_apply, ← d4TripledWeight_d4TripledTrialityPerm a (trialityPermD4.symm j),
    Equiv.apply_symm_apply]

/-- **Triality intertwines the simple reflections of the weight table with the diagram
permutation**: `π ∘ s_i = s_{σ i} ∘ π`. -/
@[simp]
theorem d4TripledTrialityPerm_d4TripledReflection (i : Fin 4) (a : Fin 24) :
    d4TripledTrialityPerm (d4TripledReflection i a) =
      d4TripledReflection (trialityPermD4 i) (d4TripledTrialityPerm a) := by
  rw [trialityPermD4_apply_eq_d4TrialityNode, d4TripledTrialityPerm_apply,
    d4TripledTrialityPerm_apply]
  fin_cases i <;> fin_cases a <;> decide +kernel

end TauCeti.DynkinType
