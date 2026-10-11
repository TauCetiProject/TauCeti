/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic
public import TauCeti.RepresentationTheory.Spin.Weight
import TauCeti.Data.Finset.Basic
import TauCeti.Data.List.Involutive

/-!
# Type `D` spin weights in the simply connected character lattice

The spinor module has weights `1 / 2 * (±e₀ ± ⋯ ± e_{n-1})` in the usual orthonormal
coordinates. The simply connected type `Dₙ` datum instead writes its character lattice in the
fundamental-weight basis, so a weight is recorded by its pairings with the simple coroots

```text
eᵢ - eᵢ₊₁  (i + 1 < n),       e_{n-2} + e_{n-1}  (i + 1 = n).
```

In those coordinates all spin weights are integral. This file defines the resulting sign-vector
family `TauCeti.DynkinType.typeDSpinWeight`, compares it coordinate by coordinate with
`TauCeti.spinWeight`, and proves that the family spans the full character lattice `Fin n → ℤ`.
Using all spinor weights is essential in even rank: either half-spin family alone reaches only
one of the two nonzero spinor cosets of the root lattice.

The type-`D` graph automorphism changes the sign of the final orthonormal coordinate. On the
sign-set indexing the spin basis, this toggles membership of the final index. The resulting
permutation exchanges the even and odd half-spin bases and carries each spin weight through the
fork-node permutation `TauCeti.graphPermD`. Thus the full spin module, rather than either
half-spin summand by itself, is the weight-stable input for the graph-twisted carrier.

The spanning result is the full-weight input needed to construct the simply connected type `D`
Chevalley carrier from the spin representation. The adjoint representation supplies only the
index-four root lattice.

The second half of the file describes how the Weyl group moves the spin basis around, uniformly
in the rank. Reflection in a chain simple root `eᵢ - eᵢ₊₁` exchanges two adjacent signs;
reflection in the fork simple root `e_{n-2} + e_{n-1}` exchanges the last two signs and reverses
both. Both act on the indexing sign sets, giving `TauCeti.DynkinType.typeDSpinReflection`, and
both change the number of positive signs by an even amount. Every pairing of a spin weight with
a simple coroot is `-1`, `0`, or `1`, and the spin weights are pairwise distinct, so the spin
module is multiplicity free, and the orbits of the simple reflections on its basis are exactly
the two half-spin parity classes. So the weight basis of the full spin module splits into two
Weyl orbits, and its weights alone do not exhibit it as irreducible.

## Main declarations

* `TauCeti.DynkinType.typeDSpinWeight`: a spin weight in fundamental-weight coordinates.
* `TauCeti.DynkinType.algebraMap_typeDSpinWeight_apply`: comparison with the half-integer
  orthonormal coordinates of `TauCeti.spinWeight`.
* `TauCeti.DynkinType.typeDSpinWeight_univ_apply`,
  `TauCeti.DynkinType.typeDSpinWeight_univ_eq_single`, and
  `TauCeti.DynkinType.typeDSpinWeight_univ_erase_last_eq_single`: the terminal and penultimate fork
  fundamental weights.
* `TauCeti.DynkinType.span_range_typeDSpinWeight_eq_top`: the spin weights generate the full
  simply connected character lattice.
* `TauCeti.DynkinType.typeDSpinGraphPerm`: the graph symmetry on the spin basis, with
  `TauCeti.DynkinType.typeDSpinWeight_typeDSpinGraphPerm_apply` recording its action on weights,
  and `TauCeti.DynkinType.typeDSpinGraphPerm_of_mem` and
  `TauCeti.DynkinType.typeDSpinGraphPerm_of_notMem` reading the toggle as an erasure or an
  insertion.
* `TauCeti.DynkinType.typeDSpinReflection`: the `i`-th simple reflection on the sign sets, with
  `TauCeti.DynkinType.mem_typeDSpinReflection_of_add_one_lt` and
  `TauCeti.DynkinType.mem_typeDSpinReflection_of_not_add_one_lt` for membership and
  `TauCeti.DynkinType.typeDSpinReflection_apply_apply` for involutivity.
* `TauCeti.DynkinType.typeDSpinWeight_typeDSpinReflection_apply` and
  `TauCeti.DynkinType.typeDSimplyConnectedRootDatum_reflection_typeDSpinWeight`: the reflection
  formula against the `i`-th row of `CartanMatrix.D n`, and its identification with reflection in
  the pinned datum.
* `TauCeti.DynkinType.typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one` and
  `TauCeti.DynkinType.typeDSpinWeight_injective`: every pairing of a spin weight with a simple
  coroot is `-1`, `0`, or `1`, and the spin weights are pairwise distinct.
* `TauCeti.DynkinType.typeDSpinReflection_eq_self_iff`: a simple reflection fixes a sign set
  exactly where the corresponding weight coordinate vanishes.
* `TauCeti.DynkinType.typeDSpinReflection_typeDSpinReflection_fork`: the two fork reflections
  compose to the toggle of the last two signs.
* `TauCeti.DynkinType.even_card_typeDSpinReflection_iff` and
  `TauCeti.DynkinType.exists_typeDSpinReflections_eq_iff`: the simple reflections preserve the
  parity of a sign set, and two sign sets lie in one reflection orbit exactly when their parities
  agree.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 13.2.

The integral-coordinate and spanning API follows the parallel type `B` construction in Tau Ceti
PR #4847. The fork coordinate and the use of both half-spin parities are the type `D` changes.
The shape of the reflection interface, from the involution on basis indices through the
coordinate equation to the orbit statement, follows the fixed-rank type-`E₆` one in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight`.
-/

public section

namespace TauCeti.DynkinType

open Set Submodule
open scoped symmDiff

/-! ## Integral spin weights -/

/-- The weight of a type `Dₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`. At the terminal fork node it is
the half-sum of the last two signs. -/
def typeDSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if h : (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if (⟨(i : ℕ) + 1, h⟩ : Fin n) ∈ s then 1 else 0
  else
    (if (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∈ s then 1 else 0) +
      (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `D` spin weight. -/
@[simp]
theorem typeDSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinWeight s i =
      if h : (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if (⟨(i : ℕ) + 1, h⟩ : Fin n) ∈ s then 1 else 0
      else
        (if (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∈ s then 1 else 0) +
          (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

private theorem algebraMap_signIndicator {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (if i ∈ s then 1 else 0) = spinWeight K s i + ⅟(2 : K) := by
  classical
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, map_one, spinWeight_of_mem hi]
    rw [← two_mul, mul_invOf_self]
  · rw [ite_eq_right hi, map_zero, spinWeight_of_notMem hi]
    simp

/-- After mapping to any coefficient ring in which `2` is invertible, `typeDSpinWeight` is obtained
from the orthonormal sign weight by pairing with the simple coroot: take an adjacent difference
away from the terminal node and the sum of the last two coordinates at the terminal fork node. -/
theorem algebraMap_typeDSpinWeight_apply {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeDSpinWeight s i) =
      if h : (i : ℕ) + 1 < n then
        spinWeight K s i - spinWeight K s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight K s (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) +
        spinWeight K s i := by
  classical
  rw [typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · simp only [dite_eq_left hnext]
    rw [map_sub, algebraMap_signIndicator, algebraMap_signIndicator]
    ring
  · simp only [dite_eq_right hnext]
    rw [map_sub, map_add, map_one, algebraMap_signIndicator, algebraMap_signIndicator]
    ring_nf
    rw [invOf_mul_self]
    ring

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeDSpinWeight {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ K (typeDSpinWeight s i)) =
      fun i : Fin n => if h : (i : ℕ) + 1 < n then
        spinWeight K s i - spinWeight K s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight K s (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) +
        spinWeight K s i := by
  funext i
  exact algebraMap_typeDSpinWeight_apply s i

/-- For a valid type `Dₙ`, the integral coordinate of a spin weight is its pairing with the
corresponding Bourbaki simple coroot in orthonormal coordinates. Type `D` is simply laced, so the
simple coroot is `typeDSimpleRoot n hn i`. -/
theorem algebraMap_typeDSpinWeight_eq_dotProduct {K : Type*} [CommRing K]
    [Invertible (2 : K)] {n : ℕ} (hn : 4 ≤ n) (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeDSpinWeight s i) =
      spinWeight K s ⬝ᵥ
        fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j) := by
  rw [algebraMap_typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [dite_eq_left hnext]
    have hmap :
        (fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j)) =
          (Pi.single i 1 - Pi.single (⟨(i : ℕ) + 1, hnext⟩ : Fin n) 1 :
            Fin n → K) := by
      rw [typeDSimpleRoot_of_add_one_lt hn hnext]
      funext j
      simp [Pi.sub_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hprev : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) =
        (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    rw [dite_eq_right hnext]
    have hmap :
        (fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j)) =
          (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 +
            Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 : Fin n → K) := by
      rw [typeDSimpleRoot_of_not_add_one_lt hn hnext]
      funext j
      simp [Pi.add_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
    exact congrArg₂ (· + ·) (congrArg (spinWeight K s) hprev)
      (congrArg (spinWeight K s) hi)

/-! ## The graph automorphism on spin weights -/

/-- The permutation of the type-`D` spin basis induced by the graph automorphism: toggle the sign
of the final orthonormal coordinate. A sign is encoded by membership in the indexing finset, so
this takes the symmetric difference with the singleton containing the final index. -/
def typeDSpinGraphPerm (n : ℕ) (hn : 1 ≤ n) : Equiv.Perm (Finset (Fin n)) :=
  let last : Fin n := ⟨n - 1, by omega⟩
  (symmDiff_left_involutive {last}).toPerm (· ∆ {last})

/-- The type-`D` spin graph permutation acts by symmetric difference with the final index. -/
theorem typeDSpinGraphPerm_apply (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) :
    typeDSpinGraphPerm n hn s = s ∆ {(⟨n - 1, by omega⟩ : Fin n)} :=
  by simp [typeDSpinGraphPerm]

private theorem symmDiff_singleton_eq_erase_or_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) :
    s ∆ {a} = if a ∈ s then s.erase a else insert a s := by
  ext x
  by_cases ha : a ∈ s <;> simp [Finset.mem_symmDiff, ha] <;> aesop

/-- **Toggling the final sign of a sign set that carries the final index erases it.** -/
@[simp]
theorem typeDSpinGraphPerm_of_mem (n : ℕ) (hn : 1 ≤ n) {s : Finset (Fin n)}
    (hs : (⟨n - 1, by omega⟩ : Fin n) ∈ s) :
    typeDSpinGraphPerm n hn s = s.erase (⟨n - 1, by omega⟩ : Fin n) := by
  rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_left hs]

/-- **Toggling the final sign of a sign set that lacks the final index inserts it.** -/
@[simp]
theorem typeDSpinGraphPerm_of_notMem (n : ℕ) (hn : 1 ≤ n) {s : Finset (Fin n)}
    (hs : (⟨n - 1, by omega⟩ : Fin n) ∉ s) :
    typeDSpinGraphPerm n hn s = insert (⟨n - 1, by omega⟩ : Fin n) s := by
  rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_right hs]

/-- An index belongs to the graph-transformed sign set precisely when its old membership agrees
with not being the final index. Thus membership is unchanged away from the final coordinate and
reversed there. -/
@[simp]
theorem mem_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) (i : Fin n) :
    i ∈ typeDSpinGraphPerm n hn s ↔ (i ∈ s ↔ (i : ℕ) + 1 ≠ n) := by
  rw [typeDSpinGraphPerm_apply]
  by_cases hi : i = (⟨n - 1, by omega⟩ : Fin n)
  · subst i
    have hval : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp [Finset.mem_symmDiff, hval]
  · have hilast : (i : ℕ) + 1 ≠ n := by
      intro h
      apply hi
      apply Fin.ext
      dsimp only
      omega
    simp [Finset.mem_symmDiff, hi, hilast]

/-- Toggling the final sign twice is the identity. -/
@[simp]
theorem typeDSpinGraphPerm_apply_apply (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) :
    typeDSpinGraphPerm n hn (typeDSpinGraphPerm n hn s) = s :=
  (typeDSpinGraphPerm n hn).left_inv s

/-- The permutation which toggles the final sign is an involution. -/
@[simp]
theorem typeDSpinGraphPerm_symm (n : ℕ) (hn : 1 ≤ n) :
    (typeDSpinGraphPerm n hn).symm = typeDSpinGraphPerm n hn :=
  by
    apply Equiv.ext
    intro s
    apply (typeDSpinGraphPerm n hn).injective
    rw [Equiv.apply_symm_apply, typeDSpinGraphPerm_apply_apply]

/-- The graph permutation exchanges the two half-spin parities: an even sign set is sent to an
odd one and conversely. -/
@[simp]
theorem even_card_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n)
    (s : Finset (Fin n)) :
    Even (typeDSpinGraphPerm n hn s).card ↔ Odd s.card := by
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hlast : last ∈ s
  · have hcard : (typeDSpinGraphPerm n hn s).card + 1 = s.card := by
      rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_left hlast]
      simpa only [last]
        using Finset.card_erase_add_one hlast
    rw [← hcard, Nat.odd_add_one, Nat.not_odd_iff_even]
  · have hcard : (typeDSpinGraphPerm n hn s).card = s.card + 1 := by
      rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_right hlast]
      simpa only [last]
        using Finset.card_insert_of_notMem hlast
    rw [hcard, Nat.even_add_one, Nat.not_even_iff_odd]

/-- Equivalently, the graph permutation sends odd sign sets to even ones. -/
@[simp]
theorem odd_card_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n)
    (s : Finset (Fin n)) :
    Odd (typeDSpinGraphPerm n hn s).card ↔ Even s.card := by
  rw [← Nat.not_even_iff_odd, even_card_typeDSpinGraphPerm_iff,
    Nat.not_odd_iff_even]

/-- Toggling the final sign exchanges the two fork coordinates of a type-`D` spin weight. -/
private theorem typeDSpinWeight_typeDSpinGraphPerm_fork {n : ℕ} (hn : 2 ≤ n)
    (s : Finset (Fin n)) :
    typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) ⟨n - 2, by omega⟩ =
        typeDSpinWeight s ⟨n - 1, by omega⟩ ∧
      typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) ⟨n - 1, by omega⟩ =
        typeDSpinWeight s ⟨n - 2, by omega⟩ := by
  have hpen_lt : n - 2 + 1 < n := by omega
  have hlast_not_lt : ¬n - 1 + 1 < n := by omega
  have hnext :
      (⟨n - 2 + 1, hpen_lt⟩ : Fin n) = (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.ext
    dsimp only
    omega
  have hprev :
      (⟨n - 1 - 1, by omega⟩ : Fin n) = (⟨n - 2, by omega⟩ : Fin n) := by
    apply Fin.ext
    dsimp only
    omega
  have hpen_ne_last : n - 2 ≠ n - 1 := by omega
  constructor
  · rw [typeDSpinWeight_apply, dite_eq_left hpen_lt, hnext,
      typeDSpinWeight_apply, dite_eq_right hlast_not_lt, hprev]
    by_cases hp : (⟨n - 2, by omega⟩ : Fin n) ∈ s <;>
      by_cases hl : (⟨n - 1, by omega⟩ : Fin n) ∈ s <;>
      simp [hpen_ne_last, hp, hl]
  · rw [typeDSpinWeight_apply, dite_eq_right hlast_not_lt, hprev,
      typeDSpinWeight_apply, dite_eq_left hpen_lt, hnext]
    by_cases hp : (⟨n - 2, by omega⟩ : Fin n) ∈ s <;>
      by_cases hl : (⟨n - 1, by omega⟩ : Fin n) ∈ s <;>
      simp [hpen_ne_last, hp, hl]

/-- **The final-sign toggle realizes the type-`D` graph automorphism on spin weights.** Applying
the fork-node permutation to the fundamental-weight coordinates of a spin weight gives the weight
indexed by the sign set with its final membership toggled. -/
theorem typeDSpinWeight_typeDSpinGraphPerm_apply {n : ℕ} (hn : 2 ≤ n)
    (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) i =
      typeDSpinWeight s (graphPermD n hn i) := by
  by_cases hbefore : (i : ℕ) + 2 < n
  · have hnext : (i : ℕ) + 1 < n := by omega
    have hilast : (i : ℕ) ≠ n - 1 := by omega
    have hipenultimate : (i : ℕ) ≠ n - 2 := by omega
    rw [graphPermD_apply_of_ne_of_ne n hn i hipenultimate hilast,
      typeDSpinWeight_apply, typeDSpinWeight_apply, dite_eq_left hnext,
      dite_eq_left hnext]
    have hi_not_last : (i : ℕ) + 1 ≠ n := by omega
    have hnext_not_last :
        ((⟨(i : ℕ) + 1, hnext⟩ : Fin n) : ℕ) + 1 ≠ n := by
      dsimp only
      omega
    simp [mem_typeDSpinGraphPerm_iff, hi_not_last, hnext_not_last]
  · by_cases hpenultimate : (i : ℕ) + 2 = n
    · have hi : i = (⟨n - 2, by omega⟩ : Fin n) := by
        apply Fin.ext
        dsimp only
        omega
      rw [hi, graphPermD_apply_left]
      exact (typeDSpinWeight_typeDSpinGraphPerm_fork hn s).1
    · have hlast : (i : ℕ) + 1 = n := by omega
      have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        dsimp only
        omega
      rw [hi, graphPermD_apply_right]
      exact (typeDSpinWeight_typeDSpinGraphPerm_fork hn s).2

/-- The type-`D` graph permutation preserves the full family of spin weights as a set. -/
theorem image_comp_graphPermD_range_typeDSpinWeight {n : ℕ} (hn : 2 ≤ n) :
    (fun wt : Fin n → ℤ => wt ∘ graphPermD n hn) ''
        Set.range (typeDSpinWeight (n := n)) =
      Set.range (typeDSpinWeight (n := n)) := by
  rw [← Set.range_comp]
  have hcomp :
      (fun wt : Fin n → ℤ => wt ∘ graphPermD n hn) ∘ typeDSpinWeight =
        typeDSpinWeight ∘ typeDSpinGraphPerm n (by omega) := by
    funext s i
    exact (typeDSpinWeight_typeDSpinGraphPerm_apply hn s i).symm
  rw [hcomp, Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]

/-! ## A spanning family -/

/-- The sign set which is positive through `i` and negative after `i`. -/
private def typeDSpinCut {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ≤ i

private theorem mem_typeDSpinCut_iff {n : ℕ} (i j : Fin n) :
    j ∈ typeDSpinCut i ↔ j ≤ i := by
  simp [typeDSpinCut]

/-- The all-positive type-`D` spin weight, evaluated at an arbitrary fundamental-weight
coordinate. -/
@[simp 1100] theorem typeDSpinWeight_univ_apply {n : ℕ} (i : Fin n) :
    typeDSpinWeight (Finset.univ : Finset (Fin n)) i =
      if (i : ℕ) + 1 = n then 1 else 0 := by
  rw [typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · have hne : ¬(i : ℕ) + 1 = n := by omega
    rw [dite_eq_left hnext, ite_eq_right hne]
    simp
  · have heq : (i : ℕ) + 1 = n := by omega
    rw [dite_eq_right hnext, ite_eq_left heq]
    simp

/-- **The all-positive type-`D` spin weight is the terminal fundamental weight.** In fundamental-
weight coordinates it has value one at the final fork node and zero at every other node. -/
theorem typeDSpinWeight_univ_eq_single {n : ℕ} (hn : 1 ≤ n) :
    typeDSpinWeight (Finset.univ : Finset (Fin n)) =
      Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
  classical
  funext i
  rw [typeDSpinWeight_univ_apply, Pi.single_apply]
  by_cases hlast : (i : ℕ) + 1 = n
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    rw [ite_eq_left hlast, ite_eq_left hi]
  · have hi : i ≠ (⟨n - 1, by omega⟩ : Fin n) := by
      intro hi
      apply hlast
      have := congrArg Fin.val hi
      dsimp only at this ⊢
      omega
    rw [ite_eq_right hlast, ite_eq_right hi]

/-- **Erasing the final sign from the all-positive type-`D` spin weight gives the penultimate
fundamental weight.** This pins the order of the two fork weights under the diagram symmetry. -/
theorem typeDSpinWeight_univ_erase_last_eq_single {n : ℕ} (hn : 2 ≤ n) :
    typeDSpinWeight
        ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n)) =
      Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 := by
  classical
  rw [← typeDSpinGraphPerm_of_mem n (by omega) (Finset.mem_univ _)]
  funext i
  rw [typeDSpinWeight_typeDSpinGraphPerm_apply hn, typeDSpinWeight_univ_eq_single (by omega),
    Pi.single_apply, Pi.single_apply]
  by_cases hpen : (i : ℕ) = n - 2
  · have hi : i = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hpen
    rw [hi]
    simp
  · by_cases hlast : (i : ℕ) = n - 1
    · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hlast
      rw [hi]
      simp [Fin.ext_iff]
      omega
    · rw [TauCeti.graphPermD_apply_of_ne_of_ne n hn i hpen hlast]
      simp only [Fin.ext_iff]
      simp [hpen, hlast]

private theorem typeDSpinWeight_cut_apply {n : ℕ} (i j : Fin n) :
    typeDSpinWeight (typeDSpinCut i) j =
      if j = i then 1
      else if (j : ℕ) + 1 = n ∧ (i : ℕ) + 2 < n then -1 else 0 := by
  rw [typeDSpinWeight_apply]
  simp only [mem_typeDSpinCut_iff]
  by_cases hjnext : (j : ℕ) + 1 < n
  · rw [dite_eq_left hjnext]
    simp only [Fin.le_def]
    split_ifs <;> omega
  · rw [dite_eq_right hjnext]
    simp only [Fin.le_def]
    split_ifs <;> omega

/-- Before the two fork nodes, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeDSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 2 < n) :
    typeDSpinWeight (typeDSpinCut i) +
        typeDSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  rw [Pi.add_apply, typeDSpinWeight_cut_apply, typeDSpinWeight_univ_apply, Pi.single_apply]
  split_ifs <;> omega

/-- **The type `Dₙ` spin weights generate the full simply connected character lattice.**

The all-positive sign sequence has weight `ω_{n-1}`. A sign sequence positive through a node
strictly before the fork has weight `ωᵢ - ω_{n-1}`; at the penultimate node it has weight
`ω_{n-2}`. Thus the weights from both half-spin parities contain enough differences to generate
every fundamental-weight basis vector. -/
theorem span_range_typeDSpinWeight_eq_top (n : ℕ) :
    Submodule.span ℤ (Set.range (typeDSpinWeight (n := n))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  by_cases hlast : (i : ℕ) + 1 = n
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    rw [hi, ← typeDSpinWeight_univ_eq_single (n := n) (by omega)]
    exact Submodule.subset_span ⟨Finset.univ, rfl⟩
  · by_cases hpenultimate : (i : ℕ) + 2 = n
    · have hi : i = (⟨n - 2, by omega⟩ : Fin n) := by
        apply Fin.ext
        dsimp only
        omega
      rw [hi, ← typeDSpinWeight_univ_erase_last_eq_single (n := n) (by omega)]
      exact Submodule.subset_span ⟨
        (Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n), rfl⟩
    · have hi : (i : ℕ) + 2 < n := by omega
      rw [← typeDSpinWeight_cut_add_univ_eq_single i hi]
      exact Submodule.add_mem _
        (Submodule.subset_span ⟨typeDSpinCut i, rfl⟩)
        (Submodule.subset_span ⟨Finset.univ, rfl⟩)

/-! ## Simple reflections on the spin basis -/

/-- **The `i`-th simple reflection of type `Dₙ`, acting on the sign sets that index the spin
basis.**

A sign is recorded by membership in the finset. At a chain node `i`, whose simple root is
`eᵢ - eᵢ₊₁`, the reflection exchanges the signs at `i` and `i + 1`. At the terminal fork node,
whose simple root is `e_{n-2} + e_{n-1}`, it exchanges the last two signs and reverses both. -/
def typeDSpinReflection {n : ℕ} (i : Fin n) (s : Finset (Fin n)) : Finset (Fin n) :=
  if h : (i : ℕ) + 1 < n then
    s.map (Equiv.swap i ⟨(i : ℕ) + 1, h⟩).toEmbedding
  else
    s.map (Equiv.swap (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) i).toEmbedding ∆
      {(⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n), i}

/-- At a chain node the simple reflection is the transposition of the two adjacent signs. -/
theorem typeDSpinReflection_of_add_one_lt {n : ℕ} {i : Fin n} (hi : (i : ℕ) + 1 < n)
    (s : Finset (Fin n)) :
    typeDSpinReflection i s = s.map (Equiv.swap i ⟨(i : ℕ) + 1, hi⟩).toEmbedding :=
  dite_eq_left hi

/-- At the terminal fork node the simple reflection transposes the last two signs and reverses
both. -/
theorem typeDSpinReflection_of_not_add_one_lt {n : ℕ} {i : Fin n} (hi : ¬(i : ℕ) + 1 < n)
    (s : Finset (Fin n)) :
    typeDSpinReflection i s =
      s.map (Equiv.swap (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) i).toEmbedding ∆
        {(⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n), i} :=
  dite_eq_right hi

/-- Membership in a chain-node reflection of a sign set, read through the transposition. -/
theorem mem_typeDSpinReflection_of_add_one_lt {n : ℕ} {i : Fin n} (hi : (i : ℕ) + 1 < n)
    (s : Finset (Fin n)) (x : Fin n) :
    x ∈ typeDSpinReflection i s ↔ Equiv.swap i (⟨(i : ℕ) + 1, hi⟩ : Fin n) x ∈ s := by
  rw [typeDSpinReflection_of_add_one_lt hi, Finset.mem_map_equiv, Equiv.symm_swap]

/-- Membership in the fork-node reflection of a sign set: away from the last two indices it is
unchanged, and at those two it is the transposed membership, reversed. -/
theorem mem_typeDSpinReflection_of_not_add_one_lt {n : ℕ} {i : Fin n} (hi : ¬(i : ℕ) + 1 < n)
    (s : Finset (Fin n)) (x : Fin n) :
    x ∈ typeDSpinReflection i s ↔
      (Equiv.swap (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) i x ∈ s ↔
        x ≠ (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∧ x ≠ i) := by
  rw [typeDSpinReflection_of_not_add_one_lt hi]
  exact Finset.mem_map_swap_symmDiff_pair_iff _ _ _ _

/-- Each simple reflection of the spin basis is an involution. -/
@[simp]
theorem typeDSpinReflection_apply_apply {n : ℕ} (i : Fin n) (s : Finset (Fin n)) :
    typeDSpinReflection i (typeDSpinReflection i s) = s := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSpinReflection_of_add_one_lt hi, typeDSpinReflection_of_add_one_lt hi]
    have h := (Equiv.swap i (⟨(i : ℕ) + 1, hi⟩ : Fin n)).finsetCongr.apply_symm_apply s
    rwa [Equiv.finsetCongr_apply, Equiv.finsetCongr_symm, Equiv.symm_swap,
      Equiv.finsetCongr_apply] at h
  · rw [typeDSpinReflection_of_not_add_one_lt hi, typeDSpinReflection_of_not_add_one_lt hi]
    exact Finset.involutive_map_swap_symmDiff_pair _ _ s

/-- The involution underlying each simple reflection of the spin basis. -/
theorem typeDSpinReflection_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (typeDSpinReflection i) :=
  typeDSpinReflection_apply_apply i

/-! ## The reflection formula -/

/-- The sign vector of a sign set in the orthonormal coordinates: `1` at the indices it contains
and `-1` elsewhere. It replaces the half-integer `TauCeti.spinWeight` over `ℤ`, where `2` is not
invertible, at the cost of the factor of two in
`TauCeti.DynkinType.typeDSpinSign_dotProduct_typeDSimpleRoot` below. -/
private def typeDSpinSign {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if i ∈ s then 1 else -1

private theorem typeDSpinSign_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinSign s i = if i ∈ s then 1 else -1 := (rfl)

/-- At a chain node, twice the spin weight coordinate is the difference of two adjacent signs. -/
private theorem two_mul_typeDSpinWeight_of_add_one_lt {n : ℕ} {i : Fin n} (hi : (i : ℕ) + 1 < n)
    (s : Finset (Fin n)) :
    2 * typeDSpinWeight s i = typeDSpinSign s i - typeDSpinSign s ⟨(i : ℕ) + 1, hi⟩ := by
  rw [typeDSpinWeight_apply, dite_eq_left hi, typeDSpinSign_apply, typeDSpinSign_apply]
  split_ifs <;> omega

/-- At the fork node, twice the spin weight coordinate is the sum of the last two signs. -/
private theorem two_mul_typeDSpinWeight_of_not_add_one_lt {n : ℕ} {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) (s : Finset (Fin n)) :
    2 * typeDSpinWeight s i =
      typeDSpinSign s (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) + typeDSpinSign s i := by
  rw [typeDSpinWeight_apply, dite_eq_right hi, typeDSpinSign_apply, typeDSpinSign_apply]
  split_ifs <;> omega

/-- Pairing the sign vector with a simple root recovers twice the spin weight coordinate: this is
the integral form of `TauCeti.DynkinType.algebraMap_typeDSpinWeight_eq_dotProduct`. -/
private theorem typeDSpinSign_dotProduct_typeDSimpleRoot {n : ℕ} (hn : 4 ≤ n)
    (s : Finset (Fin n)) (j : Fin n) :
    typeDSpinSign s ⬝ᵥ typeDSimpleRoot n hn j = 2 * typeDSpinWeight s j := by
  by_cases hj : (j : ℕ) + 1 < n
  · rw [typeDSimpleRoot_of_add_one_lt hn hj, two_mul_typeDSpinWeight_of_add_one_lt hj,
      dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  · have hjlast : j = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      have := j.isLt
      omega
    have hjprev : (⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin n) =
        (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      have := j.isLt
      omega
    rw [typeDSimpleRoot_of_not_add_one_lt hn hj, two_mul_typeDSpinWeight_of_not_add_one_lt hj,
      dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
    exact congrArg₂ (· + ·) (congrArg (typeDSpinSign s) hjprev.symm)
      (congrArg (typeDSpinSign s) hjlast.symm)

private theorem typeDSpinSign_typeDSpinReflection_of_add_one_lt {n : ℕ} {i : Fin n}
    (hi : (i : ℕ) + 1 < n) (s : Finset (Fin n)) (x : Fin n) :
    typeDSpinSign (typeDSpinReflection i s) x =
      typeDSpinSign s (Equiv.swap i (⟨(i : ℕ) + 1, hi⟩ : Fin n) x) := by
  simp only [typeDSpinSign_apply, mem_typeDSpinReflection_of_add_one_lt hi]

/-- Transposing two signs and reversing both subtracts, from the sign vector, the sum of the two
signs times the sum of the two coordinate basis vectors. This is the fork-node shape of the
reflection formula, stated with the two indices abstract. -/
private theorem typeDSpinSign_symmDiff_pair_map_swap {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (s : Finset (Fin n)) (x : Fin n) :
    typeDSpinSign (s.map (Equiv.swap a b).toEmbedding ∆ {a, b}) x =
      typeDSpinSign s x -
        (typeDSpinSign s a + typeDSpinSign s b) *
          ((Pi.single a 1 + Pi.single b 1 : Fin n → ℤ) x) := by
  have hmem : x ∈ s.map (Equiv.swap a b).toEmbedding ∆ {a, b} ↔
      (Equiv.swap a b x ∈ s ↔ x ≠ a ∧ x ≠ b) :=
    Finset.mem_map_swap_symmDiff_pair_iff a b s x
  by_cases hx : x = a
  · -- `subst` renames `a` to `x`, so the two signs below are those at `x` and at `b`.
    subst hx
    by_cases hbs : b ∈ s <;> by_cases has : x ∈ s <;>
      simp [typeDSpinSign_apply, hmem, Pi.single_eq_of_ne hab, hbs, has]
  · by_cases hx' : x = b
    · subst hx'
      by_cases hbs : x ∈ s <;> by_cases has : a ∈ s <;>
        simp [typeDSpinSign_apply, hmem, Pi.single_eq_of_ne (Ne.symm hab), hbs, has]
    · by_cases hxs : x ∈ s <;>
        simp [typeDSpinSign_apply, hmem, Equiv.swap_apply_of_ne_of_ne hx hx', hxs, hx, hx']

/-- **The simple reflections act on the sign vectors by the classical orthogonal formula.** The
reflection in the `i`-th simple root subtracts from the sign vector its pairing with that root,
which is twice the `i`-th spin weight coordinate, times the root. -/
private theorem typeDSpinSign_typeDSpinReflection {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (s : Finset (Fin n)) :
    typeDSpinSign (typeDSpinReflection i s) =
      typeDSpinSign s - (2 * typeDSpinWeight s i) • typeDSimpleRoot n hn i := by
  funext x
  by_cases hi : (i : ℕ) + 1 < n
  · have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [typeDSpinSign_typeDSpinReflection_of_add_one_lt hi,
      two_mul_typeDSpinWeight_of_add_one_lt hi, typeDSimpleRoot_of_add_one_lt hn hi]
    by_cases hx : x = i
    · subst hx
      simp only [Equiv.swap_apply_left, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, typeDSpinSign_apply]
      split_ifs <;> omega
    · by_cases hx' : x = (⟨(i : ℕ) + 1, hi⟩ : Fin n)
      · subst hx'
        simp only [Equiv.swap_apply_right, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_eq_same, Pi.single_eq_of_ne hne, typeDSpinSign_apply]
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hx,
          Pi.single_eq_of_ne hx', typeDSpinSign_apply]
        split_ifs <;> omega
  · have hilast : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      have := i.isLt
      omega
    have hiprev : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) =
        (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      have := i.isLt
      omega
    have hne : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ≠ i := fun h => by
      have hv := congrArg Fin.val h
      simp only at hv
      have := i.isLt
      omega
    have hroot : typeDSimpleRoot n hn i =
        Pi.single (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) 1 + Pi.single i 1 := by
      rw [typeDSimpleRoot_of_not_add_one_lt hn hi]
      exact congrArg₂ (· + ·) (congrArg (fun y : Fin n => Pi.single y (1 : ℤ)) hiprev.symm)
        (congrArg (fun y : Fin n => Pi.single y (1 : ℤ)) hilast.symm)
    rw [typeDSpinReflection_of_not_add_one_lt hi, typeDSpinSign_symmDiff_pair_map_swap hne s x,
      two_mul_typeDSpinWeight_of_not_add_one_lt hi, hroot, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]

/-- **The coordinate equation for a simple reflection on the type-`Dₙ` spin weights.** Reflection
in the `i`-th simple root subtracts the pairing with the `i`-th simple coroot, which is the `i`-th
coordinate of the weight, times that root; in the fundamental-weight basis the root is the `i`-th
row of the Bourbaki-numbered Cartan matrix. -/
theorem typeDSpinWeight_typeDSpinReflection_apply {n : ℕ} (hn : 4 ≤ n) (i j : Fin n)
    (s : Finset (Fin n)) :
    typeDSpinWeight (typeDSpinReflection i s) j =
      typeDSpinWeight s j - typeDSpinWeight s i * CartanMatrix.D n i j := by
  have h2 : (2 : ℤ) * typeDSpinWeight (typeDSpinReflection i s) j =
      2 * (typeDSpinWeight s j - typeDSpinWeight s i * CartanMatrix.D n i j) := by
    rw [← typeDSpinSign_dotProduct_typeDSimpleRoot hn, typeDSpinSign_typeDSpinReflection hn,
      sub_dotProduct, smul_dotProduct, typeDSpinSign_dotProduct_typeDSimpleRoot hn,
      typeDSimpleRoot_dotProduct_typeDSimpleRoot hn]
    ring
  exact mul_left_cancel₀ (by norm_num) h2

/-- The functional form of `TauCeti.DynkinType.typeDSpinWeight_typeDSpinReflection_apply`. -/
theorem typeDSpinWeight_typeDSpinReflection {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (s : Finset (Fin n)) :
    typeDSpinWeight (typeDSpinReflection i s) =
      typeDSpinWeight s - typeDSpinWeight s i • fun j => CartanMatrix.D n i j := by
  funext j
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact typeDSpinWeight_typeDSpinReflection_apply hn i j s

/-- **The simple reflections of the spin basis realize reflection in the pinned type-`Dₙ`
datum.** -/
@[simp]
theorem typeDSimplyConnectedRootDatum_reflection_typeDSpinWeight {n : ℕ} (hn : 4 ≤ n)
    (i : Fin n) (s : Finset (Fin n)) :
    (typeDSimplyConnectedRootDatum n hn).reflection (typeDSimpleIndex n hn i)
        (typeDSpinWeight s) = typeDSpinWeight (typeDSpinReflection i s) := by
  rw [typeDSpinWeight_typeDSpinReflection hn, ← root_typeDSimpleIndex hn]
  simp [RootPairing.reflection_apply, toLinearMap_typeDSimplyConnectedRootDatum,
    coroot_typeDSimpleIndex hn]

/-- **Every pairing of a type-`Dₙ` spin weight with a simple coroot is `-1`, `0`, or `1`**, that
is, every coordinate in the fundamental-weight basis is one of the three. The corresponding bound
over all coroots, which is what minusculeity asks for, is not proved here. -/
theorem typeDSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one {n : ℕ} (s : Finset (Fin n))
    (i : Fin n) :
    typeDSpinWeight s i = -1 ∨ typeDSpinWeight s i = 0 ∨ typeDSpinWeight s i = 1 := by
  rw [typeDSpinWeight_apply]
  split_ifs <;> omega

/-- The spin weight determines the sign vector, hence the sign set. The two fork coordinates
together recover the last two signs, and each earlier coordinate then recovers one more sign by
descending induction. -/
private theorem typeDSpinSign_eq_of_typeDSpinWeight_eq {n : ℕ} (hn : 2 ≤ n)
    {s t : Finset (Fin n)} (h : typeDSpinWeight s = typeDSpinWeight t) :
    typeDSpinSign s = typeDSpinSign t := by
  obtain ⟨p, hpval⟩ : ∃ p : Fin n, (p : ℕ) = n - 2 := ⟨⟨n - 2, by omega⟩, rfl⟩
  obtain ⟨q, hqval⟩ : ∃ q : Fin n, (q : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hq : ¬(q : ℕ) + 1 < n := by omega
  have hp : (p : ℕ) + 1 < n := by omega
  have hidprev : (⟨(q : ℕ) - 1, by omega⟩ : Fin n) = p := Fin.ext (by dsimp only; omega)
  have hidnext : (⟨(p : ℕ) + 1, hp⟩ : Fin n) = q := Fin.ext (by dsimp only; omega)
  have efork := two_mul_typeDSpinWeight_of_not_add_one_lt hq s
  have eforkt := two_mul_typeDSpinWeight_of_not_add_one_lt hq t
  have echain := two_mul_typeDSpinWeight_of_add_one_lt hp s
  have echaint := two_mul_typeDSpinWeight_of_add_one_lt hp t
  rw [hidprev] at efork eforkt
  rw [hidnext] at echain echaint
  have hwq := congrFun h q
  have hwp := congrFun h p
  have hsignq : typeDSpinSign s q = typeDSpinSign t q := by omega
  have hsignp : typeDSpinSign s p = typeDSpinSign t p := by omega
  have key : ∀ (k : ℕ) (j : Fin n), (j : ℕ) + k + 2 = n →
      typeDSpinSign s j = typeDSpinSign t j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjp : j = p := Fin.ext (by omega)
        rw [hjp]
        exact hsignp
    | succ k ih =>
        intro j hj
        have hjlt : (j : ℕ) + 1 < n := by omega
        have hstep := ih (⟨(j : ℕ) + 1, hjlt⟩ : Fin n) (by dsimp only; omega)
        have ej := two_mul_typeDSpinWeight_of_add_one_lt hjlt s
        have ejt := two_mul_typeDSpinWeight_of_add_one_lt hjlt t
        have hwj := congrFun h j
        omega
  funext j
  by_cases hj : (j : ℕ) + 2 ≤ n
  · exact key (n - (j : ℕ) - 2) j (by omega)
  · have hjq : j = q := Fin.ext (by have := j.isLt; omega)
    rw [hjq]
    exact hsignq

/-- **The type-`Dₙ` spin weights are pairwise distinct**, so the spin module is multiplicity
free. -/
theorem typeDSpinWeight_injective {n : ℕ} :
    Function.Injective (typeDSpinWeight (n := n)) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- In ranks `0` and `1` there is at most one index, and there the fork coordinate is
    -- `2 * [x ∈ s] - 1`, which already determines the single sign.
    intro s t h
    ext x
    have hlast : ¬(x : ℕ) + 1 < n := by have := x.isLt; omega
    have hprev : (⟨(x : ℕ) - 1, by have := x.isLt; omega⟩ : Fin n) = x :=
      Fin.ext (by dsimp only; have := x.isLt; omega)
    have hx := congrFun h x
    rw [typeDSpinWeight_apply, typeDSpinWeight_apply, dite_eq_right hlast, dite_eq_right hlast,
      hprev] at hx
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all
  · intro s t h
    have hsign := typeDSpinSign_eq_of_typeDSpinWeight_eq hn h
    ext x
    have hx := congrFun hsign x
    simp only [typeDSpinSign_apply] at hx
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all

/-- A simple reflection fixes a sign set exactly when the corresponding coordinate of its spin
weight vanishes. -/
@[simp]
theorem typeDSpinReflection_eq_self_iff {n : ℕ} (i : Fin n) (s : Finset (Fin n)) :
    typeDSpinReflection i s = s ↔ typeDSpinWeight s i = 0 := by
  rw [typeDSpinWeight_apply]
  by_cases hi : (i : ℕ) + 1 < n
  · -- At a chain node the reflection transposes the two adjacent signs, and the coordinate is
    -- their difference.
    rw [typeDSpinReflection_of_add_one_lt hi, Finset.map_swap_eq_self_iff, dite_eq_left hi]
    by_cases h1 : i ∈ s <;> by_cases h2 : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ∈ s <;> simp [h1, h2]
  · -- At the fork node the reflection transposes the last two signs and reverses both, and the
    -- coordinate is their sum.
    rw [typeDSpinReflection_of_not_add_one_lt hi, Finset.map_swap_symmDiff_pair_eq_self_iff,
      dite_eq_right hi]
    by_cases h1 : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∈ s <;>
      by_cases h2 : i ∈ s <;> simp [h1, h2]

/-- **The simple reflections preserve the parity of a sign set**, so each of the two half-spin
families of weights is stable under all of them. The graph automorphism behaves the other way
round and exchanges the two parities, by
`TauCeti.DynkinType.even_card_typeDSpinGraphPerm_iff`. -/
@[simp]
theorem even_card_typeDSpinReflection_iff {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    (s : Finset (Fin n)) :
    Even (typeDSpinReflection i s).card ↔ Even s.card := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSpinReflection_of_add_one_lt hi, Finset.card_map]
  · have hiv : (i : ℕ) = n - 1 := by have := i.isLt; omega
    have hne : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ≠ i := fun hh => by
      have hv := congrArg Fin.val hh
      simp only at hv
      omega
    rw [typeDSpinReflection_of_not_add_one_lt hi, Finset.even_card_symmDiff_iff,
      Finset.card_map, Finset.card_pair_eq_two_iff.2 hne]
    simp

/-! ## The two Weyl orbits -/

/-- **The two fork reflections compose to the toggle of the last two signs.** Their composite
reverses both fork signs and leaves every other sign alone, so the reflections move a sign set
inside its parity class by an arbitrary even number of sign changes. -/
theorem typeDSpinReflection_typeDSpinReflection_fork {n : ℕ} {p q : Fin n}
    (hp : (p : ℕ) + 2 = n) (hq : (q : ℕ) + 1 = n) (s : Finset (Fin n)) :
    typeDSpinReflection p (typeDSpinReflection q s) = s ∆ {p, q} := by
  have hqlt : ¬(q : ℕ) + 1 < n := by omega
  have hplt : (p : ℕ) + 1 < n := by omega
  have hprev : (⟨(q : ℕ) - 1, by omega⟩ : Fin n) = p :=
    Fin.ext (by dsimp only; omega)
  have hnext : (⟨(p : ℕ) + 1, hplt⟩ : Fin n) = q :=
    Fin.ext (by dsimp only; omega)
  have hmapp : ∀ u : Finset (Fin n),
      typeDSpinReflection p u = u.map (Equiv.swap p q).toEmbedding := fun u => by
    rw [typeDSpinReflection_of_add_one_lt hplt, hnext]
  have hreflq : typeDSpinReflection q s = typeDSpinReflection p s ∆ {p, q} := by
    rw [typeDSpinReflection_of_not_add_one_lt hqlt, hprev, hmapp s]
  rw [hreflq, hmapp]
  simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]
  rw [← hmapp, typeDSpinReflection_apply_apply, Finset.map_swap_pair]

/-- Base case of the toggle construction: the two fork indices themselves. -/
private theorem exists_toggle_last_base {n : ℕ} (p q : Fin n) (hp : (p : ℕ) + 2 = n)
    (hq : (q : ℕ) + 1 = n) :
    ∃ l : List (Fin n), ∀ s : Finset (Fin n),
      l.foldl (fun u j ↦ typeDSpinReflection j u) s = s ∆ {p, q} := by
  refine ⟨[q, p], fun s => ?_⟩
  simp only [List.foldl_cons, List.foldl_nil]
  exact typeDSpinReflection_typeDSpinReflection_fork hp hq s

/-- **Every pair consisting of an index and the last one is toggled by a word of simple
reflections.** Conjugating the fork toggle by the chain transpositions walks its first index down
the diagram. -/
private theorem exists_toggle_last {n : ℕ} (q : Fin n) (hq : (q : ℕ) + 1 = n) :
    ∀ (d : ℕ) (c : Fin n), n ≤ (c : ℕ) + 2 + d → (c : ℕ) + 2 ≤ n →
      ∃ l : List (Fin n), ∀ s : Finset (Fin n),
        l.foldl (fun u j ↦ typeDSpinReflection j u) s = s ∆ {c, q} := by
  intro d
  induction d with
  | zero =>
      intro c hd hc
      exact exists_toggle_last_base c q (by omega) hq
  | succ d ih =>
      intro c hd hc
      by_cases hc2 : (c : ℕ) + 2 = n
      · exact exists_toggle_last_base c q hc2 hq
      · have hclt : (c : ℕ) + 1 < n := by omega
        obtain ⟨l, hl⟩ := ih (⟨(c : ℕ) + 1, hclt⟩ : Fin n) (by dsimp only; omega)
          (by dsimp only; omega)
        have hqc : q ≠ c := fun h => by
          have _ := congrArg Fin.val h
          omega
        have hqc' : q ≠ (⟨(c : ℕ) + 1, hclt⟩ : Fin n) := fun h => by
          have hv := congrArg Fin.val h
          simp only at hv
          omega
        refine ⟨c :: (l ++ [c]), fun s => ?_⟩
        simp only [List.foldl_cons, List.foldl_append, List.foldl_nil]
        rw [hl (typeDSpinReflection c s), typeDSpinReflection_of_add_one_lt hclt]
        simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]
        rw [← typeDSpinReflection_of_add_one_lt hclt, typeDSpinReflection_apply_apply,
          Finset.map_swap_pair_right hqc hqc']

/-- **Every pair of distinct indices is toggled by a word of simple reflections.** -/
private theorem exists_toggle_pair {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ∃ l : List (Fin n), ∀ s : Finset (Fin n),
      l.foldl (fun u j ↦ typeDSpinReflection j u) s = s ∆ {a, b} := by
  obtain ⟨q, hq⟩ : ∃ q : Fin n, (q : ℕ) + 1 = n := by
    refine ⟨⟨n - 1, by omega⟩, ?_⟩
    dsimp only
    omega
  have hlast : ∀ c : Fin n, c ≠ q → ∃ l : List (Fin n), ∀ s : Finset (Fin n),
      l.foldl (fun u j ↦ typeDSpinReflection j u) s = s ∆ {c, q} := by
    intro c hc
    have hcq : (c : ℕ) ≠ (q : ℕ) := fun h => hc (Fin.ext h)
    have hcval : (c : ℕ) + 2 ≤ n := by
      have := c.isLt
      omega
    exact exists_toggle_last q hq n c (by omega) hcval
  by_cases hbq : b = q
  · subst hbq
    exact hlast a hab
  · by_cases haq : a = q
    · subst haq
      obtain ⟨l, hl⟩ := hlast b (Ne.symm hab)
      exact ⟨l, fun s => by rw [hl s, Finset.pair_comm]⟩
    · obtain ⟨l1, hl1⟩ := hlast a haq
      obtain ⟨l2, hl2⟩ := hlast b hbq
      have hpair : ({a, q} : Finset (Fin n)) ∆ {b, q} = {a, b} := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        grind
      refine ⟨l1 ++ l2, fun s => ?_⟩
      rw [List.foldl_append, hl1 s, hl2, symmDiff_assoc, hpair]

/-- Any two sign sets of equal parity are joined by a word of simple reflections: toggle two
indices at which they differ, which shrinks their symmetric difference by two. -/
private theorem exists_foldl_typeDSpinReflection_eq {n : ℕ} (hn : 2 ≤ n) :
    ∀ (m : ℕ) (s t : Finset (Fin n)), (s ∆ t).card ≤ m → Even (s ∆ t).card →
      ∃ l : List (Fin n), l.foldl (fun u j ↦ typeDSpinReflection j u) s = t := by
  have hempty : ∀ s t : Finset (Fin n), (s ∆ t).card = 0 →
      ∃ l : List (Fin n), l.foldl (fun u j ↦ typeDSpinReflection j u) s = t := by
    intro s t h0
    refine ⟨[], ?_⟩
    rw [List.foldl_nil]
    exact Finset.symmDiff_eq_empty.1 (Finset.card_eq_zero.1 h0)
  intro m
  induction m with
  | zero =>
      intro s t hcard _
      exact hempty s t (by omega)
  | succ m ih =>
      intro s t hcard heven
      by_cases h0 : (s ∆ t).card = 0
      · exact hempty s t h0
      · obtain ⟨c, hc⟩ := heven
        obtain ⟨a, ha, b, hb, hab⟩ :=
          (Finset.one_lt_card (s := s ∆ t)).1 (by omega)
        have hsub : ({a, b} : Finset (Fin n)) ⊆ s ∆ t :=
          Finset.insert_subset_iff.2 ⟨ha, Finset.singleton_subset_iff.2 hb⟩
        have hsym : (s ∆ {a, b}) ∆ t = (s ∆ t) \ {a, b} := by
          rw [symmDiff_assoc, symmDiff_comm ({a, b} : Finset (Fin n)) t, ← symmDiff_assoc,
            Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.2 hsub, Finset.union_empty]
        have hcard2 : ((s ∆ {a, b}) ∆ t).card + 2 = (s ∆ t).card := by
          rw [hsym, Finset.card_sdiff, Finset.inter_eq_left.2 hsub,
            Finset.card_pair_eq_two_iff.2 hab]
          omega
        obtain ⟨l1, hl1⟩ := ih (s ∆ {a, b}) t (by omega) (by rw [Nat.even_iff]; omega)
        obtain ⟨l2, hl2⟩ := exists_toggle_pair hn hab
        exact ⟨l2 ++ l1, by rw [List.foldl_append, hl2 s, hl1]⟩

private theorem even_card_foldl_typeDSpinReflection_iff {n : ℕ} (hn : 2 ≤ n) (l : List (Fin n))
    (s : Finset (Fin n)) :
    Even (l.foldl (fun u j ↦ typeDSpinReflection j u) s).card ↔ Even s.card :=
  predicate_foldl_iff_of_involutive (fun u => Even u.card) typeDSpinReflection
    typeDSpinReflection_involutive (fun u j h => (even_card_typeDSpinReflection_iff hn j u).2 h)
    l s

/-- **The orbits of the simple reflections on the type-`Dₙ` spin basis are exactly the two
half-spin parity classes.** Each reflection preserves the parity of the sign set, and any two
sign sets of equal parity are joined by a word of reflections. So the two half-spin families of
weights are the connected components of the reflection graph on the spin weights. -/
theorem exists_typeDSpinReflections_eq_iff {n : ℕ} (hn : 2 ≤ n) (s t : Finset (Fin n)) :
    (∃ l : List (Fin n), l.foldl (fun u j ↦ typeDSpinReflection j u) s = t) ↔
      (Even s.card ↔ Even t.card) := by
  constructor
  · rintro ⟨l, hl⟩
    rw [← hl, even_card_foldl_typeDSpinReflection_iff hn]
  · intro hparity
    exact exists_foldl_typeDSpinReflection_eq hn (s ∆ t).card s t le_rfl
      ((Finset.even_card_symmDiff_iff s t).2 hparity)

end TauCeti.DynkinType
