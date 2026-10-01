/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
public import TauCeti.RepresentationTheory.Spin.Weight
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.RootSystem.Chain

/-!
# Type `B` spin weights in the simply connected character lattice

The spinor module has weights `1 / 2 * (±e₀ ± ⋯ ± e_{n-1})` in the usual orthonormal
coordinates.  The simply connected type `Bₙ` datum instead writes its character lattice in the
fundamental-weight basis, so a weight is recorded by its pairings with the simple coroots

```text
eᵢ - eᵢ₊₁  (i + 1 < n),       2e_{n-1}  (i + 1 = n).
```

In those coordinates all spin weights are integral.  This file defines the resulting sign-vector
family `TauCeti.DynkinType.typeBSpinWeight`, compares it coordinate by coordinate with
`TauCeti.spinWeight`, and proves that the family spans the full character lattice `Fin n → ℤ`.
The spanning result is the full-weight input needed to construct the simply connected type `B`
Chevalley carrier from the spin representation: the adjoint representation supplies only the
index-two root lattice.

The file then describes how the Weyl group moves these weights around, at every rank.  A spin
weight is minuscule: each of its simple-coroot coordinates is `-1`, `0` or `1`, so the `i`-th
simple reflection carries a spin weight to a spin weight, and it does so by exchanging the signs
at the two nonterminal nodes `i` and `i + 1`, or by flipping the last sign at the terminal node.
That involution of sign sets is `TauCeti.DynkinType.typeBSpinReflection`; it is identified with
reflection in the pinned datum, distinct sign sets are shown to have distinct weights, and every
sign set is reached from the all-negative one by a finite sequence of simple reflections.  So the
spin weights form a single Weyl orbit of pairwise distinct minuscule weights, which is what makes
the spin module of the type-`B` Chevalley carrier irreducible in every characteristic.

## Main declarations

* `TauCeti.DynkinType.typeBSpinWeight`: a spin weight in fundamental-weight coordinates.
* `TauCeti.DynkinType.algebraMap_typeBSpinWeight_apply`: comparison with the half-integer
  orthonormal coordinates of `TauCeti.spinWeight`.
* `TauCeti.DynkinType.span_range_typeBSpinWeight_eq_top`: the spin weights generate the full
  simply connected character lattice.
* `TauCeti.DynkinType.typeBSpinReflection`: the `i`-th simple reflection as an involution of sign
  sets, with `TauCeti.DynkinType.typeBSpinWeight_typeBSpinReflection_apply` the reflection formula
  against the Bourbaki-numbered Cartan matrix and
  `TauCeti.DynkinType.typeBSimplyConnectedRootDatum_reflection_typeBSpinWeight` its
  identification with reflection in the pinned datum.
* `TauCeti.DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one`: the spin weights are
  minuscule.
* `TauCeti.DynkinType.typeBSpinWeight_injective`: distinct sign sets have distinct weights.
* `TauCeti.DynkinType.typeBSpinReflection_eq_self_iff`: a simple reflection fixes a sign set
  exactly when the matching coordinate of its weight vanishes.
* `TauCeti.DynkinType.exists_typeBSpinReflections_eq`: the sign sets form a single orbit of the
  simple reflections.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 13.2.

The reflection interface follows the fixed-rank tables of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight`, which the
minuscule weights of type `E₆` carry; here the orbit is described uniformly in the rank instead.
-/

public section

namespace TauCeti.DynkinType

open Set Submodule

/-! ## Integral spin weights -/

/-- The weight of a type `Bₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`; at the terminal node it is the
last sign, because the last simple coroot is `2e_{n-1}`. -/
def typeBSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if Order.succ i ∈ s then 1 else 0
  else 2 * (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `B` spin weight. -/
@[simp]
theorem typeBSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeBSpinWeight s i =
      if (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if Order.succ i ∈ s then 1 else 0
      else 2 * (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

/-- Mapping a difference of sign indicators gives the difference of the corresponding
half-integral sign weights. -/
private theorem algebraMap_indicator_sub_eq_spinWeight_sub {K : Type*} [CommRing K]
    [Invertible (2 : K)] {n : ℕ} (s : Finset (Fin n)) (i j : Fin n) :
    algebraMap ℤ K ((if i ∈ s then 1 else 0) - if j ∈ s then 1 else 0) =
      spinWeight K s i - spinWeight K s j := by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simp [hi, hj]
    · simp [hi, hj, sub_neg_eq_add]
  · by_cases hj : j ∈ s
    · simpa [hi, hj, sub_eq_add_neg] using
        (spinWeight_add_self_of_notMem (K := K) hi).symm
    · simp [hi, hj]

/-- The coordinate comparison, in any commutative ring in which `2` is invertible:
`typeBSpinWeight` is obtained from the orthonormal sign weight by pairing with the simple
coroot, that is, by taking an adjacent difference away from the terminal node and doubling the
terminal coordinate. -/
theorem algebraMap_typeBSpinWeight_apply {K : Type*} [CommRing K] [Invertible (2 : K)] {n : ℕ}
    (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeBSpinWeight s i) =
      if (i : ℕ) + 1 < n then spinWeight K s i - spinWeight K s (Order.succ i)
      else spinWeight K s i + spinWeight K s i := by
  classical
  rw [typeBSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · simpa [hnext] using algebraMap_indicator_sub_eq_spinWeight_sub s i (Order.succ i)
  · simp only [ite_eq_right hnext]
    by_cases hi : i ∈ s
    · simp [hi]
    · simp only [ite_eq_right hi, mul_zero, zero_sub, map_neg, map_one]
      exact (spinWeight_add_self_of_notMem (K := K) hi).symm

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeBSpinWeight {K : Type*} [CommRing K] [Invertible (2 : K)] {n : ℕ}
    (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ K (typeBSpinWeight s i)) =
      fun i : Fin n => if (i : ℕ) + 1 < n then spinWeight K s i - spinWeight K s (Order.succ i)
      else spinWeight K s i + spinWeight K s i := by
  funext i
  exact algebraMap_typeBSpinWeight_apply s i

/-! ## A spanning family -/

/-- The all-positive sign weight has only its terminal fundamental-weight coordinate nonzero. -/
private theorem typeBSpinWeight_univ_apply {n : ℕ} (i : Fin n) :
    typeBSpinWeight (Finset.univ : Finset (Fin n)) i =
      if (i : ℕ) + 1 = n then 1 else 0 := by
  rw [typeBSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · have hne : ¬(i : ℕ) + 1 = n := by omega
    rw [ite_eq_left hnext, ite_eq_right hne]
    simp
  · have heq : (i : ℕ) + 1 = n := by omega
    rw [ite_eq_right hnext, ite_eq_left heq]
    simp

/-- The cut weight has a `1` at the cut, a `-1` at a later terminal node, and zero in every
other coordinate. -/
private theorem typeBSpinWeight_Iic_apply {n : ℕ} (i j : Fin n) :
    typeBSpinWeight (Finset.Iic i) j =
      if j = i then 1 else if (j : ℕ) + 1 = n then -1 else 0 := by
  classical
  rcases lt_trichotomy j i with hji | hji | hij
  · have hjnext : (j : ℕ) + 1 < n := by omega
    have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
    have hjnotmax : ¬IsMax j := not_isMax_of_lt hji
    have hsuccle : Order.succ j ≤ i :=
      (Order.succ_le_iff_of_not_isMax hjnotmax).2 hji
    simp [typeBSpinWeight_apply, hjnext, hjnotlast, Finset.mem_Iic, hji.le, hsuccle, hji.ne]
  · subst j
    by_cases hinext : (i : ℕ) + 1 < n
    · have hinotmax : ¬IsMax i :=
        not_isMax_of_lt (b := (⟨(i : ℕ) + 1, hinext⟩ : Fin n)) (by simp [Fin.lt_def])
      simp [typeBSpinWeight_apply, hinext, Finset.mem_Iic,
        Order.succ_le_iff_of_not_isMax hinotmax]
    · have hilast : (i : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hilast]
  · have hjnotle : ¬j ≤ i := not_le_of_gt hij
    have hsuccnotle : ¬Order.succ j ≤ i := fun h ↦ hjnotle (Order.le_succ j |>.trans h)
    by_cases hjnext : (j : ℕ) + 1 < n
    · have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hjnext, hjnotlast, Finset.mem_Iic, hjnotle, hsuccnotle,
        hij.ne']
    · have hjlast : (j : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hjlast, Finset.mem_Iic, hjnotle, hij.ne']

/-- At a terminal node, the corresponding cut sign weight is the coordinate basis vector. -/
private theorem typeBSpinWeight_cut_eq_single_of_isLast {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    typeBSpinWeight (Finset.Iic i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeBSpinWeight_Iic_apply, Pi.single_apply]
  by_cases hji : j = i
  · simp [hji]
  · have hjnotlast : ¬(j : ℕ) + 1 = n := fun hjlast ↦ hji (Fin.ext (by omega))
    simp [hji, hjnotlast]

/-- At a nonterminal node, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeBSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeBSpinWeight (Finset.Iic i) +
        typeBSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  rw [Pi.add_apply, typeBSpinWeight_Iic_apply, typeBSpinWeight_univ_apply, Pi.single_apply]
  by_cases hji : j = i
  · subst j
    simp [hi.ne]
  · by_cases hjlast : (j : ℕ) + 1 = n
    · simp [hji, hjlast]
    · simp [hji, hjlast]

/-- **The type `Bₙ` spin weights generate the full simply connected character lattice.**

For a nonterminal node `i`, the sign sequence positive through `i` has weight
`ωᵢ - ω_{n-1}`, while the all-positive sequence has weight `ω_{n-1}`. At the terminal node the
cut sequence is already `ω_{n-1}`. Thus every fundamental-weight basis vector lies in the span. -/
theorem span_range_typeBSpinWeight_eq_top (n : ℕ) :
    Submodule.span ℤ (Set.range (typeBSpinWeight (n := n))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  by_cases hi : (i : ℕ) + 1 = n
  · rw [← typeBSpinWeight_cut_eq_single_of_isLast i hi]
    exact Submodule.subset_span ⟨Finset.Iic i, rfl⟩
  · have hi' : (i : ℕ) + 1 < n := by omega
    rw [← typeBSpinWeight_cut_add_univ_eq_single i hi']
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨Finset.Iic i, rfl⟩)
      (Submodule.subset_span ⟨Finset.univ, rfl⟩)

/-! ## The simple reflections on sign sets -/

/-- **The `i`-th simple reflection of type `Bₙ`, acting on spin sign sets.**

The spin weights are indexed by the finite set of positive signs, and the Weyl group acts on them
by signed permutations of the orthonormal coordinates. At a nonterminal node the simple root is
`eᵢ - eᵢ₊₁`, so its reflection exchanges the signs at `i` and `i + 1`; at the terminal node the
simple root is `e_{n-1}`, so its reflection flips the last sign. -/
def typeBSpinReflection {n : ℕ} (i : Fin n) : Equiv.Perm (Finset (Fin n)) :=
  if (i : ℕ) + 1 < n then
    Equiv.finsetCongr (Equiv.swap i (Order.succ i))
  else
    (symmDiff_left_involutive {i}).toPerm (fun s ↦ symmDiff s {i})

/-- At a nonterminal node the simple reflection transports a sign set along the transposition of
the node with its successor. -/
theorem typeBSpinReflection_apply_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n)
    (s : Finset (Fin n)) :
    typeBSpinReflection i s = s.map (Equiv.swap i (Order.succ i)).toEmbedding := by
  simp [typeBSpinReflection, h]

/-- At the terminal node the simple reflection toggles the membership of that node. -/
theorem typeBSpinReflection_apply_of_last {n : ℕ} {i : Fin n} (h : ¬(i : ℕ) + 1 < n)
    (s : Finset (Fin n)) :
    typeBSpinReflection i s = symmDiff s {i} := by
  simp [typeBSpinReflection, h]

/-- **The simple reflections are involutions.** -/
@[simp]
theorem typeBSpinReflection_apply_apply {n : ℕ} (i : Fin n) (s : Finset (Fin n)) :
    typeBSpinReflection i (typeBSpinReflection i s) = s :=
  by
    by_cases h : (i : ℕ) + 1 < n
    · rw [typeBSpinReflection_apply_of_lt h, typeBSpinReflection_apply_of_lt h]
      simpa [Equiv.finsetCongr_symm] using
        (Equiv.symm_apply_apply (Equiv.finsetCongr (Equiv.swap i (Order.succ i))) s)
    · simp [typeBSpinReflection_apply_of_last h]

/-- Membership in a reflected sign set at a nonterminal node, read through the transposition of
the node with its successor. -/
@[simp]
theorem mem_typeBSpinReflection_iff_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n)
    {s : Finset (Fin n)} {a : Fin n} :
    a ∈ typeBSpinReflection i s ↔ Equiv.swap i (Order.succ i) a ∈ s := by
  rw [typeBSpinReflection_apply_of_lt h, Finset.mem_map_equiv, Equiv.symm_swap]

/-- Membership in a reflected sign set at the terminal node: only that node's sign changes. -/
@[simp]
theorem mem_typeBSpinReflection_iff_of_last {n : ℕ} {i : Fin n} (h : ¬(i : ℕ) + 1 < n)
    {s : Finset (Fin n)} {a : Fin n} :
    a ∈ typeBSpinReflection i s ↔ (if a = i then a ∉ s else a ∈ s) := by
  rw [typeBSpinReflection_apply_of_last h]
  by_cases hai : a = i
  · subst hai
    simp [Finset.mem_symmDiff]
  · simp [Finset.mem_symmDiff, hai]

/-! ## The reflection formula -/

private theorem ite_mem_typeBSpinReflection_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n)
    (s : Finset (Fin n)) (a : Fin n) :
    (if a ∈ typeBSpinReflection i s then (1 : ℤ) else 0) =
      if Equiv.swap i (Order.succ i) a ∈ s then 1 else 0 := by
  simp only [mem_typeBSpinReflection_iff_of_lt h]

private theorem ite_mem_typeBSpinReflection_of_last {n : ℕ} {i : Fin n} (h : ¬(i : ℕ) + 1 < n)
    (s : Finset (Fin n)) {a : Fin n} (ha : a ≠ i) :
    (if a ∈ typeBSpinReflection i s then (1 : ℤ) else 0) = if a ∈ s then 1 else 0 := by
  simp only [mem_typeBSpinReflection_iff_of_last h, ite_eq_right ha]

private theorem ite_self_mem_typeBSpinReflection_of_last {n : ℕ} {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) (s : Finset (Fin n)) :
    (if i ∈ typeBSpinReflection i s then (1 : ℤ) else 0) = 1 - if i ∈ s then 1 else 0 := by
  by_cases hs : i ∈ s <;> simp [mem_typeBSpinReflection_iff_of_last h, hs]

/-! ### Coordinates of a reflected spin weight -/

/-- A spin weight coordinate depends only on the signs at that node and at its successor. -/
private theorem typeBSpinWeight_apply_eq_of_ite_mem_eq {n : ℕ} {s t : Finset (Fin n)} {j : Fin n}
    (hj : (if j ∈ s then (1 : ℤ) else 0) = if j ∈ t then 1 else 0)
    (hsj : (if (Order.succ j : Fin n) ∈ s then (1 : ℤ) else 0) =
      if (Order.succ j : Fin n) ∈ t then 1 else 0) :
    typeBSpinWeight s j = typeBSpinWeight t j := by
  rw [typeBSpinWeight_apply, typeBSpinWeight_apply]
  by_cases h : (j : ℕ) + 1 < n
  · rw [ite_eq_left h, ite_eq_left h, hj, hsj]
  · rw [ite_eq_right h, ite_eq_right h, hj]

/-- Reflecting in the `i`-th simple root negates the `i`-th coordinate of a spin weight. -/
private theorem typeBSpinWeight_typeBSpinReflection_apply_self {n : ℕ} (i : Fin n)
    (s : Finset (Fin n)) :
    typeBSpinWeight (typeBSpinReflection i s) i = -typeBSpinWeight s i := by
  by_cases hilt : (i : ℕ) + 1 < n
  · rw [typeBSpinWeight_apply (typeBSpinReflection i s) i, ite_eq_left hilt,
      ite_mem_typeBSpinReflection_of_lt hilt, ite_mem_typeBSpinReflection_of_lt hilt,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      typeBSpinWeight_apply s i, ite_eq_left hilt]
    ring
  · rw [typeBSpinWeight_apply (typeBSpinReflection i s) i, ite_eq_right hilt,
      ite_self_mem_typeBSpinReflection_of_last hilt,
      typeBSpinWeight_apply s i, ite_eq_right hilt]
    ring

/-- At a nonterminal node one step past the reflecting one, the reflected coordinate is the old
coordinate plus the coordinate at the reflecting node. -/
private theorem typeBSpinWeight_typeBSpinReflection_apply_of_succ {n : ℕ} {i j : Fin n}
    (hij : (j : ℕ) = (i : ℕ) + 1) (hjlt : (j : ℕ) + 1 < n) (s : Finset (Fin n)) :
    typeBSpinWeight (typeBSpinReflection i s) j = typeBSpinWeight s j + typeBSpinWeight s i := by
  have hilt : (i : ℕ) + 1 < n := by omega
  have hsucci : ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := Fin.val_orderSucc_of_lt hilt
  have hsuccj : ((Order.succ j : Fin n) : ℕ) = (j : ℕ) + 1 := Fin.val_orderSucc_of_lt hjlt
  have hjsucci : j = (Order.succ i : Fin n) := Fin.ext (by omega)
  have hswapj : Equiv.swap i (Order.succ i) j = i := by
    rw [hjsucci]; exact Equiv.swap_apply_right i (Order.succ i)
  have hswapsj : Equiv.swap i (Order.succ i) (Order.succ j) = (Order.succ j : Fin n) :=
    Equiv.swap_apply_of_ne_of_ne (fun hc => by rw [hc] at hsuccj; omega)
      (fun hc => by rw [hc, hsucci] at hsuccj; omega)
  have hmem : (if (Order.succ i : Fin n) ∈ s then (1 : ℤ) else 0) = if j ∈ s then 1 else 0 := by
    rw [hjsucci]
  rw [typeBSpinWeight_apply (typeBSpinReflection i s) j, ite_eq_left hjlt,
    ite_mem_typeBSpinReflection_of_lt hilt, ite_mem_typeBSpinReflection_of_lt hilt,
    hswapj, hswapsj, typeBSpinWeight_apply s j, ite_eq_left hjlt,
    typeBSpinWeight_apply s i, ite_eq_left hilt, hmem]
  ring

/-- At the terminal node one step past the reflecting one, where the simple root is the short one
and its coroot the long one, the reflected coordinate gains twice the coordinate at the reflecting
node. -/
private theorem typeBSpinWeight_typeBSpinReflection_apply_of_succ_of_last {n : ℕ} {i j : Fin n}
    (hij : (j : ℕ) = (i : ℕ) + 1) (hjlt : ¬(j : ℕ) + 1 < n) (s : Finset (Fin n)) :
    typeBSpinWeight (typeBSpinReflection i s) j =
      typeBSpinWeight s j + 2 * typeBSpinWeight s i := by
  have hjv := j.isLt
  have hilt : (i : ℕ) + 1 < n := by omega
  have hsucci : ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := Fin.val_orderSucc_of_lt hilt
  have hjsucci : j = (Order.succ i : Fin n) := Fin.ext (by omega)
  have hswapj : Equiv.swap i (Order.succ i) j = i := by
    rw [hjsucci]; exact Equiv.swap_apply_right i (Order.succ i)
  have hmem : (if (Order.succ i : Fin n) ∈ s then (1 : ℤ) else 0) = if j ∈ s then 1 else 0 := by
    rw [hjsucci]
  rw [typeBSpinWeight_apply (typeBSpinReflection i s) j, ite_eq_right hjlt,
    ite_mem_typeBSpinReflection_of_lt hilt, hswapj,
    typeBSpinWeight_apply s j, ite_eq_right hjlt,
    typeBSpinWeight_apply s i, ite_eq_left hilt, hmem]
  ring

/-- At the node one step before the reflecting one, the reflected coordinate is the old
coordinate plus the coordinate at the reflecting node. -/
private theorem typeBSpinWeight_typeBSpinReflection_apply_of_pred {n : ℕ} {i j : Fin n}
    (hij : (j : ℕ) + 1 = (i : ℕ)) (s : Finset (Fin n)) :
    typeBSpinWeight (typeBSpinReflection i s) j = typeBSpinWeight s j + typeBSpinWeight s i := by
  have hiv := i.isLt
  have hjlt : (j : ℕ) + 1 < n := by omega
  have hsuccj : ((Order.succ j : Fin n) : ℕ) = (j : ℕ) + 1 := Fin.val_orderSucc_of_lt hjlt
  have hsuccji : (Order.succ j : Fin n) = i := Fin.ext (by omega)
  have hji : j ≠ i := fun hc => by rw [hc] at hij; omega
  by_cases hilt : (i : ℕ) + 1 < n
  · have hsucci : ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := Fin.val_orderSucc_of_lt hilt
    have h1 : j ≠ (Order.succ i : Fin n) := fun hc => by rw [hc, hsucci] at hij; omega
    have hswapj : Equiv.swap i (Order.succ i) j = j := Equiv.swap_apply_of_ne_of_ne hji h1
    have hswapsj : Equiv.swap i (Order.succ i) (Order.succ j) = (Order.succ i : Fin n) := by
      rw [hsuccji]; exact Equiv.swap_apply_left i (Order.succ i)
    rw [typeBSpinWeight_apply (typeBSpinReflection i s) j, ite_eq_left hjlt,
      ite_mem_typeBSpinReflection_of_lt hilt, ite_mem_typeBSpinReflection_of_lt hilt,
      hswapj, hswapsj, typeBSpinWeight_apply s j, ite_eq_left hjlt,
      typeBSpinWeight_apply s i, ite_eq_left hilt, hsuccji]
    ring
  · have hrefl : (if (Order.succ j : Fin n) ∈ typeBSpinReflection i s then (1 : ℤ) else 0) =
        1 - if i ∈ s then 1 else 0 := by
      rw [hsuccji]; exact ite_self_mem_typeBSpinReflection_of_last hilt s
    rw [typeBSpinWeight_apply (typeBSpinReflection i s) j, ite_eq_left hjlt,
      ite_mem_typeBSpinReflection_of_last hilt s hji, hrefl,
      typeBSpinWeight_apply s j, ite_eq_left hjlt,
      typeBSpinWeight_apply s i, ite_eq_right hilt, hsuccji]
    ring

/-- Away from the reflecting node and its two neighbours, a spin weight coordinate is
unchanged by the reflection. -/
private theorem typeBSpinWeight_typeBSpinReflection_apply_of_not_adjacent {n : ℕ} {i j : Fin n}
    (hne : (j : ℕ) ≠ (i : ℕ)) (hsucc : (j : ℕ) ≠ (i : ℕ) + 1) (hpred : (j : ℕ) + 1 ≠ (i : ℕ))
    (s : Finset (Fin n)) :
    typeBSpinWeight (typeBSpinReflection i s) j = typeBSpinWeight s j := by
  have hji : j ≠ i := fun hc => hne (congrArg Fin.val hc)
  have hsjne : (Order.succ j : Fin n) ≠ i := by
    intro hc
    have hv := congrArg Fin.val hc
    by_cases hjlt : (j : ℕ) + 1 < n
    · rw [Fin.val_orderSucc_of_lt hjlt] at hv
      exact hpred hv
    · rw [Fin.orderSucc_eq_self_of_not_lt hjlt] at hv
      exact hne hv
  by_cases hilt : (i : ℕ) + 1 < n
  · have hsucci : ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := Fin.val_orderSucc_of_lt hilt
    have h1 : j ≠ (Order.succ i : Fin n) := fun hc => hsucc (by rw [hc, hsucci])
    have h2 : (Order.succ j : Fin n) ≠ (Order.succ i : Fin n) := by
      intro hc
      have hv := congrArg Fin.val hc
      rw [hsucci] at hv
      by_cases hjlt : (j : ℕ) + 1 < n
      · rw [Fin.val_orderSucc_of_lt hjlt] at hv
        exact hne (by omega)
      · rw [Fin.orderSucc_eq_self_of_not_lt hjlt] at hv
        exact hsucc hv
    exact typeBSpinWeight_apply_eq_of_ite_mem_eq
      (by rw [ite_mem_typeBSpinReflection_of_lt hilt, Equiv.swap_apply_of_ne_of_ne hji h1])
      (by rw [ite_mem_typeBSpinReflection_of_lt hilt, Equiv.swap_apply_of_ne_of_ne hsjne h2])
  · exact typeBSpinWeight_apply_eq_of_ite_mem_eq
      (ite_mem_typeBSpinReflection_of_last hilt s hji)
      (ite_mem_typeBSpinReflection_of_last hilt s hsjne)

/-! ### The formula -/

/-- **The reflection formula for type-`Bₙ` spin weights.** Reflecting a sign set in the `i`-th
simple root subtracts, from its weight, the `i`-th simple-coroot coordinate of that weight times
the `i`-th simple root. In the fundamental-weight basis the `i`-th simple root is the `i`-th row
of the Bourbaki-numbered Cartan matrix, so the spin weights are permuted by the Weyl group.

That row is the row of a chain of type `B`, `TauCeti.chainBEntry`, whose double edge points at the
terminal node: the terminal simple root is the short one, so the root before it pairs to `-2` with
the long terminal coroot, while the terminal root pairs to `-1` with the coroot before it. -/
theorem typeBSpinWeight_typeBSpinReflection_apply {n : ℕ} (i : Fin n) (s : Finset (Fin n))
    (j : Fin n) :
    typeBSpinWeight (typeBSpinReflection i s) j =
      typeBSpinWeight s j - typeBSpinWeight s i * CartanMatrix.B n i j := by
  have hjv := j.isLt
  rw [← chainBEntry_eq_cartanMatrix_B]
  by_cases hji : (j : ℕ) = (i : ℕ)
  · obtain rfl : j = i := Fin.ext hji
    rw [typeBSpinWeight_typeBSpinReflection_apply_self, chainBEntry_self]
    ring
  · by_cases hsucc : (j : ℕ) = (i : ℕ) + 1
    · rw [hsucc, chainBEntry_succ_right]
      by_cases hjlt : (j : ℕ) + 1 < n
      · have hnotlast : (i : ℕ) + 1 ≠ n - 1 := by omega
        rw [typeBSpinWeight_typeBSpinReflection_apply_of_succ hsucc hjlt,
          ite_eq_right hnotlast]
        ring
      · have hlast : (i : ℕ) + 1 = n - 1 := by omega
        rw [typeBSpinWeight_typeBSpinReflection_apply_of_succ_of_last hsucc hjlt,
          ite_eq_left hlast]
        ring
    · by_cases hpred : (j : ℕ) + 1 = (i : ℕ)
      · rw [typeBSpinWeight_typeBSpinReflection_apply_of_pred hpred, ← hpred,
          chainBEntry_succ_left]
        ring
      · rw [typeBSpinWeight_typeBSpinReflection_apply_of_not_adjacent hji hsucc hpred,
          chainBEntry_eq_zero (Ne.symm hji) (Ne.symm hsucc) hpred]
        ring

/-! ## Distinct weights and fixed points -/

/-- Every simple-coroot coordinate of a type-`Bₙ` spin weight is `-1`, `0` or `1`: the spin
weights are minuscule. -/
theorem typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one {n : ℕ} (s : Finset (Fin n))
    (i : Fin n) :
    typeBSpinWeight s i = -1 ∨ typeBSpinWeight s i = 0 ∨ typeBSpinWeight s i = 1 := by
  rw [typeBSpinWeight_apply]
  split_ifs <;> omega

private theorem mem_iff_of_ite_eq [DecidableEq α] {s t : Finset α} {a : α}
    (h : (if a ∈ s then (1 : ℤ) else 0) = if a ∈ t then 1 else 0) : a ∈ s ↔ a ∈ t := by
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp_all

private theorem mem_iff_mem_of_typeBSpinWeight_eq {n : ℕ} {s t : Finset (Fin n)}
    (h : typeBSpinWeight s = typeBSpinWeight t) (k : ℕ) :
    ∀ i : Fin n, (i : ℕ) + k + 1 = n → (i ∈ s ↔ i ∈ t) := by
  induction k with
  | zero =>
    intro i hik
    have hilt : ¬(i : ℕ) + 1 < n := by omega
    have hw := congrFun h i
    rw [typeBSpinWeight_apply, typeBSpinWeight_apply, ite_eq_right hilt,
      ite_eq_right hilt] at hw
    exact mem_iff_of_ite_eq (by linarith)
  | succ k ih =>
    intro i hik
    have hilt : (i : ℕ) + 1 < n := by omega
    have hsucci : ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := Fin.val_orderSucc_of_lt hilt
    have hmem := ih (Order.succ i) (by omega)
    have hsuccind : (if (Order.succ i : Fin n) ∈ s then (1 : ℤ) else 0) =
        if (Order.succ i : Fin n) ∈ t then 1 else 0 := by simp only [hmem]
    have hw := congrFun h i
    rw [typeBSpinWeight_apply, typeBSpinWeight_apply, ite_eq_left hilt, ite_eq_left hilt] at hw
    rw [hsuccind] at hw
    exact mem_iff_of_ite_eq (by linarith)

/-- **Distinct sign sets have distinct type-`Bₙ` spin weights.** The last coordinate of the weight
recovers the last sign, and the remaining signs follow from the adjacent differences. -/
theorem typeBSpinWeight_injective {n : ℕ} : Function.Injective (typeBSpinWeight (n := n)) := by
  intro s t h
  ext i
  have := i.isLt
  exact mem_iff_mem_of_typeBSpinWeight_eq h (n - 1 - (i : ℕ)) i (by omega)

/-- A simple reflection fixes a sign set exactly when the matching simple-coroot coordinate of its
weight vanishes. -/
@[simp]
theorem typeBSpinReflection_eq_self_iff {n : ℕ} (i : Fin n) (s : Finset (Fin n)) :
    typeBSpinReflection i s = s ↔ typeBSpinWeight s i = 0 := by
  constructor
  · intro h
    have hw := typeBSpinWeight_typeBSpinReflection_apply i s i
    rw [h, CartanMatrix.B_diag] at hw
    linarith
  · intro h
    apply typeBSpinWeight_injective
    funext k
    rw [typeBSpinWeight_typeBSpinReflection_apply, h]
    ring

/-! ## A single Weyl orbit -/

/-- Moving the largest positive sign up to the terminal node and flipping it there reduces a sign
set to one with a smaller support, which is the induction step behind
`TauCeti.DynkinType.exists_typeBSpinReflections_eq`. -/
private theorem exists_typeBSpinReflections_eq_aux {n : ℕ} (d : ℕ) :
    ∀ (a : Fin n) (s : Finset (Fin n)), n - 1 - (a : ℕ) = d → a ∈ s →
      (∀ b : Fin n, a < b → b ∉ s) →
      (∃ l : List (Fin n), l.foldl (fun t i => typeBSpinReflection i t) ∅ = s.erase a) →
      ∃ l : List (Fin n), l.foldl (fun t i => typeBSpinReflection i t) ∅ = s := by
  induction d with
  | zero =>
    intro a s hd ha _ hrec
    obtain ⟨l, hl⟩ := hrec
    have halast : ¬(a : ℕ) + 1 < n := by have := a.isLt; omega
    refine ⟨l ++ [a], ?_⟩
    rw [List.foldl_append, hl]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [typeBSpinReflection_apply_of_last halast]
    ext b
    simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
    by_cases hb : b = a
    · subst hb
      simp [ha]
    · simp [hb]
  | succ d ih =>
    intro a s hd ha hmax hrec
    have hlt : (a : ℕ) + 1 < n := by have := a.isLt; omega
    have hsucca : ((Order.succ a : Fin n) : ℕ) = (a : ℕ) + 1 := Fin.val_orderSucc_of_lt hlt
    have hane : a ≠ (Order.succ a : Fin n) := fun hc => by rw [← hc] at hsucca; omega
    have hasucclt : a < (Order.succ a : Fin n) := by rw [Fin.lt_def, hsucca]; omega
    have hsuccnotmem : (Order.succ a : Fin n) ∉ s := hmax _ hasucclt
    have hrefl : typeBSpinReflection a s = insert (Order.succ a : Fin n) (s.erase a) := by
      ext b
      rw [mem_typeBSpinReflection_iff_of_lt hlt, Finset.mem_insert, Finset.mem_erase]
      by_cases hba : b = a
      · subst hba
        rw [Equiv.swap_apply_left]
        simp [hsuccnotmem, hane]
      · by_cases hbs : b = (Order.succ a : Fin n)
        · subst hbs
          rw [Equiv.swap_apply_right]
          simp [ha]
        · rw [Equiv.swap_apply_of_ne_of_ne hba hbs]
          simp [hba, hbs]
    have hmax' : ∀ b : Fin n, (Order.succ a : Fin n) < b → b ∉ insert
        (Order.succ a : Fin n) (s.erase a) := by
      intro b hb hmem
      have hab : a < b := lt_trans hasucclt hb
      rw [Finset.mem_insert, Finset.mem_erase] at hmem
      rcases hmem with h | ⟨-, h⟩
      · exact absurd h.symm hb.ne
      · exact hmax b hab h
    obtain ⟨l, hl⟩ := ih (Order.succ a) (insert (Order.succ a : Fin n) (s.erase a))
      (by rw [hsucca]; omega) (Finset.mem_insert_self _ _) hmax'
      (by rw [Finset.erase_insert (fun hc => hsuccnotmem (Finset.mem_of_mem_erase hc))]
          exact hrec)
    refine ⟨l ++ [a], ?_⟩
    rw [List.foldl_append, hl]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hrefl, typeBSpinReflection_apply_apply]

/-- **The type-`Bₙ` spin weights form a single orbit of the simple reflections.** Every sign set is
reached from the all-negative one by a finite sequence of simple reflections, so the spin module is
minuscule with a connected weight graph. -/
theorem exists_typeBSpinReflections_eq {n : ℕ} (s : Finset (Fin n)) :
    ∃ l : List (Fin n), l.foldl (fun t i => typeBSpinReflection i t) ∅ = s := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨[], rfl⟩
    · exact exists_typeBSpinReflections_eq_aux (n - 1 - ((s.max' hs : Fin n) : ℕ))
        (s.max' hs) s rfl (s.max'_mem hs)
        (fun b hb hbs => absurd (s.le_max' b hbs) (not_le.2 hb))
        (ih _ (Finset.erase_ssubset (s.max'_mem hs)))

/-- **The sign-set reflection is reflection in the pinned type-`Bₙ` datum.** The weight of a
reflected sign set is the Weyl reflection of its weight in the corresponding simple root of
`TauCeti.DynkinType.typeBSimplyConnectedRootDatum`. -/
@[simp]
theorem typeBSimplyConnectedRootDatum_reflection_typeBSpinWeight {n : ℕ} (i : Fin n)
    (s : Finset (Fin n)) :
    (typeBSimplyConnectedRootDatum n).reflection (typeBSimpleIndex n i) (typeBSpinWeight s) =
      typeBSpinWeight (typeBSpinReflection i s) := by
  have hcoroot : (typeBSimplyConnectedRootDatum n).coroot' (typeBSimpleIndex n i)
      (typeBSpinWeight s) = typeBSpinWeight s i := by
    simp
  rw [RootPairing.reflection_apply, hcoroot]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, root_typeBSimpleIndex]
  rw [typeBSpinWeight_typeBSpinReflection_apply]

end TauCeti.DynkinType
