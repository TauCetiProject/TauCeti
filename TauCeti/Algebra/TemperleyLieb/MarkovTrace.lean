/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Basic
public import TauCeti.LinearAlgebra.Matrix.ExtendLast
public import TauCeti.Logic.Function.Update
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# The Markov trace on the Temperley-Lieb algebra

A *Markov trace* on the tower of Temperley-Lieb algebras `TemperleyLieb R δ n` is a family of
linear functionals `tr` with `tr (x * y) = tr (y * x)` that is compatible with adding a strand:
`tr (strandIncl x) = δ * tr x`, and `tr (strandIncl x * e (Fin.last n)) = tr x`. Composed with
the Jones representation of the braid group it is the braid route to the Kauffman bracket and the
Jones polynomial: the trace property gives invariance under conjugation of braids, and the two
compatibilities give invariance under the Markov stabilization move. This file constructs such a
trace, `TauCeti.TemperleyLieb.markovTrace`, for every loop value of the form `δ = -(q + q⁻¹)` with
`q` a unit, normalized by `tr 1 = δ ^ n`.

The construction is the spin (vertex) model. The algebra on `n` strands acts on functions of
`n` spins `s : Fin n → Bool`: the generator `e i` acts as `spinGenerator q j k` on the strands
`j = i`, `k = i + 1`, the identity on the other strands tensored with the rank-one matrix
`cup ⊗ cap` on these two, where the cup vector `spinCup q` and the cap covector `spinCap q` are
supported on the two antiparallel pairs of spins:

* `cup (true, false) = -q`, `cup (false, true) = 1`;
* `cap (true, false) = 1`, `cap (false, true) = -q⁻¹`.

These matrices satisfy the three families of Temperley-Lieb relations, which is what makes
`TauCeti.TemperleyLieb.spinRep` an algebra map: the quadratic relation, since closing a loop
gives `cap · cup = -(q + q⁻¹) = δ`; the adjacent zigzag relations, since the two zigzag
contractions of a cup with a cap are the identity; and the distant commutation relation, since
generator matrices on disjoint pairs of strands commute. The trace is the weighted matrix trace
`tr x = trace (diagonal (spinWeight q) * spinRep x)` with spin weights `-q` for `true` and `-q⁻¹`
for `false`. Every generator preserves the multiset of spins it touches, so the weight matrix
commutes with the representation and the weighted trace is a trace. The weights sum to `δ`, which
gives `tr (strandIncl x) = δ * tr x`, and the weighted partial trace of `cup ⊗ cap` over its
second strand, with that strand weighted by `markovWeight q`, is the identity, which gives the
Markov property.

## Main definitions

* `TauCeti.TemperleyLieb.spinGenerator`: the matrix of a generator in the spin model.
* `TauCeti.TemperleyLieb.spinRep`: the spin representation of the Temperley-Lieb algebra.
* `TauCeti.TemperleyLieb.spinWeight`: the weight of a spin configuration.
* `Matrix.extendLast`: a matrix on `m` spins acting on `m + 1` spins, as the
  identity on the last one: the Kronecker product `1 ⊗ₖ X`, reindexed along `Fin.snocEquiv`.
* `TauCeti.TemperleyLieb.markovTrace`: the Markov trace.

## Main results

* `TauCeti.TemperleyLieb.markovTrace_one`: the trace of the identity on `n` strands is `δ ^ n`.
* `TauCeti.TemperleyLieb.markovTrace_mul_comm`: the trace property.
* `TauCeti.TemperleyLieb.markovTrace_strandIncl`: adding a straight strand multiplies the
  trace by `δ`.
* `TauCeti.TemperleyLieb.markovTrace_strandIncl_mul_e_last`: the Markov property, capping the
  added strand with the previous one does not change the trace.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335-388 (the Markov trace on the Temperley-Lieb algebras).
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527-553 (link invariants from a weighted trace of a vertex model).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
-/

public section

open Function Matrix
open scoped Kronecker

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The cup vector of the spin model: the weight of a pair of spins at the two feet of a cup. It
is supported on the antiparallel pairs, with `cup (true, false) = -q` and
`cup (false, true) = 1`. -/
def spinCup : Bool → Bool → R
  | true, false => -(q : R)
  | false, true => 1
  | _, _ => 0

/-- The cap covector of the spin model: the weight of a pair of spins at the two feet of a cap.
It is supported on the antiparallel pairs, with `cap (true, false) = 1` and
`cap (false, true) = -q⁻¹`. -/
def spinCap : Bool → Bool → R
  | true, false => 1
  | false, true => -((q⁻¹ : Rˣ) : R)
  | _, _ => 0

/-- The weight of a single spin in the Markov trace: `-q` for `true` and `-q⁻¹` for `false`.
The two weights sum to the loop value `-(q + q⁻¹)`. -/
def markovWeight : Bool → R
  | true => -(q : R)
  | false => -((q⁻¹ : Rˣ) : R)

@[simp] theorem spinCup_true_false : spinCup q true false = -(q : R) := (rfl)

@[simp] theorem spinCup_false_true : spinCup q false true = 1 := (rfl)

/-- The cup vanishes on parallel spins. -/
@[simp] theorem spinCup_self (x : Bool) : spinCup q x x = 0 := by cases x <;> rfl

@[simp] theorem spinCap_true_false : spinCap q true false = 1 := (rfl)

@[simp] theorem spinCap_false_true : spinCap q false true = -((q⁻¹ : Rˣ) : R) := (rfl)

/-- The cap vanishes on parallel spins. -/
@[simp] theorem spinCap_self (x : Bool) : spinCap q x x = 0 := by cases x <;> rfl

@[simp] theorem markovWeight_true : markovWeight q true = -(q : R) := (rfl)

@[simp] theorem markovWeight_false : markovWeight q false = -((q⁻¹ : Rˣ) : R) := (rfl)

/-- The spin weights sum to the loop value. -/
theorem sum_markovWeight : ∑ b, markovWeight q b = -((q : R) + ((q⁻¹ : Rˣ) : R)) := by
  simp
  ring

/-- The contraction behind `e i * e (i + 1) * e i = e i`, as it appears in the matrix entry at
the spins `x` and `y` on the third strand: it is the identity matrix in `x` and `y`. -/
private theorem zigzag_left (x y : Bool) (z : R) :
    ∑ b, ∑ c, spinCap q b c * (spinCup q c x * ∑ b', ∑ c', spinCap q b' c' *
      (if c' = y then spinCup q b b' * z else 0)) = if x = y then z else 0 := by
  cases x <;> cases y <;> simp

/-- The contraction behind `e (i + 1) * e i * e (i + 1) = e (i + 1)`, as it appears in the matrix
entry at the spins `x` and `y` on the first strand: it is the identity matrix in `x` and `y`. -/
private theorem zigzag_right (x y : Bool) (z : R) :
    ∑ b, ∑ c, spinCap q b c * (spinCup q x b * ∑ b', ∑ c', spinCap q b' c' *
      (if b' = y then spinCup q c' c * z else 0)) = if x = y then z else 0 := by
  cases x <;> cases y <;> simp

variable {n : ℕ}

/-- The matrix of a Temperley-Lieb generator in the spin model on `n` strands: the identity on the
strands other than `j` and `k`, tensored with the rank-one matrix `cup ⊗ cap` on the strands `j`
and `k`. Its entry at the spin configurations `s` and `t` is `cup (s j, s k) * cap (t j, t k)` when
`s` and `t` agree off `j` and `k`, and `0` otherwise. -/
def spinGenerator (j k : Fin n) : Matrix (Fin n → Bool) (Fin n → Bool) R :=
  Matrix.of fun s t ↦ if ∀ l ∉ ({j, k} : Finset (Fin n)), s l = t l then
    spinCup q (s j) (s k) * spinCap q (t j) (t k) else 0

theorem spinGenerator_apply (j k : Fin n) (s t : Fin n → Bool) :
    spinGenerator q j k s t = if ∀ l ∉ ({j, k} : Finset (Fin n)), s l = t l then
      spinCup q (s j) (s k) * spinCap q (t j) (t k) else 0 := (rfl)

/-- Left multiplication by a generator matrix caps the strands `j` and `k` of the row index: the
row `s` of the product is `cup (s j, s k)` times the `cap`-weighted sum of the rows of `X` at the
configurations obtained from `s` by resetting the spins on `j` and `k`. -/
theorem spinGenerator_mul_apply {j k : Fin n} (hjk : j ≠ k)
    (X : Matrix (Fin n → Bool) (Fin n → Bool) R) (s u : Fin n → Bool) :
    (spinGenerator q j k * X) s u =
      spinCup q (s j) (s k) * ∑ b, ∑ c, spinCap q b c * X (update (update s j b) k c) u := by
  classical
  rw [mul_apply]
  simp only [spinGenerator_apply, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have himage : Finset.univ.filter (fun t : Fin n → Bool ↦ ∀ l ∉ ({j, k} : Finset (Fin n)),
      s l = t l) = Finset.univ.image fun bc : Bool × Bool ↦ update (update s j bc.1) k bc.2 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.exists]
    constructor
    · intro h
      refine ⟨t j, t k, funext fun l ↦ ?_⟩
      by_cases hlk : l = k
      · subst hlk; simp
      by_cases hlj : l = j
      · subst hlj; simp [hjk]
      rw [update_of_ne hlk, update_of_ne hlj]
      exact h l (by simp [hlj, hlk])
    · rintro ⟨b, c, rfl⟩ l hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      rw [update_of_ne hl.2, update_of_ne hl.1]
  rw [himage, Finset.sum_image]
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp [hjk]
    ring
  · rintro ⟨b, c⟩ - ⟨b', c'⟩ - h
    have hj := congrFun h j
    have hk := congrFun h k
    simp [hjk] at hj hk
    simp [hj, hk]

/-- A generator matrix does not see the row spins on the strands it caps, except through the
cup. -/
theorem spinGenerator_update_update_apply {j k : Fin n} (hjk : j ≠ k) (s u : Fin n → Bool)
    (b c : Bool) :
    spinGenerator q j k (update (update s j b) k c) u =
      if ∀ l ∉ ({j, k} : Finset (Fin n)), s l = u l
      then spinCup q b c * spinCap q (u j) (u k) else 0 := by
  simp only [spinGenerator_apply,
    forall_notMem_update_eq_iff_of_mem (show k ∈ ({j, k} : Finset (Fin n)) by simp),
    forall_notMem_update_eq_iff_of_mem (show j ∈ ({j, k} : Finset (Fin n)) by simp)]
  simp [update_of_ne hjk]

/-- Closing a loop multiplies a generator matrix by the loop value `-(q + q⁻¹)`. -/
theorem spinGenerator_mul_self {j k : Fin n} (hjk : j ≠ k) :
    spinGenerator q j k * spinGenerator q j k =
      (-((q : R) + ((q⁻¹ : Rˣ) : R))) • spinGenerator q j k := by
  ext s u
  rw [spinGenerator_mul_apply q hjk, Matrix.smul_apply, spinGenerator_apply]
  simp_rw [spinGenerator_update_update_apply q hjk]
  split_ifs
  · simp
    ring
  · simp

/-- The zigzag relation for two generator matrices sharing the strand `k`, with the first one
on the left. -/
theorem spinGenerator_zigzag_left {j k l : Fin n} (hjk : j ≠ k) (hkl : k ≠ l)
    (hjl : j ≠ l) :
    spinGenerator q j k * spinGenerator q k l * spinGenerator q j k = spinGenerator q j k := by
  ext s u
  rw [mul_assoc, spinGenerator_mul_apply q hjk]
  simp_rw [spinGenerator_mul_apply q hkl]
  have hl : l ∉ ({j, k} : Finset (Fin n)) := by simp [hjl.symm, hkl.symm]
  simp only [spinGenerator_apply, forall_notMem_update_eq_iff_of_notMem hl,
    forall_notMem_update_eq_iff_of_mem (show k ∈ insert l ({j, k} : Finset (Fin n)) by simp),
    forall_notMem_update_eq_iff_of_mem (show j ∈ insert l ({j, k} : Finset (Fin n)) by simp),
    Finset.forall_notMem_iff_forall_notMem_insert (p := fun l ↦ s l = u l) hl]
  simp only [update_self, update_of_ne hjk, update_of_ne hkl.symm, update_of_ne hjl.symm,
    update_of_ne hkl, update_of_ne hjl]
  by_cases hA : ∀ m ∉ insert l ({j, k} : Finset (Fin n)), s m = u m
  · simp only [eq_true hA, true_and]
    rw [zigzag_left]
    split_ifs <;> simp
  · simp only [eq_false hA, false_and, ite_false, mul_zero, Finset.sum_const_zero]

/-- The zigzag relation for two generator matrices sharing the strand `k`, with the second one
on the left. -/
theorem spinGenerator_zigzag_right {j k l : Fin n} (hjk : j ≠ k) (hkl : k ≠ l)
    (hjl : j ≠ l) :
    spinGenerator q k l * spinGenerator q j k * spinGenerator q k l = spinGenerator q k l := by
  ext s u
  rw [mul_assoc, spinGenerator_mul_apply q hkl]
  simp_rw [spinGenerator_mul_apply q hjk]
  have hj : j ∉ ({k, l} : Finset (Fin n)) := by simp [hjk, hjl]
  simp only [spinGenerator_apply,
    forall_notMem_update_eq_iff_of_mem (show k ∈ ({k, l} : Finset (Fin n)) by simp),
    forall_notMem_update_eq_iff_of_mem (show k ∈ insert j ({k, l} : Finset (Fin n)) by simp),
    forall_notMem_update_eq_iff_of_notMem hj,
    forall_notMem_update_eq_iff_of_mem (show l ∈ insert j ({k, l} : Finset (Fin n)) by simp),
    Finset.forall_notMem_iff_forall_notMem_insert (p := fun l ↦ s l = u l) hj]
  simp only [update_self, update_of_ne hjk, update_of_ne hkl.symm, update_of_ne hjl.symm,
    update_of_ne hkl, update_of_ne hjl]
  by_cases hA : ∀ m ∉ insert j ({k, l} : Finset (Fin n)), s m = u m
  · simp only [eq_true hA, true_and]
    rw [zigzag_right]
    split_ifs <;> simp
  · simp only [eq_false hA, false_and, ite_false, mul_zero, Finset.sum_const_zero]

/-- Generator matrices on disjoint pairs of strands commute. -/
theorem spinGenerator_mul_spinGenerator_comm {j k l m : Fin n} (hjk : j ≠ k) (hlm : l ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    spinGenerator q j k * spinGenerator q l m = spinGenerator q l m * spinGenerator q j k := by
  ext s u
  rw [spinGenerator_mul_apply q hjk, spinGenerator_mul_apply q hlm]
  have hk : k ∉ ({l, m} : Finset (Fin n)) := by simp [hkl, hkm]
  have hj : j ∉ insert k ({l, m} : Finset (Fin n)) := by simp [hjk, hjl, hjm]
  have hm : m ∉ ({j, k} : Finset (Fin n)) := by simp [hjm.symm, hkm.symm]
  have hl : l ∉ insert m ({j, k} : Finset (Fin n)) := by simp [hlm, hjl.symm, hkl.symm]
  have hS : insert j (insert k ({l, m} : Finset (Fin n))) = insert l (insert m {j, k}) := by
    ext; simp; tauto
  simp only [spinGenerator_apply, forall_notMem_update_eq_iff_of_notMem hk,
    forall_notMem_update_eq_iff_of_notMem hj, forall_notMem_update_eq_iff_of_notMem hm,
    forall_notMem_update_eq_iff_of_notMem hl, hS]
  simp only [update_of_ne hjl.symm, update_of_ne hjm.symm, update_of_ne hkl.symm,
    update_of_ne hkm.symm, update_of_ne hjl, update_of_ne hjm, update_of_ne hkl,
    update_of_ne hkm]
  by_cases hA : ∀ x ∉ insert l (insert m ({j, k} : Finset (Fin n))), s x = u x
  · simp only [eq_true hA, true_and, ite_and, mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    ring
  · simp only [eq_false hA, false_and, ite_false, mul_zero, Finset.sum_const_zero]

section Rep

variable {δ : R} (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))

/-- The spin representation of the Temperley-Lieb algebra on `n` strands with loop value
`δ = -(q + q⁻¹)`: the generator `e i` acts by the generator matrix on the strands `i` and
`i + 1`. -/
def spinRep : TemperleyLieb R δ n →ₐ[R] Matrix (Fin n → Bool) (Fin n → Bool) R :=
  lift (fun i ↦ spinGenerator q ⟨i, by omega⟩ ⟨i + 1, by omega⟩)
    (fun i ↦ by rw [hδ]; exact spinGenerator_mul_self q (by grind))
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      simp only at h ⊢
      rcases h with rfl | rfl
      · exact spinGenerator_zigzag_left q (by grind) (by grind) (by grind)
      · exact spinGenerator_zigzag_right q (by grind) (by grind) (by grind))
    (fun {i j} h ↦ spinGenerator_mul_spinGenerator_comm q (by grind) (by grind) (by grind)
      (by grind) (by grind) (by grind))

/-- The spin representation sends the generator `e i` to the generator matrix on the strands `i`
and `i + 1`. -/
@[simp]
theorem spinRep_e (i : Fin (n - 1)) :
    spinRep q hδ (e δ i) = spinGenerator q ⟨i, by omega⟩ ⟨i + 1, by omega⟩ :=
  lift_e _ _ _ _ i

end Rep

/-- The weight of a spin configuration in the Markov trace: the product of the weights of its
spins. -/
def spinWeight (s : Fin n → Bool) : R := ∏ l, markovWeight q (s l)

/-- Two configurations that agree away from the strands `j` and `k` and are antiparallel on them
have the same weight: each carries one spin `true` and one spin `false` on these two strands. -/
theorem spinWeight_eq_of_forall_notMem {j k : Fin n} {s t : Fin n → Bool}
    (h : ∀ l ∉ ({j, k} : Finset (Fin n)), s l = t l) (hs : s j ≠ s k) (ht : t j ≠ t k) :
    spinWeight q s = spinWeight q t := by
  have hjk : j ≠ k := by rintro rfl; exact hs rfl
  rw [spinWeight, spinWeight, ← Finset.prod_mul_prod_compl {j, k},
    ← Finset.prod_mul_prod_compl {j, k} fun l ↦ markovWeight q (t l), Finset.prod_pair hjk,
    Finset.prod_pair hjk,
    Finset.prod_congr rfl fun l hl ↦ by rw [h l (Finset.mem_compl.1 hl)]]
  congr 1
  revert hs ht; cases s j <;> cases s k <;> cases t j <;> cases t k <;> simp [mul_comm]

/-- A generator matrix commutes with the weight matrix: it only exchanges the two antiparallel
configurations of the strands it caps. -/
theorem diagonal_spinWeight_mul_spinGenerator (j k : Fin n) :
    diagonal (spinWeight q) * spinGenerator q j k =
      spinGenerator q j k * diagonal (spinWeight q) := by
  ext s t
  rw [diagonal_mul, mul_diagonal, spinGenerator_apply]
  split_ifs with h
  · by_cases hs : s j = s k
    · simp [hs]
    by_cases ht : t j = t k
    · simp [ht]
    rw [spinWeight_eq_of_forall_notMem q h hs ht]
    ring
  · simp

/-- The image of the spin representation commutes with the weight matrix. -/
theorem commute_diagonal_spinWeight_spinRep {δ : R} (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (x : TemperleyLieb R δ n) : Commute (diagonal (spinWeight q)) (spinRep q hδ x) := by
  have hle : (spinRep (n := n) q hδ).range ≤
      Subalgebra.centralizer R {diagonal (spinWeight q)} := by
    rw [← Algebra.map_top, ← adjoin_range_e, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    rw [spinRep_e]
    exact diagonal_spinWeight_mul_spinGenerator q _ _
  exact ((Subalgebra.mem_centralizer_iff R).1 (hle ⟨x, rfl⟩) _ rfl)

section Extend

variable {m : ℕ}

/-- The weight of a configuration with one more spin. -/
@[simp]
theorem spinWeight_snoc (s : Fin m → Bool) (c : Bool) :
    spinWeight q (Fin.snoc s c : Fin (m + 1) → Bool) = spinWeight q s * markovWeight q c := by
  simp [spinWeight, Fin.prod_univ_castSucc]

/-- A generator matrix on strands that do not include the last one is extended from fewer
strands. -/
@[simp]
theorem spinGenerator_castSucc (j k : Fin m) :
    spinGenerator q j.castSucc k.castSucc = extendLast (spinGenerator q j k) := by
  ext s t
  rw [extendLast_apply, spinGenerator_apply, spinGenerator_apply]
  have hiff : (∀ l ∉ ({j.castSucc, k.castSucc} : Finset (Fin (m + 1))), s l = t l) ↔
      s (Fin.last m) = t (Fin.last m) ∧ ∀ l ∉ ({j, k} : Finset (Fin m)),
        Fin.init s l = Fin.init t l := by
    rw [Fin.forall_fin_succ', and_comm]
    simp [Fin.init, (Fin.castSucc_lt_last j).ne', (Fin.castSucc_lt_last k).ne']
  simp only [hiff, ite_and]
  congr

/-- The weight matrix on `m + 1` spins is the Kronecker product of the weight matrices of the last
spin and of the first `m` spins. -/
private theorem diagonal_spinWeight_succ :
    diagonal (spinWeight q) = reindex (Fin.snocEquiv fun _ ↦ Bool) (Fin.snocEquiv fun _ ↦ Bool)
      (diagonal (markovWeight q) ⊗ₖ diagonal (spinWeight (n := m) q)) := by
  rw [diagonal_kronecker_diagonal, reindex_apply, submatrix_diagonal_equiv]
  congr 1
  funext s
  conv_lhs => rw [← Fin.snoc_init_self s]
  rw [spinWeight_snoc, mul_comm]
  rfl

/-- Weighted trace of an extended matrix: the added strand contributes the sum of the spin
weights. -/
theorem trace_diagonal_spinWeight_mul_extendLast (X : Matrix (Fin m → Bool) (Fin m → Bool) R) :
    trace (diagonal (spinWeight q) * extendLast X) =
      (∑ c, markovWeight q c) * trace (diagonal (spinWeight q) * X) := by
  rw [diagonal_spinWeight_succ, extendLast_eq, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← mul_kronecker_mul, mul_one, ← trace_diagonal, ← trace_kronecker]
  simp only [trace, Matrix.diag_apply, submatrix_apply]
  exact Equiv.sum_comp _ fun i ↦ (diagonal (markovWeight q) ⊗ₖ (diagonal (spinWeight q) * X)) i i

private theorem markov_partial_sum (y : Bool) (G H : Bool → R) :
    ∑ x, spinCup q y x * ∑ b, ∑ c, spinCap q b c *
      (G b * markovWeight q c * if c = x then H b else 0) = G y * H y := by
  cases y
  · simp only [Fintype.sum_bool]
    simp
    linear_combination (G false * H false) * q.inv_mul
  · simp only [Fintype.sum_bool]
    simp
    linear_combination (G true * H true) * q.mul_inv

/-- The weighted partial trace over the added strand of an extended matrix composed with the
generator matrix capping the added strand with the previous one recovers the weighted trace of the
original matrix. -/
theorem trace_diagonal_spinWeight_mul_extendLast_mul_spinGenerator
    (X : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) R) :
    trace (diagonal (spinWeight q) * (extendLast X *
      spinGenerator q (Fin.last m).castSucc (Fin.last (m + 1)))) =
      trace (diagonal (spinWeight q) * X) := by
  rw [← mul_assoc, trace_mul_comm, trace]
  simp only [Matrix.diag_apply, spinGenerator_mul_apply q (Fin.castSucc_lt_last _).ne, diagonal_mul,
    extendLast_apply, update_self, Fin.init_update_last, Fin.init_update_castSucc]
  rw [← (Fin.snocEquiv fun _ ↦ Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, Fin.snoc_castSucc, Fin.init_snoc,
    ← Fin.snoc_update, Fin.update_snoc_last, spinWeight_snoc]
  simp only [trace, Matrix.diag_apply, diagonal_mul]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [markov_partial_sum q (s (Fin.last m)) (fun b ↦ spinWeight q (update s (Fin.last m) b))
    (fun b ↦ X (update s (Fin.last m) b) s)]
  simp

end Extend

section MarkovTrace

variable {δ : R} (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))

/-- The Markov trace on the Temperley-Lieb algebra on `n` strands with loop value
`δ = -(q + q⁻¹)`: the trace of the spin representation weighted by
`TauCeti.TemperleyLieb.spinWeight`. It is normalized by `markovTrace q hδ 1 = δ ^ n`, one
factor of `δ` for each of the `n` loops in the closure of the identity diagram. -/
def markovTrace : TemperleyLieb R δ n →ₗ[R] R :=
  traceLinearMap (Fin n → Bool) R R ∘ₗ LinearMap.mulLeft R (diagonal (spinWeight q)) ∘ₗ
    (spinRep q hδ).toLinearMap

/-- The Markov trace is the weighted trace of the spin representation. -/
theorem markovTrace_apply (x : TemperleyLieb R δ n) :
    markovTrace q hδ x = trace (diagonal (spinWeight q) * spinRep q hδ x) := (rfl)

/-- The Markov trace of the identity on `n` strands, whose closure is `n` loops, is `δ ^ n`. -/
@[simp]
theorem markovTrace_one : markovTrace q hδ (1 : TemperleyLieb R δ n) = δ ^ n := by
  rw [markovTrace_apply, map_one, mul_one, trace_diagonal, hδ, ← sum_markovWeight q,
    ← Fin.prod_const, Fintype.prod_sum]
  simp only [spinWeight]

/-- **The trace property** of the Markov trace. -/
theorem markovTrace_mul_comm (x y : TemperleyLieb R δ n) :
    markovTrace q hδ (x * y) = markovTrace q hδ (y * x) := by
  rw [markovTrace_apply, markovTrace_apply, map_mul, map_mul, ← mul_assoc,
    (commute_diagonal_spinWeight_spinRep q hδ x).eq, mul_assoc, trace_mul_comm, mul_assoc]

/-- The spin representation intertwines adding a straight strand with `extendLast`. -/
@[simp]
theorem spinRep_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    spinRep q hδ (strandIncl x) = extendLast (spinRep q hδ x) := by
  have h : (spinRep q hδ).comp strandIncl = extendLast.comp (spinRep (n := n + 1) q hδ) :=
    hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, strandIncl_e, spinRep_e, ← spinGenerator_castSucc]
      congr 1
  exact DFunLike.congr_fun h x

/-- Adding a straight strand multiplies the Markov trace by the loop value: the new strand closes
up to one more loop. -/
@[simp]
theorem markovTrace_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    markovTrace q hδ (strandIncl x) = δ * markovTrace q hδ x := by
  rw [markovTrace_apply, markovTrace_apply, spinRep_strandIncl,
    trace_diagonal_spinWeight_mul_extendLast, sum_markovWeight, ← hδ]

/-- **The Markov property**: capping the added last strand with the previous one does not change
the Markov trace, the closure of the cap being isotopic to a straight strand. -/
@[simp]
theorem markovTrace_strandIncl_mul_e_last (x : TemperleyLieb R δ (n + 1)) :
    markovTrace q hδ (strandIncl x * e δ (Fin.last n)) = markovTrace q hδ x := by
  rw [markovTrace_apply, markovTrace_apply, map_mul, spinRep_strandIncl, spinRep_e]
  exact trace_diagonal_spinWeight_mul_extendLast_mul_spinGenerator q _

end MarkovTrace

end TauCeti.TemperleyLieb
