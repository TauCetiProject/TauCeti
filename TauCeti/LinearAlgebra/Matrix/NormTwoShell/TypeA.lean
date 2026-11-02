/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# The norm-two shell of the Cartan matrix of type `A`

Let `B = CartanMatrix.A r` be the Cartan matrix of type `A_r` on the simple-root lattice
`Q = Fin r → ℤ`. The simple root `αₖ` is `εₖ - εₖ₊₁` in the standard coordinates `εₘ` of
`ℤ^{r+1}`; the matrix `TauCeti.typeASimpleRootMatrix r` records these columns, and
`B = Dᵀ D` for that matrix `D` (`TauCeti.transpose_typeASimpleRootMatrix_mul_self`), so the Gram
pairing of `Q` is the standard dot product of the classical coordinates.

The vector of `Q` with classical coordinates `ε_p - ε_q` is `TauCeti.typeAPairRoot r p q`: its
coordinate at the vertex `k` is `1` for `p ≤ k < q`, `-1` for `q ≤ k < p`, and `0` otherwise, so
for `p < q` it is the interval root `α_p + ⋯ + α_(q-1)`. The main result is that these vectors,
for `p ≠ q`, are exactly the norm-two shell of `B`, that is, the roots of `A_r`
(`TauCeti.typeANormTwoShellEquiv`). A norm-two vector `a` has classical coordinates `D a` of
squared length `2` and coordinate sum `0`. By the classification of the integer vectors of squared
length `2` (`TauCeti.DynkinType.TypeDRoot.exists_eq_single_sub_or_add_or_neg_add`), the sum
condition leaves only the shape `ε_p - ε_q`.

The file also evaluates the ordered sign form `Matrix.orderedSignForm B` of the ordered sign
cover on two such roots (`TauCeti.orderedSignForm_cartanMatrix_A_typeAPairRoot`). For the order of
`Fin r`, the only nonzero strictly lower entries of `B` are the `-1`s just below the diagonal,
so the form of `a` and `b` is minus the sum `∑ₖ a (k + 1) * b k` of products of adjacent
coordinates. These are the facts on which the comparison of the signed shell Lie algebra of `A_r`
with the trace-zero matrices rests.

## Main definitions

* `TauCeti.typeASimpleRootMatrix`: the simple roots of `A_r` as columns in `ℤ^{r+1}`.
* `TauCeti.typeAPairRoot`: the simple-root coordinates of `ε_p - ε_q`.
* `TauCeti.typeANormTwoShellEquiv`: the ordered pairs of distinct indices enumerate the norm-two
  shell of `CartanMatrix.A r`.

## Main results

* `TauCeti.dotProduct_cartanMatrix_A_mulVec`: the Gram pairing of `CartanMatrix.A r` is the dot
  product of the classical coordinates.
* `TauCeti.typeASimpleRootMatrix_mulVec_typeAPairRoot`: the classical coordinates of
  `typeAPairRoot r p q` are `ε_p - ε_q`.
* `TauCeti.typeAPairRoot_dotProduct_cartanMatrix_A_mulVec`: the pairing of two pair roots.
* `TauCeti.exists_typeAPairRoot_eq_of_mem_normTwoShell`: every root is a pair root.
* `TauCeti.typeAPairRoot_eq_coroot`: the pair roots are the coroots of the pinned root datum
  `TauCeti.DynkinType.typeASimplyConnectedRootDatum r`, with the same index pairs.
* `TauCeti.orderedSignForm_cartanMatrix_A_typeAPairRoot`: the ordered sign form on pair roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §12.1.
-/

public section

namespace TauCeti

open _root_.Matrix

variable (r : ℕ)

/-! ### Classical coordinates -/

/-- The simple roots of type `A_r` in the standard coordinates `εₘ` of `ℤ^{r+1}`: the column at
the vertex `k` is `εₖ - εₖ₊₁`. -/
def typeASimpleRootMatrix : Matrix (Fin (r + 1)) (Fin r) ℤ :=
  .of fun m k ↦ (if m = k.castSucc then 1 else 0) - if m = k.succ then 1 else 0

@[simp]
theorem typeASimpleRootMatrix_apply (m : Fin (r + 1)) (k : Fin r) :
    typeASimpleRootMatrix r m k =
      (if m = k.castSucc then 1 else 0) - if m = k.succ then 1 else 0 :=
  (rfl)

/-- **The Cartan matrix of type `A_r` is the Gram matrix of the simple roots** `εₖ - εₖ₊₁`. -/
theorem transpose_typeASimpleRootMatrix_mul_self :
    (typeASimpleRootMatrix r)ᵀ * typeASimpleRootMatrix r = CartanMatrix.A r := by
  ext i j
  simp only [mul_apply, transpose_apply, typeASimpleRootMatrix_apply, sub_mul, mul_sub, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [CartanMatrix.A, of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- The Gram pairing of `CartanMatrix.A r` is the dot product of the classical coordinates. -/
theorem dotProduct_cartanMatrix_A_mulVec (a b : Fin r → ℤ) :
    a ⬝ᵥ CartanMatrix.A r *ᵥ b =
      (typeASimpleRootMatrix r *ᵥ a) ⬝ᵥ (typeASimpleRootMatrix r *ᵥ b) := by
  rw [← transpose_typeASimpleRootMatrix_mul_self, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- The classical coordinates of a vector of `Q` sum to zero. -/
theorem sum_typeASimpleRootMatrix_mulVec_eq_zero (a : Fin r → ℤ) :
    ∑ m, (typeASimpleRootMatrix r *ᵥ a) m = 0 := by
  simp only [mulVec, dotProduct, typeASimpleRootMatrix_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, sub_eq_zero]
  conv_rhs => rw [Finset.sum_comm]
  simp

/-- The classical coordinates determine the vector: `a ↦ D *ᵥ a` is injective. -/
theorem typeASimpleRootMatrix_mulVec_injective :
    Function.Injective (typeASimpleRootMatrix r).mulVec := by
  intro a b hab
  by_contra hne
  have h := (posDef_cartanMatrix_A r).two_le_dotProduct_mulVec_self
    (fun i ↦ by simp [CartanMatrix.A]) (sub_ne_zero.mpr hne)
  rw [dotProduct_cartanMatrix_A_mulVec, mulVec_sub, sub_eq_zero.mpr hab, zero_dotProduct] at h
  omega

/-! ### The roots -/

/-- **The root `ε_p - ε_q` of type `A_r`**, in simple-root coordinates: its coordinate at the
vertex `k` is `1` if `p ≤ k < q`, `-1` if `q ≤ k < p`, and `0` otherwise. For `p < q` it is the
interval root `α_p + ⋯ + α_(q-1)`. -/
def typeAPairRoot (p q : Fin (r + 1)) : Fin r → ℤ :=
  fun k ↦ (if p ≤ k.castSucc then 1 else 0) - if q ≤ k.castSucc then 1 else 0

theorem typeAPairRoot_apply (p q : Fin (r + 1)) (k : Fin r) :
    typeAPairRoot r p q k =
      (if p ≤ k.castSucc then 1 else 0) - if q ≤ k.castSucc then 1 else 0 :=
  (rfl)

/-- The simple root `αₖ` is the pair root `ε_k - ε_(k+1)`. -/
theorem typeAPairRoot_castSucc_succ (k : Fin r) :
    typeAPairRoot r k.castSucc k.succ = Pi.single k 1 := by
  ext j
  simp only [typeAPairRoot_apply, Pi.single_apply, Fin.le_iff_val_le_val, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> omega

/-- Exchanging the two indices negates the pair root. -/
theorem typeAPairRoot_swap (p q : Fin (r + 1)) : typeAPairRoot r q p = -typeAPairRoot r p q := by
  ext k
  simp [typeAPairRoot_apply]

/-- Pair roots with a common middle index add up. -/
theorem typeAPairRoot_add_typeAPairRoot (p q s : Fin (r + 1)) :
    typeAPairRoot r p q + typeAPairRoot r q s = typeAPairRoot r p s := by
  ext k
  simp [typeAPairRoot_apply]

/-- **The classical coordinates of `typeAPairRoot r p q` are `ε_p - ε_q`.** -/
theorem typeASimpleRootMatrix_mulVec_typeAPairRoot (p q : Fin (r + 1)) :
    typeASimpleRootMatrix r *ᵥ typeAPairRoot r p q = Pi.single p 1 - Pi.single q 1 := by
  -- With `f m = [p ≤ m] - [q ≤ m]` and `f' m = [p < m] - [q < m]`, the coordinate at `m` is
  -- `f m - f' m`: the `εₖ` terms read `f` at `k.castSucc`, the `-εₖ₊₁` terms read `f'` at `k.succ`.
  set f : Fin (r + 1) → ℤ := fun m ↦ (if p ≤ m then 1 else 0) - if q ≤ m then 1 else 0
  set f' : Fin (r + 1) → ℤ := fun m ↦ (if p < m then 1 else 0) - if q < m then 1 else 0
  have hf (k : Fin r) : typeAPairRoot r p q k = f k.castSucc := (rfl)
  have hf' (k : Fin r) : typeAPairRoot r p q k = f' k.succ := by
    simp only [typeAPairRoot_apply, f', Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
      Nat.lt_succ_iff]
  ext m
  have h₁ : ∑ k : Fin r, (if m = k.castSucc then 1 else 0) * typeAPairRoot r p q k = f m := by
    have h := Fin.sum_univ_castSucc fun m' : Fin (r + 1) ↦ (if m = m' then 1 else 0) * f m'
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    simp only [hf, ite_mul, one_mul, zero_mul]
    rw [h]
    simp [f, Fin.le_last]
  have h₂ : ∑ k : Fin r, (if m = k.succ then 1 else 0) * typeAPairRoot r p q k = f' m := by
    have h := Fin.sum_univ_succ fun m' : Fin (r + 1) ↦ (if m = m' then 1 else 0) * f' m'
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    simp only [hf', ite_mul, one_mul, zero_mul]
    rw [h]
    simp [f']
  simp only [mulVec, dotProduct, typeASimpleRootMatrix_apply, sub_mul, Finset.sum_sub_distrib,
    h₁, h₂, f, f', Pi.sub_apply, Pi.single_apply]
  split_ifs <;> first | rfl | (simp_all [lt_iff_le_and_ne]; done) | omega

/-- **The pairing of two pair roots** is the dot product of `ε_p - ε_q` and `ε_p' - ε_q'`. -/
theorem typeAPairRoot_dotProduct_cartanMatrix_A_mulVec (p q p' q' : Fin (r + 1)) :
    typeAPairRoot r p q ⬝ᵥ CartanMatrix.A r *ᵥ typeAPairRoot r p' q' =
      (if p = p' then 1 else 0) - (if p = q' then 1 else 0) - (if q = p' then 1 else 0) +
        if q = q' then 1 else 0 := by
  rw [dotProduct_cartanMatrix_A_mulVec, typeASimpleRootMatrix_mulVec_typeAPairRoot,
    typeASimpleRootMatrix_mulVec_typeAPairRoot]
  simp only [sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul, Pi.single_apply]
  split_ifs <;> simp_all

/-- For distinct indices the pair root is a root. -/
theorem typeAPairRoot_mem_normTwoShell {p q : Fin (r + 1)} (hpq : p ≠ q) :
    typeAPairRoot r p q ∈ (CartanMatrix.A r).normTwoShell := by
  rw [mem_normTwoShell, typeAPairRoot_dotProduct_cartanMatrix_A_mulVec]
  simp [hpq, hpq.symm]

/-- Two pair roots agree exactly when their pairs of indices do, the first pair being of distinct
indices. -/
theorem typeAPairRoot_inj {p q p' q' : Fin (r + 1)} (hpq : p ≠ q) :
    typeAPairRoot r p q = typeAPairRoot r p' q' ↔ p = p' ∧ q = q' := by
  refine ⟨fun h ↦ ?_, fun ⟨hp, hq⟩ ↦ hp ▸ hq ▸ rfl⟩
  have h' := congrArg (typeASimpleRootMatrix r).mulVec h
  simp only [typeASimpleRootMatrix_mulVec_typeAPairRoot] at h'
  have hp := congrFun h' p
  have hq := congrFun h' q
  simp only [Pi.sub_apply, Pi.single_apply, hpq, hpq.symm, ↓reduceIte] at hp hq
  refine ⟨by_contra fun hne ↦ ?_, by_contra fun hne ↦ ?_⟩
  · simp only [hne, ↓reduceIte] at hp
    split_ifs at hp <;> omega
  · simp only [hne, ↓reduceIte] at hq
    split_ifs at hq <;> omega

/-- **The pair root of `(p, q)` is the coroot of the pinned root datum of type `A_r`** indexed by
`(p, q)`, in simple-coroot coordinates; the Cartan matrix being symmetric, this is also the root
`ε_p - ε_q` in simple-root coordinates. -/
theorem typeAPairRoot_eq_coroot (p : DynkinType.TypeAIndex r) :
    typeAPairRoot r p.1.1 p.1.2 =
      (DynkinType.typeASimplyConnectedRootDatum r).coroot (DynkinType.typeAIndexEquiv r p) := by
  ext k
  rw [DynkinType.coroot_typeAIndexEquiv, typeAPairRoot_apply]

/-- **Every root of type `A_r` is a pair root.** -/
theorem exists_typeAPairRoot_eq_of_mem_normTwoShell {a : Fin r → ℤ}
    (ha : a ∈ (CartanMatrix.A r).normTwoShell) :
    ∃ p q, p ≠ q ∧ typeAPairRoot r p q = a := by
  rw [mem_normTwoShell, dotProduct_cartanMatrix_A_mulVec] at ha
  have hsum := sum_typeASimpleRootMatrix_mulVec_eq_zero r a
  -- The classical coordinates have squared length `2`, and their sum `0` rules out `±(ε_p + ε_q)`.
  obtain ⟨p, q, hpq, h | h | h⟩ :=
    DynkinType.TypeDRoot.exists_eq_single_sub_or_add_or_neg_add
      (⟨_, ha⟩ : DynkinType.TypeDRoot (r + 1))
  · exact ⟨p, q, hpq, typeASimpleRootMatrix_mulVec_injective r <| by
      rw [typeASimpleRootMatrix_mulVec_typeAPairRoot, ← h]⟩
  all_goals
    dsimp only at h
    rw [h] at hsum
    simp [Finset.sum_add_distrib] at hsum

/-- **The roots of type `A_r` are enumerated by the ordered pairs of distinct indices** of
`Fin (r + 1)`, the pair `(p, q)` giving the root `ε_p - ε_q`. These are the index pairs of the
pinned root datum `DynkinType.typeASimplyConnectedRootDatum r`, whose coroot at `(p, q)` is this
root (`TauCeti.typeAPairRoot_eq_coroot`). -/
noncomputable def typeANormTwoShellEquiv :
    DynkinType.TypeAIndex r ≃ (CartanMatrix.A r).normTwoShell :=
  Equiv.ofBijective
    (fun p ↦ ⟨typeAPairRoot r p.1.1 p.1.2, typeAPairRoot_mem_normTwoShell r p.2⟩)
    ⟨fun p p' h ↦ by
      obtain ⟨h₁, h₂⟩ := (typeAPairRoot_inj r p.2).mp (congrArg Subtype.val h)
      exact Subtype.ext (Prod.ext h₁ h₂),
    fun a ↦ by
      obtain ⟨p, q, hpq, h⟩ := exists_typeAPairRoot_eq_of_mem_normTwoShell r a.2
      exact ⟨⟨(p, q), hpq⟩, Subtype.ext h⟩⟩

@[simp]
theorem coe_typeANormTwoShellEquiv_apply (p : DynkinType.TypeAIndex r) :
    (typeANormTwoShellEquiv r p : Fin r → ℤ) = typeAPairRoot r p.1.1 p.1.2 :=
  (rfl)

/-- The root of the pair `(p, q)` is `ε_p - ε_q`. -/
@[simp]
theorem typeANormTwoShellEquiv_mk {p q : Fin (r + 1)} (hpq : p ≠ q) :
    typeANormTwoShellEquiv r ⟨(p, q), hpq⟩ =
      ⟨typeAPairRoot r p q, typeAPairRoot_mem_normTwoShell r hpq⟩ :=
  (rfl)

/-- The pair of indices of the root `ε_p - ε_q`. -/
@[simp]
theorem typeANormTwoShellEquiv_symm_mk {p q : Fin (r + 1)} (hpq : p ≠ q) :
    (typeANormTwoShellEquiv r).symm ⟨typeAPairRoot r p q, typeAPairRoot_mem_normTwoShell r hpq⟩ =
      ⟨(p, q), hpq⟩ :=
  (Equiv.symm_apply_eq _).mpr (typeANormTwoShellEquiv_mk r hpq).symm

/-! ### The ordered sign form -/

/-- **The ordered form of `CartanMatrix.A r`**: its only nonzero strictly lower entries are the
`-1`s just below the diagonal. -/
theorem orderedSignForm_cartanMatrix_A (a b : Fin r → ℤ) :
    orderedSignForm (CartanMatrix.A r) a b =
      -∑ i : Fin r, ∑ j : Fin r, if j.val + 1 = i.val then a i * b j else 0 := by
  simp only [orderedSignForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [CartanMatrix.A, of_apply, Fin.ext_iff, Fin.lt_def]
  split_ifs <;> first | omega | ring

/-- The indicator vector of the vertices `k` with `x ≤ k`. -/
private def typeAStep (x : Fin (r + 1)) : Fin r → ℤ :=
  fun k ↦ if x ≤ k.castSucc then 1 else 0

private theorem typeAPairRoot_eq_sub (p q : Fin (r + 1)) :
    typeAPairRoot r p q = typeAStep r p - typeAStep r q :=
  (rfl)

/-- The ordered form of two step vectors is minus the number of vertices `k ≥ max x (y + 1)`. -/
private theorem orderedSignForm_typeAStep (x y : Fin (r + 1)) :
    orderedSignForm (CartanMatrix.A r) (typeAStep r x) (typeAStep r y) =
      -((r - max (x : ℕ) (y + 1) : ℕ) : ℤ) := by
  rw [orderedSignForm_cartanMatrix_A, neg_inj]
  -- Only `j = i - 1` contributes to the inner sum, so the double sum counts the `i` with
  -- `1 ≤ i`, `x ≤ i` and `y ≤ i - 1`.
  have hinner (i : Fin r) : (∑ j : Fin r, if j.val + 1 = i.val then
      typeAStep r x i * typeAStep r y j else 0) =
      if max (x : ℕ) (y + 1) ≤ i.val then 1 else 0 := by
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · rw [Finset.sum_eq_zero fun j _ ↦ by rw [ite_eq_right (by omega)], ite_eq_right (by omega)]
    · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩ (fun j _ hj ↦ by
          rw [ite_eq_right fun h ↦ hj (Fin.ext (by simp only; omega))])
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left (by simp only; omega)]
      simp only [typeAStep, Fin.le_iff_val_le_val, Fin.val_castSucc]
      split_ifs <;> first | rfl | omega
  simp only [hinner]
  rw [Finset.sum_boole, Nat.cast_inj, ← Nat.card_Ico, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico]
  constructor
  · rintro ⟨j, h, rfl⟩
    exact ⟨h, j.2⟩
  · rintro ⟨h, hi⟩
    exact ⟨⟨i, hi⟩, h, rfl⟩

/-- **The ordered form of `CartanMatrix.A r` on two roots.** Writing `c x y = r - max x (y + 1)`
for the number of vertices `k` with `x ≤ k` and `y ≤ k - 1`, the ordered form of `ε_p - ε_q`
and `ε_p' - ε_q'` is `c p q' + c q p' - c p p' - c q q'`. -/
theorem orderedSignForm_cartanMatrix_A_typeAPairRoot (p q p' q' : Fin (r + 1)) :
    orderedSignForm (CartanMatrix.A r) (typeAPairRoot r p q) (typeAPairRoot r p' q') =
      ((r - max (p : ℕ) (q' + 1) : ℕ) : ℤ) + ((r - max (q : ℕ) (p' + 1) : ℕ) : ℤ) -
        ((r - max (p : ℕ) (p' + 1) : ℕ) : ℤ) - ((r - max (q : ℕ) (q' + 1) : ℕ) : ℤ) := by
  simp only [typeAPairRoot_eq_sub, map_sub, LinearMap.sub_apply, orderedSignForm_typeAStep]
  ring

end TauCeti
