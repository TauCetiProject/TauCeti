/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic

/-!
# Coxeter elements of the classical Cartan matrices

This file computes the characteristic polynomial and multiplicative order of the Coxeter element
`Matrix.coxeterElement` for the four classical Cartan families `Aₙ`, `Bₙ`, `Cₙ`, and `Dₙ`, and
records that the Bourbaki vertex order `List.finRange n` is a one-degenerate order of each classical
Dynkin diagram:

| type | condition | `h` | characteristic polynomial |
|---|---|---|---|
| `Aₙ` | `0 < n` (`h`); all `n` (`charpoly`) | `n + 1` | `∑_{k=0}^n X^k` |
| `Bₙ` | `0 < n` | `2 n` | `X^n + 1` |
| `Cₙ` | `0 < n` | `2 n` | `X^n + 1` |
| `Dₙ` | `2 ≤ n` | `2 n - 2` | `(X^{n-1} + 1)(X + 1)` |

In the simple-root basis itself, `coxeterElement (CartanMatrix.A n)` is the all-ones companion
matrix `Matrix.companion (fun _ => 1)`. For `Bₙ`, the unimodular change of basis to the standard
orthonormal basis `e₀, …, e_{n-1}` conjugates the simple reflections to the adjacent transpositions
`(0, 1), …, (n - 2, n - 1)` followed by the sign flip of `e_{n-1}`, whose product is the signed
cycle `Matrix.companion (Pi.single 0 1)`. Type `Cₙ` is intertwined with `Bₙ` by the diagonal
symmetrizer `diag(2, …, 2, 1)`. For `Dₙ` (`2 ≤ n`), expressing the simple roots in `e₀, …, e_{n-1}`
(`α_k = e_k - e_{k+1}` for `k < n - 1` and `α_{n-1} = e_{n-2} + e_{n-1}`) intertwines
`coxeterElement (CartanMatrix.D n)` over `ℤ` (with rational inverse) with the block diagonal sum of
`Matrix.companion (Pi.single 0 1)` of size `n - 1` and `-1` of size `1`.

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A`, `isOneDegenerateOrder_B`, `isOneDegenerateOrder_C`,
  `isOneDegenerateOrder_D`: `List.finRange n` is a one-degenerate order of each classical diagram.
* `TauCeti.Coxeter.coxeterElement_A`, `charpoly_coxeterElement_A`, `orderOf_coxeterElement_A`.
* `TauCeti.Coxeter.charpoly_coxeterElement_B`, `orderOf_coxeterElement_B`.
* `TauCeti.Coxeter.charpoly_coxeterElement_C`, `orderOf_coxeterElement_C`.
* `TauCeti.Coxeter.charpoly_coxeterElement_D`, `orderOf_coxeterElement_D`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### One-degenerate orders of the classical diagrams -/

private theorem isOneDegenerateOrder_finRange_of_lt {n : ℕ} {adj : Fin n → Fin n → Prop}
    (h : ∀ z x y : Fin n, (x : ℕ) < (z : ℕ) → (y : ℕ) < (z : ℕ) → adj z x → adj z y → x = y) :
    List.IsOneDegenerateOrder adj (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hnd : (S₁ ++ z :: S₂).Nodup := hS ▸ List.nodup_finRange n
  have hzS₁ : z ∉ S₁ := fun hz => (List.nodup_append.1 hnd).2.2 z hz z List.mem_cons_self rfl
  have hlt : ∀ u ∈ S₁, (u : ℕ) < (z : ℕ) := by
    intro u hu
    have hu_idx : (List.finRange n).idxOf u = S₁.idxOf u := by
      rw [hS, List.idxOf_append, ite_eq_left hu]
    have hz_idx : (List.finRange n).idxOf z = (z :: S₂).idxOf z + S₁.length := by
      rw [hS, List.idxOf_append, ite_eq_right hzS₁]
    rw [List.idxOf_finRange] at hu_idx hz_idx
    have hlt_len : S₁.idxOf u < S₁.length := List.idxOf_lt_length_of_mem hu
    omega
  exact h z x y (hlt x hx) (hlt y hy) hzx hzy

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.A, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext
  split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.B, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext
  split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  simp only [CartanMatrix.C, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext
  split_ifs at hzx hzy <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of type `Dₙ`. -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange_of_lt fun z x y hxz hyz hzx hzy => ?_
  have _ : (z : ℕ) < n := z.isLt
  simp only [CartanMatrix.D, of_apply, ne_eq, Fin.ext_iff] at hzx hzy
  apply Fin.ext
  split_ifs at hzx hzy <;> omega

/-! ### Prefix-product and intertwining helpers -/

private theorem take_finRange_succ {n m : ℕ} (hm : m < n) :
    (List.finRange n).take (m + 1) = (List.finRange n).take m ++ [⟨m, hm⟩] := by
  have hlen1 : ((List.finRange n).take (m + 1)).length = m + 1 := by
    simp only [List.length_take, List.length_finRange]
    omega
  have hlen2 : ((List.finRange n).take m ++ [(⟨m, hm⟩ : Fin n)]).length = m + 1 := by
    simp only [List.length_append, List.length_take, List.length_finRange, List.length_singleton]
    omega
  refine List.ext_getElem (hlen1.trans hlen2.symm) fun k h₁ h₂ => ?_
  rw [hlen1] at h₁
  have hlen_m : ((List.finRange n).take m).length = m := by
    simp only [List.length_take, List.length_finRange]
    omega
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ h₁) with hkm | rfl
  · rw [List.getElem_take, List.getElem_append_left (by omega), List.getElem_take]
  · rw [List.getElem_take, List.getElem_append_right (by omega)]
    simp [hlen_m]

private theorem take_finRange_self (n : ℕ) :
    (List.finRange n).take n = List.finRange n :=
  List.take_of_length_le (by simp)

private theorem reflMatrix_mulVec_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    reflMatrix A i *ᵥ Pi.single j 1 = Pi.single j 1 - A j i • Pi.single i 1 := by
  ext k
  rw [mulVec_single_one, col_apply, reflMatrix_apply]
  simp [Pi.single_apply, eq_comm]

private theorem mul_reflMatrix_apply {n : ℕ} (V A : Matrix (Fin n) (Fin n) ℤ) (i r j : Fin n) :
    (V * reflMatrix A i) r j = V r j - V r i * A j i := by
  rw [Matrix.mul_apply]
  simp only [reflMatrix_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem mul_list_prod_eq_of_intertwine {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ)
    (f g : Fin n → Matrix (Fin n) (Fin n) ℤ) (h : ∀ i, V * f i = g i * V) (l : List (Fin n)) :
    V * (l.map f).prod = (l.map g).prod * V := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, h a, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

/-- If `V * M = G * V` over `ℤ` and `V` is left-invertible over `ℚ`, then `M` and `G` have the same
characteristic polynomial and multiplicative order. -/
private theorem charpoly_and_orderOf_eq_of_intertwine {n : ℕ}
    {V M G : Matrix (Fin n) (Fin n) ℤ} (hinter : V * M = G * V)
    {U : Matrix (Fin n) (Fin n) ℚ} (hUV : U * V.map (Int.castRingHom ℚ) = 1) :
    M.charpoly = G.charpoly ∧ orderOf M = orderOf G := by
  let φ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℚ :=
    (Int.castRingHom ℚ).mapMatrix
  have hφ_inj : Function.Injective φ :=
    Matrix.map_injective (Int.castRingHom ℚ).injective_int
  have hUV' : U * φ V = 1 := hUV
  have hVU' : φ V * U = 1 := mul_eq_one_comm.1 hUV'
  have hinterQ : φ V * φ M = φ G * φ V := by
    simpa only [map_mul] using congrArg φ hinter
  have hconj : φ V * φ M * U = φ G := by
    rw [hinterQ, Matrix.mul_assoc, hVU', Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · apply Matrix.charpoly_eq_of_map_rat
    change (φ M).charpoly = G.charpoly.map (Int.castRingHom ℚ)
    rw [← charpoly_map, ← RingHom.mapMatrix_apply, ← hconj, Matrix.charpoly_mul_comm,
      ← Matrix.mul_assoc, hUV', Matrix.one_mul]
  · have hpow : ∀ k : ℕ, φ V * φ M ^ k = φ G ^ k * φ V := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hinterQ, ← Matrix.mul_assoc,
          ← pow_succ]
    rw [orderOf_eq_orderOf_iff]
    intro k
    rw [← hφ_inj.eq_iff, map_pow, map_one, ← hφ_inj.eq_iff, map_pow, map_one]
    constructor
    · intro hMk
      calc φ G ^ k = φ G ^ k * (φ V * U) := by rw [hVU', Matrix.mul_one]
        _ = (φ G ^ k * φ V) * U := by rw [Matrix.mul_assoc]
        _ = (φ V * φ M ^ k) * U := by rw [hpow k]
        _ = 1 := by rw [hMk, Matrix.mul_one, hVU']
    · intro hGk
      calc φ M ^ k = (U * φ V) * φ M ^ k := by rw [hUV', Matrix.one_mul]
        _ = U * (φ V * φ M ^ k) := by rw [Matrix.mul_assoc]
        _ = U * (φ G ^ k * φ V) := by rw [hpow k]
        _ = 1 := by rw [hGk, Matrix.one_mul, hUV']

/-! ### Type `Aₙ` -/

private def aPrefixVec (n m : ℕ) (j k : Fin n) : ℤ :=
  if (j : ℕ) + 1 < m then (if (k : ℕ) = (j : ℕ) + 1 then 1 else 0)
  else if (j : ℕ) + 1 = m then (if (k : ℕ) < m then -1 else 0)
  else if (j : ℕ) = m then (if (k : ℕ) ≤ m then 1 else 0)
  else if k = j then 1 else 0

private theorem prod_take_reflMatrix_A_mulVec_single (n : ℕ) {m : ℕ} (hm : m ≤ n) (j : Fin n) :
    (((List.finRange n).take m).map (reflMatrix (CartanMatrix.A n))).prod *ᵥ Pi.single j 1 =
      aPrefixVec n m j := by
  induction m generalizing j with
  | zero =>
    rw [List.take_zero, List.map_nil, List.prod_nil, one_mulVec]
    ext k
    rcases eq_or_ne k j with rfl | hkj
    · simp only [Pi.single_eq_same, aPrefixVec]
      grind
    · have hne : (k : ℕ) ≠ (j : ℕ) := Fin.ext_iff.not.1 hkj
      simp only [Pi.single_eq_of_ne hkj, aPrefixVec, Fin.ext_iff]
      split_ifs <;> omega
  | succ m ih =>
    have hmlt : m < n := by omega
    rw [take_finRange_succ hmlt, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ← mulVec_mulVec, reflMatrix_mulVec_single, mulVec_sub, mulVec_smul,
      ih (by omega), ih (by omega)]
    ext k
    have hp_m : aPrefixVec n m ⟨m, hmlt⟩ k = if (k : ℕ) ≤ m then 1 else 0 := by
      simp [aPrefixVec]
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hp_m]
    have _ := k.isLt
    have _ := j.isLt
    simp only [CartanMatrix.A, of_apply, aPrefixVec, Fin.ext_iff]
    grind

/-- **In the simple-root basis, the Coxeter element of `CartanMatrix.A n` is the all-ones companion
matrix.** -/
theorem coxeterElement_A (n : ℕ) :
    coxeterElement (CartanMatrix.A n) = companion (fun _ : Fin n => (1 : ℤ)) := by
  ext k j
  have h := congrFun (prod_take_reflMatrix_A_mulVec_single n le_rfl j) k
  rw [take_finRange_self, ← coxeterElement, mulVec_single_one, col_apply] at h
  rw [h, companion_apply]
  simp only [aPrefixVec]
  have _ := j.isLt
  have _ := k.isLt
  split_ifs <;> omega

/-- **The characteristic polynomial of the `Aₙ` Coxeter element is `∑_{k=0}^n X^k`.** -/
theorem charpoly_coxeterElement_A (n : ℕ) :
    (coxeterElement (CartanMatrix.A n)).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  rw [coxeterElement_A, charpoly_companion_const_one]

/-- **The Coxeter number of `Aₙ` (`0 < n`) is `n + 1`**: the Coxeter element has order `n + 1`. -/
theorem orderOf_coxeterElement_A {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  rw [coxeterElement_A]
  exact orderOf_companion_const_one hn (by decide)

/-! ### Adjacent-transposition chains for types `Bₙ` and `Dₙ` -/

private def swapMatrix {n : ℕ} (i₁ i₂ : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r c => if r = Equiv.swap i₁ i₂ c then 1 else 0

private theorem swapMatrix_mulVec_single {n : ℕ} (i₁ i₂ j : Fin n) :
    swapMatrix i₁ i₂ *ᵥ Pi.single j 1 = Pi.single (Equiv.swap i₁ i₂ j) 1 := by
  ext r
  rw [mulVec_single_one, col_apply, swapMatrix, of_apply]
  simp [Pi.single_apply]

private theorem swapMatrix_mul_apply {n : ℕ} (i₁ i₂ : Fin n) (V : Matrix (Fin n) (Fin n) ℤ)
    (r j : Fin n) :
    (swapMatrix i₁ i₂ * V) r j = V (Equiv.swap i₁ i₂ r) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Equiv.swap i₁ i₂ r)]
  · simp [swapMatrix]
  · intro x hx
    have hne : r ≠ Equiv.swap i₁ i₂ x := by
      intro hr
      apply hx
      rw [hr, Equiv.swap_apply_self]
    simp [swapMatrix, hne]

private def swapPrefixVec {n : ℕ} (m : ℕ) (j k : Fin n) : ℤ :=
  if (j : ℕ) < m then (if (k : ℕ) = (j : ℕ) + 1 then 1 else 0)
  else if (j : ℕ) = m then (if (k : ℕ) = 0 then 1 else 0)
  else if k = j then 1 else 0

private theorem prod_take_swap_mulVec_single {n : ℕ} (g : Fin n → Matrix (Fin n) (Fin n) ℤ)
    {m : ℕ} (hm : m < n)
    (hg : ∀ (u : ℕ) (_hu : u < m) (hu1 : u + 1 < n),
      g ⟨u, by omega⟩ = swapMatrix ⟨u, by omega⟩ ⟨u + 1, hu1⟩)
    (j : Fin n) :
    (((List.finRange n).take m).map g).prod *ᵥ Pi.single j 1 = swapPrefixVec m j := by
  induction m generalizing j with
  | zero =>
    rw [List.take_zero, List.map_nil, List.prod_nil, one_mulVec]
    ext k
    rw [Pi.single_apply]
    simp only [swapPrefixVec, Fin.ext_iff]
    have _ := k.isLt
    have _ := j.isLt
    split_ifs <;> omega
  | succ m ih =>
    have hm0 : m < n := by omega
    rw [take_finRange_succ hm0, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ← mulVec_mulVec, hg m (by omega) hm, swapMatrix_mulVec_single,
      ih hm0 (fun u hu hu1 => hg u (by omega) hu1)]
    rcases eq_or_ne j ⟨m, hm0⟩ with rfl | hjm
    · rw [Equiv.swap_apply_left]
      ext k
      simp only [swapPrefixVec, Fin.ext_iff]
      split_ifs <;> omega
    · rcases eq_or_ne j ⟨m + 1, hm⟩ with rfl | hjm1
      · rw [Equiv.swap_apply_right]
        ext k
        simp only [swapPrefixVec, Fin.ext_iff]
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hjm hjm1]
        have h1 : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
        have h2 : (j : ℕ) ≠ m + 1 := fun h => hjm1 (Fin.ext h)
        ext k
        simp only [swapPrefixVec, Fin.ext_iff]
        split_ifs <;> omega

/-! ### Type `Bₙ` -/

private def basisB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j => (if r = j then 1 else 0) - (if (r : ℕ) = (j : ℕ) + 1 then 1 else 0)

private def invBasisB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k i => if (i : ℕ) ≤ (k : ℕ) then 1 else 0

private theorem invBasisB_mul_basisB (n : ℕ) : invBasisB n * basisB n = 1 := by
  ext k j
  rw [Matrix.mul_apply]
  simp only [basisB, invBasisB, of_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Fin.ext_iff, Matrix.one_apply]
  rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
  · have h1 : (∑ x : Fin n, if (x : ℕ) = (j : ℕ) then if (x : ℕ) ≤ (k : ℕ) then (1 : ℤ) else 0
        else 0) = if (j : ℕ) ≤ (k : ℕ) then 1 else 0 := by
      rw [Fintype.sum_eq_single j]
      · simp
      · intro x hx
        have hne : (x : ℕ) ≠ (j : ℕ) := fun h => hx (Fin.ext h)
        simp [hne]
    have h2 : (∑ x : Fin n, if (x : ℕ) = (j : ℕ) + 1 then
        if (x : ℕ) ≤ (k : ℕ) then (1 : ℤ) else 0 else 0) =
        if (j : ℕ) + 1 ≤ (k : ℕ) then 1 else 0 := by
      rw [Fintype.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
      · simp
      · intro x hx
        have hne : (x : ℕ) ≠ (j : ℕ) + 1 := fun h => hx (Fin.ext h)
        simp [hne]
    rw [h1, h2]
    split_ifs <;> omega
  · have h2 : (∑ x : Fin n, if (x : ℕ) = (j : ℕ) + 1 then
        if (x : ℕ) ≤ (k : ℕ) then (1 : ℤ) else 0 else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have _ := x.isLt
      split_ifs <;> omega
    have h1 : (∑ x : Fin n, if (x : ℕ) = (j : ℕ) then if (x : ℕ) ≤ (k : ℕ) then (1 : ℤ) else 0
        else 0) = if (j : ℕ) ≤ (k : ℕ) then 1 else 0 := by
      rw [Fintype.sum_eq_single j]
      · simp
      · intro x hx
        have hne : (x : ℕ) ≠ (j : ℕ) := fun h => hx (Fin.ext h)
        simp [hne]
    rw [h1, h2, sub_zero]
    have _ := j.isLt
    have _ := k.isLt
    split_ifs <;> omega

private def signFlipLast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r c => if r = c then (if (c : ℕ) + 1 = n then -1 else 1) else 0

private def reflStdB (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : (i : ℕ) + 1 < n then swapMatrix i ⟨(i : ℕ) + 1, hi⟩ else signFlipLast n

private theorem basisB_mul_reflMatrix_B (n : ℕ) (i : Fin n) :
    basisB n * reflMatrix (CartanMatrix.B n) i = reflStdB n i * basisB n := by
  ext r j
  rw [mul_reflMatrix_apply, reflStdB]
  rcases lt_or_ge ((i : ℕ) + 1) n with hi | hi
  · rw [dite_eq_left hi, swapMatrix_mul_apply]
    have _ := i.isLt
    have _ := r.isLt
    have _ := j.isLt
    rcases eq_or_ne r i with rfl | hri
    · simp only [Equiv.swap_apply_left, basisB, CartanMatrix.B, of_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rcases eq_or_ne r ⟨(i : ℕ) + 1, hi⟩ with rfl | hri1
      · simp only [Equiv.swap_apply_right, basisB, CartanMatrix.B, of_apply, Fin.ext_iff]
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hri hri1]
        have h1 : (r : ℕ) ≠ (i : ℕ) := Fin.ext_iff.not.1 hri
        have h2 : (r : ℕ) ≠ (i : ℕ) + 1 := fun h => hri1 (Fin.ext h)
        have hbi : basisB n r i = 0 := by
          simp only [basisB, of_apply, Fin.ext_iff]
          split_ifs <;> omega
        rw [hbi, zero_mul, sub_zero]
  · have hni : ¬ ((i : ℕ) + 1 < n) := by omega
    rw [dite_eq_right hni, Matrix.mul_apply]
    simp only [signFlipLast, of_apply, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte, basisB, CartanMatrix.B, of_apply, Fin.ext_iff]
    have _ := i.isLt
    have _ := r.isLt
    have _ := j.isLt
    split_ifs <;> omega

private theorem prod_reflStdB_eq_companion {n : ℕ} (hn : 0 < n) :
    ((List.finRange n).map (reflStdB n)).prod = companion (Pi.single ⟨0, hn⟩ (1 : ℤ)) := by
  have hm : n - 1 < n := by omega
  have hlist : List.finRange n = (List.finRange n).take (n - 1) ++ [⟨n - 1, hm⟩] := by
    have h := take_finRange_succ hm
    rwa [show n - 1 + 1 = n by omega, take_finRange_self] at h
  ext k j
  have hcol : ((List.finRange n).map (reflStdB n)).prod *ᵥ Pi.single j 1 =
      companion (Pi.single ⟨0, hn⟩ (1 : ℤ)) *ᵥ Pi.single j 1 := by
    conv_lhs => rw [hlist]
    rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      ← mulVec_mulVec]
    have hlast : reflStdB n ⟨n - 1, hm⟩ = signFlipLast n := by
      rw [reflStdB, dite_eq_right (by simp; omega)]
    rw [hlast]
    have hflip : signFlipLast n *ᵥ Pi.single j 1 =
        if (j : ℕ) + 1 = n then -Pi.single j 1 else Pi.single j 1 := by
      ext r
      rw [mulVec_single_one, col_apply, signFlipLast, of_apply]
      rcases eq_or_ne ((j : ℕ) + 1) n with hjeq | hjne <;>
        rcases eq_or_ne r j with rfl | hrj <;> simp [*]
    rw [hflip]
    have hswap : ∀ (u : ℕ) (_hu : u < n - 1) (hu1 : u + 1 < n),
        reflStdB n ⟨u, by omega⟩ = swapMatrix ⟨u, by omega⟩ ⟨u + 1, hu1⟩ := by
      intro u _ hu1
      simp [reflStdB, hu1]
    rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
    · have hjne : ¬ ((j : ℕ) + 1 = n) := by omega
      rw [ite_eq_right hjne, prod_take_swap_mulVec_single (reflStdB n) hm hswap j,
        companion_mulVec_single_of_lt _ hj]
      ext r
      simp only [swapPrefixVec, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · have hjeq : (j : ℕ) + 1 = n := by have := j.isLt; omega
      rw [ite_eq_left hjeq, mulVec_neg, prod_take_swap_mulVec_single (reflStdB n) hm hswap j,
        companion_mulVec_single_of_eq _ hjeq]
      ext r
      simp only [Pi.neg_apply, swapPrefixVec, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  simpa only [mulVec_single_one, col_apply] using congrFun hcol k

private theorem charpoly_and_orderOf_B {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly =
        (companion (Pi.single ⟨0, hn⟩ (1 : ℤ))).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.B n)) =
        orderOf (companion (Pi.single ⟨0, hn⟩ (1 : ℤ))) := by
  have hinter : basisB n * coxeterElement (CartanMatrix.B n) =
      companion (Pi.single ⟨0, hn⟩ (1 : ℤ)) * basisB n := by
    rw [coxeterElement,
      mul_list_prod_eq_of_intertwine (basisB n) _ _ (basisB_mul_reflMatrix_B n),
      prod_reflStdB_eq_companion hn]
  have hUV : (invBasisB n).map (Int.castRingHom ℚ) * (basisB n).map (Int.castRingHom ℚ) = 1 := by
    rw [← Matrix.map_mul, invBasisB_mul_basisB, Matrix.map_one _ (map_zero _) (map_one _)]
  exact charpoly_and_orderOf_eq_of_intertwine hinter hUV

/-- **The characteristic polynomial of the `Bₙ` (`0 < n`) Coxeter element is `X^n + 1`.** -/
theorem charpoly_coxeterElement_B {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 := by
  rw [(charpoly_and_orderOf_B hn).1, charpoly_companion_single_zero hn 1, map_one]

/-- **The Coxeter number of `Bₙ` (`0 < n`) is `2 n`**: the Coxeter element has order `2 n`. -/
theorem orderOf_coxeterElement_B {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  rw [(charpoly_and_orderOf_B hn).2]
  exact orderOf_companion_single_zero_one hn (by decide)

/-! ### Type `Cₙ` -/

private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun k : Fin n => if (k : ℕ) + 1 = n then 1 else 2

private theorem diagBC_mul_reflMatrix_B (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.B n) i = reflMatrix (CartanMatrix.C n) i * diagBC n := by
  ext r j
  simp only [diagBC, diagonal_mul, mul_diagonal, reflMatrix_apply, CartanMatrix.B, CartanMatrix.C,
    of_apply, Fin.ext_iff]
  have _ := i.isLt
  have _ := r.isLt
  have _ := j.isLt
  split_ifs <;> omega

private theorem charpoly_and_orderOf_C (n : ℕ) :
    (coxeterElement (CartanMatrix.B n)).charpoly =
        (coxeterElement (CartanMatrix.C n)).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.B n)) =
        orderOf (coxeterElement (CartanMatrix.C n)) := by
  have hinter : diagBC n * coxeterElement (CartanMatrix.B n) =
      coxeterElement (CartanMatrix.C n) * diagBC n :=
    mul_list_prod_eq_of_intertwine (diagBC n) _ _ (diagBC_mul_reflMatrix_B n) _
  let U : Matrix (Fin n) (Fin n) ℚ :=
    diagonal fun k : Fin n => if (k : ℕ) + 1 = n then 1 else 1 / 2
  have hUV : U * (diagBC n).map (Int.castRingHom ℚ) = 1 := by
    ext r j
    rw [diagBC, diagonal_map (map_zero _)]
    dsimp only [U]
    rw [diagonal_mul]
    rcases eq_or_ne r j with rfl | hne
    · simp only [diagonal_apply_eq, Matrix.one_apply_eq]
      split_ifs <;> norm_num
    · simp [diagonal_apply_ne _ hne, Matrix.one_apply_ne hne]
  exact charpoly_and_orderOf_eq_of_intertwine hinter hUV

/-- **The characteristic polynomial of the `Cₙ` (`0 < n`) Coxeter element is `X^n + 1`.** -/
theorem charpoly_coxeterElement_C {n : ℕ} (hn : 0 < n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 := by
  rw [← (charpoly_and_orderOf_C n).1, charpoly_coxeterElement_B hn]

/-- **The Coxeter number of `Cₙ` (`0 < n`) is `2 n`**: the Coxeter element has order `2 n`. -/
theorem orderOf_coxeterElement_C {n : ℕ} (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n := by
  rw [← (charpoly_and_orderOf_C n).2, orderOf_coxeterElement_B hn]

/-! ### Type `Dₙ` (`2 ≤ n`) -/

private def basisD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if (j : ℕ) + 1 < n then
      (if r = j then 1 else 0) - (if (r : ℕ) = (j : ℕ) + 1 then 1 else 0)
    else
      (if (r : ℕ) + 2 = n then 1 else 0) + (if (r : ℕ) + 1 = n then 1 else 0)

private def twiceInvBasisD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k i =>
    if (i : ℕ) + 1 < n then
      if (k : ℕ) + 2 < n then (if (i : ℕ) ≤ (k : ℕ) then 2 else 0) else 1
    else
      if (k : ℕ) + 2 = n then -1 else if (k : ℕ) + 1 = n then 1 else 0

private theorem twiceInvBasisD_mul_basisD {n : ℕ} (hn : 2 ≤ n) :
    twiceInvBasisD n * basisD n = (2 : ℤ) • 1 := by
  ext k j
  have hcol : (twiceInvBasisD n * basisD n) *ᵥ Pi.single j 1 =
      ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) *ᵥ Pi.single j 1 := by
    rw [← mulVec_mulVec]
    rcases lt_or_ge ((j : ℕ) + 1) n with hj | hj
    · have hv : basisD n *ᵥ Pi.single j 1 = Pi.single j 1 - Pi.single ⟨(j : ℕ) + 1, hj⟩ 1 := by
        ext r
        rw [mulVec_single_one, col_apply, basisD, of_apply, ite_eq_left hj]
        simp [Pi.single_apply, Fin.ext_iff]
      rw [hv, mulVec_sub, mulVec_single_one, mulVec_single_one, smul_mulVec, one_mulVec]
      ext r
      simp only [Pi.sub_apply, col_apply, twiceInvBasisD, of_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, Fin.ext_iff]
      have _ := j.isLt
      have _ := r.isLt
      split_ifs <;> omega
    · have hnot : ¬ ((j : ℕ) + 1 < n) := by omega
      have hv : basisD n *ᵥ Pi.single j 1 =
          Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 := by
        ext r
        rw [mulVec_single_one, col_apply, basisD, of_apply, ite_eq_right hnot]
        simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
        have _ := r.isLt
        split_ifs <;> omega
      rw [hv, mulVec_add, mulVec_single_one, mulVec_single_one, smul_mulVec, one_mulVec]
      ext r
      simp only [Pi.add_apply, col_apply, twiceInvBasisD, of_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, Fin.ext_iff]
      have _ := j.isLt
      have _ := r.isLt
      split_ifs <;> omega
  simpa only [mulVec_single_one, col_apply] using congrFun hcol k

private def negSwapLast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r c =>
    if (r : ℕ) + 2 < n then (if r = c then 1 else 0)
    else if (r : ℕ) + 2 = n then (if (c : ℕ) + 1 = n then -1 else 0)
    else if (c : ℕ) + 2 = n then -1 else 0

private def reflStdD (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : (i : ℕ) + 1 < n then swapMatrix i ⟨(i : ℕ) + 1, hi⟩ else negSwapLast n

private theorem negSwapLast_mul_apply {n : ℕ} (hn : 2 ≤ n) (V : Matrix (Fin n) (Fin n) ℤ)
    (r j : Fin n) :
    (negSwapLast n * V) r j =
      if (r : ℕ) + 2 < n then V r j
      else if (r : ℕ) + 2 = n then -V ⟨n - 1, by omega⟩ j
      else -V ⟨n - 2, by omega⟩ j := by
  rw [Matrix.mul_apply]
  rcases lt_or_ge ((r : ℕ) + 2) n with hr2 | hr2
  · rw [ite_eq_left hr2, Fintype.sum_eq_single r]
    · simp [negSwapLast, hr2]
    · intro x hx
      simp [negSwapLast, hr2, hx.symm]
  · have hnr2 : ¬ ((r : ℕ) + 2 < n) := by omega
    rw [ite_eq_right hnr2]
    rcases eq_or_ne ((r : ℕ) + 2) n with hreq | hrne
    · rw [ite_eq_left hreq, Fintype.sum_eq_single ⟨n - 1, by omega⟩]
      · have h1 : (n - 1) + 1 = n := by omega
        simp [negSwapLast, hreq, h1]
      · intro x hx
        have hne : (x : ℕ) + 1 ≠ n := by
          have := x.isLt
          intro h
          apply hx
          apply Fin.ext
          dsimp only
          omega
        simp [negSwapLast, hreq, hne]
    · rw [ite_eq_right hrne, Fintype.sum_eq_single ⟨n - 2, by omega⟩]
      · have h2 : (n - 2) + 2 = n := by omega
        simp [negSwapLast, hnr2, hrne, h2]
      · intro x hx
        have hne : (x : ℕ) + 2 ≠ n := by
          have := x.isLt
          intro h
          apply hx
          apply Fin.ext
          dsimp only
          omega
        simp [negSwapLast, hnr2, hrne, hne]

private theorem basisD_sub_succ_eq_cartanD {n : ℕ} {i : Fin n} (hi : (i : ℕ) + 1 < n)
    (j : Fin n) :
    basisD n i j - basisD n ⟨(i : ℕ) + 1, hi⟩ j = CartanMatrix.D n j i := by
  have _ := i.isLt
  have _ := j.isLt
  simp only [basisD, CartanMatrix.D, of_apply, Fin.ext_iff]
  grind

private theorem basisD_mul_reflMatrix_D {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    basisD n * reflMatrix (CartanMatrix.D n) i = reflStdD n i * basisD n := by
  ext r j
  rw [mul_reflMatrix_apply, reflStdD]
  have _ := i.isLt
  have _ := r.isLt
  have _ := j.isLt
  rcases lt_or_ge ((i : ℕ) + 1) n with hi | hi
  · rw [dite_eq_left hi, swapMatrix_mul_apply]
    rcases eq_or_ne r i with rfl | hri
    · rw [Equiv.swap_apply_left]
      have hbi : basisD n r r = 1 := by simp [basisD, hi]
      rw [hbi, one_mul, ← basisD_sub_succ_eq_cartanD hi j]
      ring
    · rcases eq_or_ne r ⟨(i : ℕ) + 1, hi⟩ with hreq | hri1
      · rw [hreq, Equiv.swap_apply_right]
        have hbi : basisD n ⟨(i : ℕ) + 1, hi⟩ i = -1 := by
          simp only [basisD, of_apply, ite_eq_left hi, Fin.ext_iff]; grind
        rw [hbi, ← basisD_sub_succ_eq_cartanD hi j]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hri hri1]
        have h1 : (r : ℕ) ≠ (i : ℕ) := Fin.ext_iff.not.1 hri
        have h2 : (r : ℕ) ≠ (i : ℕ) + 1 := fun h => hri1 (Fin.ext h)
        have hbi : basisD n r i = 0 := by
          simp only [basisD, of_apply, ite_eq_left hi, Fin.ext_iff]; grind
        rw [hbi, zero_mul, sub_zero]
  · have hni : ¬ ((i : ℕ) + 1 < n) := by omega
    rw [dite_eq_right hni, negSwapLast_mul_apply hn]
    rcases lt_or_ge ((r : ℕ) + 2) n with hr2 | hr2
    · rw [ite_eq_left hr2]
      have hbi : basisD n r i = 0 := by
        simp only [basisD, of_apply, ite_eq_right hni]; grind
      rw [hbi, zero_mul, sub_zero]
    · have hnr2 : ¬ ((r : ℕ) + 2 < n) := by omega
      rw [ite_eq_right hnr2]
      have hbi : basisD n r i = 1 := by
        simp only [basisD, of_apply, ite_eq_right hni]; grind
      rw [hbi, one_mul]
      rcases eq_or_ne ((r : ℕ) + 2) n with hreq | hrne
      · rw [ite_eq_left hreq]
        by_cases hj : (j : ℕ) + 1 < n <;>
          simp only [basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte, Fin.ext_iff] <;> grind
      · rw [ite_eq_right hrne]
        by_cases hj : (j : ℕ) + 1 < n <;>
          simp only [basisD, CartanMatrix.D, of_apply, hj, ↓reduceIte, Fin.ext_iff] <;> grind

private abbrev splitEquivD {n : ℕ} (hn : 2 ≤ n) : Fin (n - 1) ⊕ Fin 1 ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem splitEquivD_symm_of_lt {n : ℕ} (hn : 2 ≤ n) (x : Fin n) (hx : (x : ℕ) < n - 1) :
    (splitEquivD hn).symm x = Sum.inl ⟨(x : ℕ), hx⟩ := by
  apply (splitEquivD hn).injective
  simp [splitEquivD, finSumFinEquiv_apply_left]

private theorem splitEquivD_symm_of_ge {n : ℕ} (hn : 2 ≤ n) (x : Fin n) (hx : n - 1 ≤ (x : ℕ)) :
    (splitEquivD hn).symm x = Sum.inr ⟨0, by omega⟩ := by
  apply (splitEquivD hn).injective
  have _ := x.isLt
  ext
  simp [splitEquivD, finSumFinEquiv_apply_right]
  omega

private def modelD {n : ℕ} (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  reindex (splitEquivD hn) (splitEquivD hn)
    (fromBlocks (companion (Pi.single ⟨0, by omega⟩ (1 : ℤ))) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

private theorem prod_reflStdD_eq_modelD {n : ℕ} (hn : 2 ≤ n) :
    ((List.finRange n).map (reflStdD n)).prod = modelD hn := by
  have hm2 : n - 2 < n := by omega
  have hm1 : n - 1 < n := by omega
  have hlist : List.finRange n =
      (List.finRange n).take (n - 2) ++ [⟨n - 2, hm2⟩, ⟨n - 1, hm1⟩] := by
    have h1 := take_finRange_succ hm1
    rw [show n - 1 + 1 = n by omega, take_finRange_self] at h1
    have h2 := take_finRange_succ hm2
    rw [show n - 2 + 1 = n - 1 by omega] at h2
    calc List.finRange n = (List.finRange n).take (n - 1) ++ [⟨n - 1, hm1⟩] := h1
      _ = ((List.finRange n).take (n - 2) ++ [⟨n - 2, hm2⟩]) ++ [⟨n - 1, hm1⟩] := by rw [h2]
      _ = (List.finRange n).take (n - 2) ++ [⟨n - 2, hm2⟩, ⟨n - 1, hm1⟩] := by simp
  ext k j
  have hcol : ((List.finRange n).map (reflStdD n)).prod *ᵥ Pi.single j 1 =
      modelD hn *ᵥ Pi.single j 1 := by
    conv_lhs => rw [hlist]
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    have hpen : reflStdD n ⟨n - 2, hm2⟩ = swapMatrix ⟨n - 2, hm2⟩ ⟨n - 1, hm1⟩ := by
      have hlt : (n - 2) + 1 < n := by omega
      have hidx : (⟨(n - 2) + 1, hlt⟩ : Fin n) = ⟨n - 1, hm1⟩ := Fin.ext (by dsimp; omega)
      simp [reflStdD, hlt, hidx]
    have hlast : reflStdD n ⟨n - 1, hm1⟩ = negSwapLast n := by
      rw [reflStdD, dite_eq_right (by simp; omega)]
    rw [hpen, hlast]
    have htail : swapMatrix ⟨n - 2, hm2⟩ ⟨n - 1, hm1⟩ *ᵥ (negSwapLast n *ᵥ Pi.single j 1) =
        if (j : ℕ) < n - 2 then Pi.single j 1 else -Pi.single j 1 := by
      rw [mulVec_mulVec, mulVec_single_one]
      ext r
      rw [col_apply, swapMatrix_mul_apply]
      have _ := j.isLt
      have _ := r.isLt
      rcases eq_or_ne r ⟨n - 2, hm2⟩ with rfl | hr2
      · rw [Equiv.swap_apply_left]
        rcases lt_or_ge (j : ℕ) (n - 2) with hj2 | hj2
        · rw [ite_eq_left hj2, Pi.single_apply]
          simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
        · rw [ite_eq_right (by omega), Pi.neg_apply, Pi.single_apply]
          simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
      · rcases eq_or_ne r ⟨n - 1, hm1⟩ with rfl | hr1
        · rw [Equiv.swap_apply_right]
          rcases lt_or_ge (j : ℕ) (n - 2) with hj2 | hj2
          · rw [ite_eq_left hj2, Pi.single_apply]
            simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
          · rw [ite_eq_right (by omega), Pi.neg_apply, Pi.single_apply]
            simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
        · rw [Equiv.swap_apply_of_ne_of_ne hr2 hr1]
          have _ : (r : ℕ) ≠ n - 2 := fun h => hr2 (Fin.ext h)
          have _ : (r : ℕ) ≠ n - 1 := fun h => hr1 (Fin.ext h)
          rcases lt_or_ge (j : ℕ) (n - 2) with hj2 | hj2
          · rw [ite_eq_left hj2, Pi.single_apply]
            simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
          · rw [ite_eq_right (by omega), Pi.neg_apply, Pi.single_apply]
            simp only [negSwapLast, of_apply, Fin.ext_iff]; grind
    rw [htail]
    have hswap : ∀ (u : ℕ) (_hu : u < n - 2) (hu1 : u + 1 < n),
        reflStdD n ⟨u, by omega⟩ = swapMatrix ⟨u, by omega⟩ ⟨u + 1, hu1⟩ := by
      intro u _ hu1
      simp [reflStdD, hu1]
    rcases lt_or_ge (j : ℕ) (n - 2) with hj | hj
    · rw [ite_eq_left hj, prod_take_swap_mulVec_single (reflStdD n) hm2 hswap j,
        mulVec_single_one]
      ext r
      rw [col_apply]
      simp only [swapPrefixVec, modelD, reindex_apply, submatrix_apply]
      rw [splitEquivD_symm_of_lt hn j (by omega)]
      rcases lt_or_ge (r : ℕ) (n - 1) with hr | hr
      · rw [splitEquivD_symm_of_lt hn r hr]
        simp only [fromBlocks_apply₁₁, companion_apply, Pi.single_apply, Fin.ext_iff]; grind
      · rw [splitEquivD_symm_of_ge hn r hr]
        have _ := r.isLt
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, Fin.ext_iff]; grind
    · rw [ite_eq_right (by omega), mulVec_neg,
        prod_take_swap_mulVec_single (reflStdD n) hm2 hswap j, mulVec_single_one]
      ext r
      rw [col_apply]
      simp only [Pi.neg_apply, swapPrefixVec, modelD, reindex_apply, submatrix_apply]
      rcases lt_or_ge (j : ℕ) (n - 1) with hj1 | hj1
      · rw [splitEquivD_symm_of_lt hn j hj1]
        rcases lt_or_ge (r : ℕ) (n - 1) with hr | hr
        · rw [splitEquivD_symm_of_lt hn r hr]
          simp only [fromBlocks_apply₁₁, companion_apply, Pi.single_apply, Fin.ext_iff]; grind
        · rw [splitEquivD_symm_of_ge hn r hr]
          have _ := r.isLt
          simp only [fromBlocks_apply₂₁, Matrix.zero_apply, Fin.ext_iff]; grind
      · rw [splitEquivD_symm_of_ge hn j hj1]
        have _ := j.isLt
        rcases lt_or_ge (r : ℕ) (n - 1) with hr | hr
        · rw [splitEquivD_symm_of_lt hn r hr]
          simp only [fromBlocks_apply₁₂, Matrix.zero_apply, Fin.ext_iff]; grind
        · rw [splitEquivD_symm_of_ge hn r hr]
          have _ := r.isLt
          simp only [fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Fin.ext_iff]; grind
  simpa only [mulVec_single_one, col_apply] using congrFun hcol k

private theorem charpoly_and_orderOf_D {n : ℕ} (hn : 2 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (modelD hn).charpoly ∧
      orderOf (coxeterElement (CartanMatrix.D n)) = orderOf (modelD hn) := by
  have hinter : basisD n * coxeterElement (CartanMatrix.D n) = modelD hn * basisD n := by
    rw [coxeterElement,
      mul_list_prod_eq_of_intertwine (basisD n) _ _ (basisD_mul_reflMatrix_D hn),
      prod_reflStdD_eq_modelD hn]
  let φ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℚ :=
    (Int.castRingHom ℚ).mapMatrix
  let U : Matrix (Fin n) (Fin n) ℚ := (1 / 2 : ℚ) • φ (twiceInvBasisD n)
  have hUV : U * (basisD n).map (Int.castRingHom ℚ) = 1 := by
    change ((1 / 2 : ℚ) • φ (twiceInvBasisD n)) * φ (basisD n) = 1
    rw [smul_mul_assoc, ← map_mul, twiceInvBasisD_mul_basisD hn]
    ext r j
    change (1 / 2 : ℚ) * (Int.castRingHom ℚ (((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) r j)) =
      (1 : Matrix (Fin n) (Fin n) ℚ) r j
    rw [Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    rcases eq_or_ne r j with rfl | hne
    · simp
    · simp [hne]
  exact charpoly_and_orderOf_eq_of_intertwine hinter hUV

/-- **The characteristic polynomial of the `Dₙ` (`2 ≤ n`) Coxeter element is
`(X^{n-1} + 1)(X + 1)`.** -/
theorem charpoly_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  rw [(charpoly_and_orderOf_D hn).1, modelD, charpoly_reindex, charpoly_fromBlocks_zero₁₂,
    charpoly_companion_single_zero (by omega) 1, map_one]
  congr 1
  rw [Matrix.charpoly, det_fin_one]
  simp [charmatrix]

/-- **The Coxeter number of `Dₙ` (`2 ≤ n`) is `2 n - 2`**: the Coxeter element has order
`2 n - 2`. -/
theorem orderOf_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.D n)) = 2 * n - 2 := by
  rw [(charpoly_and_orderOf_D hn).2]
  let C₁ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ := companion (Pi.single ⟨0, by omega⟩ (1 : ℤ))
  let D₁ : Matrix (Fin 1) (Fin 1) ℤ := -1
  have hmodel :
      modelD hn = (reindexAlgEquiv ℤ ℤ (splitEquivD hn)).toMulEquiv (fromBlocks C₁ 0 0 D₁) := rfl
  rw [hmodel, MulEquiv.orderOf_eq]
  have hordC : orderOf C₁ = 2 * (n - 1) :=
    orderOf_companion_single_zero_one (by omega) (by decide)
  rw [show 2 * n - 2 = 2 * (n - 1) by omega]
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun m hmlt hm0 hpow => ?_⟩
  · rw [fromBlocks_diagonal_pow,
      show C₁ ^ (2 * (n - 1)) = 1 by rw [← hordC, pow_orderOf_eq_one],
      show D₁ ^ (2 * (n - 1)) = 1 by simp [D₁, pow_mul], fromBlocks_one]
  · rw [fromBlocks_diagonal_pow] at hpow
    have hCpow : C₁ ^ m = 1 := by
      ext i j
      simpa only [fromBlocks_apply₁₁, Matrix.one_apply, Sum.inl.injEq] using
        congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hpow
    have hdvd : orderOf C₁ ∣ m := orderOf_dvd_iff_pow_eq_one.2 hCpow
    rw [hordC] at hdvd
    exact absurd (Nat.le_of_dvd hm0 hdvd) (by omega)

end TauCeti.Coxeter

end
