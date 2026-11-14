/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B

/-!
# The Coxeter element of type `Dₙ` has order `2n - 2`

Mathlib's `Dₙ` (`n = m + 3`) has the chain `0 - 1 - ⋯ - (n-3)` and the fork `n-3 - n-2`,
`n-3 - n-1`. In the `ε`-model `αᵢ = εᵢ - εᵢ₊₁` for `i ≤ n - 2` and `α_{n-1} = ε_{n-2} + ε_{n-1}`
(`TauCeti.Coxeter.epsD`, injective but of determinant `2`). The reflections become the
transpositions `(i i+1)` and the signed swap `ε_{n-2} ↦ -ε_{n-1}`, `ε_{n-1} ↦ -ε_{n-2}`; the Coxeter
element is the negacyclic shift of the first `n - 1` coordinates times `-1` on the last, of order
`2n - 2`.
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {m : ℕ}

/-- The `ε`-coordinates of the simple roots of type `D_{m+3}`. -/
@[expose] def epsD (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun a i =>
    if i.val < m + 2 then (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)
    else (if a.val = m + 1 then 1 else 0) + (if a.val = m + 2 then 1 else 0)

/-- The signed swap `ε_{m+1} ↦ -ε_{m+2}`, `ε_{m+2} ↦ -ε_{m+1}`. -/
@[expose] def flipPair (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun a b =>
    if a.val = m + 1 ∧ b.val = m + 2 then -1 else if a.val = m + 2 ∧ b.val = m + 1 then -1
    else if a = b ∧ a.val < m + 1 then 1 else 0

theorem flipPair_mul_apply {k : Type*} (M : Matrix (Fin (m + 3)) k ℤ) (a : Fin (m + 3)) (j : k) :
    (flipPair m * M) a j =
      if a.val = m + 1 then -M (Fin.last (m + 2)) j
      else if a.val = m + 2 then -M ⟨m + 1, by omega⟩ j else M a j := by
  rw [Matrix.mul_apply]
  by_cases h1 : a.val = m + 1
  · rw [Finset.sum_eq_single (Fin.last (m + 2))]
    · simp [flipPair, h1]
    · intro c _ hc
      have : c.val ≠ m + 2 := fun h => hc (Fin.ext h)
      simp only [flipPair, Matrix.of_apply]
      split_ifs <;> simp_all
      omega
    · simp
  · by_cases h2 : a.val = m + 2
    · rw [Finset.sum_eq_single ⟨m + 1, by omega⟩]
      · simp [flipPair, h2]
      · intro c _ hc
        have : c.val ≠ m + 1 := fun h => hc (Fin.ext h)
        simp only [flipPair, Matrix.of_apply]
        split_ifs <;> simp_all
        omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp only [flipPair, Matrix.of_apply, h1, h2, false_and, ite_false, true_and]
        rw [ite_eq_left (by omega), one_mul]
      · intro c _ hc
        simp only [flipPair, Matrix.of_apply]
        split_ifs <;> simp_all
      · simp


/-- The fork reflection `s_{n-1}` of type `Dₙ` is the signed swap of the last two coordinates. -/
theorem epsD_mul_reflMatrix_last (i : Fin (m + 3)) (hi : i.val = m + 2) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i = flipPair m * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, flipPair_mul_apply]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  simp only [epsD, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last, hi, h2,
    ite_false, lt_irrefl, or_true, and_true]
  split_ifs <;> omega

private theorem epsD_mul_reflMatrix_chain (i : Fin (m + 3)) (hi : i.val < m) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : i.val + 2 < m + 3 := by omega
  have h4 : ¬ (i.val + 3 = m + 3) := by omega
  have h5 : ¬ (i.val + 2 = m + 3 ∨ i.val + 1 = m + 3) := by omega
  have h6 : i.val < m + 2 := by omega
  simp only [epsD, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, h2, h3,
    h4, h5, h6, ite_false, and_true, and_false, false_and]
  split_ifs <;> (try simp only at *) <;> omega

private theorem epsD_mul_reflMatrix_branch (i : Fin (m + 3)) (hi : i.val = m) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : m + 2 < m + 3 := by omega
  have h5 : ¬ (m + 2 = m + 3 ∨ m + 1 = m + 3) := by omega
  have h6 : m < m + 2 := by omega
  simp only [epsD, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, hi, h2, h3,
    h5, h6, ite_false, ite_true, and_true, and_false, true_and]
  split_ifs <;> (try simp only [not_true_eq_false] at *) <;>
    omega

private theorem epsD_mul_reflMatrix_pre (i : Fin (m + 3)) (hi : i.val = m + 1) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : ¬ (m + 1 + 2 < m + 3) := by omega
  have h4 : ¬ (m + 1 + 3 = m + 3) := by omega
  have h6 : m + 1 < m + 2 := by omega
  simp only [epsD, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, hi, h2, h3,
    h4, h6, ite_false, ite_true, and_false, false_and]
  split_ifs <;> (try simp only [not_true_eq_false, and_true, true_or] at *) <;>
    omega

/-- The simple reflections `s₀, …, s_{n-2}` of type `Dₙ` are transpositions in the `ε`-model. -/
theorem epsD_mul_reflMatrix_of_lt (i : Fin (m + 3)) (hi : i.val < m + 2) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  rcases Nat.lt_or_ge i.val m with h | h
  · exact epsD_mul_reflMatrix_chain i h
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact epsD_mul_reflMatrix_branch i h'.symm
    · exact epsD_mul_reflMatrix_pre i (by omega)

/-- The Coxeter element of type `D_{m+3}` in the `ε`-model: the negacyclic shift of the first
`m + 2` coordinates, and `-1` on the last. -/
@[expose] def negaD (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun a b =>
    if b.val < m + 1 ∧ a.val = b.val + 1 then 1 else if b.val = m + 1 ∧ a.val = 0 then -1
    else if b.val = m + 2 ∧ a.val = m + 2 then -1 else 0

theorem epsD_mul_coxeterElement :
    epsD m * coxeterElement (CartanMatrix.D (m + 3)) = negaD m * epsD m := by
  have hlist : ∀ l : List (Fin (m + 2)), epsD m *
      (l.map (reflMatrix (CartanMatrix.D (m + 3)) ∘ Fin.castSucc)).prod =
      permMatrixHom (R := ℤ) (l.map adjSwap).prod * epsD m := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Function.comp_apply,
        epsD_mul_reflMatrix_of_lt i.castSucc (by simp), Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
        List.map_cons, List.prod_cons, map_mul]
      rfl
  rw [coxeterElement, List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    ← Matrix.mul_assoc, hlist, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.mul_assoc, epsD_mul_reflMatrix_last _ (by simp), ← Matrix.mul_assoc,
    prod_adjSwap_eq_finRotate]
  congr 1
  ext a b
  rw [permMatrixHom_mul_apply]
  obtain ⟨x, rfl⟩ := (finRotate (m + 3)).surjective a
  have hval : (finRotate (m + 3) x).val = (x.val + 1) % (m + 3) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one]
  rw [Equiv.symm_apply_apply]
  simp only [flipPair, negaD, Matrix.of_apply, Fin.ext_iff]
  rw [hval]
  by_cases hx : x.val + 1 < m + 3
  · have hm := Nat.mod_eq_of_lt hx
    split_ifs <;> omega
  · have hx' : x.val + 1 = m + 3 := by omega
    have hm : (x.val + 1) % (m + 3) = 0 := by rw [hx', Nat.mod_self]
    split_ifs <;> omega

/-- Closed form of `negaD m ^ k` for `k ≤ m + 2`. -/
theorem negaD_pow {k : ℕ} (hk : k ≤ m + 2) (a b : Fin (m + 3)) :
    (negaD m ^ k) a b =
      if a.val < m + 2 ∧ b.val < m + 2 then
        (if a.val = b.val + k then 1 else if a.val + (m + 2) = b.val + k then -1 else 0)
      else if a.val = m + 2 ∧ b.val = m + 2 then (if k % 2 = 0 then 1 else -1) else 0 := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, add_zero, Nat.zero_mod]
    split_ifs <;> omega
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases ha0 : a.val = 0
    · rw [Finset.sum_eq_single ⟨m + 1, by omega⟩]
      · rw [ih (by omega)]
        simp only [negaD, Matrix.of_apply]
        split_ifs <;> (try simp only [true_and] at *) <;> omega
      · intro c _ hc
        have hc' : c.val ≠ m + 1 := fun h => hc (Fin.ext h)
        simp only [negaD, Matrix.of_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp
    · by_cases ha2 : a.val = m + 2
      · rw [Finset.sum_eq_single ⟨m + 2, by omega⟩]
        · rw [ih (by omega)]
          simp only [negaD, Matrix.of_apply]
          split_ifs <;> (try simp only [true_and] at *) <;> omega
        · intro c _ hc
          have hc' : c.val ≠ m + 2 := fun h => hc (Fin.ext h)
          simp only [negaD, Matrix.of_apply]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
        · simp
      · rw [Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
        · rw [ih (by omega)]
          simp only [negaD, Matrix.of_apply]
          split_ifs <;> omega
        · intro c _ hc
          have hc' : c.val ≠ a.val - 1 := fun h => hc (Fin.ext h)
          simp only [negaD, Matrix.of_apply]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
        · simp

/-- **The `Dₙ` Coxeter matrix `negaD` has order `2n - 2`.** -/
theorem orderOf_negaD : orderOf (negaD m) = 2 * (m + 2) := by
  have hzero : ∀ a c : Fin (m + 3), c ≠ a → (negaD m ^ (m + 2)) a c = 0 := by
    intro a c hc
    have hca : c.val ≠ a.val := fun h => hc (Fin.ext h)
    rw [negaD_pow le_rfl]
    split_ifs <;> omega
  rw [orderOf_eq_iff (by omega)]
  refine ⟨?_, fun k hk hk0 h => ?_⟩
  · ext a b
    rw [two_mul, pow_add, Matrix.mul_apply,
      Finset.sum_eq_single a (fun c _ hc => by rw [hzero a c hc, zero_mul]) (by simp),
      negaD_pow le_rfl, negaD_pow le_rfl]
    simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> omega
  · by_cases hkp : k < m + 2
    · have := congrFun (congrFun h ⟨k, by omega⟩) 0
      rw [negaD_pow hkp.le] at this
      simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
      split_ifs at this <;> omega
    · by_cases hkp' : k = m + 2
      · subst hkp'
        have := congrFun (congrFun h 0) 0
        rw [negaD_pow le_rfl] at this
        simp only [Fin.val_zero, Matrix.one_apply] at this
        split_ifs at this <;> omega
      · obtain ⟨j, rfl⟩ : ∃ j, k = (m + 2) + j := ⟨k - (m + 2), by omega⟩
        have := congrFun (congrFun h ⟨j, by omega⟩) 0
        rw [pow_add, Matrix.mul_apply,
          Finset.sum_eq_single ⟨j, by omega⟩
            (fun c _ hc => by rw [hzero _ c hc, zero_mul]) (by simp),
          negaD_pow le_rfl, negaD_pow (by omega)] at this
        simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
        split_ifs at this <;> omega

theorem epsD_mul_apply {k : Type*} (Z : Matrix (Fin (m + 3)) k ℤ) (a : Fin (m + 3)) (j : k) :
    (epsD m * Z) a j =
      (if a.val < m + 2 then Z a j else 0) -
        (if h : 1 ≤ a.val then Z ⟨a.val - 1, by omega⟩ j else 0) +
        (if a.val = m + 1 ∨ a.val = m + 2 then Z (Fin.last (m + 2)) j else 0) := by
  have hsplit : ∀ c, epsD m a c * Z c j =
      (if c = a then (if a.val < m + 2 then Z c j else 0) else 0) -
        (if a.val = c.val + 1 ∧ c.val < m + 2 then Z c j else 0) +
        (if c = Fin.last (m + 2) then (if a.val = m + 1 ∨ a.val = m + 2 then Z c j else 0)
          else 0) := by
    intro c
    simp only [epsD, Matrix.of_apply, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 2
  by_cases ha : 1 ≤ a.val
  · rw [dite_eq_left ha, Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
    · intro c _ hc
      exact ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simp; omega)) hc
    · simp
  · rw [dite_eq_right ha]
    exact Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 fun h => absurd h.1 (by omega)

theorem mul_epsD_apply {k : Type*} (Z : Matrix k (Fin (m + 3)) ℤ) (r : k) (i : Fin (m + 3)) :
    (Z * epsD m) r i =
      if h : i.val < m + 2 then Z r i - Z r ⟨i.val + 1, by omega⟩
      else Z r ⟨m + 1, by omega⟩ + Z r (Fin.last (m + 2)) := by
  rw [Matrix.mul_apply]
  by_cases hi : i.val < m + 2
  · rw [dite_eq_left hi]
    have : ∀ c, Z r c * epsD m c i =
        (if c = i then Z r c else 0) - (if c = ⟨i.val + 1, by omega⟩ then Z r c else 0) := by
      intro c
      simp only [epsD, Matrix.of_apply, hi, ite_true, Fin.ext_iff]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  · rw [dite_eq_right hi]
    have : ∀ c, Z r c * epsD m c i =
        (if c = ⟨m + 1, by omega⟩ then Z r c else 0) +
          (if c = Fin.last (m + 2) then Z r c else 0) := by
      intro c
      simp only [epsD, Matrix.of_apply, hi, ite_false, Fin.ext_iff, Fin.val_last]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp

/-- `epsD` is injective on the left (it has determinant `2` and `ℤ` is torsion-free). -/
theorem epsD_mul_left_cancel {X Y : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ}
    (h : epsD m * X = epsD m * Y) : X = Y := by
  have hZ : epsD m * (X - Y) = 0 := by rw [Matrix.mul_sub, h, sub_self]
  rw [← sub_eq_zero]
  ext c j
  let v : ℕ → ℤ := fun t => if ht : t < m + 3 then (X - Y) ⟨t, ht⟩ j else 0
  have hv : ∀ c : Fin (m + 3), (X - Y) c j = v c.val := fun c => by simp [v, c.isLt]
  have row : ∀ t, t < m + 3 →
      (if t < m + 2 then v t else 0) - (if 1 ≤ t then v (t - 1) else 0) +
        (if t = m + 1 ∨ t = m + 2 then v (m + 2) else 0) = 0 := by
    intro t ht
    have := congrFun (congrFun hZ ⟨t, ht⟩) j
    rw [epsD_mul_apply] at this
    simpa [hv] using this
  have chain : ∀ t ≤ m, v t = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      have := row 0 (by omega)
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at this
      omega
    | succ t ih =>
      intro ht
      have := row (t + 1) (by omega)
      have := ih (by omega)
      simp only [Nat.add_sub_cancel] at *
      split_ifs at * <;> omega
  have h1 := row (m + 1) (by omega)
  have h2 := row (m + 2) (by omega)
  have hm := chain m le_rfl
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (Or.inl rfl)] at h1
  rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (Or.inr rfl)] at h2
  have hm1 : m + 2 - 1 = m + 1 := rfl
  simp only [Nat.add_sub_cancel, hm1] at h1 h2
  rw [Matrix.zero_apply, hv]
  have hc := c.isLt
  by_cases hcm : c.val ≤ m
  · exact chain _ hcm
  · obtain hh | hh : c.val = m + 1 ∨ c.val = m + 2 := by omega
    all_goals rw [hh]; omega

/-- `epsD` is injective on the right. -/
theorem epsD_mul_right_cancel {X Y : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ}
    (h : X * epsD m = Y * epsD m) : X = Y := by
  have hZ : (X - Y) * epsD m = 0 := by rw [Matrix.sub_mul, h, sub_self]
  rw [← sub_eq_zero]
  ext r c
  let u : ℕ → ℤ := fun t => if ht : t < m + 3 then (X - Y) r ⟨t, ht⟩ else 0
  have hu : ∀ c : Fin (m + 3), (X - Y) r c = u c.val := fun c => by simp [u, c.isLt]
  have col : ∀ t < m + 2, u t - u (t + 1) = 0 := by
    intro t ht
    have := congrFun (congrFun hZ r) ⟨t, by omega⟩
    rw [mul_epsD_apply, dite_eq_left ht] at this
    simpa [hu] using this
  have colLast : u (m + 1) + u (m + 2) = 0 := by
    have := congrFun (congrFun hZ r) (Fin.last (m + 2))
    rw [mul_epsD_apply, dite_eq_right (by simp)] at this
    simpa [hu] using this
  have hconst : ∀ t ≤ m + 2, u t = u 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih => intro ht; have := col t (by omega); have := ih (by omega); omega
  have h0 : u 0 = 0 := by
    have := hconst (m + 1) (by omega)
    have := hconst (m + 2) le_rfl
    omega
  rw [Matrix.zero_apply, hu, hconst _ (by omega), h0]

/-- **The Coxeter element of type `Dₙ` has order `2n - 2`** (`n = m + 3`). -/
theorem orderOf_coxeterElement_D (m : ℕ) :
    orderOf (coxeterElement (CartanMatrix.D (m + 3))) = 2 * (m + 2) := by
  rw [← orderOf_negaD, orderOf_eq_orderOf_of_mul_eq_mul epsD_mul_coxeterElement
    (fun k h => epsD_mul_left_cancel (h.trans (Matrix.mul_one _).symm))
    (fun k h => epsD_mul_right_cancel (h.trans (Matrix.one_mul _).symm))]

/-- The order `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Dₙ`
(`n = m + 3`): the fork node `n - 1` has the single earlier neighbour `n - 3`. -/
theorem isOneDegenerateOrder_D (m : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin (m + 3) => CartanMatrix.D (m + 3) i j ≠ 0)
      (List.finRange (m + 3)) := by
  refine List.isOneDegenerateOrder_iff.2 fun S₁ z S₂ hS x hx y hy hzx hzy => ?_
  have hlt := (List.pairwise_append.1 (hS ▸ List.pairwise_lt_finRange (m + 3))).2.2
  have key : ∀ w : Fin (m + 3), w ∈ S₁ → CartanMatrix.D (m + 3) z w ≠ 0 →
      (z.val ≤ m + 1 ∧ w.val + 1 = z.val) ∨ (z.val = m + 2 ∧ w.val = m) := by
    intro w hw h
    have hwz : w.val < z.val := hlt w hw z List.mem_cons_self
    simp only [CartanMatrix.D, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ h₅ h₆ <;> first | exact absurd rfl h | (subst h₁; omega) | omega
  rcases key x hx hzx with h | h <;> rcases key y hy hzy with h' | h' <;> ext <;> omega

end TauCeti.Coxeter

end
