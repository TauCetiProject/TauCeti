/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg

/-!
# Adjacent root strings in a minuscule weight table

An adjacent pair of simple roots acts in strings of length at most two. The
resulting matrix commutator has a primitive entry, and its support is disjoint
from the supports of the two simple-root matrices, over every commutative ring.
-/

public section

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

/-- Negating every weight interchanges the raising and lowering actions. -/
def negWeights : MinusculeWeightTable B ι where
  cartanMatrix := T.cartanMatrix
  weight a := -T.weight a
  reflection := T.reflection
  cartanMatrix_diag := T.cartanMatrix_diag
  cartanMatrix_offDiag_nonpos := T.cartanMatrix_offDiag_nonpos
  cartanMatrix_zero_comm := T.cartanMatrix_zero_comm
  weight_eq_neg_one_or_eq_zero_or_eq_one a i := by
    rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
    · exact Or.inr (Or.inr (by simpa using congrArg Neg.neg h))
    · exact Or.inr (Or.inl (by simpa using congrArg Neg.neg h))
    · exact Or.inl (by simpa using congrArg Neg.neg h)
  weight_reflection i a j := by
    dsimp
    rw [T.weight_reflection]
    ring
  weight_injective := fun a b h ↦ T.weight_injective (neg_injective h)

/-- Weight negation preserves the Cartan matrix. -/
@[simp]
theorem negWeights_cartanMatrix : T.negWeights.cartanMatrix = T.cartanMatrix := by rfl

/-- The weights of the negated table are the negatives of the original weights. -/
@[simp]
theorem negWeights_weight (a : ι) : T.negWeights.weight a = -T.weight a := by rfl

variable [DecidableEq ι]

/-- Raising for the negated table is lowering for the original table. -/
@[simp]
theorem negWeights_raisingMatrix (i : B) : T.negWeights.raisingMatrix i = T.loweringMatrix i := by
  ext a b
  simp [negWeights, neg_eq_iff_eq_neg]

variable [Fintype ι] {R : Type*} [CommRing R]

private theorem mul_raisingMatrix_map_apply (i : B) (M : Matrix ι ι R) (a b : ι) :
    (M * (T.raisingMatrix i).map (Int.cast : ℤ → R)) a b =
      if T.weight b i = -1 then M a (T.reflection i b) else 0 := by
  by_cases hb : T.weight b i = -1
  all_goals simp [Matrix.mul_apply, hb]

/-- An alternating triple of adjacent raising operators vanishes integrally. -/
theorem raisingMatrix_mul_raisingMatrix_mul_of_adjacent (i j : B)
    (hij : T.cartanMatrix i j = -1) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) *
        (T.raisingMatrix j).map (Int.cast : ℤ → R) *
          (T.raisingMatrix i).map (Int.cast : ℤ → R) = 0 := by
  ext a b
  rw [T.mul_raisingMatrix_map_apply, T.mul_raisingMatrix_map_apply]
  by_cases hi : T.weight b i = -1
  · by_cases hj : T.weight (T.reflection i b) j = -1
    · have hlast : T.weight (T.reflection j (T.reflection i b)) i ≠ -1 := by
        rw [T.weight_reflection, T.weight_reflection_self, hi, hj, hij]
        norm_num
      simp [hi, hj, hlast]
    · simp [hi, hj]
  · simp [hi]

omit [Fintype ι] [DecidableEq ι] in
/-- A negative coordinate at one end of an edge supplies a two-step raising string. -/
theorem exists_adjacent_raising_string (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    (hi : ∃ a, T.weight a i = -1) :
    ∃ a, (T.weight a i = -1 ∧ T.weight a j = 0) ∨
      (T.weight a i = 0 ∧ T.weight a j = -1) := by
  obtain ⟨a, ha⟩ := hi
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a j with hj | hj | hj
  · have h := T.weight_eq_neg_one_or_eq_zero_or_eq_one (T.reflection i a) j
    rw [T.weight_reflection, ha, hj, hji] at h
    omega
  · exact ⟨a, Or.inl ⟨ha, hj⟩⟩
  · refine ⟨T.reflection j a, Or.inr ⟨?_, ?_⟩⟩
    · rw [T.weight_reflection, ha, hj, hij]
      norm_num
    · simp [hj]

private theorem raisingMatrix_map_mul_self (i : B) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix i).map (Int.cast : ℤ → R) = 0 := by
  ext a b
  have h := congrArg (Int.cast : ℤ → R) (congrFun (congrFun (T.raisingMatrix_pow_two i) a) b)
  simpa [pow_two, Matrix.mul_apply] using h

/-- The matrix of the edge commutator, with the ordered-pair sign convention. -/
def raisingCommutatorMatrix (i j : B) : Matrix ι ι R :=
  (T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix j).map (Int.cast : ℤ → R) -
    (T.raisingMatrix j).map (Int.cast : ℤ → R) *
      (T.raisingMatrix i).map (Int.cast : ℤ → R)

/-- The ordered matrix difference defining the edge commutator. -/
theorem raisingCommutatorMatrix_eq (i j : B) :
    T.raisingCommutatorMatrix (R := R) i j =
      (T.raisingMatrix i).map Int.cast * (T.raisingMatrix j).map Int.cast -
        (T.raisingMatrix j).map Int.cast * (T.raisingMatrix i).map Int.cast := by rfl

/-- The adjacent commutator matrix annihilates both simple-root actions on either side. -/
theorem raisingCommutatorMatrix_annihilates (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) * T.raisingCommutatorMatrix i j = 0 ∧
    T.raisingCommutatorMatrix i j * (T.raisingMatrix i).map (Int.cast : ℤ → R) = 0 ∧
    (T.raisingMatrix j).map (Int.cast : ℤ → R) * T.raisingCommutatorMatrix i j = 0 ∧
    T.raisingCommutatorMatrix i j * (T.raisingMatrix j).map (Int.cast : ℤ → R) = 0 := by
  have hi := T.raisingMatrix_map_mul_self (R := R) i
  have hj := T.raisingMatrix_map_mul_self (R := R) j
  have hA := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) i j hij
  have hB := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) j i hji
  simp only [raisingCommutatorMatrix, mul_sub, sub_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hi, hA, zero_mul, sub_zero]
  · rw [hA, mul_assoc, hi, mul_zero, sub_zero]
  · rw [← mul_assoc, ← mul_assoc, hB, hj, zero_mul, sub_zero]
  · rw [hB, mul_assoc, hj, mul_zero, sub_zero]

/-- The edge commutator matrix is square zero over every commutative ring. -/
theorem raisingCommutatorMatrix_mul_self (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) :
    T.raisingCommutatorMatrix (R := R) i j * T.raisingCommutatorMatrix i j = 0 := by
  obtain ⟨_, hi, _, hj⟩ := T.raisingCommutatorMatrix_annihilates (R := R) i j hij hji
  nth_rw 2 [raisingCommutatorMatrix]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, hi, hj, zero_mul, zero_mul, sub_zero]

omit [Fintype ι] in
private theorem raisingMatrix_map_apply_eq_zero (i k : B) (a b : ι)
    (h : T.weight a k - T.weight b k ≠ T.cartanMatrix k i) :
    ((T.raisingMatrix i).map (Int.cast : ℤ → R)) a b = 0 := by
  have hz := T.raisingMatrix_apply_eq_zero_of_weight_sub_ne i a b (fun he ↦ h (congrFun he k))
  -- Scalar extension casts each matrix entry.
  change (T.raisingMatrix i a b : R) = 0
  rw [hz, Int.cast_zero]

omit [DecidableEq ι] in
private theorem mul_apply_eq_zero_of_weight_ne (w : ι → ℤ) (p q : ℤ)
    (M N : Matrix ι ι R) (hM : ∀ a b, w a - w b ≠ p → M a b = 0)
    (hN : ∀ a b, w a - w b ≠ q → N a b = 0) (a b : ι)
    (h : w a - w b ≠ p + q) : (M * N) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : w a - w c = p
  · rw [hN c b (by omega), mul_zero]
  · rw [hM a c hc, zero_mul]

private theorem raisingMatrix_mul_apply_eq_zero (i j k : B) (a b : ι)
    (h : T.weight a k - T.weight b k ≠ T.cartanMatrix k i + T.cartanMatrix k j) :
    ((T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix j).map (Int.cast : ℤ → R)) a b = 0 :=
  mul_apply_eq_zero_of_weight_ne (fun a ↦ T.weight a k) _ _ _ _
    (T.raisingMatrix_map_apply_eq_zero i k) (T.raisingMatrix_map_apply_eq_zero j k) a b h

/-- An adjacent edge commutator has an entry equal to `1` or `-1`, over any base ring. -/
theorem raisingCommutatorMatrix_has_unit_entry (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    (hi : ∃ a, T.weight a i = -1) :
    ∃ a b, T.raisingCommutatorMatrix (R := R) i j a b = 1 ∨
      T.raisingCommutatorMatrix (R := R) i j a b = -1 := by
  obtain ⟨b, hb | hb⟩ := T.exists_adjacent_raising_string i j hij hji hi
  · refine ⟨T.reflection j (T.reflection i b), b, Or.inr ?_⟩
    have hj : T.weight (T.reflection i b) j = -1 := by
      rw [T.weight_reflection, hb.1, hb.2, hji]
      norm_num
    simp [raisingCommutatorMatrix, Matrix.sub_apply, T.mul_raisingMatrix_map_apply, hb, hj]
  · refine ⟨T.reflection i (T.reflection j b), b, Or.inl ?_⟩
    have hi' : T.weight (T.reflection j b) i = -1 := by
      rw [T.weight_reflection, hb.1, hb.2, hij]
      norm_num
    simp [raisingCommutatorMatrix, Matrix.sub_apply, T.mul_raisingMatrix_map_apply, hb, hi']

/-- Scalar multiples of the adjacent commutator matrix have unique parameters. -/
theorem smul_raisingCommutatorMatrix_injective (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (fun t : R ↦ t • T.raisingCommutatorMatrix (R := R) i j) := by
  obtain ⟨a, b, hab | hab⟩ := T.raisingCommutatorMatrix_has_unit_entry (R := R) i j hij hji hi
  all_goals
    intro t u h
    have he := congrFun (congrFun h a) b
    simpa [Matrix.smul_apply, hab, smul_eq_mul] using he

/-- Ordered Heisenberg coordinates on an adjacent pair of raising strings. -/
def raisingHeisenbergMatrix (i j : B) (g : HeisenbergGroup R) : Matrix ι ι R :=
  1 + g.x • (T.raisingMatrix i).map Int.cast + g.y • (T.raisingMatrix j).map Int.cast +
    (g.x * g.y) • ((T.raisingMatrix j).map Int.cast * (T.raisingMatrix i).map Int.cast) +
      g.z • T.raisingCommutatorMatrix i j

/-- The identity Heisenberg element acts trivially. -/
@[simp]
theorem raisingHeisenbergMatrix_one (i j : B) :
    T.raisingHeisenbergMatrix i j (1 : HeisenbergGroup R) = 1 := by
  simp [raisingHeisenbergMatrix]

/-- The ordered matrix coordinates satisfy the existing Heisenberg multiplication law. -/
theorem raisingHeisenbergMatrix_mul (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    (g h : HeisenbergGroup R) :
    T.raisingHeisenbergMatrix i j (g * h) =
      T.raisingHeisenbergMatrix i j g * T.raisingHeisenbergMatrix i j h := by
  have hi := T.raisingMatrix_map_mul_self (R := R) i
  have hj := T.raisingMatrix_map_mul_self (R := R) j
  have hA := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) i j hij
  have hB := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) j i hji
  have hABB : (T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix j).map Int.cast * (T.raisingMatrix j).map Int.cast = 0 := by
    rw [mul_assoc, hj, mul_zero]
  have hBAA : (T.raisingMatrix j).map (Int.cast : ℤ → R) *
      (T.raisingMatrix i).map Int.cast * (T.raisingMatrix i).map Int.cast = 0 := by
    rw [mul_assoc, hi, mul_zero]
  simp only [raisingHeisenbergMatrix, raisingCommutatorMatrix, HeisenbergGroup.mul_x,
    HeisenbergGroup.mul_y, HeisenbergGroup.mul_z, smul_sub, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  simp only [← mul_assoc, hi, hj, hA, hB, hABB, hBAA, zero_mul, smul_zero, add_zero, sub_zero]
  module

private theorem raisingCoordinates_apply_reflection (i j : B)
    (hij : T.cartanMatrix i j = -1) (b : ι) (hb : T.weight b i = -1) (x y z w : R) :
    (1 + x • (T.raisingMatrix i).map Int.cast + y • (T.raisingMatrix j).map Int.cast +
      z • ((T.raisingMatrix i).map Int.cast * (T.raisingMatrix j).map Int.cast) +
      w • ((T.raisingMatrix j).map Int.cast * (T.raisingMatrix i).map Int.cast) : Matrix ι ι R)
        (T.reflection i b) b = x := by
  have hd : T.weight (T.reflection i b) i - T.weight b i = 2 := by simp [hb]
  have hne : T.reflection i b ≠ b := by
    intro h
    rw [h] at hd
    omega
  have hB := T.raisingMatrix_map_apply_eq_zero (R := R) j i (T.reflection i b) b
    (by rw [hd, hij]; omega)
  have hAB := T.raisingMatrix_mul_apply_eq_zero (R := R) i j i (T.reflection i b) b
    (by rw [hd, T.cartanMatrix_diag, hij]; omega)
  have hBA := T.raisingMatrix_mul_apply_eq_zero (R := R) j i i (T.reflection i b) b
    (by rw [hd, hij, T.cartanMatrix_diag]; omega)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hB, hAB, hBA, mul_zero,
    add_zero]
  simp [hne, hb]

/-- Integer support labels separate the first two coordinates; a primitive commutator entry
separates the third, even in characteristics two and three. -/
theorem raisingHeisenbergMatrix_injective (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.raisingHeisenbergMatrix (R := R) i j) := by
  have hj : ∃ a, T.weight a j = -1 := by
    obtain ⟨a, ha | ha⟩ := T.exists_adjacent_raising_string i j hij hji hi
    · refine ⟨T.reflection i a, ?_⟩
      rw [T.weight_reflection, ha.1, ha.2, hji]
      norm_num
    · exact ⟨a, ha.2⟩
  have hform (g : HeisenbergGroup R) : T.raisingHeisenbergMatrix i j g =
      1 + g.x • (T.raisingMatrix i).map Int.cast + g.y • (T.raisingMatrix j).map Int.cast +
        g.z • ((T.raisingMatrix i).map Int.cast * (T.raisingMatrix j).map Int.cast) +
          (g.x * g.y - g.z) •
            ((T.raisingMatrix j).map Int.cast * (T.raisingMatrix i).map Int.cast) := by
    simp only [raisingHeisenbergMatrix, raisingCommutatorMatrix, smul_sub, sub_smul]
    abel
  intro g h he
  have hx : g.x = h.x := by
    obtain ⟨b, hb⟩ := hi
    have he' := congrFun (congrFun he (T.reflection i b)) b
    simpa only [hform, T.raisingCoordinates_apply_reflection i j hij b hb] using he'
  have hy : g.y = h.y := by
    obtain ⟨b, hb⟩ := hj
    have hswap (g : HeisenbergGroup R) : T.raisingHeisenbergMatrix i j g =
        1 + g.y • (T.raisingMatrix j).map Int.cast + g.x • (T.raisingMatrix i).map Int.cast +
          (g.x * g.y - g.z) •
            ((T.raisingMatrix j).map Int.cast * (T.raisingMatrix i).map Int.cast) +
          g.z • ((T.raisingMatrix i).map Int.cast * (T.raisingMatrix j).map Int.cast) := by
      rw [hform]
      abel
    have he' := congrFun (congrFun he (T.reflection j b)) b
    simpa only [hswap, T.raisingCoordinates_apply_reflection j i hji b hb] using he'
  have hz : g.z = h.z := by
    apply T.smul_raisingCommutatorMatrix_injective i j hij hji hi
    simpa only [raisingHeisenbergMatrix, hx, hy, add_right_inj] using he
  exact HeisenbergGroup.ext hx hy hz

/-- The adjacent simple unipotent commutator is linear in the product of the parameters. -/
theorem raising_unipotent_commutator (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) (s t : R) :
    (1 + s • (T.raisingMatrix i).map Int.cast) *
        (1 + t • (T.raisingMatrix j).map Int.cast) *
        (1 + (-s) • (T.raisingMatrix i).map Int.cast) *
        (1 + (-t) • (T.raisingMatrix j).map Int.cast) =
      1 + (s * t) • T.raisingCommutatorMatrix (R := R) i j := by
  have hi := T.raisingMatrix_map_mul_self (R := R) i
  have hj := T.raisingMatrix_map_mul_self (R := R) j
  have hA := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) i j hij
  have hB := T.raisingMatrix_mul_raisingMatrix_mul_of_adjacent (R := R) j i hji
  have hABB : (T.raisingMatrix i).map (Int.cast : ℤ → R) *
      (T.raisingMatrix j).map Int.cast * (T.raisingMatrix j).map Int.cast = 0 := by
    rw [mul_assoc, hj, mul_zero]
  simp only [raisingCommutatorMatrix, smul_sub, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  simp only [hi, hj, hA, hB, hABB, zero_mul, smul_zero, add_zero]
  module

/-- Heisenberg coordinates are the ordered product of the two simple-root parameters
and the edge commutator parameter. -/
theorem raisingHeisenbergMatrix_eq_mul (i j : B)
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) (g : HeisenbergGroup R) :
    T.raisingHeisenbergMatrix i j g =
      (1 + g.y • (T.raisingMatrix j).map Int.cast) *
        (1 + g.x • (T.raisingMatrix i).map Int.cast) *
          (1 + g.z • T.raisingCommutatorMatrix i j) := by
  obtain ⟨hi, _, hj, _⟩ := T.raisingCommutatorMatrix_annihilates (R := R) i j hij hji
  simp only [raisingHeisenbergMatrix, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  simp only [mul_assoc, hi, hj, mul_zero, smul_zero, add_zero]
  module

end TauCeti.MinusculeWeightTable
