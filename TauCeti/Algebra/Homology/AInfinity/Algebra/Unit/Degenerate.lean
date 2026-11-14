/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate
public import TauCeti.LinearAlgebra.TensorCoalgebra.Grading

/-!
# The bar differential and Taylor map on unit-containing words

For a strict unit `e` of an uncurved `A∞` algebra `A` and a pure homogeneous word of length `n + 1`
with `x j = e`, every summand of `𝒜.barDifferential` either keeps `e` outside the collapsed block
(producing a degenerate word of length at least two) or collapses `[e, a]` or `[a, e]`. Interior
collapses (`0 < j < n`) cancel, leaving the initial/final boundary difference modulo
`degenerateWords R A e` (`barDifferential_of_tprod_sub_mem_degenerateWords`) with zero one-letter
projection (`letter_barDifferential_of_tprod_sub_eq_zero`).

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

namespace TauCeti.AInfinityAlgebra.StrictUnit

open ReducedTensorWords

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
  {𝒜 : AInfinityAlgebra R A} {e : A}

private noncomputable def unitCollapseTerm {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) (p d : ℕ) : ReducedTensorWords R A :=
  (if p = j.1 ∧ d = 2 ∧ j.1 + 1 ≤ n then
    negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
      splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0)
  else 0) +
  (if p = j.1 - 1 ∧ d = 2 ∧ 1 ≤ j.1 then
    negOnePowCast R (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
      negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
      splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩)
  else 0)

private theorem barDifferential_summand_eq_unitCollapseTerm_of_two (h : 𝒜.StrictUnit e)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e)
    (p : ℕ) (hfit2 : p + 2 ≤ n + 1) (hblock : p ≤ j.1 ∧ j.1 < p + 2) :
    (((∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
      splice R x 0 (n + 1) p 2 (𝒜.taylor (subword R x p 2)) =
    unitCollapseTerm x 𝒟 j p 2 := by
  have := j.isLt
  dsimp only [unitCollapseTerm]
  rcases Nat.lt_or_ge p j.1 with hpj | hpj
  · obtain rfl : p = j.1 - 1 := by omega
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
    rw [subword_two_eq R x hfit2, show (⟨j.1 - 1 + 1, by omega⟩ : Fin (n + 1)) = j from
      Fin.ext (by simp; omega), hj, h.taylor_of_two_unit_right,
      𝒜.grading.koszulTwist_one_apply_of_mem
        (by simpa [InternalGrading.shift_piece] using hx ⟨j.1 - 1, by omega⟩),
      splice_smul]
    simp only [negOnePowCast_eq_intCast]
  · obtain rfl : p = j.1 := by omega
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero]
    rw [subword_two_eq R x hfit2, Fin.eta, hj, h.taylor_of_two_unit_left,
      negOnePowCast_eq_intCast, dite_eq_left (by omega)]

private theorem barDifferential_summand_sub_unitCollapseTerm (h : 𝒜.StrictUnit e)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e)
    (p d : ℕ) (hd : d ∈ Finset.range (n + 1 + 1)) :
    let diff :=
      (((∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
        splice R x 0 (n + 1) p d (𝒜.taylor (subword R x p d)) -
      unitCollapseTerm x 𝒟 j p d
    diff ∈ degenerateWords R A e ∧ letter R A diff = 0 := by
  have := j.isLt
  rw [Finset.mem_range] at hd
  by_cases hfit : 0 < d ∧ p + d ≤ n + 1
  swap
  · dsimp only [unitCollapseTerm]
    simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, smul_zero, ite_eq_right,
      add_zero, sub_zero, Submodule.zero_mem, map_zero, and_self]
  by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
  swap
  · obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R x hfit.2
      (𝒜.taylor (subword R x p d)) hblock
    have hne : (⟨n + 1 + 1 - d, by omega⟩ : {m : ℕ // 0 < m}) ≠ 1 := fun h1 ↦ by
      have hval : n + 1 + 1 - d = 1 := congrArg Subtype.val h1
      omega
    dsimp only [unitCollapseTerm]
    simp (disch := omega) only [hy, ite_eq_right, add_zero, sub_zero]
    refine ⟨Submodule.smul_mem _ _
        (of_tprod_mem_degenerateWords ⟨n + 1 + 1 - d, by omega⟩ y ⟨k, hk.trans hj⟩), ?_⟩
    rw [map_smul, letter_of_of_ne_one R A hne, smul_zero]
  by_cases hd2 : d = 2
  swap
  · have hzero : 𝒜.taylor (subword R x p d) = 0 := by
      rw [subword_eq_of_tprod R x hfit.1 hfit.2]
      exact h.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩ hd2 _
        ⟨⟨j.1 - p, by dsimp only; omega⟩, by rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
    dsimp only [unitCollapseTerm]
    simp (disch := omega) only [hzero, splice_zero, smul_zero, ite_eq_right, add_zero, sub_zero,
      Submodule.zero_mem, map_zero, and_self]
  subst hd2
  rw [h.barDifferential_summand_eq_unitCollapseTerm_of_two x 𝒟 hx j hj p hfit.2 hblock, sub_self]
  exact ⟨Submodule.zero_mem _, map_zero _⟩

private theorem sum_unitCollapseTerm_eq {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) :
    (∑ p ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1 + 1), unitCollapseTerm x 𝒟 j p d) =
      (if j.1 = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.1 = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0) := by
  have hjn := j.isLt
  have hsum : (∑ p ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1 + 1),
      unitCollapseTerm x 𝒟 j p d) =
      (if j.1 + 1 ≤ n then
        negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0) else 0) +
      (if 1 ≤ j.1 then
        negOnePowCast R (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
          splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩) else 0) := by
    simp only [unitCollapseTerm, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_range]
    congr 1 <;> split_ifs <;> first | rfl | omega
  rw [hsum]
  set S : ℕ → ℤ := fun p ↦ ∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0 with hS
  have hSsucc (p : ℕ) (hp : p < n + 1) : S (p + 1) = S p + 𝒟 ⟨p, hp⟩ := by
    simp only [hS, Finset.sum_range_succ, dite_eq_left hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp (disch := omega)
  rcases Nat.eq_zero_or_pos j.1 with hj0 | hj0
  · simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero, dite_eq_left]
    rw [splice_two_succ_eq_subword R hn hj0 x, hj0, Finset.sum_range_zero, negOnePowCast_zero,
      one_smul, sub_zero]
  rcases Nat.lt_or_ge j.1 n with hjlt | hjge
  · simp (disch := omega) only [ite_eq_right, ite_eq_left, dite_eq_left]
    rw [splice_two_succ_eq_splice_two_pred R hj0 hjlt x, smul_smul, ← negOnePowCast_add, ← add_smul]
    have hSj := hSsucc (j.1 - 1) (by omega)
    rw [Nat.sub_add_cancel hj0] at hSj
    have hsign : negOnePowCast R (S j.1) +
        negOnePowCast R (S (j.1 - 1) + (𝒟 ⟨j.1 - 1, by omega⟩ + 1)) = 0 := by
      rw [hSj, ← add_assoc, negOnePowCast_add (R := R) _ 1, negOnePowCast_one, mul_neg_one,
        add_neg_cancel]
    simp only [hS] at hsign
    rw [hsign, zero_smul, sub_zero]
  · have hmem : subword R x 0 n ∈
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece (S n) := by
      rw [grading_piece]
      simpa only [hS, Nat.zero_add] using
        subword_mem_gradedPiece x (fun i ↦ if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0)
          (fun i ↦ by simpa only [Fin.is_lt, dite_true, Fin.eta] using hx i) 0 n
    simp (disch := omega) only [ite_eq_right, ite_eq_left, zero_add, zero_sub]
    rw [splice_two_pred_eq_subword R (by omega) x,
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist_one_apply_of_mem hmem,
      ← negOnePowCast_eq_intCast, smul_smul, ← negOnePowCast_add, ← neg_smul]
    have hSn : S n = S (j.1 - 1) + 𝒟 ⟨j.1 - 1, by omega⟩ := by
      rw [← hSsucc]; congr 1; omega
    congr 1
    simp only [hS] at hSn ⊢
    rw [hSn, ← add_assoc, negOnePowCast_add (R := R) _ 1, negOnePowCast_one, mul_neg_one]

/-- On a pure homogeneous word whose `j`-th letter is the strict unit `e`, the bar differential
agrees modulo `degenerateWords R A e` with the boundary difference at `j = 0` and `j = n`. -/
theorem barDifferential_of_tprod_sub_mem_degenerateWords (h : 𝒜.StrictUnit e)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e) :
    𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) -
      ((if j.1 = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.1 = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0)) ∈ degenerateWords R A e := by
  rw [barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ x 𝒟 hx,
    ← sum_unitCollapseTerm_eq x 𝒟 hx j]
  simp only [one_mul, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun d hd ↦
    (barDifferential_summand_sub_unitCollapseTerm h x 𝒟 hx j hj p d hd).1

/-- The difference between the bar differential of a homogeneous word with strict unit at `j` and
its boundary formula has zero one-letter projection. -/
theorem letter_barDifferential_of_tprod_sub_eq_zero (h : 𝒜.StrictUnit e)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e) :
    letter R A
      (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) -
        ((if j.1 = 0 ∧ 0 < n then subword R x 1 n else 0) -
          (if j.1 = n ∧ 0 < n then
            (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
          else 0))) = 0 := by
  rw [barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ x 𝒟 hx,
    ← sum_unitCollapseTerm_eq x 𝒟 hx j]
  simp only [one_mul, ← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d hd ↦
    (barDifferential_summand_sub_unitCollapseTerm h x 𝒟 hx j hj p d hd).2

/-- A linear map vanishing on pure degenerate words of length at least two evaluates on the bar
differential of a homogeneous word with strict unit at `j` by the initial/final boundary formula. -/
theorem apply_barDifferential_of_tprod_of_higher_eq_zero (h : 𝒜.StrictUnit e)
    {F : ReducedTensorWords R A →ₗ[R] M}
    (hFe : ∀ (m : {m : ℕ // 0 < m}), m.1 ≠ 1 → ∀ y : Fin m.1 → A,
      (∃ i, y i = e) → F (of R A m (PiTensorProduct.tprod R y)) = 0)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e) :
    F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then F (subword R x 1 n) else 0) -
        (if j.1 = n ∧ 0 < n then
          F ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n))
        else 0) := by
  have hzero : F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) -
      ((if j.1 = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.1 = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0))) = 0 := by
    rw [apply_eq_comp_letter_of_mem_degenerateWords F hFe
        (h.barDifferential_of_tprod_sub_mem_degenerateWords x 𝒟 hx j hj),
      h.letter_barDifferential_of_tprod_sub_eq_zero x 𝒟 hx j hj, map_zero, map_zero]
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, map_sub]
  congr 1 <;> split_ifs <;> simp

/-- A linear map vanishing on `degenerateWords R A e` evaluates on the bar differential of a
homogeneous word with strict unit at `j` by the initial/final boundary formula. -/
theorem apply_barDifferential_of_tprod_of_ker (h : 𝒜.StrictUnit e)
    {F : ReducedTensorWords R A →ₗ[R] M} (hFe : degenerateWords R A e ≤ LinearMap.ker F)
    {n : ℕ} (x : Fin (n + 1) → A) (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1)) (hj : x j = e) :
    F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then F (subword R x 1 n) else 0) -
        (if j.1 = n ∧ 0 < n then
          F ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n))
        else 0) :=
  h.apply_barDifferential_of_tprod_of_higher_eq_zero
    (fun m _ y hy ↦ LinearMap.mem_ker.mp (hFe (of_tprod_mem_degenerateWords m y hy))) x 𝒟 hx j hj

/-- Prepending two letters to a nonempty tensor word produces a word of length at least three, so
the Taylor map of `𝒜` kills it whenever either prepended letter is the strict unit or the tail is
degenerate. -/
theorem taylor_prepend_prepend_eq_zero (h : 𝒜.StrictUnit e) (a b : A)
    (w : ReducedTensorWords R A) (habw : a = e ∨ b = e ∨ w ∈ degenerateWords R A e) :
    𝒜.taylor (prepend R A a (prepend R A b w)) = 0 := by
  let T : ReducedTensorWords R A →ₗ[R] A := 𝒜.taylor ∘ₗ prepend R A a ∘ₗ prepend R A b
  change T w = 0
  have hT (m : {m : ℕ // 0 < m}) (y : Fin m.1 → A)
      (hy : ∃ k, (Fin.cons a (Fin.cons b y) : Fin (m.1 + 1 + 1) → A) k = e) :
      T (of R A m (PiTensorProduct.tprod R y)) = 0 := by
    dsimp only [T, LinearMap.comp_apply]
    rw [prepend_of_tprod, prepend_of_tprod]
    exact h.taylor_of_tprod_eq_zero ⟨m.1 + 1 + 1, by omega⟩ (by dsimp only; omega) _ hy
  rcases habw with rfl | rfl | hw
  · exact LinearMap.congr_fun (show T = 0 from linearMap_ext R A fun m y ↦ hT m y ⟨0, rfl⟩) w
  · exact LinearMap.congr_fun (show T = 0 from linearMap_ext R A fun m y ↦ hT m y ⟨1, rfl⟩) w
  · exact LinearMap.mem_ker.mp (degenerateWords_le_iff.2
      (fun m y ⟨i, hi⟩ ↦ LinearMap.mem_ker.mpr (hT m y ⟨i.succ.succ, by simpa using hi⟩)) hw)

end TauCeti.AInfinityAlgebra.StrictUnit
