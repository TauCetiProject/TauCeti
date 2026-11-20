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

For a strict unit `e` of an uncurved `A∞` algebra `A`, the bar differential of any pure word
containing `e` agrees modulo `degenerateWords R A e` with the initial and final boundary collapses,
with vanishing one-letter projection (`barDifferential_of_tprod_sub_mem_degenerateWords`,
`letter_barDifferential_of_tprod_sub_eq_zero`). Any linear map vanishing on higher degenerate words
(or on `degenerateWords R A e`) therefore evaluates on `𝒜.barDifferential` by that boundary
difference (`apply_barDifferential_of_tprod_of_higher_eq_zero`,
`apply_barDifferential_of_tprod_of_ker`).

Moreover, `taylor_prepend_prepend_eq_zero` shows that `𝒜.taylor` kills words of length at least
three with `e` in either leading slot or a degenerate tail. Combining the two yields
`degenerateWords_le_ker_taylor_coalgHom_sub_barDifferential`: for any degree-zero Taylor map
sending `e` to a target strict unit `e'` and killing higher `e`-degenerate pure words, the `A∞`
morphism defect `ℬ.taylor ∘ₗ coalgHom R t - t ∘ₗ 𝒜.barDifferential` vanishes on all
`e`-degenerate words.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

namespace TauCeti.AInfinityAlgebra.StrictUnit

open ReducedTensorWords

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] {𝒜 : AInfinityAlgebra R A} {e : A}

private noncomputable def unitCollapseTerm (𝒜 : AInfinityAlgebra R A) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (p d : ℕ) : ReducedTensorWords R A :=
  let y := (𝒜.grading.shift 1).twistedTuple 1 x 0 j.val
  (if p = j.val ∧ d = 2 ∧ j.val + 1 ≤ n then
    splice R y 0 (n + 1) j.val 2 (if h : j.val + 1 < n + 1 then y ⟨j.val + 1, h⟩ else 0) else 0) +
  (if p = j.val - 1 ∧ d = 2 ∧ 1 ≤ j.val then
    -splice R y 0 (n + 1) (j.val - 1) 2 (y ⟨j.val - 1, by omega⟩) else 0)

private theorem splice_twistedTuple_pred_eq {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1))
    (hj1 : 1 ≤ j.val) (v : A) :
    splice R ((𝒜.grading.shift 1).twistedTuple 1 x 0 (j.val - 1)) 0 (n + 1) (j.val - 1) 2 v =
      splice R ((𝒜.grading.shift 1).twistedTuple 1 x 0 j.val) 0 (n + 1) (j.val - 1) 2 v := by
  have := j.isLt
  rw [splice_eq_of_tprod R _ v two_pos (by omega) (by omega),
    splice_eq_of_tprod R _ v two_pos (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun i ↦ ?_
  have := i.isLt; simp only [Fin.val_cast]
  split_ifs <;> first | rfl |
    exact InternalGrading.twistedTuple_apply_eq_twistedTuple_apply _ _ _ _ (by simp; omega)

private theorem barDifferential_summand_eq_unitCollapseTerm_of_two (h : 𝒜.StrictUnit e) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) (p : ℕ) (hfit2 : p + 2 ≤ n + 1)
    (hblock : p ≤ j.val ∧ j.val < p + 2) :
    splice R ((𝒜.grading.shift 1).twistedTuple 1 x 0 p) 0 (n + 1) p 2
        (𝒜.taylor (subword R x p 2)) = unitCollapseTerm 𝒜 x j p 2 := by
  have := j.isLt; dsimp only [unitCollapseTerm]
  rcases Nat.lt_or_ge p j.val with hpj | hpj
  · obtain rfl : p = j.val - 1 := by omega
    have hj' : (⟨j.val - 1 + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
    rw [subword_two_eq R x hfit2, hj', hj, h.taylor_of_two_unit_right,
      splice_twistedTuple_pred_eq x j (by omega)]
    have hneg : 𝒜.grading.koszulTwist 1 (x ⟨j.val - 1, by omega⟩) =
        -((𝒜.grading.shift 1).twistedTuple 1 x 0 j.val ⟨j.val - 1, by omega⟩) := by
      rw [InternalGrading.twistedTuple_apply_of_mem_Ico
            (hi := by simp only [Nat.zero_le, true_and]; omega),
        InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, neg_neg]
    rw [hneg, splice_neg]
  · obtain rfl : p = j.val := by omega
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero, dite_eq_left]
    rw [subword_two_eq R x hfit2, Fin.eta, hj, h.taylor_of_two_unit_left,
      InternalGrading.twistedTuple_apply_of_not_mem_Ico (hi := by simp)]

private theorem barDifferential_summand_sub_unitCollapseTerm (h : 𝒜.StrictUnit e) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) (p d : ℕ) :
    let diff :=
      splice R ((𝒜.grading.shift 1).twistedTuple 1 x 0 p) 0 (n + 1) p d
        (𝒜.taylor (subword R x p d)) - unitCollapseTerm 𝒜 x j p d
    diff ∈ degenerateWords R A e ∧ letter R A diff = 0 := by
  have := j.isLt
  by_cases hfit : 0 < d ∧ p + d ≤ n + 1
  swap
  · dsimp only [unitCollapseTerm]
    simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, ite_eq_right,
      add_zero, sub_zero, Submodule.zero_mem, map_zero, and_self]
  by_cases hblock : p ≤ j.val ∧ j.val < p + d
  swap
  · obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R
      ((𝒜.grading.shift 1).twistedTuple 1 x 0 p) hfit.2 (𝒜.taylor (subword R x p d)) hblock
    have hne : (⟨n + 1 + 1 - d, by omega⟩ : {m : ℕ // 0 < m}) ≠ 1 := fun h1 ↦ by
      have := congrArg Subtype.val h1; dsimp at this; omega
    have hdeg : of R A ⟨n + 1 + 1 - d, by omega⟩ (PiTensorProduct.tprod R y) ∈
        degenerateWords R A e := by
      by_cases hjp : j.val < p
      · refine of_tprod_mem_degenerateWords_of_eq_smul ⟨n + 1 + 1 - d, by omega⟩ y
          (i := k) (c := (-1 : R)) ?_
        rw [hk, InternalGrading.twistedTuple_apply_of_mem_Ico (hi := by simp [hjp]), hj,
          InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
          𝒜.grading.koszulTwist_apply_of_mem_zero h.degree_zero, neg_one_smul]
      · exact of_tprod_mem_degenerateWords ⟨n + 1 + 1 - d, by omega⟩ y ⟨k, by
          rw [hk, InternalGrading.twistedTuple_apply_of_not_mem_Ico (hi := by simp [hjp]), hj]⟩
    dsimp only [unitCollapseTerm]
    simp (disch := omega) only [hy, ite_eq_right, add_zero, sub_zero]
    exact ⟨hdeg, letter_of_of_ne_one R A hne _⟩
  by_cases hd2 : d = 2
  swap
  · have hzero : 𝒜.taylor (subword R x p d) = 0 := by
      rw [subword_eq_of_tprod R x hfit.1 hfit.2]
      exact h.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩ hd2 _
        ⟨⟨j.val - p, by dsimp; omega⟩, by rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
    dsimp only [unitCollapseTerm]
    simp (disch := omega) only [hzero, splice_zero, ite_eq_right, add_zero, sub_zero,
      Submodule.zero_mem, map_zero, and_self]
  subst hd2
  rw [h.barDifferential_summand_eq_unitCollapseTerm_of_two x j hj p hfit.2 hblock, sub_self]
  exact ⟨Submodule.zero_mem _, map_zero _⟩

private theorem sum_unitCollapseTerm_eq {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1)) :
    (∑ p ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1 + 1), unitCollapseTerm 𝒜 x j p d) =
      (if j.val = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.val = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0) := by
  have hjn := j.isLt; set y := (𝒜.grading.shift 1).twistedTuple 1 x 0 j.val
  have hsum : (∑ p ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1 + 1),
      unitCollapseTerm 𝒜 x j p d) =
      (if j.val + 1 ≤ n then
        splice R y 0 (n + 1) j.val 2 (if h : j.val + 1 < n + 1 then y ⟨j.val + 1,
            h⟩ else 0) else 0) +
      (if 1 ≤ j.val then -splice R y 0 (n + 1) (j.val - 1) 2 (y ⟨j.val - 1, by omega⟩) else 0) := by
    simp only [unitCollapseTerm, y, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_range]
    congr 1 <;> split_ifs <;> first | rfl | omega
  rw [hsum]
  rcases Nat.eq_zero_or_pos n with rfl | hn; · simp (disch := omega)
  rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
  · have hyx : y = x := by simp [y, hj0]
    simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero, dite_eq_left, sub_zero, hyx]
    exact splice_two_succ_eq_subword R hn hj0 x
  rcases Nat.lt_or_ge j.val n with hjlt | hjge
  · simp (disch := omega) only [ite_eq_right, ite_eq_left, dite_eq_left, sub_zero]
    rw [splice_two_succ_eq_splice_two_pred R hj0 hjlt y, add_neg_cancel]
  · simp (disch := omega) only [ite_eq_right, ite_eq_left, zero_add, zero_sub]
    rw [splice_two_pred_eq_subword R (by omega) y, koszulTwist_grading, map_subword]
    exact congrArg (-·) <| subword_congr R y _ (by omega) (by omega) fun k hk ↦
      InternalGrading.twistedTuple_apply_of_mem_Ico _ _ _ _ _ _ (by simp; omega)

/-- On a pure word whose `j`-th letter is the strict unit `e`, the bar differential agrees modulo
`degenerateWords R A e` with the boundary difference at `j = 0` and `j = n`. -/
theorem barDifferential_of_tprod_sub_mem_degenerateWords (h : 𝒜.StrictUnit e) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) :
    𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) -
      ((if j.val = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.val = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0)) ∈ degenerateWords R A e := by
  rw [barDifferential_def, gradedCoderiv_of_tprod, ← sum_unitCollapseTerm_eq x j]
  simp only [← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun d _ ↦
    (barDifferential_summand_sub_unitCollapseTerm h x j hj p d).1

/-- The difference between the bar differential of a pure word with strict unit at `j` and its
boundary formula has zero one-letter projection. -/
theorem letter_barDifferential_of_tprod_sub_eq_zero (h : 𝒜.StrictUnit e) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) :
    letter R A (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) -
      ((if j.val = 0 ∧ 0 < n then subword R x 1 n else 0) -
        (if j.val = n ∧ 0 < n then
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)
        else 0))) = 0 := by
  rw [barDifferential_def, gradedCoderiv_of_tprod, ← sum_unitCollapseTerm_eq x j]
  simp only [← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
    (barDifferential_summand_sub_unitCollapseTerm h x j hj p d).2

/-- A linear map vanishing on pure degenerate words of length at least two evaluates on the bar
differential of a pure word with strict unit at `j` by the initial/final boundary formula. -/
theorem apply_barDifferential_of_tprod_of_higher_eq_zero (h : 𝒜.StrictUnit e)
    {F : ReducedTensorWords R A →ₗ[R] M}
    (hFe : ∀ (m : {m : ℕ // 0 < m}), m.val ≠ 1 → ∀ y : Fin m.val → A,
      (∃ i, y i = e) → F (of R A m (PiTensorProduct.tprod R y)) = 0)
    {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) :
    F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.val = 0 ∧ 0 < n then F (subword R x 1 n) else 0) -
        (if j.val = n ∧ 0 < n then
          F ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n))
        else 0) := by
  have hzero := apply_eq_comp_letter_of_mem_degenerateWords F hFe
    (h.barDifferential_of_tprod_sub_mem_degenerateWords x j hj)
  rw [h.letter_barDifferential_of_tprod_sub_eq_zero x j hj, map_zero, map_zero, map_sub,
    sub_eq_zero] at hzero
  rw [hzero, map_sub]; congr 1 <;> split_ifs <;> simp

/-- A linear map vanishing on `degenerateWords R A e` evaluates on the bar differential of a pure
word with strict unit at `j` by the initial/final boundary formula. -/
theorem apply_barDifferential_of_tprod_of_ker (h : 𝒜.StrictUnit e)
    {F : ReducedTensorWords R A →ₗ[R] M} (hFe : degenerateWords R A e ≤ LinearMap.ker F) {n : ℕ}
    (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = e) :
    F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.val = 0 ∧ 0 < n then F (subword R x 1 n) else 0) -
        (if j.val = n ∧ 0 < n then
          F ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n))
        else 0) :=
  h.apply_barDifferential_of_tprod_of_higher_eq_zero
    (fun m _ y hy ↦ LinearMap.mem_ker.mp (hFe (of_tprod_mem_degenerateWords m y hy))) x j hj

/-- Prepending two letters to a nonempty tensor word produces a word of length at least three, so
`𝒜.taylor` kills it whenever either prepended letter is the strict unit or the tail is
degenerate. -/
theorem taylor_prepend_prepend_eq_zero (h : 𝒜.StrictUnit e) (a b : A) (w : ReducedTensorWords R A)
    (habw : a = e ∨ b = e ∨ w ∈ degenerateWords R A e) :
    𝒜.taylor (prepend R A a (prepend R A b w)) = 0 := by
  let T : ReducedTensorWords R A →ₗ[R] A := 𝒜.taylor ∘ₗ prepend R A a ∘ₗ prepend R A b
  suffices T w = 0 by simpa only [T, LinearMap.comp_apply] using this
  have hT (m : {m : ℕ // 0 < m}) (y : Fin m.val → A)
      (hy : ∃ k, (Fin.cons a (Fin.cons b y) : Fin (m.val + 1 + 1) → A) k = e) :
      T (of R A m (PiTensorProduct.tprod R y)) = 0 := by
    dsimp only [T, LinearMap.comp_apply]; rw [prepend_of_tprod, prepend_of_tprod]
    exact h.taylor_of_tprod_eq_zero ⟨m.val + 1 + 1, by omega⟩ (by dsimp; omega) _ hy
  rcases habw with rfl | rfl | hw
  · have hT0 : T = 0 := linearMap_ext R A fun m y ↦ hT m y ⟨0, rfl⟩
    rw [hT0, LinearMap.zero_apply]
  · have hT0 : T = 0 := linearMap_ext R A fun m y ↦ hT m y ⟨1, rfl⟩
    rw [hT0, LinearMap.zero_apply]
  · exact LinearMap.mem_ker.mp (degenerateWords_le_iff.2
      (fun m y ⟨i, hi⟩ ↦ LinearMap.mem_ker.mpr (hT m y ⟨i.succ.succ, by simpa using hi⟩)) hw)

/-! ### Strict-unit morphism compatibility on degenerate words -/

section Morphism

variable {ℬ : AInfinityAlgebra R B} {e' : B}

section Helpers

variable (t : ReducedTensorWords R A →ₗ[R] B) (ht_unit : t (ofLetter R A e) = e')
  (ht_deg : ∀ (m : {m : ℕ // 0 < m}), m.val ≠ 1 → ∀ y : Fin m.val → A,
    (∃ i, y i = e) → t (of R A m (PiTensorProduct.tprod R y)) = 0)
include ht_unit ht_deg

private theorem apply_subword_of_mem_block {k : ℕ} (x : Fin k → A) {j : Fin k} (hj : x j = e)
    {a b : ℕ} (ha : a ≤ j.val) (hb : j.val < a + b) :
    t (subword R x a b) = if b = 1 then e' else 0 := by
  have := j.isLt; by_cases hb1 : b = 1
  · subst hb1
    have hja : (⟨a, by omega⟩ : Fin k) = j := Fin.ext (by simp; omega)
    rw [ite_eq_left rfl, subword_one R A x (by omega), hja, hj, ht_unit]
  · rw [ite_eq_right hb1, apply_eq_comp_letter_of_mem_degenerateWords t ht_deg
      (subword_mem_degenerateWords x ⟨j, ha, hb, hj⟩),
      letter_subword_of_ne_one R A x a hb1, map_zero, map_zero]

variable (hB : ℬ.StrictUnit e')
include hB

private theorem sum_taylor_prepend_prepend_coalgHom_eq_zero {n : ℕ} (x : Fin (n + 1) → A)
    (j : Fin (n + 1)) (hj : x j = e) (d : ℕ) :
    ∑ c ∈ Finset.range (n + 1 - d),
      ℬ.taylor (prepend R B (t (subword R x 0 d))
        (prepend R B (t (subword R x d c))
          (coalgHom R t (subword R x (d + c) (n + 1 - d - c))))) = 0 := by
  have := j.isLt; refine Finset.sum_eq_zero fun c hc ↦ ?_; rw [Finset.mem_range] at hc
  rcases Nat.eq_zero_or_pos c with rfl | _; · simp [subword_length_zero]
  by_cases hjd : j.val < d
  · rw [apply_subword_of_mem_block t ht_unit ht_deg x hj (a := 0) (by omega) (by omega)]
    split_ifs <;> simp [hB.taylor_prepend_prepend_eq_zero]
  · by_cases hjdc : j.val < d + c
    · rw [apply_subword_of_mem_block t ht_unit ht_deg x hj (a := d) (by omega) (by omega)]
      split_ifs <;> simp [hB.taylor_prepend_prepend_eq_zero]
    · exact hB.taylor_prepend_prepend_eq_zero _ _ _ (Or.inr (Or.inr
        (coalgHom_subword_mem_degenerateWords t ht_unit ht_deg x (by omega)
          ⟨j, by omega, by omega, hj⟩)))

private theorem taylor_prepend_coalgHom_subword {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1))
    (hj : x j = e) (d : ℕ) (hd : d ∈ Finset.range (n + 1)) :
    ℬ.taylor (prepend R B (t (subword R x 0 d)) (coalgHom R t (subword R x d (n + 1 - d)))) =
      (if d = 1 ∧ (j.val = 0 ∧ 0 < n) then t (subword R x 1 n) else 0) +
        (if d = n ∧ (j.val = n ∧ 0 < n) then
          ℬ.grading.koszulTwist 1 (t (subword R x 0 n)) else 0) := by
  have := j.isLt; rw [Finset.mem_range] at hd
  rcases Nat.eq_zero_or_pos d with rfl | _; · simp (disch := omega) [subword_length_zero]
  rw [coalgHom_subword _ x d (n + 1 - d), map_add, map_add, map_sum, map_sum,
    sum_taylor_prepend_prepend_coalgHom_eq_zero t ht_unit ht_deg hB x j hj d, add_zero]
  by_cases hjd : j.val < d
  · rw [apply_subword_of_mem_block t ht_unit ht_deg x hj (a := 0) (by omega) (by omega)]
    by_cases hd1 : d = 1
    · subst hd1; rw [ite_eq_left rfl, Nat.add_sub_cancel, prepend_ofLetter,
        hB.taylor_of_two_unit_left]
      simp (disch := omega) only [true_and, ite_eq_left, ite_eq_right, add_zero]
    · rw [ite_eq_right hd1]; simp (disch := omega)
  · rw [apply_subword_of_mem_block t ht_unit ht_deg x hj (a := d) (by omega) (by omega)]
    by_cases hdn : d = n
    · subst hdn; rw [Nat.add_sub_cancel_left, ite_eq_left rfl, prepend_ofLetter,
        hB.taylor_of_two_unit_right]
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
    · rw [ite_eq_right (by omega : n + 1 - d ≠ 1), map_zero, map_zero, map_zero]
      simp (disch := omega) only [ite_eq_right, add_zero]

private theorem taylor_coalgHom_of_tprod {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1))
    (hj : x j = e) :
    ℬ.taylor (coalgHom R t (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.val = 0 ∧ 0 < n then t (subword R x 1 n) else 0) +
        (if j.val = n ∧ 0 < n then ℬ.grading.koszulTwist 1 (t (subword R x 0 n)) else 0) := by
  have hjn := j.isLt
  rw [of_tprod_eq_subword R (Nat.zero_lt_succ n), coalgHom_subword, map_add, map_sum,
    apply_subword_of_mem_block t ht_unit ht_deg x hj (a := 0) (by omega) (by omega)]
  have hsingle : ℬ.taylor (ofLetter R B (if n + 1 = 1 then e' else 0)) = 0 := by
    split_ifs
    · rw [ofLetter_eq_of_tprod]
      exact hB.taylor_of_tprod_eq_zero ⟨1, Nat.one_pos⟩ (by decide) _ ⟨0, rfl⟩
    · simp
  simp only [hsingle, zero_add]
  rw [Finset.sum_congr rfl (taylor_prepend_coalgHom_subword t ht_unit ht_deg hB x j hj)]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

end Helpers

/-- For any degree-zero Taylor map `t : Tᶜ(sA) →ₗ[R] B` sending the source strict unit `e` to the
target strict unit `e'` and vanishing on higher `e`-degenerate pure words, the `A∞` morphism defect
`ℬ.taylor ∘ₗ coalgHom R t - t ∘ₗ 𝒜.barDifferential` vanishes on all `e`-degenerate words. -/
theorem degenerateWords_le_ker_taylor_coalgHom_sub_barDifferential
    (hA : 𝒜.StrictUnit e) (hB : ℬ.StrictUnit e') (t : ReducedTensorWords R A →ₗ[R] B)
    (ht_hom : LinearMap.IsHomogeneous t (gradedPiece (𝒜.grading.shift 1))
      (ℬ.grading.shift 1).piece 0)
    (ht_unit : t (ofLetter R A e) = e')
    (ht_deg : ∀ (m : {m : ℕ // 0 < m}), m.val ≠ 1 → ∀ y : Fin m.val → A,
      (∃ i, y i = e) → t (of R A m (PiTensorProduct.tprod R y)) = 0) :
    degenerateWords R A e ≤
      LinearMap.ker (ℬ.taylor ∘ₗ coalgHom R t - t ∘ₗ 𝒜.barDifferential) := by
  rw [degenerateWords_le_iff]
  rintro ⟨_ | n, hN⟩ x ⟨j, hj⟩; · omega
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; simp only [LinearMap.comp_apply]
  rw [taylor_coalgHom_of_tprod t ht_unit ht_deg hB x j hj,
    hA.apply_barDifferential_of_tprod_of_higher_eq_zero ht_deg x j hj]
  rw [← grading_piece] at ht_hom
  have hkt : t ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (subword R x 0 n)) =
      -ℬ.grading.koszulTwist 1 (t (subword R x 0 n)) := by
    simpa [InternalGrading.koszulTwist_one_shift_one] using
      (ht_hom.koszulTwist_apply 1 (subword R x 0 n)).symm
  rw [hkt, sub_eq_add_neg]; congr 1; split_ifs <;> simp

end Morphism

end TauCeti.AInfinityAlgebra.StrictUnit
