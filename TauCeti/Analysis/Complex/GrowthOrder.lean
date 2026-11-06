/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.RCLike
public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The order of growth of a complex function

A function `f : ℂ → ℂ` has *order at most `A`*, `TauCeti.OrderLE f A`, when for every `A' > A`
it is `O(exp ‖s‖ ^ A')` as `‖s‖ → ∞`. This is the classical order of an entire function
(Davenport, *Multiplicative Number Theory*, §11; Titchmarsh, *The Theory of Functions*,
Chapter VIII), phrased through upper bounds only: no numeric order is defined. Entirety is not
part of the predicate; it is a hypothesis of the theorems that need it. The predicate is the
growth input of Hadamard's factorization and of the convexity bounds for L-functions.

## Main results

* `TauCeti.OrderLE.mono`, `TauCeti.OrderLE.add`, `TauCeti.OrderLE.mul`, `TauCeti.OrderLE.sum`,
  `TauCeti.OrderLE.prod`: the predicate is monotone in the exponent and closed under the ring
  operations at a common exponent.
* `TauCeti.OrderLE.comp_mul_add`: the order does not increase under an affine substitution
  `s ↦ a * s + b`.
* `Polynomial.orderLE_eval`: polynomials have order at most `0`; constants have every order.
* `TauCeti.orderLE_cexp_mul_pow`: `exp (a * s ^ n)` has order at most `n`, and
  `TauCeti.orderLE_cexp_pow_iff` shows that `exp (s ^ n)` has no smaller order when `n ≠ 0`.
  In particular `exp` has order exactly `1` (`TauCeti.orderLE_cexp_iff`).
* `TauCeti.orderLE_iff_isConst`: an entire function of negative order is constant (Liouville).
* `TauCeti.IsFiniteOrder`: existence of an order bound, with closure under finite sums,
  products and affine pullback. Invertible affine substitutions and nonzero polynomial
  factors preserve finite order in both directions; the latter permits changing a
  polynomial used to clear poles without changing the finite-order condition.
-/

public section

open Complex Filter Asymptotics Bornology Topology

namespace TauCeti

/-! ### The order predicate -/

/-- `f` has order at most `A`: for every `A' > A`, `f s = O(exp ‖s‖ ^ A')` as `‖s‖ → ∞`.
Entirety is not part of the predicate. -/
def OrderLE (f : ℂ → ℂ) (A : ℝ) : Prop :=
  ∀ A' > A, f =O[cobounded ℂ] fun s ↦ Real.exp (‖s‖ ^ A')

variable {f g : ℂ → ℂ} {A B : ℝ}

/-- The defining property of `OrderLE`. -/
theorem orderLE_def :
    OrderLE f A ↔ ∀ A' > A, f =O[cobounded ℂ] fun s ↦ Real.exp (‖s‖ ^ A') :=
  Iff.rfl

namespace OrderLE

/-- A function of order at most `A` is `O(exp ‖s‖ ^ A')` for every `A' > A`. -/
theorem isBigO (h : OrderLE f A) {A' : ℝ} (hA' : A < A') :
    f =O[cobounded ℂ] fun s ↦ Real.exp (‖s‖ ^ A') :=
  h A' hA'

/-- Order at most `A` implies order at most every `B ≥ A`. -/
theorem mono (h : OrderLE f A) (hAB : A ≤ B) : OrderLE f B :=
  fun A' hA' ↦ h A' (hAB.trans_lt hA')

end OrderLE

/-- A function dominated at infinity by a function of order at most `A` has order at most `A`. -/
theorem _root_.Asymptotics.IsBigO.orderLE (hfg : f =O[cobounded ℂ] g) (hg : OrderLE g A) :
    OrderLE f A :=
  fun A' hA' ↦ hfg.trans (hg A' hA')

/-- Constants have order at most `A` for every real `A`, including negative `A`. -/
@[simp]
theorem orderLE_const (c : ℂ) (A : ℝ) : OrderLE (fun _ ↦ c) A := fun A' _ ↦
  (isBigO_const_one ℝ c _).trans <| isBigO_of_le _ fun s ↦ by
    simpa using Real.one_le_exp (Real.rpow_nonneg (norm_nonneg s) A')

namespace OrderLE

/-- A sum of two functions of order at most `A` has order at most `A`. -/
theorem add (hf : OrderLE f A) (hg : OrderLE g A) : OrderLE (fun s ↦ f s + g s) A :=
  fun A' hA' ↦ (hf A' hA').add (hg A' hA')

/-- The negative of a function of order at most `A` has order at most `A`. -/
theorem neg (hf : OrderLE f A) : OrderLE (fun s ↦ -f s) A :=
  fun A' hA' ↦ (hf A' hA').neg_left

/-- A difference of two functions of order at most `A` has order at most `A`. -/
theorem sub (hf : OrderLE f A) (hg : OrderLE g A) : OrderLE (fun s ↦ f s - g s) A :=
  fun A' hA' ↦ (hf A' hA').sub (hg A' hA')

/-- A product of two functions of order at most `A` has order at most `A`. -/
theorem mul (hf : OrderLE f A) (hg : OrderLE g A) : OrderLE (fun s ↦ f s * g s) A := by
  intro A' hA'
  have h₁ : A < (A + A') / 2 := by linarith
  have h₂ : (A + A') / 2 < A' := by linarith
  refine ((hf _ h₁).mul (hg _ h₁)).trans <|
    (isBigO_exp_mul_norm_rpow 2 h₂).congr_left fun s ↦ ?_
  rw [← Real.exp_add, two_mul]

/-- A constant multiple of a function of order at most `A` has order at most `A`. -/
theorem const_mul (hf : OrderLE f A) (c : ℂ) : OrderLE (fun s ↦ c * f s) A :=
  (orderLE_const c A).mul hf

/-- A power of a function of order at most `A` has order at most `A`. -/
theorem pow (hf : OrderLE f A) (n : ℕ) : OrderLE (fun s ↦ f s ^ n) A := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hf

/-- A finite sum of functions of order at most `A` has order at most `A`. -/
theorem sum {ι : Type*} {t : Finset ι} {F : ι → ℂ → ℂ} (h : ∀ i ∈ t, OrderLE (F i) A) :
    OrderLE (fun s ↦ ∑ i ∈ t, F i s) A :=
  fun A' hA' ↦ (IsBigO.sum fun i hi ↦ h i hi A' hA').congr_left fun s ↦ Finset.sum_apply s t F

/-- A finite product of functions of order at most `A` has order at most `A`. -/
theorem prod {ι : Type*} {t : Finset ι} {F : ι → ℂ → ℂ} (h : ∀ i ∈ t, OrderLE (F i) A) :
    OrderLE (fun s ↦ ∏ i ∈ t, F i s) A := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i t)).mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- The order does not increase under an affine substitution `s ↦ a * s + b`. -/
theorem comp_mul_add (h : OrderLE f A) (a b : ℂ) : OrderLE (fun s ↦ f (a * s + b)) A := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  intro A' hA'
  have h₁ : A < (A + A') / 2 := by linarith
  have h₂ : (A + A') / 2 < A' := by linarith
  have ht : Tendsto (fun s : ℂ ↦ a * s + b) (cobounded ℂ) (cobounded ℂ) :=
    (tendsto_add_const_cobounded b).comp (tendsto_mul_left_cobounded ha)
  refine ((h _ h₁).comp_tendsto ht).trans ?_
  rcases le_or_gt ((A + A') / 2) 0 with h₀ | h₀
  · -- for a nonpositive exponent the comparison function is bounded far out
    refine IsBigO.of_bound (Real.exp 1) ?_
    filter_upwards [ht.eventually (eventually_cobounded_le_norm 1)] with s hs
    have h₃ : 1 ≤ Real.exp (‖s‖ ^ A') := Real.one_le_exp (Real.rpow_nonneg (norm_nonneg s) _)
    have h₄ : ‖a * s + b‖ ^ ((A + A') / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs h₀
    simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp]
    calc Real.exp (‖a * s + b‖ ^ ((A + A') / 2)) ≤ Real.exp 1 := Real.exp_le_exp.2 h₄
      _ ≤ Real.exp 1 * Real.exp (‖s‖ ^ A') := le_mul_of_one_le_right (Real.exp_pos 1).le h₃
  · -- for a positive exponent, `‖a * s + b‖ ≤ (‖a‖ + ‖b‖) * ‖s‖` far out
    refine (IsBigO.of_bound 1 ?_).trans (isBigO_exp_mul_norm_rpow ((‖a‖ + ‖b‖) ^ ((A + A') / 2)) h₂)
    filter_upwards [eventually_cobounded_le_norm 1] with s hs
    simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp, one_mul, Real.exp_le_exp]
    rw [← Real.mul_rpow (by positivity) (norm_nonneg s)]
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ h₀.le
    calc ‖a * s + b‖ ≤ ‖a‖ * ‖s‖ + ‖b‖ * 1 := by
          rw [mul_one, ← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖a‖ * ‖s‖ + ‖b‖ * ‖s‖ := by gcongr
      _ = (‖a‖ + ‖b‖) * ‖s‖ := by ring

/-- **Liouville's theorem for functions of negative order.** An entire function of order at most
`A < 0` is constant. -/
theorem isConst (h : OrderLE f A) (hf : Differentiable ℂ f) (hA : A < 0) : f.IsConst := by
  refine hf.isConst_of_isBigO_one ?_
  rw [← Metric.cobounded_eq_cocompact]
  refine (h 0 hA).trans <| (isBigO_const_one ℝ (Real.exp 1) _).congr_left fun s ↦ ?_
  rw [Real.rpow_zero]

end OrderLE

/-- An entire function has order at most a negative `A` if and only if it is constant. -/
theorem orderLE_iff_isConst (hf : Differentiable ℂ f) (hA : A < 0) :
    OrderLE f A ↔ f.IsConst := by
  refine ⟨fun h ↦ h.isConst hf hA, fun hc ↦ ?_⟩
  have hf₀ : f = fun _ ↦ f 0 := funext fun s ↦ hc s 0
  rw [hf₀]
  exact orderLE_const _ A

/-! ### Polynomials and exponentials -/

/-- A function that is `O(s ^ n)` at infinity has order at most `0`. -/
theorem orderLE_zero_of_isBigO_pow {n : ℕ} (h : f =O[cobounded ℂ] (· ^ n)) : OrderLE f 0 :=
  fun _ hA' ↦ h.trans <| (isBigO_of_le _ fun s ↦ by simp).trans
    (isBigO_norm_pow_exp_norm_rpow n hA')

/-- A polynomial has order at most `0`. -/
theorem _root_.Polynomial.orderLE_eval (p : Polynomial ℂ) : OrderLE p.eval 0 :=
  orderLE_zero_of_isBigO_pow p.isBigO_cobounded_pow_natDegree

/-- `exp (a * s ^ n)` has order at most `n`, for every `a : ℂ`. -/
theorem orderLE_cexp_mul_pow (a : ℂ) (n : ℕ) : OrderLE (fun s ↦ cexp (a * s ^ n)) n := by
  intro A' hA'
  refine (isBigO_of_le _ fun s ↦ ?_).trans (isBigO_exp_mul_norm_rpow ‖a‖ hA')
  rw [norm_exp, Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp, Real.rpow_natCast]
  calc (a * s ^ n).re ≤ ‖a * s ^ n‖ := re_le_norm _
    _ = ‖a‖ * ‖s‖ ^ n := by rw [norm_mul, norm_pow]

/-- `exp (a * s)` has order at most `1`, for every `a : ℂ`. -/
theorem orderLE_cexp_mul (a : ℂ) : OrderLE (fun s ↦ cexp (a * s)) 1 := by
  simpa using orderLE_cexp_mul_pow a 1

/-- For `n ≠ 0`, `exp (s ^ n)` has order at most `A` exactly when `n ≤ A`: along the positive
reals `exp (x ^ n)` outgrows `exp (x ^ A')` for every `A' < n`. -/
@[simp]
theorem orderLE_cexp_pow_iff {n : ℕ} (hn : n ≠ 0) :
    OrderLE (fun s ↦ cexp (s ^ n)) A ↔ (n : ℝ) ≤ A := by
  refine ⟨fun h ↦ ?_, fun hA ↦ by simpa using (orderLE_cexp_mul_pow 1 n).mono hA⟩
  by_contra! hA
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set A' := (max A 0 + n) / 2 with hA'
  have h₁ : A < A' := by have := le_max_left A 0; linarith
  have h₀ : 0 < A' := by have := le_max_right A 0; linarith
  have h₂ : A' < n := by have := max_lt hA hn'; linarith
  have ht := RCLike.tendsto_ofReal_atTop_cobounded ℂ
  -- along the positive reals, `exp (2 x ^ A') ≤ C exp (x ^ n) ≤ C' exp (x ^ A')`
  have hlow : (fun x : ℝ ↦ Real.exp (‖(x : ℂ)‖ ^ (n : ℝ))) =O[atTop]
      fun x : ℝ ↦ cexp ((x : ℂ) ^ n) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [norm_exp, ← ofReal_pow, abs_of_nonneg hx]
  have hO : (fun x : ℝ ↦ Real.exp (2 * ‖(x : ℂ)‖ ^ A')) =O[atTop]
      fun x : ℝ ↦ Real.exp (‖(x : ℂ)‖ ^ A') :=
    (((isBigO_exp_mul_norm_rpow 2 h₂).comp_tendsto ht).trans hlow).trans
      ((h A' h₁).comp_tendsto ht)
  rw [Real.isBigO_exp_comp_exp_comp] at hO
  refine not_isBoundedUnder_of_tendsto_atTop ?_ hO
  have hnorm : Tendsto (fun x : ℝ ↦ ‖(x : ℂ)‖) atTop atTop :=
    tendsto_norm_atTop_iff_cobounded.2 ht
  refine ((tendsto_rpow_atTop h₀).comp hnorm).congr fun x ↦ ?_
  simp only [Function.comp_apply, Pi.sub_apply]
  ring

/-- The exponential function has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_cexp_iff : OrderLE cexp A ↔ 1 ≤ A := by
  simpa using orderLE_cexp_pow_iff (A := A) one_ne_zero

/-! ### Finite order -/

/-- A function has finite order if it has order at most some real exponent.
Entirety is not part of this predicate. -/
def IsFiniteOrder (f : ℂ → ℂ) : Prop := ∃ A, OrderLE f A

/-- The defining characterization of finite order. -/
theorem isFiniteOrder_def : IsFiniteOrder f ↔ ∃ A, OrderLE f A := Iff.rfl

/-- Any upper bound on the order witnesses finite order. -/
theorem OrderLE.isFiniteOrder (hf : OrderLE f A) : IsFiniteOrder f := ⟨A, hf⟩

/-- Domination at infinity preserves finite order. -/
theorem _root_.Asymptotics.IsBigO.isFiniteOrder (hfg : f =O[cobounded ℂ] g)
    (hg : IsFiniteOrder g) : IsFiniteOrder f := by
  obtain ⟨A, hA⟩ := hg
  exact (hfg.orderLE hA).isFiniteOrder

/-- Constants have finite order. -/
@[simp]
theorem isFiniteOrder_const (c : ℂ) : IsFiniteOrder (fun _ ↦ c) :=
  (orderLE_const c 0).isFiniteOrder

namespace IsFiniteOrder

/-- Two functions of finite order admit a common nonnegative upper bound on their orders. -/
theorem exists_common_orderLE (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    ∃ A ≥ 0, OrderLE f A ∧ OrderLE g A := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨max 0 (max A B), le_max_left _ _,
    hA.mono ((le_max_left A B).trans (le_max_right _ _)),
    hB.mono ((le_max_right A B).trans (le_max_right _ _))⟩

/-- The sum of two functions of finite order has finite order. -/
theorem add (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    IsFiniteOrder (fun s ↦ f s + g s) := by
  obtain ⟨A, _, hA, hB⟩ := hf.exists_common_orderLE hg
  exact (hA.add hB).isFiniteOrder

/-- Negation preserves finite order. -/
theorem neg (hf : IsFiniteOrder f) : IsFiniteOrder (fun s ↦ -f s) := by
  obtain ⟨A, hA⟩ := hf
  exact hA.neg.isFiniteOrder

/-- The difference of two functions of finite order has finite order. -/
theorem sub (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    IsFiniteOrder (fun s ↦ f s - g s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The product of two functions of finite order has finite order. -/
theorem mul (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    IsFiniteOrder (fun s ↦ f s * g s) := by
  obtain ⟨A, _, hA, hB⟩ := hf.exists_common_orderLE hg
  exact (hA.mul hB).isFiniteOrder

/-- Multiplication by a constant preserves finite order. -/
theorem const_mul (hf : IsFiniteOrder f) (c : ℂ) :
    IsFiniteOrder (fun s ↦ c * f s) :=
  (isFiniteOrder_const c).mul hf

/-- Natural powers preserve finite order. -/
theorem pow (hf : IsFiniteOrder f) (n : ℕ) : IsFiniteOrder (fun s ↦ f s ^ n) := by
  obtain ⟨A, hA⟩ := hf
  exact (hA.pow n).isFiniteOrder

/-- A finite sum of functions of finite order has finite order. -/
theorem sum {ι : Type*} {t : Finset ι} {F : ι → ℂ → ℂ}
    (h : ∀ i ∈ t, IsFiniteOrder (F i)) : IsFiniteOrder (fun s ↦ ∑ i ∈ t, F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- A finite product of functions of finite order has finite order. -/
theorem prod {ι : Type*} {t : Finset ι} {F : ι → ℂ → ℂ}
    (h : ∀ i ∈ t, IsFiniteOrder (F i)) : IsFiniteOrder (fun s ↦ ∏ i ∈ t, F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i t)).mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- An affine pullback of a function of finite order has finite order, even for a constant map. -/
theorem comp_mul_add (hf : IsFiniteOrder f) (a b : ℂ) :
    IsFiniteOrder (fun s ↦ f (a * s + b)) := by
  obtain ⟨A, hA⟩ := hf
  exact (hA.comp_mul_add a b).isFiniteOrder

end IsFiniteOrder

/-- An invertible affine substitution preserves finite order in both directions. -/
@[simp]
theorem isFiniteOrder_comp_mul_add_iff {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsFiniteOrder (fun s ↦ f (a * s + b)) ↔ IsFiniteOrder f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_mul_add a b⟩
  have h' := h.comp_mul_add a⁻¹ (-(a⁻¹ * b))
  simpa [mul_add, ← mul_assoc, ha] using h'

/-- Polynomials have finite order. -/
theorem _root_.Polynomial.isFiniteOrder_eval (p : Polynomial ℂ) : IsFiniteOrder p.eval :=
  p.orderLE_eval.isFiniteOrder

/-- A nonzero polynomial factor can be cancelled when testing finite order.
No continuity or analyticity assumption on the other factor is needed. -/
@[simp]
theorem _root_.Polynomial.isFiniteOrder_eval_mul_iff (p : Polynomial ℂ) (hp : p ≠ 0) :
    IsFiniteOrder (fun s ↦ p.eval s * f s) ↔ IsFiniteOrder f := by
  refine ⟨fun h ↦ ?_, fun h ↦ p.isFiniteOrder_eval.mul h⟩
  have hP : (fun _ : ℂ ↦ (1 : ℂ)) =O[cobounded ℂ] p.eval := by
    simpa using Polynomial.isBigO_cobounded_of_degree_le
      (P := (1 : Polynomial ℂ)) (Q := p)
      (Polynomial.degree_one_le.trans (Polynomial.zero_le_degree_iff.mpr hp))
  simpa only [one_mul] using (hP.mul (isBigO_refl f _)).isFiniteOrder h

/-- The exponential of a monomial has finite order, regardless of its degree. -/
theorem isFiniteOrder_cexp_mul_pow (a : ℂ) (n : ℕ) :
    IsFiniteOrder (fun s ↦ cexp (a * s ^ n)) :=
  (orderLE_cexp_mul_pow a n).isFiniteOrder

/-- The iterated exponential does not have finite order: on the positive real axis,
its logarithmic norm outgrows every power. -/
@[simp]
theorem not_isFiniteOrder_cexp_cexp : ¬ IsFiniteOrder (fun s ↦ cexp (cexp s)) := by
  rintro ⟨A, hA⟩
  let B := max A 0 + 1
  have hAB : A < B := by dsimp [B]; linarith [le_max_left A 0]
  have hO := ((hA B hAB).comp_tendsto
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ)).norm_left
  have hreal : (fun x : ℝ ↦ Real.exp (Real.exp x)) =O[atTop]
      (fun x : ℝ ↦ Real.exp (|x| ^ B)) := by
    simpa [Function.comp_def, ← Complex.ofReal_exp] using hO
  rw [Real.isBigO_exp_comp_exp_comp] at hreal
  have hsmall := (isLittleO_rpow_exp_atTop B).bound (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : Tendsto (fun x : ℝ ↦ Real.exp x - |x| ^ B) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (Real.tendsto_exp_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall, eventually_ge_atTop 0] with x hx hx0
    simp only [Real.norm_eq_abs, Real.abs_exp] at hx
    rw [abs_of_nonneg hx0]
    have hp := Real.rpow_nonneg hx0 B
    rw [abs_of_nonneg hp] at hx
    linarith
  exact not_isBoundedUnder_of_tendsto_atTop ht hreal

end TauCeti
