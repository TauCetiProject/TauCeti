/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Rolle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Sign.Defs

/-! # Thom sign conditions from polynomial Rolle

Sign conditions on all formal derivatives are order-convex. Consequently the
signs of the positive-order derivatives distinguish roots of a nonzero
polynomial, including multiple roots. No squarefreeness assumption is needed.
The finite Thom encoding records derivatives 1 through `natDegree`. The last
differing derivative sign and the next common sign determine the order of two points.
The only extra premise on the ordered field is polynomial Rolle, supplied by
`TauCeti.RealClosure.polynomialRolle_of_isRealClosed` over every real closed ordered field.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Propositions 2.27 and 2.28 (Thom's lemma and root encodings).
-/

public section

open TauCeti (PolynomialRolle)

open Polynomial SignType Set

namespace Polynomial

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The sign of the `k`th formal derivative at `x`, including order zero. -/
noncomputable def derivativeSign (p : R[X]) (x : R) (k : ℕ) : SignType :=
  sign ((derivative^[k] p).eval x)

/-- Derivative signs are signs of evaluations of iterated formal derivatives. -/
theorem derivativeSign_def (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = sign ((derivative^[k] p).eval x) := (rfl)

@[grind =]
theorem derivativeSign_eq_one_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = 1 ↔ 0 < (derivative^[k] p).eval x := by
  rw [derivativeSign_def, sign_eq_one_iff]

@[grind =]
theorem derivativeSign_eq_neg_one_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = -1 ↔ (derivative^[k] p).eval x < 0 := by
  rw [derivativeSign_def, sign_eq_neg_one_iff]

@[simp, grind =]
theorem derivativeSign_eq_zero_iff (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = 0 ↔ (derivative^[k] p).eval x = 0 := by
  rw [derivativeSign_def, sign_eq_zero_iff]

theorem derivativeSign_ne_zero (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k ≠ 0 ↔ (derivative^[k] p).eval x ≠ 0 :=
  not_congr (derivativeSign_eq_zero_iff p x k)

@[simp, grind =]
theorem derivativeSign_zero (x : R) (k : ℕ) : derivativeSign (0 : R[X]) x k = 0 := by
  simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_index_zero (p : R[X]) (x : R) :
    derivativeSign p x 0 = sign (p.eval x) := by
  simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_eq_zero (p : R[X]) (x : R) {k : ℕ} (hk : p.natDegree < k) :
    derivativeSign p x k = 0 := by
  simp [derivativeSign_def, iterate_derivative_eq_zero hk]

@[simp, grind =]
theorem derivativeSign_C (a x : R) (k : ℕ) :
    derivativeSign (C a) x k = if k = 0 then sign a else 0 := by
  cases k with
  | zero => simp [derivativeSign_def]
  | succ k => simp

/-- Taking one derivative advances the derivative-sign index by one. -/
@[simp, grind =]
theorem derivativeSign_derivative (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p.derivative x k = derivativeSign p x (k + 1) := by
  simp only [derivativeSign_def, Function.iterate_succ_apply]

/-- Shifting the polynomial shifts the derivative index. -/
@[simp, grind =]
theorem derivativeSign_iterate_derivative (p : R[X]) (x : R) (i j : ℕ) :
    derivativeSign (derivative^[i] p) x j = derivativeSign p x (j + i) := by
  simp only [derivativeSign_def, Function.iterate_add_apply]

/-- The usual finite Thom encoding retains derivatives 1 through the degree. -/
noncomputable def thomEncoding (p : R[X]) (x : R) : Fin p.natDegree → SignType :=
  fun i => derivativeSign p x (i.val + 1)

/-- Coordinate `i` records the sign of derivative `i + 1`. -/
@[simp, grind =]
theorem thomEncoding_apply (p : R[X]) (x : R) (i : Fin p.natDegree) :
    thomEncoding p x i = derivativeSign p x (i.val + 1) := (rfl)

/-- A finite Thom word consists of the signs of derivatives 1 through the degree. -/
theorem thomEncoding_def (p : R[X]) (x : R) :
    thomEncoding p x = fun i => sign ((derivative^[i.val + 1] p).eval x) := by
  funext i
  rw [thomEncoding_apply, derivativeSign_def]

private theorem derivativeSign_tail (p : R[X]) {a b : R} {n : ℕ}
    (h : ∀ i : Fin p.natDegree, n < i.val + 1 → thomEncoding p a i = thomEncoding p b i)
    (k : ℕ) (hk : n < k) : derivativeSign p a k = derivativeSign p b k := by
  by_cases hd : k ≤ p.natDegree
  · have hkpos : 1 ≤ k := by omega
    have he := h ⟨k - 1, by omega⟩
      (by simpa only [Fin.val_mk, Nat.sub_add_cancel hkpos] using hk)
    simpa only [thomEncoding_apply, Nat.sub_add_cancel hkpos] using he
  · simp [derivativeSign_eq_zero p _ (by omega : p.natDegree < k)]

/-- Finite Thom encodings agree exactly when all positive-order derivative signs agree. -/
theorem thomEncoding_eq_iff (p : R[X]) (a b : R) :
    thomEncoding p a = thomEncoding p b ↔
      ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k := by
  constructor
  · intro h
    exact derivativeSign_tail p (fun i _ => congrFun h i)
  · intro h
    funext i
    simp only [thomEncoding_apply]
    exact h (i.val + 1) (Nat.succ_pos _)

/-- At and above the degree the derivative is constant, so its sign is
independent of the point. -/
theorem derivativeSign_const (p : R[X]) (a b : R) {k : ℕ} (hk : p.natDegree ≤ k) :
    derivativeSign p a k = derivativeSign p b k := by
  have hd : (derivative^[k] p).natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_iterate_derivative p k).trans (by omega))
  simp only [derivativeSign_def]
  rw [eq_C_of_natDegree_eq_zero hd]
  simp

/-- A differing finite Thom coordinate lies below the top derivative,
so a next coordinate exists. -/
theorem thomEncoding_succ_lt_natDegree (p : R[X]) {a b : R} {i : Fin p.natDegree}
    (hne : thomEncoding p a i ≠ thomEncoding p b i) : i.val + 1 < p.natDegree := by
  by_contra! hi
  simp only [thomEncoding_apply] at hne
  exact hne (derivativeSign_const p a b hi)

/-- Distinct Thom encodings have a last disagreement strictly below the degree.
All larger derivative signs agree, including the highest derivative sign.
For distinct roots, `thomEncoding_injOn` supplies the unequal encodings. -/
theorem exists_derivativeSign_ne (p : R[X]) {a b : R}
    (henc : thomEncoding p a ≠ thomEncoding p b) :
    ∃ k, 0 < k ∧ k < p.natDegree ∧
      derivativeSign p a k ≠ derivativeSign p b k ∧
      ∀ j, k < j → derivativeSign p a j = derivativeSign p b j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp henc
  let s := (Finset.range (p.natDegree + 1)).filter
    (fun j => derivativeSign p a j ≠ derivativeSign p b j)
  have hi_mem : i.val + 1 ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa only [thomEncoding_apply] using hi⟩
  have hs : s.Nonempty := ⟨i.val + 1, hi_mem⟩
  let k := s.max' hs
  have hk : k ∈ s := Finset.max'_mem s hs
  have hk' := (Finset.mem_filter.mp hk).2
  have hpos : 0 < k := (Nat.succ_pos i.val).trans_le (Finset.le_max' s _ hi_mem)
  have hdeg : k < p.natDegree := by
    by_contra hn
    exact hk' (derivativeSign_const p a b (by omega))
  refine ⟨k, hpos, hdeg, hk', ?_⟩
  intro j hj
  by_cases hd : p.natDegree ≤ j
  · exact derivativeSign_const p a b hd
  · by_contra hne
    have hjs : j ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hne⟩
    have hle : j ≤ k := Finset.le_max' s j hjs
    omega

/-- Distinct finite Thom encodings have a last differing coordinate. -/
theorem exists_thomEncoding_ne (p : R[X]) {a b : R}
    (henc : thomEncoding p a ≠ thomEncoding p b) :
    ∃ i : Fin p.natDegree, thomEncoding p a i ≠ thomEncoding p b i ∧
      ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j := by
  obtain ⟨k, hk, hkd, hne, ht⟩ := exists_derivativeSign_ne p henc
  refine ⟨⟨k - 1, by omega⟩, ?_, ?_⟩
  · simpa only [thomEncoding_apply, Nat.sub_add_cancel hk] using hne
  · intro j hj
    simp only [Fin.lt_def] at hj
    simpa only [thomEncoding_apply] using ht (j.val + 1) (by omega)

end Basic

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem sign_between_aux (hrolle : PolynomialRolle R) (n : ℕ) (p : R[X])
    (hn : derivative^[n] p = 0) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) := by
  have hab := hx.1.trans hx.2
  induction n generalizing p x with
  | zero =>
    have hp : p = 0 := by simpa only [Function.iterate_zero_apply] using hn
    simp [hp]
  | succ n ih =>
    have hd : derivative^[n] p.derivative = 0 := by
      simpa only [Function.iterate_succ_apply] using hn
    have hs : ∀ k, derivativeSign p.derivative a k = derivativeSign p.derivative b k := by
      intro k
      simpa only [derivativeSign_derivative] using h (k + 1)
    have hd_sign (y : R) (hy : y ∈ Icc a b) :
        sign (p.derivative.eval y) = sign (p.derivative.eval a) := ih p.derivative hd hy hs
    have h0 : sign (p.eval a) = sign (p.eval b) := by
      simpa only [derivativeSign_index_zero] using h 0
    rcases le_total 0 (p.derivative.eval a) with hp | hp
    · have hm : MonotoneOn p.eval (Icc a b) :=
        hrolle.monotoneOn p (by
            intro y hy
            rw [← sign_nonneg_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
            exact sign_nonneg_iff.mpr hp)
      exact le_antisymm ((sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)).trans_eq h0.symm)
        (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
    · have hm : AntitoneOn p.eval (Icc a b) :=
        hrolle.antitoneOn p (by
            intro y hy
            rw [← sign_nonpos_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
            exact sign_nonpos_iff.mpr hp)
      exact le_antisymm (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
        (h0.trans_le (sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)))

/-- Equal derivative sign vectors at the endpoints force the sign of the polynomial
itself to be constant on the interval. -/
private theorem sign_between (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) :=
  sign_between_aux hrolle (p.natDegree + 1) p (iterate_derivative_eq_zero (by omega))
    hx h

/-- Agreement of all derivative signs from index `k` onward forces the sign at
index `k` to be constant between the endpoints. -/
theorem derivativeSign_eq_on_Icc (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R}
    (hx : x ∈ Icc a b) {k : ℕ}
    (h : ∀ j, k ≤ j → derivativeSign p a j = derivativeSign p b j) :
    derivativeSign p x k = derivativeSign p a k := by
  apply sign_between (derivative^[k] p) hrolle hx
  intro j
  simp only [derivativeSign_iterate_derivative]
  exact h (j + k) (Nat.le_add_left _ _)

/-- A full derivative sign condition is order-convex. Empty conditions are
allowed; this statement does not assert that an arbitrary word is realizable. -/
theorem ordConnected_preimage_derivativeSign (p : R[X]) (hrolle : PolynomialRolle R)
    (σ : ℕ → SignType) :
    OrdConnected (derivativeSign p ⁻¹' {σ}) := by
  constructor
  intro a ha b hb x hx
  funext k
  exact (derivativeSign_eq_on_Icc p hrolle hx
    (fun j _ => congrFun (ha.trans hb.symm) j)).trans (congrFun ha k)

/-- A finite Thom sign condition is order-convex, including unrealized conditions. -/
theorem ordConnected_preimage_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R)
    (τ : Fin p.natDegree → SignType) : OrdConnected (thomEncoding p ⁻¹' {τ}) := by
  constructor
  intro a ha b hb x hx
  apply Eq.trans ?_ ha
  apply (thomEncoding_eq_iff p x a).mpr
  intro k hk
  exact derivativeSign_eq_on_Icc p hrolle hx
    (fun j hj => (thomEncoding_eq_iff p a b).mp (ha.trans hb.symm) j (hk.trans_le hj))

/-- Roots with equal signs of every positive-order derivative are equal.
The polynomial need not be squarefree. -/
theorem eq_of_derivativeSign_eq (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hs : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) : a = b := by
  have h (k : ℕ) : derivativeSign p a k = derivativeSign p b k := by
    cases k with
    | zero => simp [derivativeSign_def, ha, hb]
    | succ k => exact hs _ (Nat.succ_pos _)
  have no_lt {u v : R} (hu : p.eval u = 0)
      (hσ : ∀ k, derivativeSign p u k = derivativeSign p v k) (huv : u < v) : False := by
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    apply (Ioo_infinite huv).mono
    intro x hx
    apply sign_eq_zero_iff.mp
    simpa only [hu, sign_zero] using sign_between p hrolle ⟨hx.1.le, hx.2.le⟩ hσ
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (no_lt ha h hab).elim
  · exact hab
  · exact (no_lt hb (fun k => (h k).symm) hba).elim

/-- A finite Thom encoding uniquely identifies a root of a nonzero polynomial. -/
theorem thomEncoding_injOn (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) :
    Set.InjOn (thomEncoding p) {x | p.eval x = 0} := by
  intro a ha b hb h
  apply eq_of_derivativeSign_eq p hrolle hp ha hb
  exact (thomEncoding_eq_iff p a b).mp h

private theorem sign_order_aux (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} (hab : a < b)
    (hne : sign (p.eval a) ≠ sign (p.eval b))
    (htail : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) :
    (sign (p.derivative.eval a) = 1 ∧ sign (p.eval a) < sign (p.eval b)) ∨
    (sign (p.derivative.eval a) = -1 ∧ sign (p.eval b) < sign (p.eval a)) := by
  have hd (x : R) (hx : x ∈ Icc a b) :
      sign (p.derivative.eval x) = sign (p.derivative.eval a) := by
    simpa only [derivativeSign_def, Function.iterate_one] using
      derivativeSign_eq_on_Icc p hrolle hx (k := 1) (fun j hj => htail j hj)
  rcases lt_trichotomy (p.derivative.eval a) 0 with hn | hz | hp
  · have hm : StrictAntiOn p.eval (Icc a b) :=
      hrolle.strictAntiOn p (by
        intro x hx
        rw [← sign_eq_neg_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
        exact sign_neg hn)
    exact Or.inr ⟨sign_neg hn,
      lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne.symm⟩
  · have hp0 : p.derivative = 0 := by
      apply p.derivative.eq_zero_of_infinite_isRoot
      apply (Ioo_infinite hab).mono
      intro x hx
      apply sign_eq_zero_iff.mp
      simpa only [hz, sign_zero] using hd x ⟨hx.1.le, hx.2.le⟩
    have hc := eq_C_of_derivative_eq_zero hp0
    exact (hne (by rw [hc]; simp)).elim
  · have hm : StrictMonoOn p.eval (Icc a b) :=
      hrolle.strictMonoOn p (by
        intro x hx
        rw [← sign_eq_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
        exact sign_pos hp)
    exact Or.inl ⟨sign_pos hp,
      lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne⟩

/-- At the largest derivative index where signs differ, the next common sign
and the two differing signs determine the order of the points. -/
theorem lt_iff_derivativeSign (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    (a < b ↔
      (derivativeSign p a (k + 1) = 1 ∧ derivativeSign p a k < derivativeSign p b k) ∨
      (derivativeSign p a (k + 1) = -1 ∧ derivativeSign p b k < derivativeSign p a k)) := by
  have forward {u v : R} (huv : u < v)
      (hne : derivativeSign p u k ≠ derivativeSign p v k)
      (ht : ∀ j, k < j → derivativeSign p u j = derivativeSign p v j) :
      (derivativeSign p u (k + 1) = 1 ∧ derivativeSign p u k < derivativeSign p v k) ∨
      (derivativeSign p u (k + 1) = -1 ∧ derivativeSign p v k < derivativeSign p u k) := by
    simp only [derivativeSign_def] at hne
    have h := sign_order_aux (derivative^[k] p) hrolle huv hne (by
      intro j hj
      rw [derivativeSign_iterate_derivative, derivativeSign_iterate_derivative]
      exact ht _ (by omega))
    simpa only [derivativeSign_def, Function.iterate_succ_apply'] using h
  constructor
  · exact fun hab => forward hab hne htail
  · intro h
    rcases lt_trichotomy a b with hab | hab | hba
    · exact hab
    · subst b; exact (hne rfl).elim
    · have hrev := forward hba hne.symm (fun j hj => (htail j hj).symm)
      have heq := htail (k + 1) (by omega)
      rcases h with ⟨hpos, hlt⟩ | ⟨hneg, hlt⟩ <;>
        rcases hrev with ⟨hpos', hlt'⟩ | ⟨hneg', hlt'⟩
      · exact (lt_asymm hlt hlt').elim
      · rw [← heq, hpos] at hneg'; cases hneg'
      · rw [← heq, hneg] at hpos'; cases hpos'
      · exact (lt_asymm hlt hlt').elim

/-- The comparison rule directly on finite Thom words. `thomEncoding_succ_lt_natDegree` supplies
existence of the next coordinate from the differing signs. Every coordinate
above the disagreement must agree. -/
theorem lt_iff_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (i : Fin p.natDegree)
    (hne : thomEncoding p a i ≠ thomEncoding p b i)
    (htail : ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j) :
    (a < b ↔
      (thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ = 1 ∧
        thomEncoding p a i < thomEncoding p b i) ∨
      (thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ = -1 ∧
        thomEncoding p b i < thomEncoding p a i)) := by
  simp only [thomEncoding_apply] at hne ⊢
  apply lt_iff_derivativeSign p hrolle hne
  exact derivativeSign_tail p (fun j hj => htail j (Nat.lt_of_succ_lt_succ hj))

/-- The common sign immediately above the last disagreement cannot be zero. -/
theorem derivativeSign_succ_ne_zero (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    derivativeSign p a (k + 1) ≠ 0 := by
  have hab : a ≠ b := fun h => hne (congrArg (fun x => derivativeSign p x k) h)
  rcases hab.lt_or_gt with hlt | hlt
  · rcases (lt_iff_derivativeSign p hrolle hne htail).mp hlt with h | h <;>
      simp only [h.1, ne_eq, reduceCtorEq, not_false_eq_true]
  · have ht := fun j hj => (htail j hj).symm
    rw [htail (k + 1) (by omega)]
    rcases (lt_iff_derivativeSign p hrolle hne.symm ht).mp hlt with h | h <;>
      simp only [h.1, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The common finite Thom coordinate immediately above the last disagreement is nonzero. -/
theorem thomEncoding_succ_ne_zero (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (i : Fin p.natDegree)
    (hne : thomEncoding p a i ≠ thomEncoding p b i)
    (htail : ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j) :
    thomEncoding p a ⟨i.val + 1, thomEncoding_succ_lt_natDegree p hne⟩ ≠ 0 := by
  simp only [thomEncoding_apply] at hne ⊢
  exact derivativeSign_succ_ne_zero p hrolle hne
    (derivativeSign_tail p (fun j hj => htail j (Nat.lt_of_succ_lt_succ hj)))


end Polynomial
