/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Matrices raising a degree, and uniqueness of ordered unipotent products

Give the index set `η` of a square matrix an integer degree `deg : η → ℤ`. A matrix `X`
*raises the degree by at least `d`*, `Matrix.RaisesDegree deg d X`, when every nonzero entry
`X r s` has `deg s + d ≤ deg r`. These conditions form a multiplicative filtration of the matrix
ring: degrees add under multiplication.

The main result is a uniqueness theorem for ordered products of one-parameter families of the
shape `x i t = 1 + t • X i + (higher-degree terms)`, the shape of a root subgroup of a Chevalley
group written in a weight basis. Suppose the basis indices carry weights `wt : η → G`, that each
`X i` shifts weights by exactly `α i`, that the weights `α i` occurring in a list `l` are distinct
and of positive degree for an additive `degree : G →+ ℤ`, and that `c • X i = 0` forces `c = 0`.
Then the ordered product `∏_{i ∈ l} x i (u i)` determines every parameter `u i`
(`TauCeti.Matrix.list_prod_map_inj_of_raisesDegree`). The proof compares the two products modulo the
matrices raising the degree by more than the smallest degree at which the parameters differ;
at that degree the product is the sum of its linear terms `u i • X i`, which are independent
because they shift weights differently. No commutator formula is used.

## Main declarations

* `Matrix.RaisesDegree`: the degree-raising condition, with its closure properties.
* `Matrix.RaisesDegree.mul`: degrees add under multiplication.
* `Matrix.RaisesDegree.of_shift`: a matrix shifting weights by `a` raises their degree by
  `degree a`.
* `TauCeti.Matrix.list_prod_map_inj_of_raisesDegree`: an ordered product of graded unipotent
  families determines its parameters.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace Matrix

variable {η A : Type*} {deg : η → ℤ} {d d' : ℤ}

section Zero

variable [Zero A] {X : Matrix η η A}

/-- A square matrix **raises the degree `deg` by at least `d`** when each of its nonzero entries
`X r s` satisfies `deg s + d ≤ deg r`. -/
def RaisesDegree (deg : η → ℤ) (d : ℤ) (X : Matrix η η A) : Prop :=
  ∀ r s, X r s ≠ 0 → deg s + d ≤ deg r

/-- Unfolding `Matrix.RaisesDegree` into its entrywise condition. -/
theorem raisesDegree_iff : RaisesDegree deg d X ↔ ∀ r s, X r s ≠ 0 → deg s + d ≤ deg r :=
  Iff.rfl

/-- The entries of a degree-raising matrix vanish where the degree does not rise enough. -/
theorem RaisesDegree.apply_eq_zero (hX : RaisesDegree deg d X) {r s : η}
    (hrs : deg r < deg s + d) : X r s = 0 :=
  not_not.mp fun hne ↦ (hX r s hne).not_gt hrs

variable (deg d) in
/-- The zero matrix raises every degree by any amount. -/
@[simp] theorem raisesDegree_zero : RaisesDegree deg d (0 : Matrix η η A) :=
  fun _ _ h ↦ (h rfl).elim

variable (deg) in
/-- The identity matrix raises the degree by any nonpositive amount. -/
theorem raisesDegree_one [One A] [DecidableEq η] (hd : d ≤ 0) :
    RaisesDegree deg d (1 : Matrix η η A) := by
  intro r s h
  obtain rfl : r = s := by_contra fun hrs ↦ h (one_apply_ne hrs)
  omega

/-- Raising the degree by at least `d` implies raising it by at least any `d' ≤ d`. -/
theorem RaisesDegree.mono (hX : RaisesDegree deg d X) (hd : d' ≤ d) : RaisesDegree deg d' X :=
  fun r s h ↦ (add_le_add_right hd _).trans (hX r s h)

/-- A matrix shifting weights `wt : η → G` by exactly `a` raises the degree `degree ∘ wt` by
`degree a`. -/
theorem RaisesDegree.of_shift {G : Type*} [AddCommGroup G] {wt : η → G} (degree : G →+ ℤ)
    {a : G} (hX : ∀ r s, X r s ≠ 0 → wt r = wt s + a) :
    RaisesDegree (degree ∘ wt) (degree a) X := by
  intro r s h
  simp [hX r s h]

end Zero

/-- Matrices raising the degree by at least `d` are closed under addition. -/
theorem RaisesDegree.add [AddZeroClass A] {X Y : Matrix η η A} (hX : RaisesDegree deg d X)
    (hY : RaisesDegree deg d Y) : RaisesDegree deg d (X + Y) := by
  intro r s h
  by_cases hXrs : X r s = 0
  · exact hY r s fun hY0 ↦ h (by simp [hXrs, hY0])
  · exact hX r s hXrs

/-- Matrices raising the degree by at least `d` are closed under negation. -/
theorem RaisesDegree.neg [NegZeroClass A] {X : Matrix η η A} (hX : RaisesDegree deg d X) :
    RaisesDegree deg d (-X) :=
  fun r s h ↦ hX r s fun h0 ↦ h (by simp [h0])

/-- Matrices raising the degree by at least `d` are closed under subtraction. -/
theorem RaisesDegree.sub [SubNegZeroMonoid A] {X Y : Matrix η η A} (hX : RaisesDegree deg d X)
    (hY : RaisesDegree deg d Y) : RaisesDegree deg d (X - Y) := by
  intro r s h
  by_cases hXrs : X r s = 0
  · exact hY r s fun hY0 ↦ h (by simp [hXrs, hY0])
  · exact hX r s hXrs

/-- A matrix differing from the identity by a matrix that raises the degree by at least `0`
raises the degree by at least `0` itself. -/
theorem RaisesDegree.of_sub_one [AddGroupWithOne A] [DecidableEq η] {Y : Matrix η η A}
    (hY : RaisesDegree deg 0 (Y - 1)) : RaisesDegree deg 0 Y := by
  simpa using hY.add (raisesDegree_one deg le_rfl)

/-- Matrices raising the degree by at least `d` are closed under left scalar multiplication. -/
theorem RaisesDegree.smul [MulZeroClass A] {X : Matrix η η A} (hX : RaisesDegree deg d X) (c : A) :
    RaisesDegree deg d (c • X) :=
  fun r s h ↦ hX r s fun h0 ↦ h (by simp [h0])

/-- Matrices raising the degree by at least `d` are closed under finite sums. -/
theorem RaisesDegree.sum [AddCommMonoid A] {ι : Type*} {s : Finset ι} {X : ι → Matrix η η A}
    (hX : ∀ i ∈ s, RaisesDegree deg d (X i)) : RaisesDegree deg d (∑ i ∈ s, X i) := by
  intro r t h
  rw [Matrix.sum_apply] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hX i hi r t hne

/-- **Degrees add under multiplication.** -/
theorem RaisesDegree.mul [NonUnitalNonAssocSemiring A] [Fintype η] {X Y : Matrix η η A}
    (hX : RaisesDegree deg d X) (hY : RaisesDegree deg d' Y) :
    RaisesDegree deg (d + d') (X * Y) := by
  intro r s h
  rw [Matrix.mul_apply] at h
  obtain ⟨t, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hr := hX r t (left_ne_zero_of_mul hne)
  have hs := hY t s (right_ne_zero_of_mul hne)
  omega

/-! ## Uniqueness of ordered products -/

section OrderedProduct

variable [Fintype η] [DecidableEq η] [Ring A]
variable {ι G : Type*} [AddCommGroup G]
variable {wt : η → G} {degree : G →+ ℤ} {α : ι → G}
variable {x : ι → A → Matrix η η A} {X : ι → Matrix η η A}

variable {l : List ι}
variable (hpos : ∀ i ∈ l, 0 < degree (α i))
variable (hX : ∀ i ∈ l, RaisesDegree (degree ∘ wt) (degree (α i)) (X i))
variable (hx : ∀ i ∈ l, ∀ t, RaisesDegree (degree ∘ wt) (degree (α i) + 1) (x i t - 1 - t • X i))
include hX hx

omit [Fintype η] in
/-- Each factor differs from the identity by a matrix raising the degree by `degree (α i)`. -/
private theorem raisesDegree_sub_one {i : ι} (hi : i ∈ l) (t : A) :
    RaisesDegree (degree ∘ wt) (degree (α i)) (x i t - 1) := by
  have h : x i t - 1 = (x i t - 1 - t • X i) + t • X i := by abel
  rw [h]
  exact ((hx i hi t).mono (by omega)).add ((hX i hi).smul t)

include hpos

/-- An ordered product of the factors differs from the identity by a strictly degree-raising
matrix. -/
private theorem raisesDegree_list_prod_sub_one (u : ι → A) :
    RaisesDegree (degree ∘ wt) 1 ((l.map fun i ↦ x i (u i)).prod - 1) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj := raisesDegree_sub_one hX hx List.mem_cons_self (u j)
    have hjpos := hpos j List.mem_cons_self
    simp only [List.mem_cons, forall_eq_or_imp] at hpos hX hx
    have hP := ih hpos.2 hX.2 hx.2
    have hP0 : RaisesDegree (degree ∘ wt) 0 ((l.map fun i ↦ x i (u i)).prod) :=
      (hP.mono zero_le_one).of_sub_one
    rw [List.map_cons, List.prod_cons]
    have h : x j (u j) * (l.map fun i ↦ x i (u i)).prod - 1 =
        (x j (u j) - 1) * (l.map fun i ↦ x i (u i)).prod +
          ((l.map fun i ↦ x i (u i)).prod - 1) := by noncomm_ring
    rw [h]
    exact ((hj.mul hP0).mono (by omega)).add hP

omit [Fintype η] [DecidableEq η] hpos hx in
/-- The linear terms of degree `n` raise the degree by `n`. -/
private theorem raisesDegree_sum_linear (n : ℤ) (u : ι → A) :
    RaisesDegree (degree ∘ wt) n
      (((l.filter fun i ↦ degree (α i) = n).map fun i ↦ u i • X i).sum) := by
  induction l with
  | nil => exact raisesDegree_zero _ _
  | cons j l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hX
    rw [List.filter_cons]
    split_ifs with hj
    · rw [List.map_cons, List.sum_cons]
      have hXj := hX.1.smul (u j)
      rw [decide_eq_true_iff.mp hj] at hXj
      exact hXj.add (ih hX.2)
    · exact ih hX.2

/-- **The key congruence.** Modulo matrices raising the degree by more than `n`, an ordered product
is the ordered product of its factors of degree less than `n`, plus the linear terms of its factors
of degree exactly `n`. -/
private theorem raisesDegree_list_prod_sub (n : ℤ) (u : ι → A) :
    RaisesDegree (degree ∘ wt) (n + 1)
      ((l.map fun i ↦ x i (u i)).prod -
        ((l.filter fun i ↦ degree (α i) < n).map fun i ↦ x i (u i)).prod -
        ((l.filter fun i ↦ degree (α i) = n).map fun i ↦ u i • X i).sum) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj := raisesDegree_sub_one hX hx List.mem_cons_self (u j)
    have hjpos := hpos j List.mem_cons_self
    have hXj := hX j List.mem_cons_self
    have hxj := hx j List.mem_cons_self
    simp only [List.mem_cons, forall_eq_or_imp] at hpos hX hx
    have hP := raisesDegree_list_prod_sub_one hpos.2 hX.2 hx.2 u
    have hS := raisesDegree_sum_linear (l := l) hX.2 n u
    have ih := ih hpos.2 hX.2 hx.2
    set P := (l.map fun i ↦ x i (u i)).prod
    set Q := ((l.filter fun i ↦ degree (α i) < n).map fun i ↦ x i (u i)).prod
    set S := ((l.filter fun i ↦ degree (α i) = n).map fun i ↦ u i • X i).sum
    simp only [List.map_cons, List.prod_cons, List.filter_cons]
    by_cases hlt : degree (α j) < n
    · -- A factor of low degree multiplies both products and commutes past the linear terms.
      have hne : ¬degree (α j) = n := hlt.ne
      simp only [hlt, hne, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
        List.map_cons, List.prod_cons]
      have h : x j (u j) * P - x j (u j) * Q - S =
          x j (u j) * (P - Q - S) + (x j (u j) - 1) * S := by noncomm_ring
      have hxj0 : RaisesDegree (degree ∘ wt) 0 (x j (u j)) := (hj.mono hjpos.le).of_sub_one
      have hxP := hxj0.mul ih
      rw [zero_add] at hxP
      rw [h]
      exact hxP.add ((hj.mul hS).mono (by omega))
    · -- A factor of degree at least `n` contributes only its linear term, if any.
      have hjP := (hj.mul hP).mono (d' := n + 1) (by omega)
      by_cases heq : degree (α j) = n
      · simp only [heq, lt_self_iff_false, decide_true, decide_false, ↓reduceIte,
          Bool.false_eq_true, List.map_cons, List.sum_cons]
        have h' : x j (u j) * P - Q - (u j • X j + S) =
            (P - Q - S) + (x j (u j) - 1) * (P - 1) + (x j (u j) - 1 - u j • X j) := by
          noncomm_ring
        rw [h']
        exact (ih.add hjP).add (by simpa [heq] using hxj (u j))
      · simp only [hlt, heq, decide_false, Bool.false_eq_true, ↓reduceIte]
        have h : x j (u j) * P - Q - S =
            (P - Q - S) + (x j (u j) - 1) * (P - 1) + (x j (u j) - 1) := by noncomm_ring
        rw [h]
        exact (ih.add hjP).add (hj.mono (by omega))

end OrderedProduct

end Matrix

namespace TauCeti.Matrix

open _root_.Matrix

variable {η A : Type*} [Fintype η] [DecidableEq η] [Ring A]
variable {ι G : Type*} [AddCommGroup G]

/-- **An ordered product of graded unipotent families determines its parameters.**

Let the basis indices carry weights `wt : η → G`, let `X i` shift weights by exactly `α i`, and
let `x i t` agree with `1 + t • X i` up to a matrix raising the degree by more than
`degree (α i)`. If the weights `α i` along the list `l` are distinct and of positive degree, and
`c • X i = 0` only for `c = 0`, then two ordered products `∏_{i ∈ l} x i (u i)` agree exactly when
the parameters agree along `l`. -/
theorem list_prod_map_inj_of_raisesDegree (wt : η → G) (degree : G →+ ℤ) (α : ι → G)
    (x : ι → A → Matrix η η A) (X : ι → Matrix η η A) {l : List ι}
    (hl : (l.map α).Nodup) (hpos : ∀ i ∈ l, 0 < degree (α i))
    (hX : ∀ i ∈ l, ∀ r s, X i r s ≠ 0 → wt r = wt s + α i)
    (hx : ∀ i ∈ l, ∀ t, RaisesDegree (degree ∘ wt) (degree (α i) + 1) (x i t - 1 - t • X i))
    (hfaith : ∀ i ∈ l, ∀ c : A, c • X i = 0 → c = 0) {u v : ι → A} :
    (l.map fun i ↦ x i (u i)).prod = (l.map fun i ↦ x i (v i)).prod ↔ ∀ i ∈ l, u i = v i := by
  classical
  refine ⟨fun huv ↦ ?_, fun h ↦ congrArg List.prod (List.map_congr_left fun i hi ↦ by rw [h i hi])⟩
  have hdeg : ∀ i ∈ l, RaisesDegree (degree ∘ wt) (degree (α i)) (X i) :=
    fun i hi ↦ .of_shift degree (hX i hi)
  by_contra hne
  simp only [not_forall, exists_prop] at hne
  -- Choose a parameter that differs, of least degree among those that differ.
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image ({i ∈ l.toFinset | u i ≠ v i})
    (fun i ↦ degree (α i)) (by
      obtain ⟨i, hi, huvi⟩ := hne
      exact ⟨i, by simpa [hi] using huvi⟩)
  simp only [Finset.mem_filter, List.mem_toFinset] at hi hmin
  set n := degree (α i)
  -- The factors of degree less than `n` have equal parameters.
  have hQ : ((l.filter fun j ↦ degree (α j) < n).map fun j ↦ x j (u j)).prod =
      ((l.filter fun j ↦ degree (α j) < n).map fun j ↦ x j (v j)).prod := by
    refine congrArg List.prod (List.map_congr_left fun j hj ↦ ?_)
    rw [List.mem_filter, decide_eq_true_iff] at hj
    by_contra hxj
    exact (hmin j ⟨hj.1, fun h ↦ hxj (by rw [h])⟩).not_gt hj.2
  -- Hence the linear terms of degree `n` agree modulo higher degree.
  have hS := (raisesDegree_list_prod_sub hpos hdeg hx n v).sub
    (raisesDegree_list_prod_sub hpos hdeg hx n u)
  have hnd : (l.filter fun j ↦ degree (α j) = n).Nodup := (hl.of_map α).filter _
  rw [huv, hQ, sub_sub_sub_cancel_left, ← List.sum_toFinset _ hnd, ← List.sum_toFinset _ hnd,
    ← Finset.sum_sub_distrib] at hS
  -- The linear terms shift weights differently, so the term at `i` vanishes on its own.
  refine hi.2 (sub_eq_zero.mp (hfaith i hi.1 _ (ext fun r s ↦ ?_)))
  by_cases hXrs : X i r s = 0
  · simp [hXrs]
  have hwt := hX i hi.1 r s hXrs
  have hzero := hS.apply_eq_zero (r := r) (s := s) (by simp [hwt, n])
  rw [_root_.Matrix.sum_apply, Finset.sum_eq_single i] at hzero
  · simpa [sub_mul] using hzero
  · intro j hj hji
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_iff] at hj
    by_contra hjrs
    have hαj : α j = α i := by
      have := hX j hj.1 r s fun h0 ↦ hjrs (by simp [h0])
      rw [hwt] at this
      exact (add_left_cancel this).symm
    exact hji (List.inj_on_of_nodup_map hl hj.1 hi.1 hαj)
  · intro hi'
    simp [hi.1, n] at hi'

end TauCeti.Matrix
