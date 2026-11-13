/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.CriticalLine

/-!
# A certified list of zeros on the critical line

The quadratic `f s = (s - (1/2 + i)) (s - (1/2 - i))` has simple zeros at `1/2 ± i`. On the
rectangle `[0, 1] × [-2, 2]` the two rectangles `[0, 1] × [1/2, 3/2]` and
`[0, 1] × [-3/2, -1/2]` with multiplicities `[1, 1]` form a certificate in the sense of
`TauCeti.HasZerosInRects`. Each of the two rectangles is symmetric under `s ↦ 1 - conj s`, as is
the divisor of `f`, so the symmetry criterion places each zero on the critical line, and the
certificate transfers this to the whole rectangle.
-/

public section

open Set Complex ComplexConjugate

namespace TauCeti.CriticalLineCertificateExample

open LFunctions

/-- The zero `1/2 + i` of `f`. -/
noncomputable def zeroAbove : ℂ := ⟨1 / 2, 1⟩

/-- The zero `1/2 - i` of `f`. -/
noncomputable def zeroBelow : ℂ := ⟨1 / 2, -1⟩

@[simp] theorem zeroAbove_re : zeroAbove.re = 1 / 2 := (rfl)
@[simp] theorem zeroAbove_im : zeroAbove.im = 1 := (rfl)
@[simp] theorem zeroBelow_re : zeroBelow.re = 1 / 2 := (rfl)
@[simp] theorem zeroBelow_im : zeroBelow.im = -1 := (rfl)

theorem zeroAbove_ne_zeroBelow : zeroAbove ≠ zeroBelow := by
  intro h
  have := congrArg im h
  norm_num at this

/-- A quadratic with simple zeros at `1/2 + i` and `1/2 - i`. -/
noncomputable def f (s : ℂ) : ℂ := (s - zeroAbove) * (s - zeroBelow)

private theorem analyticAt_f (s : ℂ) : AnalyticAt ℂ f s := by
  unfold f
  fun_prop

private theorem meromorphicOn_f : MeromorphicOn f univ := fun s _ ↦ (analyticAt_f s).meromorphicAt

/-- The divisor of `f` is `1` at each of its two zeros and `0` elsewhere. -/
theorem divisor_f (s : ℂ) : MeromorphicOn.divisor f univ s =
    if s = zeroAbove ∨ s = zeroBelow then 1 else 0 := by
  have hfun : f = (· - zeroAbove) * (· - zeroBelow) := (rfl)
  rw [meromorphicOn_f.divisor_eq_analyticOrderNatAt (analyticAt_f s) (mem_univ s), hfun,
    analyticOrderNatAt, analyticOrderAt_mul (by fun_prop) (by fun_prop)]
  by_cases ha : s = zeroAbove
  · subst ha
    simp [zeroAbove_ne_zeroBelow]
  by_cases hb : s = zeroBelow
  · subst hb
    simp [zeroAbove_ne_zeroBelow.symm]
  simp [ha, hb]

private theorem support_f :
    Function.support (fun s ↦ (MeromorphicOn.divisor f univ s).toNat) = {zeroAbove, zeroBelow} := by
  ext s
  simp only [Function.mem_support, divisor_f, mem_insert_iff, mem_singleton_iff]
  split_ifs with h <;> simp [h]

/-- The zero count of `f` in a region only sees the two zeros of `f`. -/
private theorem zeroCount_f (S : Set ℂ) :
    zeroCount f univ S = ∑ᶠ s ∈ S ∩ {zeroAbove, zeroBelow},
      (MeromorphicOn.divisor f univ s).toNat := by
  rw [zeroCount_def, ← finsum_mem_inter_support, support_f]

private theorem meromorphicOrderAt_f {s : ℂ} (ha : s ≠ zeroAbove) (hb : s ≠ zeroBelow) :
    meromorphicOrderAt f s = 0 := by
  rw [(analyticAt_f s).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr ?_)]
  · rfl
  simp [f, sub_eq_zero, ha, hb]

/-- A function with no zero on the frontier of a rectangle has order `0` there; a zero of `f`
avoids the frontier when it lies in the open rectangle or outside the closed one. -/
private theorem frontier_order {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (ha : z.im < 1 ∧ 1 < w.im ∨ 1 < z.im ∨ w.im < 1)
    (hb : z.im < -1 ∧ -1 < w.im ∨ -1 < z.im ∨ w.im < -1)
    (hre' : z.re < 1 / 2 ∧ 1 / 2 < w.re) :
    ∀ s ∈ frontier (Rectangle z w), meromorphicOrderAt f s = 0 := by
  have key (ρ : ℂ) (hρre : ρ.re = 1 / 2)
      (hρ : z.im < ρ.im ∧ ρ.im < w.im ∨ ρ.im < z.im ∨ w.im < ρ.im) :
      ρ ∉ frontier (Rectangle z w) := by
    rcases hρ with hρ | hρ
    · refine disjoint_left.1 disjoint_interior_frontier ?_
      rw [interior_rectangle hre.le him.le, mem_reProdIm, mem_Ioo, mem_Ioo]
      exact ⟨hρre ▸ hre', hρ⟩
    · refine fun hfr ↦ ?_
      have := (mem_rectangle_iff hre.le him.le).1 ((isClosed_rectangle z w).frontier_subset hfr)
      rcases hρ with hρ | hρ <;> linarith [this.2.1, this.2.2]
  intro s hs
  refine meromorphicOrderAt_f ?_ ?_ <;> rintro rfl
  · exact key _ zeroAbove_re (by simpa using ha) hs
  · exact key _ zeroBelow_re (by simpa using hb) hs

/-- The rectangles `[0, 1] × [1/2, 3/2]` and `[0, 1] × [-3/2, -1/2]`, each enclosing one zero
of `f`. -/
noncomputable def rects : List (ℂ × ℂ) := [(⟨0, 1 / 2⟩, ⟨1, 3 / 2⟩), (⟨0, -3 / 2⟩, ⟨1, -1 / 2⟩)]

/-- The two rectangles certify the two zeros of `f` in `[0, 1] × [-2, 2]`. -/
theorem hasZerosInRects : HasZerosInRects f univ ⟨0, -2⟩ ⟨1, 2⟩ rects [1, 1] where
  meromorphicOn := meromorphicOn_f
  rectangle_subset := subset_univ _
  divisor_nonneg s _ := by
    rw [divisor_f]
    split_ifs <;> norm_num
  subset_rectangle B hB := by
    simp only [rects, List.mem_cons, List.not_mem_nil, or_false] at hB
    intro s hs
    rw [mem_rectangle_iff (by norm_num) (by norm_num)]
    rcases hB with rfl | rfl <;>
    · rw [mem_rectangle_iff (by norm_num) (by norm_num)] at hs
      norm_num at hs ⊢
      exact ⟨hs.1, by linarith [hs.2.1], by linarith [hs.2.2]⟩
  pairwise_disjoint_interior := by
    simp only [rects, List.pairwise_pair]
    rw [interior_rectangle (by norm_num) (by norm_num),
      interior_rectangle (by norm_num) (by norm_num)]
    refine disjoint_left.2 fun s hs hs' ↦ ?_
    rw [mem_reProdIm, mem_Ioo, mem_Ioo] at hs hs'
    norm_num at hs hs'
    linarith [hs.2.1, hs'.2.2]
  meromorphicOrderAt_frontier := frontier_order (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  meromorphicOrderAt_frontier_of_mem B hB := by
    simp only [rects, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl <;>
    exact frontier_order (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  map_zeroCount := by
    have hcount (z w ρ : ℂ) (hρ : Rectangle z w ∩ {zeroAbove, zeroBelow} = {ρ})
        (hρ' : ρ = zeroAbove ∨ ρ = zeroBelow) : zeroCount f univ (Rectangle z w) = 1 := by
      rw [zeroCount_f, hρ, finsum_mem_singleton, divisor_f]
      simp [hρ']
    simp only [rects, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨hcount _ _ zeroAbove ?_ (Or.inl rfl), hcount _ _ zeroBelow ?_ (Or.inr rfl)⟩ <;>
    · ext s
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      rw [mem_rectangle_iff (by norm_num) (by norm_num)]
      constructor
      · rintro ⟨hs, rfl | rfl⟩ <;> first | rfl | (norm_num at hs)
      · rintro rfl
        norm_num
  zeroCount_eq_sum := by
    have hinter : Rectangle ⟨0, -2⟩ ⟨1, 2⟩ ∩ {zeroAbove, zeroBelow} = {zeroAbove, zeroBelow} := by
      refine inter_eq_right.2 (insert_subset_iff.2 ⟨?_, singleton_subset_iff.2 ?_⟩) <;>
      · rw [mem_rectangle_iff (by norm_num) (by norm_num)]
        norm_num
    rw [zeroCount_f, hinter, finsum_mem_pair zeroAbove_ne_zeroBelow]
    simp [divisor_f]

/-- The divisor of `f` is invariant under the reflection `s ↦ 1 - conj s`, which fixes both
zeros. -/
private theorem divisor_f_one_sub_conj (s : ℂ) :
    MeromorphicOn.divisor f univ (1 - conj s) = MeromorphicOn.divisor f univ s := by
  have key (c : ℂ) (hc : c.re = 1 / 2) : 1 - conj s = c ↔ s = c := by
    simp only [Complex.ext_iff, sub_re, one_re, conj_re, sub_im, one_im, conj_im, zero_sub,
      neg_neg, hc]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
  simp only [divisor_f, key _ zeroAbove_re, key _ zeroBelow_re]

/-- Both zeros of `f` in `[0, 1] × [-2, 2]` lie on the critical line, by the symmetry criterion
in each certified rectangle. -/
theorem allOnCriticalLine : AllOnCriticalLine f univ (Rectangle ⟨0, -2⟩ ⟨1, 2⟩) := by
  refine hasZerosInRects.allOnCriticalLine fun B hB ↦ ?_
  have hcount := hasZerosInRects.map_zeroCount
  simp only [rects, List.mem_cons, List.not_mem_nil, or_false] at hB
  simp only [rects, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcount
  refine allOnCriticalLine_of_zeroCount_eq_one (fun s hs ↦ ?_)
    (fun s _ ↦ divisor_f_one_sub_conj s) ?_
  · rcases hB with rfl | rfl <;>
    · rw [mem_rectangle_iff (by norm_num) (by norm_num)] at hs ⊢
      simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, zero_sub, neg_neg] at hs ⊢
      exact ⟨⟨by linarith [hs.1.2], by linarith [hs.1.1]⟩, hs.2⟩
  · rcases hB with rfl | rfl
    exacts [hcount.1, hcount.2]

end TauCeti.CriticalLineCertificateExample
