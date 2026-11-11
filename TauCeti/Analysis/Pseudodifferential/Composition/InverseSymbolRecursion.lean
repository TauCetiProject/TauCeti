/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion

/-!
# The inverse-symbol recursions

Let `a` be a symbol of order `m` with values in `V →L[ℂ] W`. The composition of quantizations
has the asymptotic expansion `a # b ∼ ∑ₖ sharpTerm a b k`, the `k`-th term having order
`m + m_b - k` (`TauCeti.Symbol.sharpTerm`). A symbol `b` of order `-m` is a right parametrix
symbol of `a` when this formal composition is the identity, `1 ∼ ∑ₖ sharpTerm a b k`, and a left
parametrix symbol when `1 ∼ ∑ₖ sharpTerm b a k`. The module
`TauCeti.Analysis.Pseudodifferential.Composition.Parametrix` constructs such symbols by successive
corrections.

This file computes the full asymptotic expansion of these symbols from a pointwise inverse `b₀`
of `a` modulo smoothing symbols, for instance the cut-off inverse `χ(ξ / R) a(x, ξ)⁻¹` of an
elliptic symbol. Grouping the terms of the formal composition `a # (b₀ + b₁ + b₂ + ⋯)`, with `bⱼ`
of order `-m - j`, by their orders gives the **inverse-symbol recursion** (Taylor, Lecture I,
(4.1)–(4.6))

`b_l = -b₀ ∘ ∑_{j < l} sharpTerm a b_j (l - j)` for `l ≥ 1`,

so that the terms of order `-l` of the formal composition cancel modulo smoothing symbols for every
`l ≥ 1` (`TauCeti.Symbol.rightInverseTerm`). Every asymptotic sum `b ∼ ∑ₗ b_l` is then a right
parametrix symbol. The recursion uses only the bilinearity of the terms `sharpTerm` and their
compatibility with the inclusions of symbol classes, not the associativity of the formal
composition. The left recursion `b_l = -(∑_{j < l} sharpTerm b_j a (l - j)) ∘ b₀` is the mirror
image (`TauCeti.Symbol.leftInverseTerm`).

## Main declarations

* `TauCeti.Symbol.rightInverseTerm`, `TauCeti.Symbol.leftInverseTerm`: the terms of the right and
  left inverse-symbol recursions.
* `TauCeti.Symbol.isAsymptoticSum_sharpTerm_of_isAsymptoticSum_rightInverseTerm`: if `a ∘ b₀ - 1` is
  smoothing and `b ∼ ∑ₗ rightInverseTerm a b₀ l`, then `1 ∼ ∑ₖ sharpTerm a b k`; and
  `TauCeti.Symbol.isAsymptoticSum_sharpTerm_of_isAsymptoticSum_leftInverseTerm`, the left version.
* `TauCeti.Symbol.exists_isAsymptoticSum_rightInverseTerm`,
  `TauCeti.Symbol.exists_isAsymptoticSum_leftInverseTerm`: the recursions have asymptotic sums, and
  these are right (left) parametrix symbols.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Finset

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Coefficients of a given order -/

variable (n V W) in
/-- The coefficients of the symbols of order `μ`, as a submodule of all functions. -/
private def orderSubmodule (μ : ℝ) :
    Submodule ℂ (CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) where
  carrier := {f | ∃ r : Symbol n V W μ, r.coefficient = f}
  add_mem' := by
    rintro _ _ ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r + s, coefficient_add r s⟩
  zero_mem' := ⟨0, coefficient_zero⟩
  smul_mem' := by
    rintro c _ ⟨r, rfl⟩
    exact ⟨c • r, coefficient_smul c r⟩

private theorem mem_orderSubmodule {μ : ℝ}
    {f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} :
    f ∈ orderSubmodule n V W μ ↔ ∃ r : Symbol n V W μ, f = r.coefficient :=
  ⟨fun ⟨r, hr⟩ ↦ ⟨r, hr.symm⟩, fun ⟨r, hr⟩ ↦ ⟨r, hr.symm⟩⟩

private theorem coefficient_mem_orderSubmodule {μ μ' : ℝ} (h : μ ≤ μ') (r : Symbol n V W μ) :
    r.coefficient ∈ orderSubmodule n V W μ' :=
  ⟨inclusion h r, coefficient_inclusion h r⟩

private theorem IsSmoothing.coefficient_mem_orderSubmodule {s : Symbol n V W m}
    (hs : s.IsSmoothing) (μ' : ℝ) : s.coefficient ∈ orderSubmodule n V W μ' :=
  isSmoothing_iff.1 hs μ'

/-- The bookkeeping behind the inverse-symbol recursions. Let `g k` be the terms of a formal
composition, `f k j` the contribution of order `-(j + k)` to `g k`, and `S N` the coefficients of
order `-N`. If `g k ≡ ∑_{j < N - k} f k j` modulo `S N`, the part `f 0 0` of order `0` is `1`
modulo `S N` and the parts `f 0 l + ∑_{j < l} f (l - j) j` of order `-l` vanish modulo `S N` for
`l ≥ 1`, then `1 ≡ ∑_{k < N} g k` modulo `S N`. -/
private theorem sub_sum_mem_of_sum_antidiagonal_mem {M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : ℕ → Submodule ℂ M) (e : M) (g : ℕ → M) (f : ℕ → ℕ → M)
    (hg : ∀ N k, k < N → g k - ∑ j ∈ range (N - k), f k j ∈ S N)
    (h₀ : ∀ N, e - f 0 0 ∈ S N)
    (hf : ∀ l N, f 0 (l + 1) + ∑ j : Fin (l + 1), f (l + 1 - j) j ∈ S N)
    (he : e ∈ S 0) (N : ℕ) : e - ∑ k ∈ range N, g k ∈ S N := by
  -- The part of order `-(l + 1)`, as a sum over the antidiagonal `k + j = l + 1`.
  have hf' : ∀ l N, ∑ k ∈ range (l + 2), f k (l + 1 - k) ∈ S N := fun l N ↦ by
    convert hf l N using 1
    rw [sum_range_succ', Fin.sum_univ_eq_sum_range (fun j ↦ f (l + 1 - j) j), ← sum_range_reflect,
      add_comm]
    refine congrArg _ (sum_congr rfl fun k hk ↦ ?_)
    have hk := mem_range.1 hk
    congr 1 <;> omega
  cases N with
  | zero => simpa using he
  | succ N =>
    -- Regroup `∑_{k ≤ N} ∑_{j ≤ N - k} f k j` by the total order `l = j + k`.
    have hsum : e - ∑ k ∈ range (N + 1), g k = (e - f 0 0) -
        ∑ l ∈ range N, ∑ k ∈ range (l + 2), f k (l + 1 - k) -
        ∑ k ∈ range (N + 1), (g k - ∑ j ∈ range (N + 1 - k), f k j) := by
      rw [sum_sub_distrib, ← sum_range_diag_flip,
        sum_range_succ' (fun l ↦ ∑ k ∈ range (l + 1), f k (l - k))]
      simp
      abel
    rw [hsum]
    refine sub_mem (sub_mem (h₀ _) (sum_mem fun l _ ↦ hf' l _)) (sum_mem fun k hk ↦ ?_)
    exact hg _ k (mem_range.1 hk)

/-- The orders in the right recursion: the term of index `l + 1 - j` of the formal composition of
`a`, of order `m`, with a symbol of order `-m - j` has order `-(l + 1)`. -/
private theorem order_le (m : ℝ) {l : ℕ} (j : Fin (l + 1)) :
    m + (-m - (j : ℕ)) - ((l + 1 - j : ℕ) : ℝ) ≤ -((l + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

/-- The orders in the left recursion, as in `order_le`. -/
private theorem order_le' (m : ℝ) {l : ℕ} (j : Fin (l + 1)) :
    (-m - (j : ℕ)) + m - ((l + 1 - j : ℕ) : ℝ) ≤ -((l + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

/-! ### The right inverse-symbol recursion -/

section Right

/-- The terms of the **right inverse-symbol recursion** of a symbol `a` of order `m`, starting from
a symbol `b₀` of order `-m`: `b_0 = b₀` and, for `l ≥ 1`,

`b_l = -b₀ ∘ ∑_{j < l} sharpTerm a b_j (l - j)`,

a symbol of order `-m - l`. When `a ∘ b₀ = 1` modulo smoothing symbols, every asymptotic sum
`b ∼ ∑ₗ b_l` satisfies `1 ∼ ∑ₖ sharpTerm a b k`
(`isAsymptoticSum_sharpTerm_of_isAsymptoticSum_rightInverseTerm`). -/
def rightInverseTerm (a : Symbol n V W m) (b₀ : Symbol n W V (-m)) :
    (l : ℕ) → Symbol n W V (-m - l)
  | 0 => inclusion (by simp) b₀
  | l + 1 => -inclusion (by push_cast; linarith) (b₀.comp
      (∑ j : Fin (l + 1), inclusion (order_le m j)
        (a.sharpTerm (rightInverseTerm a b₀ j) (l + 1 - j)) : Symbol n W W (-((l + 1 : ℕ) : ℝ))))

variable (a : Symbol n V W m) (b₀ : Symbol n W V (-m))

@[simp]
theorem coefficient_rightInverseTerm_zero :
    (a.rightInverseTerm b₀ 0).coefficient = b₀.coefficient := by
  rw [rightInverseTerm, coefficient_inclusion]

theorem coefficient_rightInverseTerm_succ (l : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.rightInverseTerm b₀ (l + 1)).coefficient p = -(b₀.coefficient p).comp
      (∑ j : Fin (l + 1), (a.sharpTerm (a.rightInverseTerm b₀ j) (l + 1 - j)).coefficient p) := by
  rw [rightInverseTerm]
  simp [coefficient_sum]

variable {a b₀}

/-- **The right inverse-symbol recursion.** If `b₀` is a pointwise right inverse of `a` modulo
smoothing symbols and `b ∼ ∑ₗ b_l` is an asymptotic sum of the terms of the recursion
(`TauCeti.Symbol.rightInverseTerm`), then the formal composition `a # b` is the identity: for every
`N`, the symbol `1 - ∑_{k < N} sharpTerm a b k` has order `-N`. -/
theorem isAsymptoticSum_sharpTerm_of_isAsymptoticSum_rightInverseTerm
    (h₀ : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing)
    {b : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun l : ℕ ↦ -m - l) (inclusion (by simp) b)
      (a.rightInverseTerm b₀)) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b) := by
  set f : ℕ → ℕ → CoordinateSpace n × CoordinateSpace n → W →L[ℂ] W :=
    fun k j ↦ (a.sharpTerm (a.rightInverseTerm b₀ j) k).coefficient with hf
  refine isAsymptoticSum_iff.2 fun N ↦ mem_orderSubmodule.1 ?_
  refine sub_sum_mem_of_sum_antidiagonal_mem (fun N ↦ orderSubmodule n W W (m + -m - N))
    (inclusion (by simp) (const (.id ℂ W)) : Symbol n W W (m + -m - (0 : ℕ))).coefficient
    (fun k ↦ (a.sharpTerm b k).coefficient) f (fun N k hk ↦ ?_) (fun N ↦ ?_) (fun l N ↦ ?_)
    (coefficient_mem_orderSubmodule le_rfl _) N
  · -- Split `b = ∑_{j < N - k} b_j + r` with `r` of order `-m - (N - k)`.
    obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb (N - k)
    have hb' : b = ∑ j ∈ range (N - k), inclusion (by simp) (a.rightInverseTerm b₀ j) +
        inclusion (by simp) r := by
      ext1
      rw [coefficient_add, coefficient_sum, coefficient_inclusion, ← hr]
      simp [coefficient_inclusion]
    rw [hb', sharpTerm_add, sharpTerm_sum, coefficient_add, coefficient_sum]
    simp only [sharpTerm_inclusion, coefficient_inclusion, hf, add_sub_cancel_left]
    refine coefficient_mem_orderSubmodule ?_ _
    rw [Nat.cast_sub hk.le]
    linarith
  · -- The part of order `0` is `a ∘ b₀`.
    have h := IsSmoothing.coefficient_mem_orderSubmodule h₀.neg (m + -m - N)
    convert h using 1
    funext p
    simp [hf]
  · -- The part of order `-(l + 1)` is `-(a ∘ b₀ - 1) ∘ c` for the sum `c` in the recursion.
    have h := IsSmoothing.coefficient_mem_orderSubmodule
      ((h₀.comp_right (∑ j : Fin (l + 1), inclusion (order_le m j)
        (a.sharpTerm (a.rightInverseTerm b₀ j) (l + 1 - j)) :
          Symbol n W W (-((l + 1 : ℕ) : ℝ)))).neg) (m + -m - N)
    convert h using 1
    funext p
    simp [hf, coefficient_sum, coefficient_rightInverseTerm_succ,
      ContinuousLinearMap.comp_assoc]
    abel

/-- **Right parametrix symbols from the recursion.** If `b₀` is a pointwise right inverse of `a`
modulo smoothing symbols, the right inverse-symbol recursion has an asymptotic sum `b` of order
`-m`, and every such sum satisfies `1 ∼ ∑ₖ sharpTerm a b k`. -/
theorem exists_isAsymptoticSum_rightInverseTerm
    (h₀ : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing) :
    ∃ b : Symbol n W V (-m),
      IsAsymptoticSum (m := fun l : ℕ ↦ -m - l) (inclusion (by simp) b)
        (a.rightInverseTerm b₀) ∧
      IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
        (a.sharpTerm b) := by
  have hm : Antitone fun l : ℕ ↦ -m - l := fun _ _ h ↦ sub_le_sub_left (Nat.cast_le.2 h) _
  have hm' : Tendsto (fun l : ℕ ↦ -m - l) atTop atBot :=
    tendsto_atBot_add_const_left atTop (-m) <|
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  obtain ⟨b, hb⟩ := exists_asymptoticSum hm hm' (a.rightInverseTerm b₀)
  have hb' : IsAsymptoticSum (m := fun l : ℕ ↦ -m - l)
      (inclusion (by simp) (inclusion (by simp) b : Symbol n W V (-m))) (a.rightInverseTerm b₀) :=
    isAsymptoticSum_iff.2 fun N ↦ (isAsymptoticSum_iff.1 hb N).imp fun _ h ↦ by simpa using h
  exact ⟨_, hb', isAsymptoticSum_sharpTerm_of_isAsymptoticSum_rightInverseTerm h₀ hb'⟩

end Right

/-! ### The left inverse-symbol recursion -/

section Left

/-- The terms of the **left inverse-symbol recursion** of a symbol `a` of order `m`, starting from
a symbol `b₀` of order `-m`: `b_0 = b₀` and, for `l ≥ 1`,

`b_l = -(∑_{j < l} sharpTerm b_j a (l - j)) ∘ b₀`,

a symbol of order `-m - l`. When `b₀ ∘ a = 1` modulo smoothing symbols, every asymptotic sum
`b ∼ ∑ₗ b_l` satisfies `1 ∼ ∑ₖ sharpTerm b a k`
(`isAsymptoticSum_sharpTerm_of_isAsymptoticSum_leftInverseTerm`). -/
def leftInverseTerm (a : Symbol n V W m) (b₀ : Symbol n W V (-m)) :
    (l : ℕ) → Symbol n W V (-m - l)
  | 0 => inclusion (by simp) b₀
  | l + 1 => -inclusion (by push_cast; linarith)
      ((∑ j : Fin (l + 1), inclusion (order_le' m j)
        ((leftInverseTerm a b₀ j).sharpTerm a (l + 1 - j)) :
          Symbol n V V (-((l + 1 : ℕ) : ℝ))).comp b₀)

variable (a : Symbol n V W m) (b₀ : Symbol n W V (-m))

@[simp]
theorem coefficient_leftInverseTerm_zero :
    (a.leftInverseTerm b₀ 0).coefficient = b₀.coefficient := by
  rw [leftInverseTerm, coefficient_inclusion]

theorem coefficient_leftInverseTerm_succ (l : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.leftInverseTerm b₀ (l + 1)).coefficient p =
      -(∑ j : Fin (l + 1), ((a.leftInverseTerm b₀ j).sharpTerm a (l + 1 - j)).coefficient p).comp
        (b₀.coefficient p) := by
  rw [leftInverseTerm]
  simp [coefficient_sum]

variable {a b₀}

/-- **The left inverse-symbol recursion.** If `b₀` is a pointwise left inverse of `a` modulo
smoothing symbols and `b ∼ ∑ₗ b_l` is an asymptotic sum of the terms of the recursion
(`TauCeti.Symbol.leftInverseTerm`), then the formal composition `b # a` is the identity: for every
`N`, the symbol `1 - ∑_{k < N} sharpTerm b a k` has order `-N`. -/
theorem isAsymptoticSum_sharpTerm_of_isAsymptoticSum_leftInverseTerm
    (h₀ : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing)
    {b : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun l : ℕ ↦ -m - l) (inclusion (by simp) b)
      (a.leftInverseTerm b₀)) :
    IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a) := by
  set f : ℕ → ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] V :=
    fun k j ↦ ((a.leftInverseTerm b₀ j).sharpTerm a k).coefficient with hf
  refine isAsymptoticSum_iff.2 fun N ↦ mem_orderSubmodule.1 ?_
  refine sub_sum_mem_of_sum_antidiagonal_mem (fun N ↦ orderSubmodule n V V (-m + m - N))
    (inclusion (by simp) (const (.id ℂ V)) : Symbol n V V (-m + m - (0 : ℕ))).coefficient
    (fun k ↦ (b.sharpTerm a k).coefficient) f (fun N k hk ↦ ?_) (fun N ↦ ?_) (fun l N ↦ ?_)
    (coefficient_mem_orderSubmodule le_rfl _) N
  · -- Split `b = ∑_{j < N - k} b_j + r` with `r` of order `-m - (N - k)`.
    obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb (N - k)
    have hb' : b = ∑ j ∈ range (N - k), inclusion (by simp) (a.leftInverseTerm b₀ j) +
        inclusion (by simp) r := by
      ext1
      rw [coefficient_add, coefficient_sum, coefficient_inclusion, ← hr]
      simp [coefficient_inclusion]
    rw [hb', add_sharpTerm, sum_sharpTerm, coefficient_add, coefficient_sum]
    simp only [inclusion_sharpTerm, coefficient_inclusion, hf, add_sub_cancel_left]
    refine coefficient_mem_orderSubmodule ?_ _
    rw [Nat.cast_sub hk.le]
    linarith
  · -- The part of order `0` is `b₀ ∘ a`.
    have h := IsSmoothing.coefficient_mem_orderSubmodule h₀.neg (-m + m - N)
    convert h using 1
    funext p
    simp [hf]
  · -- The part of order `-(l + 1)` is `-c ∘ (b₀ ∘ a - 1)` for the sum `c` in the recursion.
    have h := IsSmoothing.coefficient_mem_orderSubmodule
      ((h₀.comp_left (∑ j : Fin (l + 1), inclusion (order_le' m j)
        ((a.leftInverseTerm b₀ j).sharpTerm a (l + 1 - j)) :
          Symbol n V V (-((l + 1 : ℕ) : ℝ)))).neg) (-m + m - N)
    convert h using 1
    funext p
    simp [hf, coefficient_sum, coefficient_leftInverseTerm_succ,
      ContinuousLinearMap.comp_assoc]
    abel

/-- **Left parametrix symbols from the recursion.** If `b₀` is a pointwise left inverse of `a`
modulo smoothing symbols, the left inverse-symbol recursion has an asymptotic sum `b` of order
`-m`, and every such sum satisfies `1 ∼ ∑ₖ sharpTerm b a k`. -/
theorem exists_isAsymptoticSum_leftInverseTerm
    (h₀ : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing) :
    ∃ b : Symbol n W V (-m),
      IsAsymptoticSum (m := fun l : ℕ ↦ -m - l) (inclusion (by simp) b)
        (a.leftInverseTerm b₀) ∧
      IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
        (b.sharpTerm a) := by
  have hm : Antitone fun l : ℕ ↦ -m - l := fun _ _ h ↦ sub_le_sub_left (Nat.cast_le.2 h) _
  have hm' : Tendsto (fun l : ℕ ↦ -m - l) atTop atBot :=
    tendsto_atBot_add_const_left atTop (-m) <|
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  obtain ⟨b, hb⟩ := exists_asymptoticSum hm hm' (a.leftInverseTerm b₀)
  have hb' : IsAsymptoticSum (m := fun l : ℕ ↦ -m - l)
      (inclusion (by simp) (inclusion (by simp) b : Symbol n W V (-m))) (a.leftInverseTerm b₀) :=
    isAsymptoticSum_iff.2 fun N ↦ (isAsymptoticSum_iff.1 hb N).imp fun _ h ↦ by simpa using h
  exact ⟨_, hb', isAsymptoticSum_sharpTerm_of_isAsymptoticSum_leftInverseTerm h₀ hb'⟩

end Left

end Symbol

end TauCeti
