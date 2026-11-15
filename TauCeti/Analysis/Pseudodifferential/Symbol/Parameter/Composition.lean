/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic

/-!
# Composition and parametrices of strongly parameter-dependent symbols

The symbol of the composition of two pseudodifferential operators has the expansion
`a # b ∼ ∑ₖ sharpTerm a b k`, with
`sharpTerm a b k = ((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` (Taylor, Lecture I, (2.5)–(2.7)).
This file develops these terms for the strongly parameter-dependent symbols
`TauCeti.ParameterSymbol`, whose estimates are uniform in the spectral parameter `z`, and uses them
to invert a parameter-elliptic symbol up to any order.

* `TauCeti.ParameterSymbol.sharpTerm a b k`: the term of order `m' + m - k` of the composition
  expansion of symbols of orders `m'` and `m`: each of its `k` frequency derivatives lowers the
  order by one, uniformly in the spectral parameter.
* `TauCeti.ParameterSymbol.IsElliptic.exists_sub_sum_sharpTerm_left`,
  `TauCeti.ParameterSymbol.IsElliptic.exists_sub_sum_sharpTerm_right`: **parametrices with
  parameter.** If `a` has order `m` and is elliptic with parameter, then for every `N` there is a
  symbol `b` of order `-m`, equal to the pointwise inverse `a⁻¹` up to order `-m - 1`, with
  `1 - ∑_{k < N} sharpTerm b a k` (respectively `1 - ∑_{k < N} sharpTerm a b k`) a
  parameter-dependent symbol of order `-N`.

The remainder of order `-N` is a parameter-dependent symbol: its estimates are uniform in `z`, and
it decays like `(1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-N)` also as `z → ∞` at a fixed frequency. For the
symbol `a` of `A - z`, with `A` an elliptic operator of order `2`, the right parametrix is the
symbol-level construction of the approximate resolvent `(A - z)⁻¹` that enters the contour
integrals defining the complex powers of `A` (Seeley; Shubin, Chapter II, §§9–11).

## Proof outline

The pointwise inverse `b = a⁻¹` inverts `a` exactly in the first term `sharpTerm b a 0 = b ∘ a`.
If `R = 1 - ∑_{k ≤ N} sharpTerm b a k` has order `-N`, the correction `d = R ∘ a⁻¹` of order
`-m - N` satisfies `sharpTerm d a 0 = d ∘ a = R`, so `1 - ∑_{k ≤ N} sharpTerm (b + d) a k` is
`-∑_{1 ≤ k ≤ N} sharpTerm d a k`, which has order `-N - 1`. The right parametrix uses the
correction `a⁻¹ ∘ R` on the right instead. This is the construction of Taylor, Lecture I,
(4.1)–(4.6), with the exact inverse as the starting point.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7) and (4.1)–(4.6).
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §§9–11.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] {m m' : ℝ}

/-! ### The terms of the composition expansion -/

section Term

/-- The term of order `m' + m - k` in the composition expansion of the parameter-dependent symbols
`a` and `b` of orders `m'` and `m`: `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running
over the words `w` of coordinate indices of length `k`. It is defined by the recursion
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting from the
pointwise composition `sharpTerm a b 0 = a ∘ b`. -/
def sharpTerm : {m m' : ℝ} → ParameterSymbol n Λ W U m' → ParameterSymbol n Λ V W m →
    (k : ℕ) → ParameterSymbol n Λ V U (m' + m - k)
  | _, _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m) :
    a.sharpTerm b 0 = inclusion (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m)
    (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

@[simp]
theorem coefficient_sharpTerm_zero (a : ParameterSymbol n Λ W U m')
    (b : ParameterSymbol n Λ V W m) :
    (a.sharpTerm b 0).coefficient = (a.comp b).coefficient := by
  rw [sharpTerm_zero, coefficient_inclusion]

theorem coefficient_sharpTerm_succ (a : ParameterSymbol n Λ W U m')
    (b : ParameterSymbol n Λ V W m) (k : ℕ) :
    (a.sharpTerm b (k + 1)).coefficient = (-Complex.I / (k + 1)) •
      ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient := by
  rw [sharpTerm_succ, coefficient_inclusion, coefficient_smul, coefficient_sum]

/-- The first correction term of the composition expansion is `-i ∑ⱼ ∂_{ξⱼ} a ∘ ∂_{xⱼ} b`. -/
theorem coefficient_sharpTerm_one (a : ParameterSymbol n Λ W U m')
    (b : ParameterSymbol n Λ V W m) :
    (a.sharpTerm b 1).coefficient =
      (-Complex.I) • ∑ j, ((frequencyDeriv j a).comp (spatialDeriv j b)).coefficient := by
  simp [coefficient_sharpTerm_succ]

/-- The terms of the composition expansion depend only on the coefficients of the two symbols,
whatever their orders. -/
theorem coefficient_sharpTerm_congr {μ μ' : ℝ} {a : ParameterSymbol n Λ W U m'}
    {a' : ParameterSymbol n Λ W U μ'} {b : ParameterSymbol n Λ V W m}
    {b' : ParameterSymbol n Λ V W μ} (ha : a.coefficient = a'.coefficient)
    (hb : b.coefficient = b'.coefficient) (k : ℕ) :
    (a.sharpTerm b k).coefficient = (a'.sharpTerm b' k).coefficient := by
  induction k generalizing m m' μ μ' with
  | zero => funext p; simp [ha, hb]
  | succ k ih =>
    rw [coefficient_sharpTerm_succ, coefficient_sharpTerm_succ]
    congr 1
    exact sum_congr rfl fun j _ => ih (coefficient_frequencyDeriv_congr ha j)
      (coefficient_spatialDeriv_congr hb j)

/-- The terms of the composition expansion are additive in the first symbol, for symbols of
possibly different orders: if `a₀ = a₁ + a₂` coefficientwise, then
`sharpTerm a₀ b k = sharpTerm a₁ b k + sharpTerm a₂ b k` coefficientwise. -/
theorem coefficient_sharpTerm_eq_add_left {μ₁ μ₂ : ℝ} {a₀ : ParameterSymbol n Λ W U m'}
    {a₁ : ParameterSymbol n Λ W U μ₁} {a₂ : ParameterSymbol n Λ W U μ₂}
    (h : a₀.coefficient = a₁.coefficient + a₂.coefficient) (b : ParameterSymbol n Λ V W m)
    (k : ℕ) :
    (a₀.sharpTerm b k).coefficient =
      (a₁.sharpTerm b k).coefficient + (a₂.sharpTerm b k).coefficient := by
  induction k generalizing m m' μ₁ μ₂ with
  | zero =>
    funext p
    simp [h, ContinuousLinearMap.add_comp]
  | succ k ih =>
    simp only [coefficient_sharpTerm_succ, ← smul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => ih (coefficient_frequencyDeriv_eq_add h j) _

/-- The terms of the composition expansion are additive in the second symbol, for symbols of
possibly different orders: if `b₀ = b₁ + b₂` coefficientwise, then
`sharpTerm a b₀ k = sharpTerm a b₁ k + sharpTerm a b₂ k` coefficientwise. -/
theorem coefficient_sharpTerm_eq_add_right {μ₁ μ₂ : ℝ} {b₀ : ParameterSymbol n Λ V W m}
    {b₁ : ParameterSymbol n Λ V W μ₁} {b₂ : ParameterSymbol n Λ V W μ₂}
    (h : b₀.coefficient = b₁.coefficient + b₂.coefficient) (a : ParameterSymbol n Λ W U m')
    (k : ℕ) :
    (a.sharpTerm b₀ k).coefficient =
      (a.sharpTerm b₁ k).coefficient + (a.sharpTerm b₂ k).coefficient := by
  induction k generalizing m m' μ₁ μ₂ with
  | zero =>
    funext p
    simp [h, ContinuousLinearMap.comp_add]
  | succ k ih =>
    simp only [coefficient_sharpTerm_succ, ← smul_add, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => ih (coefficient_spatialDeriv_eq_add h j) _

end Term

/-! ### Parametrices with parameter -/

section Parametrix

variable [CompleteSpace V] {a : ParameterSymbol n Λ V W m}

/-- Composing with the inverse of a parameter-elliptic symbol on one side and the symbol itself
on the other side gives back the original coefficient. -/
theorem coefficient_comp_inverse_comp (ha : a.IsElliptic) (c : ParameterSymbol n Λ V U m') :
    ((c.comp (a.inverse ha)).comp a).coefficient = c.coefficient := by
  funext ⟨⟨x, ξ⟩, z⟩
  by_cases hz : z ∈ Λ
  · have h := coefficient_inverse_comp_coefficient ha x ξ hz
    rw [coefficient_inverse] at h
    simp [ContinuousLinearMap.comp_assoc, h]
  · simp [c.coefficient_of_notMem ((x, ξ), z) hz]

/-- Composing with a parameter-elliptic symbol on one side and its inverse on the other side gives
back the original coefficient. -/
theorem coefficient_comp_comp_inverse (ha : a.IsElliptic) (c : ParameterSymbol n Λ U W m') :
    (a.comp ((a.inverse ha).comp c)).coefficient = c.coefficient := by
  funext ⟨⟨x, ξ⟩, z⟩
  by_cases hz : z ∈ Λ
  · have h := coefficient_comp_coefficient_inverse ha x ξ hz
    rw [coefficient_inverse] at h
    simp [← ContinuousLinearMap.comp_assoc, h]
  · simp [c.coefficient_of_notMem ((x, ξ), z) hz]

/-- The correction step for left parametrices: if `R = 1 - ∑_{k ≤ N} sharpTerm b a k` and `d` is
`R ∘ a⁻¹` at order `-m - N`, then the remainder `1 - ∑_{k ≤ N} sharpTerm (b + d) a k` of the
corrected symbol is `-∑_{k < N} sharpTerm d a (k + 1)`. -/
private theorem coefficient_sub_sum_sharpTerm_left_succ (ha : a.IsElliptic) {N : ℕ}
    {b : ParameterSymbol n Λ W V (-m)} {R : ParameterSymbol n Λ V V (-N)}
    (hR : (const (.id ℂ V) : ParameterSymbol n Λ V V 0).coefficient -
      ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient = R.coefficient)
    {d : ParameterSymbol n Λ W V (-m - N)}
    (hd : d.coefficient = (R.comp (a.inverse ha)).coefficient)
    {b' : ParameterSymbol n Λ W V (-m)} (hb' : b'.coefficient = b.coefficient + d.coefficient) :
    (const (.id ℂ V) : ParameterSymbol n Λ V V 0).coefficient -
      ∑ k ∈ range (N + 1), (b'.sharpTerm a k).coefficient =
        -∑ k ∈ range N, (d.sharpTerm a (k + 1)).coefficient := by
  have hd₀ : (d.sharpTerm a 0).coefficient = R.coefficient := by
    rw [coefficient_sharpTerm_zero, ← coefficient_comp_inverse_comp ha R]
    funext p
    simp [hd]
  simp only [coefficient_sharpTerm_eq_add_left hb', sum_add_distrib]
  rw [sum_range_succ' fun k => (d.sharpTerm a k).coefficient, hd₀, ← hR]
  abel

/-- The correction step for right parametrices: if `R = 1 - ∑_{k ≤ N} sharpTerm a b k` and `d` is
`a⁻¹ ∘ R` at order `-m - N`, then the remainder `1 - ∑_{k ≤ N} sharpTerm a (b + d) k` of the
corrected symbol is `-∑_{k < N} sharpTerm a d (k + 1)`. -/
private theorem coefficient_sub_sum_sharpTerm_right_succ (ha : a.IsElliptic) {N : ℕ}
    {b : ParameterSymbol n Λ W V (-m)} {R : ParameterSymbol n Λ W W (-N)}
    (hR : (const (.id ℂ W) : ParameterSymbol n Λ W W 0).coefficient -
      ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient = R.coefficient)
    {d : ParameterSymbol n Λ W V (-m - N)}
    (hd : d.coefficient = ((a.inverse ha).comp R).coefficient)
    {b' : ParameterSymbol n Λ W V (-m)} (hb' : b'.coefficient = b.coefficient + d.coefficient) :
    (const (.id ℂ W) : ParameterSymbol n Λ W W 0).coefficient -
      ∑ k ∈ range (N + 1), (a.sharpTerm b' k).coefficient =
        -∑ k ∈ range N, (a.sharpTerm d (k + 1)).coefficient := by
  have hd₀ : (a.sharpTerm d 0).coefficient = R.coefficient := by
    rw [coefficient_sharpTerm_zero, ← coefficient_comp_comp_inverse ha R]
    funext p
    simp [hd]
  simp only [coefficient_sharpTerm_eq_add_right hb', sum_add_distrib]
  rw [sum_range_succ' fun k => (a.sharpTerm d k).coefficient, hd₀, ← hR]
  abel

/-- Left parametrices up to every positive order, by induction on the order. -/
private theorem IsElliptic.exists_sub_sum_sharpTerm_left_succ (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ V V (-((N + 1 : ℕ) : ℝ)),
        (const (.id ℂ V) : ParameterSymbol n Λ V V 0).coefficient -
          ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient = r.coefficient := by
  induction N with
  | zero =>
    refine ⟨a.inverse ha, ⟨0, by simp⟩, 0, ?_⟩
    funext ⟨⟨x, ξ⟩, z⟩
    by_cases hz : z ∈ Λ
    · have h := coefficient_inverse_comp_coefficient ha x ξ hz
      rw [coefficient_inverse] at h
      simp [coefficient_const _ x ξ hz, h]
    · simp [(const _ : ParameterSymbol n Λ V V 0).coefficient_of_notMem ((x, ξ), z) hz,
        a.coefficient_of_notMem ((x, ξ), z) hz]
  | succ N ih =>
    obtain ⟨b, ⟨d, hd⟩, r, hr⟩ := ih
    -- The remainder `R = 1 - ∑_{k ≤ N + 1} sharpTerm b a k` of order `-(N + 1)`.
    set R : ParameterSymbol n Λ V V (-((N + 1 : ℕ) : ℝ)) :=
      r - inclusion (by push_cast; linarith) (b.sharpTerm a (N + 1)) with hRdef
    have hR : (const (.id ℂ V) : ParameterSymbol n Λ V V 0).coefficient -
        ∑ k ∈ range (N + 1 + 1), (b.sharpTerm a k).coefficient = R.coefficient := by
      rw [sum_range_succ, hRdef, coefficient_sub, coefficient_inclusion, ← hr]
      abel
    -- The correction `D = R ∘ a⁻¹` of order `-m - (N + 1)`.
    set D : ParameterSymbol n Λ W V (-m - ((N + 1 : ℕ) : ℝ)) :=
      inclusion (by linarith) (R.comp (a.inverse ha)) with hDdef
    have hD : D.coefficient = (R.comp (a.inverse ha)).coefficient := by
      rw [hDdef, coefficient_inclusion]
    refine ⟨b + inclusion (by push_cast; linarith) D,
      ⟨d + inclusion (by push_cast; linarith) D, ?_⟩,
      -∑ k : Fin (N + 1), inclusion
        (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
        (D.sharpTerm a (k + 1)), ?_⟩
    · simp only [coefficient_add, coefficient_inclusion, hd, add_assoc]
    · rw [coefficient_sub_sum_sharpTerm_left_succ ha hR hD (by
          rw [coefficient_add, coefficient_inclusion]),
        coefficient_neg, coefficient_sum]
      simp only [coefficient_inclusion]
      rw [Fin.sum_univ_eq_sum_range fun k => (D.sharpTerm a (k + 1)).coefficient]

/-- **Left parametrices with parameter.** If `a` has order `m` and is elliptic with parameter, then
for every `N` there is a parameter-dependent symbol `b` of order `-m`, equal to the pointwise
inverse `a⁻¹` up to a symbol of order `-m - 1`, such that `1 - ∑_{k < N} sharpTerm b a k` is a
parameter-dependent symbol of order `-N`. -/
theorem IsElliptic.exists_sub_sum_sharpTerm_left (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ V V (-N),
        (const (.id ℂ V) : ParameterSymbol n Λ V V 0).coefficient -
          ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient := by
  cases N with
  | zero => exact ⟨a.inverse ha, ⟨0, by simp⟩, inclusion (by simp) (const (.id ℂ V)), by simp⟩
  | succ N => exact ha.exists_sub_sum_sharpTerm_left_succ N

/-- Right parametrices up to every positive order, by induction on the order. -/
private theorem IsElliptic.exists_sub_sum_sharpTerm_right_succ (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ W W (-((N + 1 : ℕ) : ℝ)),
        (const (.id ℂ W) : ParameterSymbol n Λ W W 0).coefficient -
          ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient = r.coefficient := by
  induction N with
  | zero =>
    refine ⟨a.inverse ha, ⟨0, by simp⟩, 0, ?_⟩
    funext ⟨⟨x, ξ⟩, z⟩
    by_cases hz : z ∈ Λ
    · have h := coefficient_comp_coefficient_inverse ha x ξ hz
      rw [coefficient_inverse] at h
      simp [coefficient_const _ x ξ hz, h]
    · simp [(const _ : ParameterSymbol n Λ W W 0).coefficient_of_notMem ((x, ξ), z) hz,
        a.coefficient_of_notMem ((x, ξ), z) hz]
  | succ N ih =>
    obtain ⟨b, ⟨d, hd⟩, r, hr⟩ := ih
    -- The remainder `R = 1 - ∑_{k ≤ N + 1} sharpTerm a b k` of order `-(N + 1)`.
    set R : ParameterSymbol n Λ W W (-((N + 1 : ℕ) : ℝ)) :=
      r - inclusion (by push_cast; linarith) (a.sharpTerm b (N + 1)) with hRdef
    have hR : (const (.id ℂ W) : ParameterSymbol n Λ W W 0).coefficient -
        ∑ k ∈ range (N + 1 + 1), (a.sharpTerm b k).coefficient = R.coefficient := by
      rw [sum_range_succ, hRdef, coefficient_sub, coefficient_inclusion, ← hr]
      abel
    -- The correction `D = a⁻¹ ∘ R` of order `-m - (N + 1)`.
    set D : ParameterSymbol n Λ W V (-m - ((N + 1 : ℕ) : ℝ)) :=
      inclusion (by linarith) ((a.inverse ha).comp R) with hDdef
    have hD : D.coefficient = ((a.inverse ha).comp R).coefficient := by
      rw [hDdef, coefficient_inclusion]
    refine ⟨b + inclusion (by push_cast; linarith) D,
      ⟨d + inclusion (by push_cast; linarith) D, ?_⟩,
      -∑ k : Fin (N + 1), inclusion
        (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
        (a.sharpTerm D (k + 1)), ?_⟩
    · simp only [coefficient_add, coefficient_inclusion, hd, add_assoc]
    · rw [coefficient_sub_sum_sharpTerm_right_succ ha hR hD (by
          rw [coefficient_add, coefficient_inclusion]),
        coefficient_neg, coefficient_sum]
      simp only [coefficient_inclusion]
      rw [Fin.sum_univ_eq_sum_range fun k => (a.sharpTerm D (k + 1)).coefficient]

/-- **Right parametrices with parameter.** If `a` has order `m` and is elliptic with parameter,
then for every `N` there is a parameter-dependent symbol `b` of order `-m`, equal to the pointwise
inverse `a⁻¹` up to a symbol of order `-m - 1`, such that `1 - ∑_{k < N} sharpTerm a b k` is a
parameter-dependent symbol of order `-N`. -/
theorem IsElliptic.exists_sub_sum_sharpTerm_right (ha : a.IsElliptic) (N : ℕ) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      (∃ d : ParameterSymbol n Λ W V (-m - 1),
        b.coefficient = (a.inverse ha).coefficient + d.coefficient) ∧
      ∃ r : ParameterSymbol n Λ W W (-N),
        (const (.id ℂ W) : ParameterSymbol n Λ W W 0).coefficient -
          ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient := by
  cases N with
  | zero => exact ⟨a.inverse ha, ⟨0, by simp⟩, inclusion (by simp) (const (.id ℂ W)), by simp⟩
  | succ N => exact ha.exists_sub_sum_sharpTerm_right_succ N

end Parametrix

end ParameterSymbol

end TauCeti
