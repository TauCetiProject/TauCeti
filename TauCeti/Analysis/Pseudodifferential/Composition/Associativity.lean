/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
import TauCeti.Algebra.BigOperators.NatAntidiagonal

/-!
# Associativity of the formal composition and uniqueness of parametrix symbols

The terms `TauCeti.Symbol.sharpTerm a b k` of the asymptotic expansion
`a # b ∼ ∑ₖ sharpTerm a b k` of the composition symbol define a formal composition of symbols,
graded by the decrease `k` of the order. This file proves that the formal composition is
associative: for symbols `c`, `b`, `a`, the terms of total degree `k` of `(c # b) # a` and of
`c # (b # a)` agree,

`∑_{i + j = k} sharpTerm (sharpTerm c b i) a j = ∑_{i + j = k} sharpTerm c (sharpTerm b a j) i`.

As a consequence, left and right parametrix symbols agree modulo smoothing symbols: if `a` has
order `m` and `b_L`, `b_R` have order `-m` with `1 ∼ ∑ₖ sharpTerm b_L a k` and
`1 ∼ ∑ₖ sharpTerm a b_R k`, then `b_L - b_R` is smoothing. Since the formal composition only
changes by smoothing terms when one factor does, `b_L` is then also a right parametrix symbol and
`b_R` a left one: each is a two-sided parametrix symbol.

## Main results

* `TauCeti.Symbol.sum_antidiagonal_coefficient_sharpTerm_assoc`: **associativity of the formal
  composition**, degree by degree.
* `TauCeti.Symbol.isSmoothing_sub_of_isAsymptoticSum_sharpTerm`: a left and a right parametrix
  symbol differ by a smoothing symbol.
* `TauCeti.Symbol.isAsymptoticSum_sharpTerm_of_isSmoothing_sub_right` and
  `TauCeti.Symbol.isAsymptoticSum_sharpTerm_of_isSmoothing_sub_left`: changing one factor by a
  smoothing symbol does not change an asymptotic sum of the formal composition.

## Proof outline

Both sides of the associativity identity are determined by the same recursion. Write
`L(c, b, a, k)` for the left side. Multiplying by `k + 1 = i + j` and using the recursion
`(k + 1) sharpTerm c b (k + 1) = -i ∑ₗ sharpTerm (∂_{ξₗ} c) (∂_{xₗ} b) k` of the terms, once for the
inner and once for the outer composition, together with the Leibniz rule for the frequency
derivative of the inner composition, gives

`(k + 1) L(c, b, a, k + 1) = -i ∑ₗ (L(∂_{ξₗ} c, ∂_{xₗ} b, a, k) + L(∂_{ξₗ} c, b, ∂_{xₗ} a, k)`
`  + L(c, ∂_{ξₗ} b, ∂_{xₗ} a, k))`.

The right side satisfies the same recursion, now through the Leibniz rule for the position
derivative of the inner composition, and both sides start from the associativity of the pointwise
composition at `k = 0`. Induction on `k` concludes.

For the parametrix symbols, sum the terms of degree less than `N + 1` of `(b_L # a) # b_R`. Grouped
by the degree of the outer factor `b_R` this is `b_R` up to a symbol of order `-m - (N + 1)`, since
`b_L # a ∼ 1`; grouped by the degree of the outer factor `b_L` and by associativity it is `b_L` up
to a symbol of the same order, since `a # b_R ∼ 1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7) and (4.1)–(4.6).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W U U' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup U'] [NormedSpace ℂ U']

/-! ### Associativity -/

section Assoc

variable {m₁ m₂ m₃ : ℝ}

/-- The recursion satisfied by the terms of degree `k` of the formal composition `(c # b) # a`. -/
private theorem succ_smul_sum_antidiagonal_sharpTerm_sharpTerm_left (c : Symbol n U U' m₃)
    (b : Symbol n W U m₂) (a : Symbol n V W m₁) (k : ℕ) :
    ((k : ℂ) + 1) •
        ∑ p ∈ antidiagonal (k + 1), ((c.sharpTerm b p.1).sharpTerm a p.2).coefficient =
      -Complex.I • ∑ l, (∑ p ∈ antidiagonal k,
          (((frequencyDeriv l c).sharpTerm (spatialDeriv l b) p.1).sharpTerm a p.2).coefficient +
        ∑ p ∈ antidiagonal k,
          (((frequencyDeriv l c).sharpTerm b p.1).sharpTerm (spatialDeriv l a) p.2).coefficient +
        ∑ p ∈ antidiagonal k, ((c.sharpTerm (frequencyDeriv l b) p.1).sharpTerm
          (spatialDeriv l a) p.2).coefficient) := by
  -- Raising the degree of the inner composition.
  have h₁ (i j : ℕ) : ((i : ℂ) + 1) • ((c.sharpTerm b (i + 1)).sharpTerm a j).coefficient =
      -Complex.I • ∑ l,
        (((frequencyDeriv l c).sharpTerm (spatialDeriv l b) i).sharpTerm a j).coefficient := by
    rw [coefficient_sharpTerm_eq_sum_left univ (fun _ ↦ -Complex.I / ((i : ℂ) + 1))
      (fun l ↦ (frequencyDeriv l c).sharpTerm (spatialDeriv l b) i) ?_ a j, smul_sum, smul_sum]
    · refine sum_congr rfl fun l _ ↦ ?_
      rw [smul_smul, mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero i)]
    · funext p
      simp [coefficient_sharpTerm_succ, smul_sum]
  -- Raising the degree of the outer composition.
  have h₂ (i j : ℕ) : ((j : ℂ) + 1) • ((c.sharpTerm b i).sharpTerm a (j + 1)).coefficient =
      -Complex.I • ∑ l,
        ((((frequencyDeriv l c).sharpTerm b i).sharpTerm (spatialDeriv l a) j).coefficient +
          ((c.sharpTerm (frequencyDeriv l b) i).sharpTerm (spatialDeriv l a) j).coefficient) := by
    have h : ((c.sharpTerm b i).sharpTerm a (j + 1)).coefficient = (-Complex.I / ((j : ℂ) + 1)) •
        ∑ l, ((frequencyDeriv l (c.sharpTerm b i)).sharpTerm (spatialDeriv l a) j).coefficient := by
      funext p
      simp [coefficient_sharpTerm_succ]
    rw [h, smul_smul, mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero j)]
    refine congrArg _ (sum_congr rfl fun l _ ↦ coefficient_sharpTerm_eq_add_left ?_ _ _)
    funext p
    exact coefficient_frequencyDeriv_sharpTerm l c b i p
  rw [Finset.Nat.natCast_add_one_smul_sum_antidiagonal_succ]
  simp only [h₁, h₂, ← smul_sum, ← smul_add, sum_add_distrib]
  rw [sum_comm, sum_comm (s := antidiagonal k), sum_comm (s := antidiagonal k), add_assoc]

/-- The recursion satisfied by the terms of degree `k` of the formal composition `c # (b # a)`. -/
private theorem succ_smul_sum_antidiagonal_sharpTerm_sharpTerm_right (c : Symbol n U U' m₃)
    (b : Symbol n W U m₂) (a : Symbol n V W m₁) (k : ℕ) :
    ((k : ℂ) + 1) •
        ∑ p ∈ antidiagonal (k + 1), (c.sharpTerm (b.sharpTerm a p.2) p.1).coefficient =
      -Complex.I • ∑ l, (∑ p ∈ antidiagonal k,
          ((frequencyDeriv l c).sharpTerm ((spatialDeriv l b).sharpTerm a p.2) p.1).coefficient +
        ∑ p ∈ antidiagonal k,
          ((frequencyDeriv l c).sharpTerm (b.sharpTerm (spatialDeriv l a) p.2) p.1).coefficient +
        ∑ p ∈ antidiagonal k, (c.sharpTerm
          ((frequencyDeriv l b).sharpTerm (spatialDeriv l a) p.2) p.1).coefficient) := by
  -- Raising the degree of the outer composition.
  have h₁ (i j : ℕ) : ((i : ℂ) + 1) • (c.sharpTerm (b.sharpTerm a j) (i + 1)).coefficient =
      -Complex.I • ∑ l,
        (((frequencyDeriv l c).sharpTerm ((spatialDeriv l b).sharpTerm a j) i).coefficient +
          ((frequencyDeriv l c).sharpTerm (b.sharpTerm (spatialDeriv l a) j) i).coefficient) := by
    have h : (c.sharpTerm (b.sharpTerm a j) (i + 1)).coefficient = (-Complex.I / ((i : ℂ) + 1)) •
        ∑ l, ((frequencyDeriv l c).sharpTerm (spatialDeriv l (b.sharpTerm a j)) i).coefficient := by
      funext p
      simp [coefficient_sharpTerm_succ]
    rw [h, smul_smul, mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero i)]
    refine congrArg _ (sum_congr rfl fun l _ ↦ coefficient_sharpTerm_eq_add_right ?_ _ _)
    rw [spatialDeriv_sharpTerm, coefficient_add]
  -- Raising the degree of the inner composition.
  have h₂ (i j : ℕ) : ((j : ℂ) + 1) • (c.sharpTerm (b.sharpTerm a (j + 1)) i).coefficient =
      -Complex.I • ∑ l,
        (c.sharpTerm ((frequencyDeriv l b).sharpTerm (spatialDeriv l a) j) i).coefficient := by
    rw [coefficient_sharpTerm_eq_sum_right univ (fun _ ↦ -Complex.I / ((j : ℂ) + 1))
      (fun l ↦ (frequencyDeriv l b).sharpTerm (spatialDeriv l a) j) ?_ c i, smul_sum, smul_sum]
    · refine sum_congr rfl fun l _ ↦ ?_
      rw [smul_smul, mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero j)]
    · funext p
      simp [coefficient_sharpTerm_succ, smul_sum]
  rw [Finset.Nat.natCast_add_one_smul_sum_antidiagonal_succ]
  simp only [h₁, h₂, ← smul_sum, ← smul_add, sum_add_distrib]
  rw [sum_comm, sum_comm (s := antidiagonal k), sum_comm (s := antidiagonal k)]

/-- **Associativity of the formal composition.** For symbols `c`, `b` and `a`, the terms of degree
`k` of the formal compositions `(c # b) # a` and `c # (b # a)` agree:
`∑_{i + j = k} sharpTerm (sharpTerm c b i) a j = ∑_{i + j = k} sharpTerm c (sharpTerm b a j) i`.
Both sides are symbols of order `m₃ + m₂ + m₁ - k`, so the identity is stated for their
coefficients. -/
theorem sum_antidiagonal_coefficient_sharpTerm_assoc (c : Symbol n U U' m₃)
    (b : Symbol n W U m₂) (a : Symbol n V W m₁) (k : ℕ) :
    ∑ p ∈ antidiagonal k, ((c.sharpTerm b p.1).sharpTerm a p.2).coefficient =
      ∑ p ∈ antidiagonal k, (c.sharpTerm (b.sharpTerm a p.2) p.1).coefficient := by
  induction k generalizing m₁ m₂ m₃ with
  | zero =>
    funext p
    simp [ContinuousLinearMap.comp_assoc]
  | succ k ih =>
    have h := succ_smul_sum_antidiagonal_sharpTerm_sharpTerm_left c b a k
    simp only [ih] at h
    rw [← succ_smul_sum_antidiagonal_sharpTerm_sharpTerm_right] at h
    exact smul_right_injective _ (Nat.cast_add_one_ne_zero k) h

end Assoc

/-! ### Left and right parametrix symbols -/

section Parametrix

variable {m : ℝ}

/-- Inside the left factor of the formal composition, the first `M` terms of an asymptotic sum
`e ∼ ∑ᵢ Aᵢ` add up to `e` minus the remainder. -/
private theorem sum_range_coefficient_sharpTerm_left {μ : ℕ → ℝ} {ν : ℝ} (hμ : ∀ M, μ M ≤ μ 0)
    {e : Symbol n W U (μ 0)} {A : ∀ i, Symbol n W U (μ i)} {r : ∀ M, Symbol n W U (μ M)}
    (hr : ∀ M, e.coefficient - ∑ i ∈ range M, (A i).coefficient = (r M).coefficient)
    (B : Symbol n V W ν) (M j : ℕ) :
    ∑ i ∈ range M, ((A i).sharpTerm B j).coefficient =
      (e.sharpTerm B j).coefficient - ((r M).sharpTerm B j).coefficient := by
  have h₁ : e.coefficient = (e - inclusion (hμ M) (r M)).coefficient + (r M).coefficient := by
    simp
  have h₂ : (e - inclusion (hμ M) (r M)).coefficient =
      ∑ i ∈ range M, (1 : ℂ) • (A i).coefficient := by
    rw [coefficient_sub, coefficient_inclusion, ← hr M, sub_sub_cancel]
    simp
  rw [coefficient_sharpTerm_eq_add_left h₁, coefficient_sharpTerm_eq_sum_left _ _ A h₂,
    add_sub_cancel_right]
  simp

/-- Inside the right factor of the formal composition, the first `M` terms of an asymptotic sum
`e ∼ ∑ⱼ Aⱼ` add up to `e` minus the remainder. -/
private theorem sum_range_coefficient_sharpTerm_right {μ : ℕ → ℝ} {ν : ℝ} (hμ : ∀ M, μ M ≤ μ 0)
    {e : Symbol n V W (μ 0)} {A : ∀ j, Symbol n V W (μ j)} {r : ∀ M, Symbol n V W (μ M)}
    (hr : ∀ M, e.coefficient - ∑ j ∈ range M, (A j).coefficient = (r M).coefficient)
    (B : Symbol n W U ν) (M i : ℕ) :
    ∑ j ∈ range M, (B.sharpTerm (A j) i).coefficient =
      (B.sharpTerm e i).coefficient - (B.sharpTerm (r M) i).coefficient := by
  have h₁ : e.coefficient = (e - inclusion (hμ M) (r M)).coefficient + (r M).coefficient := by
    simp
  have h₂ : (e - inclusion (hμ M) (r M)).coefficient =
      ∑ j ∈ range M, (1 : ℂ) • (A j).coefficient := by
    rw [coefficient_sub, coefficient_inclusion, ← hr M, sub_sub_cancel]
    simp
  rw [coefficient_sharpTerm_eq_add_right h₁, coefficient_sharpTerm_eq_sum_right _ _ A h₂,
    add_sub_cancel_right]
  simp

/-- **Left and right parametrix symbols agree modulo smoothing symbols.** Let `a` be a symbol of
order `m`, and `b_L`, `b_R` symbols of order `-m` such that the formal compositions `b_L # a` and
`a # b_R` are the identity: `1 ∼ ∑ₖ sharpTerm b_L a k` and `1 ∼ ∑ₖ sharpTerm a b_R k`. Then
`b_L - b_R` is smoothing. -/
theorem isSmoothing_sub_of_isAsymptoticSum_sharpTerm {a : Symbol n V W m}
    {bL bR : Symbol n W V (-m)}
    (hL : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (bL.sharpTerm a))
    (hR : IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm bR)) :
    (bL - bR).IsSmoothing := by
  choose r hr using isAsymptoticSum_iff.1 hL
  choose s hs using isAsymptoticSum_iff.1 hR
  have hμL : ∀ M : ℕ, -m + m - (M : ℝ) ≤ -m + m - ((0 : ℕ) : ℝ) := fun M ↦ by simp
  have hμR : ∀ M : ℕ, m + -m - (M : ℝ) ≤ m + -m - ((0 : ℕ) : ℝ) := fun M ↦ by simp
  -- Grouping the terms of degree at most `N` of `(b_L # a) # b_R` in two ways.
  have key (N : ℕ) : (bL - bR).coefficient =
      ∑ i ∈ range (N + 1), (bL.sharpTerm (s (N + 1 - i)) i).coefficient -
        ∑ j ∈ range (N + 1), ((r (N + 1 - j)).sharpTerm bR j).coefficient := by
    have hR' : ∑ k ∈ range (N + 1), ∑ p ∈ antidiagonal k,
        ((bL.sharpTerm a p.1).sharpTerm bR p.2).coefficient =
          bR.coefficient - ∑ j ∈ range (N + 1), ((r (N + 1 - j)).sharpTerm bR j).coefficient := by
      have hswap (k : ℕ) : ∑ p ∈ antidiagonal k,
          ((bL.sharpTerm a p.1).sharpTerm bR p.2).coefficient =
            ∑ p ∈ antidiagonal k, ((bL.sharpTerm a p.2).sharpTerm bR p.1).coefficient :=
        (Finset.Nat.sum_antidiagonal_swap
          (f := fun p ↦ ((bL.sharpTerm a p.1).sharpTerm bR p.2).coefficient)).symm
      simp_rw [hswap, Finset.Nat.sum_range_sum_antidiagonal fun j i ↦
          ((bL.sharpTerm a i).sharpTerm bR j).coefficient,
        sum_range_coefficient_sharpTerm_left hμL hr bR, sum_sub_distrib, sum_range_succ',
        coefficient_sharpTerm_congr (coefficient_inclusion _ _) rfl, const_sharpTerm_succ]
      funext p
      simp
    have hL' : ∑ k ∈ range (N + 1), ∑ p ∈ antidiagonal k,
        ((bL.sharpTerm a p.1).sharpTerm bR p.2).coefficient =
          bL.coefficient - ∑ i ∈ range (N + 1), (bL.sharpTerm (s (N + 1 - i)) i).coefficient := by
      simp_rw [sum_antidiagonal_coefficient_sharpTerm_assoc,
        Finset.Nat.sum_range_sum_antidiagonal fun i j ↦
          (bL.sharpTerm (a.sharpTerm bR j) i).coefficient,
        sum_range_coefficient_sharpTerm_right hμR hs bL, sum_sub_distrib, sum_range_succ',
        coefficient_sharpTerm_congr rfl (coefficient_inclusion _ _), sharpTerm_const_succ]
      funext p
      simp
    rw [coefficient_sub, ← sub_eq_sub_iff_sub_eq_sub]
    exact hL'.symm.trans hR'
  refine isSmoothing_iff.2 fun μ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (-m - μ)
  refine ⟨inclusion (m := -m - ((N + 1 : ℕ) : ℝ)) (by push_cast; linarith)
    (∑ i : Fin (N + 1), inclusion (by rw [Nat.cast_sub i.isLt.le]; push_cast; linarith)
        (bL.sharpTerm (s (N + 1 - i)) i) -
      ∑ j : Fin (N + 1), inclusion (by rw [Nat.cast_sub j.isLt.le]; push_cast; linarith)
        ((r (N + 1 - j)).sharpTerm bR j)), ?_⟩
  rw [key N, coefficient_inclusion, coefficient_sub, coefficient_sum, coefficient_sum]
  simp only [coefficient_inclusion]
  rw [Fin.sum_univ_eq_sum_range fun i ↦ (bL.sharpTerm (s (N + 1 - i)) i).coefficient,
    Fin.sum_univ_eq_sum_range fun j ↦ ((r (N + 1 - j)).sharpTerm bR j).coefficient]

/-- Changing the right factor by a smoothing symbol does not change an asymptotic sum of the formal
composition: if `e ∼ ∑ₖ sharpTerm a b k` and `b' - b` is smoothing, then
`e ∼ ∑ₖ sharpTerm a b' k`. -/
theorem isAsymptoticSum_sharpTerm_of_isSmoothing_sub_right {m' : ℝ} {a : Symbol n W U m'}
    {b b' : Symbol n V W m} {e : Symbol n V U (m' + m - (0 : ℕ))}
    (h : IsAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) e (a.sharpTerm b))
    (hb : (b' - b).IsSmoothing) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) e (a.sharpTerm b') := by
  refine isAsymptoticSum_iff.2 fun N ↦ ?_
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 h N
  obtain ⟨d, hd⟩ := isSmoothing_iff.1 hb (m - N)
  have hk (k : ℕ) : (a.sharpTerm b' k).coefficient =
      (a.sharpTerm b k).coefficient + (a.sharpTerm d k).coefficient :=
    coefficient_sharpTerm_eq_add_right (by rw [hd, coefficient_sub, add_sub_cancel]) a k
  refine ⟨r - ∑ k : Fin N, inclusion (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (a.sharpTerm d k), ?_⟩
  rw [coefficient_sub, coefficient_sum, ← hr]
  simp only [coefficient_inclusion, hk, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range fun k ↦ (a.sharpTerm d k).coefficient]
  abel

/-- Changing the left factor by a smoothing symbol does not change an asymptotic sum of the formal
composition: if `e ∼ ∑ₖ sharpTerm b a k` and `b' - b` is smoothing, then
`e ∼ ∑ₖ sharpTerm b' a k`. -/
theorem isAsymptoticSum_sharpTerm_of_isSmoothing_sub_left {m' : ℝ} {a : Symbol n V W m'}
    {b b' : Symbol n W U m} {e : Symbol n V U (m + m' - (0 : ℕ))}
    (h : IsAsymptoticSum (m := fun k : ℕ ↦ m + m' - k) e (b.sharpTerm a))
    (hb : (b' - b).IsSmoothing) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m + m' - k) e (b'.sharpTerm a) := by
  refine isAsymptoticSum_iff.2 fun N ↦ ?_
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 h N
  obtain ⟨d, hd⟩ := isSmoothing_iff.1 hb (m - N)
  have hk (k : ℕ) : (b'.sharpTerm a k).coefficient =
      (b.sharpTerm a k).coefficient + (d.sharpTerm a k).coefficient :=
    coefficient_sharpTerm_eq_add_left (by rw [hd, coefficient_sub, add_sub_cancel]) a k
  refine ⟨r - ∑ k : Fin N, inclusion (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (d.sharpTerm a k), ?_⟩
  rw [coefficient_sub, coefficient_sum, ← hr]
  simp only [coefficient_inclusion, hk, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range fun k ↦ (d.sharpTerm a k).coefficient]
  abel

end Parametrix

end Symbol

end TauCeti
