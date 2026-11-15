/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.Combinatorics.Hive.Fibre
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The top hive and the direct vertical Pieri rule for hives

In the product chart of the triangular lattice, the vertex `(x, y, z)` sits in column `i = z` of
row `j = y + z`: the side `A → B` is column `0`, the side `B → C` is row `n`, and the side `C → A`
is the diagonal `i = j`. In this chart every unit rhombus belongs to one of three families, two of
which are the Gelfand–Tsetlin families comparing neighbouring steps of adjacent rows. Summing
them along the rows of an integer hive with boundary `(λ, μ, γ*)` shows that each step along row
`j` lies between two entries of `μ` (Gelfand–Tsetlin interlacing with top row `μ`), and that the
steps along a row weakly decrease.
Two consequences are proved directly from the hive inequalities, without passing through tableaux.

1. **The top hive.** The output `γ = λ + μ` has exactly one integer hive, `TauCeti.Hive.topHive`,
   with value `λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z` at `(x, y, z)`, so
   `hiveCount (productBoundary λ μ (λ + μ)) = 1`.
2. **Vertical Pieri.** If every entry of `μ` is `0` or `1`, then so is every step, and each row
   rises with slope one and then stays flat. The hive is `TauCeti.Hive.pieriHive`, and it exists
   exactly when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`, so the hive count is `1` in
   that case and `0` otherwise. This is the vertical Pieri rule `s_λ e_k = ∑ s_γ`, the sum over
   the `γ` with `γ / λ` a vertical strip of size `k`.

On the way, every output coordinate satisfies `λₖ + μₙ ≤ γₖ ≤ λₖ + μ₁`.

## Main definitions

* `TauCeti.Hive.topHive`: the unique integer hive with boundary `(λ, μ, (λ + μ)*)`.
* `TauCeti.Hive.pieriHive`: the integer hive with boundary `(λ, μ, γ*)` for a `0`/`1` weight `μ`.

## Main results

* `TauCeti.Hive.add_last_le_of_productBoundary`, `TauCeti.Hive.le_add_first_of_productBoundary`:
  `λₖ + μₙ ≤ γₖ ≤ λₖ + μ₁` whenever `(λ, μ, γ*)` carries an integer hive.
* `TauCeti.Hive.eq_topHive_of_boundary`, `TauCeti.Hive.hiveCount_productBoundary_add`: the top hive
  is unique.
* `TauCeti.Hive.eq_pieriHive_of_boundary`,
  `TauCeti.Hive.nonempty_fixedIntegerHive_productBoundary_iff`,
  `TauCeti.Hive.hiveCount_productBoundary_of_zero_le_le_one`: the direct vertical Pieri rule.

## References

* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §4, Proposition 4.
* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: proof of the saturation
  conjecture*, J. Amer. Math. Soc. **12** (1999), Appendix 2.
* I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford University Press,
  1995, Chapter I, (5.17).
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-- The vertex `(n - j, j - i, i)`: column `i` of row `j` in the product chart. -/
private def cv (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : Vertex n := ⟨n - j, j - i, i, by omega⟩

private theorem eq_cv (p : Vertex n) :
    p = cv n p.z (p.y + p.z) (Nat.le_add_left _ _) (by have := p.sum_eq; omega) := by
  have := p.sum_eq
  exact Vertex.ext (by simp only [cv]; omega) (by simp only [cv]; omega) rfl

/-- The chart displacement `(Δz, Δ(y + z))` of a unit lattice edge is one of six unit vectors. -/
private theorem chart_cases_of_sqDist_eq_two {p q : Vertex n} (h : p.sqDist q = 2) :
    (q.z = p.z ∧ q.y + q.z = p.y + p.z + 1) ∨ (p.z = q.z ∧ p.y + p.z = q.y + q.z + 1) ∨
    (q.z = p.z + 1 ∧ q.y + q.z = p.y + p.z + 1) ∨ (p.z = q.z + 1 ∧ p.y + p.z = q.y + q.z + 1) ∨
    (q.z = p.z + 1 ∧ q.y + q.z = p.y + p.z) ∨ (p.z = q.z + 1 ∧ p.y + p.z = q.y + q.z) := by
  rw [Vertex.sqDist_def] at h
  have hp := p.sum_eq
  have hq := q.sum_eq
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = (p.y : ℤ) - q.y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = (p.z : ℤ) - q.z := ⟨_, rfl⟩
  have hx : (p.x : ℤ) - q.x = -a - b := by omega
  rw [hx, ← ha, ← hb] at h
  have h₁ : 3 * (a * a) + (a + 2 * b) * (a + 2 * b) = 4 := by linear_combination 2 * h
  have h₂ : 3 * (b * b) + (2 * a + b) * (2 * a + b) = 4 := by linear_combination 2 * h
  have hsa : a * a ≤ 1 := by
    have := mul_self_nonneg (a + 2 * b)
    generalize a * a = t at *; generalize (a + 2 * b) * (a + 2 * b) = u at *; omega
  have hsb : b * b ≤ 1 := by
    have := mul_self_nonneg (2 * a + b)
    generalize b * b = t at *; generalize (2 * a + b) * (2 * a + b) = u at *; omega
  obtain ⟨ha0, ha1⟩ := abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr hsa)
  obtain ⟨hb0, hb1⟩ := abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr hsb)
  clear h₁ h₂ hsa hsb
  interval_cases a <;> interval_cases b <;> norm_num at h <;> omega

variable {R : Type*} [AddCommGroup R] [PartialOrder R]

/-- **Three-family rhombus criterion in the product chart.** A lattice function written as
`p ↦ G p.z (p.y + p.z)` (column `i = z`, row `j = y + z`) is rhombus-concave as soon as three
families of chart inequalities hold: the rhombi whose short diagonal lies along a row, and the two
Gelfand–Tsetlin families comparing neighbouring steps of adjacent rows. Every unit rhombus is one of
these, based at one of its acute corners. -/
private theorem isRhombusConcave_of_chart_families {G : ℕ → ℕ → R}
    (hG : (∀ i j, i ≤ j → j + 2 ≤ n →
        G i j + G (i + 1) (j + 2) ≤ G i (j + 1) + G (i + 1) (j + 1)) ∧
      (∀ i j, i + 1 ≤ j → j + 1 ≤ n →
        G i j + G (i + 2) (j + 1) ≤ G (i + 1) j + G (i + 1) (j + 1)) ∧
      (∀ i j, i + 1 ≤ j → j + 1 ≤ n →
        G i (j + 1) + G (i + 1) j ≤ G i j + G (i + 1) (j + 1))) :
    IsRhombusConcave (fun p : Vertex n => G p.z (p.y + p.z)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hG
  refine (isRhombusConcave_def _).mpr fun a b c d hr => ?_
  -- Pass to chart coordinates: the sides at `b` and the short diagonal are unit chart steps.
  have hab := chart_cases_of_sqDist_eq_two (by rw [Vertex.sqDist_comm]; exact hr.side_ab)
  have hbc := chart_cases_of_sqDist_eq_two hr.side_bc
  have hac := chart_cases_of_sqDist_eq_two hr.short
  have hmz := hr.midpoint_z
  have hmj : a.y + a.z + (c.y + c.z) = b.y + b.z + (d.y + d.z) := by
    have := hr.midpoint_y; omega
  have ha := a.sum_eq; have hb := b.sum_eq; have hc := c.sum_eq; have hd := d.sum_eq
  have hbn : b.y + b.z ≤ n := by omega
  have hdn : d.y + d.z ≤ n := by omega
  have hbz : b.z ≤ b.y + b.z := by omega
  have hdz : d.z ≤ d.y + d.z := by omega
  clear ha hb hc hd hr
  generalize a.y + a.z = aj at *
  generalize b.y + b.z = bj at *
  generalize c.y + c.z = cj at *
  generalize d.y + d.z = dj at *
  generalize a.z = ai at *
  generalize b.z = bi at *
  generalize c.z = ci at *
  generalize d.z = di at *
  -- The target inequality is symmetric in the acute corners and in the obtuse corners.
  have key : ∀ {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ : ℕ}, G p₁ p₂ + G q₁ q₂ ≤ G r₁ r₂ + G s₁ s₂ →
      (p₁ = bi ∧ p₂ = bj ∧ q₁ = di ∧ q₂ = dj ∨ p₁ = di ∧ p₂ = dj ∧ q₁ = bi ∧ q₂ = bj) →
      (r₁ = ai ∧ r₂ = aj ∧ s₁ = ci ∧ s₂ = cj ∨ r₁ = ci ∧ r₂ = cj ∧ s₁ = ai ∧ s₂ = aj) →
      G bi bj + G di dj ≤ G ai aj + G ci cj := by
    rintro p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ hle (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
      (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> simpa only [add_comm] using hle
  -- Of the `36` choices of the two sides at `b`, the short diagonal excludes `24`; each remaining
  -- one is a family based at the acute corner `b` or `d`.
  rcases hab with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;>
  rcases hbc with ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩ | ⟨f₁, f₂⟩ <;>
  first
    | (exfalso; omega)
    | exact key (h₁ bi bj (by omega) (by omega)) (by omega) (by omega)
    | exact key (h₁ di dj (by omega) (by omega)) (by omega) (by omega)
    | exact key (h₂ bi bj (by omega) (by omega)) (by omega) (by omega)
    | exact key (h₂ di dj (by omega) (by omega)) (by omega) (by omega)
    | exact key (h₃ bi (bj - 1) (by omega) (by omega)) (by omega) (by omega)
    | exact key (h₃ di (dj - 1) (by omega) (by omega)) (by omega) (by omega)

/-! ### Parallelograms in the other two orientations -/

section Parallelogram

variable [IsOrderedAddMonoid R] {f : Vertex n → R}

/-- Summed rhombus inequalities with sides along `(1, 0)` and `(0, 1)` in the product chart. -/
private theorem cv_parallelogram_row (hf : IsRhombusConcave f) {i i' j j' : ℕ} (hi : i ≤ i')
    (hij : i' ≤ j) (hj : j ≤ j') (hjn : j' ≤ n) :
    f (cv n i' j hij (by omega)) + f (cv n i j' (by omega) hjn) ≤
      f (cv n i j (by omega) (by omega)) + f (cv n i' j' (by omega) hjn) := by
  have hrot : IsRhombusConcave fun p : Vertex n => f p.rotate :=
    (isRhombusConcave_def _).mpr fun _ _ _ _ hr => (isRhombusConcave_def f).mp hf hr.rotate
  have := hrot.parallelogram_le (y₀ := i) (y₁ := i') (z₀ := n - j') (z₁ := n - j) hi (by omega)
    (by omega)
  rw [add_comm (f (cv n i' j _ _)), add_comm (f (cv n i j _ _))]
  convert this using 2 <;> congr 1 <;> ext <;> simp [cv] <;> omega

/-- Summed rhombus inequalities with sides along `(1, 0)` and `(1, 1)` in the product chart. -/
private theorem cv_parallelogram_diag (hf : IsRhombusConcave f) {i i' j t : ℕ} (hi : i ≤ i')
    (hij : i' ≤ j) (hjn : j + t ≤ n) :
    f (cv n (i' + t) (j + t) (by omega) hjn) + f (cv n i j (by omega) (by omega)) ≤
      f (cv n i' j hij (by omega)) + f (cv n (i + t) (j + t) (by omega) hjn) := by
  have hrot : IsRhombusConcave fun p : Vertex n => f p.rotate.rotate :=
    (isRhombusConcave_def _).mpr fun _ _ _ _ hr =>
      (isRhombusConcave_def f).mp hf hr.rotate.rotate
  have := hrot.parallelogram_le (y₀ := n - j - t) (y₁ := n - j) (z₀ := j - i') (z₁ := j - i)
    (by omega) (by omega) (by omega)
  convert this using 2 <;> congr 1 <;> ext <;> simp [cv] <;> omega

end Parallelogram

/-! ### Integer sequences with slopes in `{0, 1}` -/

/-- Locally decreasing successive differences decrease along the whole interval. -/
private theorem slope_antitone {g : ℕ → ℤ} {m : ℕ}
    (hanti : ∀ i, i + 2 ≤ m → g (i + 2) - g (i + 1) ≤ g (i + 1) - g i) {r s : ℕ} (hrs : r ≤ s)
    (hs : s < m) : g (s + 1) - g s ≤ g (r + 1) - g r := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih => exact (hanti s (by omega)).trans (ih (by omega))

/-- An integer sequence on `[0, m]` whose successive differences lie in `{0, 1}` and weakly decrease
first rises with slope one and then stays constant: `g i = g 0 + min i (g m - g 0)`. -/
private theorem eq_add_min_of_slope_mem_zero_one {g : ℕ → ℤ} {m : ℕ}
    (hslope : ∀ i < m, g i ≤ g (i + 1) ∧ g (i + 1) ≤ g i + 1)
    (hanti : ∀ i, i + 2 ≤ m → g (i + 2) - g (i + 1) ≤ g (i + 1) - g i) {i : ℕ} (hi : i ≤ m) :
    g i = g 0 + min (i : ℤ) (g m - g 0) := by
  -- The sequence is monotone with slope at most one; a unit step forces all earlier steps to be
  -- unit steps, and a flat step forces all later steps to be flat.
  have hmono : ∀ s t, s ≤ t → t ≤ m → g s ≤ g t := by
    intro s t hst htm
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih => exact (ih (by omega)).trans (hslope t (by omega)).1
  have hlip : ∀ s, s ≤ m → g s ≤ g 0 + s := by
    intro s hs
    induction s with
    | zero => simp
    | succ s ih => have := ih (by omega); have := hslope s (by omega); push_cast; omega
  have hrise : ∀ k, k < m → g (k + 1) = g k + 1 → g (k + 1) = g 0 + (k + 1) := by
    intro k
    induction k with
    | zero => intro _ h; simpa using h
    | succ k ih =>
      intro hk h
      have := slope_antitone hanti (r := k) (s := k + 1) (by omega) hk
      have := hslope k (by omega)
      have := ih (by omega) (by omega)
      push_cast; omega
  have hflat : ∀ k, k < m → g (k + 1) = g k → g m = g k := by
    intro k hk h
    suffices ∀ s, k ≤ s → s ≤ m → g s = g k from this m hk.le le_rfl
    intro s hks hsm
    induction s, hks using Nat.le_induction with
    | base => rfl
    | succ s hks ih =>
      have := slope_antitone hanti hks (by omega)
      have := hslope s (by omega)
      have := ih (by omega)
      omega
  induction i with
  | zero => have := hmono 0 m (Nat.zero_le m) le_rfl; simp; omega
  | succ i ih =>
    have ih := ih (by omega)
    have hs := hslope i (by omega)
    have hm := hmono (i + 1) m hi le_rfl
    have hl := hlip i (by omega)
    rcases (by omega : g (i + 1) = g i + 1 ∨ g (i + 1) = g i) with h | h
    · have := hrise i (by omega) h
      push_cast; omega
    · have := hflat i (by omega) h
      push_cast; omega

/-! ### Side values of a hive with product boundary -/

section SideValues

variable {lam μ γ : DominantWeight n} {h : IntegerHive n}

private theorem apply_cv_left (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (cv n 0 j (Nat.zero_le j) hj) = prefixSum j lam.1 := by
  have e : cv n 0 j (Nat.zero_le j) hj = Vertex.edgePoint n 0 ⟨j, by omega⟩ := by
    ext <;> simp [cv]
  rw [e, h.apply_edgePoint_zero, hb, productBoundary_zero, prefixSum_def]

private theorem apply_cv_right (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) (hj : j = n) : h (cv n i j hij hjn) = (∑ k, lam.1 k) + prefixSum i μ.1 := by
  subst j
  have e : cv n i n hij hjn = Vertex.edgePoint n 1 ⟨i, by omega⟩ := by
    ext <;> simp [cv]
  rw [e, h.apply_edgePoint_one, hb, productBoundary_zero, productBoundary_one, prefixSum_def]

private theorem apply_cv_diag (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (cv n j j le_rfl hj) = prefixSum j γ.1 := by
  have e : cv n j j le_rfl hj = Vertex.edgePoint n 2 ⟨n - j, by omega⟩ := by
    ext <;> simp [cv]; omega
  rw [e, h.apply_edgePoint_two, hb, productBoundary_two, prefixSum_def]
  simp only [DominantWeight.dual_apply, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_nbij' Fin.rev Fin.rev (fun i hi => ?_) (fun i hi => ?_) (fun i _ => by simp)
    (fun i _ => by simp) (fun i _ => rfl) <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢ <;> omega

/-- Gelfand–Tsetlin upper interlacing: a step along row `j` is at most the matching entry of `μ`. -/
private theorem row_step_le (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ} (hij : i < j)
    (hjn : j ≤ n) :
    h (cv n (i + 1) j hij hjn) - h (cv n i j hij.le hjn) ≤ μ.1 ⟨i, by omega⟩ := by
  have hpar := cv_parallelogram_row h.isRhombusConcave (i := i) (i' := i + 1) (j := j) (j' := n)
    (by omega) hij hjn le_rfl
  rw [apply_cv_right hb _ _ rfl, apply_cv_right hb _ _ rfl, prefixSum_succ (by omega)] at hpar
  linarith

/-- Gelfand–Tsetlin lower interlacing: a step along row `j` is at least the entry of `μ` reached by
moving diagonally to the side `x = 0`. -/
private theorem le_row_step (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ} (hij : i < j)
    (hjn : j ≤ n) :
    μ.1 ⟨i + (n - j), by omega⟩ ≤ h (cv n (i + 1) j hij hjn) - h (cv n i j hij.le hjn) := by
  have hpar := cv_parallelogram_diag h.isRhombusConcave (i := i) (i' := i + 1) (j := j)
    (t := n - j) (by omega) hij (by omega)
  have e : prefixSum (i + 1 + (n - j)) μ.1 =
      prefixSum (i + (n - j)) μ.1 + μ.1 ⟨i + (n - j), by omega⟩ := by
    rw [show i + 1 + (n - j) = i + (n - j) + 1 by omega]; exact prefixSum_succ _ _
  rw [apply_cv_right hb (i := i + 1 + (n - j)) (j := j + (n - j)) _ _ (by omega),
    apply_cv_right hb (i := i + (n - j)) (j := j + (n - j)) _ _ (by omega), e] at hpar
  linarith

/-- The steps along each row of a hive weakly decrease. -/
private theorem row_step_antitone (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ}
    (hij : i + 2 ≤ j) (hjn : j ≤ n) :
    h (cv n (i + 2) j hij hjn) - h (cv n (i + 1) j (by omega) hjn) ≤
      h (cv n (i + 1) j (by omega) hjn) - h (cv n i j (by omega) hjn) := by
  rcases Nat.lt_or_ge j n with hj | hj
  · have h₁ : h (cv n (i + 2) j hij hjn) + h (cv n (i + 1) (j + 1) (by omega) hj) ≤
        h (cv n (i + 1) j (by omega) hjn) + h (cv n (i + 2) (j + 1) (by omega) hj) :=
      cv_parallelogram_row h.isRhombusConcave (by omega) hij (by omega) hj
    have h₂ : h (cv n (i + 2) (j + 1) (by omega) hj) + h (cv n i j (by omega) hjn) ≤
        h (cv n (i + 1) j (by omega) hjn) + h (cv n (i + 1) (j + 1) (by omega) hj) :=
      cv_parallelogram_diag h.isRhombusConcave (i := i) (i' := i + 1) (t := 1) (by omega)
        (by omega) hj
    linarith
  · have hjn' : j = n := by omega
    rw [apply_cv_right hb _ _ hjn', apply_cv_right hb _ _ hjn', apply_cv_right hb _ _ hjn']
    have h₁ : prefixSum (i + 2) μ.1 = prefixSum (i + 1) μ.1 + μ.1 ⟨i + 1, by omega⟩ :=
      prefixSum_succ (by omega) μ.1
    have h₂ := prefixSum_succ (k := i) (by omega) μ.1
    have := μ.antitone (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, by omega⟩ from
      Fin.mk_le_mk.mpr (by omega))
    linarith

end SideValues

/-! ### Interlacing of the output with the two inputs -/

section Interlacing

variable {lam μ γ : DominantWeight n} {h : IntegerHive n}

/-- **Lower interlacing of the output**: if an integer hive has boundary `(λ, μ, γ*)`, then
`λₖ + μₙ ≤ γₖ` for every coordinate `k`. At the last coordinate this is
`TauCeti.Hive.last_le_of_productBoundary`. -/
theorem add_last_le_of_productBoundary (hb : h.boundary = productBoundary lam μ γ) (k : Fin n) :
    lam.1 k + μ.1 ⟨n - 1, Nat.sub_lt k.pos Nat.one_pos⟩ ≤ γ.1 k := by
  have hk := k.isLt
  have h₁ := cv_parallelogram_row h.isRhombusConcave (i := 0) (i' := k) (j := k) (j' := k + 1)
    (Nat.zero_le _) le_rfl (by omega) hk
  have h₂ := le_row_step hb (i := k) (j := k + 1) (by omega) hk
  have e : (⟨k + (n - (k + 1)), by omega⟩ : Fin n) = ⟨n - 1, Nat.sub_lt k.pos Nat.one_pos⟩ :=
    Fin.ext (by simp only; omega)
  rw [e] at h₂
  rw [apply_cv_left hb, apply_cv_left hb, apply_cv_diag hb] at h₁
  have e₁ := prefixSum_succ hk lam.1
  have e₂ := prefixSum_succ hk γ.1
  rw [Fin.eta] at e₁ e₂
  have h₃ : h (cv n (k + 1) (k + 1) le_rfl hk) = prefixSum (k + 1) γ.1 := apply_cv_diag hb hk
  linarith

/-- **Upper interlacing of the output**: if an integer hive has boundary `(λ, μ, γ*)`, then
`γₖ ≤ λₖ + μ₁` for every coordinate `k`. At the first coordinate this is
`TauCeti.Hive.first_le_of_productBoundary`. -/
theorem le_add_first_of_productBoundary (hb : h.boundary = productBoundary lam μ γ) (k : Fin n) :
    γ.1 k ≤ lam.1 k + μ.1 ⟨0, k.pos⟩ := by
  have hk := k.isLt
  have h₁ := cv_parallelogram_diag h.isRhombusConcave (i := 0) (i' := k) (j := k) (t := 1)
    (Nat.zero_le _) le_rfl hk
  have h₂ := row_step_le hb (i := 0) (j := k + 1) (by omega) hk
  rw [apply_cv_left hb, apply_cv_diag hb] at h₁
  have e₁ := prefixSum_succ hk lam.1
  have e₂ := prefixSum_succ hk γ.1
  rw [Fin.eta] at e₁ e₂
  have h₃ : h (cv n k k le_rfl hk.le) = prefixSum k γ.1 := apply_cv_diag hb hk.le
  have h₄ : h (cv n 0 (k + 1) (Nat.zero_le _) hk) = prefixSum (k + 1) lam.1 := apply_cv_left hb hk
  linarith

end Interlacing

/-! ### The top hive at `γ = λ + μ` -/

section TopHive

/-- The **top hive** of `(λ, μ)`: its value at `(x, y, z)` is `λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z`.
Its boundary is `(λ, μ, (λ + μ)*)` (`TauCeti.Hive.boundary_topHive`), and it is the only integer
hive with that boundary (`TauCeti.Hive.eq_topHive_of_boundary`). -/
def topHive (lam μ : DominantWeight n) : IntegerHive n where
  value p := prefixSum (p.y + p.z) lam.1 + prefixSum p.z μ.1
  value_cornerA' := by simp
  le_of_isRhombus' {_ _ _ _} hr := (isRhombusConcave_def _).mp
    (isRhombusConcave_of_chart_families (n := n)
      (G := fun i j => prefixSum j lam.1 + prefixSum i μ.1)
      ⟨fun i j _ hjn => by
        have h₁ := prefixSum_succ (k := j) (by omega) lam.1
        have h₂ : prefixSum (j + 2) lam.1 = prefixSum (j + 1) lam.1 + lam.1 ⟨j + 1, by omega⟩ :=
          prefixSum_succ (by omega) lam.1
        have := lam.antitone (show (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, by omega⟩ from
          Fin.mk_le_mk.mpr (by omega))
        omega,
      fun i j hij hjn => by
        have h₁ := prefixSum_succ (k := i) (by omega) μ.1
        have h₂ : prefixSum (i + 2) μ.1 = prefixSum (i + 1) μ.1 + μ.1 ⟨i + 1, by omega⟩ :=
          prefixSum_succ (by omega) μ.1
        have := μ.antitone (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, by omega⟩ from
          Fin.mk_le_mk.mpr (by omega))
        omega,
      fun i j _ _ => by omega⟩) hr

@[simp] theorem topHive_apply (lam μ : DominantWeight n) (p : Vertex n) :
    topHive lam μ p = prefixSum (p.y + p.z) lam.1 + prefixSum p.z μ.1 := (rfl)

/-- The top hive has boundary `(λ, μ, (λ + μ)*)`. -/
theorem boundary_topHive (lam μ : DominantWeight n) :
    (topHive lam μ).boundary = productBoundary lam μ (lam + μ) := by
  ext s k
  have hk := k.isLt
  fin_cases s
  · simp [boundary_apply, prefixSum_succ hk]
  · have e₁ : n - (k + 1) + (k + 1) = n := by omega
    have e₂ : n - k + k = n := by omega
    simp [boundary_apply, e₁, e₂, prefixSum_succ hk]
  · have e : n - k = n - (k + 1) + 1 := by omega
    have hk' : n - (k + 1) < n := by omega
    have hrev : k.rev = ⟨n - (k + 1), hk'⟩ := Fin.ext (by simp)
    simp [boundary_apply, e, prefixSum_succ hk', hrev]
    abel

/-- **Uniqueness of the top hive**: summing rhombus inequalities along the rows of the product
chart pins every entry of an integer hive with boundary `(λ, μ, (λ + μ)*)`. -/
theorem eq_topHive_of_boundary {lam μ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ (lam + μ)) : h = topHive lam μ := by
  ext p
  have hp := p.sum_eq
  rw [congrArg h (eq_cv p), topHive_apply]
  have hij : p.z ≤ p.y + p.z := Nat.le_add_left _ _
  have hjn : p.y + p.z ≤ n := by omega
  have h₁ := cv_parallelogram_row h.isRhombusConcave (i := 0) (i' := p.z) (j := p.y + p.z)
    (j' := n) (Nat.zero_le _) hij hjn le_rfl
  have h₂ := cv_parallelogram_row h.isRhombusConcave (i := p.z) (i' := p.y + p.z)
    (j := p.y + p.z) (j' := n) hij le_rfl hjn le_rfl
  rw [apply_cv_left hb, apply_cv_right hb _ _ rfl, apply_cv_left hb] at h₁
  rw [apply_cv_diag hb, apply_cv_right hb _ _ rfl, apply_cv_right hb _ _ rfl] at h₂
  have e₁ := prefixSum_of_le le_rfl lam.1
  have e₂ : prefixSum (p.y + p.z) (lam + μ).1 = prefixSum (p.y + p.z) lam.1 +
      prefixSum (p.y + p.z) μ.1 := prefixSum_add _ _ _
  linarith

instance (lam μ : DominantWeight n) :
    Unique (FixedIntegerHive (productBoundary lam μ (lam + μ))) where
  default := ⟨topHive lam μ, boundary_topHive lam μ⟩
  uniq h := Subtype.ext (eq_topHive_of_boundary h.2)

/-- **The top coefficient is one**: `V_{λ + μ}` occurs exactly once in `V_λ ⊗ V_μ`, as a hive
count. -/
@[simp] theorem hiveCount_productBoundary_add (lam μ : DominantWeight n) :
    hiveCount (productBoundary lam μ (lam + μ)) = 1 := by
  rw [← card_fixedIntegerHive]; exact Fintype.card_unique

end TopHive

/-! ### Vertical Pieri -/

section Pieri

variable {lam μ γ : DominantWeight n}

/-- Partial sums of a `0`/`1` dominant weight: `μ₁ + ⋯ + μᵢ = min i |μ|`. -/
private theorem prefixSum_eq_min (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) {i : ℕ} (hi : i ≤ n) :
    prefixSum i μ.1 = min (i : ℤ) (∑ k, μ.1 k) := by
  have := eq_add_min_of_slope_mem_zero_one (g := fun i => prefixSum i μ.1) (m := n)
    (fun i hi => by rw [prefixSum_succ hi]; have := hμ ⟨i, hi⟩; omega)
    (fun i hi => by
      have h₁ : prefixSum (i + 2) μ.1 = prefixSum (i + 1) μ.1 + μ.1 ⟨i + 1, by omega⟩ :=
        prefixSum_succ (by omega) μ.1
      have h₂ := prefixSum_succ (k := i) (by omega) μ.1
      have := μ.antitone (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega))
      omega) hi
  simpa [prefixSum_of_le le_rfl] using this

/-- If `γ - λ` is a `0`/`1` vector, then `0 ≤ (γ - λ)₁ + ⋯ + (γ - λ)ⱼ ≤ j`. -/
private theorem prefixSum_sub_mem (hγ : ∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1) {j : ℕ}
    (hj : j ≤ n) :
    0 ≤ prefixSum j γ.1 - prefixSum j lam.1 ∧ prefixSum j γ.1 - prefixSum j lam.1 ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := ih (by omega)
    have := hγ ⟨j, by omega⟩
    rw [prefixSum_succ (by omega), prefixSum_succ (by omega)]
    push_cast; omega

/-- The **vertical Pieri hive** of `λ ⊆ γ`, for `γ - λ` a `0`/`1` vector: its value at `(x, y, z)`
is `λ₁ + ⋯ + λⱼ + min z ((γ - λ)₁ + ⋯ + (γ - λ)ⱼ)` with `j = y + z`, so each row of the product
chart rises with slope one and then stays flat. Its boundary is `(λ, μ, γ*)` for the `0`/`1`
weight `μ` with `|μ| = |γ| - |λ|` (`TauCeti.Hive.boundary_pieriHive`). -/
def pieriHive (lam γ : DominantWeight n) (hγ : ∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1) :
    IntegerHive n where
  value p := prefixSum (p.y + p.z) lam.1 +
    min (p.z : ℤ) (prefixSum (p.y + p.z) γ.1 - prefixSum (p.y + p.z) lam.1)
  value_cornerA' := by simp
  le_of_isRhombus' {_ _ _ _} hr := (isRhombusConcave_def _).mp
    (isRhombusConcave_of_chart_families (n := n)
      (G := fun i j => prefixSum j lam.1 + min (i : ℤ) (prefixSum j γ.1 - prefixSum j lam.1))
      ⟨fun i j _ hjn => by
        have h₁ := prefixSum_succ (k := j) (by omega) lam.1
        have h₂ : prefixSum (j + 2) lam.1 = prefixSum (j + 1) lam.1 + lam.1 ⟨j + 1, by omega⟩ :=
          prefixSum_succ (by omega) lam.1
        have h₃ := prefixSum_succ (k := j) (by omega) γ.1
        have h₄ : prefixSum (j + 2) γ.1 = prefixSum (j + 1) γ.1 + γ.1 ⟨j + 1, by omega⟩ :=
          prefixSum_succ (by omega) γ.1
        have hle : (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
        have := lam.antitone hle
        have := γ.antitone hle
        have := hγ ⟨j, by omega⟩
        have := hγ ⟨j + 1, by omega⟩
        push_cast; omega,
      fun i j _ hjn => by
        have h₁ := prefixSum_succ (k := j) (by omega) lam.1
        have h₃ := prefixSum_succ (k := j) (by omega) γ.1
        have := hγ ⟨j, by omega⟩
        push_cast; omega,
      fun i j _ hjn => by
        have h₁ := prefixSum_succ (k := j) (by omega) lam.1
        have h₃ := prefixSum_succ (k := j) (by omega) γ.1
        have := hγ ⟨j, by omega⟩
        push_cast; omega⟩) hr

@[simp] theorem pieriHive_apply (hγ : ∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1) (p : Vertex n) :
    pieriHive lam γ hγ p = prefixSum (p.y + p.z) lam.1 +
      min (p.z : ℤ) (prefixSum (p.y + p.z) γ.1 - prefixSum (p.y + p.z) lam.1) := (rfl)

/-- The vertical Pieri hive has boundary `(λ, μ, γ*)` for every `0`/`1` weight `μ` with
`|λ| + |μ| = |γ|`. -/
theorem boundary_pieriHive (hγ : ∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1)
    (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) (hsum : ∑ i, γ.1 i = ∑ i, lam.1 i + ∑ i, μ.1 i) :
    (pieriHive lam γ hγ).boundary = productBoundary lam μ γ := by
  ext s k
  have hk := k.isLt
  fin_cases s
  · have h₀ := prefixSum_sub_mem hγ (j := k) (by omega)
    have h₁ := prefixSum_sub_mem hγ (j := k + 1) (by omega)
    have e := prefixSum_succ hk lam.1
    rw [Fin.eta] at e
    simp [boundary_apply]
    omega
  · have e₁ : n - (k + 1) + (k + 1) = n := by omega
    have e₂ : n - k + k = n := by omega
    have m₀ := prefixSum_eq_min hμ (i := k) (by omega)
    have m₁ := prefixSum_eq_min hμ (i := k + 1) (by omega)
    have e := prefixSum_succ hk μ.1
    rw [Fin.eta] at e
    simp [boundary_apply, e₁, e₂, prefixSum_of_le le_rfl]
    omega
  · have e : n - k = n - (k + 1) + 1 := by omega
    have hk' : n - (k + 1) < n := by omega
    have hrev : k.rev = ⟨n - (k + 1), hk'⟩ := Fin.ext (by simp)
    have h₀ := prefixSum_sub_mem hγ (j := n - (k + 1)) (by omega)
    have h₁ := prefixSum_sub_mem hγ (j := n - (k + 1) + 1) (by omega)
    have e₁ := prefixSum_succ hk' lam.1
    have e₂ := prefixSum_succ hk' γ.1
    simp [boundary_apply, e, hrev]
    omega

/-- When the side `B → C` of an integer hive is a `0`/`1` weight, each row of the product chart
rises with slope one and then stays flat. -/
private theorem apply_eq_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1)
    (p : Vertex n) :
    h p = prefixSum (p.y + p.z) lam.1 +
      min (p.z : ℤ) (prefixSum (p.y + p.z) γ.1 - prefixSum (p.y + p.z) lam.1) := by
  have hp := p.sum_eq
  rw [congrArg h (eq_cv p)]
  generalize_proofs hij hjn
  generalize p.y + p.z = j at *
  generalize p.z = i at *
  let g : ℕ → ℤ := fun i' => if hi' : i' ≤ j then h (cv n i' j hi' hjn) else 0
  have hg : ∀ i' (hi' : i' ≤ j), g i' = h (cv n i' j hi' hjn) := fun i' hi' => by simp [g, hi']
  have key := eq_add_min_of_slope_mem_zero_one (g := g) (m := j)
    (fun i' hi' => by
      rw [hg i' hi'.le, hg (i' + 1) hi']
      have := row_step_le hb hi' hjn
      have := le_row_step hb hi' hjn
      have := hμ ⟨i', by omega⟩
      have := hμ ⟨i' + (n - j), by omega⟩
      constructor <;> linarith)
    (fun i' hi' => by
      rw [hg i' (by omega), hg (i' + 1) (by omega), hg (i' + 2) hi']
      exact row_step_antitone hb hi' hjn) hij
  rw [hg i hij, hg 0 (Nat.zero_le _), hg j le_rfl, apply_cv_left hb, apply_cv_diag hb] at key
  exact key

/-- **Vertical strip condition**: if an integer hive has boundary `(λ, μ, γ*)` with `μ` a `0`/`1`
weight, then `γ - λ` is a `0`/`1` vector. -/
theorem le_and_le_add_one_of_productBoundary {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) (k : Fin n) :
    lam.1 k ≤ γ.1 k ∧ γ.1 k ≤ lam.1 k + 1 := by
  have := add_last_le_of_productBoundary hb k
  have := le_add_first_of_productBoundary hb k
  have := hμ ⟨n - 1, Nat.sub_lt k.pos Nat.one_pos⟩
  have := hμ ⟨0, k.pos⟩
  omega

/-- **Uniqueness for vertical Pieri**: an integer hive whose side `B → C` is a `0`/`1` weight is
the vertical Pieri hive of its other two sides. -/
theorem eq_pieriHive_of_boundary {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ)
    (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) :
    h = pieriHive lam γ (le_and_le_add_one_of_productBoundary hb hμ) :=
  ext (apply_eq_of_zero_le_le_one hb hμ)

/-- For a `0`/`1` weight `μ`, there is at most one integer hive with boundary `(λ, μ, γ*)`. -/
theorem subsingleton_fixedIntegerHive_productBoundary (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) :
    Subsingleton (FixedIntegerHive (productBoundary lam μ γ)) :=
  ⟨fun h₁ h₂ => Subtype.ext <| (eq_pieriHive_of_boundary h₁.2 hμ).trans
    (eq_pieriHive_of_boundary h₂.2 hμ).symm⟩

/-- **Direct vertical Pieri rule for hives**: when `μ` is a `0`/`1` weight (the highest weight of
an exterior power `Λᵏ ℂⁿ`, up to its size), the integer hives with boundary `(λ, μ, γ*)` exist
exactly when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`. -/
theorem nonempty_fixedIntegerHive_productBoundary_iff (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) :
    Nonempty (FixedIntegerHive (productBoundary lam μ γ)) ↔
      (∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1) ∧
        ∑ i, γ.1 i = ∑ i, lam.1 i + ∑ i, μ.1 i := by
  refine ⟨fun ⟨⟨h, hb⟩⟩ => ⟨le_and_le_add_one_of_productBoundary hb hμ,
    (sum_eq_of_productBoundary hb).symm⟩, fun ⟨hγ, hsum⟩ => ⟨⟨pieriHive lam γ hγ,
      boundary_pieriHive hγ hμ hsum⟩⟩⟩

/-- **Vertical Pieri rule as a hive count**: for a `0`/`1` weight `μ`, the hive count of
`(λ, μ, γ*)` is `1` when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`, and `0` otherwise. -/
theorem hiveCount_productBoundary_of_zero_le_le_one (hμ : ∀ i, 0 ≤ μ.1 i ∧ μ.1 i ≤ 1) :
    hiveCount (productBoundary lam μ γ) =
      if (∀ i, lam.1 i ≤ γ.1 i ∧ γ.1 i ≤ lam.1 i + 1) ∧
          ∑ i, γ.1 i = ∑ i, lam.1 i + ∑ i, μ.1 i then 1 else 0 := by
  have := subsingleton_fixedIntegerHive_productBoundary (lam := lam) (γ := γ) hμ
  split_ifs with hc
  · rw [← card_fixedIntegerHive]
    have : Nonempty (FixedIntegerHive (productBoundary lam μ γ)) :=
      (nonempty_fixedIntegerHive_productBoundary_iff hμ).mpr hc
    exact Fintype.card_eq_one_iff_nonempty_unique.mpr
      ⟨uniqueOfSubsingleton (Classical.choice this)⟩
  · rw [hiveCount_eq_zero_iff]
    exact not_nonempty_iff.mp fun hne =>
      hc ((nonempty_fixedIntegerHive_productBoundary_iff hμ).mp hne)

end Pieri

/-! ### Rank-`2` checks -/

section Checks

/-- For `λ = μ = (1, 0)`, the top hive is the hive `exampleTwo` of the output `(2, 0)`. -/
theorem topHive_two_std_std : topHive ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ = exampleTwo :=
  (eq_topHive_of_boundary (boundary_exampleTwo.trans (by
    congr 1; ext i; fin_cases i <;> rfl))).symm

/-- Rank-`2` vertical Pieri checks with `μ = (1, 0)`: for `λ = (2, 0)` the outputs `(3, 0)` and
`(2, 1)` each occur once; for `λ = (1, 1)` the output `(2, 1)` occurs once, while `(2, 0)`, whose
difference `(1, -1)` with `λ` is not a `0`/`1` vector, does not occur. -/
theorem hiveCount_two_pieri_checks :
    hiveCount (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![3, 0], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 0 := by
  simp only [hiveCount_productBoundary_of_zero_le_le_one (μ := ⟨![1, 0], by decide⟩) (by decide)]
  decide

end Checks

end TauCeti.Hive
