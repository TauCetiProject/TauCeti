/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Group.Indicator

/-!
# Sums of extended nonnegative reals bounded along a walk

Let `f : X → ℝ≥0∞` and let `x₀ ∈ X` be a root. Suppose that every point `x ≠ x₀` has a *step*
`σ`, taken from a family of injective maps `step σ : X → X`, which lowers a height
`height : X → ℕ` and satisfies `f x ≤ c σ * f (step σ x)`. Following the steps from any point
gives a walk down to `x₀` along which `f` changes by at most the factors `c σ`, and each point
is reached by a given step from at most one point. The result is that `∑' x, f x` is at most
`f x₀` times the geometric series of ratio `ρ = ∑' σ, c σ`:
`∑' x, f x ≤ f x₀ / (1 - ρ)` (`ENNReal.tsum_le_div_of_walk`), and the points other than `x₀`
contribute at most `ρ * (f x₀ / (1 - ρ))` (`ENNReal.tsum_compl_le_mul_div_of_walk`). Both hold
for every `ρ`: when `ρ ≥ 1` the right-hand side is `∞` unless `f x₀ = 0`, and then `f` vanishes.

This is how one bounds a sum over the lattices of a genus, or over the cosets of a compact open
subgroup, by walking through neighbouring lattices in Kneser's sense: each step to a neighbour
lowers the index of the lattice in a fixed one, and changes the summand by a factor that is
summable over all the steps. For instance, when the steps at a set of places have total weight
`ρ ≤ 1 / 3`, the moduli of the coefficients of the vacuum of the Weil representation, summed over
the cosets of a level at those places, are at most `1 / (1 - ρ) ≤ 3 / 2` times their value at the
trivial coset.

## Main results

* `ENNReal.tsum_le_tsum_mul_tsum_of_injective`: if each `f x` is at most `c σ * g (step σ x)` for
  some `σ`, with every `step σ` injective, then `∑' x, f x ≤ (∑' σ, c σ) * ∑' y, g y`.
* `ENNReal.tsum_le_of_walk`: summation along a walk, `∑' x, f x ≤ B` for every `B` with
  `f x₀ + (∑' σ, c σ) * B ≤ B`.
* `ENNReal.tsum_le_div_of_walk`, `ENNReal.tsum_compl_le_mul_div_of_walk`: the geometric bounds.

## Attribution

`ENNReal.tsum_le_of_walk` and its proof (truncate by the height and induct on the truncation
level, using the injectivity of the steps at each stage) follow `New.tsum_le_of_walk` and
`New.tsum_ite_lt_succ_le_of_walk` in the file
`src/Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241–250.
* M. Greenberg, J. Voight, *Lattice methods for algebraic modular forms on classical groups*,
  in *Computations with modular forms*, Contrib. Math. Comput. Sci. 6, Springer (2014), §5.
-/

public section

open Function
open scoped ENNReal

namespace ENNReal

variable {X Y S : Type*}

/-- **Domination along injective maps.** If every `f x` is at most `c σ * g (step σ x)` for some
`σ`, and every `step σ` is injective, then `∑' x, f x ≤ (∑' σ, c σ) * ∑' y, g y`. -/
theorem tsum_le_tsum_mul_tsum_of_injective {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞} {c : S → ℝ≥0∞}
    {step : S → X → Y} (h_inj : ∀ σ, Injective (step σ))
    (h_le : ∀ x, ∃ σ, f x ≤ c σ * g (step σ x)) :
    ∑' x, f x ≤ (∑' σ, c σ) * ∑' y, g y := by
  choose σ hσ using h_le
  -- `x` is recovered from the step it takes and the point it lands on.
  have h_pair : Injective fun x ↦ (σ x, step (σ x) x) := by
    intro x x' h_eq
    obtain ⟨hσx, h_image⟩ := Prod.mk.inj h_eq
    rw [hσx] at h_image
    exact h_inj (σ x') h_image
  calc ∑' x, f x ≤ ∑' x, c (σ x) * g (step (σ x) x) := _root_.tsum_le_tsum hσ
    _ ≤ ∑' p : S × Y, c p.1 * g p.2 :=
        _root_.tsum_comp_le_tsum_of_injective h_pair fun p ↦ c p.1 * g p.2
    _ = (∑' σ, c σ) * ∑' y, g y := by
        rw [_root_.tsum_prod']
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

variable {f : X → ℝ≥0∞} {c : S → ℝ≥0∞} {height : X → ℕ} {step : S → X → X} {x₀ : X}

/-- One stage of summation along a walk: the sum of `f` over the points of height below `N + 1`
is at most `f x₀` plus `∑' σ, c σ` times the sum over the points of height below `N`. -/
private theorem tsum_indicator_height_lt_succ_le (h_inj : ∀ σ, Injective (step σ))
    (h_step : ∀ x ≠ x₀, ∃ σ, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x))
    (N : ℕ) :
    ∑' x, {x | height x < N + 1}.indicator f x ≤
      f x₀ + (∑' σ, c σ) * ∑' x, {x | height x < N}.indicator f x := by
  have h_root : {x | height x < N + 1}.indicator f x₀ ≤ f x₀ :=
    Set.indicator_le_self' (fun _ _ ↦ zero_le) x₀
  -- Away from `x₀`, the truncation at `N + 1` is dominated by the truncation at `N` after a step.
  have h_off : ∀ x : ({x₀}ᶜ : Set X), ∃ σ, {x | height x < N + 1}.indicator f x ≤
      c σ * {x | height x < N}.indicator f (step σ x) := by
    intro x
    obtain ⟨σ, h_lt, h_le⟩ := h_step x x.property
    refine ⟨σ, ?_⟩
    by_cases hx : height x < N + 1
    · have h_next : height (step σ x) < N := h_lt.trans_le (Nat.lt_succ_iff.1 hx)
      simpa only [Set.indicator_apply, Set.mem_ofPred, hx, h_next, ite_true] using h_le
    · simp only [Set.indicator_apply, Set.mem_ofPred, hx, ite_false]
      exact zero_le
  have h_compl := tsum_le_tsum_mul_tsum_of_injective
    (fun σ ↦ (h_inj σ).comp Subtype.val_injective) h_off
  rw [← CompleteLattice.summable.tsum_add_tsum_compl (s := {x₀}) CompleteLattice.summable,
    tsum_singleton]
  exact add_le_add h_root h_compl

/-- **Summation along a walk.** Suppose that every point `x ≠ x₀` has a step `σ` that lowers the
height and satisfies `f x ≤ c σ * f (step σ x)`, and that every `step σ` is injective. Then
`∑' x, f x ≤ B` for every `B` with `f x₀ + (∑' σ, c σ) * B ≤ B`. -/
theorem tsum_le_of_walk {B : ℝ≥0∞} (h_inj : ∀ σ, Injective (step σ))
    (h_step : ∀ x ≠ x₀, ∃ σ, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x))
    (hB : f x₀ + (∑' σ, c σ) * B ≤ B) :
    ∑' x, f x ≤ B := by
  -- The sums truncated by the height are at most `B`, by induction on the truncation level.
  have h_trunc (N : ℕ) : ∑' x, {x | height x < N}.indicator f x ≤ B := by
    induction N with
    | zero => simp
    | succ N ih =>
      calc ∑' x, {x | height x < N + 1}.indicator f x
          ≤ f x₀ + (∑' σ, c σ) * ∑' x, {x | height x < N}.indicator f x :=
            tsum_indicator_height_lt_succ_le h_inj h_step N
        _ ≤ f x₀ + (∑' σ, c σ) * B := by gcongr
        _ ≤ B := hB
  -- Every finite partial sum is a partial sum of a truncation.
  rw [_root_.tsum_eq_iSup_sum]
  refine iSup_le fun t ↦ ?_
  calc ∑ x ∈ t, f x = ∑ x ∈ t, {x | height x < t.sup height + 1}.indicator f x :=
        Finset.sum_congr rfl fun x hx ↦ by
          rw [Set.indicator_of_mem]
          exact Set.mem_ofPred.2 (Nat.lt_succ_of_le (Finset.le_sup hx))
    _ ≤ B := (_root_.sum_le_tsum t).trans (h_trunc _)

/-- **The geometric bound along a walk.** Suppose that every point `x ≠ x₀` has a step `σ` that
lowers the height and satisfies `f x ≤ c σ * f (step σ x)`, and that every `step σ` is injective.
Then `∑' x, f x ≤ f x₀ / (1 - ∑' σ, c σ)`. -/
theorem tsum_le_div_of_walk (h_inj : ∀ σ, Injective (step σ))
    (h_step : ∀ x ≠ x₀, ∃ σ, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x)) :
    ∑' x, f x ≤ f x₀ / (1 - ∑' σ, c σ) := by
  refine tsum_le_of_walk h_inj h_step (le_of_eq ?_)
  -- `B = f x₀ / (1 - ρ)` solves `f x₀ + ρ * B = B`: for `ρ < 1` since `(1 - ρ) + ρ = 1`, and for
  -- `ρ ≥ 1` since then `B` is `∞`, or `0` when `f x₀ = 0`.
  set ρ := ∑' σ, c σ
  rcases lt_or_ge ρ 1 with hρ | hρ
  · have h_ne_zero : 1 - ρ ≠ 0 := (tsub_pos_of_lt hρ).ne'
    have h_ne_top : 1 - ρ ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
    calc f x₀ + ρ * (f x₀ / (1 - ρ)) = f x₀ / (1 - ρ) * ((1 - ρ) + ρ) := by
          rw [mul_add, ENNReal.div_mul_cancel h_ne_zero h_ne_top, mul_comm]
      _ = f x₀ / (1 - ρ) := by rw [tsub_add_cancel_of_le hρ.le, mul_one]
  · rw [tsub_eq_zero_of_le hρ]
    rcases eq_or_ne (f x₀) 0 with h_zero | h_ne
    · simp [h_zero]
    · simp [ENNReal.div_zero h_ne, ENNReal.mul_top (zero_lt_one.trans_le hρ).ne']

/-- **The points off the root, along a walk.** Suppose that every point `x ≠ x₀` has a step `σ`
that lowers the height and satisfies `f x ≤ c σ * f (step σ x)`, and that every `step σ` is
injective. Then, with `ρ = ∑' σ, c σ`, the sum of `f` over the points other than `x₀` is at most
`ρ * (f x₀ / (1 - ρ))`. -/
theorem tsum_compl_le_mul_div_of_walk (h_inj : ∀ σ, Injective (step σ))
    (h_step : ∀ x ≠ x₀, ∃ σ, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x)) :
    ∑' x : ({x₀}ᶜ : Set X), f x ≤ (∑' σ, c σ) * (f x₀ / (1 - ∑' σ, c σ)) := by
  have h_off : ∀ x : ({x₀}ᶜ : Set X), ∃ σ, f x ≤ c σ * f (step σ x) := fun x ↦
    (h_step x x.property).imp fun _ ↦ And.right
  calc ∑' x : ({x₀}ᶜ : Set X), f x ≤ (∑' σ, c σ) * ∑' x, f x :=
        tsum_le_tsum_mul_tsum_of_injective (fun σ ↦ (h_inj σ).comp Subtype.val_injective) h_off
    _ ≤ (∑' σ, c σ) * (f x₀ / (1 - ∑' σ, c σ)) := by
        gcongr
        exact tsum_le_div_of_walk h_inj h_step

end ENNReal
