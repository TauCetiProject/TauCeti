/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.Height.Subspace.Basic

import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.NumberTheory.Height.Primitive

/-!
# An upper bound for the height of the span of an approximation domain

Let `K` be a number field, `S₀` a finite set of finite places of `K`, and `L v i` linear forms on
`ι → K`, linearly independent at every infinite place and at every place of `S₀`. For exponents
`c v i` bounded above by `e v` at each place, and a level `Q ≥ 1`, the points `x` of the
approximation domain `approxDomain S₀ L c Q` have every coordinate bounded at the place `v` by a
constant times `Q ^ e v`, and are integral at the other finite places. The Plücker coordinates
of `p` such points are therefore integral outside `S₀` and bounded at the place `v` by a constant
times `Q ^ (p * e v)`, so their logarithmic height is at most

```text
p * ((∑ v | ∞, mult v * e v) + ∑ v ∈ S₀, e v) * log Q + C
```

with `C` depending only on `K`, `S₀` and the forms, not on the exponents `c`, the bounds `e` or the
level `Q`. Applied to a basis of the span `V(Q) = approxSpan S₀ L c Q` drawn from the domain, this
bounds the relative logarithmic height of `V(Q)` by the same expression with `p = dim V(Q)`.

This is the upper half of the two-sided estimate on the height of `V(Q)` in Schmidt's proof of
the Subspace Theorem: when `V(Q)` is a hyperplane, `p = #ι - 1` and `e v` is the largest exponent
at `v`. It holds at every level `Q ≥ 1`, and its constant is uniform over all exponent systems.
The level cannot go below `1`: for `Q < 1` the bound `Q ^ c v i ≤ Q ^ e v` reverses, and with the
coordinate forms, `c = 0`, `e = 1` and nonempty `ι` the span is everything, of height `1`, at
every level, while the right-hand side tends to `-∞` as `Q → 0`.

## Main results

* `TauCeti.NumberField.exists_forall_logHeight_plucker_le_of_mem_approxDomain`: the bound for the
  Plücker coordinates of a linearly independent family of points of an approximation domain.
* `TauCeti.NumberField.exists_forall_relativeSubspaceLogHeight_approxSpan_le`: the bound for the
  relative logarithmic height of the span of an approximation domain.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.21, the upper bound.
-/

public section

open Module NumberField Height Set

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {ι : Type*} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

/-- One constant per absolute value, at least `1`, by which the forms control the coordinates
wherever they are linearly independent. -/
private theorem exists_one_le_forall_apply_le_mul [Finite ι] :
    ∃ A : AbsoluteValue K ℝ → ℝ, (∀ w, 1 ≤ A w) ∧ ∀ w, LinearIndependent K (L w) →
      ∀ (x : ι → K) (b : ℝ), (∀ i, w (L w i x) ≤ b) → ∀ j, w (x j) ≤ A w * b := by
  have h (w : AbsoluteValue K ℝ) : ∃ A : ℝ, 1 ≤ A ∧ (LinearIndependent K (L w) →
      ∀ (x : ι → K) (b : ℝ), (∀ i, w (L w i x) ≤ b) → ∀ j, w (x j) ≤ A * b) := by
    by_cases hw : LinearIndependent K (L w)
    · obtain ⟨A, -, hA⟩ := hw.exists_forall_abv_apply_le_mul w
      refine ⟨max A 1, le_max_right _ _, fun _ x b hb j ↦ (hA x b hb j).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) ((w.nonneg _).trans (hb j))
    · exact ⟨1, le_rfl, fun h ↦ (hw h).elim⟩
  choose A hA1 hA using h
  exact ⟨A, hA1, hA⟩

variable [NumberField K] [Finite ι] [LinearOrder ι] {S₀ : Finset (FinitePlace K)}

/-- The local bounds on the Plücker coordinates of `p` points of an approximation domain at a
level `Q ≥ 1`: `(#ι)! * A v ^ #ι * Q ^ (p * e v)` at an infinite place, the same without the
factorial at a place of `S₀`, and `1` at the other finite places. -/
private theorem exists_forall_apply_plucker_le
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    ∃ A : AbsoluteValue K ℝ → ℝ, (∀ w, 1 ≤ A w) ∧
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (e : AbsoluteValue K ℝ → ℝ), (∀ v i, c v i ≤ e v) →
      ∀ Q : ℝ, 1 ≤ Q → ∀ (p : ℕ) (x : Fin p → ι → K), p ≤ Nat.card ι →
        (∀ k, x k ∈ approxDomain S₀ L c Q) → ∀ s : powersetCard ι p,
          (∀ v : InfinitePlace K, v (plucker x s) ≤
            (Nat.card ι).factorial * (A v.1 ^ Nat.card ι * Q ^ (p * e v.1))) ∧
          (∀ v ∈ S₀, v (plucker x s) ≤ A v.1 ^ Nat.card ι * Q ^ (p * e v.1)) ∧
          ∀ v : FinitePlace K, v ∉ S₀ → v (plucker x s) ≤ 1 := by
  obtain ⟨A, hA1, hA⟩ := exists_one_le_forall_apply_le_mul (L := L)
  refine ⟨A, hA1, fun c e hce Q hQ p x hp hxmem s ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  -- Where the domain bounds the forms, every coordinate is at most `A w * Q ^ e w`.
  have hcoord (w : AbsoluteValue K ℝ) (hw : LinearIndependent K (L w))
      (hdom : ∀ k i, w (L w i (x k)) ≤ Q ^ c w i) (k : Fin p) (j : ι) :
      w (x k j) ≤ A w * Q ^ e w :=
    hA w hw (x k) _ (fun i ↦ (hdom k i).trans (Real.rpow_le_rpow_of_exponent_le hQ (hce w i))) j
  have hpow (w : AbsoluteValue K ℝ) :
      (A w * Q ^ e w) ^ p ≤ A w ^ Nat.card ι * Q ^ (p * e w) := by
    rw [mul_pow, mul_comm (p : ℝ), Real.rpow_mul_natCast hQ0.le]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (hA1 w) hp) (by positivity)
  rw [plucker_apply]
  refine ⟨fun v ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · refine (Matrix.abv_det_le_factorial_prod _ v.1 fun k j ↦ hcoord v.1 (hLinf v)
      (fun k i ↦ (mem_approxDomain.mp (hxmem k)).1 v i) k _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul (Nat.cast_le.mpr (Nat.factorial_le hp)) (hpow v.1)
      (pow_nonneg (mul_nonneg (zero_le_one.trans (hA1 _)) (by positivity)) _) (Nat.cast_nonneg _)
  · refine (Matrix.abv_det_le_prod_of_le _ v.add_le fun k j ↦ hcoord v.1 (hLfin v hv)
      (fun k i ↦ (mem_approxDomain.mp (hxmem k)).2.1 v hv i) k _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hpow v.1
  · exact Matrix.abv_det_le_one_of_isNonarchimedean v.add_le fun k j ↦
      (mem_approxDomain.mp (hxmem k)).2.2 v hv _

/-- **The height of the Plücker coordinates of points of an approximation domain.** For forms
independent at every infinite place and every place of `S₀`, there is a constant `C` such that for
all exponents `c` bounded above by `e v` at each place, every level `Q ≥ 1` and every linearly
independent family `x` of `p` points of `approxDomain S₀ L c Q`,
`logHeight (plucker x) ≤ p * ((∑ v | ∞, mult v * e v) + ∑ v ∈ S₀, e v) * log Q + C`. -/
theorem exists_forall_logHeight_plucker_le_of_mem_approxDomain
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    ∃ C : ℝ, ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (e : AbsoluteValue K ℝ → ℝ),
      (∀ v i, c v i ≤ e v) → ∀ Q : ℝ, 1 ≤ Q → ∀ (p : ℕ) (x : Fin p → ι → K),
        LinearIndependent K x → (∀ k, x k ∈ approxDomain S₀ L c Q) →
          logHeight (plucker x) ≤
            p * ((∑ v : InfinitePlace K, v.mult * e v.1) + ∑ v ∈ S₀, e v.1) * Real.log Q + C := by
  obtain ⟨A, hA1, hA⟩ := exists_forall_apply_plucker_le hLinf hLfin
  set n := Nat.card ι
  refine ⟨∑ v : InfinitePlace K, v.mult * (Real.log n.factorial + n * Real.log (A v.1)) +
    ∑ v ∈ S₀, n * Real.log (A v.1), fun c e hce Q hQ p x hx hxmem ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hp : p ≤ n := by
    have := Fintype.ofFinite ι
    simpa [n, Nat.card_eq_fintype_card] using hx.fintype_card_le_finrank
  have hbd := hA c e hce Q hQ p x hp hxmem
  obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp ((plucker_ne_zero_iff x).2 hx)
  have hsup (w : AbsoluteValue K ℝ) : 0 < ⨆ s, w (plucker x s) :=
    (w.pos hs₀).trans_le (le_ciSup (f := fun s ↦ w (plucker x s)) (Finite.bddAbove_range _) s₀)
  have : Nonempty (powersetCard ι p) := ⟨s₀⟩
  have hlog (w : AbsoluteValue K ℝ) :
      Real.log (A w ^ n * Q ^ (p * e w)) = n * Real.log (A w) + p * e w * Real.log Q := by
    rw [Real.log_mul (pow_pos (zero_lt_one.trans_le (hA1 w)) _).ne'
      (Real.rpow_pos_of_pos hQ0 _).ne', Real.log_pow, Real.log_rpow hQ0]
  -- The local bounds in logarithmic form.
  have hinf (v : InfinitePlace K) : Real.log (⨆ s, v (plucker x s)) ≤
      Real.log n.factorial + n * Real.log (A v.1) + p * e v.1 * Real.log Q := by
    refine (Real.log_le_log (hsup v.1) (ciSup_le fun s ↦ (hbd s).1 v)).trans_eq ?_
    rw [Real.log_mul (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
      (mul_pos (pow_pos (zero_lt_one.trans_le (hA1 v.1)) _) (Real.rpow_pos_of_pos hQ0 _)).ne',
      hlog, add_assoc]
  have hfin (v : FinitePlace K) (hv : v ∈ S₀) : Real.log (⨆ s, v (plucker x s)) ≤
      n * Real.log (A v.1) + p * e v.1 * Real.log Q :=
    (Real.log_le_log (hsup v.1) (ciSup_le fun s ↦ (hbd s).2.1 v hv)).trans_eq (hlog v.1)
  calc logHeight (plucker x)
      ≤ ∑ v : InfinitePlace K, v.mult * Real.log (⨆ s, v (plucker x s)) +
          ∑ v ∈ S₀, Real.log (⨆ s, v (plucker x s)) :=
        NumberField.logHeight_le_sum_of_forall_apply_le_one S₀ fun v hv s ↦ (hbd s).2.2 v hv
    _ ≤ ∑ v : InfinitePlace K, v.mult *
          (Real.log n.factorial + n * Real.log (A v.1) + p * e v.1 * Real.log Q) +
          ∑ v ∈ S₀, (n * Real.log (A v.1) + p * e v.1 * Real.log Q) := by
        gcongr with v _ v hv
        · exact hinf v
        · exact hfin v hv
    _ = _ := by
        have h₁ : ∑ v : InfinitePlace K, v.mult *
            (Real.log n.factorial + n * Real.log (A v.1) + p * e v.1 * Real.log Q) =
            ∑ v : InfinitePlace K, v.mult * (Real.log n.factorial + n * Real.log (A v.1)) +
              p * (∑ v : InfinitePlace K, v.mult * e v.1) * Real.log Q := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ ↦ by ring
        have h₂ : ∑ v ∈ S₀, (n * Real.log (A v.1) + p * e v.1 * Real.log Q) =
            ∑ v ∈ S₀, n * Real.log (A v.1) + p * (∑ v ∈ S₀, e v.1) * Real.log Q := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
        rw [h₁, h₂]
        ring

/-- **The height of the span of an approximation domain** (Bombieri–Gubler, Lemma 7.5.21, upper
bound). For forms independent at every infinite place and every place of `S₀`, there is a constant
`C` such that for all exponents `c` bounded above by `e v` at each place and every level `Q ≥ 1`,
the span `V(Q)` of `approxDomain S₀ L c Q` has relative logarithmic height at most
`dim V(Q) * ((∑ v | ∞, mult v * e v) + ∑ v ∈ S₀, e v) * log Q + C`. -/
theorem exists_forall_relativeSubspaceLogHeight_approxSpan_le
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    ∃ C : ℝ, ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (e : AbsoluteValue K ℝ → ℝ),
      (∀ v i, c v i ≤ e v) → ∀ Q : ℝ, 1 ≤ Q →
        (approxSpan S₀ L c Q).relativeSubspaceLogHeight ≤
          finrank K (approxSpan S₀ L c Q) *
            ((∑ v : InfinitePlace K, v.mult * e v.1) + ∑ v ∈ S₀, e v.1) * Real.log Q + C := by
  obtain ⟨C, hC⟩ := exists_forall_logHeight_plucker_le_of_mem_approxDomain hLinf hLfin
  refine ⟨C, fun c e hce Q hQ ↦ ?_⟩
  -- A basis of the span drawn from the domain computes the height.
  obtain ⟨x, hxmem, hspan, hx⟩ := Submodule.exists_fun_fin_finrank_span_eq K (approxDomain S₀ L c Q)
  have hheight := Submodule.relativeSubspaceLogHeight_span_range hx
  rw [hspan] at hheight
  rw [approxSpan_eq_span]
  exact hheight.trans_le (hC c e hce Q hQ _ x hx hxmem)

end TauCeti.NumberField
