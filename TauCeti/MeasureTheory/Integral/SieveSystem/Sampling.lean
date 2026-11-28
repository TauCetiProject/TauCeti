/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.SieveSystem.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Sampling one entry of a sieve system

To remove one entry from a finite sum over pairs of heads, split the sum according to
whether the two entries agree. The diagonal is a sample of a nonnegative density; its
integral is the sum at the previous stage. The off-diagonal is controlled by the decay at the
difference of the entries. This separates the recurrence from the particular Fourier sampling
inequality (for example, one-sided Poisson summation) used to bound the diagonal.

The recurrence is the one in `New.Filling.densitySum_le` (`New/Spanning/MainTerm/GlobalSieve.lean`)
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
-/

public section

open MeasureTheory Finset Function
open scoped ComplexOrder

namespace TauCeti.SieveSystem

variable {C U : Type*} [Ring C] [MeasureSpace C] [TopologicalSpace U]
  {u : C → U} {ι : U → C} {n : ℕ} {J : ℕ → (ℕ → U) → (ℕ → U) → ℂ} {ψ : C → ℂ} {En : ℝ}
  {Λ : ℕ → (ℕ → U) → ℝ} {β : C → ℝ}

/-- The sum over two families of heads is bounded by the decay at the difference of their
common entries, provided this difference maps to a unit. -/
theorem norm_sum_le_of_isUnit_sub {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i < n)
    (a : κ → ℕ → U) (b : κ' → ℕ → U) {v w : U}
    (ha : ∀ k, a k i = v) (hb : ∀ l, b l i = w) (hvw : IsUnit (ι v - ι w)) :
    ‖∑ k, ∑ l, J (i + 1) (a k) (b l)‖ ≤
      β (ι v - ι w) * ((∑ k, Λ (i + 1) (a k)) * ∑ l, Λ (i + 1) (b l)) := by
  calc
    _ ≤ ∑ k, ∑ l, β (ι v - ι w) * (Λ (i + 1) (a k) * Λ (i + 1) (b l)) :=
      norm_sum_le_of_le _ fun k _ ↦ norm_sum_le_of_le _ fun l _ ↦ by
        simpa only [ha k, hb l] using K.norm_le_of_isUnit_sub i hi (a k) (b l)
          (by simpa only [ha k, hb l] using hvw)
    _ = _ := by rw [sum_mul_sum]; simp only [mul_sum]

variable [TopologicalSpace C] [FirstCountableTopology C] {κ : Type} [Fintype κ]

/-- One step of sieve descent. Sample a new entry at position `i` from `S` in both heads.
If distinct samples give unit differences, their contribution is at most the off-diagonal
sum of decay bounds. For equal samples, apply `hsample`, a Fourier sampling inequality with
main factor `P` and error `ε` per unit of the Fourier bound `B`, then integrate out the new entry.
The last entry is not removed by this step (`i < n`). -/
theorem re_sum_update_le_of_sampling (K : SieveSystem u ι n J ψ En Λ β)
    {i : ℕ} (hi : i < n) (a : κ → ℕ → U) (S : Finset C) {P ε : ℝ}
    (hu : ∀ x ∈ S, ContinuousAt u x)
    (hsep : ∀ x ∈ S.offDiag, IsUnit (ι (u x.1) - ι (u x.2)))
    (hsample : ∀ (F : C → ℝ) (B : ℝ), Integrable F → (∀ x, 0 ≤ F x) →
      (∀ x ∈ S, LowerSemicontinuousAt (fun y ↦ ENNReal.ofReal (F y)) x) →
      (∀ ξ : C, IsUnit ξ → ‖∫ y, ψ (ξ * y) * (F y : ℂ)‖ ≤ β ξ * B) →
      ∑ x ∈ S, F x ≤ P * ((∫ y, F y) + ε * B)) :
    let b := fun (x : C) k ↦ update (a k) i (u x)
    let W := fun x ↦ ∑ k, Λ (i + 1) (b x k)
    (∑ x ∈ S, ∑ y ∈ S, ∑ k, ∑ l, J (i + 1) (b x k) (b y l)).re ≤
      P * ((∑ k, ∑ l, J i (a k) (a l)).re + ε * (∑ k, Λ i (a k)) ^ 2) +
        ∑ x ∈ S.offDiag, β (ι (u x.1) - ι (u x.2)) * (W x.1 * W x.2) := by
  classical
  dsimp only
  let b := fun (x : C) k ↦ update (a k) i (u x)
  let G := fun x y ↦ ∑ k, ∑ l, J (i + 1) (b x k) (b y l)
  have hentry (x : C) (k : κ) : b x k i = u x := update_self ..
  have hlsc (x : C) (hx : x ∈ S) :
      LowerSemicontinuousAt (fun y ↦ ENNReal.ofReal (G y y).re) x := by
    refine K.lowerSemicontinuousAt_sum hi.le b hentry (x := x) fun k ↦ ?_
    dsimp only [b]
    have hux := hu x hx
    fun_prop
  have hn (x : C) : 0 ≤ G x x := K.sum_nonneg hi.le (b x) (hentry x)
  have hreal (x : C) : ((G x x).re : ℂ) = G x x :=
    Complex.ext (by simp) (by simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp (hn x)).2)
  have htw (ξ : C) (hξ : IsUnit ξ) :
      ‖∫ y, ψ (ξ * y) * ((G y y).re : ℂ)‖ ≤ β ξ * (∑ k, Λ i (a k)) ^ 2 := by
    simp only [hreal]
    exact K.norm_integral_mul_sum_update_le hi.le a hξ
  have hint : Integrable (fun y ↦ G y y) := K.integrable_sum_update hi.le a
  have hdiag := hsample (fun x ↦ (G x x).re) ((∑ k, Λ i (a k)) ^ 2)
    hint.re (fun x ↦ (Complex.nonneg_iff.mp (hn x)).1) hlsc htw
  have hrec : (∫ y, (G y y).re) = (∑ k, ∑ l, J i (a k) (a l)).re :=
    (integral_re hint).trans (congrArg Complex.re (K.integral_sum_update hi.le a))
  rw [hrec] at hdiag
  have hsplit : ∑ x ∈ S, ∑ y ∈ S, G x y =
      (∑ x ∈ S, G x x) + ∑ x ∈ S.offDiag, G x.1 x.2 := by
    rw [← sum_product', ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _), sum_diag]
  rw [hsplit, Complex.add_re]
  refine add_le_add (by simpa only [Complex.re_sum] using hdiag) ?_
  rw [Complex.re_sum]
  exact sum_le_sum fun x hx ↦ (Complex.re_le_norm _).trans
    (K.norm_sum_le_of_isUnit_sub hi (b x.1) (b x.2) (hentry _) (hentry _) (hsep x hx))

end TauCeti.SieveSystem
