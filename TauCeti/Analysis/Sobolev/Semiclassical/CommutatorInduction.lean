/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.CoordinateDeriv
public import TauCeti.Analysis.Sobolev.Semiclassical.Basic
import TauCeti.Analysis.Calculus.CoordinateDeriv.LpNorm

/-!
# Raising semiclassical estimates by commutators

On `ℝⁿ` the semiclassical Sobolev norms `‖u‖_{k,h} = h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ u‖₂`
(`TauCeti.semiclassicalSobolevNorm`) form a scale whose steps are the semiclassical partial
derivatives `h ∂ⱼ`:

* `h ∂ⱼ` lowers the order by one with norm at most one, `‖h ∂ⱼ u‖_{k,h} ≤ ‖u‖_{k+1,h}`
  (`TauCeti.semiclassicalSobolevNorm_const_smul_coordinateDeriv_le`);
* conversely the order `k + 1` is controlled by the order `0` and the order `k` of the
  `h ∂ⱼ u`, `‖u‖_{k+1,h} ≤ ‖u‖_{0,h} + ∑ⱼ ‖h ∂ⱼ u‖_{k,h}`
  (`TauCeti.semiclassicalSobolevNorm_succ_le_add_sum`).

This file uses the two steps to lift an a priori estimate for an operator `L` from the lowest
level of the scale to every level, the commutator induction of elliptic regularity. Suppose that
on smooth fields `u` with all derivatives in `L²`

* at level zero, `‖u‖_{1,h} ≤ C₀ (‖L u‖_{0,h} + ‖u‖_{0,h})`, and
* the commutators of `L` with the `h ∂ⱼ` lose one order:
  `‖L (h ∂ⱼ u) - h ∂ⱼ (L u)‖_{k,h} ≤ B_k ‖u‖_{k+1,h}`.

Then `‖u‖_{k+1,h} ≤ C_k (‖L u‖_{k,h} + ‖u‖_{0,h})` for every `k`, with constants obeying
`C_(k+1) ≥ 1 + n C_k (1 + B_k C_k + C₀)`
(`TauCeti.semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le`). The step applies the
estimate at level `k` to the fields `h ∂ⱼ u` and moves `h ∂ⱼ` through `L` at the price of the
commutator. The lower-order term `‖u‖_{0,h}` is what an elliptic estimate gives on its own; when
`L` is injective with `‖u‖_{1,h} ≤ C₀ ‖L u‖_{0,h}` it is absorbed, and
`‖u‖_{k+1,h} ≤ C_k (1 + C₀) ‖L u‖_{k,h}`
(`TauCeti.semiclassicalSobolevNorm_succ_le_mul_of_commutator_le`).

The constants depend only on `C₀`, the `B_k` and the dimension, not on the scale `h`. For a
first-order operator `L = ∑ₗ aₗ h ∂ₗ + b` whose coefficients have semiclassical bounds
`hⁱ ‖Dⁱ aₗ‖, hⁱ ‖Dⁱ b‖ ≤ K`, the commutator `[h ∂ⱼ, L] = ∑ₗ h (∂ⱼ aₗ) h ∂ₗ + h ∂ⱼ b` is again of
first order with such bounds, so the multiplier estimates of
`TauCeti.Analysis.Sobolev.Semiclassical.Basic` give `B_k` independent of `h`
(`TauCeti.semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_sub_le`, in
`TauCeti.Analysis.Sobolev.Semiclassical.FirstOrder`). The linearized
gauge-fixed operators of Taubes's large-parameter Seiberg–Witten equations, written in a flat
chart in the rescaled variables, are of this form. The induction therefore runs through any finite
number of levels without a loss in `h`. It goes upward only: an estimate at a high level gives
none at a lower one.

## Main results

* `TauCeti.semiclassicalSobolevNorm_const_smul_coordinateDeriv_le`: `h ∂ⱼ` is a contraction from
  order `k + 1` to order `k`.
* `TauCeti.semiclassicalSobolevNorm_succ_le_add_sum`: the order `k + 1` from the order `0` and the
  order `k` of the semiclassical partial derivatives, through
  `TauCeti.lpNorm_iteratedFDeriv_succ_le_sum_coordinateDeriv`.
* `TauCeti.semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le`: the commutator induction.
* `TauCeti.semiclassicalSobolevNorm_succ_le_mul_of_commutator_le`: its form for an a priori
  estimate without lower-order term.

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory
open scoped ContDiff

variable {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The semiclassical partial derivatives -/

/-- **`h ∂ⱼ` lowers the order by one.** For `f` of class `C^(k+1)` whose derivatives of orders
`1, …, k + 1` are square integrable, and `h ≥ 0`, `‖h ∂ⱼ f‖_{k,h} ≤ ‖f‖_{k+1,h}`. -/
theorem semiclassicalSobolevNorm_const_smul_coordinateDeriv_le {k : ℕ} {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ (k + 1) f) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ (i + 1) f) 2) {h : ℝ}
    (hh : 0 ≤ h) (j : Fin n) :
    semiclassicalSobolevNorm k h (h • coordinateDeriv [j] f) ≤
      semiclassicalSobolevNorm (k + 1) h f := by
  rw [semiclassicalSobolevNorm_const_smul, abs_of_nonneg hh, semiclassicalSobolevNorm_succ_eq,
    semiclassicalSobolevNorm_def k, mul_left_comm, Finset.mul_sum]
  refine le_add_of_nonneg_of_le (semiclassicalSobolevNorm_nonneg 0 hh f)
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (Real.rpow_nonneg hh _))
  have hi : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [pow_succ', mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (lpNorm_iteratedFDeriv_coordinateDeriv_le (hf.of_le (by exact_mod_cast Nat.succ_le_succ hi))
      (hfm i hi) j) (pow_nonneg hh i)) hh

/-- **The order `k + 1` from the semiclassical partial derivatives.** For `f` of class `C^(k+1)`
and `h ≥ 0`, `‖f‖_{k+1,h} ≤ ‖f‖_{0,h} + ∑ⱼ ‖h ∂ⱼ f‖_{k,h}`. No integrability is assumed: a
derivative outside `L²` contributes `0` to the left side. -/
theorem semiclassicalSobolevNorm_succ_le_add_sum {k : ℕ} {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ (k + 1) f) {h : ℝ} (hh : 0 ≤ h) :
    semiclassicalSobolevNorm (k + 1) h f ≤
      semiclassicalSobolevNorm 0 h f +
        ∑ j, semiclassicalSobolevNorm k h (h • coordinateDeriv [j] f) := by
  simp only [semiclassicalSobolevNorm_const_smul, abs_of_nonneg hh]
  rw [semiclassicalSobolevNorm_succ_eq]
  simp only [semiclassicalSobolevNorm_def k]
  refine add_le_add le_rfl ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left
      (lpNorm_iteratedFDeriv_succ_le_sum_coordinateDeriv (hf.of_le ?_) one_le_two)
      (pow_nonneg hh _)) (Real.rpow_nonneg hh _)).trans_eq ?_)
  · exact_mod_cast Nat.succ_le_succ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring

/-! ### The commutator induction -/

/-- A semiclassical partial derivative of a smooth field with all derivatives in `L²` is again
such a field. -/
private theorem contDiff_const_smul_coordinateDeriv_and_memLp {u : CoordinateSpace n → F}
    (hu : ContDiff ℝ ∞ u) (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2) (h : ℝ) (j : Fin n) :
    ContDiff ℝ ∞ (h • coordinateDeriv [j] u) ∧
      ∀ i, MemLp (iteratedFDeriv ℝ i (h • coordinateDeriv [j] u)) 2 := by
  refine ⟨(hu.coordinateDeriv [j]).const_smul h, fun i ↦ ?_⟩
  have hD : iteratedFDeriv ℝ i (h • coordinateDeriv [j] u) =
      h • iteratedFDeriv ℝ i (coordinateDeriv [j] u) :=
    funext fun x ↦ iteratedFDeriv_const_smul_apply
      ((hu.coordinateDeriv [j]).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hD]
  exact (memLp_iteratedFDeriv_coordinateDeriv_of_forall hu hum j i).const_smul h

/-- Constants obeying `C (k + 1) ≥ 1 + n C k (1 + B k C k + C 0)` with `C 0, B k ≥ 0` are
nonnegative. -/
private theorem nonneg_of_one_add_mul_le {B C : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) (hC₀ : 0 ≤ C 0)
    (hC : ∀ k, 1 + n * C k * (1 + B k * C k + C 0) ≤ C (k + 1)) (k : ℕ) : 0 ≤ C k := by
  induction k with
  | zero => exact hC₀
  | succ k ih =>
    have : 0 ≤ (n : ℝ) * C k * (1 + B k * C k + C 0) := by
      have := hB k
      positivity
    linarith [hC k]

variable {L : (CoordinateSpace n → F) → CoordinateSpace n → G} {h : ℝ} {B C : ℕ → ℝ}

/-- One semiclassical partial derivative through the induction hypothesis: if the estimate holds
at level `k`, then `‖h ∂ⱼ u‖_{k+1,h} ≤ C_k (1 + B_k C_k + C₀) (‖L u‖_{k+1,h} + ‖u‖_{0,h})`. -/
private theorem semiclassicalSobolevNorm_const_smul_coordinateDeriv_le_mul (hh : 0 ≤ h)
    (hB : ∀ k, 0 ≤ B k) (hCk : ∀ k, 0 ≤ C k)
    (hL : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      ContDiff ℝ ∞ (L u) ∧ ∀ i, MemLp (iteratedFDeriv ℝ i (L u)) 2)
    (hbase : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) → semiclassicalSobolevNorm 1 h u ≤
        C 0 * (semiclassicalSobolevNorm 0 h (L u) + semiclassicalSobolevNorm 0 h u))
    (hcomm : ∀ k (j : Fin n) (u : CoordinateSpace n → F), ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u) - h • coordinateDeriv [j] (L u)) ≤
        B k * semiclassicalSobolevNorm (k + 1) h u)
    {k : ℕ} (ih : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) → semiclassicalSobolevNorm (k + 1) h u ≤
        C k * (semiclassicalSobolevNorm k h (L u) + semiclassicalSobolevNorm 0 h u))
    {u : CoordinateSpace n → F} (hu : ContDiff ℝ ∞ u) (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2)
    (j : Fin n) :
    semiclassicalSobolevNorm (k + 1) h (h • coordinateDeriv [j] u) ≤ C k * (1 + B k * C k + C 0) *
      (semiclassicalSobolevNorm (k + 1) h (L u) + semiclassicalSobolevNorm 0 h u) := by
  set X := semiclassicalSobolevNorm (k + 1) h (L u) + semiclassicalSobolevNorm 0 h u
  have hX₁ : semiclassicalSobolevNorm (k + 1) h (L u) ≤ X :=
    le_add_of_nonneg_right (semiclassicalSobolevNorm_nonneg 0 hh u)
  have hmono (l : ℕ) (hl : l ≤ k + 1) : semiclassicalSobolevNorm l h (L u) +
      semiclassicalSobolevNorm 0 h u ≤ X :=
    add_le_add_left (semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_of_le hl hh _) _
  obtain ⟨hLu, hLum⟩ := hL u hu hum
  obtain ⟨hv, hvm⟩ := contDiff_const_smul_coordinateDeriv_and_memLp hu hum h j
  have hw := contDiff_const_smul_coordinateDeriv_and_memLp hLu hLum h j
  -- Move `h ∂ⱼ` through `L`, at the price of the commutator.
  have hcomm' : semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u)) ≤
      X + B k * (C k * X) := by
    calc semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u))
        = semiclassicalSobolevNorm k h (h • coordinateDeriv [j] (L u) +
            (L (h • coordinateDeriv [j] u) - h • coordinateDeriv [j] (L u))) := by
          rw [add_sub_cancel]
      _ ≤ semiclassicalSobolevNorm k h (h • coordinateDeriv [j] (L u)) +
            semiclassicalSobolevNorm k h
              (L (h • coordinateDeriv [j] u) - h • coordinateDeriv [j] (L u)) :=
          semiclassicalSobolevNorm_add_le (hw.1.of_le (by exact_mod_cast le_top))
            (((hL _ hv hvm).1.sub hw.1).of_le (by exact_mod_cast le_top)) (fun i _ ↦ hw.2 i) hh
      _ ≤ X + B k * (C k * X) := by
          refine add_le_add ((semiclassicalSobolevNorm_const_smul_coordinateDeriv_le
            (hLu.of_le (by exact_mod_cast le_top)) (fun i _ ↦ hLum _) hh j).trans hX₁)
            ((hcomm k j u hu hum).trans (mul_le_mul_of_nonneg_left ?_ (hB k)))
          exact (ih u hu hum).trans (mul_le_mul_of_nonneg_left (hmono k k.le_succ) (hCk k))
  -- The lower-order term is controlled by the estimate at level zero.
  have hlow : semiclassicalSobolevNorm 0 h (h • coordinateDeriv [j] u) ≤ C 0 * X :=
    (semiclassicalSobolevNorm_const_smul_coordinateDeriv_le (hu.of_le (by exact_mod_cast le_top))
      (fun i _ ↦ hum _) hh j).trans ((hbase u hu hum).trans
        (mul_le_mul_of_nonneg_left (hmono 0 (Nat.zero_le _)) (hCk 0)))
  calc semiclassicalSobolevNorm (k + 1) h (h • coordinateDeriv [j] u)
      ≤ C k * (semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u)) +
          semiclassicalSobolevNorm 0 h (h • coordinateDeriv [j] u)) := ih _ hv hvm
    _ ≤ C k * (X + B k * (C k * X) + C 0 * X) := by gcongr; exact hCk k
    _ = C k * (1 + B k * C k + C 0) * X := by ring

/-- **The semiclassical commutator induction.** Let `L` map smooth fields on `ℝⁿ` with all
derivatives in `L²` to such fields, and let `h ≥ 0`. Suppose that on these fields `L` satisfies the
estimate `‖u‖_{1,h} ≤ C₀ (‖L u‖_{0,h} + ‖u‖_{0,h})` at level zero, and that its commutators with
the semiclassical partial derivatives `h ∂ⱼ` lose one order,
`‖L (h ∂ⱼ u) - h ∂ⱼ (L u)‖_{k,h} ≤ B_k ‖u‖_{k+1,h}`, with `B_k ≥ 0`. If the constants satisfy
`C_(k+1) ≥ 1 + n C_k (1 + B_k C_k + C₀)`, then at every level

`‖u‖_{k+1,h} ≤ C_k (‖L u‖_{k,h} + ‖u‖_{0,h})`.

The constants `C_k` are determined by `C₀`, the `B_k` and `n` alone, so the estimates are uniform in
`h` when the hypotheses are. -/
theorem semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le (hh : 0 ≤ h)
    (hB : ∀ k, 0 ≤ B k) (hC₀ : 0 ≤ C 0)
    (hC : ∀ k, 1 + n * C k * (1 + B k * C k + C 0) ≤ C (k + 1))
    (hL : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      ContDiff ℝ ∞ (L u) ∧ ∀ i, MemLp (iteratedFDeriv ℝ i (L u)) 2)
    (hbase : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) → semiclassicalSobolevNorm 1 h u ≤
        C 0 * (semiclassicalSobolevNorm 0 h (L u) + semiclassicalSobolevNorm 0 h u))
    (hcomm : ∀ k (j : Fin n) (u : CoordinateSpace n → F), ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u) - h • coordinateDeriv [j] (L u)) ≤
        B k * semiclassicalSobolevNorm (k + 1) h u)
    (k : ℕ) {u : CoordinateSpace n → F} (hu : ContDiff ℝ ∞ u)
    (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2) :
    semiclassicalSobolevNorm (k + 1) h u ≤
      C k * (semiclassicalSobolevNorm k h (L u) + semiclassicalSobolevNorm 0 h u) := by
  have hCk := nonneg_of_one_add_mul_le hB hC₀ hC
  induction k generalizing u with
  | zero => simpa using hbase u hu hum
  | succ k ih =>
    set X := semiclassicalSobolevNorm (k + 1) h (L u) + semiclassicalSobolevNorm 0 h u
    have hX : 0 ≤ X := add_nonneg (semiclassicalSobolevNorm_nonneg _ hh _)
      (semiclassicalSobolevNorm_nonneg _ hh _)
    calc semiclassicalSobolevNorm (k + 1 + 1) h u
        ≤ semiclassicalSobolevNorm 0 h u +
            ∑ j, semiclassicalSobolevNorm (k + 1) h (h • coordinateDeriv [j] u) :=
          semiclassicalSobolevNorm_succ_le_add_sum (hu.of_le (by exact_mod_cast le_top)) hh
      _ ≤ X + ∑ _j : Fin n, C k * (1 + B k * C k + C 0) * X :=
          add_le_add (le_add_of_nonneg_left (semiclassicalSobolevNorm_nonneg _ hh _))
            (Finset.sum_le_sum fun j _ ↦
              semiclassicalSobolevNorm_const_smul_coordinateDeriv_le_mul hh hB hCk hL hbase hcomm
                (fun _ hv hvm ↦ ih hv hvm) hu hum j)
      _ = (1 + n * C k * (1 + B k * C k + C 0)) * X := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ C (k + 1) * X := mul_le_mul_of_nonneg_right (hC k) hX

/-- **The commutator induction for an injective estimate.** If in
`semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le` the estimate at level zero has no
lower-order term, `‖u‖_{1,h} ≤ C₀ ‖L u‖_{0,h}`, then at every level
`‖u‖_{k+1,h} ≤ C_k (1 + C₀) ‖L u‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_succ_le_mul_of_commutator_le (hh : 0 ≤ h)
    (hB : ∀ k, 0 ≤ B k) (hC₀ : 0 ≤ C 0)
    (hC : ∀ k, 1 + n * C k * (1 + B k * C k + C 0) ≤ C (k + 1))
    (hL : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      ContDiff ℝ ∞ (L u) ∧ ∀ i, MemLp (iteratedFDeriv ℝ i (L u)) 2)
    (hbase : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
        semiclassicalSobolevNorm 1 h u ≤ C 0 * semiclassicalSobolevNorm 0 h (L u))
    (hcomm : ∀ k (j : Fin n) (u : CoordinateSpace n → F), ContDiff ℝ ∞ u →
      (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      semiclassicalSobolevNorm k h (L (h • coordinateDeriv [j] u) - h • coordinateDeriv [j] (L u)) ≤
        B k * semiclassicalSobolevNorm (k + 1) h u)
    (k : ℕ) {u : CoordinateSpace n → F} (hu : ContDiff ℝ ∞ u)
    (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2) :
    semiclassicalSobolevNorm (k + 1) h u ≤
      C k * (1 + C 0) * semiclassicalSobolevNorm k h (L u) := by
  have hLk : semiclassicalSobolevNorm 0 h (L u) ≤ semiclassicalSobolevNorm k h (L u) :=
    semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_of_le (Nat.zero_le k) hh _
  -- The lower-order term: `‖u‖_{0,h} ≤ ‖u‖_{1,h} ≤ C₀ ‖L u‖_{0,h} ≤ C₀ ‖L u‖_{k,h}`.
  have hu₀ : semiclassicalSobolevNorm 0 h u ≤ C 0 * semiclassicalSobolevNorm k h (L u) :=
    (semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_of_le zero_le_one hh u).trans
      ((hbase u hu hum).trans (mul_le_mul_of_nonneg_left hLk hC₀))
  calc semiclassicalSobolevNorm (k + 1) h u
      ≤ C k * (semiclassicalSobolevNorm k h (L u) + semiclassicalSobolevNorm 0 h u) :=
        semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le hh hB hC₀ hC hL
          (fun v hv hvm ↦ (hbase v hv hvm).trans (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (semiclassicalSobolevNorm_nonneg 0 hh v)) hC₀)) hcomm k hu hum
    _ ≤ C k * (semiclassicalSobolevNorm k h (L u) + C 0 * semiclassicalSobolevNorm k h (L u)) := by
        gcongr
        exact nonneg_of_one_add_mul_le hB hC₀ hC k
    _ = C k * (1 + C 0) * semiclassicalSobolevNorm k h (L u) := by ring

end TauCeti
