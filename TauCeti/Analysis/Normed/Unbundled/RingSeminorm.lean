/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Additional lemmas on ring seminorms

This file extends `Mathlib.Analysis.Normed.Unbundled.RingSeminorm` with general estimates for
`RingSeminorm` and ring seminorms on pairs of algebras.

A multiplicative cross-norm identity for two algebra maps transfers scalar homogeneity
from the source seminorm to the target. A contractive algebra map also forces both
seminorms to be at most one on the unit. These facts let cross-norm constructions avoid
assuming target homogeneity and unit bounds separately.

## Main results

* `RingSeminorm.map_add_pow_le_of_forall_map_pow_le`: geometric upper bounds on `μ (x ^ k)` and
  `μ (y ^ k)` yield a geometric upper bound on `μ ((x + y) ^ n)`.
* `IsPowMul.iInf`, `RingSeminorm.iInfOfDirected`, `RingSeminorm.isPowMul_iInfOfDirected`: the
  pointwise infimum of a nonempty downward-directed family of ring seminorms is a `RingSeminorm`,
  and preserves power-multiplicativity.
* `RingSeminorm.apply_one_le_one_of_pair`: a contractive algebra map and a multiplicative
  cross-norm identity force both seminorms to be at most one on the unit.
* `RingSeminorm.smul_eq_of_pair`: homogeneity transfers along a multiplicative cross-norm
  identity when the source seminorm is homogeneous and at most one on the unit.
-/

public section

/-- The pointwise infimum of a nonempty family of nonnegative power-multiplicative functions is
power-multiplicative. -/
theorem IsPowMul.iInf {R : Type*} {ι : Sort*} [Pow R ℕ] [Nonempty ι] {f : ι → R → ℝ}
    (hf_nonneg : ∀ i a, 0 ≤ f i a) (hf_pm : ∀ i, IsPowMul (f i)) :
    IsPowMul (fun a ↦ ⨅ i, f i a) := by
  intro a k hk
  have hmono : Monotone fun t : ℝ ↦ (max t 0) ^ k := fun x y hxy ↦
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 hxy) k
  have hcont : Continuous fun t : ℝ ↦ (max t 0) ^ k :=
    (continuous_id.max continuous_const).pow k
  have hbdd : BddBelow (Set.range fun i ↦ f i a) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact hf_nonneg i a⟩
  have hmap := (hmono.map_ciInf_of_continuousAt hcont.continuousAt hbdd).symm
  have hnonneg : 0 ≤ ⨅ i, f i a := le_ciInf fun i ↦ hf_nonneg i a
  simp only [max_eq_left hnonneg, fun i ↦ max_eq_left (hf_nonneg i a),
    fun i ↦ (hf_pm i a hk).symm] at hmap
  exact hmap

namespace RingSeminorm

section CommRing

variable {R : Type*} [CommRing R]

/-- Binomial power bound: geometric upper bounds on `μ (x ^ k)` and `μ (y ^ k)` yield a
geometric upper bound on `μ ((x + y) ^ n)`. -/
theorem map_add_pow_le_of_forall_map_pow_le (μ : RingSeminorm R) {x y : R} {Cx Cy a b : ℝ}
    (hCx : ∀ k, μ (x ^ k) ≤ Cx * a ^ k) (hCy : ∀ k, μ (y ^ k) ≤ Cy * b ^ k) (n : ℕ) :
    μ ((x + y) ^ n) ≤ Cx * Cy * (a + b) ^ n := by
  calc μ ((x + y) ^ n)
      = μ (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * n.choose k) := by rw [add_pow]
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ (x ^ k * y ^ (n - k) * n.choose k) :=
        Finset.map_sum_le_sum μ (Finset.range (n + 1)) _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (μ (x ^ k) * μ (y ^ (n - k))) := by
        gcongr with k
        have hchoose : μ (x ^ k * y ^ (n - k) * n.choose k) ≤
            (n.choose k : ℝ) * μ (x ^ k * y ^ (n - k)) := by
          simpa only [Finset.sum_const, Finset.card_range, ← nsmul_eq_mul', nsmul_eq_mul] using
            Finset.map_sum_le_sum μ (Finset.range (n.choose k)) (fun _ ↦ x ^ k * y ^ (n - k))
        exact hchoose.trans
          (mul_le_mul_of_nonneg_left (map_mul_le_mul μ _ _) (Nat.cast_nonneg _))
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((Cx * a ^ k) * (Cy * b ^ (n - k))) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left
          (mul_le_mul (hCx k) (hCy (n - k)) (apply_nonneg μ _) ((apply_nonneg μ _).trans (hCx k)))
          (Nat.cast_nonneg _)
    _ = Cx * Cy * ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * n.choose k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = Cx * Cy * (a + b) ^ n := by rw [← add_pow]

end CommRing

section Pair

variable {C A B : Type*}

/-- A contractive algebra map and a multiplicative cross-norm identity force both
seminorms to be at most one on the unit. -/
theorem apply_one_le_one_of_pair [CommSemiring C] [Ring A] [Ring B]
    [Algebra C A] [Algebra C B] (N : RingSeminorm A) (M : RingSeminorm B)
    (D L R : A →ₐ[C] B) (hD : ∀ x, M (D x) ≤ N x)
    (hLR : ∀ x y, M (L x * R y) = N x * N y) : N 1 ≤ 1 ∧ M 1 ≤ 1 := by
  have h := hD 1
  have h' := hLR 1 1
  simp only [map_one, mul_one] at h h'
  have hN : N 1 ≤ 1 := by nlinarith [apply_nonneg N 1]
  exact ⟨hN, h.trans hN⟩

/-- Homogeneity transfers to the target seminorm along a multiplicative cross-norm
identity when the source seminorm is homogeneous and at most one on the unit. -/
theorem smul_eq_of_pair [NormedField C] [Ring A] [Ring B]
    [Algebra C A] [Algebra C B] (N : RingSeminorm A) (M : RingSeminorm B)
    (hNsmul : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    (L R : A →ₐ[C] B) (hLR : ∀ x y, M (L x * R y) = N x * N y) (hN1 : N 1 ≤ 1)
    (c : C) (x : B) : M (c • x) = ‖c‖ * M x := by
  have hscalar (a : C) : M (algebraMap C B a) ≤ ‖a‖ := by
    have h := hLR (a • (1 : A)) 1
    simp only [map_smul, map_one, mul_one, hNsmul] at h
    rw [Algebra.algebraMap_eq_smul_one, h]
    calc
      ‖a‖ * N 1 * N 1 ≤ ‖a‖ * 1 * 1 := by gcongr
      _ = ‖a‖ := by ring
  have hle (a : C) (b : B) : M (a • b) ≤ ‖a‖ * M b := by
    rw [Algebra.smul_def]
    exact (map_mul_le_mul M _ _).trans
      (mul_le_mul_of_nonneg_right (hscalar a) (apply_nonneg M _))
  refine (hle c x).antisymm ?_
  by_cases hc : c = 0
  · simp [hc]
  have h := hle c⁻¹ (c • x)
  rw [inv_smul_smul₀ hc, norm_inv] at h
  have hmul := mul_le_mul_of_nonneg_left h (norm_nonneg c)
  rwa [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul] at hmul

end Pair

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

/-- The pointwise infimum of a nonempty downward-directed family of ring seminorms is a
`RingSeminorm`. -/
noncomputable def iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) : RingSeminorm R where
  toFun a := ⨅ i, p i a
  map_zero' := by simp only [map_zero, ciInf_const]
  add_le' a b := by
    have hbdd : BddBelow (Set.range fun i ↦ p i (a + b)) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) (a + b)⟩
    refine le_ciInf_add_ciInf fun i j ↦ ?_
    obtain ⟨k, hki, hkj⟩ := hp i j
    exact (ciInf_le hbdd k).trans
      ((map_add_le_add (p k) a b).trans (add_le_add (hki a) (hkj b)))
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have hbdd : BddBelow (Set.range fun i ↦ p i (a * b)) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact apply_nonneg (p i) (a * b)⟩
    have hpair (i j : ι) : (⨅ k, p k (a * b)) ≤ p i a * p j b := by
      obtain ⟨k, hki, hkj⟩ := hp i j
      exact (ciInf_le hbdd k).trans
        ((map_mul_le_mul (p k) a b).trans (mul_le_mul (hki a) (hkj b)
          (apply_nonneg (p k) b) (apply_nonneg (p i) a)))
    have h1 (i : ι) : (⨅ k, p k (a * b)) ≤ p i a * ⨅ j, p j b := by
      rw [Real.mul_iInf_of_nonneg (apply_nonneg (p i) a)]
      exact le_ciInf fun j ↦ hpair i j
    have hnonneg_b : 0 ≤ ⨅ j, p j b := le_ciInf fun j ↦ apply_nonneg (p j) b
    rw [Real.iInf_mul_of_nonneg hnonneg_b]
    exact le_ciInf h1

/-- Evaluating `iInfOfDirected p hp` at `a` gives `⨅ i, p i a`. -/
@[simp]
theorem iInfOfDirected_apply {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (a : R) :
    iInfOfDirected p hp a = ⨅ i, p i a :=
  (rfl)

/-- The underlying function of `iInfOfDirected p hp` is `fun a ↦ ⨅ i, p i a`. -/
@[simp]
theorem coe_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) :
    ⇑(iInfOfDirected p hp) = fun a ↦ ⨅ i, p i a :=
  (rfl)

/-- `iInfOfDirected p hp` is bounded above pointwise by every `p i`. -/
theorem iInfOfDirected_le {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (i : ι) (a : R) :
    iInfOfDirected p hp a ≤ p i a :=
  ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact apply_nonneg (p j) a⟩ i

/-- Any real lower bound on `p i a` for all `i` bounds `iInfOfDirected p hp a` from below. -/
theorem le_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) {a : R} {r : ℝ}
    (hr : ∀ i, r ≤ p i a) :
    r ≤ iInfOfDirected p hp a :=
  le_ciInf hr

/-- A function `q : R → ℝ` bounds `iInfOfDirected p hp` from below pointwise if and only if
it bounds every `p i` from below pointwise. -/
theorem le_iInfOfDirected_iff {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) {q : R → ℝ} :
    (∀ a, q a ≤ iInfOfDirected p hp a) ↔ ∀ i a, q a ≤ p i a :=
  ⟨fun h i a ↦ (h a).trans (iInfOfDirected_le p hp i a),
    fun h a ↦ le_iInfOfDirected p hp fun i ↦ h i a⟩

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R]

/-- The pointwise infimum of a nonempty downward-directed family of power-multiplicative ring
seminorms is power-multiplicative. -/
theorem isPowMul_iInfOfDirected {ι : Sort*} [Nonempty ι] (p : ι → RingSeminorm R)
    (hp : Directed (· ≥ ·) (fun i ↦ (p i : R → ℝ))) (hpm : ∀ i, IsPowMul (p i)) :
    IsPowMul (iInfOfDirected p hp) :=
  IsPowMul.iInf (fun i ↦ apply_nonneg (p i)) hpm

end Ring

end RingSeminorm
