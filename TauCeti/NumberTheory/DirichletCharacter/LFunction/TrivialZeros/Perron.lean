/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Finset.Preimage
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.NegativeArgument
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros.Order

/-!
# Negative trivial zeros in the subtracted Dirichlet Perron formula

For `1 < a ≤ b`, the contribution of any finite selection of strictly negative zeros to
subtracted Perron inversion on `(a, b]` is bounded by `1 / (a - 1)`. The estimate is independent
of the conductor, parity, and left edge of the contour. In particular, the left edge of the
half-interval contour can move arbitrarily far to the left without an increasing residue cost.

The contour method is described in Koukoulopoulos, *The Distribution of Prime Numbers*,
Chapter 8, proof of Theorem 5.1.
-/

public section

open Complex

namespace DirichletCharacter

/-- The total absolute contribution of the strictly negative zeros in any finite set to the
subtracted Perron contour for `(a, b]` is at most `1 / (a - 1)`. At points where the L-function is
nonzero the analytic multiplicity is zero. -/
theorem sum_norm_trivialZeros_sub_cpow_div_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (S : Finset ℂ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∑ ρ ∈ S with ρ.re < 0,
        ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) *
          (((b : ℂ) ^ ρ - (a : ℂ) ^ ρ) / ρ)‖ ≤ 1 / (a - 1) := by
  classical
  let f : ℂ → ℝ := fun ρ ↦ ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) *
    (((b : ℂ) ^ ρ - (a : ℂ) ^ ρ) / ρ)‖
  let Z := S.filter fun ρ ↦ ρ.re < 0 ∧ χ.LFunction ρ = 0
  have hfilter : ∑ ρ ∈ S with ρ.re < 0, f ρ = ∑ ρ ∈ Z, f ρ := by
    symm
    refine Finset.sum_subset (fun ρ hρ ↦ ?_) fun ρ hρ hn ↦ ?_
    · simp only [Z, Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, hρ.2.1⟩
    · rcases Finset.mem_filter.mp hρ with ⟨hS, hre⟩
      have hz : χ.LFunction ρ ≠ 0 := fun h ↦ hn (Finset.mem_filter.mpr ⟨hS, hre, h⟩)
      have ho : analyticOrderNatAt χ.LFunction ρ = 0 :=
        not_ne_iff.mp (mt apply_eq_zero_of_analyticOrderNatAt_ne_zero hz)
      simp [f, ho]
  let e : ℕ → ℂ := fun j ↦ -((j + 1 : ℕ) : ℂ)
  have he : Function.Injective e := by
    intro i j h
    have hij : i + 1 = j + 1 := by exact_mod_cast neg_injective h
    omega
  let J := Z.preimage e he.injOn
  have hZ : J.image e = Z := by
    rw [Finset.image_preimage]
    refine Finset.filter_eq_self.mpr fun ρ hρ ↦ ?_
    obtain ⟨hre, hz⟩ := (Finset.mem_filter.mp hρ).2
    obtain ⟨j, hj, rfl⟩ := χ.exists_eq_neg_natCast_of_LFunction_eq_zero_of_re_neg hre hz
    exact ⟨j - 1, by simp only [e, Nat.sub_add_cancel (Nat.one_le_of_lt hj)]⟩
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hgeom := summable_geometric_of_lt_one (by positivity : 0 ≤ a⁻¹) (inv_lt_one_of_one_lt₀ ha)
  calc
    _ = ∑ j ∈ J, f (e j) := by rw [hfilter, ← hZ, Finset.sum_image he.injOn]
    _ ≤ ∑ j ∈ J, a⁻¹ ^ (j + 1) := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      obtain ⟨hre, hz⟩ := (Finset.mem_filter.mp (Finset.mem_preimage.mp hj)).2
      have horder := χ.meromorphicOrderAt_LFunction_of_re_neg hre
      rw [ite_eq_left hz] at horder
      have hm : analyticOrderNatAt χ.LFunction (e j) = 1 :=
        (χ.meromorphicOrderAt_LFunction_eq_natCast_iff one_ne_zero).mp (by simpa using horder)
      simpa only [f, hm, Nat.cast_one, one_mul, e] using
        TauCeti.norm_sub_cpow_div_neg_natCast_le ha0 hab (j + 1)
    _ ≤ ∑' j : ℕ, a⁻¹ ^ (j + 1) := by
      simpa only [pow_succ] using (hgeom.mul_right a⁻¹).sum_le_tsum J (fun j _ ↦ by positivity)
    _ = 1 / (a - 1) := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ ha)]
      field_simp

/-- The strictly negative zero terms of the subtracted Perron formula are absolutely summable
when both endpoints exceed `1`. Points where the L-function is nonzero have weight zero. -/
theorem summable_norm_trivialZeros_sub_cpow_div {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Summable (fun ρ : {s : ℂ // s.re < 0} ↦
      ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) *
        (((b : ℂ) ^ (ρ : ℂ) - (a : ℂ) ^ (ρ : ℂ)) / ρ)‖) := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [← neg_sub ((b : ℂ) ^ (_ : ℂ)), neg_div, mul_neg, norm_neg] using
      this hb ha (le_of_not_ge hab)
  refine summable_of_sum_le (c := 1 / (a - 1)) (fun _ ↦ norm_nonneg _) fun S ↦ ?_
  have hfilter : (S.map (Function.Embedding.subtype _)).filter (fun ρ ↦ ρ.re < 0) =
      S.map (Function.Embedding.subtype _) := by
    refine Finset.filter_eq_self.mpr fun z hz ↦ ?_
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp hz
    exact ρ.property
  simpa only [hfilter, Finset.sum_map, Function.Embedding.subtype_apply] using
    χ.sum_norm_trivialZeros_sub_cpow_div_le (S.map (Function.Embedding.subtype _)) ha hab

end DirichletCharacter
