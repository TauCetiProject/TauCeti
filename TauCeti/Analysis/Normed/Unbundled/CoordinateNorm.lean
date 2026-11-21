/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Comparisons with basis coordinate norms

For any algebra `E` over a normed field `K` equipped with a finite `K`-basis `b`, Mathlib's
`Module.Basis.norm` (`Mathlib.Analysis.Normed.Unbundled.FiniteExtension`) assigns to each element
`x : E` the maximum of the norms of its coordinates in the basis `b`.

This file records general comparison bounds between `b.norm`, arbitrary `K`-seminorms on `E`, and
boundedness of `K`-linear functionals (`Module.Dual K E`), without assuming that `K` is ultrametric
or complete, or that `E` is a field extension.

## Main results

* `Module.Basis.apply_le_sum_mul_norm`: any `K`-seminorm on `E` is bounded above by a constant
  times the basis coordinate norm `b.norm`.
* `Module.Basis.forall_exists_bound_iff`: every `K`-linear functional on `E` is bounded by a
  nonnegative function `f : E → ℝ` if and only if `b.norm` is bounded by a multiple of `f`.
* `Module.Basis.exists_norm_comparison_of_forall_exists_bound`: a `K`-seminorm bounding every
  `K`-linear functional on `E` is equivalent to `b.norm`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§2.3.1 and 3.5.1–3.5.2.
-/

public section

namespace Module.Basis

variable {K E ι F : Type*} [NormedField K] [Ring E] [Algebra K E] [Fintype ι] [Nonempty ι]

/-- Any `K`-seminorm on `E` is bounded above by a constant times the coordinate norm of any finite
`K`-basis of `E`. -/
theorem apply_le_sum_mul_norm [FunLike F E ℝ] [SeminormClass F K E]
    (b : Basis ι K E) (f : F) (x : E) :
    f x ≤ (∑ i, f (b i)) * b.norm x := by
  calc
    f x = f (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
    _ ≤ ∑ i, f (b.repr x i • b i) :=
      Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
    _ = ∑ i, ‖b.repr x i‖ * f (b i) := by simp only [map_smul_eq_mul]
    _ ≤ ∑ i, b.norm x * f (b i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (b.norm_repr_le_norm i)
        (apply_nonneg _ _)
    _ = (∑ i, f (b i)) * b.norm x := by rw [← Finset.mul_sum, mul_comm]

/-- Every `K`-linear functional on `E` is bounded by a nonnegative function `f : E → ℝ` if and only
if the coordinate norm of one (hence any) finite `K`-basis is bounded by `f`. -/
theorem forall_exists_bound_iff (b : Basis ι K E) {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (∀ φ : Module.Dual K E, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * f x) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x, b.norm x ≤ C * f x := by
  classical
  constructor
  · intro h
    choose C hC using fun i ↦ h (b.coord i)
    let D := 1 + ∑ i, |C i|
    have hD : 0 < D :=
      add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    refine ⟨D, hD, fun x ↦ ?_⟩
    apply Finset.sup'_le
    intro i _
    have hi : C i ≤ D := by
      have := Finset.single_le_sum (f := fun i ↦ |C i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      dsimp [D]
      linarith [le_abs_self (C i)]
    exact (hC i x).trans (mul_le_mul_of_nonneg_right hi (hf x))
  · rintro ⟨C, _, hC⟩ φ
    refine ⟨(∑ i, ‖φ (b i)‖) * C, fun x ↦ ?_⟩
    calc
      ‖φ x‖ = ‖∑ i, b.repr x i • φ (b i)‖ := by
        simpa only [map_sum, map_smul] using congrArg (fun y ↦ ‖φ y‖) (b.sum_repr x).symm
      _ ≤ ∑ i, ‖b.repr x i‖ * ‖φ (b i)‖ := by
        simpa only [smul_eq_mul, norm_mul] using
          norm_sum_le Finset.univ (fun i ↦ b.repr x i • φ (b i))
      _ ≤ ∑ i, (C * f x) * ‖φ (b i)‖ :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
          ((b.norm_repr_le_norm i).trans (hC x)) (norm_nonneg _)
      _ = ((∑ i, ‖φ (b i)‖) * C) * f x := by
        rw [← Finset.mul_sum]
        ring

/-- If every `K`-linear functional on `E` is bounded by a `K`-seminorm `f`, then `f` is equivalent
to the coordinate norm of any finite `K`-basis of `E`. -/
theorem exists_norm_comparison_of_forall_exists_bound [FunLike F E ℝ] [SeminormClass F K E]
    (b : Basis ι K E) (f : F)
    (hf : ∀ φ : Module.Dual K E, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * f x) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x, b.norm x ≤ C * f x ∧ f x ≤ D * b.norm x := by
  obtain ⟨C, hC, hb⟩ := (b.forall_exists_bound_iff (apply_nonneg f)).mp hf
  have : 0 ≤ ∑ i, f (b i) := Finset.sum_nonneg fun i _ ↦ apply_nonneg f (b i)
  refine ⟨C, 1 + ∑ i, f (b i), hC, by linarith, fun x ↦ ⟨hb x, ?_⟩⟩
  exact (b.apply_le_sum_mul_norm f x).trans
    (mul_le_mul_of_nonneg_right (by linarith) (b.norm_nonneg x))

end Module.Basis
