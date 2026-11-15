/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable

/-!
# Coordinate norms and weak stability

For any `K`-algebra `E` with a finite `K`-basis `b`, every `K`-seminorm `f` on `E` is bounded above
by a constant times the coordinate norm `b.norm`, and a reverse bound holds if and only if every
`K`-linear functional on `E` is bounded by `f`. Specializing to a finite extension of an ultrametric
normed field, over a weakly stable field the spectral norm and every finite-basis coordinate norm
are equivalent.

These comparisons express weak cartesianness without imposing a topology on the extension or
assuming completeness of the base field. In particular they apply to incomplete perfect fields.
They do not assert that the spectral norm is multiplicative, or that every extension of the
absolute value is equivalent to it.

The coordinate norm is Mathlib's `Module.Basis.norm`, and the spectral norm is Mathlib's
`spectralNorm`. No additional norm or topology instance is installed.

## Main results

* `Module.Basis.apply_le_sum_mul_norm`: any `K`-seminorm on `E` is bounded above by a basis
  coordinate norm.
* `Module.Basis.forall_exists_bound_iff`: every `K`-linear functional on `E` is bounded by a
  nonnegative function `f` if and only if `b.norm` is bounded by a multiple of `f`.
* `Module.Basis.exists_norm_comparison_of_forall_exists_bound`: a `K`-seminorm bounding every
  `K`-linear functional is equivalent to `b.norm`.
* `Module.Basis.spectralNorm_le_sum_mul_norm`, `Module.Basis.forall_exists_bound_spectralNorm_iff`,
  and `TauCeti.IsWeaklyStable.exists_basis_norm_comparison`: specializations to `spectralNorm` on
  finite field extensions.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§2.3.1 and 3.5.1–3.5.2.
-/

public section

namespace Module.Basis

section Seminorm

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
    have hD : 0 < D := by positivity
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
  refine ⟨C, 1 + ∑ i, f (b i), hC, by positivity, fun x ↦ ⟨hb x, ?_⟩⟩
  exact (b.apply_le_sum_mul_norm f x).trans
    (mul_le_mul_of_nonneg_right (by linarith) (b.norm_nonneg x))

end Seminorm

variable {K L ι : Type*} [NormedField K] [IsUltrametricDist K]
  [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]

/-- The spectral norm is bounded above by a basis coordinate norm, without any completeness
or weak-stability hypothesis. -/
theorem spectralNorm_le_sum_mul_norm (b : Basis ι K L) (x : L) :
    spectralNorm K L x ≤ (∑ i, spectralNorm K L (b i)) * b.norm x := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  simpa only [spectralAlgNorm_def] using b.apply_le_sum_mul_norm (spectralAlgNorm K L) x

omit [IsUltrametricDist K] in
/-- Every functional on a finite extension is spectrally bounded if and only if the
coordinate norm of one (hence any) basis is bounded by the spectral norm. -/
theorem forall_exists_bound_spectralNorm_iff (b : Basis ι K L) :
    (∀ φ : Module.Dual K L, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * spectralNorm K L x) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x, b.norm x ≤ C * spectralNorm K L x :=
  b.forall_exists_bound_iff spectralNorm_nonneg

end Module.Basis

namespace TauCeti.IsWeaklyStable

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- On every finite extension of a weakly stable field, the spectral norm is equivalent to
the coordinate norm of any finite basis. The two comparison constants may differ. -/
theorem exists_basis_norm_comparison (hK : IsWeaklyStable K)
    {L : Type u} [Field L] [Algebra K L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x,
      b.norm x ≤ C * spectralNorm K L x ∧ spectralNorm K L x ≤ D * b.norm x := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  simpa only [spectralAlgNorm_def] using
    b.exists_norm_comparison_of_forall_exists_bound (spectralAlgNorm K L)
      ((isWeaklyStable_iff K).mp hK L)

end TauCeti.IsWeaklyStable
