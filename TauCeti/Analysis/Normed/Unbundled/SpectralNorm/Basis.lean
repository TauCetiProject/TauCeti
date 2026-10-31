/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable

/-!
# Coordinate norms and weak stability

For a finite extension of an ultrametric normed field, the spectral norm is bounded above by
a constant times the coordinate norm of any basis. The reverse bound holds exactly when every
linear functional is bounded for the spectral norm. Thus over a weakly stable field the
spectral norm and every finite-basis coordinate norm are equivalent.

These comparisons express weak cartesianness without imposing a topology on the extension or
assuming completeness of the base field. In particular they apply to incomplete perfect fields.
They do not assert that the spectral norm is multiplicative, or that every extension of the
absolute value is equivalent to it.

The coordinate norm is Mathlib's `Module.Basis.norm`, and the spectral norm is Mathlib's
`spectralNorm`. No additional norm or topology instance is installed.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§2.3.1 and 3.5.1–3.5.2.
-/

public section

namespace Module.Basis

variable {K L ι : Type*} [NormedField K] [IsUltrametricDist K]
  [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]

/-- The spectral norm is bounded above by a basis coordinate norm, without any completeness
or weak-stability hypothesis. -/
theorem spectralNorm_le_sum_mul_norm (b : Basis ι K L) (x : L) :
    spectralNorm K L x ≤ (∑ i, spectralNorm K L (b i)) * b.norm x := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  calc
    spectralNorm K L x = spectralAlgNorm K L (∑ i, b.repr x i • b i) := by
      rw [b.sum_repr, spectralAlgNorm_def]
    _ ≤ ∑ i, spectralAlgNorm K L (b.repr x i • b i) :=
      Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
    _ = ∑ i, ‖b.repr x i‖ * spectralNorm K L (b i) := by
      simp only [map_smul_eq_mul, spectralAlgNorm_def]
    _ ≤ ∑ i, b.norm x * spectralNorm K L (b i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (b.norm_repr_le_norm i)
        (spectralNorm_nonneg _)
    _ = (∑ i, spectralNorm K L (b i)) * b.norm x := by rw [← Finset.mul_sum, mul_comm]

omit [IsUltrametricDist K] in
/-- Every functional on a finite extension is spectrally bounded if and only if the
coordinate norm of one (hence any) basis is bounded by the spectral norm. -/
theorem forall_exists_bound_spectralNorm_iff (b : Basis ι K L) :
    (∀ φ : Module.Dual K L, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * spectralNorm K L x) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x, b.norm x ≤ C * spectralNorm K L x := by
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
    exact (hC i x).trans (mul_le_mul_of_nonneg_right hi (spectralNorm_nonneg x))
  · rintro ⟨C, _, hC⟩ φ
    refine ⟨(∑ i, ‖φ (b i)‖) * C, fun x ↦ ?_⟩
    calc
      ‖φ x‖ = ‖∑ i, b.repr x i • φ (b i)‖ := by
        simpa only [map_sum, map_smul] using congrArg (fun y ↦ ‖φ y‖) (b.sum_repr x).symm
      _ ≤ ∑ i, ‖b.repr x i‖ * ‖φ (b i)‖ := by
        simpa only [smul_eq_mul, norm_mul] using
          norm_sum_le Finset.univ (fun i ↦ b.repr x i • φ (b i))
      _ ≤ ∑ i, (C * spectralNorm K L x) * ‖φ (b i)‖ :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
          ((b.norm_repr_le_norm i).trans (hC x)) (norm_nonneg _)
      _ = ((∑ i, ‖φ (b i)‖) * C) * spectralNorm K L x := by
        rw [← Finset.mul_sum]
        ring

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
  obtain ⟨C, hC, hb⟩ := b.forall_exists_bound_spectralNorm_iff.mp ((isWeaklyStable_iff K).mp hK L)
  have hsum : 0 ≤ ∑ i, spectralNorm K L (b i) :=
    Finset.sum_nonneg fun i _ ↦ spectralNorm_nonneg (b i)
  refine ⟨C, 1 + ∑ i, spectralNorm K L (b i), hC, by positivity, fun x ↦ ⟨hb x, ?_⟩⟩
  exact (b.spectralNorm_le_sum_mul_norm x).trans
    (mul_le_mul_of_nonneg_right (by linarith) (b.norm_nonneg x))

end TauCeti.IsWeaklyStable
