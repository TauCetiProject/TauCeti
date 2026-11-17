/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Alternating forms on orthonormal frames

The operator norm of an alternating map on a real inner product space
can be tested on orthonormal frames. For real-valued forms this identifies the native norm
with comass, the supremum of the absolute values on those frames; in positive degree, a one-sided
upper bound on orthonormal frames suffices
(`ContinuousAlternatingMap.opNorm_le_iff_apply_le_orthonormal`).
The formula includes degree zero. On a finite-dimensional space, degrees greater than the dimension
give an empty set, its real supremum is zero, and every alternating form vanishes.

The bound criterion works for maps into any real normed space. Restriction to the span of
an independent frame reduces it to the top-degree norm formula in an orthonormal basis;
dependent frames give zero. No additional norm on alternating forms is introduced.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, §II.3.
-/

public section

open Module Set

namespace ContinuousAlternatingMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- A nonnegative bound for an alternating map on all orthonormal frames is a bound for
its operator norm, even when the degree exceeds the dimension. -/
theorem opNorm_le_iff_le_orthonormal {ω : E [⋀^Fin k]→L[ℝ] F} {C : ℝ} (hC : 0 ≤ C) :
    ‖ω‖ ≤ C ↔ ∀ v : Fin k → E, Orthonormal ℝ v → ‖ω v‖ ≤ C := by
  classical
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ω.opNorm_le_bound hC fun v ↦ ?_⟩
  · have hnorm : ‖ω v‖ ≤ ‖ω‖ := by simpa [hv.norm_eq_one] using ω.le_opNorm v
    exact hnorm.trans h
  · by_cases hv : LinearIndependent ℝ v
    swap
    · have hzero : ω v = 0 := by
        simpa only [coe_toAlternatingMap] using ω.toAlternatingMap.map_linearDependent v hv
      rw [hzero, norm_zero]
      positivity
    let W := Submodule.span ℝ (range v)
    have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (finite_range v)
    let w : Fin k → W := fun i ↦ ⟨v i, Submodule.subset_span (mem_range_self i)⟩
    let b : OrthonormalBasis (Fin k) ℝ W := (stdOrthonormalBasis ℝ W).reindex
      (finCongr (by simpa using finrank_span_eq_card hv))
    let ψ := ω.compContinuousLinearMap W.subtypeL
    have hb : Orthonormal ℝ (fun i ↦ (b i : E)) :=
      b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hψ : ‖ψ‖ ≤ C := by
      rw [ψ.norm_eq_norm_apply_orthonormalBasis b]
      exact h _ hb
    simpa [ψ, w, Function.comp_def] using
      (ψ.le_opNorm w).trans (mul_le_mul_of_nonneg_right hψ (Finset.prod_nonneg fun i _ ↦
        norm_nonneg (w i)))

/-- The operator norm is the supremum of the norms of the values on orthonormal frames.
For a degree greater than the dimension the set is empty and both sides are zero. -/
theorem norm_eq_sSup_norm_orthonormal (ω : E [⋀^Fin k]→L[ℝ] F) :
    ‖ω‖ = sSup {r | ∃ v : Fin k → E, Orthonormal ℝ v ∧ r = ‖ω v‖} := by
  let S := {r | ∃ v : Fin k → E, Orthonormal ℝ v ∧ r = ‖ω v‖}
  have hbound (v : Fin k → E) (hv : Orthonormal ℝ v) : ‖ω v‖ ≤ ‖ω‖ :=
    (opNorm_le_iff_le_orthonormal (norm_nonneg ω)).1 le_rfl v hv
  have hbounded : BddAbove S := ⟨‖ω‖, by rintro _ ⟨v, hv, rfl⟩; exact hbound v hv⟩
  by_cases hS : S.Nonempty
  · have hnonneg : 0 ≤ sSup S := by
      obtain ⟨r, v, hv, rfl⟩ := hS
      exact (norm_nonneg _).trans (le_csSup hbounded ⟨v, hv, rfl⟩)
    exact le_antisymm
      ((opNorm_le_iff_le_orthonormal hnonneg).2 fun v hv ↦
        le_csSup hbounded ⟨v, hv, rfl⟩)
      (csSup_le hS (by rintro _ ⟨v, hv, rfl⟩; exact hbound v hv))
  · have hzero : ‖ω‖ = 0 := le_antisymm
      ((opNorm_le_iff_le_orthonormal (C := 0) le_rfl).2 fun v hv ↦
        False.elim (hS ⟨‖ω v‖, v, hv, rfl⟩)) (norm_nonneg ω)
    have hempty : {r | ∃ v : Fin k → E, Orthonormal ℝ v ∧ r = ‖ω v‖} = ∅ :=
      not_nonempty_iff_eq_empty.mp hS
    rw [hempty, Real.sSup_empty]
    exact hzero

/-- **Comass equals the native operator norm**: the norm of a real alternating form is
the supremum of its absolute values on orthonormal frames, in every degree. -/
theorem norm_eq_sSup_abs_orthonormal (ω : E [⋀^Fin k]→L[ℝ] ℝ) :
    ‖ω‖ = sSup {r | ∃ v : Fin k → E, Orthonormal ℝ v ∧ r = |ω v|} := by
  simpa only [Real.norm_eq_abs] using ω.norm_eq_sSup_norm_orthonormal

/-- In positive degree, a nonnegative comass bound `‖φ‖ ≤ C` on a real alternating `k`-form is
equivalent to the one-sided bound `φ v ≤ C` on all orthonormal frames `v`, since negating the
first vector of an orthonormal frame preserves orthonormality and negates `φ v`. -/
theorem opNorm_le_iff_apply_le_orthonormal {φ : E [⋀^Fin k]→L[ℝ] ℝ} (hk : 1 ≤ k) {C : ℝ}
    (hC : 0 ≤ C) : ‖φ‖ ≤ C ↔ ∀ v : Fin k → E, Orthonormal ℝ v → φ v ≤ C := by
  rw [φ.opNorm_le_iff_le_orthonormal hC]
  refine ⟨fun h v hv ↦ (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h v hv),
    fun h v hv ↦ (Real.norm_eq_abs _).trans_le (abs_le.2 ⟨?_, h v hv⟩)⟩
  let i₀ : Fin k := ⟨0, hk⟩
  have hneg : φ (Function.update v i₀ (-v i₀)) = -φ v := by
    simpa [neg_one_smul] using φ.map_update_smul v i₀ (-1 : ℝ) (v i₀)
  linarith [h _ (hv.update_neg i₀)]

end ContinuousAlternatingMap
