/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# The standard symplectic form on complex coordinate space

On `ι → ℂ`, with coordinates `z_j = s_j + i t_j`, the standard symplectic form is
`ω₀ = Σ_j ds_j ∧ dt_j`, the sum of the standard area forms of the coordinate lines. It is
compatible with multiplication by `i`, with `ω₀(v, i v) = Σ_j |v_j|²`, and the real locus
`ι → ℝ` is a Lagrangian subspace.

## Main declarations

* `TauCeti.stdComplexPiSymplecticForm`: the form `ω₀(v, w) = Σ_j (Re v_j Im w_j - Im v_j Re w_j)`.
* `TauCeti.stdComplexPiSymplecticForm_compatible`: `ω₀` is compatible with multiplication by
  `i`; in particular it is invariant under and tames multiplication by `i`.
* `TauCeti.isLagrangian_stdComplexPiSymplecticForm_range_ofReal`: the real locus is Lagrangian.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1.
-/

public section

namespace TauCeti

open Complex Module

variable (ι : Type*) [Fintype ι]

/-- The bilinear form `Σ_j ω_ℂ(v_j, w_j)` on `ι → ℂ`, summing the coordinate area forms. -/
private noncomputable def stdComplexPiBilin : LinearMap.BilinForm ℝ (ι → ℂ) :=
  ∑ j, stdComplexSymplecticForm.toBilinForm.compl₁₂ (LinearMap.proj j) (LinearMap.proj j)

private lemma stdComplexPiBilin_apply (v w : ι → ℂ) :
    stdComplexPiBilin ι v w = ∑ j, stdComplexSymplecticForm (v j) (w j) := by
  simp [stdComplexPiBilin, LinearMap.sum_apply]

private lemma stdComplexPiBilin_apply_ofComplexModule (v : ι → ℂ) :
    stdComplexPiBilin ι v (AlmostComplexStructure.ofComplexModule (ι → ℂ) v) =
      ∑ j, Complex.normSq (v j) := by
  rw [stdComplexPiBilin_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← stdComplexSymplecticForm_apply_ofComplexModule]
  simp [AlmostComplexStructure.ofComplexModule_apply]

private lemma stdComplexPiBilin_pos {v : ι → ℂ} (hv : v ≠ 0) :
    0 < stdComplexPiBilin ι v (AlmostComplexStructure.ofComplexModule (ι → ℂ) v) := by
  rw [stdComplexPiBilin_apply_ofComplexModule]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun i _ ↦ Complex.normSq_nonneg (v i))
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.2 hj⟩

/-- The standard symplectic form `Σ_j ds_j ∧ dt_j` on complex coordinate space `ι → ℂ`, where
`z_j = s_j + i t_j`. -/
noncomputable def stdComplexPiSymplecticForm : SymplecticForm (ι → ℂ) where
  toBilinForm := stdComplexPiBilin ι
  isAlt v := by simp [stdComplexPiBilin_apply]
  nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (LinearMap.IsAlt.isRefl (B := stdComplexPiBilin ι) fun v ↦ by
        simp [stdComplexPiBilin_apply])).2 fun v hv ↦ ?_
    by_contra h
    exact (stdComplexPiBilin_pos ι h).ne' (hv _)

variable {ι}

/-- The standard symplectic form on `ι → ℂ` is the sum of the coordinate area forms. -/
@[simp]
theorem stdComplexPiSymplecticForm_apply (v w : ι → ℂ) :
    stdComplexPiSymplecticForm ι v w = ∑ j, stdComplexSymplecticForm (v j) (w j) :=
  stdComplexPiBilin_apply ι v w

/-- Pairing with multiplication by `i` gives the squared Euclidean norm. -/
theorem stdComplexPiSymplecticForm_apply_ofComplexModule (v : ι → ℂ) :
    stdComplexPiSymplecticForm ι v (AlmostComplexStructure.ofComplexModule (ι → ℂ) v) =
      ∑ j, Complex.normSq (v j) :=
  stdComplexPiBilin_apply_ofComplexModule ι v

/-- The standard symplectic form on `ι → ℂ` is invariant under multiplication by `i`. -/
theorem stdComplexPiSymplecticForm_invariant :
    (stdComplexPiSymplecticForm ι).Invariant (AlmostComplexStructure.ofComplexModule (ι → ℂ)) := by
  refine (SymplecticForm.invariant_iff _ _).2 fun v w ↦ ?_
  simp only [stdComplexPiSymplecticForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa [AlmostComplexStructure.ofComplexModule_apply] using
    (SymplecticForm.invariant_iff _ _).1 stdComplexSymplecticForm_invariant (v j) (w j)

/-- The standard symplectic form on `ι → ℂ` is compatible with multiplication by `i`. -/
theorem stdComplexPiSymplecticForm_compatible :
    (stdComplexPiSymplecticForm ι).Compatible (AlmostComplexStructure.ofComplexModule (ι → ℂ)) :=
  .of_tames stdComplexPiSymplecticForm_invariant fun _ hv ↦ stdComplexPiBilin_pos ι hv

/-- The standard symplectic form on `ι → ℂ` tames multiplication by `i`. -/
theorem stdComplexPiSymplecticForm_tames :
    (stdComplexPiSymplecticForm ι).Tames (AlmostComplexStructure.ofComplexModule (ι → ℂ)) :=
  stdComplexPiSymplecticForm_compatible.tames

/-- The real locus `ι → ℝ` is a Lagrangian subspace of `ι → ℂ` for the standard symplectic
form. -/
theorem isLagrangian_stdComplexPiSymplecticForm_range_ofReal :
    (stdComplexPiSymplecticForm ι).IsLagrangian
      (LinearMap.range (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM).toLinearMap) := by
  let L : (ι → ℝ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hinj : Function.Injective L := Function.Injective.piMap fun _ ↦ Complex.ofReal_injective
  have hi : (stdComplexPiSymplecticForm ι).IsIsotropic (LinearMap.range L.toLinearMap) := by
    rw [SymplecticForm.isIsotropic_iff]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp [L]
  refine hi.isLagrangian_of_finrank ?_
  rw [LinearMap.finrank_range_of_inj hinj]
  simp [Module.finrank_pi_fintype, Nat.mul_comm]

end TauCeti
