/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Rescale

/-!
# Constant rescaling of smooth symplectic forms

Multiplication by a nonzero real constant preserves nondegeneracy and symplecticity of a smooth
two-form. Its tangent-space symplectic forms are the rescalings of the original tangent-space
forms. Consequently symplectic complements and all four linear subspace predicates are unchanged.
This comparison allows the linear rescaling API to apply directly to tangent images of immersed
or embedded submanifolds, including when the scale is negative.

Primitives scale by the same constant, with the convention `σ = -dθ`.

The conventions follow McDuff--Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- Nonzero constant rescaling preserves and reflects fiberwise nondegeneracy. -/
@[simp]
theorem isNondegenerate_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (c • σ).IsNondegenerate ↔ σ.IsNondegenerate := by
  simp only [isNondegenerate_iff_separatingLeft, SmoothForm.eval₂_smul, smul_eq_mul, mul_eq_zero,
    hc, false_or]

/-- A nonzero multiple of a nondegenerate smooth two-form is nondegenerate. -/
theorem IsNondegenerate.smul (hσ : σ.IsNondegenerate) (c : ℝ) (hc : c ≠ 0) :
    (c • σ).IsNondegenerate :=
  (isNondegenerate_smul_iff c hc).2 hσ

/-- Negation preserves and reflects fiberwise nondegeneracy. -/
@[simp]
theorem isNondegenerate_neg_iff : (-σ).IsNondegenerate ↔ σ.IsNondegenerate := by
  rw [← neg_one_smul ℝ σ]
  exact isNondegenerate_smul_iff (-1) (by norm_num)

/-- A nonzero multiple of a symplectic form is symplectic. -/
theorem IsSymplectic.smul (hσ : σ.IsSymplectic) (c : ℝ) (hc : c ≠ 0) :
    (c • σ).IsSymplectic :=
  ⟨hσ.isClosed.smul c, hσ.isNondegenerate.smul c hc⟩

/-- Nonzero constant rescaling preserves and reflects symplecticity. -/
@[simp]
theorem isSymplectic_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (c • σ).IsSymplectic ↔ σ.IsSymplectic := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul c hc⟩
  have hclosed := h.isClosed.smul c⁻¹
  rw [inv_smul_smul₀ hc] at hclosed
  exact ⟨hclosed, (isNondegenerate_smul_iff c hc).1 h.isNondegenerate⟩

/-- Negation preserves and reflects symplecticity. -/
@[simp]
theorem isSymplectic_neg_iff : (-σ).IsSymplectic ↔ σ.IsSymplectic := by
  rw [← neg_one_smul ℝ σ]
  exact isSymplectic_smul_iff (-1) (by norm_num)

/-- The tangent-space symplectic form of a constant multiple is the corresponding linear
rescaling. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_smul (hσ : σ.IsNondegenerate) (c : ℝ) (hc : c ≠ 0)
    (x : M) :
    (hσ.smul c hc).symplecticFormAt x = (hσ.symplecticFormAt x).rescale c hc := by
  apply SymplecticForm.toBilinForm_injective
  ext v w
  simp only [IsNondegenerate.symplecticFormAt_apply, SmoothForm.eval₂_smul,
    SymplecticForm.rescale_apply, smul_eq_mul]

/-- Constant rescaling preserves the convention relating a symplectic form and its chosen
primitive, including negative scale factors. -/
theorem smul_eq_neg_mextDerivₗ (θ : SmoothForm I M ℝ 1)
    (hθ : σ = -mextDerivₗ I 1 θ) (c : ℝ) :
    c • σ = -mextDerivₗ I 1 (c • θ) := by
  rw [hθ, map_smul, smul_neg]

end TauCeti.SmoothTwoForm
