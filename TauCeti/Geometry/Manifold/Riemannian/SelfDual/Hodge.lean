/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic

/-!
# The Hodge Laplacian on self-dual forms

The Hodge Laplacian preserves self-dual middle-degree forms. On these forms it is twice
the self-dual part of `d d*`. For a closed middle-degree form, applying `d*` to its self-dual
part gives half its codifferential. These identities give the Hodge factorization of the
normalized operator `(-d*, √2 d⁺)` on four-manifolds.

The conventions for `d*` and the Hodge Laplacian are those of
`TauCeti.Geometry.Manifold.Riemannian.Codifferential`, following Warner,
*Foundations of Differentiable Manifolds and Lie Groups*, §6.1–6.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hodge Laplacian preserves self-dual middle-degree forms. -/
theorem hodgeLaplacian_mem_selfDualForms {k : ℕ}
    (o : Manifold.Orientation I M (Fin (k + k))) {α : SmoothForm I M ℝ k}
    (hα : α ∈ selfDualForms o) : hodgeLaplacian o rfl α ∈ selfDualForms o := by
  rw [mem_selfDualForms, hodgeStar_hodgeLaplacian, mem_selfDualForms.mp hα]

/-- The Hodge Laplacian restricted to smooth self-dual middle-degree forms. -/
def selfDualHodgeLaplacian {k : ℕ} (o : Manifold.Orientation I M (Fin (k + k))) :
    selfDualForms o →ₗ[ℝ] selfDualForms o :=
  (hodgeLaplacian o rfl).restrict (fun _ hα ↦ hodgeLaplacian_mem_selfDualForms o hα)

/-- Restriction to self-dual forms does not change the underlying Hodge Laplacian. -/
@[simp]
theorem coe_selfDualHodgeLaplacian_apply {k : ℕ}
    (o : Manifold.Orientation I M (Fin (k + k))) (α : selfDualForms (I := I) (M := M) o) :
    (selfDualHodgeLaplacian o α : SmoothForm I M ℝ k) = hodgeLaplacian o rfl α :=
  (rfl)

/-- On a closed middle-degree form, `d*` of its self-dual part is half its codifferential.
Here closed means `dα = 0`; no compactness assumption on the manifold is needed. -/
theorem codifferential_selfDualPart_of_mextDeriv_eq_zero {k : ℕ}
    (o : Manifold.Orientation I M (Fin ((k + 1) + (k + 1))))
    {α : SmoothForm I M ℝ (k + 1)} (hα : mextDerivₗ I (k + 1) α = 0) :
    codifferential o rfl (selfDualPart o α) = (2⁻¹ : ℝ) • codifferential o rfl α := by
  have hstar : codifferential o rfl (hodgeStar o rfl α) = 0 := by
    rw [codifferential_apply o rfl (by omega), hodgeStar_hodgeStar, map_smul, hα,
      smul_zero, map_zero, smul_zero]
  simp [selfDualPart_apply, hstar]

/-- On a self-dual form of positive middle degree, the self-dual part of `d d*` is
half the Hodge Laplacian. -/
theorem selfDualPart_mextDeriv_codifferential {k : ℕ}
    (o : Manifold.Orientation I M (Fin ((k + 1) + (k + 1))))
    {α : SmoothForm I M ℝ (k + 1)} (hα : α ∈ selfDualForms o) :
    selfDualPart o (mextDerivₗ I k (codifferential o rfl α)) =
      (2⁻¹ : ℝ) • hodgeLaplacian o rfl α := by
  have hstar : hodgeStar o rfl (mextDerivₗ I k (codifferential o rfl α)) =
      codifferential o (show k + 1 + 1 + k = (k + 1) + (k + 1) by omega)
        (mextDerivₗ I (k + 1) α) := by
    rw [hodgeStar_mextDeriv o (by omega) (by omega) rfl,
      hodgeStar_codifferential o rfl (by omega), mem_selfDualForms.mp hα,
      map_smul, smul_smul, ← mul_pow]
    norm_num
  rw [selfDualPart_apply, hstar, hodgeLaplacian_add_one_add_one o rfl (by omega)]
  module

end TauCeti.SmoothForm
