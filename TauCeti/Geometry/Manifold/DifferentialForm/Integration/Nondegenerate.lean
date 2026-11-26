/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.MapCoeff
import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# Nondegeneracy of the integrated paired wedge

On an oriented manifold of positive dimension `m = k + l`, the integration pairing
`(α, β) ↦ ∫_M α ∧ β` of real forms is nondegenerate on compactly supported forms
(`TauCeti.SmoothForm.exists_integralTopForm_wedge_ne_zero`). This file extends the statement to
vector-valued forms paired by a nondegenerate continuous bilinear form
`μ : F →L[ℝ] G →L[ℝ] ℝ`: a nonzero compactly supported `F`-valued `k`-form `φ` has a `G`-valued
`l`-form `ψ` with `∫_M μ(φ ∧ ψ) ≠ 0`
(`TauCeti.SmoothForm.exists_integralTopForm_wedgeWith_ne_zero`).

This is the nondegeneracy statement behind integrated pairings of Lie-algebra-valued forms such as
the Atiyah–Bott form `∫_M B(a ∧ b)` on connections.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Paired wedges are nondegenerate**: for a nondegenerate real-valued pairing `μ`, a nonzero
compactly supported smooth `F`-valued `k`-form `φ` on an oriented manifold of positive dimension
`m = k + l` pairs nontrivially with some smooth `G`-valued form `ψ` of the complementary degree,
`∫_M μ(φ ∧ ψ) ≠ 0`. For `F = G = ℝ` and `μ` the product this is
`TauCeti.SmoothForm.exists_integralTopForm_wedge_ne_zero`. -/
theorem exists_integralTopForm_wedgeWith_ne_zero {m k l : ℕ} [NeZero m]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    {μ : F →L[ℝ] G →L[ℝ] ℝ} (hμ : ∀ u, (∀ z, μ u z = 0) → u = 0) {φ : SmoothForm I M F k}
    (hφ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ.val)) (hφ₀ : φ ≠ 0) :
    ∃ ψ : SmoothForm I M G l, integralTopForm o
      (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) hkl (wedgeWith μ φ ψ) :
        RoughForm I M ℝ m) ≠ 0 := by
  -- Some real component `μ(φ, z)` of `φ` is nonzero and pairs nontrivially with a real form
  -- `c`; then `ψ = c z` works, since `μ(φ ∧ c z) = μ(φ, z) ∧ c`.
  obtain ⟨z, hz⟩ := exists_mapCoeff_flip_ne_zero hμ hφ₀
  have hsupp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (mapCoeff (μ.flip z) φ).val ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ.val :=
    closure_mono fun x hx h0 ↦ hx <| by
      ext v
      rw [coe_mapCoeff, RoughForm.mapCoeff_apply, h0]
      exact map_zero (μ.flip z)
  obtain ⟨c, hc⟩ := exists_integralTopForm_wedge_ne_zero o hkl
    ((mem_compactlySupportedForms I).mpr <| hφ.of_isClosed_subset (isClosed_tsupport _) hsupp) hz
  exact ⟨mapCoeff ((ContinuousLinearMap.id ℝ ℝ).smulRight z) c, by
    rwa [wedgeWith_mapCoeff_smulRight]⟩

end SmoothForm

end TauCeti
