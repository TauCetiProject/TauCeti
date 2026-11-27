/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.HodgeStar
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# Codifferential on open submanifolds

The codifferential commutes with restriction to an open submanifold in degrees one through
the dimension. Thus a coclosed form remains coclosed after restriction.
-/

public section

noncomputable section

open Bundle Manifold TopologicalSpace
open scoped ContDiff Manifold TauCeti

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The codifferential commutes with restriction to an open submanifold. -/
theorem codifferential_mpullback_subtypeVal {m k l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (U : Opens M) (a : SmoothForm I M ℝ (k + 1)) :
    codifferential (o.restrict U) hkl (mpullback (Subtype.val : U → M) contMDiff_subtypeVal a) =
      mpullback (Subtype.val : U → M) contMDiff_subtypeVal (codifferential o hkl a) := by
  have hlk : l + 1 + k = m := by omega
  rw [codifferential_apply (o.restrict U) hkl hlk, codifferential_apply o hkl hlk,
    hodgeStar_mpullback_subtypeVal, mextDerivₗ_mpullback, hodgeStar_mpullback_subtypeVal, map_smul]

end TauCeti.SmoothForm
