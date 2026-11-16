/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Changing the model space of a charted space with a structure groupoid

Let `Φ : H ≃ₜ H'` be a homeomorphism between two model spaces. A charted space `M` over `H`
becomes a charted space over `H'` for the composite charts `ChartedSpace.comp H' H M`, where `H`
carries the single chart `Φ`. If conjugating by `Φ` carries a structure groupoid `G` on `H` into a
structure groupoid `G'` on `H'`, then a `G`-manifold is a `G'`-manifold for the composite charts
(`Homeomorph.hasGroupoid_chartedSpaceComp`). This is the common step of
`Diffeomorph.isManifold_chartedSpaceComp` and `Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`.
-/

public section

open scoped Manifold

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']

namespace Homeomorph

/-- If conjugating by a homeomorphism of models `Φ : H ≃ₜ H'` carries the structure groupoid `G`
into `G'`, a charted space with structure groupoid `G` has structure groupoid `G'` for the
composite charts `ChartedSpace.comp H' H M`, when `H` carries the single chart `Φ`. -/
theorem hasGroupoid_chartedSpaceComp (Φ : H ≃ₜ H') {G : StructureGroupoid H}
    {G' : StructureGroupoid H'}
    (hG : ∀ e ∈ G, Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph) ∈ G')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    HasGroupoid M G' := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, φ, hφ, rfl⟩ ⟨c', hc', φ', hφ', rfl⟩
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ hφ
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ' hφ'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact hG _ (HasGroupoid.compatible hc hc')

end Homeomorph
