/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.PathClass
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer

/-!
# Final diffeomorphisms of path classes through a form stabilizer

Let `σ` be a smooth differential form on a manifold `M` and let
`G_σ = TauCeti.SmoothForm.diffeomorphStabilizer σ` be the group of diffeomorphisms preserving it.
The final diffeomorphisms of the path classes through `G_σ` (`TauCeti.Diffeotopy.PathClass G_σ`)
are exactly the isotopy stabilizer of `σ` (`TauCeti.SmoothForm.isotopyStabilizer σ`): the final
diffeomorphisms of the diffeotopies preserving `σ` at every time.

## Main results

* `TauCeti.range_pathClass_final`: the final diffeomorphisms of the path classes through `G_σ`
  form the isotopy stabilizer of `σ`.
* `TauCeti.Diffeotopy.PathClass.final_mem_isotopyStabilizer`: the final diffeomorphism of a path
  class through `G_σ` lies in the isotopy stabilizer of `σ`.
-/

public section

open scoped ContDiff

namespace TauCeti

open SmoothForm Diffeotopy

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm J M F k}

/-- **The final diffeomorphisms of the path classes** through the stabilizer of `σ` form the
isotopy stabilizer of `σ`: the final diffeomorphisms of the diffeotopies preserving `σ` at every
time. -/
theorem range_pathClass_final :
    (PathClass.final (diffeomorphStabilizer σ) le_rfl).range = isotopyStabilizer σ := by
  rw [PathClass.range_final]
  ext φ
  simp only [Subgroup.mem_map, mem_sliceSubgroup, finalHom_apply, mem_isotopyStabilizer]

/-- The final diffeomorphism of a path class through the stabilizer of `σ` lies in the isotopy
stabilizer of `σ`. -/
theorem Diffeotopy.PathClass.final_mem_isotopyStabilizer
    (γ : PathClass (diffeomorphStabilizer σ) le_rfl) :
    PathClass.final _ _ γ ∈ isotopyStabilizer σ :=
  (range_pathClass_final (σ := σ)) ▸ MonoidHom.mem_range.2 ⟨γ, rfl⟩

end TauCeti
