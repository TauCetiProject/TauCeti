/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Maps from a sphere into a topological group

Evaluation at the basepoint `Map(S^k, G) → G` has the constant spheres `ContinuousMap.const` as a
section, and its fibre over the identity is the based mapping space `Map_*(S^k, G)`. For a
topological group `G` the fibration is trivial, `G × Map_*(S^k, G) ≃ₜ Map(S^k, G)`
(`TauCeti.mappingSpaceGroupHomeomorph`), and by the identification of based maps out of the sphere
with the iterated loop space, `G × Ω^[k] G ≃ₜ Map(S^k, G)`, in particular
`G × Ω²G ≃ₜ Map(S², G)`.

## Main declarations

* `TauCeti.sphereGroupHomeomorphIteratedLoopSpace`: `G × Ω^[k] G ≃ₜ Map(S^k, G)` for `k ≥ 1`,
  sending `(g, γ)` to the product of the constant sphere `g` and the based sphere map of `γ`, with
  the characteristic lemmas `_apply`, `_symm_fst` and `_symm_snd`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

open Metric

namespace TauCeti

variable (k : ℕ) [NeZero k] (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-- **`G × Ω^[k] G ≃ₜ Map(S^k, G)` for a topological group `G` and `k ≥ 1`**, through the
identification of based maps out of `S^k`, based at `s₀`, with the `k`-fold loop space. -/
def sphereGroupHomeomorphIteratedLoopSpace :
    G × (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ k).carrier ≃ₜ
      C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, G) :=
  (Homeomorph.prodCongr (Homeomorph.refl G)
    (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace k ⟨G, 1⟩ s₀).symm).trans
      (mappingSpaceGroupHomeomorph s₀)

variable {k G s₀}

@[simp]
theorem sphereGroupHomeomorphIteratedLoopSpace_apply (g : G)
    (γ : (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ k).carrier) :
    sphereGroupHomeomorphIteratedLoopSpace k G s₀ (g, γ) =
      ContinuousMap.const _ g *
        ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace k ⟨G, 1⟩
          s₀).symm γ).1 := by
  rw [sphereGroupHomeomorphIteratedLoopSpace, Homeomorph.trans_apply,
    mappingSpaceGroupHomeomorph_apply]
  rfl

/-- The group coordinate of the decomposition of a sphere map is its value at the basepoint. -/
@[simp]
theorem sphereGroupHomeomorphIteratedLoopSpace_symm_fst
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, G)) :
    ((sphereGroupHomeomorphIteratedLoopSpace k G s₀).symm f).1 = f s₀ := by
  rw [sphereGroupHomeomorphIteratedLoopSpace, Homeomorph.symm_trans_apply]
  exact mappingSpaceGroupHomeomorph_symm_fst s₀ f

/-- The loop coordinate of the decomposition of a sphere map `f` is the loop corresponding to the
based sphere map `(f s₀)⁻¹ * f`. -/
@[simp]
theorem sphereGroupHomeomorphIteratedLoopSpace_symm_snd
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, G)) :
    ((sphereGroupHomeomorphIteratedLoopSpace k G s₀).symm f).2 =
      BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace k ⟨G, 1⟩ s₀
        ((mappingSpaceGroupHomeomorph s₀).symm f).2 := by
  rw [sphereGroupHomeomorphIteratedLoopSpace, Homeomorph.symm_trans_apply]
  rfl

end TauCeti
