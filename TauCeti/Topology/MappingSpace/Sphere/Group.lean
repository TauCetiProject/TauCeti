/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.FreeLoop
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

For the circle this reads `G × ΩG ≃ₜ C(S¹, G)`: the free loop space of a topological group is the
product of the group and its based loop space at `1`
(`TauCeti.circleMapGroupHomeomorphLoopSpace`), through the identification of loops based at
`1 ∈ S¹` with paths (`TauCeti.basedMapCircleOneHomeomorphPath`).

## Main declarations

* `TauCeti.sphereGroupHomeomorphIteratedLoopSpace`: `G × Ω^[k] G ≃ₜ Map(S^k, G)` for `k ≥ 1`,
  sending `(g, γ)` to the product of the constant sphere `g` and the based sphere map of `γ`, with
  the characteristic lemmas `_apply`, `_symm_fst` and `_symm_snd`.
* `TauCeti.circleMapGroupHomeomorphLoopSpace`: `G × ΩG ≃ₜ C(S¹, G)`, sending `(g, γ)` to the loop
  `t ↦ g γ(t)`, with the characteristic lemmas `_apply`, `_symm_fst` and `_symm_snd_apply`.

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

/-- The decomposition sends `(g, γ)` to the product of the constant sphere map `g` and the based
sphere map of the loop `γ`. -/
@[simp]
theorem sphereGroupHomeomorphIteratedLoopSpace_apply (g : G)
    (γ : (BasedTopologicalSpace.iteratedLoopSpace ⟨G, 1⟩ k).carrier) :
    sphereGroupHomeomorphIteratedLoopSpace k G s₀ (g, γ) =
      ContinuousMap.const _ g *
        ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace k ⟨G, 1⟩
          s₀).symm γ).val := by
  rw [sphereGroupHomeomorphIteratedLoopSpace, Homeomorph.trans_apply,
    mappingSpaceGroupHomeomorph_apply]
  -- both sides are the constant map times the based sphere map of `γ`
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
  -- the loop coordinate is the second component of the inverse of the product decomposition
  rfl

section FreeLoop

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **The free loop space of a topological group is a product**, `G × ΩG ≃ₜ C(S¹, G)`: the pair
`(g, γ)` of a group element and a loop at `1` goes to the free loop `t ↦ g γ(t)`, read on the
circle through `TauCeti.basedMapCircleOneHomeomorphPath`. The inverse records the value at `1 ∈ S¹`
and translates the loop back to `1`. -/
def circleMapGroupHomeomorphLoopSpace : G × Path (1 : G) 1 ≃ₜ C(Circle, G) :=
  (Homeomorph.prodCongr (Homeomorph.refl G) (basedMapCircleOneHomeomorphPath (1 : G)).symm).trans
    (mappingSpaceGroupHomeomorph 1)

variable {G}

/-- The free loop of `(g, γ)` at the image `unitToCircle t` of a time `t` is `g γ(t)`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_apply_unitToCircle (g : G) (γ : Path (1 : G) 1)
    (t : unitInterval) :
    circleMapGroupHomeomorphLoopSpace G (g, γ) (unitToCircle t) = g * γ t := by
  simp [circleMapGroupHomeomorphLoopSpace]

/-- The group coordinate of a free loop in `G` is its value at `1 ∈ S¹`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_symm_fst (f : C(Circle, G)) :
    ((circleMapGroupHomeomorphLoopSpace G).symm f).1 = f 1 :=
  mappingSpaceGroupHomeomorph_symm_fst 1 f

/-- The loop coordinate of a free loop `f` in `G` is the loop `t ↦ f(1)⁻¹ f(t)` at `1`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_symm_snd_apply (f : C(Circle, G)) (t : unitInterval) :
    ((circleMapGroupHomeomorphLoopSpace G).symm f).2 t = (f 1)⁻¹ * f (unitToCircle t) := by
  simp [circleMapGroupHomeomorphLoopSpace]

end FreeLoop

end TauCeti
