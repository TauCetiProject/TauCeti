/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Sphere
public import TauCeti.Topology.Homotopy.Extension.Collapse
import TauCeti.Topology.Homotopy.Extension.Cube

/-!
# A point of a sphere is a closed cofibration

Every point `s₀` of the unit sphere `Sᵏ ⊆ ℝᵏ⁺¹` has the homotopy extension property in the sphere
(`TauCeti.hasHomotopyExtensionProperty_singleton_sphere`). For `k ≥ 1` the sphere is the cube `Iᵏ`
with its boundary collapsed to `s₀` (`TauCeti.sphereCollapse`), and the boundary of the cube has
the homotopy extension property (`TauCeti.hasHomotopyExtensionProperty_cubeBoundary`), which passes
to the collapsed point (`TauCeti.HasHomotopyExtensionProperty.image_of_isQuotientMap`). For `k = 0`
the sphere is a zero-dimensional manifold, hence discrete, so every point is open and closed.

Restriction to a closed cofibration is a Hurewicz fibration of mapping spaces, so this makes
evaluation `Map(Sᵏ, X) → X` at the basepoint a Hurewicz fibration, with fibre the based mapping
space `Map_*(Sᵏ, X)`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.
-/

public section

open Metric Set Topology

namespace TauCeti

/-- **A point of a sphere has the homotopy extension property.** Every point `s₀` of the unit
sphere `Sᵏ` in `ℝᵏ⁺¹` has the homotopy extension property in the sphere, so the inclusion of the
basepoint is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_singleton_sphere (k : ℕ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    HasHomotopyExtensionProperty ({s₀} : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- The sphere `S⁰` is a manifold modelled on the point `ℝ⁰`, hence discrete.
    have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
      (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    exact (isClopen_discrete _).hasHomotopyExtensionProperty
  · have : NeZero k := ⟨hk.ne'⟩
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    -- The collapse of the cube boundary onto `s₀` is a quotient map, compact onto Hausdorff.
    have hq : IsQuotientMap (sphereCollapse k s₀) :=
      (sphereCollapse k s₀).continuous.isClosedMap.isQuotientMap
        (sphereCollapse k s₀).continuous (sphereCollapse_surjective k s₀)
    convert hasHomotopyExtensionProperty_cubeBoundary.image_of_isQuotientMap Cube.isClosed_boundary
      hq fun z z' h ↦ eq_or_mem_boundary_of_sphereCollapse_eq k s₀ h using 1
    -- The image of the nonempty cube boundary is the basepoint.
    refine (Set.Subset.antisymm ?_ ?_).symm
    · rintro _ ⟨z, hz, rfl⟩
      exact (sphereCollapse_eq_basepoint_iff k s₀ z).2 hz
    · intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      obtain ⟨z, hz⟩ : (Cube.boundary (Fin k)).Nonempty :=
        ⟨fun _ ↦ 0, ⟨0, hk⟩, Or.inl rfl⟩
      exact ⟨z, hz, (sphereCollapse_eq_basepoint_iff k s₀ z).2 hz⟩

end TauCeti
