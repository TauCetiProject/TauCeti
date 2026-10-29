/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.Sheaves.NoZeroDivisors
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic stalks are integral domains

On a complex curve, holomorphic sections over a connected open set have no zero divisors,
by the identity theorem. Every point has a basis of connected open neighborhoods, so the
same holds for the stalk of the holomorphic structure sheaf. Thus a holomorphic germ embeds
in its fraction field, providing the local algebra for meromorphic functions and divisor sheaves.

Neither the curve nor an arbitrary domain of sections is required to be connected: only the
sectionwise statement needs connectedness of its domain. Compactness is not needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6 and 16.
* The section argument uses `TauCeti.RiemannSurface.apply_eq_of_eventuallyConst`;
  the passage to stalks uses `TopCat.Presheaf.stalk_noZeroDivisors_of_hasBasis`.
-/

public noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Holomorphic sections on a preconnected open set have no zero divisors. -/
instance sectionsNoZeroDivisors (U : Opens X) [PreconnectedSpace U] :
    NoZeroDivisors ((holomorphicStructureSheaf 𝓘(ℂ) X).obj.obj (op U)) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    have hfg : ∀ y : U, f y * g y = 0 := fun y ↦ by
      simpa only [mul_apply, zero_apply] using congrArg (fun s ↦ s y) h
    obtain ⟨y, hy⟩ : ∃ y : U, f y ≠ 0 := by
      by_contra hn
      exact hf (ext fun y ↦ by simpa using not_exists.mp hn y)
    have hg : g =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [(contMDiff f).continuous.continuousAt.eventually_ne hy] with z hz
      exact (mul_eq_zero.mp (hfg z)).resolve_left hz
    apply ext
    intro z
    simpa only [zero_apply] using (RiemannSurface.apply_eq_of_eventuallyConst (mdifferentiable g)
      (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨0, hg⟩) z).trans hg.eq_of_nhds

/-- The stalk of holomorphic functions at any point of a complex curve is an integral domain. -/
instance stalkIsDomain (x : X) :
    IsDomain ((holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk x) := by
  let F := (holomorphicStructureSheaf 𝓘(ℂ) X).presheaf
  have : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hB : (𝓝 x).HasBasis
      (fun U : Opens X ↦ x ∈ U ∧ IsConnected (U : Set X)) (fun U ↦ (U : Set X)) :=
    (LocallyConnectedSpace.open_connected_basis x).to_hasBasis
      (fun C hC ↦ ⟨⟨C, hC.1⟩, hC.2, Subset.rfl⟩)
      (fun U hU ↦ ⟨U, ⟨U.isOpen, hU⟩, Subset.rfl⟩)
  have : NoZeroDivisors (F.stalk x) := F.stalk_noZeroDivisors_of_hasBasis x hB fun U hU ↦ by
    have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.2.isPreconnected
    infer_instance
  exact NoZeroDivisors.to_isDomain _

end TauCeti.holomorphicStructureSheaf
