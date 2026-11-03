/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Topology.Sheaves.NoZeroDivisors
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic stalks are integral domains

On a finite-dimensional complex manifold without boundary, holomorphic sections over a
preconnected open set have no zero divisors, by the analytic identity theorem in charts.
Every point has a basis of connected open neighborhoods, so the same holds for the stalk of
the holomorphic structure sheaf. Thus a holomorphic germ embeds in its fraction field,
providing the local algebra for meromorphic functions and local analytic equations.
The existing section and stalk comparisons transfer these properties to Mathlib's native
complex-smooth structure sheaf as well.

Neither the manifold nor an arbitrary domain of sections is required to be connected: only the
sectionwise statement needs preconnectedness of its domain. Compactness, separation and
second countability are not needed. Zero-dimensional models are included.

## References

* Lars Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6 and 16, for the curve case.
* The section argument uses `ContMDiff.eq_of_eventuallyEq`;
  the passage to stalks uses `TopCat.Presheaf.stalk_noZeroDivisors_of_hasBasis`.
-/

public noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- Holomorphic sections on a preconnected open set have no zero divisors. -/
instance sectionsNoZeroDivisors (U : Opens X) [PreconnectedSpace U] :
    NoZeroDivisors ((holomorphicStructureSheaf I X).obj.obj (op U)) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
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
    have hg0 : toFun I X (op U) g = (fun _ : U ↦ (0 : ℂ)) :=
      (contMDiff g).eq_of_eventuallyEq contMDiff_const hg
    exact ext fun z ↦ (congrFun hg0 z).trans (zero_apply z).symm

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is an integral domain. -/
instance stalkIsDomain (x : X) :
    IsDomain ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let F := (holomorphicStructureSheaf I X).presheaf
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace H X
  have hB : (𝓝 x).HasBasis
      (fun U : Opens X ↦ x ∈ U ∧ IsConnected (U : Set X)) (fun U ↦ (U : Set X)) :=
    (LocallyConnectedSpace.open_connected_basis x).to_hasBasis
      (fun C hC ↦ ⟨⟨C, hC.1⟩, hC.2, Subset.rfl⟩)
      (fun U hU ↦ ⟨U, ⟨U.isOpen, hU⟩, Subset.rfl⟩)
  have : NoZeroDivisors (F.stalk x) := F.stalk_noZeroDivisors_of_hasBasis x hB fun U hU ↦ by
    have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.2.isPreconnected
    infer_instance
  exact NoZeroDivisors.to_isDomain _

/-- Complex-smooth sections on a preconnected open set have no zero divisors. This is the
native smooth-sheaf version of `sectionsNoZeroDivisors`, over `ℂ`, not over `ℝ`. -/
instance smoothSectionsNoZeroDivisors (U : Opens X) [PreconnectedSpace U] :
    NoZeroDivisors ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :=
  (smoothSectionsEquiv I X U).symm.toMulEquiv.noZeroDivisors

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is an integral domain, via its comparison with holomorphic germs. -/
instance smoothStalkIsDomain (x : X) :
    IsDomain ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain

end TauCeti.holomorphicStructureSheaf
