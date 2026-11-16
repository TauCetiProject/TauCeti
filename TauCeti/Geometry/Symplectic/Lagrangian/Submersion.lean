/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Manifold.Submersion.Descent

/-!
# Lagrangian maps under submersive parametrization

Precomposing a smooth map with a surjective submersion leaves its tangent images unchanged.
Consequently the Lagrangian condition descends to a smooth quotient. When the quotient removes
exactly the kernel of the original map, the descended map is an immersion; a separate topological
embedding condition makes it an embedded Lagrangian. No dimension condition is imposed on an
empty embedded source.

This is the descent step for clean composition of Lagrangian correspondences: the matching
manifold may have positive dimensional excess fibres, even when its reduced image is embedded.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
-/

public section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [K.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M} {q : P → N}

/-- A surjective submersion preserves and reflects the Lagrangian tangent-image condition.
It suffices to know smoothness of the composite; smoothness of the descended map follows. -/
theorem isLagrangianMap_comp_submersion_iff (hq : IsSubmersion K J ∞ q)
    (hsurj : Surjective q) (hfq : ContMDiff K I ∞ (f ∘ q)) :
    hσ.IsLagrangianMap K (f ∘ q) ↔ hσ.IsLagrangianMap J f := by
  have hf := (hq.contMDiff_comp_iff hsurj le_rfl).mp hfq
  have hrange (x : P) : (mfderiv K I (f ∘ q) x).range =
      (mfderiv J I f (q x)).range := by
    rw [mfderiv_comp x (hf.mdifferentiable (by simp) _) (hq.contMDiff.mdifferentiable (by simp) _),
      ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hq.surjective_mfderiv (by simp) x))
  simp only [isLagrangianMap_iff_forall, hrange, Function.comp_apply]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hsurj y
    exact h x
  · exact fun h x ↦ h (q x)

variable {hσ} [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]

/-- A Lagrangian parametrization descends to a Lagrangian embedding when a surjective
submersion removes exactly its tangent kernel and the descended map is a topological embedding.
Neither smoothness nor the immersion property of the descended map is assumed. -/
theorem IsLagrangianMap.isLagrangianEmbedding_of_comp_submersion
    (h : hσ.IsLagrangianMap K (f ∘ q)) (hq : IsSubmersion K J ∞ q)
    (hsurj : Surjective q) (hfq : ContMDiff K I ∞ (f ∘ q))
    (hker : ∀ x, (mfderiv K I (f ∘ q) x).ker = (mfderiv K J q x).ker)
    (hemb : Topology.IsEmbedding f) : hσ.IsLagrangianEmbedding J f :=
  ⟨(hq.isImmersion_iff_ker_mfderiv_comp hsurj (by simp)).mpr ⟨hfq, hker⟩, hemb,
    (hσ.isLagrangianMap_comp_submersion_iff hq hsurj hfq).mp h⟩

/-- If the quotient of a Lagrangian parametrization removes exactly its tangent kernel,
the descended map is a Lagrangian immersion. Self-intersections are allowed. -/
theorem IsLagrangianMap.isLagrangianImmersion_of_comp_submersion [Nonempty N]
    (h : hσ.IsLagrangianMap K (f ∘ q)) (hq : IsSubmersion K J ∞ q)
    (hsurj : Surjective q) (hfq : ContMDiff K I ∞ (f ∘ q))
    (hker : ∀ x, (mfderiv K I (f ∘ q) x).ker = (mfderiv K J q x).ker) :
    hσ.IsLagrangianImmersion J f :=
  isLagrangianImmersion_iff.mpr
    ⟨(hq.isImmersion_iff_ker_mfderiv_comp hsurj (by simp)).mpr ⟨hfq, hker⟩,
      (hσ.isLagrangianMap_comp_submersion_iff hq hsurj hfq).mp h⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
