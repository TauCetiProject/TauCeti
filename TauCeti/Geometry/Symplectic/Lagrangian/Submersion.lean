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

Precomposing a map with a surjective submersion leaves its tangent images unchanged
(`Manifold.IsSubmersionAt.range_mfderiv_comp`), with no regularity assumed on the map.
Consequently the isotropic, coisotropic and Lagrangian conditions descend to, and lift from,
a quotient manifold. When the quotient removes the whole kernel of the original map, the
descended map is an immersion. It is then a Lagrangian immersion if the quotient is nonempty,
and a separate topological embedding condition makes it an embedded Lagrangian. No dimension
condition or nonemptiness is imposed on an embedded source.

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
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M} {q : P → N} {n : ℕ∞ω}

omit [IsManifold I ∞ M] in
/-- A pointwise condition on tangent images holds for `f ∘ q` exactly when it holds for `f`,
if `q` is a surjective submersion. -/
private theorem forall_range_mfderiv_comp_iff (hq : IsSubmersion K J n q) (hn : n ≠ 0)
    (hsurj : Surjective q) {Φ : ∀ y : M, Submodule ℝ (TangentSpace I y) → Prop} :
    (∀ x, Φ (f (q x)) (LinearMap.range (mfderiv K I (f ∘ q) x).toLinearMap)) ↔
      ∀ y, Φ (f y) (LinearMap.range (mfderiv J I f y).toLinearMap) := by
  simp only [(hq.isSubmersionAt _).range_mfderiv_comp hn]
  exact ⟨fun h y ↦ (hsurj y).elim fun x hx ↦ hx ▸ h x, fun h x ↦ h (q x)⟩

/-- A surjective submersion preserves and reflects the isotropic tangent-image condition. -/
theorem isIsotropicMap_comp_isSubmersion_iff (hq : IsSubmersion K J n q) (hn : n ≠ 0)
    (hsurj : Surjective q) : hσ.IsIsotropicMap K (f ∘ q) ↔ hσ.IsIsotropicMap J f := by
  rw [isIsotropicMap_iff_forall, isIsotropicMap_iff_forall]
  exact forall_range_mfderiv_comp_iff hq hn hsurj
    (Φ := fun y ↦ (hσ.symplecticFormAt y).IsIsotropic)

/-- A surjective submersion preserves and reflects the coisotropic tangent-image condition. -/
theorem isCoisotropicMap_comp_isSubmersion_iff (hq : IsSubmersion K J n q) (hn : n ≠ 0)
    (hsurj : Surjective q) : hσ.IsCoisotropicMap K (f ∘ q) ↔ hσ.IsCoisotropicMap J f := by
  rw [isCoisotropicMap_iff, isCoisotropicMap_iff]
  exact forall_range_mfderiv_comp_iff hq hn hsurj
    (Φ := fun y ↦ (hσ.symplecticFormAt y).IsCoisotropic)

/-- A surjective submersion preserves and reflects the Lagrangian tangent-image condition.
No regularity of `f` is assumed. -/
theorem isLagrangianMap_comp_isSubmersion_iff (hq : IsSubmersion K J n q) (hn : n ≠ 0)
    (hsurj : Surjective q) : hσ.IsLagrangianMap K (f ∘ q) ↔ hσ.IsLagrangianMap J f := by
  rw [isLagrangianMap_iff_forall, isLagrangianMap_iff_forall]
  exact forall_range_mfderiv_comp_iff hq hn hsurj
    (Φ := fun y ↦ (hσ.symplecticFormAt y).IsLagrangian)

variable {hσ} [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]

/-- A Lagrangian parametrization descends to a Lagrangian embedding when a surjective
submersion removes its whole tangent kernel and the descended map is a topological embedding.
Neither smoothness nor the immersion property of the descended map is assumed, and the source
may be empty. -/
theorem IsLagrangianMap.isLagrangianEmbedding_of_comp_isSubmersion
    (h : hσ.IsLagrangianMap K (f ∘ q)) (hq : IsSubmersion K J ∞ q)
    (hsurj : Surjective q) (hfq : ContMDiff K I ∞ (f ∘ q))
    (hker : ∀ x, (mfderiv K I (f ∘ q) x).ker ≤ (mfderiv K J q x).ker)
    (hemb : Topology.IsEmbedding f) : hσ.IsLagrangianEmbedding J f :=
  ⟨(hq.isImmersion_iff_ker_mfderiv_comp_le hsurj (by simp) le_rfl).mpr ⟨hfq, hker⟩, hemb,
    (hσ.isLagrangianMap_comp_isSubmersion_iff hq (by simp) hsurj).mp h⟩

/-- If the quotient of a Lagrangian parametrization removes its whole tangent kernel and is
nonempty, the descended map is a Lagrangian immersion. Self-intersections are allowed. -/
theorem IsLagrangianMap.isLagrangianImmersion_of_comp_isSubmersion [Nonempty N]
    (h : hσ.IsLagrangianMap K (f ∘ q)) (hq : IsSubmersion K J ∞ q)
    (hsurj : Surjective q) (hfq : ContMDiff K I ∞ (f ∘ q))
    (hker : ∀ x, (mfderiv K I (f ∘ q) x).ker ≤ (mfderiv K J q x).ker) :
    hσ.IsLagrangianImmersion J f :=
  isLagrangianImmersion_iff.mpr
    ⟨(hq.isImmersion_iff_ker_mfderiv_comp_le hsurj (by simp) le_rfl).mpr ⟨hfq, hker⟩,
      (hσ.isLagrangianMap_comp_isSubmersion_iff hq (by simp) hsurj).mp h⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
