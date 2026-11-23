/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath

/-!
# Global primitives of `1`-forms on simply connected manifolds

On a simply connected `C¹` manifold every `1`-form `φ` with local primitives has a global
primitive (`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`), given from a basepoint by
continuous path integration
(`TauCeti.exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_of_simplyConnectedSpace`), and the
same holds on any simply connected open subset (`TauCeti.exists_isPrimitiveOn_of_isSimplyConnected`)
and any open subset whose connected components are simply connected
(`TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn`).

The proof is the monodromy argument via the covering space `TauCeti.PrimitiveSpace φ` of local
primitives. It requires only a `C¹` manifold over a real model with corners, with no smoothness
beyond local primitives, no finite dimensionality, no Hausdorff property, and no completeness of the
coefficients. The specialization to closed forms via the Poincaré lemma and de Rham cohomology
lives in `TauCeti.Geometry.Manifold.DeRham.SimplyConnected`.

## Main declarations

* `TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`: a `1`-form with local primitives on
  a simply connected `C¹` manifold has a global primitive.
* `TauCeti.exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_of_simplyConnectedSpace`: the
  global primitive vanishing at a basepoint is given by continuous path integration.
* `TauCeti.exists_isPrimitiveOn_of_isSimplyConnected` and
  `TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn`: global primitives on
  simply connected open subsets and on open subsets with simply connected components.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
* Allen Hatcher, *Algebraic Topology*, Proposition 1.33 (the lifting criterion).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`1`-forms with local primitives on simply connected manifolds have global primitives.** On a
simply connected `C¹` manifold over any real model with corners, a `1`-form `φ` such that every
point lies in an open set carrying a primitive of `φ` is the differential of a function
differentiable on the whole manifold. Nothing else is assumed of `φ`, and neither finite
dimensionality, the Hausdorff property nor completeness of the coefficients is needed. -/
theorem exists_isPrimitiveOn_univ_of_simplyConnectedSpace [IsManifold I 1 M]
    [SimplyConnectedSpace M] {φ : RoughForm I M F 1}
    (hφ : ∀ x, ∃ g : M → F, ∃ U, x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g univ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- lift the identity of `M` through the covering space of local primitives
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
      hφ).existsUnique_continuousMap_lifts (ContinuousMap.id M) x₀ (PrimitiveSpace.graph φ 0 x₀)
      (PrimitiveSpace.proj_graph x₀)
  have hps (y : M) : PrimitiveSpace.proj φ (s y) = y := congrFun hs y
  -- Near each point `x`, the value of `s` differs by a constant from a local primitive of `φ`.
  refine ⟨fun y ↦ PrimitiveSpace.value φ (s y),
    isPrimitiveOn_of_forall_eventuallyEq_add_const isOpen_univ fun x _ ↦ ?_⟩
  obtain ⟨g, U, hxU, hgU⟩ := hφ x
  refine ⟨g, U, hxU, hgU, PrimitiveSpace.value φ (s x) - g x, ?_⟩
  filter_upwards [PrimitiveSpace.eventually_value_eq_add_const (s.continuous.continuousAt (x := x))
    hgU ((hps x).symm ▸ hxU)] with y hy
  rw [hy.2, hps, hps]

/-- On a simply connected `C¹` manifold, a `1`-form with local primitives has a global primitive
vanishing at a chosen basepoint `x₀`, given at every point `x` by the continuous path integral
along any path from `x₀` to `x`. -/
theorem exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_of_simplyConnectedSpace
    [IsManifold I 1 M] [SimplyConnectedSpace M] {φ : RoughForm I M F 1}
    (hφ : ∀ x : M, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U) (x₀ : M) :
    ∃ g : M → F, IsPrimitiveOn φ g univ ∧ g x₀ = 0 ∧
      ∀ (x : M) (γ : Path x₀ x), g x = continuousPathIntegral φ γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveOn_univ_of_simplyConnectedSpace hφ
  refine ⟨fun y ↦ g y + -g x₀, hg.add_const (-g x₀), add_neg_cancel _, fun x γ ↦ ?_⟩
  rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn hφ hg γ (fun _ ↦ mem_univ _), sub_eq_add_neg]

/-- A `1`-form with local primitives on a simply connected open subset `U` of a `C¹` manifold has
a primitive on `U`. -/
theorem exists_isPrimitiveOn_of_isSimplyConnected [IsManifold I 1 M]
    {φ : RoughForm I M F 1} {U : Set M} (hU : IsOpen U) (hUsc : IsSimplyConnected U)
    (hφ : ∀ x ∈ U, ∃ (g : M → F) (V : Set M), x ∈ V ∧ IsPrimitiveOn φ g V) :
    ∃ g : M → F, IsPrimitiveOn φ g U := by
  let U' : TopologicalSpace.Opens M := ⟨U, hU⟩
  have : SimplyConnectedSpace U' := hUsc.simplyConnectedSpace
  have hloc : ∀ x : U', ∃ (g : U' → F) (V : Set U'), x ∈ V ∧
      IsPrimitiveOn (mpullback I I (Subtype.val : U' → M) φ) g V :=
    (forall_exists_isPrimitiveOn_mpullback_subtypeVal_iff (U := U') φ).mpr hφ
  obtain ⟨g, hg⟩ := exists_isPrimitiveOn_univ_of_simplyConnectedSpace hloc
  exact ⟨Function.extend (Subtype.val : U' → M) g 0, by simpa [U'] using hg.of_mpullback_subtypeVal⟩

/-- A `1`-form with local primitives on an open subset `U` of a `C¹` manifold has a primitive on
`U` whenever every connected component of `U` is simply connected. -/
theorem exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn [IsManifold I 1 M]
    {φ : RoughForm I M F 1} {U : Set M} (hU : IsOpen U)
    (hUsc : ∀ x ∈ U, IsSimplyConnected (connectedComponentIn U x))
    (hφ : ∀ x ∈ U, ∃ (g : M → F) (V : Set M), x ∈ V ∧ IsPrimitiveOn φ g V) :
    ∃ g : M → F, IsPrimitiveOn φ g U := by
  let U' : TopologicalSpace.Opens M := ⟨U, hU⟩
  let φ' : RoughForm I U' F 1 := mpullback I I (Subtype.val : U' → M) φ
  have hloc : ∀ x : U', ∃ (g : U' → F) (V : Set U'), x ∈ V ∧ IsPrimitiveOn φ' g V :=
    (forall_exists_isPrimitiveOn_mpullback_subtypeVal_iff (U := U') φ).mpr hφ
  have hloop : ∀ (x : U') (γ : Path x x), continuousPathIntegral φ' γ = 0 := by
    intro x γ
    let C : Set M := connectedComponentIn U x
    have : SimplyConnectedSpace C := (hUsc x x.property).simplyConnectedSpace
    have hmem (t : unitInterval) : (γ t : M) ∈ C := by
      have hsub : range (fun s : unitInterval ↦ (γ s : M)) ⊆ C :=
        (isPreconnected_range
          (continuous_subtypeVal.comp γ.continuous)).subset_connectedComponentIn
            ⟨0, by simp⟩ (by rintro _ ⟨s, rfl⟩; exact (γ s).property)
      exact hsub ⟨t, rfl⟩
    let γC : Path (⟨x, mem_connectedComponentIn x.property⟩ : C)
        ⟨x, mem_connectedComponentIn x.property⟩ :=
      { toFun := fun t ↦ ⟨γ t, hmem t⟩
        continuous_toFun := (continuous_subtypeVal.comp γ.continuous).subtype_mk hmem
        source' := Subtype.ext (by simp)
        target' := Subtype.ext (by simp) }
    let incl : C → U' := fun z ↦ ⟨z.val, connectedComponentIn_subset U x z.property⟩
    have hincl : Continuous incl := continuous_subtypeVal.subtype_mk _
    have hhom : γ.Homotopic (Path.refl x) := by
      have hC : γC.Homotopic (Path.refl _) := SimplyConnectedSpace.paths_homotopic _ _
      have h1 : γC.map hincl = γ := Path.ext (funext fun _ ↦ rfl)
      have h2 : (Path.refl (⟨x, mem_connectedComponentIn x.property⟩ : C)).map hincl =
          Path.refl x :=
        Path.ext (funext fun _ ↦ rfl)
      simpa only [h1, h2] using hC.map ⟨incl, hincl⟩
    rw [continuousPathIntegral_eq_of_homotopic hhom, continuousPathIntegral_refl]
  obtain ⟨g, hg⟩ :=
    (exists_isPrimitiveOn_univ_iff_forall_continuousPathIntegral_loop_eq_zero hloc).mpr hloop
  exact ⟨Function.extend (Subtype.val : U' → M) g 0, by simpa [U'] using hg.of_mpullback_subtypeVal⟩

end TauCeti
