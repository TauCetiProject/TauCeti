/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath

/-!
# Exactness of `1`-forms on simply connected manifolds

Every `1`-form with local primitives on a simply connected `C¹` manifold over any real model with
corners has a global primitive (`TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`),
requiring no regularity of the form, completeness of the coefficients, finite dimensionality, or
Hausdorff property. The same holds on any open subset whose connected components are simply
connected (`TauCeti.exists_isPrimitiveOn_of_isSimplyConnected`,
`TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn`).

In particular, on a simply connected finite-dimensional Hausdorff smooth manifold every closed
`C^r` `1`-form (`1 ≤ r`) with complete coefficients is the differential of a `C^r` function
(`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`), so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

The proof is the monodromy argument. Pairs `(x, a)` of a point and a value are topologized so
that the graphs `{(y, g y) | y ∈ U}` of the local primitives `g` of `φ` on open sets `U` form a
basis (`TauCeti.PrimitiveSpace`). Projecting to the point is a covering map: over an open set
carrying a primitive `g`, the sheets are the graphs of the translates `g + c`. A simply connected,
locally path-connected base lifts the identity through every covering map, and the second
coordinate of such a lift is a global primitive of `φ`, since near each point it agrees with a
translate of a local primitive. For closed `C^r` forms, the Poincaré lemma
(`TauCeti.exists_mextDeriv_eq_nhds`) supplies the local primitives; that is the only step using
finite dimensionality, the Hausdorff property, and completeness of the coefficient space.

## Main declarations

* `TauCeti.exists_isPrimitiveOn_univ_of_simplyConnectedSpace`: a `1`-form with local primitives on
  a simply connected `C¹` manifold has a global primitive.
* `TauCeti.exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_of_simplyConnectedSpace`: the
  global primitive vanishing at a basepoint is given by continuous path integration.
* `TauCeti.exists_isPrimitiveOn_of_isSimplyConnected` and
  `TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn`: global primitives on
  simply connected open subsets and on open subsets with simply connected components.
* `TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`: a closed `C^r` `1`-form (`1 ≤ r`) with
  values in a complete space on a simply connected manifold has a `C^r` primitive.
* `TauCeti.exactForms_one_eq_closedForms_of_simplyConnectedSpace`: on a simply connected manifold
  every closed smooth real `1`-form is exact.
* `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`: `H¹_dR(M) = 0` for simply
  connected `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields* (closed covector fields on simply connected manifolds are exact), and
  Chapter 17.
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

/-! ### `1`-forms with local primitives on simply connected `C¹` manifolds -/

section LocalPrimitives

/-- **Exactness on simply connected manifolds.** A `1`-form with local primitives on a simply
connected `C¹` manifold over any real model with corners has a global primitive. No regularity of
`φ`, completeness of `F`, finite dimensionality, or Hausdorff property is assumed. -/
theorem exists_isPrimitiveOn_univ_of_simplyConnectedSpace [IsManifold I 1 M]
    [SimplyConnectedSpace M] {φ : RoughForm I M F 1}
    (hφ : ∀ x : M, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U) :
    ∃ g : M → F, IsPrimitiveOn φ g univ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id M) x₀ (PrimitiveSpace.graph φ 0 x₀)
      (PrimitiveSpace.proj_graph x₀)
  have hps (y : M) : PrimitiveSpace.proj φ (s y) = y := congrFun hs y
  refine ⟨fun y ↦ PrimitiveSpace.value φ (s y), isOpen_univ, fun x _ ↦ ?_, fun x _ ↦ ?_⟩
  · obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hφ
        (s.continuous.continuousAt (x := x))
    rw [hps] at hxU
    have hmd : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ g y + c) x :=
      ((hgU.mdifferentiableOn x hxU).mdifferentiableAt (hgU.isOpen.mem_nhds hxU)).add
        (mdifferentiableAt_const (c := c))
    exact (hmd.congr_of_eventuallyEq (hc.mono fun y hy ↦ by rw [hy.2, hps])).mdifferentiableWithinAt
  · obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hφ
        (s.continuous.continuousAt (x := x))
    rw [hps] at hxU
    rw [mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (hc.mono fun y hy ↦ by rw [hy.2, hps])]
    exact hgU.mextDeriv_eq x hxU

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

end LocalPrimitives

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]

/-! ### Exactness of closed smooth forms on simply connected manifolds -/

/-- **Closed `1`-forms on simply connected manifolds are exact.** A closed `C^r` `1`-form
(`1 ≤ r`) with values in a complete space on a simply connected manifold is the exterior
derivative of a `C^r` function. -/
theorem exists_mextDeriv_eq_of_simplyConnectedSpace [SimplyConnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  have hloc : ∀ x : M, ∃ (g : M → F) (U : Set M), x ∈ U ∧ IsPrimitiveOn φ g U := fun x ↦
    let ⟨g, _, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
    ⟨g, U, hxU, hgU⟩
  obtain ⟨f, hf⟩ := exists_isPrimitiveOn_univ_of_simplyConnectedSpace hloc
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const (f := f) fun x ↦ ?_
  obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
  exact ⟨g, f x - g x, hg x, hf.eventuallyEq_add_const hgU (mem_univ x) hxU, hgU.mextDeriv_eq x hxU⟩

variable (I M) in
/-- On a simply connected manifold every closed smooth real `1`-form is exact. -/
theorem exactForms_one_eq_closedForms_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    exactForms I M 1 = closedForms I M 1 := by
  refine le_antisymm (exactForms_le_closedForms I 1) fun φ hφ ↦ ?_
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_simplyConnectedSpace (r := ⊤) le_top
    φ.isSmoothForm ((mem_closedForms I φ).mp hφ)
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

variable (I M) in
/-- **The first de Rham cohomology of a simply connected manifold vanishes.** -/
theorem subsingleton_deRhamCohomology_one_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    Subsingleton (deRhamCohomology I M 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective _ _ c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_one_eq_closedForms_of_simplyConnectedSpace]
  exact φ.property

end TauCeti
