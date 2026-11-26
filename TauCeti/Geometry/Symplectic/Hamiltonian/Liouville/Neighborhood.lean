/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.ConnectedComponents

/-!
# Commuting Hamiltonian flows are complete near a compact component of a level

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless Hausdorff manifold `M`,
with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, and let
`F : M → (ι → ℝ)` be a family of pairwise Poisson-commuting `C²` functions. Their Hamiltonian
vector fields need not be complete on `M`. This file shows that they become complete after
restriction to a suitable open neighbourhood of any compact connected component `L` of a level
`F⁻¹(c₀)`.

Indeed `L` has an open neighbourhood `W` meeting every level of `F` in a compact set
(`Continuous.exists_isOpen_forall_isCompact_inter_preimage_singleton`). On the open submanifold
`W`, with the restriction of `σ`, the restricted functions still Poisson-commute
(`TauCeti.SmoothTwoForm.poissonBracket_comp_subtype_val`), so each of them is a
first integral of the others. Every maximal integral curve of their Hamiltonian vector fields
therefore stays in one compact level of `F` in `W`, and these vector fields are complete
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_opens_isCompleteVectorField_hamiltonianVectorField`).
The same holds on any open set meeting the levels of `F` in compact sets, for the Hamiltonian vector
field of every function Poisson-commuting there with the `F_i`
(`isCompleteVectorField_hamiltonianVectorField_of_isCompact_inter_preimage_singleton`).
Since `L ⊆ W`, the set `L` is also the connected component of its level in `W`
(`Topology.IsInducing.image_connectedComponentIn_preimage`), and it is compact and regular there
when it is so in `M`
(`IsNondegenerate.exists_opens_isCompact_connectedComponentIn_isCompleteVectorField`).
Reading the complete flows on `W` in `M`, each `X_{F_i}` is complete along `L`: its maximal flow
through a point of `L` is defined at every time and stays in `L`
(`IsNondegenerate.mem_flowDomain_and_flowOf_mem_connectedComponentIn_of_isCompact`).

This is how the theorems about the action of complete commuting Hamiltonian flows, such as the
Liouville–Arnold theorem near a compact regular component of a level, hold with no global
completeness hypothesis: they are applied on `W` and transported along the inclusion `W → M`.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `isCompleteVectorField_hamiltonianVectorField_of_isCompact_inter_preimage_singleton`: on an open
  set with compact levels of `F`, the Hamiltonian vector field of a function Poisson-commuting with
  the `F_i` is complete.
* `exists_opens_isCompleteVectorField_hamiltonianVectorField`: a compact component of a level of
  a family of commuting functions has an open neighbourhood with compact levels on which their
  Hamiltonian vector fields are complete.
* `exists_opens_isCompact_connectedComponentIn_isCompleteVectorField`: a compact regular component
  of a level is a compact regular component of a level of the restricted family on such a
  neighbourhood.
* `mem_flowDomain_and_flowOf_mem_connectedComponentIn_of_isCompact`: the Hamiltonian vector fields
  of the family are complete along a compact component of a level, and their flows preserve it.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
include hσ

/-- **Hamiltonian flows are complete on an open set with compact levels.** Let `U` be an open set
of a finite-dimensional boundaryless Hausdorff manifold with a nondegenerate form `σ`, meeting every
level of a family `F : M → (ι → ℝ)` of differentiable functions in a compact set. On the open
submanifold `U`, with the restriction of `σ`, the Hamiltonian vector field of every `C²` function
`f` which Poisson-commutes on `U` with every `F_i` is complete: its integral curves stay in the
compact levels of `F` in `U`. -/
theorem isCompleteVectorField_hamiltonianVectorField_of_isCompact_inter_preimage_singleton
    [T2Space M] [BoundarylessManifold I M] {ι : Type*} {F : M → ι → ℝ} {U : Opens M}
    (hF : ∀ i, MDifferentiableOn I 𝓘(ℝ) (F · i) U) (hU : ∀ c, IsCompact ((U : Set M) ∩ F ⁻¹' {c}))
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ) 2 f U)
    (hfF : ∀ y ∈ U, ∀ i, σ.poissonBracket (F · i) f y = 0) :
    IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) fun y : U ↦ f y) := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  -- the levels of `F` restricted to `U` are the compact sets `U ∩ F⁻¹(c)`
  have hlev (c : ι → ℝ) : IsCompact ((fun y : U ↦ F y) ⁻¹' {c}) := by
    have hc := hU c
    rw [← Subtype.image_preimage_coe] at hc
    exact Subtype.isCompact_iff.2 hc
  have hσU := hσ.mpullback_subtype_val U
  -- each restricted `F_i` is a first integral of the restricted `f`
  exact hσU.isCompleteVectorField_hamiltonianVectorField_of_isCompact_preimage_singleton
    (hf.comp_contMDiff contMDiff_subtypeVal Subtype.prop) (fun _ ↦ hlev _)
    (fun i ↦ isFirstIntegral_iff.2 fun y ↦
      (poissonBracket_comp_subtype_val σ (F · i) f y).trans (hfF y y.property i))
    fun i y ↦ ((hF i y y.property).mdifferentiableAt (U.isOpen.mem_nhds y.property)).comp y
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)

/-- **Commuting Hamiltonian flows are complete near a compact component of a level.** Let `F` be
a family of pairwise Poisson-commuting `C²` functions for a nondegenerate form `σ` on a
finite-dimensional boundaryless Hausdorff manifold, and let the connected component of `x` in its
level `F⁻¹(F x)` be compact. Then this component lies in an open set `W` which meets every level
of `F` in a compact set. On the open submanifold `W`, with the restriction of `σ`, the restrictions
of the functions `F_i` still Poisson-commute, and their Hamiltonian vector fields are complete. -/
theorem exists_opens_isCompleteVectorField_hamiltonianVectorField [T2Space M]
    [BoundarylessManifold I M] {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) 2 F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    {x : M} (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ W : Opens M, connectedComponentIn (F ⁻¹' {F x}) x ⊆ W ∧
      (∀ c, IsCompact ((fun y : W ↦ F y) ⁻¹' {c})) ∧
      (∀ i j y, SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ)
        (fun y : W ↦ F y i) (fun y : W ↦ F y j) y = 0) ∧
      ∀ i, IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ)
        fun y : W ↦ F y i) := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨W, hWo, hLW, hWc⟩ :=
    hF.continuous.exists_isOpen_forall_isCompact_inter_preimage_singleton hK
  set U : Opens M := ⟨W, hWo⟩
  have hFi (j : ι) : ContMDiff I 𝓘(ℝ) 2 (F · j) := contMDiff_pi_module_iff.1 hF j
  -- the levels of `F` in `U` are the compact sets `W ∩ F⁻¹(c)`
  have hlev (c : ι → ℝ) : IsCompact ((fun y : U ↦ F y) ⁻¹' {c}) := by
    have hc := hWc c
    rw [← Subtype.image_preimage_coe] at hc
    exact Subtype.isCompact_iff.2 hc
  have hcommU (i j : ι) (y : U) :=
    (poissonBracket_comp_subtype_val σ (F · i) (F · j) y).trans (hcomm i j y)
  exact ⟨U, hLW, hlev, hcommU, fun i ↦
    hσ.isCompleteVectorField_hamiltonianVectorField_of_isCompact_inter_preimage_singleton
      (fun j ↦ ((hFi j).mdifferentiable (by simp)).mdifferentiableOn) hWc
      (hFi i).contMDiffOn fun y _ j ↦ hcomm j i y⟩

/-- **Restriction to a neighbourhood of a compact regular component of a level.** Let `F` be a
family of pairwise Poisson-commuting `C²` functions for a nondegenerate form `σ` on a
finite-dimensional boundaryless Hausdorff manifold, and let the connected component `L` of `x` in
its level `F⁻¹(F x)` be compact and consist of regular points of `F`. Then there is an open set `W`
containing `x` such that `L` is the image of the connected component of `x` in the level of the
restriction of `F` to `W`, and that component is compact and consists of regular points of the
restriction. On the open submanifold `W`, with the restriction of `σ`, the restrictions of the
functions `F_i` still Poisson-commute, and their Hamiltonian vector fields are complete. -/
theorem exists_opens_isCompact_connectedComponentIn_isCompleteVectorField [T2Space M]
    [BoundarylessManifold I M] {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) 2 F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    {x : M} (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ (W : Opens M) (hxW : x ∈ W),
      ((↑) : W → M) '' connectedComponentIn ((fun z : W ↦ F z) ⁻¹' {F x}) ⟨x, hxW⟩ =
        connectedComponentIn (F ⁻¹' {F x}) x ∧
      IsCompact (connectedComponentIn ((fun z : W ↦ F z) ⁻¹' {F x}) ⟨x, hxW⟩) ∧
      (∀ z ∈ connectedComponentIn ((fun z : W ↦ F z) ⁻¹' {F x}) ⟨x, hxW⟩,
        IsRegularPoint I 𝓘(ℝ, ι → ℝ) (fun z : W ↦ F z) z) ∧
      (∀ i j y, SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ)
        (fun y : W ↦ F y i) (fun y : W ↦ F y j) y = 0) ∧
      ∀ i, IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ)
        fun y : W ↦ F y i) := by
  obtain ⟨W, hLW, -, hcommW, hcW⟩ :=
    hσ.exists_opens_isCompleteVectorField_hamiltonianVectorField hF hcomm hK
  have hxW : x ∈ W := hLW (mem_connectedComponentIn rfl)
  have himage : ((↑) : W → M) '' connectedComponentIn ((fun z : W ↦ F z) ⁻¹' {F x}) ⟨x, hxW⟩ =
      connectedComponentIn (F ⁻¹' {F x}) x :=
    Topology.IsInducing.subtypeVal.image_connectedComponentIn_preimage (F := F ⁻¹' {F x})
      (y := ⟨x, hxW⟩) (by rwa [Subtype.range_coe])
  refine ⟨W, hxW, himage, by rwa [Subtype.isCompact_iff, himage], fun z hz ↦ ?_, hcommW, hcW⟩
  exact (hreg z (himage ▸ mem_image_of_mem _ hz)).comp (isRegularPoint_subtype_val z)

/-- **Commuting Hamiltonian flows are complete along a compact component of a level.** Let `F` be
a family of pairwise Poisson-commuting `C²` functions for a nondegenerate form `σ` on a
finite-dimensional boundaryless Hausdorff manifold, and let the connected component `L` of `x` in
its level `F⁻¹(F x)` be compact. The Hamiltonian vector fields `X_{F_i}` need not be complete on
`M`, but for every point `y` of `L` and every time `t`, the maximal flow of `X_{F_i}` through `y`
is defined at time `t`, and it stays in `L`. -/
theorem mem_flowDomain_and_flowOf_mem_connectedComponentIn_of_isCompact [T2Space M]
    [BoundarylessManifold I M] {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) 2 F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    {x : M} (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (i : ι) {y : M}
    (hy : y ∈ connectedComponentIn (F ⁻¹' {F x}) x) (t : ℝ) :
    (t, y) ∈ flowDomain (σ.hamiltonianVectorField (F · i)) ∧
      flowOf (σ.hamiltonianVectorField (F · i)) t y ∈ connectedComponentIn (F ⁻¹' {F x}) x := by
  obtain ⟨W, hLW, -, -, hcW⟩ :=
    hσ.exists_opens_isCompleteVectorField_hamiltonianVectorField hF hcomm hK
  have hFi (j : ι) : ContMDiff I 𝓘(ℝ) 2 (F · j) := contMDiff_pi_module_iff.1 hF j
  -- A global integral curve of the complete restricted field through `y`, read in `M`, is an
  -- integral curve of `X_{F_i}`, since the inclusion of `W` carries Hamiltonian vector fields of
  -- restrictions to those on `M`.
  obtain ⟨γ, hγ0, hγ⟩ := (isCompleteVectorField_iff_exists_isMIntegralCurve
    ((hσ.mpullback_subtype_val W).contMDiff_hamiltonianVectorField (n := 1) (by simp)
      ((hFi i).comp contMDiff_subtypeVal))).1 (hcW i) ⟨y, hLW hy⟩
  have hγM : IsMIntegralCurve (fun s ↦ (γ s : M)) (σ.hamiltonianVectorField (F · i)) :=
    isMIntegralCurve_iff_isMIntegralCurveOn.2
      (hγ.isMIntegralCurveOn univ).coe_of_hamiltonianVectorField_mpullback_subtype_val
  have hγ0' : (γ 0 : M) = y := congrArg Subtype.val hγ0
  refine ⟨mem_flowDomain.2 ?_, ?_⟩
  · rw [hγM.maximalIntegralCurveInterval_eq_univ hγ0']
    exact mem_univ t
  rw [← hγ0', flowOf_eq_of_isMIntegralCurve
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hFi i)) hγM t]
  -- The curve stays in the level of `y`, since every `F_j` is a first integral of `F_i`; being
  -- connected, it stays in the component of `y` in that level, which is `L`.
  have hlev : range (fun s ↦ (γ s : M)) ⊆ F ⁻¹' {F x} := by
    rintro _ ⟨s, rfl⟩
    refine funext fun j ↦ ?_
    rw [← (connectedComponentIn_subset _ _ hy : F y = F x), ← hγ0']
    exact (isFirstIntegral_iff.2 fun z ↦ hcomm j i z).apply_eq_of_isMIntegralCurve hγM
      (fun s ↦ ((hFi j).mdifferentiable (by simp)) _) 0 s
  rw [connectedComponentIn_eq hy]
  exact (isPreconnected_range hγM.continuous).subset_connectedComponentIn ⟨0, hγ0'⟩ hlev
    (mem_range_self t)

end IsNondegenerate

end SmoothTwoForm

end TauCeti
