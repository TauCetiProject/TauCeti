/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.RepresentationTheory.Compact.Semisimple
import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Equivariant linear slices at points with compact stabilizer

Let a finite-dimensional real Lie group `G` act smoothly on a finite-dimensional boundaryless
manifold `M`, and let `x : M` be a point whose stabilizer `H = G_x` is compact, as it is for every
point of a proper action (`ProperSMul.isCompact_stabilizer`). This file constructs the linear
data of the slice theorem at `x`:

* an `H`-invariant complement `V` of the orbit tangent space `𝔤 · x` in `T_x M`, for the
  tangent representation `h ↦ dh_x` of `H`
  (`TauCeti.exists_isCompl_orbitTangent_of_isCompact_stabilizer`). The orbit tangent space is
  `H`-invariant because `dh_x` carries `ξ_M(x)` to `(Ad_h ξ)_M(x)`, and the tangent
  representation of the compact group `H` is completely reducible;
* a smooth chart `e` at `x`, with `e x = 0`, derivative the identity at `x` and `H`-invariant
  domain, in which `H` acts by its tangent representation
  (`TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`). This is Bochner's
  linearization theorem `TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace` applied to
  `H` with the Lie group structure of Cartan's closed-subgroup theorem.

The slice through `x` is then `v ↦ e.symm v` on the `H`-invariant open set of `v ∈ V` with
`v ∈ e.target`; its derivative at `0` is the inclusion of `V`. It is `H`-equivariant on the
`H`-invariant set `U = {v ∈ V | v ∈ e.target}`, so the slice map
`(g, v) ↦ g • e.symm v : G × V → M` satisfies `(g h⁻¹) • e.symm (dh_x v) = g • e.symm v` for
`v ∈ U`, and its restriction to `G × U` descends to `G ×_H U`. Outside `e.target` the values of
`e.symm` need not respect the action of `H`. Its differential at `(1, 0)` is `(ξ, v) ↦ ξ_M(x) + v`
(`TauCeti.mfderiv_smul_slice_apply`), which is onto `T_x M` with kernel `𝔤_x × 0` for any slice
along a complement of `𝔤 · x` (`TauCeti.surjective_mfderiv_smul_slice` and
`TauCeti.mfderiv_smul_slice_eq_zero_iff`, in the module on transverse slices). These are the
inputs of the slice theorem `G ×_H B ≅ G • S` for a small invariant ball `B ⊆ V`, which is not
proved here.

## Main results

* `TauCeti.exists_isCompl_orbitTangent_of_isCompact_stabilizer`: the orbit tangent space at a
  point with compact stabilizer has a complement invariant under the stabilizer.
* `TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`: a smooth chart at such
  a point in which the stabilizer acts by its tangent representation.
* `TauCeti.exists_equivariant_slice_of_isCompact_stabilizer`: the equivariant linear slice and
  the differential of its slice map.
* `ProperSMul.exists_equivariant_slice`: the same at every point of a proper smooth action.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.25 and its proof.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.4.
-/

public section

noncomputable section

open Function Set Filter Manifold MulAction
open scoped ContDiff Manifold Topology

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

variable (I) in
/-- **Invariant complements of orbit tangent spaces.** If the stabilizer `G_x` of `x` is compact,
the orbit tangent space `𝔤 · x` has a complement `V` in `T_x M` that is invariant under the
tangent representation `h ↦ dh_x` of `G_x`. -/
theorem exists_isCompl_orbitTangent_of_isCompact_stabilizer [CompleteSpace E]
    [FiniteDimensional ℝ E'] {x : M} (hx : IsCompact (stabilizer G x : Set G)) :
    ∃ V : Submodule ℝ E',
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V ∧
        ∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : CompactSpace (stabilizer G x) := isCompact_iff_compactSpace.mp hx
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    fun g _ ↦ ((ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g) x).mdifferentiableAt
      (by simp)
  -- The tangent representation, on the model space `E'` of `T_x M`.
  let ρ : ContRepresentation ℝ (stabilizer G x) E' := tangentRepresentation hd
  have hρ : Continuous ρ := continuous_tangentRepresentation I hd
  -- The tangent representation of the compact group `G_x` is completely reducible.
  have hss : ρ.toRepresentation.IsSemisimpleRepresentation :=
    Representation.isSemisimpleRepresentation_of_continuous ρ.toRepresentation fun f v ↦
      (LinearMap.continuous_of_finiteDimensional (f : E' →ₗ[ℝ] ℝ)).comp
        (hρ.clm_apply continuous_const)
  -- The orbit tangent space is a subrepresentation.
  let W : Subrepresentation ρ.toRepresentation :=
    { toSubmodule := (InfinitesimalAction.fundamental I G I' M).orbitTangent x
      apply_mem_toSubmodule g _ hv := tangentRepresentation_mem_orbitTangent_fundamental hd g hv }
  obtain ⟨V, hV⟩ := exists_isCompl W
  refine ⟨V.toSubmodule, Subrepresentation.isCompl_toSubmodule.mpr hV, fun g hg v hv ↦ ?_⟩
  rw [← tangentRepresentation_apply hd ⟨g, hg⟩]
  exact V.apply_mem_toSubmodule ⟨g, hg⟩ hv

variable (I) in
include I in
/-- **Equivariant charts at points with compact stabilizer.** If the stabilizer `G_x` of `x` is
compact, there is a smooth chart `e` at `x`, with smooth inverse, `e x = 0` and derivative the
identity at `x`, whose domain is invariant under `G_x` and in which each `h ∈ G_x` acts linearly
by its differential `dh_x`. This is Bochner's linearization theorem for `G_x`, a compact Lie group
by the closed-subgroup theorem. -/
theorem exists_equivariant_contMDiff_chart_of_isCompact_stabilizer [FiniteDimensional ℝ E]
    [CompleteSpace E'] [I'.Boundaryless] {x : M} (hx : IsCompact (stabilizer G x : Set G)) :
    ∃ e : OpenPartialHomeomorph M E',
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I' 𝓘(ℝ, E') ∞ e e.source ∧ ContMDiffOn 𝓘(ℝ, E') I' ∞ e.symm e.target ∧
      HasMFDerivAt I' 𝓘(ℝ, E') e x (ContinuousLinearMap.id ℝ E') ∧
      ∀ g ∈ stabilizer G x, ∀ z ∈ e.source,
        g • z ∈ e.source ∧ e (g • z) = mfderiv I' I' (fun y : M ↦ g • y) x (e z) := by
  have : T2Space G := ModelWithCorners.t2Space_of_lieGroup (I := I) ∞
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The stabilizer is a compact Lie group, with the structure of the closed-subgroup theorem.
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hx.isClosed
  let _ := d.chartedSpace
  have := d.lieGroup
  have : CompactSpace (stabilizer G x) := isCompact_iff_compactSpace.mp hx
  have : ContMDiffSMul 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule)
      I' ∞ (stabilizer G x) M :=
    ⟨(ContMDiffSMul.contMDiff_smul (I := I) (I' := I') (n := ∞) (G := G) (M := M)).comp
      (d.contMDiff_subtypeVal.prodMap contMDiff_id)⟩
  obtain ⟨σ, e, -, hxe, hex, he, hes, hequiv, hσ, hderiv⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace (I := I') (n := ⊤)
      𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule) le_top
      (G := stabilizer G x) (x := x) fun g ↦ g.property
  refine ⟨e, hxe, hex, he, hes, hderiv, fun g hg z hz ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hequiv ⟨g, hg⟩ z hz
  exact ⟨h₁, h₂.trans (by rw [hσ]; rfl)⟩

variable (I) in
/-- **Equivariant linear slices at points with compact stabilizer.** Let the stabilizer `G_x` of
`x` be compact. There are a complement `V` of the orbit tangent space `𝔤 · x` in `T_x M` and a
smooth chart `e` at `x`, with smooth inverse, `e x = 0` and derivative the identity at `x`, such
that:

* each `g ∈ G_x` maps the domain of `e` to itself and acts in the chart by `dg_x`, which preserves
  `V` and the target of `e`; so the slice `v ↦ e.symm v` satisfies
  `e.symm (dg_x v) = g • e.symm v`;
* the slice map `Ψ (g, v) = g • e.symm v` on `G × V` has differential `(ξ, v) ↦ ξ_M(x) + v` at
  `(1, 0)`, which is onto `T_x M` and vanishes exactly on `𝔤_x × 0`.

Equivariance gives `Ψ (g * h⁻¹, dh_x v) = Ψ (g, v)` for `h ∈ G_x` and `v` in the `G_x`-invariant
set `U = {v ∈ V | v ∈ e.target}`, so `Ψ` restricted to `G × U` descends to `G ×_{G_x} U`. The
surjectivity and kernel statements are the inputs for proving that the descended map has bijective
differential at the class of `(1, 0)`; that quotient and its differential are not constructed
here. -/
theorem exists_equivariant_slice_of_isCompact_stabilizer [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [I'.Boundaryless] {x : M} (hx : IsCompact (stabilizer G x : Set G)) :
    ∃ (V : Submodule ℝ E') (e : OpenPartialHomeomorph M E'),
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V ∧
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I' 𝓘(ℝ, E') ∞ e e.source ∧ ContMDiffOn 𝓘(ℝ, E') I' ∞ e.symm e.target ∧
      HasMFDerivAt I' 𝓘(ℝ, E') e x (ContinuousLinearMap.id ℝ E') ∧
      (∀ g ∈ stabilizer G x, ∀ z ∈ e.source,
        g • z ∈ e.source ∧ e (g • z) = mfderiv I' I' (fun y : M ↦ g • y) x (e z)) ∧
      (∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V) ∧
      (∀ g ∈ stabilizer G x, ∀ v ∈ e.target,
        mfderiv I' I' (fun y : M ↦ g • y) x v ∈ e.target ∧
          e.symm (mfderiv I' I' (fun y : M ↦ g • y) x v) = g • e.symm v) ∧
      (∀ v : V, mfderiv 𝓘(ℝ, V) I' (fun v : V ↦ e.symm (v : E')) 0 v = (v : E')) ∧
      Surjective
        (mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • e.symm (p.2 : E')) (1, 0)) ∧
      ∀ (ξ : GroupLieAlgebra I G) (v : V),
        mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • e.symm (p.2 : E')) (1, 0) (ξ, v) =
            0 ↔ ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ∧ v = 0 := by
  obtain ⟨V, hV, hVinv⟩ := exists_isCompl_orbitTangent_of_isCompact_stabilizer (I' := I') I hx
  obtain ⟨e, hxe, hex, he, hes, hderiv, hequiv⟩ :=
    exists_equivariant_contMDiff_chart_of_isCompact_stabilizer (I' := I') I hx
  have h0 : (0 : E') ∈ e.target := hex ▸ e.map_source hxe
  have hsymm0 : e.symm 0 = x := by rw [← hex, e.left_inv hxe]
  -- The inverse chart has derivative the identity at `0`, since `e ∘ e.symm` is the identity near
  -- `0` and `e` has derivative the identity at `x`.
  have hsd : MDifferentiableAt 𝓘(ℝ, E') I' e.symm 0 :=
    (hes.contMDiffAt (e.open_target.mem_nhds h0)).mdifferentiableAt (by simp)
  have hed : MDifferentiableAt I' 𝓘(ℝ, E') e (e.symm 0) := hsymm0 ▸ hderiv.mdifferentiableAt
  have hL (w : E') : mfderiv 𝓘(ℝ, E') I' e.symm 0 w = w := by
    have h₁ (u : E') : mfderiv I' 𝓘(ℝ, E') e (e.symm 0) u = u := by
      rw [hsymm0, hderiv.mfderiv]
      rfl
    exact (h₁ _).symm.trans (e.mfderiv_apply_mfderiv_symm_apply h0 hed hsd w)
  -- The slice `σ v = e.symm v` on `V` has derivative the inclusion of `V` at `0`.
  set σ : V → M := fun v ↦ e.symm (v : E') with hσ
  have hσd : MDifferentiableAt 𝓘(ℝ, V) I' σ 0 :=
    hsd.comp (0 : V) V.subtypeL.mdifferentiableAt
  have hσL (v : V) : mfderiv 𝓘(ℝ, V) I' σ 0 v = (v : E') := by
    have h := mfderiv_comp_apply (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E')) (I'' := I') (f := V.subtypeL)
      (g := e.symm) (0 : V) hsd V.subtypeL.mdifferentiableAt v
    rw [V.subtypeL.mfderiv_eq] at h
    exact h.trans (hL v)
  have hσ0 : σ 0 = x := by simp [hσ, hsymm0]
  refine ⟨V, e, hV, hxe, hex, he, hes, hderiv, hequiv, hVinv, fun g hg v hv ↦ ?_, hσL,
    surjective_mfderiv_smul_slice hV.sup_eq_top hσd hσ0 hσL,
    mfderiv_smul_slice_eq_zero_iff hV.disjoint hσd hσ0 hσL⟩
  -- The chart intertwines `g` with `dg_x`, so `e.symm` does too.
  obtain ⟨h₁, h₂⟩ := hequiv g hg (e.symm v) (e.map_target hv)
  rw [e.right_inv hv] at h₂
  rw [← h₂]
  exact ⟨e.map_source h₁, e.left_inv h₁⟩

variable (I) in
/-- **Equivariant linear slices of proper actions.** At every point `x` of a proper smooth action,
the conclusions of `TauCeti.exists_equivariant_slice_of_isCompact_stabilizer` hold: the stabilizer
of `x` is compact. -/
theorem _root_.ProperSMul.exists_equivariant_slice [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [I'.Boundaryless] [ProperSMul G M] (x : M) :
    ∃ (V : Submodule ℝ E') (e : OpenPartialHomeomorph M E'),
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) V ∧
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I' 𝓘(ℝ, E') ∞ e e.source ∧ ContMDiffOn 𝓘(ℝ, E') I' ∞ e.symm e.target ∧
      HasMFDerivAt I' 𝓘(ℝ, E') e x (ContinuousLinearMap.id ℝ E') ∧
      (∀ g ∈ stabilizer G x, ∀ z ∈ e.source,
        g • z ∈ e.source ∧ e (g • z) = mfderiv I' I' (fun y : M ↦ g • y) x (e z)) ∧
      (∀ g ∈ stabilizer G x, ∀ v ∈ V, mfderiv I' I' (fun y : M ↦ g • y) x v ∈ V) ∧
      (∀ g ∈ stabilizer G x, ∀ v ∈ e.target,
        mfderiv I' I' (fun y : M ↦ g • y) x v ∈ e.target ∧
          e.symm (mfderiv I' I' (fun y : M ↦ g • y) x v) = g • e.symm v) ∧
      (∀ v : V, mfderiv 𝓘(ℝ, V) I' (fun v : V ↦ e.symm (v : E')) 0 v = (v : E')) ∧
      Surjective
        (mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • e.symm (p.2 : E')) (1, 0)) ∧
      ∀ (ξ : GroupLieAlgebra I G) (v : V),
        mfderiv (I.prod 𝓘(ℝ, V)) I' (fun p : G × V ↦ p.1 • e.symm (p.2 : E')) (1, 0) (ξ, v) =
            0 ↔ ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ∧ v = 0 :=
  exists_equivariant_slice_of_isCompact_stabilizer I (ProperSMul.isCompact_stabilizer x)

end TauCeti
