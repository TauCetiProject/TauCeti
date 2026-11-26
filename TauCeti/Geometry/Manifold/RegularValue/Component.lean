/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Topology.ConnectedComponents

/-!
# Components of a level as open subsets of a regular fibre

Let `f : M → N` be a `C^m` map, `m ≥ 1`, from a finite-dimensional boundaryless manifold to a
finite-dimensional manifold, and let `L` be the connected component of a point `x` in its level
`f⁻¹(f x)`. The level need not be a regular fibre: other components may contain critical points.
Suppose that `L` lies in an open set `U` of regular points of `f`. Then the fibre
`{y : U // f y = f x}` of the restriction of `f` to `U` is a regular fibre, carrying its
regular-fibre atlas (`TauCeti.regularFiberComponentChartedSpace`, which is
`TauCeti.regularFiberChartedSpace` for the restriction, applicable by
`TauCeti.isRegularValue_restrict_of_forall_isRegularPoint`), and `L` is an open subset of it
(`TauCeti.regularFiberComponent`). Indeed `L`, read in this fibre, is the connected component of
`x` there (`TauCeti.coe_regularFiberComponent`), and a manifold is locally connected. This gives
`L` the smooth structure of an open submanifold of a regular fibre, of dimension `dim M - dim N`,
for which its inclusion in `M` is a smooth embedding
(`TauCeti.isSmoothEmbedding_coe_regularFiberComponent`). Its topology is the subspace topology
from `M` (`TauCeti.regularFiberComponentHomeomorph`).

This smooth structure is recognized through smooth embeddings: a smooth embedding `g` of any
manifold into `M` with range `L` is a diffeomorphism onto this open submanifold
(`Manifold.IsSmoothEmbedding.regularFiberComponentDiffeomorph`). This is how a component of a
level that is regular, but lies in a level containing critical points, is identified with a model
manifold, for instance a regular component of a level of an integrable system with a torus.

## Main definitions

* `TauCeti.regularFiberComponentChartedSpace`: the regular-fibre atlas of the fibre of the
  restriction of `f` to `U`.
* `TauCeti.regularFiberComponent`: the component of `x` in its level, as an open subset of the
  regular fibre of the restriction of `f` to `U`.
* `TauCeti.regularFiberComponentHomeomorph`: its identification with the component as a subspace
  of `M`.
* `Manifold.IsSmoothEmbedding.regularFiberComponentDiffeomorph`: a smooth embedding with range the
  component, as a diffeomorphism onto this open submanifold.

## Main results

* `TauCeti.coe_regularFiberComponent`: the component, read in the regular fibre, is the connected
  component of `x` in the regular fibre.
* `TauCeti.isSmoothEmbedding_coe_regularFiberComponent`: its inclusion in `M` is a smooth
  embedding.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Proposition 5.1 (open submanifolds).
-/

public section

noncomputable section

open Function Module Set TopologicalSpace Topology Manifold
open scoped ContDiff

namespace TauCeti

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J m N]
  {f : M → N} {U : Opens M} {x : M}

variable (hm : 1 ≤ m) (hf : ContMDiff I J m f) (hc : J.IsInteriorPoint (f x))
  (hU : ∀ y : U, IsRegularPoint I J f y) (hLU : connectedComponentIn (f ⁻¹' {f x}) x ⊆ U)

/-- The regular-fibre atlas of the fibre `{y : U // f y = f x}` of the restriction of `f` to an
open set `U` of regular points, of dimension `dim M - dim N`. It is not a global instance; every
statement about `TauCeti.regularFiberComponent` installs it locally. -/
abbrev regularFiberComponentChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ) {y : U // f y = f x} :=
  regularFiberChartedSpace (f := fun y : U ↦ f y) hm (hf.comp contMDiff_subtypeVal) hc
    (isRegularValue_restrict_of_forall_isRegularPoint hU (f x))

omit [TopologicalSpace N] in
/-- Read in the fibre `{y : U // f y = f x}`, the component of `x` in its level is the connected
component of `x` there: every point of the component lies in `U` and in the level, so it is a point
of the fibre. -/
private theorem setOf_mem_connectedComponentIn_eq :
    {z : {y : U // f y = f x} | ((z : U) : M) ∈ connectedComponentIn (f ⁻¹' {f x}) x} =
      connectedComponent ⟨⟨x, hLU (mem_connectedComponentIn rfl)⟩, rfl⟩ :=
  IsInducing.preimage_connectedComponentIn (f := fun z : {y : U // f y = f x} ↦ ((z : U) : M))
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).isInducing (F := f ⁻¹' {f x})
    (y := ⟨⟨x, hLU (mem_connectedComponentIn rfl)⟩, rfl⟩) (range_subset_iff.2 fun z ↦ z.property)
    fun w hw ↦ ⟨⟨⟨w, hLU hw⟩, connectedComponentIn_subset _ _ hw⟩, rfl⟩

/-- **The component of a level as an open subset of a regular fibre.** If the connected
component `L` of `x` in its level `f⁻¹(f x)` lies in an open set `U` of regular points of `f`,
then `L` is an open subset of the regular fibre `{y : U // f y = f x}` of the restriction of `f`
to `U`. With the regular-fibre atlas of that fibre, this open subset is a manifold of dimension
`dim M - dim N` (`TauCeti.isSmoothEmbedding_coe_regularFiberComponent`). -/
def regularFiberComponent : Opens {y : U // f y = f x} where
  carrier := {z | ((z : U) : M) ∈ connectedComponentIn (f ⁻¹' {f x}) x}
  is_open' := by
    let := regularFiberComponentChartedSpace hm hf hc hU
    have := ChartedSpace.locallyConnectedSpace (Fin (finrank ℝ E - finrank ℝ F) → ℝ)
      {y : U // f y = f x}
    -- Read in the fibre, the component is the connected component of `x` there.
    rw [setOf_mem_connectedComponentIn_eq hLU]
    exact isOpen_connectedComponent

@[simp]
theorem mem_regularFiberComponent {z : {y : U // f y = f x}} :
    z ∈ regularFiberComponent hm hf hc hU hLU ↔
      ((z : U) : M) ∈ connectedComponentIn (f ⁻¹' {f x}) x :=
  Iff.rfl

/-- The component, read in the regular fibre, is the connected component of `x` in the regular
fibre. -/
theorem coe_regularFiberComponent :
    (regularFiberComponent hm hf hc hU hLU : Set {y : U // f y = f x}) =
      connectedComponent ⟨⟨x, hLU (mem_connectedComponentIn rfl)⟩, rfl⟩ :=
  setOf_mem_connectedComponentIn_eq hLU

/-- The open subset `TauCeti.regularFiberComponent` of the regular fibre is homeomorphic to the
component of `x` in its level, with the subspace topology from `M`, by the identity on points. -/
def regularFiberComponentHomeomorph :
    regularFiberComponent hm hf hc hU hLU ≃ₜ connectedComponentIn (f ⁻¹' {f x}) x where
  toFun z := ⟨(((z : {y : U // f y = f x}) : U) : M), z.property⟩
  invFun w := ⟨⟨⟨w, hLU w.property⟩, connectedComponentIn_subset _ _ w.property⟩, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_regularFiberComponentHomeomorph_apply (z : regularFiberComponent hm hf hc hU hLU) :
    (regularFiberComponentHomeomorph hm hf hc hU hLU z : M) =
      (((z : {y : U // f y = f x}) : U) : M) :=
  (rfl)

@[simp]
theorem coe_regularFiberComponentHomeomorph_symm_apply
    (w : connectedComponentIn (f ⁻¹' {f x}) x) :
    ((((regularFiberComponentHomeomorph hm hf hc hU hLU).symm w :
      {y : U // f y = f x}) : U) : M) = w :=
  (rfl)

variable [IsManifold I m M]

/-- The inclusion in `M` of the component of a level, with its structure of an open submanifold of
the regular fibre of the restriction of `f` to `U`, is a smooth embedding. -/
theorem isSmoothEmbedding_coe_regularFiberComponent :
    letI := regularFiberComponentChartedSpace hm hf hc hU
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ) I m
      (fun z : regularFiberComponent hm hf hc hU hLU ↦ (((z : {y : U // f y = f x}) : U) : M)) := by
  let := regularFiberComponentChartedSpace hm hf hc hU
  have hreg := isRegularValue_restrict_of_forall_isRegularPoint hU (f x)
  have := isManifold_regularFiber (f := fun y : U ↦ f y) hm (hf.comp contMDiff_subtypeVal) hc hreg
  -- The inclusion factors through the open inclusion of the component into the fibre, the fibre
  -- inclusion into `U` and the open inclusion of `U` into `M`.
  exact isSmoothEmbedding_subtypeVal_comp_iff.2
    ((isSmoothEmbedding_coe_regularFiber (f := fun y : U ↦ f y) hm (hf.comp contMDiff_subtypeVal)
      hc hreg).comp_subtypeVal (regularFiberComponent hm hf hc hU hLU))

variable {E' H' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {K : ModelWithCorners ℝ E' H'} [TopologicalSpace P] [ChartedSpace H' P] {g : P → M}

/-- **Smooth embeddings onto a regular component of a level.** A smooth embedding `g` of a
manifold `P` into `M` whose range is the connected component `L` of `x` in its level is a
diffeomorphism of `P` onto `L`, with its structure of an open submanifold of the regular fibre of
the restriction of `f` to an open set `U` of regular points containing `L`
(`TauCeti.regularFiberComponent`). -/
def _root_.Manifold.IsSmoothEmbedding.regularFiberComponentDiffeomorph
    (hg : IsSmoothEmbedding K I m g) (hrange : range g = connectedComponentIn (f ⁻¹' {f x}) x) :
    letI := regularFiberComponentChartedSpace hm hf hc hU
    P ≃ₘ^m⟮K, 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ regularFiberComponent hm hf hc hU hLU :=
  letI := regularFiberComponentChartedSpace hm hf hc hU
  ((hg.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)).trans
    (regularFiberComponentHomeomorph hm hf hc hU hLU).symm).diffeomorphOfImmersions
      hg.isImmersion (isSmoothEmbedding_coe_regularFiberComponent hm hf hc hU hLU).isImmersion
      -- Each homeomorphism in the composite keeps the underlying point of `M`.
      (funext fun _ ↦ rfl)

/-- The diffeomorphism onto the regular component sends `p` to the point `g p`. -/
@[simp]
theorem _root_.Manifold.IsSmoothEmbedding.coe_regularFiberComponentDiffeomorph_apply
    (hg : IsSmoothEmbedding K I m g) (hrange : range g = connectedComponentIn (f ⁻¹' {f x}) x)
    (p : P) :
    letI := regularFiberComponentChartedSpace hm hf hc hU
    (((hg.regularFiberComponentDiffeomorph hm hf hc hU hLU hrange p :
      {y : U // f y = f x}) : U) : M) = g p := by
  let := regularFiberComponentChartedSpace hm hf hc hU
  rw [Manifold.IsSmoothEmbedding.regularFiberComponentDiffeomorph,
    Homeomorph.diffeomorphOfImmersions_apply]
  -- Each homeomorphism in the composite keeps the underlying point of `M`.
  rfl

/-- The inverse of the diffeomorphism onto the regular component sends a point of the component
to its preimage under `g`. -/
theorem _root_.Manifold.IsSmoothEmbedding.apply_regularFiberComponentDiffeomorph_symm_apply
    (hg : IsSmoothEmbedding K I m g) (hrange : range g = connectedComponentIn (f ⁻¹' {f x}) x)
    (z : regularFiberComponent hm hf hc hU hLU) :
    letI := regularFiberComponentChartedSpace hm hf hc hU
    g ((hg.regularFiberComponentDiffeomorph hm hf hc hU hLU hrange).symm z) =
      (((z : {y : U // f y = f x}) : U) : M) := by
  let := regularFiberComponentChartedSpace hm hf hc hU
  rw [← hg.coe_regularFiberComponentDiffeomorph_apply hm hf hc hU hLU hrange,
    Diffeomorph.apply_symm_apply]

end TauCeti
