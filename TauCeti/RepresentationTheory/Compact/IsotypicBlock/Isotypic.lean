/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.TraceCoefficient.Basic
public import TauCeti.RepresentationTheory.Compact.IsotypicBlock.Equivariance
public import TauCeti.RingTheory.SimpleModule.Isotypic
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Continuous.Intertwining

/-!
# The algebraic isotypic decomposition of the left regular representation

Under left translation, the matrix coefficients of an irreducible model belong to the
algebraic isotypic component of that model in `L²(G)`. Consequently its Peter–Weyl block is
isotypic of the model's type as a module over the group algebra. Over an algebraically closed
field, for a skeleton of the unitary dual, it is exactly that isotypic component. This applies
to infinite compact groups: the ambient left regular action need only be strongly continuous.

The coefficient map is linear in its second vector. Equivariance follows from the existing
trace-coefficient comparison, which sends a rank-one operator to a matrix coefficient and
identifies left translation with postcomposition by the model's action. For the reverse
inclusion, the equivariant block projections kill maps from inequivalent simple modules;
Peter–Weyl density then forces every map from the model to land in its own block.

## Main results

* `TauCeti.isIsotypicOfType_leftRegularPeterWeylBlock`: each block is algebraically isotypic
  of its model's type, without an algebraic closedness assumption.
* `TauCeti.leftRegularPeterWeylBlock_asSubmodule_eq_isotypicComponent`: the block is the full
  algebraic isotypic component under left translation.
* `TauCeti.mem_peterWeylBlock_iff_mem_isotypicComponent` and
  `TauCeti.restrictScalars_isotypicComponent_eq_peterWeylBlock`: membership and scalar-restriction
  forms of the identification, for an arbitrary compact group.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*,
  Springer GTM 98 (1985), Chapter III.
-/

public section

open MeasureTheory
open scoped MonoidAlgebra

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A Peter–Weyl block as a subrepresentation of the left regular representation. -/
noncomputable def leftRegularPeterWeylBlock (model : IrrepModel 𝕜 G) :
    Subrepresentation (leftRegularLp 𝕜 G).toRepresentation where
  toSubmodule := peterWeylBlock model
  apply_mem_toSubmodule g _ hf := leftRegularLp_mem_peterWeylBlock model g hf

/-- The left regular block has the usual matrix-coefficient subspace. -/
@[simp]
theorem leftRegularPeterWeylBlock_toSubmodule (model : IrrepModel 𝕜 G) :
    (leftRegularPeterWeylBlock model).toSubmodule = peterWeylBlock model := (rfl)

/-- Membership in the left regular subrepresentation is membership in its coefficient block. -/
@[simp]
theorem mem_leftRegularPeterWeylBlock (model : IrrepModel 𝕜 G)
    (f : Lp 𝕜 2 (haarProb G)) :
    f ∈ leftRegularPeterWeylBlock model ↔ f ∈ peterWeylBlock model := (Iff.rfl)

/-- Every matrix coefficient of an irreducible model lies in its algebraic isotypic
component in the left regular representation. -/
theorem matrixCoeffLp_mem_isotypicComponent (model : IrrepModel 𝕜 G)
    (v w : EuclideanSpace 𝕜 (Fin model.dim)) :
    (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv.symm
      (_root_.ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w) ∈
      isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        model.rep.toRepresentation.asModule := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (_root_.ContRepresentation.matrixCoeffLpIntertwiner model.rep model.continuous_rep
      model.isUnitary v).toIntertwiningMap
  have hf := f.apply_mem_isotypicComponent
    (model.rep.toRepresentation.asModuleEquiv.symm w)
  rw [Representation.IntertwiningMap.equivLinearMapAsModule_apply] at hf
  simpa only [Representation.asModuleEquiv_symm_apply,
    ContIntertwiningMap.toIntertwiningMap_apply,
    _root_.ContRepresentation.matrixCoeffLpIntertwiner_apply] using hf

/-- Every vector in a Peter–Weyl block belongs to the algebraic isotypic component of
its model under left translation, even for an infinite compact group. -/
theorem mem_isotypicComponent_of_mem_peterWeylBlock (model : IrrepModel 𝕜 G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model) :
    (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv.symm f ∈
      isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
      model.rep.toRepresentation.asModule := by
  let C := isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
    model.rep.toRepresentation.asModule
  rw [peterWeylBlock_eq_span_range (fun _ : Unit ↦ model) ()] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    simp only [peterWeylFamily_apply, map_smul]
    exact (C.restrictScalars 𝕜).smul_mem _
      (matrixCoeffLp_mem_isotypicComponent model (model.basis p.1) (model.basis p.2))
  | zero => simpa only [map_zero] using C.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact (C.restrictScalars 𝕜).smul_mem c hx

/-- The left regular Peter–Weyl block is contained in its model's algebraic isotypic component. -/
theorem leftRegularPeterWeylBlock_asSubmodule_le_isotypicComponent (model : IrrepModel 𝕜 G) :
    (leftRegularPeterWeylBlock model).asSubmodule ≤
      isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        model.rep.toRepresentation.asModule := by
  intro x hx
  have hx' : (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv x ∈ peterWeylBlock model :=
    (mem_leftRegularPeterWeylBlock model _).mp
      (Subrepresentation.mem_asSubmodule_iff.mp hx)
  simpa only [LinearEquiv.symm_apply_apply] using
    mem_isotypicComponent_of_mem_peterWeylBlock model hx'

/-- Under left translation a Peter–Weyl block is algebraically isotypic of its model's
type. No algebraic closedness or skeleton of irreducibles is needed. -/
theorem isIsotypicOfType_leftRegularPeterWeylBlock (model : IrrepModel 𝕜 G) :
    IsIsotypicOfType 𝕜[G] (leftRegularPeterWeylBlock model).asSubmodule
      model.rep.toRepresentation.asModule := by
  have hle := leftRegularPeterWeylBlock_asSubmodule_le_isotypicComponent model
  exact (IsIsotypicOfType.isotypicComponent 𝕜[G]
    (leftRegularLp 𝕜 G).toRepresentation.asModule model.rep.toRepresentation.asModule).of_injective
      (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

private noncomputable def blockProjection {ι : Type*} {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) (j : ι) :
    (leftRegularLp 𝕜 G).toRepresentation.asModule →ₗ[𝕜[G]]
      (leftRegularPeterWeylBlock (models j)).asSubmodule := by
  let P : Representation.IntertwiningMap (leftRegularLp 𝕜 G).toRepresentation
      (leftRegularLp 𝕜 G).toRepresentation :=
    { __ := (peterWeylBlockAveraging (models j)).toLinearMap
      isIntertwining' g := congrArg ContinuousLinearMap.toLinearMap
        (peterWeylBlockAveraging_comp_leftRegularLp (models j) g) }
  exact (Representation.IntertwiningMap.equivLinearMapAsModule _ _ P).codRestrict _
    fun x => peterWeylBlockAveraging_apply_mem_peterWeylBlock h j _

private theorem blockProjection_apply {ι : Type*} {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) (j : ι)
    (x : (leftRegularLp 𝕜 G).toRepresentation.asModule) :
    (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv (blockProjection h j x).val =
      peterWeylBlockAveraging (models j)
        ((leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv x) := rfl

private theorem blockProjection_comp_eq_zero {ι : Type*} {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) {i j : ι} (hij : i ≠ j)
    (f : (models i).rep.toRepresentation.asModule →ₗ[𝕜[G]]
      (leftRegularLp 𝕜 G).toRepresentation.asModule) :
    (blockProjection h j).comp f = 0 := by
  apply (isIsotypicOfType_leftRegularPeterWeylBlock (models j)).linearMap_eq_zero
  intro he
  have he' := ContRepresentation.nonempty_equiv_iff.mpr
    (Representation.nonempty_equiv_iff.mpr he)
  exact (h.pairwise_isEmpty_equiv hij).false he'.some

private theorem linearMap_apply_mem_peterWeylBlock [IsAlgClosed 𝕜]
    {ι : Type*} {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models) (i : ι)
    (f : (models i).rep.toRepresentation.asModule →ₗ[𝕜[G]]
      (leftRegularLp 𝕜 G).toRepresentation.asModule)
    (x : (models i).rep.toRepresentation.asModule) :
    (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv (f x) ∈
      peterWeylBlock (models i) := by
  classical
  let y := (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv (f x)
  -- Every block projection kills the remainder; density then makes the remainder zero.
  have hy : y - peterWeylBlockAveraging (models i) y ∈
      (⨆ j, peterWeylBlock (models j))ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    simp only [Submodule.mem_iInf]
    intro j
    rw [← Submodule.starProjection_apply_eq_zero_iff,
      ← peterWeylBlockAveraging_eq_starProjection h j, map_sub]
    by_cases hji : j = i
    · subst j
      rw [peterWeylBlockAveraging_apply_of_mem (models i)
        (peterWeylBlockAveraging_apply_mem_peterWeylBlock h i y), sub_self]
    · have hz := DFunLike.congr_fun (blockProjection_comp_eq_zero h (Ne.symm hji) f) x
      have hz' : peterWeylBlockAveraging (models j) y = 0 := by
        have := congrArg (fun z =>
          (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv z.val) hz
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply, blockProjection_apply,
          ZeroMemClass.coe_zero, map_zero] using this
      rw [hz', peterWeylBlockAveraging_apply_eq_zero_of_mem
        (h.pairwise_isEmpty_equiv hji)
        (peterWeylBlockAveraging_apply_mem_peterWeylBlock h i y), sub_self]
  rw [orthogonal_iSup_peterWeylBlock_eq_bot h, Submodule.mem_bot, sub_eq_zero] at hy
  -- Give the transported vector its local name before rewriting the remainder identity.
  change y ∈ peterWeylBlock (models i)
  rw [hy]
  exact peterWeylBlockAveraging_apply_mem_peterWeylBlock h i y

/-- The Peter–Weyl block is exactly the algebraic isotypic component of its model in the
left regular representation of an arbitrary compact group. -/
theorem leftRegularPeterWeylBlock_asSubmodule_eq_isotypicComponent [IsAlgClosed 𝕜]
    {ι : Type*} {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models) (i : ι) :
    (leftRegularPeterWeylBlock (models i)).asSubmodule =
      isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule := by
  refine le_antisymm (leftRegularPeterWeylBlock_asSubmodule_le_isotypicComponent _) ?_
  rw [isotypicComponent]
  refine sSup_le fun S hS => ?_
  obtain ⟨e⟩ := hS
  intro x hx
  refine (Subrepresentation.mem_asSubmodule_iff
    (σ := leftRegularPeterWeylBlock (models i))
    (v := (leftRegularLp 𝕜 G).toRepresentation.asModuleEquiv x)).mpr ?_
  apply (mem_leftRegularPeterWeylBlock (models i) _).mpr
  let f := S.subtype.comp e.symm.toLinearMap
  have hf := linearMap_apply_mem_peterWeylBlock h i f (e ⟨x, hx⟩)
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply] using hf

/-- Membership in a Peter–Weyl block is membership in the corresponding algebraic
isotypic component of the left regular representation. -/
theorem mem_peterWeylBlock_iff_mem_isotypicComponent [IsAlgClosed 𝕜]
    {ι : Type*} {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models) (i : ι)
    (f : Lp 𝕜 2 (haarProb G)) :
    f ∈ peterWeylBlock (models i) ↔
      f ∈ isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule := by
  rw [← leftRegularPeterWeylBlock_asSubmodule_eq_isotypicComponent h i,
    Subrepresentation.mem_asSubmodule_iff, mem_leftRegularPeterWeylBlock]

/-- Restricting scalars on the algebraic isotypic component of the left regular
representation gives the Peter–Weyl block, for arbitrary compact groups. -/
theorem restrictScalars_isotypicComponent_eq_peterWeylBlock [IsAlgClosed 𝕜]
    {ι : Type*} {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models) (i : ι) :
    (isotypicComponent 𝕜[G] (leftRegularLp 𝕜 G).toRepresentation.asModule
        (models i).rep.toRepresentation.asModule).restrictScalars 𝕜 =
      peterWeylBlock (models i) :=
  SetLike.ext fun f => (mem_peterWeylBlock_iff_mem_isotypicComponent h i f).symm

end TauCeti
