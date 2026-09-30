/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Algebra.Group.Basic
public import TauCeti.Topology.Discrete

/-!
# Coordinate topology on permutation wreath products

The base has the product topology and the permutation group has the topology of pointwise
convergence. Relabeling the index type by a continuous equivalence is continuous. When the base
is a topological group and the index type is discrete, this topology makes the wreath product a
topological group.
-/

public section

namespace TauCeti.WreathProduct

universe u v

variable (D : Type u) (ι : Type v) [Group D]

/-- The coordinate topology on a permutation wreath product. The base coordinates have the
product topology, while the permutation has the topology of pointwise convergence. -/
instance instTopologicalSpace [TopologicalSpace D] [TopologicalSpace ι] :
    TopologicalSpace (WreathProduct D ι) :=
  TopologicalSpace.induced
    (fun w : WreathProduct D ι => (w.left, (w.right : ι → ι))) inferInstance

variable {D ι} {κ : Type*} [TopologicalSpace D] [TopologicalSpace ι]
  [TopologicalSpace κ]

/-- The coordinate map induces the topology on the permutation wreath product. -/
theorem isInducing_left_right :
    Topology.IsInducing (fun w : WreathProduct D ι => (w.left, (w.right : ι → ι))) := ⟨rfl⟩

/-- The coordinate map embeds the permutation wreath product into the product of function spaces. -/
theorem isEmbedding_left_right :
    Topology.IsEmbedding (fun w : WreathProduct D ι => (w.left, (w.right : ι → ι))) := by
  refine ⟨isInducing_left_right, ?_⟩
  intro w z h
  apply SemidirectProduct.ext
  · exact congrArg Prod.fst h
  · exact Equiv.ext (congrFun (congrArg Prod.snd h))

/-- A map into a permutation wreath product is continuous exactly when each base and
permutation coordinate is continuous. -/
theorem continuous_iff {α : Type*} [TopologicalSpace α]
    {f : α → WreathProduct D ι} :
    Continuous f ↔
      (∀ i, Continuous fun a => (f a).left i) ∧
      (∀ i, Continuous fun a => (f a).right i) := by
  constructor
  · intro hf
    have h : Continuous (fun a => ((f a).left, ((f a).right : ι → ι))) :=
      isInducing_left_right.continuous_iff.mp hf
    exact ⟨fun i => (continuous_apply i).comp h.fst,
      fun i => (continuous_apply i).comp h.snd⟩
  · rintro ⟨hl, hr⟩
    exact isInducing_left_right.continuous_iff.mpr
      ((continuous_pi hl).prodMk (continuous_pi hr))

/-- Evaluation of a base coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_left (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.left i) :=
  (continuous_iff.mp continuous_id).1 i

/-- Evaluation of a permutation coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_right (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.right i) :=
  (continuous_iff.mp continuous_id).2 i

/-- Evaluation of the inverse permutation coordinate is continuous when the index is discrete. -/
@[continuity, fun_prop] theorem continuous_right_inv [DiscreteTopology ι] (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.right⁻¹ i) := by
  simpa only [Equiv.Perm.coe_inv] using
    (continuous_equiv_symm_apply (f := fun w : WreathProduct D ι => w.right)
      (fun j => continuous_right j) i)

/-- Joint evaluation of a base coordinate is continuous for a discrete index type. -/
theorem continuous_left_eval [DiscreteTopology ι] :
    Continuous (fun p : WreathProduct D ι × ι => p.1.left p.2) :=
  continuous_prod_of_discrete_right.mpr fun i => by
    simpa using (continuous_left i)

/-- Joint evaluation of a permutation coordinate is continuous for a discrete index type. -/
theorem continuous_right_eval [DiscreteTopology ι] :
    Continuous (fun p : WreathProduct D ι × ι => p.1.right p.2) :=
  continuous_prod_of_discrete_right.mpr fun i => by
    simpa using (continuous_right i)

/-- Multiplication is continuous when the base has continuous multiplication and the index is
discrete. -/
instance instContinuousMul [ContinuousMul D] [DiscreteTopology ι] :
    ContinuousMul (WreathProduct D ι) := ⟨by
    apply continuous_iff.mpr
    constructor
    · intro i
      have hi : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.1.right⁻¹ i) := (continuous_right_inv i).comp continuous_fst
      have hb : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.2.left (p.1.right⁻¹ i)) :=
        continuous_left_eval.comp (continuous_snd.prodMk hi)
      convert ((continuous_left i).comp continuous_fst).mul hb using 1
      ext p
      exact (PermutationWreathProduct.mul_left p.1 p.2 i).symm
    · intro i
      have hi : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.2.right i) := (continuous_right i).comp continuous_snd
      have hc : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.1.right (p.2.right i)) :=
        continuous_right_eval.comp (continuous_fst.prodMk hi)
      convert hc using 1
      ext p
      simp only [SemidirectProduct.mul_right, Equiv.Perm.mul_apply]⟩

/-- Inversion is continuous when the base has continuous inversion and the index is discrete. -/
instance instContinuousInv [ContinuousInv D] [DiscreteTopology ι] :
    ContinuousInv (WreathProduct D ι) := ⟨by
    apply continuous_iff.mpr
    constructor
    · intro i
      have hi : Continuous (fun w : WreathProduct D ι => w.right i) := continuous_right i
      have hb : Continuous (fun w : WreathProduct D ι => (w.left (w.right i))⁻¹) :=
        (continuous_left_eval.comp (continuous_id.prodMk hi)).inv
      simpa only [PermutationWreathProduct.inv_left, Equiv.Perm.smul_def] using hb
    · intro i
      simpa only [SemidirectProduct.inv_right] using (continuous_right_inv i)⟩

/-- The coordinate topology makes a wreath product a topological group when the base is one and
the index type is discrete. -/
instance instIsTopologicalGroup [IsTopologicalGroup D] [DiscreteTopology ι] :
    IsTopologicalGroup (WreathProduct D ι) := ⟨⟩

/-- Relabeling a wreath product is continuous when the relabeling of its index type is
continuous. -/
theorem continuous_congr (e : ι ≃ κ) (he : Continuous e) :
    Continuous (congr (D := D) e) := by
  apply continuous_iff.mpr
  constructor
  · intro i
    simpa only [congr_left, Function.comp_def] using (continuous_left (e.symm i))
  · intro i
    simpa only [congr_right, Equiv.permCongr_apply, Function.comp_def] using
      he.comp (continuous_right (e.symm i))

end TauCeti.WreathProduct
