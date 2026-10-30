/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Permutation groups of discrete spaces

For every topological space, the permutation type carries the topology induced by
`σ ↦ (σ, σ⁻¹)` in the product of two function spaces with their pointwise-convergence topologies.
For a discrete carrier, this is a group topology and the embedding is closed. Consequently the
permutation group of a countable discrete space is Polish; in particular this constructs the
infinite symmetric group on `ℕ` as a Polish group.

For a discrete carrier, finite pointwise stabilizers form a neighbourhood basis at the identity.
The inverse coordinate adds no open sets: continuity of a family of permutations is equivalent
to continuity of its forward evaluations. These facts supply the topology used in the logic
action on structures. Stabilizers are closed whenever the carrier is T₁.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, §9 (the infinite symmetric group).
-/

public section

open Set Filter Topology

namespace Equiv.Perm

variable {α X : Type*} [TopologicalSpace α]

/-- The topology on permutations of any topological space induced by recording the forward
and inverse functions in the product of pointwise-convergence function spaces. -/
instance instTopologicalSpace : TopologicalSpace (Equiv.Perm α) :=
  TopologicalSpace.induced (fun σ : Equiv.Perm α => ((σ : α → α), ⇑(σ⁻¹)))
    inferInstance

/-- A permutation and its inverse give an embedding into the product of function spaces. -/
theorem isEmbedding_prodMk_coe_coe_inv :
    IsEmbedding (fun σ : Equiv.Perm α => ((σ : α → α), ⇑(σ⁻¹))) :=
  ⟨⟨rfl⟩, fun _ _ h => Equiv.ext (congrFun (congrArg Prod.fst h))⟩

/-- Forward evaluation at a fixed point is continuous. -/
@[fun_prop]
theorem continuous_apply (a : α) : Continuous (fun σ : Equiv.Perm α => σ a) :=
  (_root_.continuous_apply a).comp isEmbedding_prodMk_coe_coe_inv.continuous.fst

/-- Inverse evaluation at a fixed point is continuous. -/
@[fun_prop]
theorem continuous_inv_apply (a : α) : Continuous (fun σ : Equiv.Perm α => σ⁻¹ a) :=
  (_root_.continuous_apply a).comp isEmbedding_prodMk_coe_coe_inv.continuous.snd

/-- Continuity into permutations can be checked on forward and inverse evaluations. -/
theorem continuous_iff [TopologicalSpace X] {f : X → Equiv.Perm α} :
    Continuous f ↔ (∀ a, Continuous fun x => f x a) ∧
      (∀ a, Continuous fun x => (f x)⁻¹ a) := by
  rw [isEmbedding_prodMk_coe_coe_inv.isInducing.continuous_iff]
  simp only [Function.comp_def, continuous_prodMk, continuous_pi_iff]

/-- Permutations of a Hausdorff space form a Hausdorff space in the induced topology. -/
instance instT2Space [T2Space α] : T2Space (Equiv.Perm α) :=
  isEmbedding_prodMk_coe_coe_inv.t2Space

variable [DiscreteTopology α]

/-- Joint evaluation of a permutation at a point is continuous for a discrete carrier. -/
@[fun_prop]
theorem continuous_eval : Continuous (fun p : Equiv.Perm α × α => p.1 p.2) :=
  continuous_prod_of_discrete_right.2 continuous_apply

/-- The natural action on the discrete carrier is continuous. -/
instance instContinuousSMul : ContinuousSMul (Equiv.Perm α) α :=
  ⟨continuous_eval⟩

/-- A family of permutations of a discrete space is continuous exactly when every
forward evaluation is continuous. -/
theorem continuous_iff_apply [TopologicalSpace X] {f : X → Equiv.Perm α} :
    Continuous f ↔ ∀ a, Continuous fun x => f x a := by
  rw [continuous_iff]
  refine and_iff_left_of_imp fun h a => continuous_discrete_rng.2 fun b => ?_
  convert (isOpen_discrete ({a} : Set α)).preimage (h b) using 1
  ext x
  exact (f x).symm_apply_eq.trans eq_comm

/-- Forward functions alone induce the pointwise topology; recording inverses adds no opens. -/
theorem isEmbedding_coe : IsEmbedding (fun σ : Equiv.Perm α => (σ : α → α)) := by
  refine ⟨⟨le_antisymm isEmbedding_prodMk_coe_coe_inv.continuous.fst.le_induced ?_⟩,
    fun _ _ h => Equiv.ext (congrFun h)⟩
  -- Compare the forward-induced topology with the forward/inverse-induced topology.
  -- In the former, each forward evaluation is continuous by construction;
  -- continuous_iff_apply then makes the identity into the latter continuous.
  have h : @Continuous (Equiv.Perm α) (Equiv.Perm α)
      (TopologicalSpace.induced (fun σ : Equiv.Perm α => (σ : α → α)) inferInstance)
      instTopologicalSpace id := by
    let : TopologicalSpace (Equiv.Perm α) :=
      TopologicalSpace.induced (fun σ : Equiv.Perm α => (σ : α → α)) inferInstance
    exact continuous_iff_apply.2 fun a =>
      (_root_.continuous_apply a).comp continuous_induced_dom
  simpa only [induced_id] using h.le_induced

/-- Permutations of a discrete space form a topological group. -/
instance instIsTopologicalGroup : IsTopologicalGroup (Equiv.Perm α) where
  continuous_mul := continuous_iff_apply.2 fun a => by
    simpa only [mul_apply, Function.comp_def] using
      continuous_eval.comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd))
  continuous_inv := continuous_iff_apply.2 continuous_inv_apply

omit [TopologicalSpace α] [DiscreteTopology α] in
/-- The image consists exactly of pairs of mutually inverse functions. -/
theorem range_prodMk_coe_coe_inv :
    Set.range (fun σ : Equiv.Perm α => ((σ : α → α), ⇑(σ⁻¹))) =
      {p | Function.LeftInverse p.2 p.1 ∧ Function.RightInverse p.2 p.1} := by
  ext p
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ.symm_apply_apply, σ.apply_symm_apply⟩
  · rintro ⟨hl, hr⟩
    exact ⟨⟨p.1, p.2, hl, hr⟩, rfl⟩

/-- Recording forward and inverse functions is a closed embedding. -/
theorem isClosedEmbedding_prodMk_coe_coe_inv :
    IsClosedEmbedding (fun σ : Equiv.Perm α => ((σ : α → α), ⇑(σ⁻¹))) := by
  refine ⟨isEmbedding_prodMk_coe_coe_inv, ?_⟩
  rw [range_prodMk_coe_coe_inv]
  have heval : Continuous (fun p : (α → α) × α => p.1 p.2) :=
    continuous_prod_of_discrete_right.2 _root_.continuous_apply
  have hclosed : IsClosed {p : (α → α) × (α → α) | ∀ a, p.2 (p.1 a) = a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_eq
      (heval.comp (continuous_snd.prodMk
        ((_root_.continuous_apply a).comp continuous_fst))) (continuous_const (y := a))
  exact hclosed.inter (hclosed.preimage continuous_swap)

/-- The permutation group of a countable discrete space is Polish. -/
instance instPolishSpace [Countable α] : PolishSpace (Equiv.Perm α) := by
  have : PolishSpace α := inferInstance
  have : PolishSpace (α → α) := inferInstance
  exact isClosedEmbedding_prodMk_coe_coe_inv.polishSpace

/-- Pointwise stabilizers of finite sets form a neighbourhood basis at the identity. -/
theorem hasBasis_nhds_one_fixingSubgroup :
    (𝓝 (1 : Equiv.Perm α)).HasBasis (fun s : Set α => s.Finite)
      (fun s => (fixingSubgroup (Equiv.Perm α) s : Set (Equiv.Perm α))) := by
  rw [isEmbedding_coe.isInducing.nhds_eq_comap, nhds_pi]
  simp only [nhds_discrete, Equiv.Perm.coe_one, id_eq]
  convert (Filter.hasBasis_pi_pure (fun a : α => a)).comap
    (fun σ : Equiv.Perm α => (σ : α → α)) using 1
  funext s
  ext σ
  simp [mem_fixingSubgroup_iff, Equiv.Perm.smul_def]

omit [DiscreteTopology α] in
/-- Every pointwise stabilizer of a T₁ space is closed. -/
theorem isClosed_fixingSubgroup [T1Space α] (s : Set α) :
    IsClosed (fixingSubgroup (Equiv.Perm α) s : Set (Equiv.Perm α)) := by
  convert (isClosed_biInter fun a (_ : a ∈ s) =>
    (isClosed_singleton (x := a)).preimage (continuous_apply a)) using 1
  ext σ
  simp [mem_fixingSubgroup_iff, Equiv.Perm.smul_def]

/-- Stabilizers of finite sets are open. -/
theorem isOpen_fixingSubgroup {s : Set α} (hs : s.Finite) :
    IsOpen (fixingSubgroup (Equiv.Perm α) s : Set (Equiv.Perm α)) := by
  convert (hs.isOpen_biInter fun a _ =>
    (isOpen_discrete ({a} : Set α)).preimage (continuous_apply a)) using 1
  ext σ
  simp [mem_fixingSubgroup_iff, Equiv.Perm.smul_def]

/-- The pointwise topology on permutations of a finite discrete space is discrete. -/
instance instDiscreteTopology [Finite α] : DiscreteTopology (Equiv.Perm α) :=
  isEmbedding_coe.discreteTopology

end Equiv.Perm
