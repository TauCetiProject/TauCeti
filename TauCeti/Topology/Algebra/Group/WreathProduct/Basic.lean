/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Coordinate topology on permutation wreath products

The base has the product topology and the permutation group has the topology of pointwise
convergence. Relabeling coordinates continuously preserves this topology. When the base is a
topological group and the index type is discrete, this topology makes the wreath product a
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
      continuous_induced_rng.mp hf
    exact ⟨fun i => (continuous_apply i).comp h.fst,
      fun i => (continuous_apply i).comp h.snd⟩
  · rintro ⟨hl, hr⟩
    exact continuous_induced_rng.mpr ((continuous_pi hl).prodMk (continuous_pi hr))

/-- Evaluation of a base coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_left (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.left i) :=
  (continuous_iff.mp continuous_id).1 i

/-- Evaluation of a permutation coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_right (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.right i) :=
  (continuous_iff.mp continuous_id).2 i

/-- Evaluation of the inverse permutation coordinate is continuous when the index is discrete. -/
theorem continuous_right_inv [DiscreteTopology ι] (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.right⁻¹ i) := by
  rw [continuous_discrete_rng]
  intro j
  have h : (fun w : WreathProduct D ι => w.right⁻¹ i) ⁻¹' {j} =
      (fun w : WreathProduct D ι => w.right j) ⁻¹' {i} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    simpa only [Equiv.Perm.coe_inv] using
      (Equiv.symm_apply_eq (e := w.right) (x := i) (y := j)).trans eq_comm
  rw [h]
  exact (isOpen_discrete _).preimage (continuous_right j)

/-- For a discrete index type, the coordinate topology makes the permutation wreath
product a topological group. -/
instance instIsTopologicalGroup [IsTopologicalGroup D] [DiscreteTopology ι] :
    IsTopologicalGroup (WreathProduct D ι) := by
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_iff.mpr
    constructor
    · intro i
      have hi : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.1.right⁻¹ i) := (continuous_right_inv i).comp continuous_fst
      have heval : Continuous (fun p :
          (WreathProduct D ι × WreathProduct D ι) × ι => p.1.2.left p.2) :=
        continuous_prod_of_discrete_right.mpr fun j => by
          simpa only [Function.comp_def] using (continuous_left j).comp
            (continuous_snd : Continuous (fun p : WreathProduct D ι × WreathProduct D ι => p.2))
      have hb : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.2.left (p.1.right⁻¹ i)) :=
        heval.comp (continuous_id.prodMk hi)
      convert ((continuous_left i).comp continuous_fst).mul hb using 1
      ext p
      exact (mul_left p.1 p.2 i).symm
    · intro i
      have hi : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.2.right i) := (continuous_right i).comp continuous_snd
      have heval : Continuous (fun p :
          (WreathProduct D ι × WreathProduct D ι) × ι => p.1.1.right p.2) :=
        continuous_prod_of_discrete_right.mpr fun j => by
          simpa only [Function.comp_def] using (continuous_right j).comp
            (continuous_fst : Continuous (fun p : WreathProduct D ι × WreathProduct D ι => p.1))
      have hc : Continuous (fun p : WreathProduct D ι × WreathProduct D ι =>
          p.1.right (p.2.right i)) :=
        heval.comp (continuous_id.prodMk hi)
      convert hc using 1
      ext p
      simp only [SemidirectProduct.mul_right, Equiv.Perm.mul_apply]
  · apply continuous_iff.mpr
    constructor
    · intro i
      have hi : Continuous (fun w : WreathProduct D ι => w.right i) := continuous_right i
      have heval : Continuous (fun p : WreathProduct D ι × ι => p.1.left p.2) :=
        continuous_prod_of_discrete_right.mpr fun j => by
          simpa using (continuous_left j)
      have hb : Continuous (fun w : WreathProduct D ι => (w.left (w.right i))⁻¹) :=
        (heval.comp (continuous_id.prodMk hi)).inv
      convert hb using 1
      ext w
      rw [SemidirectProduct.inv_left]
      -- The permutation acts on functions by precomposition with its inverse.
      change (w.left⁻¹) ((w.right⁻¹)⁻¹ i) = (w.left (w.right i))⁻¹
      simp
    · intro i
      have hi : Continuous (fun w : WreathProduct D ι => w.right⁻¹ i) :=
        continuous_right_inv i
      convert hi using 1

/-- Relabeling a wreath product is continuous when the relabeling of its index type is
continuous. -/
theorem continuous_congr (e : ι ≃ κ) (he : Continuous e) :
    Continuous (congr (D := D) e) := by
  have hcoords : Continuous (fun w : WreathProduct D ι =>
      (w.left, (w.right : ι → ι))) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  exact (continuous_pi fun i => by
    simpa only [congr_left, Function.comp_def] using
      (continuous_apply (e.symm i)).comp hcoords.fst).prodMk
      (continuous_pi fun i => by
        simpa only [congr_right, Equiv.permCongr_apply, Function.comp_def] using
          he.comp ((continuous_apply (e.symm i)).comp hcoords.snd))

end TauCeti.WreathProduct
