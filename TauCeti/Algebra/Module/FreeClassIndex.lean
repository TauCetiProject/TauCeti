/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.Index
import TauCeti.Algebra.Module.LinearMap.Defs

/-!
# Least free indices of modules

The least free index of a module is the least positive finite additive index of an injective
map from a free module of the specified rank. It is infinite when no such map exists. This
construction only uses the module and its underlying additive group, independently of orders
and lattices.

`Module.freeClassIndex_def` gives its infimum formula, while
`Module.freeClassIndex_le_natCast_iff` characterizes finite bounds by embeddings.
`Module.freeClassIndex_equiv` transports the index across semilinear equivalences.
-/

public section

namespace Module

variable (R : Type*) [Ring R] (e : ℕ) (M : Type*) [AddCommGroup M] [Module R M]

/-- The least positive finite additive index of a free submodule of rank `e`, or infinity if
there is no such free submodule. -/
noncomputable def freeClassIndex : ℕ∞ :=
  ⨅ f : {f : (Fin e → R) →ₗ[R] M //
    Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0},
    ((LinearMap.range f.val).toAddSubgroup.index : ℕ∞)

/-- The least free index is the infimum of the positive finite additive indices of injective
maps from the standard free module. -/
theorem freeClassIndex_def : freeClassIndex R e M =
    ⨅ f : {f : (Fin e → R) →ₗ[R] M //
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0},
      ((LinearMap.range f.val).toAddSubgroup.index : ℕ∞) := by
  rfl

variable {R e M}

/-- A finite bound for the least free index is equivalent to an embedding satisfying that bound. -/
theorem freeClassIndex_le_natCast_iff (n : ℕ) : freeClassIndex R e M ≤ n ↔
    ∃ f : (Fin e → R) →ₗ[R] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      (LinearMap.range f).toAddSubgroup.index ≤ n := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top n), freeClassIndex_def, iInf_lt_iff]
  simp only [ENat.lt_add_one_iff (ENat.natCast_ne_top n), ENat.natCast_le_natCast]
  exact ⟨fun ⟨f, h⟩ => ⟨f.val, f.property.1, f.property.2, h⟩,
    fun ⟨f, hf, hi, h⟩ => ⟨⟨f, hf, hi⟩, h⟩⟩

/-- An injective map of positive finite additive index bounds the least free index. -/
theorem freeClassIndex_le (f : (Fin e → R) →ₗ[R] M) (hf : Function.Injective f)
    (hi : (LinearMap.range f).toAddSubgroup.index ≠ 0) :
    freeClassIndex R e M ≤ (LinearMap.range f).toAddSubgroup.index :=
  (freeClassIndex_le_natCast_iff _).2 ⟨f, hf, hi, le_rfl⟩

/-- Every least free index is at least one, including when no embedding exists. -/
theorem one_le_freeClassIndex : 1 ≤ freeClassIndex R e M := by
  rw [freeClassIndex_def]
  refine le_iInf fun f => ?_
  exact_mod_cast Nat.one_le_iff_ne_zero.2 f.property.2

/-- Whenever an embedding of positive finite index exists, the least index is attained. -/
theorem freeClassIndex_exists_eq
    (h : ∃ f : (Fin e → R) →ₗ[R] M,
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0) :
    ∃ f : (Fin e → R) →ₗ[R] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      ((LinearMap.range f).toAddSubgroup.index : ℕ∞) = freeClassIndex R e M := by
  have : Nonempty {f : (Fin e → R) →ₗ[R] M //
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0} :=
    ⟨⟨h.choose, h.choose_spec⟩⟩
  obtain ⟨f, hf⟩ := ENat.exists_eq_iInf (fun f : {f : (Fin e → R) →ₗ[R] M //
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0} =>
    ((LinearMap.range f.val).toAddSubgroup.index : ℕ∞))
  exact ⟨f.val, f.property.1, f.property.2, hf.trans (freeClassIndex_def R e M).symm⟩

private theorem freeClassIndex_le_semilinearEquiv {S : Type*} [Ring S] {N : Type*}
    [AddCommGroup N] [Module S N] {σ : R →+* S} {τ : S →+* R}
    [RingHomInvPair σ τ] [RingHomInvPair τ σ] (a : M ≃ₛₗ[σ] N) :
    freeClassIndex S e N ≤ freeClassIndex R e M := by
  conv_rhs => rw [freeClassIndex_def]
  refine le_iInf fun f => ?_
  let c : (Fin e → S) ≃ₛₗ[τ] (Fin e → R) :=
    { toFun := fun x i => τ (x i)
      invFun := fun x i => σ (x i)
      left_inv := fun x => funext fun i => RingHomInvPair.comp_apply_eq₂
      right_inv := fun x => funext fun i => RingHomInvPair.comp_apply_eq
      map_add' := fun x y => funext fun i => τ.map_add _ _
      map_smul' := fun r x => funext fun i => τ.map_mul _ _ }
  let g : (Fin e → S) →ₗ[S] N := a.toLinearMap.comp (f.val.comp c.toLinearMap)
  have hr : g.toAddMonoidHom.range = f.val.toAddMonoidHom.range.map a.toAddMonoidHom := by
    dsimp only [g]
    rw [LinearMap.toAddMonoidHom_comp, LinearMap.toAddMonoidHom_comp]
    rw [AddMonoidHom.range_comp, AddMonoidHom.range_comp]
    rw [AddMonoidHom.range_eq_top.mpr c.surjective, AddSubgroup.map_top]
  have hi : (LinearMap.range g).toAddSubgroup.index =
      (LinearMap.range f.val).toAddSubgroup.index := by
    rw [LinearMap.range_toAddSubgroup, LinearMap.range_toAddSubgroup, hr]
    exact AddSubgroup.index_map_equiv _ a.toAddEquiv
  simpa only [hi] using freeClassIndex_le g
    (a.injective.comp (f.property.1.comp c.injective)) (hi ▸ f.property.2)

/-- A semilinear equivalence over a ring equivalence preserves the least free index. -/
theorem freeClassIndex_equiv {S : Type*} [Ring S] {N : Type*}
    [AddCommGroup N] [Module S N] {σ : R →+* S} {τ : S →+* R}
    [RingHomInvPair σ τ] [RingHomInvPair τ σ] (a : M ≃ₛₗ[σ] N) :
    freeClassIndex R e M = freeClassIndex S e N :=
  le_antisymm (freeClassIndex_le_semilinearEquiv a.symm)
    (freeClassIndex_le_semilinearEquiv a)

/-- A free module has least free index one in its own rank. -/
@[simp]
theorem freeClassIndex_pi : freeClassIndex R e (Fin e → R) = 1 := by
  apply le_antisymm _ one_le_freeClassIndex
  simpa using freeClassIndex_le (LinearMap.id : (Fin e → R) →ₗ[R] (Fin e → R))
    Function.injective_id (by simp)

/-- A zero-rank free module has index one in a trivial module. -/
@[simp]
theorem freeClassIndex_zero [Subsingleton M] : freeClassIndex R 0 M = 1 := by
  apply le_antisymm _ one_le_freeClassIndex
  let f : (Fin 0 → R) →ₗ[R] M := 0
  have hf : Function.Injective f := Function.injective_of_subsingleton _
  have hr : LinearMap.range f = ⊤ := Subsingleton.elim _ _
  simpa only [hr, Submodule.top_toAddSubgroup, AddSubgroup.index_top, Nat.cast_one] using
    freeClassIndex_le f hf (by simp [hr])

end Module
