/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Fixed vectors of coordinate permutations

Functions on the cycle quotient identify linearly with the fixed submodule of
precomposition by a permutation. The underlying bijection is the existing
invariant-colouring equivalence; no enumeration of cycles is needed. The orbit basis
requires only finitely many cycles, even when their elements form an infinite type.
-/

public noncomputable section

open Equiv

namespace Equiv.Perm

open LinearEquiv

variable {R M I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Functions on permutation cycles are precisely the fixed vectors of precomposition. -/
def permutationFixedEquiv (σ : Perm I) :
    (Quotient (Perm.SameCycle.setoid σ) → M) ≃ₗ[R]
      (funCongrLeft R M σ).toLinearMap.fixedSubmodule where
  toFun a := ⟨(TauCeti.invariantColouringEquiv σ a).val, by
    apply LinearMap.mem_fixedSubmodule_iff.mpr
    funext i
    simpa only [coe_coe, funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      using congrFun (TauCeti.invariantColouringEquiv σ a).property i⟩
  invFun v := (TauCeti.invariantColouringEquiv σ).symm ⟨v.val, by
    funext i
    simpa only [coe_coe, funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      using congrFun (LinearMap.mem_fixedSubmodule_iff.mp v.property) i⟩
  left_inv a := (TauCeti.invariantColouringEquiv σ).symm_apply_apply a
  right_inv v := by
    apply Subtype.ext
    exact congrArg Subtype.val ((TauCeti.invariantColouringEquiv σ).apply_symm_apply _)
  map_add' a b := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_add, Pi.add_apply, TauCeti.invariantColouringEquiv_apply_coe]
  map_smul' r a := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_smul, Pi.smul_apply, TauCeti.invariantColouringEquiv_apply_coe,
      RingHom.id_apply]

/-- The fixed-vector equivalence reads the coordinate of the containing cycle. -/
@[simp]
theorem permutationFixedEquiv_apply (σ : Perm I)
    (a : Quotient (Perm.SameCycle.setoid σ) → M) (i : I) :
    (permutationFixedEquiv (R := R) (M := M) σ a).val i = a (Quotient.mk _ i) :=
  TauCeti.invariantColouringEquiv_apply_coe σ a i

/-- Inverse coordinates recover every ambient coordinate of a fixed vector. -/
@[simp]
theorem permutationFixedEquiv_symm_apply (σ : Perm I)
    (v : (funCongrLeft R M σ).toLinearMap.fixedSubmodule) (i : I) :
    (permutationFixedEquiv (R := R) (M := M) σ).symm v (Quotient.mk _ i) = v.val i :=
  TauCeti.invariantColouringEquiv_symm_apply σ _ i

/-- The orbit indicator vectors form a basis of the fixed submodule. -/
def permutationFixedBasis (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))] :
    Module.Basis (Quotient (Perm.SameCycle.setoid σ)) R
      (funCongrLeft R R σ).toLinearMap.fixedSubmodule :=
  Module.Basis.ofEquivFun (permutationFixedEquiv (R := R) (M := R) σ).symm

/-- A fixed vector's orbit coordinate is its value at any member of that orbit. -/
@[simp]
theorem permutationFixedBasis_repr (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))]
    (v : (funCongrLeft R R σ).toLinearMap.fixedSubmodule) (i : I) :
    (permutationFixedBasis (R := R) σ).repr v (Quotient.mk _ i) = v.val i := by
  rw [permutationFixedBasis, Module.Basis.ofEquivFun_repr_apply]
  exact permutationFixedEquiv_symm_apply σ v i

/-- An orbit basis vector is the indicator of its cycle, which may be infinite. -/
@[simp]
theorem permutationFixedBasis_apply (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))]
    [DecidableEq (Quotient (Perm.SameCycle.setoid σ))]
    (c : Quotient (Perm.SameCycle.setoid σ)) (i : I) :
    (permutationFixedBasis (R := R) σ c).val i =
      if Quotient.mk _ i = c then 1 else 0 := by
  have h := permutationFixedBasis_repr σ (permutationFixedBasis (R := R) σ c) i
  simpa only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h.symm

/-- Each basis vector is the literal sum of coordinate vectors in its cycle. -/
theorem permutationFixedBasis_eq_sum [Fintype I] [DecidableEq I] (σ : Perm I)
    [DecidableEq (Quotient (Perm.SameCycle.setoid σ))]
    (c : Quotient (Perm.SameCycle.setoid σ)) :
    (permutationFixedBasis (R := R) σ c).val =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk _ i = c), Pi.single i (1 : R) := by
  ext i
  rw [permutationFixedBasis_apply]
  simp [Finset.sum_apply, Pi.single_apply, eq_comm]

/-- Read one chosen coordinate per cycle, then extend it constantly along that cycle.
A section of the quotient map makes this a retraction; the map depends on that section. -/
def permutationFixedProjection (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I) :
    (I → M) →ₗ[R] (funCongrLeft R M σ).toLinearMap.fixedSubmodule :=
  (permutationFixedEquiv (R := R) (M := M) σ).toLinearMap.comp (LinearMap.funLeft R M r)

/-- The chosen representative determines every coordinate of the projection. -/
@[simp]
theorem permutationFixedProjection_apply (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I) (v : I → M) (i : I) :
    (permutationFixedProjection (R := R) σ r v).val i =
      v (r (Quotient.mk _ i)) := by
  simp only [permutationFixedProjection, LinearMap.comp_apply, coe_coe,
    permutationFixedEquiv_apply, LinearMap.funLeft_apply]

/-- A section-based projection fixes every vector in the fixed submodule. -/
@[simp]
theorem permutationFixedProjection_fixed (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I)
    (hr : Function.RightInverse r (Quotient.mk (Perm.SameCycle.setoid σ)))
    (v : (funCongrLeft R M σ).toLinearMap.fixedSubmodule) :
    permutationFixedProjection (R := R) σ r v.val = v := by
  apply Subtype.ext
  funext i
  rw [permutationFixedProjection_apply,
    ← permutationFixedEquiv_symm_apply σ v (r (Quotient.mk _ i)), hr,
    permutationFixedEquiv_symm_apply]

/-- The section-based projection is a linear retraction of the actual fixed-submodule inclusion. -/
theorem permutationFixedProjection_comp_subtype (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I)
    (hr : Function.RightInverse r (Quotient.mk (Perm.SameCycle.setoid σ))) :
    (permutationFixedProjection (R := R) (M := M) σ r).comp
      (funCongrLeft R M σ).toLinearMap.fixedSubmodule.subtype = LinearMap.id := by
  ext v i
  exact congrFun (congrArg Subtype.val (permutationFixedProjection_fixed σ r hr v)) i

end Equiv.Perm
