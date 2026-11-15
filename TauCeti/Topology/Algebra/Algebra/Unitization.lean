/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The product topology on a forced unitization

The forced unitization has the product topology on its scalar and algebra components.
Its addition, multiplication and scalar action are continuous whenever the corresponding
operations on the factors are. In particular this supplies unitizations of locally convex
algebras without requiring a norm. The scalar inclusion and augmentation are continuous;
they are the maps used to define relative continuous cochains.
-/

public section

namespace Unitization

variable {R A : Type*}

/-- The product topology on the scalar and algebra components of a forced unitization. -/
instance instTopologicalSpace [TopologicalSpace R] [TopologicalSpace A] :
    TopologicalSpace (Unitization R A) :=
  TopologicalSpace.induced toProd inferInstance

/-- The unitization is homeomorphic, as a space, to the product of its two components. -/
def homeomorphProd [TopologicalSpace R] [TopologicalSpace A] :
    Unitization R A ≃ₜ R × A :=
  { equiv with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := continuous_induced_rng.2 continuous_id }

@[simp]
theorem homeomorphProd_apply [TopologicalSpace R] [TopologicalSpace A]
    (x : Unitization R A) : homeomorphProd x = x.toProd := (rfl)

@[simp]
theorem homeomorphProd_symm_apply [TopologicalSpace R] [TopologicalSpace A] (x : R × A) :
    homeomorphProd.symm x = Unitization.mk x := (rfl)

@[fun_prop]
theorem continuous_fst_prod [TopologicalSpace R] [TopologicalSpace A] :
    Continuous (fun x : Unitization R A ↦ x.fst) :=
  _root_.continuous_fst.comp homeomorphProd.continuous

@[fun_prop]
theorem continuous_snd_prod [TopologicalSpace R] [TopologicalSpace A] :
    Continuous (fun x : Unitization R A ↦ x.snd) :=
  _root_.continuous_snd.comp homeomorphProd.continuous

/-- Continuity into a unitization is equivalent to continuity of both components. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] [TopologicalSpace R]
    [TopologicalSpace A] {f : X → Unitization R A} :
    Continuous f ↔ Continuous (fun x ↦ (f x).fst) ∧ Continuous (fun x ↦ (f x).snd) := by
  exact homeomorphProd.isInducing.continuous_iff.trans continuous_prodMk

instance [AddCommGroup R] [AddCommGroup A] [TopologicalSpace R] [TopologicalSpace A]
    [IsTopologicalAddGroup R] [IsTopologicalAddGroup A] :
    IsTopologicalAddGroup (Unitization R A) :=
  homeomorphProd.isInducing.isTopologicalAddGroup (addEquiv R A)

instance [Mul R] [Add A] [Mul A] [SMul R A] [TopologicalSpace R]
    [TopologicalSpace A] [ContinuousMul R] [ContinuousAdd A] [ContinuousMul A]
    [ContinuousSMul R A] : ContinuousMul (Unitization R A) where
  continuous_mul := continuous_iff.2 ⟨by simp only [fst_mul]; fun_prop,
    by simp only [snd_mul]; fun_prop⟩

instance [Semiring R] [AddCommMonoid A] [Module R A] [TopologicalSpace R]
    [TopologicalSpace A] [ContinuousSMul R R] [ContinuousSMul R A] :
    ContinuousSMul R (Unitization R A) :=
  continuousSMul_induced (linearEquiv R R A)

@[fun_prop]
theorem continuous_inl_prod [Zero A] [TopologicalSpace R] [TopologicalSpace A] :
    Continuous (inl : R → Unitization R A) :=
  continuous_iff.2 ⟨continuous_id, continuous_const⟩

/-- The scalar algebra map into the product-topologized unitization is continuous,
even without continuity of the scalar action on the algebra. -/
@[fun_prop]
theorem continuous_algebraMap_prod [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace R] [TopologicalSpace A] :
    Continuous (algebraMap R (Unitization R A)) := by
  rw [algebraMap_eq_inl]
  exact continuous_inl_prod

@[fun_prop]
theorem continuous_inr_prod [Zero R] [TopologicalSpace R] [TopologicalSpace A] :
    Continuous (inr : A → Unitization R A) :=
  continuous_iff.2 ⟨continuous_const, continuous_id⟩

end Unitization
