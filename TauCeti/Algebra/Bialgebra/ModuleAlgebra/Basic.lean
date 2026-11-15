/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.BigOperators

/-!
# Left module algebras

A left module algebra over a bialgebra `H` is an algebra `A` with an `R`-linear
`H`-action for which multiplication and the unit are equivariant. The action is
bundled as an algebra homomorphism into `Module.End R A`; in particular it is not
an action by algebra endomorphisms. The product law uses comultiplication and is
independent of a representation of the coproduct.

This file provides the product law in Sweedler form for any `Coalgebra.Repr`,
restriction along bialgebra homomorphisms, the trivial action, the invariant
subalgebra, and equivariant algebra maps. These are the action data used in the
construction of smash products.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

variable (R H A : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A]

/-- A left module algebra over a bialgebra. The action on a product is obtained
by applying the two legs of the coproduct, then multiplying in `A`. -/
structure LeftModuleAlgebra where
  /-- The unital, associative, bilinear left action. -/
  action : H →ₐ[R] Module.End R A
  /-- The unit transforms by the counit. -/
  action_one : ∀ h, action h 1 = counit (R := R) h • (1 : A)
  /-- Multiplication is equivariant for the diagonal action. -/
  action_mul : ∀ h a b, action h (a * b) =
    LinearMap.mul' R A
      (((Module.endTensorEndAlgHom (R := R) (S := R) (A := R)).comp
        (Algebra.TensorProduct.map action action)).comp
          (Bialgebra.comulAlgHom R H) h (a ⊗ₜ[R] b))

namespace LeftModuleAlgebra

variable {R H A}

/-- Module algebra structures are determined by their actions. -/
@[ext]
theorem ext {μ ν : LeftModuleAlgebra R H A}
    (h : ∀ x a, μ.action x a = ν.action x a) : μ = ν := by
  have he : μ.action = ν.action := by ext x a; exact h x a
  cases μ
  cases ν
  cases he
  rfl

attribute [simp] action_one

/-- The product equation in any finite representation of the coproduct. -/
theorem action_mul_eq_sum (μ : LeftModuleAlgebra R H A) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) (a b : A) :
    μ.action h (a * b) = ∑ i ∈ r.index, μ.action (r.left i) a * μ.action (r.right i) b := by
  rw [μ.action_mul]
  simp [AlgHom.comp_apply, ← r.eq, Module.endTensorEndAlgHom_apply]

/-- The trivial module algebra action factors through the counit. -/
def trivial : LeftModuleAlgebra R H A where
  action := (Algebra.lsmul R R A).comp (Bialgebra.counitAlgHom R H)
  action_one _ := rfl
  action_mul h a b := by
    have hc := congrArg (counit (R := R)) (sum_counit_smul (ℛ R h))
    simpa [AlgHom.comp_apply, ← (ℛ R h).eq, Module.endTensorEndAlgHom_apply,
      smul_mul_smul_comm, smul_smul, mul_comm, ← Finset.sum_smul, map_sum] using
      (congrArg (fun c : R => c • (a * b)) hc).symm

@[simp]
theorem trivial_action (h : H) (a : A) :
    (trivial (R := R) (H := H) (A := A)).action h a = counit (R := R) h • a :=
  (rfl)

variable {K : Type*} [Semiring K] [Bialgebra R K]

/-- Restrict a module algebra action along a bialgebra homomorphism. -/
def restrict (μ : LeftModuleAlgebra R H A) (f : K →ₐc[R] H) :
    LeftModuleAlgebra R K A where
  action := μ.action.comp f.toAlgHom
  action_one h := by simp
  action_mul h a b := by
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
    rw [μ.action_mul]
    simp only [Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
    have hc := DFunLike.congr_fun f.map_comp_comulAlgHom h
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom] at hc
    rw [hc]

@[simp]
theorem restrict_action (μ : LeftModuleAlgebra R H A) (f : K →ₐc[R] H) (h : K) (a : A) :
    (μ.restrict f).action h a = μ.action (f h) a :=
  (rfl)

/-- Restriction preserves the trivial module algebra action. -/
@[simp]
theorem restrict_trivial (f : K →ₐc[R] H) :
    (trivial (R := R) (H := H) (A := A)).restrict f = trivial := by
  ext
  simp [CoalgHomClass.counit_comp_apply]

@[simp]
theorem restrict_id (μ : LeftModuleAlgebra R H A) : μ.restrict (BialgHom.id R H) = μ := by
  ext
  rfl

/-- Iterated restriction agrees with restriction along the composite. -/
@[simp]
theorem restrict_restrict {L : Type*} [Semiring L] [Bialgebra R L]
    (μ : LeftModuleAlgebra R H A) (f : K →ₐc[R] H) (g : L →ₐc[R] K) :
    (μ.restrict f).restrict g = μ.restrict (f.comp g) := by
  ext
  rfl

/-- The invariant subalgebra consists of the elements on which `H` acts through
its counit, not the elements fixed by every element of the underlying monoid. -/
def invariants (μ : LeftModuleAlgebra R H A) : Subalgebra R A where
  carrier := {a | ∀ h, μ.action h a = counit (R := R) h • a}
  zero_mem' := by simp
  add_mem' ha hb h := by simp [map_add, ha h, hb h, smul_add]
  one_mem' := μ.action_one
  mul_mem' {a b} ha hb h := by
    rw [μ.action_mul_eq_sum (ℛ R h)]
    simp only [ha _, hb _, smul_mul_smul_comm, ← Finset.sum_smul]
    have hc := congrArg (counit (R := R)) (sum_counit_smul (ℛ R h))
    simpa [map_sum] using congrArg (fun c : R => c • (a * b)) hc
  algebraMap_mem' r h := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, μ.action_one, smul_comm]

@[simp]
theorem mem_invariants_iff (μ : LeftModuleAlgebra R H A) (a : A) :
    a ∈ μ.invariants ↔ ∀ h, μ.action h a = counit (R := R) h • a :=
  Iff.rfl

@[simp]
theorem invariants_trivial :
    (trivial (R := R) (H := H) (A := A)).invariants = ⊤ := by
  ext
  simp

/-- Restriction can only enlarge the invariant subalgebra. -/
theorem invariants_le_invariants_restrict (μ : LeftModuleAlgebra R H A) (f : K →ₐc[R] H) :
    μ.invariants ≤ (μ.restrict f).invariants := by
  intro a ha h
  simpa using ha (f h)

/-- Surjective restriction does not change the invariant subalgebra. -/
theorem invariants_restrict_eq (μ : LeftModuleAlgebra R H A) (f : K →ₐc[R] H)
    (hf : Function.Surjective f) : (μ.restrict f).invariants = μ.invariants := by
  apply le_antisymm ?_ (μ.invariants_le_invariants_restrict f)
  intro a ha h
  obtain ⟨k, rfl⟩ := hf h
  simpa using ha k

variable {B : Type*} [Semiring B] [Algebra R B]

/-- An equivariant algebra homomorphism between left module algebras. -/
structure Hom (μ : LeftModuleAlgebra R H A) (ν : LeftModuleAlgebra R H B)
    extends A →ₐ[R] B where
  /-- The algebra map commutes with the bialgebra action. -/
  map_action' : ∀ h a, toAlgHom (μ.action h a) = ν.action h (toAlgHom a)

namespace Hom

variable {μ : LeftModuleAlgebra R H A} {ν : LeftModuleAlgebra R H B}

instance : FunLike (Hom μ ν) A B where
  coe f := f.toAlgHom
  coe_injective f g h := by
    have he : f.toAlgHom = g.toAlgHom := DFunLike.coe_injective h
    cases f
    cases g
    cases he
    rfl

/-- Equivariant algebra maps are determined by their values. -/
@[ext]
theorem ext {f g : Hom μ ν} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

instance : AlgHomClass (Hom μ ν) R A B where
  map_add f := f.toAlgHom.map_add
  map_zero f := f.toAlgHom.map_zero
  map_mul f := f.toAlgHom.map_mul
  map_one f := f.toAlgHom.map_one
  commutes f := f.toAlgHom.commutes

@[simp]
theorem coe_toAlgHom (f : Hom μ ν) : ⇑f.toAlgHom = f :=
  (rfl)

@[simp]
theorem coe_mk (φ : A →ₐ[R] B) (hφ) : ⇑(⟨φ, hφ⟩ : Hom μ ν) = φ :=
  (rfl)

/-- An equivariant algebra map commutes with the bialgebra action. -/
@[simp]
theorem map_action (f : Hom μ ν) (h : H) (a : A) :
    f (μ.action h a) = ν.action h (f a) := by
  simpa only [coe_toAlgHom] using f.map_action' h a

/-- The identity equivariant algebra map. -/
def id (μ : LeftModuleAlgebra R H A) : Hom μ μ where
  toAlgHom := AlgHom.id R A
  map_action' _ _ := rfl

/-- Compose equivariant algebra maps. -/
def comp {C : Type*} [Semiring C] [Algebra R C] {ξ : LeftModuleAlgebra R H C}
    (g : Hom ν ξ) (f : Hom μ ν) : Hom μ ξ where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  map_action' h a := by simp

@[simp]
theorem id_apply (μ : LeftModuleAlgebra R H A) (a : A) : id μ a = a :=
  (rfl)

@[simp]
theorem comp_apply {C : Type*} [Semiring C] [Algebra R C] {ξ : LeftModuleAlgebra R H C}
    (g : Hom ν ξ) (f : Hom μ ν) (a : A) : g.comp f a = g (f a) :=
  (rfl)

@[simp]
theorem id_comp (f : Hom μ ν) : (id ν).comp f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : Hom μ ν) : f.comp (id μ) = f := by
  ext
  rfl

/-- Composition of equivariant algebra maps is associative. -/
theorem comp_assoc {C D : Type*} [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
    {ξ : LeftModuleAlgebra R H C} {ζ : LeftModuleAlgebra R H D}
    (h : Hom ξ ζ) (g : Hom ν ξ) (f : Hom μ ν) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

/-- An equivariant algebra map sends invariants to invariants. -/
theorem map_mem_invariants (f : Hom μ ν) {a : A} (ha : a ∈ μ.invariants) :
    f a ∈ ν.invariants := by
  intro h
  rw [← f.map_action, ha h, map_smul]

/-- Restrict an equivariant algebra map to the invariant subalgebras. -/
def mapInvariants (f : Hom μ ν) : μ.invariants →ₐ[R] ν.invariants :=
  (f.toAlgHom.comp μ.invariants.val).codRestrict ν.invariants fun a =>
    f.map_mem_invariants a.property

@[simp]
theorem coe_mapInvariants (f : Hom μ ν) (a : μ.invariants) :
    (f.mapInvariants a : B) = f (a : A) :=
  (rfl)

@[simp]
theorem mapInvariants_id (μ : LeftModuleAlgebra R H A) :
    (id μ).mapInvariants = AlgHom.id R μ.invariants := by
  ext
  rfl

@[simp]
theorem mapInvariants_comp {C : Type*} [Semiring C] [Algebra R C]
    {ξ : LeftModuleAlgebra R H C} (g : Hom ν ξ) (f : Hom μ ν) :
    (g.comp f).mapInvariants = g.mapInvariants.comp f.mapInvariants := by
  ext
  rfl

end Hom
end LeftModuleAlgebra
end TauCeti
