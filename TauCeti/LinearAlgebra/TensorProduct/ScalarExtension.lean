/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar extensions of modules

A flat module embeds in its scalar extension along a faithful semiring algebra. The map
`m ↦ 1 ⊗ m` identifies it with the submodule of unit pure tensors, which is free whenever the
original module is free. For a module with a basis, this submodule is the span over the original
semiring of the base-changed basis.

The canonical identification `(E ⊗[K] L) ⊗[L] V ≃ E ⊗[K] V` is linear over `E`, although
`L` acts on the right component of the scalar-extended algebra. This identification compares
scalar extension of an underlying `K`-module with scalar extension of an `L`-module, and is used
when a construction over `L/K` is transported along `K → E`.

The construction uses Mathlib's `Algebra.TensorProduct.commRight`,
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, and `TensorProduct.comm`.

With `B` acting on the left factor instead, `TensorProduct.cancelBaseChangeLeft` is the
`R`-linear identification `(B ⊗[R] P) ⊗[B] N ≃ P ⊗[R] N` for an `R`-module `P`. Under it,
tensoring a `B`-linear map over `B` with the `B`-module `B ⊗[R] P` becomes tensoring the
underlying `R`-linear map with `P` (`TensorProduct.cancelBaseChangeLeft_lTensor`), so the two are
injective together (`LinearMap.injective_lTensor_iff_injective_lTensor_restrictScalars`). When
`P` is an `R`-algebra, the first is extension of scalars along `B → B ⊗[R] P`; for `P = κ(p)`,
this compares base change to the fibre ring `B ⊗[R] κ(p)` with base change to `κ(p)`.

## Main declarations

* `Module.Basis.range_mk_one_eq_span`: the unit pure tensors are the span over the original
  semiring of a base-changed basis.
* `TauCeti.TensorProduct.unitTmulEquiv`: a flat module is equivalent to its unit-tensor image
  under a faithful scalar extension.
* `TauCeti.TensorProduct.free_range_mk_one`: the unit-tensor image of a free module is free.
* `TensorProduct.cancelBaseChangeRight` and `TensorProduct.cancelBaseChangeLeft`: cancelling
  a scalar-extended algebra identifies two iterated scalar extensions.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (K L E V : Type*) [CommSemiring K] [CommSemiring L] [CommSemiring E]
  [Algebra K L] [Algebra K E] [AddCommMonoid V] [Module L V] [Module K V]
  [IsScalarTower K L V]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Cancelling the scalar-extended algebra identifies extension of an `L`-module with extension
of its underlying `K`-module. The map sends `(e ⊗ l) ⊗ v` to `e ⊗ (l • v)`. -/
def _root_.TensorProduct.cancelBaseChangeRight :
    ((E ⊗[K] L) ⊗[L] V) ≃ₗ[E] E ⊗[K] V := by
  let f := (TensorProduct.comm L (E ⊗[K] L) V).restrictScalars K
    ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl L V)
      (Algebra.TensorProduct.commRight K L E).symm.toLinearEquiv).restrictScalars K
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V E).restrictScalars K
    ≪≫ₗ TensorProduct.comm K V E
  refine { f.toAddEquiv with map_smul' := ?_ }
  intro c x
  -- Normalize the additive equivalence's `toFun` field before tensor induction.
  change f (c • x) = c • f x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul a v =>
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp [TensorProduct.add_tmul, smul_add, ha, hb]
    | tmul e l => simp [f, TensorProduct.smul_tmul']

/-- The cancellation equivalence acts by the `L`-scalar on the vector component. -/
@[simp]
theorem _root_.TensorProduct.cancelBaseChangeRight_tmul (e : E) (l : L) (v : V) :
    TensorProduct.cancelBaseChangeRight K L E V ((e ⊗ₜ[K] l) ⊗ₜ[L] v) =
      e ⊗ₜ[K] (l • v) := (rfl)

/-- The inverse cancellation inserts the unit of `L` in the scalar-extended algebra. -/
@[simp]
theorem _root_.TensorProduct.cancelBaseChangeRight_symm_tmul (e : E) (v : V) :
    (TensorProduct.cancelBaseChangeRight K L E V).symm (e ⊗ₜ[K] v) =
      (e ⊗ₜ[K] (1 : L)) ⊗ₜ[L] v := (rfl)

end TauCeti

namespace TensorProduct

variable (R B P : Type*) [CommSemiring R] [CommSemiring B] [Algebra R B]
  [AddCommMonoid P] [Module R P]

/-- Cancelling `B` on the left identifies the tensor product over `B` of the `B`-module
`B ⊗[R] P` with a `B`-module `N` with the tensor product over `R` of `P` and the underlying
`R`-module of `N`. The map sends `(b ⊗ p) ⊗ n` to `p ⊗ (b • n)`. -/
def cancelBaseChangeLeft (N : Type*) [AddCommMonoid N] [Module R N] [Module B N]
    [IsScalarTower R B N] : (B ⊗[R] P) ⊗[B] N ≃ₗ[R] P ⊗[R] N :=
  (TensorProduct.comm B (B ⊗[R] P) N).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R B B N P).restrictScalars R ≪≫ₗ
    TensorProduct.comm R N P

variable {N N' : Type*} [AddCommMonoid N] [Module R N] [Module B N] [IsScalarTower R B N]
  [AddCommMonoid N'] [Module R N'] [Module B N'] [IsScalarTower R B N']

/-- The left cancellation equivalence moves the `B`-scalar onto the module component. -/
@[simp]
theorem cancelBaseChangeLeft_tmul (b : B) (p : P) (n : N) :
    cancelBaseChangeLeft R B P N ((b ⊗ₜ[R] p) ⊗ₜ[B] n) = p ⊗ₜ[R] (b • n) := by
  simp [cancelBaseChangeLeft]

/-- The inverse left cancellation inserts the unit of `B` in the left factor of `B ⊗[R] P`. -/
@[simp]
theorem cancelBaseChangeLeft_symm_tmul (p : P) (n : N) :
    (cancelBaseChangeLeft R B P N).symm (p ⊗ₜ[R] n) = (1 ⊗ₜ[R] p) ⊗ₜ[B] n := by
  simp [LinearEquiv.symm_apply_eq]

variable {R B P}

/-- Through `cancelBaseChangeLeft`, tensoring a `B`-linear map `f` over `B` with `B ⊗[R] P` is
tensoring the underlying `R`-linear map of `f` with `P`. -/
theorem cancelBaseChangeLeft_lTensor (f : N →ₗ[B] N') (z : (B ⊗[R] P) ⊗[B] N) :
    cancelBaseChangeLeft R B P N' (f.lTensor (B ⊗[R] P) z) =
      (f.restrictScalars R).lTensor P (cancelBaseChangeLeft R B P N z) := by
  induction z with
  | tmul y n =>
    induction y with
    | tmul b p => simp
    | add x y hx hy => simp_all [add_tmul]
  | add x y hx hy => simp_all

namespace AlgebraTensorModule

/-- Tensor cancellation commutes with tensoring the underlying linear map on the right. -/
theorem cancelBaseChange_rTensor (f : N →ₗ[B] N') (z : N ⊗[B] (B ⊗[R] P)) :
    cancelBaseChange R B B N' P (f.rTensor (B ⊗[R] P) z) =
      (f.restrictScalars R).rTensor P (cancelBaseChange R B B N P z) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul n d =>
    induction d using TensorProduct.inductionOn with
    | add d e hd he => simp only [TensorProduct.tmul_add, map_add, hd, he]
    | tmul b p => simp

end AlgebraTensorModule

end TensorProduct

namespace LinearMap

open TensorProduct

variable {R B : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B] (P : Type*)
  [AddCommMonoid P] [Module R P] {N N' : Type*} [AddCommMonoid N] [Module R N] [Module B N]
  [IsScalarTower R B N] [AddCommMonoid N'] [Module R N'] [Module B N'] [IsScalarTower R B N']

/-- Tensoring a `B`-linear map over `B` with `B ⊗[R] P` gives an injective map exactly when
tensoring its underlying `R`-linear map with `P` does. -/
theorem injective_lTensor_iff_injective_lTensor_restrictScalars (f : N →ₗ[B] N') :
    Function.Injective (f.lTensor (B ⊗[R] P)) ↔
      Function.Injective ((f.restrictScalars R).lTensor P) := by
  have : ⇑((f.restrictScalars R).lTensor P) = cancelBaseChangeLeft R B P N' ∘
      f.lTensor (B ⊗[R] P) ∘ (cancelBaseChangeLeft R B P N).symm := by
    ext z
    simp [cancelBaseChangeLeft_lTensor]
  rw [this, EquivLike.comp_injective, EquivLike.injective_comp]

end LinearMap

namespace TauCeti.TensorProduct

open Module

universe u v w

variable {R : Type u} {K : Type v} {M : Type w}

section CommSemiring

variable [CommSemiring R] [Semiring K] [Algebra R K]
variable [AddCommMonoid M] [Module R M]

/-- The unit pure tensors are the `R`-span of the base change of any basis. -/
theorem _root_.Module.Basis.range_mk_one_eq_span {ι : Type*} (b : Basis ι R M) :
    LinearMap.range (TensorProduct.mk R K M 1) =
      Submodule.span R (Set.range (b.baseChange K)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span R)
    (congrArg Set.range (funext fun i ↦ (Basis.baseChange_apply K b i).symm))

variable [FaithfulSMul R K]

section Flat

variable [Module.Flat R M]

variable (R K M) in
/-- A flat module is canonically isomorphic to the module of unit pure tensors in its scalar
extension along a faithful algebra. -/
noncomputable def unitTmulEquiv : M ≃ₗ[R] LinearMap.range (TensorProduct.mk R K M 1) :=
  LinearEquiv.ofInjective _ (Module.Flat.tensorProduct_mk_injective R M K)

/-- The unit-tensor equivalence sends a vector to its unit pure tensor. This equation
characterizes the equivalence. -/
@[simp]
theorem coe_unitTmulEquiv_apply (m : M) :
    (unitTmulEquiv R K M m : K ⊗[R] M) = 1 ⊗ₜ[R] m := by
  rw [unitTmulEquiv, LinearEquiv.ofInjective_apply, TensorProduct.mk_apply]

/-- The inverse unit-tensor equivalence recovers a vector from its unit pure tensor. -/
@[simp]
theorem unitTmulEquiv_symm_tmul (m : M)
    (h : (1 : K) ⊗ₜ[R] m ∈ LinearMap.range (TensorProduct.mk R K M 1)) :
    (unitTmulEquiv R K M).symm ⟨1 ⊗ₜ[R] m, h⟩ = m := by
  apply (unitTmulEquiv R K M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (coe_unitTmulEquiv_apply m).symm

end Flat

/-- The module of unit pure tensors is free whenever the original module is free. -/
instance free_range_mk_one [Module.Free R M] :
    Module.Free R (LinearMap.range (TensorProduct.mk R K M 1)) :=
  Module.Free.of_equiv (unitTmulEquiv R K M)

end CommSemiring

end TauCeti.TensorProduct
