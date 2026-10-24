/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Coproduct actions on tensor products of modules

For a bialgebra `H` over a commutative semiring `R`, its coproduct acts on the tensor product
of two `H`-modules. `BialgebraModule.Tensor` is a type synonym of the native `R`-tensor
product, with this coproduct action. A synonym is necessary because the native tensor
product's left-factor scalar action would otherwise compete with the coproduct action.
The original factor `R`-module structures are retained; `tensorEquiv` identifies the base action
with the native tensor action.

`tensorEquiv` identifies the underlying `R`-module with the native tensor product; `tmul`
constructs pure tensors. `tensorMap` tensors native `H`-linear intertwiners.

The action is assembled from Mathlib's `Algebra.lsmul`, `Algebra.TensorProduct.map`, and
`Module.endTensorEndAlgHom`, by restriction along `Bialgebra.comulAlgHom`.
-/

public section

open scoped TensorProduct

namespace TauCeti.BialgebraModule

/-- The tensor product over `R`, with a separate carrier for the coproduct action of `H`.

The synonym separates that action from the native tensor product's left-factor action.
The carrier definition is exposed so that its module structures can reuse the native structures;
the action itself is characterized by `tensorEquiv_smul`.
Its base action agrees with the native tensor action under `tensorEquiv`. -/
@[expose] def Tensor (R _H M N : Type*) [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] := M ⊗[R] N

variable (R H M N : Type*) [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

instance : AddCommMonoid (Tensor R H M N) := inferInstanceAs (AddCommMonoid (M ⊗[R] N))

instance (R H M N : Type*) [CommSemiring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : AddCommGroup (Tensor R H M N) :=
  inferInstanceAs (AddCommGroup (M ⊗[R] N))

section PairAction

variable [Semiring H] [Algebra R H]
variable [Module H M] [IsScalarTower R H M] [Module H N] [IsScalarTower R H N]

/-- The two factor actions assembled into an action of `H ⊗[R] H`. -/
noncomputable def tensorPairAction : H ⊗[R] H →ₐ[R] Module.End R (M ⊗[R] N) :=
  (Module.endTensorEndAlgHom (R := R) (S := R) (A := R)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul R R M) (Algebra.lsmul R R N))

/-- A pure tensor of algebra elements acts on the two factors separately. -/
@[simp] theorem tensorPairAction_tmul (a b : H) (m : M) (n : N) :
    tensorPairAction R H M N (a ⊗ₜ[R] b) (m ⊗ₜ[R] n) =
      (a • m) ⊗ₜ[R] (b • n) := (rfl)

variable {M' N' : Type*}
variable [AddCommMonoid M'] [Module R M'] [Module H M'] [IsScalarTower R H M']
variable [AddCommMonoid N'] [Module R N'] [Module H N'] [IsScalarTower R H N']

variable {M N} in
/-- Tensor products of intertwiners commute with the separate factor actions. -/
theorem tensorPairAction_natural (f : M →ₗ[H] M') (g : N →ₗ[H] N')
    (t : H ⊗[R] H) (x : M ⊗[R] N) :
    TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)
        (tensorPairAction R H M N t x) =
      tensorPairAction R H M' N' t
        (TensorProduct.map (f.restrictScalars R) (g.restrictScalars R) x) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp [ht, hu]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul m n => simp

end PairAction

section Action

variable [Semiring H] [Bialgebra R H]
variable [Module H M] [IsScalarTower R H M] [Module H N] [IsScalarTower R H N]

/-- The representation of `H` on the native tensor product obtained from its coproduct. -/
noncomputable def tensorAction : H →ₐ[R] Module.End R (M ⊗[R] N) :=
  (tensorPairAction R H M N).comp (Bialgebra.comulAlgHom R H)

/-- The coproduct action is the pair action applied to the coproduct. -/
theorem tensorAction_apply (h : H) (x : M ⊗[R] N) :
    tensorAction R H M N h x =
      tensorPairAction R H M N (Coalgebra.comul h) x := (rfl)

/-- The coproduct module structure on the tensor carrier. -/
noncomputable instance : Module H (Tensor R H M N) :=
  Module.compHom (M ⊗[R] N) (tensorAction R H M N).toRingHom

/-- The base action is restriction of the coproduct action along the algebra map.

For the canonical algebra structure when `H = R`, this presentation also aligns the two
scalar actions.
The underlying equivalence below identifies it with the original native tensor action.
The priority keeps this presentation ahead of generic natural and integer scalar actions. -/
noncomputable instance (priority := 1100) : Module R (Tensor R H M N) :=
  Module.compHom (Tensor R H M N) (algebraMap R H)

/-- The coproduct module is compatible with the caller's base scalar action. -/
instance : IsScalarTower R H (Tensor R H M N) := IsScalarTower.of_compHom R H (Tensor R H M N)

/-- The underlying `R`-linear identification with the native tensor product. -/
noncomputable def tensorEquiv : Tensor R H M N ≃ₗ[R] M ⊗[R] N :=
  let e : Tensor R H M N ≃+ M ⊗[R] N := AddEquiv.refl _
  e.toLinearEquiv fun r x => LinearMap.congr_fun ((tensorAction R H M N).commutes r) x

/-- Finite base modules have a finite tensor product with the coproduct action. -/
instance [Module.Finite R M] [Module.Finite R N] : Module.Finite R (Tensor R H M N) :=
  Module.Finite.of_surjective (tensorEquiv R H M N).symm.toLinearMap
    (tensorEquiv R H M N).symm.surjective

variable {M N} in
/-- A pure tensor in the carrier with the coproduct action. -/
noncomputable def tmul (m : M) (n : N) : Tensor R H M N :=
  (tensorEquiv R H M N).symm (m ⊗ₜ[R] n)

/-- The underlying equivalence sends a pure tensor to the native pure tensor. -/
@[simp] theorem tensorEquiv_tmul (m : M) (n : N) :
    tensorEquiv R H M N (tmul R H m n) = m ⊗ₜ[R] n := by
  simp [tmul]

/-- The inverse underlying equivalence constructs pure tensors. -/
@[simp] theorem tensorEquiv_symm_tmul (m : M) (n : N) :
    (tensorEquiv R H M N).symm (m ⊗ₜ[R] n) = tmul R H m n := (rfl)

variable {M N} in
/-- Pure tensors are additive in the first factor. -/
@[simp] theorem add_tmul (m m' : M) (n : N) :
    tmul R H (m + m') n = tmul R H m n + tmul R H m' n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.add_tmul]

variable {M N} in
/-- Pure tensors are additive in the second factor. -/
@[simp] theorem tmul_add (m : M) (n n' : N) :
    tmul R H m (n + n') = tmul R H m n + tmul R H m n' := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.tmul_add]

variable {M N} in
/-- A zero first factor gives the zero tensor. -/
@[simp] theorem zero_tmul (n : N) : tmul R H (0 : M) n = 0 := by
  apply (tensorEquiv R H M N).injective
  simp

variable {M N} in
/-- A zero second factor gives the zero tensor. -/
@[simp] theorem tmul_zero (m : M) : tmul R H m (0 : N) = 0 := by
  apply (tensorEquiv R H M N).injective
  simp

variable {M N} in
/-- Base scalars may be applied to the first factor. -/
theorem smul_tmul' (r : R) (m : M) (n : N) :
    r • tmul R H m n = tmul R H (r • m) n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.smul_tmul']

variable {M N} in
/-- Base scalars may be applied to the second factor. -/
@[simp] theorem tmul_smul (r : R) (m : M) (n : N) :
    tmul R H m (r • n) = r • tmul R H m n := by
  apply (tensorEquiv R H M N).injective
  simp

variable {R H M N} in
/-- Prove a proposition about coproduct tensors by pure tensors and addition. -/
@[elab_as_elim] theorem Tensor.inductionOn {P : Tensor R H M N → Prop}
    (x : Tensor R H M N) (htmul : ∀ m n, P (tmul R H m n))
    (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
  have h : ∀ y : M ⊗[R] N, P ((tensorEquiv R H M N).symm y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m n => exact htmul m n
    | add y z hy hz => simpa only [map_add] using hadd _ _ hy hz
  simpa using h (tensorEquiv R H M N x)

variable {R H M N} in
/-- Two `H`-linear maps from the coproduct tensor carrier agree if they agree on pure tensors. -/
@[ext] theorem Tensor.ext {P : Type*} [AddCommMonoid P] [Module H P]
    {f g : Tensor R H M N →ₗ[H] P}
    (h : ∀ m n, f (tmul R H m n) = g (tmul R H m n)) : f = g := by
  apply LinearMap.ext
  intro x
  exact Tensor.inductionOn x h fun x y hx hy ↦ by simp only [map_add, hx, hy]

/-- The underlying equivalence expresses the action through the coproduct representation. -/
@[simp]
theorem tensorEquiv_smul (h : H) (x : Tensor R H M N) :
    tensorEquiv R H M N (h • x) =
      tensorAction R H M N h (tensorEquiv R H M N x) := (rfl)

variable {M' N' : Type*}
variable [AddCommMonoid M'] [Module R M'] [Module H M'] [IsScalarTower R H M']
variable [AddCommMonoid N'] [Module R N'] [Module H N'] [IsScalarTower R H N']

variable {M N} in
/-- The tensor product of native `H`-linear intertwiners, for the coproduct actions. -/
noncomputable def tensorMap (f : M →ₗ[H] M') (g : N →ₗ[H] N') :
    Tensor R H M N →ₗ[H] Tensor R H M' N' where
  toAddHom := ((tensorEquiv R H M' N').symm.toLinearMap.comp
    ((TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)).comp
      (tensorEquiv R H M N).toLinearMap)).toAddHom
  map_smul' h x := by
    apply (tensorEquiv R H M' N').injective
    simpa [tensorAction_apply] using
      tensorPairAction_natural R H f g (Coalgebra.comul h) (tensorEquiv R H M N x)

variable {M N} in
/-- The underlying map of a tensor intertwiner is the native tensor product of maps. -/
@[simp] theorem tensorEquiv_tensorMap (f : M →ₗ[H] M') (g : N →ₗ[H] N')
    (x : Tensor R H M N) :
    tensorEquiv R H M' N' (tensorMap R H f g x) =
      TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)
        (tensorEquiv R H M N x) := (rfl)

variable {M N} in
/-- A tensor intertwiner acts on pure tensors by its two component maps. -/
@[simp] theorem tensorMap_tmul (f : M →ₗ[H] M') (g : N →ₗ[H] N') (m : M) (n : N) :
    tensorMap R H f g (tmul R H m n) = tmul R H (f m) (g n) := by
  apply (tensorEquiv R H M' N').injective
  simp

/-- Tensoring the identity intertwiners gives the identity. -/
@[simp] theorem tensorMap_id :
    tensorMap R H (LinearMap.id : M →ₗ[H] M) (LinearMap.id : N →ₗ[H] N) =
      LinearMap.id := by
  apply Tensor.ext
  intro m n
  simp

variable {M'' N'' : Type*}
variable [AddCommMonoid M''] [Module R M''] [Module H M''] [IsScalarTower R H M'']
variable [AddCommMonoid N''] [Module R N''] [Module H N''] [IsScalarTower R H N'']

variable {M N} in
/-- Tensor products of intertwiners preserve composition. -/
@[simp] theorem tensorMap_comp (f : M →ₗ[H] M') (f' : M' →ₗ[H] M'')
    (g : N →ₗ[H] N') (g' : N' →ₗ[H] N'') :
    tensorMap R H (f'.comp f) (g'.comp g) =
      (tensorMap R H f' g').comp (tensorMap R H f g) := by
  apply Tensor.ext
  intro m n
  simp

end Action

end TauCeti.BialgebraModule
