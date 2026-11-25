/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Extension of scalars along a ring homomorphism

For a ring homomorphism `f : A →+* B` and an `A`-module `M`, the extension of scalars of `M`
along `f` is `B ⊗[A] M` for the `A`-algebra structure `f.toAlgebra` on `B`, written
`B ⊗[A, f] M` in the docstrings. Installing `f.toAlgebra` as an instance is not possible in
general: when `B = A` and `f` is not the identity it competes with `Algebra.id`, and on
`A ⊗[A] M` the `A`-module structure acting on the left factor competes with the one acting
through the base ring. The type synonym `TauCeti.TensorAlong f M` keeps `f.toAlgebra` local and
carries only the `B`-module structure through the left factor, together with the `B`-module
topology when `B` is a topological semiring.

## Main definitions

* `TauCeti.TensorAlong f M`: the extension of scalars `B ⊗[A, f] M` as a `B`-module.
* `TauCeti.TensorAlong.tmul`: the pure tensor `b ⊗ m`.
* `TauCeti.TensorAlong.basis`: the basis `1 ⊗ b i` extending a basis `b` of `M`.
* `TauCeti.TensorAlong.liftAddHom`: the lift of a biadditive map balanced along `f`.
* `TauCeti.TensorAlong.algebraMapEquiv`: extension of scalars along `algebraMap A B` is
  `B ⊗[A] M`.

## Main statements

* `TauCeti.TensorAlong.inductionOn`: induction over sums of pure tensors.
* `TauCeti.TensorAlong.ext`: `B`-linear maps out of `B ⊗[A, f] M` agree once they agree on the
  tensors `1 ⊗ m`.
* `TauCeti.TensorAlong.addHom_ext`: additive maps out of `B ⊗[A, f] M` agree once they agree on
  pure tensors.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- **Extension of scalars along a ring homomorphism.** For `f : A →+* B` and an `A`-module `M`,
`TensorAlong f M` is `B ⊗[A] M` for the `A`-algebra structure `f.toAlgebra` on `B`, a `B`-module
through the left factor. The type synonym keeps the `A`-algebra structure on `B` local, which
matters when `B = A` and `f` is not the identity. It is `implicit_reducible`, like Mathlib's
`DirectSum`, so that the additive group and monoid structures agree during instance search. -/
@[expose, implicit_reducible]
def TensorAlong (f : A →+* B) (M : Type*) [AddCommMonoid M] [Module A M] : Type _ :=
  letI := f.toAlgebra
  B ⊗[A] M

namespace TensorAlong

section Instances

variable (f : A →+* B) (M : Type*) [AddCommMonoid M] [Module A M]

instance instAddCommMonoid : AddCommMonoid (TensorAlong f M) :=
  letI := f.toAlgebra
  (inferInstance : AddCommMonoid (B ⊗[A] M))

instance instModule : Module B (TensorAlong f M) :=
  letI := f.toAlgebra
  (inferInstance : Module B (B ⊗[A] M))

instance instModuleFinite [Module.Finite A M] : Module.Finite B (TensorAlong f M) :=
  letI := f.toAlgebra
  (inferInstance : Module.Finite B (B ⊗[A] M))

instance instModuleFree [Module.Free A M] : Module.Free B (TensorAlong f M) :=
  letI := f.toAlgebra
  (inferInstance : Module.Free B (B ⊗[A] M))

/-- `TensorAlong f M` carries its `B`-module topology. -/
instance instTopologicalSpace [TopologicalSpace B] : TopologicalSpace (TensorAlong f M) :=
  moduleTopology B (TensorAlong f M)

instance instIsModuleTopology [TopologicalSpace B] : IsModuleTopology B (TensorAlong f M) :=
  ⟨rfl⟩

end Instances

instance instAddCommGroup {B : Type*} [CommRing B] (f : A →+* B) (M : Type*) [AddCommMonoid M]
    [Module A M] : AddCommGroup (TensorAlong f M) :=
  letI := f.toAlgebra
  (inferInstance : AddCommGroup (B ⊗[A] M))

variable {f : A →+* B} {M : Type*} [AddCommMonoid M] [Module A M]

/-- The pure tensor `b ⊗ m` in `B ⊗[A, f] M`. -/
def tmul (b : B) (m : M) : TensorAlong f M :=
  letI := f.toAlgebra
  b ⊗ₜ[A] m

/-- `tmul b m` is the pure tensor `b ⊗ₜ[A] m` of `B ⊗[A] M` for `f.toAlgebra`. -/
theorem tmul_def (b : B) (m : M) :
    (tmul b m : TensorAlong f M) = (letI := f.toAlgebra; (b ⊗ₜ[A] m : B ⊗[A] M)) :=
  (rfl)

@[simp]
theorem zero_tmul (m : M) : tmul (0 : B) m = (0 : TensorAlong f M) :=
  letI := f.toAlgebra
  TensorProduct.zero_tmul B m

@[simp]
theorem tmul_zero (b : B) : tmul b (0 : M) = (0 : TensorAlong f M) :=
  letI := f.toAlgebra
  TensorProduct.tmul_zero M b

theorem add_tmul (b b' : B) (m : M) :
    (tmul (b + b') m : TensorAlong f M) = tmul b m + tmul b' m :=
  letI := f.toAlgebra
  TensorProduct.add_tmul b b' m

theorem tmul_add (b : B) (m m' : M) :
    (tmul b (m + m') : TensorAlong f M) = tmul b m + tmul b m' :=
  letI := f.toAlgebra
  TensorProduct.tmul_add b m m'

/-- `B` acts on `B ⊗[A, f] M` through the left factor. -/
@[simp]
theorem smul_tmul' (b b' : B) (m : M) : b • (tmul b' m : TensorAlong f M) = tmul (b * b') m :=
  letI := f.toAlgebra
  TensorProduct.smul_tmul' b b' m

/-- Scalars of `A` move across the tensor sign through `f`. -/
theorem tmul_smul (b : B) (a : A) (m : M) :
    (tmul b (a • m) : TensorAlong f M) = tmul (f a * b) m :=
  letI := f.toAlgebra
  (TensorProduct.smul_tmul a b m).symm

/-- **Induction on `B ⊗[A, f] M`**: a property of pure tensors that is closed under sums holds
everywhere. -/
@[elab_as_elim]
theorem inductionOn {motive : TensorAlong f M → Prop} (x : TensorAlong f M)
    (tmul : ∀ (b : B) (m : M), motive (tmul b m))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  letI := f.toAlgebra
  TensorProduct.inductionOn (motive := motive) x tmul add

/-- `B`-linear maps out of `B ⊗[A, f] M` agree once they agree on the tensors `1 ⊗ m`. -/
@[ext]
theorem ext {N : Type*} [AddCommMonoid N] [Module B N] {φ ψ : TensorAlong f M →ₗ[B] N}
    (h : ∀ m : M, φ (tmul 1 m) = ψ (tmul 1 m)) : φ = ψ := by
  refine LinearMap.ext fun x => inductionOn x (fun b m => ?_) fun x y hx hy => by
    rw [map_add, map_add, hx, hy]
  rw [← mul_one b, ← smul_tmul', map_smul, map_smul, h]

variable (f) in
/-- The basis `1 ⊗ b i` of `B ⊗[A, f] M` extending a basis `b` of `M`. -/
def basis {ι : Type*} (b : Module.Basis ι A M) : Module.Basis ι B (TensorAlong f M) :=
  letI := f.toAlgebra
  Algebra.TensorProduct.basis B b

/-- `basis f b` is Mathlib's base-changed basis `Algebra.TensorProduct.basis B b` for
`f.toAlgebra`. -/
theorem basis_def {ι : Type*} (b : Module.Basis ι A M) :
    basis f b = (letI := f.toAlgebra; Algebra.TensorProduct.basis B b) :=
  (rfl)

@[simp]
theorem basis_apply {ι : Type*} (b : Module.Basis ι A M) (i : ι) :
    basis f b i = tmul 1 (b i) :=
  letI := f.toAlgebra
  Algebra.TensorProduct.basis_apply b i

/-- The coordinates of `c ⊗ m` in the base-changed basis are `c` times the images under `f` of
the coordinates of `m`. -/
@[simp]
theorem basis_repr_tmul {ι : Type*} (b : Module.Basis ι A M) (c : B) (m : M) :
    (basis f b).repr (tmul c m) = c • Finsupp.mapRange f (map_zero f) (b.repr m) :=
  letI := f.toAlgebra
  Algebra.TensorProduct.basis_repr_tmul b c m

section Lift

variable (f M) in
/-- The biadditive map `(b, m) ↦ b ⊗ m` into `B ⊗[A, f] M`: Mathlib's `TensorProduct.mk` for
`f.toAlgebra`, as an additive map. -/
def mkAddHom : B →+ M →+ TensorAlong f M :=
  letI := f.toAlgebra
  (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk A B M).toAddMonoidHom :
    B →+ M →+ B ⊗[A] M)

@[simp]
theorem mkAddHom_apply (b : B) (m : M) : mkAddHom f M b m = tmul b m :=
  (rfl)

variable {P : Type*} [AddCommMonoid P]

variable (f) in
/-- **The universal property of `B ⊗[A, f] M` for additive maps**: a biadditive map `φ` that is
balanced along `f`, `φ (f a * b) m = φ b (a • m)`, lifts to `B ⊗[A, f] M`. This is
`TensorProduct.liftAddHom` for `f.toAlgebra`. -/
def liftAddHom (φ : B →+ M →+ P) (hφ : ∀ (a : A) (b : B) (m : M), φ (f a * b) m = φ b (a • m)) :
    TensorAlong f M →+ P :=
  letI := f.toAlgebra
  TensorProduct.liftAddHom φ fun a b m => by rw [Algebra.smul_def]; exact hφ a b m

@[simp]
theorem liftAddHom_tmul (φ : B →+ M →+ P)
    (hφ : ∀ (a : A) (b : B) (m : M), φ (f a * b) m = φ b (a • m)) (b : B) (m : M) :
    liftAddHom f φ hφ (tmul b m) = φ b m :=
  letI := f.toAlgebra
  TensorProduct.liftAddHom_tmul _ _ b m

/-- Additive maps out of `B ⊗[A, f] M` agree once they agree on pure tensors: the uniqueness
half of the universal property `liftAddHom`. -/
@[ext]
theorem addHom_ext {φ ψ : TensorAlong f M →+ P}
    (h : ∀ (b : B) (m : M), φ (tmul b m) = ψ (tmul b m)) : φ = ψ :=
  AddMonoidHom.ext fun x => inductionOn x h fun x y hx hy => by rw [map_add, map_add, hx, hy]

end Lift

section AlgebraMap

variable [Algebra A B]

/-- The map `B ⊗[A] M → B ⊗[A, algebraMap A B] M` that is the identity on pure tensors. -/
private def toAlgebraMap : B ⊗[A] M →+ TensorAlong (algebraMap A B) M :=
  TensorProduct.liftAddHom (mkAddHom (algebraMap A B) M) fun a b m => by
    rw [mkAddHom_apply, mkAddHom_apply, tmul_smul, Algebra.smul_def]

/-- The map `B ⊗[A, algebraMap A B] M → B ⊗[A] M` that is the identity on pure tensors. -/
private def ofAlgebraMap : TensorAlong (algebraMap A B) M →+ B ⊗[A] M :=
  liftAddHom (algebraMap A B)
    (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk A B M).toAddMonoidHom) fun a b m => by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, ← Algebra.smul_def,
        TensorProduct.smul_tmul]

private theorem toAlgebraMap_tmul (b : B) (m : M) :
    toAlgebraMap (b ⊗ₜ[A] m) = (tmul b m : TensorAlong (algebraMap A B) M) :=
  TensorProduct.liftAddHom_tmul _ _ b m

private theorem ofAlgebraMap_tmul (b : B) (m : M) :
    ofAlgebraMap (tmul b m : TensorAlong (algebraMap A B) M) = b ⊗ₜ[A] m :=
  liftAddHom_tmul _ _ b m

variable (A B M) in
/-- **Extension of scalars along `algebraMap A B` is `B ⊗[A] M`**: the `B`-linear equivalence
`B ⊗[A] M ≃ B ⊗[A, algebraMap A B] M` that is the identity on pure tensors. It is not the
identity map, because the `A`-module structure on `B` from `(algebraMap A B).toAlgebra` agrees
with the given one only propositionally. -/
def algebraMapEquiv : B ⊗[A] M ≃ₗ[B] TensorAlong (algebraMap A B) M :=
  AddEquiv.toLinearEquiv
    { toFun := toAlgebraMap
      invFun := ofAlgebraMap
      left_inv x := by
        induction x using TensorProduct.inductionOn with
        | tmul b m => rw [toAlgebraMap_tmul, ofAlgebraMap_tmul]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      right_inv x := by
        induction x using inductionOn with
        | tmul b m => rw [ofAlgebraMap_tmul, toAlgebraMap_tmul]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      map_add' := map_add _ }
    fun c x => by
      induction x using TensorProduct.inductionOn with
      | tmul b m =>
        simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, TensorProduct.smul_tmul', toAlgebraMap_tmul,
          smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp]
theorem algebraMapEquiv_tmul (b : B) (m : M) :
    algebraMapEquiv A B M (b ⊗ₜ[A] m) = tmul b m :=
  toAlgebraMap_tmul b m

@[simp]
theorem algebraMapEquiv_symm_tmul (b : B) (m : M) :
    (algebraMapEquiv A B M).symm (tmul b m) = b ⊗ₜ[A] m :=
  ofAlgebraMap_tmul b m

end AlgebraMap

end TensorAlong

end TauCeti
