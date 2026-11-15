/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.PiTensorProduct.Option
public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul
import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-!
# Algebra equivalences for indexed tensor products

The linear equivalences for reindexing, removing an empty index set, and splitting off one
factor preserve the algebra structures on indexed tensor products. Their algebra versions
allow algebraic properties stable under binary tensor products to be proved by induction on a
finite index type.

These constructions upgrade Mathlib's `PiTensorProduct.reindex` and
`PiTensorProduct.isEmptyEquiv`, and `PiTensorProduct.optionEquiv`. Reindexing along permutations
gives the action of `Equiv.Perm ι` on a tensor power by algebra automorphisms
(`PiTensorProduct.permAlgEquiv`).

Applying algebra equivalences factorwise gives `PiTensorProduct.congrAlgEquiv`, the algebra
version of Mathlib's `PiTensorProduct.congr`.

For finite index types, the tensor product of the split algebras `κ i → R` is the split algebra
of functions on `Π i, κ i` (`PiTensorProduct.piScalarAlgEquiv`), built from Mathlib's
`PiTensorProduct.ofFinsuppEquiv'`. On a tensor power of `κ → R`, permuting the factors becomes
precomposition on functions on `ι → κ`.

A finite tensor product of commutative algebras commutes with base change: for a commutative
`R`-algebra `T`, `T ⊗[R] ⨂[R] i, A i ≃ₐ[T] ⨂[T] i, T ⊗[R] A i`
(`PiTensorProduct.baseChangeAlgEquiv`), compatibly with permutations of the factors of a tensor
power. Its inverse is built from the coproduct property `PiTensorProduct.productMap`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

/-- Reindexing an indexed tensor product of algebras as an algebra equivalence. -/
noncomputable def reindexAlgEquiv {ι κ : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) :
    (⨂[R] i, A i) ≃ₐ[R] ⨂[R] j, A (e.symm j) :=
  AlgEquiv.ofLinearEquiv (reindex R A e) (by simp [one_def, reindex_tprod, Pi.one_def]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext a b
      simp [tprod_mul_tprod, reindex_tprod, Pi.mul_def]

/-- The underlying linear equivalence of algebra reindexing is tensor reindexing. -/
@[simp]
theorem reindexAlgEquiv_toLinearEquiv {ι κ : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) :
    (reindexAlgEquiv (R := R) A e).toLinearEquiv = reindex R A e := (rfl)

/-- Reindexing preserves the labels of the entries of a pure tensor. -/
@[simp]
theorem reindexAlgEquiv_tprod {ι κ : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) (a : ∀ i, A i) :
    reindexAlgEquiv A e (tprod R a) = tprod R (fun j ↦ a (e.symm j)) := by
  simp [reindexAlgEquiv, reindex_tprod]

/-- Reattaching the original index labels recovers the original pure tensor. -/
@[simp]
theorem reindexAlgEquiv_symm_tprod {ι κ : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) (a : ∀ i, A i) :
    (reindexAlgEquiv (R := R) A e).symm (tprod R (fun j ↦ a (e.symm j))) = tprod R a := by
  rw [AlgEquiv.symm_apply_eq, reindexAlgEquiv_tprod]

/-- Reindexing along `e` moves the factor inclusion at `i` to the factor inclusion at `e i`. It is
a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem reindexAlgEquiv_singleAlgHom {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {A : Type*}
    [Semiring A] [Algebra R A] (e : ι ≃ κ) (i : ι) (a : A) :
    reindexAlgEquiv (R := R) (fun _ ↦ A) e (singleAlgHom i a) = singleAlgHom (e i) a := by
  rw [singleAlgHom_apply, singleAlgHom_apply, reindexAlgEquiv_tprod, MonoidHom.mulSingle_apply,
    MonoidHom.mulSingle_apply]
  have := Pi.mulSingle_comp_equiv e.symm i a
  rw [Equiv.symm_symm] at this
  exact congrArg (tprod R) this

section Congr

variable {ι : Type*} {A B : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]

/-- The tensor product of a family of algebra equivalences `A i ≃ₐ[R] B i`, as an algebra
equivalence. This upgrades Mathlib's `PiTensorProduct.congr`. -/
noncomputable def congrAlgEquiv (e : ∀ i, A i ≃ₐ[R] B i) : (⨂[R] i, A i) ≃ₐ[R] ⨂[R] i, B i :=
  AlgEquiv.ofLinearEquiv (congr fun i ↦ (e i).toLinearEquiv)
    (by simp [one_def, congr_tprod, Pi.one_def]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext a b
      simp [tprod_mul_tprod, congr_tprod, Pi.mul_def]

/-- The underlying linear equivalence of `PiTensorProduct.congrAlgEquiv` is
`PiTensorProduct.congr`. -/
@[simp]
theorem congrAlgEquiv_toLinearEquiv (e : ∀ i, A i ≃ₐ[R] B i) :
    (congrAlgEquiv e).toLinearEquiv = congr fun i ↦ (e i).toLinearEquiv := (rfl)

/-- `PiTensorProduct.congrAlgEquiv e` applies `e i` to the factor in slot `i` of a pure tensor. -/
@[simp]
theorem congrAlgEquiv_tprod (e : ∀ i, A i ≃ₐ[R] B i) (a : ∀ i, A i) :
    congrAlgEquiv e (tprod R a) = tprod R fun i ↦ e i (a i) :=
  congr_tprod _ a

/-- `PiTensorProduct.congrAlgEquiv e` sends `a` in the slot `i` to `e i a` in the slot `i`. It is
a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem congrAlgEquiv_singleAlgHom [DecidableEq ι] (e : ∀ i, A i ≃ₐ[R] B i) (i : ι) (a : A i) :
    congrAlgEquiv e (singleAlgHom i a) = singleAlgHom i (e i a) := by
  rw [singleAlgHom_apply, congrAlgEquiv_tprod, singleAlgHom_apply]
  congr 1
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]

end Congr

section Perm

variable {ι : Type*} (A : Type*) [Semiring A] [Algebra R A]

/-- The permutations of `ι` act on the tensor power `⨂[R] _ : ι, A` by algebra automorphisms:
`σ` moves the factor in slot `i` to slot `σ i`. This is `PiTensorProduct.reindexAlgEquiv` along
`σ`, made multiplicative in `σ`. -/
noncomputable def permAlgEquiv : Equiv.Perm ι →* (⨂[R] _ : ι, A) ≃ₐ[R] ⨂[R] _ : ι, A where
  toFun σ := reindexAlgEquiv (fun _ ↦ A) σ
  map_one' := AlgEquiv.ext fun x ↦ by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [Equiv.Perm.one_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' σ τ := AlgEquiv.ext fun x ↦ by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [Equiv.Perm.mul_def]
    | add x y hx hy => simp only [map_add, hx, hy]

variable {A}

/-- The underlying linear equivalence of a permutation of the factors is tensor reindexing. -/
@[simp]
theorem permAlgEquiv_toLinearEquiv (σ : Equiv.Perm ι) :
    (permAlgEquiv (R := R) A σ).toLinearEquiv = reindex R (fun _ ↦ A) σ := (rfl)

/-- A permutation `σ` sends the pure tensor `⨂ₜ xᵢ` to the pure tensor with `x (σ⁻¹ j)` in
slot `j`. -/
@[simp]
theorem permAlgEquiv_tprod (σ : Equiv.Perm ι) (x : ι → A) :
    permAlgEquiv (R := R) A σ (tprod R x) = tprod R (x ∘ σ.symm) :=
  reindexAlgEquiv_tprod (fun _ ↦ A) σ x

/-- A permutation `σ` moves the factor inclusion at `i` to the factor inclusion at `σ i`. -/
@[simp↓]
theorem permAlgEquiv_singleAlgHom [DecidableEq ι] (σ : Equiv.Perm ι) (i : ι) (a : A) :
    permAlgEquiv (R := R) A σ (singleAlgHom i a) = singleAlgHom (σ i) a :=
  reindexAlgEquiv_singleAlgHom σ i a

/-- Permuting the factors of a tensor power commutes with applying the same algebra equivalence
to every factor. -/
theorem congrAlgEquiv_permAlgEquiv {B : Type*} [Semiring B] [Algebra R B] (e : A ≃ₐ[R] B)
    (σ : Equiv.Perm ι) (x : ⨂[R] _ : ι, A) :
    congrAlgEquiv (fun _ ↦ e) (permAlgEquiv A σ x) =
      permAlgEquiv B σ (congrAlgEquiv (fun _ ↦ e) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [Function.comp_def]
  | add x y hx hy => simp only [map_add, hx, hy]

end Perm

/-- The tensor product over an empty family of algebras is the base algebra. -/
noncomputable def isEmptyAlgEquiv (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] : (⨂[R] i, A i) ≃ₐ[R] R :=
  AlgEquiv.ofLinearEquiv (isEmptyEquiv ι) (by simp [one_def, isEmptyEquiv_apply_tprod]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext a b
      simp [tprod_mul_tprod, isEmptyEquiv_apply_tprod]

/-- The empty-family algebra equivalence has the usual empty-family linear equivalence. -/
@[simp]
theorem isEmptyAlgEquiv_toLinearEquiv (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    (isEmptyAlgEquiv (R := R) ι A).toLinearEquiv = isEmptyEquiv ι := (rfl)

/-- An empty pure tensor is the multiplicative unit. -/
@[simp]
theorem isEmptyAlgEquiv_tprod (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    isEmptyAlgEquiv ι A (tprod R a) = 1 := by
  simp [isEmptyAlgEquiv, isEmptyEquiv_apply_tprod]

/-- The inverse empty-family equivalence sends a scalar to that scalar times the empty tensor. -/
@[simp]
theorem isEmptyAlgEquiv_symm_apply (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (r : R) :
    (isEmptyAlgEquiv (R := R) ι A).symm r = r • 1 := by
  apply (isEmptyAlgEquiv (R := R) ι A).injective
  simp

/-- Splitting off the factor at `none` of an indexed tensor product of algebras. -/
noncomputable def optionAlgEquiv {ι : Type*} (A : Option ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    (⨂[R] i, A i) ≃ₐ[R] (⨂[R] i, A (some i)) ⊗[R] A none :=
  AlgEquiv.ofLinearEquiv (optionEquiv A) (by
    simp [one_def, optionEquiv_tprod, Algebra.TensorProduct.one_def, Pi.one_def]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext a b
      simp [tprod_mul_tprod, optionEquiv_tprod, Algebra.TensorProduct.tmul_mul_tmul, Pi.mul_def]

/-- The underlying linear equivalence splits off the same factor at `none`. -/
@[simp]
theorem optionAlgEquiv_toLinearEquiv {ι : Type*} (A : Option ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    (optionAlgEquiv (R := R) A).toLinearEquiv = optionEquiv A := (rfl)

/-- Splitting off a factor of a pure tensor separates the `some` entries from the `none` entry. -/
@[simp]
theorem optionAlgEquiv_tprod {ι : Type*} (A : Option ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    optionAlgEquiv (R := R) A (tprod R a) = tprod R (fun i ↦ a (some i)) ⊗ₜ a none := by
  simp [optionAlgEquiv]

/-- Reattaching the separated factor recovers the original pure tensor. -/
@[simp]
theorem optionAlgEquiv_symm_tmul {ι : Type*} (A : Option ι → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    (optionAlgEquiv (R := R) A).symm (tprod R (fun i ↦ a (some i)) ⊗ₜ a none) = tprod R a := by
  rw [AlgEquiv.symm_apply_eq, optionAlgEquiv_tprod]

section PiScalar

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Finite (κ i)]

variable (R κ) in
/-- The underlying linear equivalence of `PiTensorProduct.piScalarAlgEquiv`. -/
private noncomputable def piScalarLinearEquiv :
    (⨂[R] i, (κ i → R)) ≃ₗ[R] ((Π i, κ i) → R) := by
  classical
  exact congr (fun i ↦ (Finsupp.linearEquivFunOnFinite R R (κ i)).symm) ≪≫ₗ
    ofFinsuppEquiv' ≪≫ₗ Finsupp.linearEquivFunOnFinite R R (Π i, κ i)

private theorem piScalarLinearEquiv_tprod (f : Π i, κ i → R) :
    piScalarLinearEquiv R κ (tprod R f) = fun p ↦ ∏ i, f i (p i) := by
  classical
  ext p
  simp [piScalarLinearEquiv]

variable (R κ) in
/-- For finite index types, the tensor product of the function algebras `κ i → R` is the algebra
of functions on the product `Π i, κ i`: the pure tensor `⨂ₜ fᵢ` is the function
`p ↦ ∏ i, fᵢ (p i)`. In particular, a tensor power of a split algebra `κ → R` is split. -/
noncomputable def piScalarAlgEquiv : (⨂[R] i, (κ i → R)) ≃ₐ[R] ((Π i, κ i) → R) :=
  AlgEquiv.ofLinearEquiv (piScalarLinearEquiv R κ)
    (by ext p; simp [one_def, piScalarLinearEquiv_tprod]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by
      ext f g p
      simp [tprod_mul_tprod, piScalarLinearEquiv_tprod, Finset.prod_mul_distrib]

/-- `PiTensorProduct.piScalarAlgEquiv` sends `⨂ₜ fᵢ` to `p ↦ ∏ i, fᵢ (p i)`. -/
@[simp]
theorem piScalarAlgEquiv_tprod (f : Π i, κ i → R) :
    piScalarAlgEquiv R κ (tprod R f) = fun p ↦ ∏ i, f i (p i) :=
  piScalarLinearEquiv_tprod f

/-- `PiTensorProduct.piScalarAlgEquiv` sends the function `f` placed in slot `i` to
`p ↦ f (p i)`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the
factor inclusion first. -/
@[simp↓]
theorem piScalarAlgEquiv_singleAlgHom [DecidableEq ι] (i : ι) (f : κ i → R) :
    piScalarAlgEquiv R κ (singleAlgHom i f) = fun p ↦ f (p i) := by
  ext p
  rw [singleAlgHom_apply, piScalarAlgEquiv_tprod]
  dsimp only
  rw [Finset.prod_eq_single i (fun j _ hj ↦ ?_) (by simp), MonoidHom.mulSingle_apply,
    Pi.mulSingle_eq_same]
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, Pi.one_apply]

/-- Permuting the tensor factors of a tensor power of a function algebra by `σ` becomes
precomposition with `σ` on functions on `ι → κ`. -/
theorem piScalarAlgEquiv_permAlgEquiv {κ : Type*} [Finite κ] (σ : Equiv.Perm ι)
    (x : ⨂[R] _ : ι, (κ → R)) :
    piScalarAlgEquiv R (fun _ ↦ κ) (permAlgEquiv (κ → R) σ x) =
      fun p ↦ piScalarAlgEquiv R (fun _ ↦ κ) x (p ∘ σ) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    ext p
    simp only [map_smul, permAlgEquiv_tprod, piScalarAlgEquiv_tprod, Pi.smul_apply,
      Function.comp_apply]
    congr 1
    exact (Equiv.prod_comp σ fun i ↦ f (σ.symm i) (p i)).symm.trans (by simp)
  | add x y hx hy =>
    ext p
    simp only [map_add, Pi.add_apply, hx, hy]

end PiScalar

section BaseChange

variable (T : Type*) [CommSemiring T] [Algebra R T] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type*) [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]

/-- Base change of a finite tensor product of commutative algebras: for a commutative
`R`-algebra `T`, the `T`-algebra `T ⊗[R] ⨂[R] i, A i` is the tensor product over `T` of the base
changes `T ⊗[R] A i`. It sends `t ⊗ ⨂ₜ aᵢ` to `t • ⨂ₜ (1 ⊗ aᵢ)`
(`PiTensorProduct.baseChangeAlgEquiv_tmul_tprod`). -/
noncomputable def baseChangeAlgEquiv : T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, T ⊗[R] A i :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId T _)
      (productMap fun i ↦ ((singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i).restrictScalars
        R).comp Algebra.TensorProduct.includeRight) fun _ _ ↦ .all _ _)
    (productMap fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i))
    (algHom_ext fun i ↦ Algebra.TensorProduct.ext' fun t a ↦ by
      simp only [AlgHom.comp_apply, productMap_singleAlgHom, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
      -- `t ⊗ a = t • (1 ⊗ a)` returns to the slot `i` it came from.
      rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) (algHom_ext fun i ↦ AlgHom.ext fun a ↦ by
      simp [-singleAlgHom_apply, Algebra.TensorProduct.lift_tmul]))

variable {T A}

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ ⨂ₜ aᵢ` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul_tprod (t : T) (a : ∀ i, A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ tprod R a) = t • tprod T fun i ↦ (1 : T) ⊗ₜ[R] a i := by
  rw [baseChangeAlgEquiv, AlgEquiv.ofAlgHom_apply, Algebra.TensorProduct.lift_tmul,
    productMap_tprod, Algebra.ofId_apply, ← Algebra.smul_def, tprod_eq_prod_singleAlgHom (R := T)]
  rfl

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `1 ⊗ a`, for `a` in the slot `i`, to `1 ⊗ a` in
the slot `i`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the factor
inclusion first. -/
@[simp↓]
theorem baseChangeAlgEquiv_one_tmul_singleAlgHom (i : ι) (a : A i) :
    baseChangeAlgEquiv T A (1 ⊗ₜ[R] singleAlgHom i a) = singleAlgHom i ((1 : T) ⊗ₜ[R] a) := by
  rw [baseChangeAlgEquiv, AlgEquiv.ofAlgHom_apply, Algebra.TensorProduct.lift_tmul, map_one,
    one_mul, productMap_singleAlgHom]
  rfl

/-- The inverse of `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a` in the slot `i` to
`t ⊗ a`, with `a` in the slot `i`. It is a pre-simp lemma since `singleAlgHom_apply` would
otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem baseChangeAlgEquiv_symm_singleAlgHom (i : ι) (t : T) (a : A i) :
    (baseChangeAlgEquiv T A).symm (singleAlgHom (A := fun i ↦ T ⊗[R] A i) i (t ⊗ₜ[R] a)) =
      t ⊗ₜ[R] singleAlgHom i a := by
  rw [baseChangeAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, productMap_singleAlgHom,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Base change of tensor powers commutes with permuting the factors: on
`T ⊗[R] ⨂[R] _ : ι, B` a permutation `σ` acts through the right factor. -/
theorem baseChangeAlgEquiv_map_permAlgEquiv {B : Type*} [CommSemiring B] [Algebra R B]
    (σ : Equiv.Perm ι) (x : T ⊗[R] (⨂[R] _ : ι, B)) :
    baseChangeAlgEquiv T (fun _ ↦ B)
        (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv B σ).toAlgHom x) =
      permAlgEquiv (T ⊗[R] B) σ (baseChangeAlgEquiv T (fun _ ↦ B) x) := by
  suffices h : (baseChangeAlgEquiv (R := R) T fun _ : ι ↦ B).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv B σ).toAlgHom) =
      (permAlgEquiv (T ⊗[R] B) σ).toAlgHom.comp (baseChangeAlgEquiv T fun _ ↦ B).toAlgHom from
    DFunLike.congr_fun h x
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    (algHom_ext fun i ↦ AlgHom.ext fun b ↦ ?_)
  simp [-singleAlgHom_apply]

end BaseChange

end PiTensorProduct
