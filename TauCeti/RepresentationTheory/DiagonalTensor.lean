/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Diagonal tensor products of a representation with a module over a group algebra

Let `σ` be a representation of a monoid `Δ` on a `k`-module `W`, and let `N` be a module over the
group algebra `R[Δ]` which is also a `k`-module, the two structures commuting. Then `W ⊗[k] N` is
again an `R[Δ]`-module: an element `g` of `Δ` acts diagonally, by `σ g ⊗ g`, and a scalar of `R`
acts on `N` alone. The coefficient rings `k` of `W` and `R` of `N` may differ; for instance `k` is
`ZMod ℓ` and `N` is a module over an arbitrary ring `R` killed by `ℓ`. When `σ` is inflated from a
quotient of `Δ`, the construction `W ↦ W ⊗[k] N` turns representations of the quotient into
`R[Δ]`-modules, and it is exact when `N` is flat over `k`.

## Main definitions

* `TauCeti.diagonalTensorAction`: the ring homomorphism `R[Δ] → End_k(W ⊗[k] N)`.
* `TauCeti.diagonalTensor`: the `R[Δ]`-module `W ⊗[k] N` with this action.
* `TauCeti.diagonalTensorMap`: the morphism `f ⊗ 1` for an equivariant linear map `f`.
* `TauCeti.diagonalTensorTrivialEquiv`: the diagonal tensor product with a trivial line is `N`.

## Main results

* `TauCeti.shortExact_diagonalTensorMap`: for `N` flat over `k`, an equivariant short exact
  sequence of representations gives a short exact sequence of diagonal tensor products.
* `TauCeti.eq_zero_of_smul_eq_self_diagonalTensor`: over `ZMod ℓ`, if an element `z` of `Δ` fixes
  no nonzero vector of `N` and `z ^ ℓ ^ a` acts trivially on `W`, then `z` fixes no nonzero vector
  of `W ⊗ N`.
-/

public section

open CategoryTheory TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section DiagonalTensor

variable {R : Type u} [Ring R] {Δ : Type*} [Monoid Δ] {k : Type*} [CommRing k]
  {W : Type w} [AddCommGroup W] [Module k W] (σ : Representation k Δ W)
  (N : Type v) [AddCommGroup N] [Module R[Δ] N] [Module k N] [SMulCommClass R[Δ] k N]

omit [Module R[Δ] N] [SMulCommClass R[Δ] k N] in
/-- `Module.End.lTensorAlgHom` on a pure tensor; this holds by definition of `lTensorAlgHom`. -/
private theorem lTensorAlgHom_tmul (f : Module.End k N) (w : W) (n : N) :
    Module.End.lTensorAlgHom k N W f (w ⊗ₜ n) = w ⊗ₜ f n :=
  (rfl)

/-- The diagonal action of `R[Δ]` on `W ⊗[k] N`: an element `g` of `Δ` acts by `σ g ⊗ g`, and a
scalar of `R` acts on the second factor only. -/
noncomputable def diagonalTensorAction : R[Δ] →+* Module.End k (W ⊗[k] N) :=
  MonoidAlgebra.liftNCRingHom
    (RingHom.comp (RingHom.comp (Module.End.lTensorAlgHom k N W).toRingHom
      (Module.toModuleEnd k N)) (MonoidAlgebra.singleOneRingHom (R := R) (M := Δ)))
    (σ.tprod ((Module.toModuleEnd k N).toMonoidHom.comp (MonoidAlgebra.of R Δ)))
    fun r g ↦ TensorProduct.ext' fun w n ↦ by
      simp only [mul_apply_eq_comp, Representation.tprod_apply, TensorProduct.map_tmul,
        RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lTensorAlgHom_tmul,
        MonoidHom.comp_apply, Module.toModuleEnd_apply,
        MonoidAlgebra.of_apply]
      simp [MonoidAlgebra.singleOneRingHom, ← mul_smul, MonoidAlgebra.single_mul_single]

/-- On a pure tensor, `single g r` acts by `σ g` on the first factor and by `single g r` on the
second. -/
@[simp]
theorem diagonalTensorAction_single_tmul (g : Δ) (r : R) (w : W) (n : N) :
    diagonalTensorAction σ N (MonoidAlgebra.single g r) (w ⊗ₜ n) =
      σ g w ⊗ₜ (MonoidAlgebra.single g r • n) := by
  simp only [diagonalTensorAction, MonoidAlgebra.liftNCRingHom_single, mul_apply_eq_comp,
    Representation.tprod_apply, TensorProduct.map_tmul, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lTensorAlgHom_tmul, MonoidHom.comp_apply,
    Module.toModuleEnd_apply, MonoidAlgebra.of_apply]
  simp [MonoidAlgebra.singleOneRingHom, ← mul_smul, MonoidAlgebra.single_mul_single]

/-- The diagonal action intertwines `f ⊗ 1` for an equivariant `f`. -/
theorem diagonalTensorAction_comp_rTensor {W' : Type*} [AddCommGroup W'] [Module k W']
    {σ' : Representation k Δ W'} (f : W →ₗ[k] W') (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f) (a : R[Δ]) :
    f.rTensor N ∘ₗ diagonalTensorAction σ N a = diagonalTensorAction σ' N a ∘ₗ f.rTensor N := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | single g r =>
    refine TensorProduct.ext' fun w n ↦ ?_
    simp [← LinearMap.comp_apply (f := f), hf]

end DiagonalTensor

section DiagonalTensorModule

variable {R : Type u} [Ring R] {Δ : Type*} [Monoid Δ] {k : Type*} [CommRing k]
  {W : Type w} [AddCommGroup W] [Module k W] (σ : Representation k Δ W)
  (N : ModuleCat.{v} R[Δ]) [Module k N] [SMulCommClass R[Δ] k N]

/-- The `R[Δ]`-module `W ⊗[k] N` with the diagonal action of `Δ`, for a representation `σ` of `Δ`
on `W` and an `R[Δ]`-module `N` whose `k`-module structure commutes with `R[Δ]`. -/
@[expose] noncomputable def diagonalTensor : ModuleCat.{max w v} R[Δ] :=
  letI := Module.compHom (W ⊗[k] N) (diagonalTensorAction (R := R) σ N)
  ModuleCat.of R[Δ] (W ⊗[k] N)

/-- The `k`-module structure of `W ⊗[k] N`. -/
noncomputable instance : Module k (diagonalTensor σ N) :=
  inferInstanceAs (Module k (W ⊗[k] N))

/-- The scalar action on `diagonalTensor σ N` is the diagonal action. -/
@[simp]
theorem diagonalTensor_smul (a : R[Δ]) (x : diagonalTensor σ N) :
    a • x = diagonalTensorAction σ N a x :=
  (rfl)

/-- The diagonal action commutes with the `k`-module structure. -/
instance : SMulCommClass R[Δ] k (diagonalTensor σ N) where
  smul_comm a c x := by
    rw [diagonalTensor_smul, diagonalTensor_smul]
    exact (diagonalTensorAction σ N a).map_smul c x

variable {σ} in
/-- The map `f ⊗ 1` between diagonal tensor products, for an equivariant `f`. -/
noncomputable def diagonalTensorMap {W' : Type w} [AddCommGroup W'] [Module k W']
    {σ' : Representation k Δ W'} (f : W →ₗ[k] W') (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f) :
    diagonalTensor σ N ⟶ diagonalTensor σ' N :=
  ModuleCat.ofHom (X := diagonalTensor σ N) (Y := diagonalTensor σ' N)
    { toFun := f.rTensor N
      map_add' := map_add _
      map_smul' a x := by
        exact LinearMap.congr_fun (diagonalTensorAction_comp_rTensor σ N f hf a) x }

/-- `diagonalTensorMap N f hf` is `f ⊗ 1`. -/
@[simp]
theorem diagonalTensorMap_hom_apply {W' : Type w} [AddCommGroup W'] [Module k W']
    {σ' : Representation k Δ W'} (f : W →ₗ[k] W') (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f)
    (x : diagonalTensor σ N) : (diagonalTensorMap N f hf).hom x = f.rTensor N x :=
  (rfl)

variable {σ} in
/-- Composition of the maps `f ⊗ 1` between diagonal tensor products. -/
theorem diagonalTensorMap_comp {W' W'' : Type w} [AddCommGroup W'] [Module k W'] [AddCommGroup W'']
    [Module k W''] {σ' : Representation k Δ W'} {σ'' : Representation k Δ W''} (f : W →ₗ[k] W')
    (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f) (f' : W' →ₗ[k] W'') (hf' : ∀ g, f' ∘ₗ σ' g = σ'' g ∘ₗ f') :
    diagonalTensorMap N f hf ≫ diagonalTensorMap N f' hf' =
      diagonalTensorMap N (f' ∘ₗ f) fun g ↦ by
        rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hf', LinearMap.comp_assoc] := by
  ext x
  exact (LinearMap.rTensor_comp_apply N f' f x).symm

variable {σ} in
/-- **`− ⊗ N` is exact on equivariant short exact sequences** when `N` is flat over `k`: an
injection, an exact pair and a surjection of representations give a short exact sequence of
diagonal tensor products. -/
theorem shortExact_diagonalTensorMap [Module.Flat k N] {W' W'' : Type w} [AddCommGroup W']
    [Module k W'] [AddCommGroup W''] [Module k W''] {σ' : Representation k Δ W'}
    {σ'' : Representation k Δ W''} {f : W →ₗ[k] W'} (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f)
    {f' : W' →ₗ[k] W''} (hf' : ∀ g, f' ∘ₗ σ' g = σ'' g ∘ₗ f') (hinj : Function.Injective f)
    (hex : Function.Exact f f') (hsurj : Function.Surjective f') :
    (ShortComplex.mk (diagonalTensorMap N f hf) (diagonalTensorMap N f' hf') (by
      rw [diagonalTensorMap_comp]
      ext x
      simp only [diagonalTensorMap_hom_apply, hex.linearMap_comp_eq_zero, LinearMap.rTensor_zero]
      rfl)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact rTensor_exact N hex hsurj
  · exact (ModuleCat.mono_iff_injective _).2
      (Module.Flat.rTensor_preserves_injective_linearMap f hinj)
  · exact (ModuleCat.epi_iff_surjective _).2 (LinearMap.rTensor_surjective N hsurj)

/-- The diagonal tensor product with a trivial line is `N` itself, through `c ⊗ n ↦ c • n`. -/
noncomputable def diagonalTensorTrivialEquiv {τ : Representation k Δ k} (hτ : ∀ g, τ g = 1) :
    diagonalTensor τ N ≃ₗ[R[Δ]] N where
  toFun := TensorProduct.lid k N
  invFun := (TensorProduct.lid k N).symm
  left_inv := (TensorProduct.lid k N).symm_apply_apply
  right_inv := (TensorProduct.lid k N).apply_symm_apply
  map_add' := map_add _
  map_smul' a x := by
    rw [RingHom.id_apply, diagonalTensor_smul]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul c n =>
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]
      | single g r => simp [smul_comm, hτ]

/-- The isomorphism `diagonalTensorTrivialEquiv` sends `c ⊗ n` to `c • n`. -/
@[simp]
theorem diagonalTensorTrivialEquiv_tmul {τ : Representation k Δ k} (hτ : ∀ g, τ g = 1) (c : k)
    (n : N) : diagonalTensorTrivialEquiv N hτ (c ⊗ₜ[k] n) = c • n :=
  TensorProduct.lid_tmul n c

/-- A diagonal tensor product of finite modules over a finite ring is finite. -/
instance [Finite k] [Finite W] [Finite N] : Finite (diagonalTensor σ N) :=
  have : Module.Finite k W := Module.Finite.of_finite
  have : Module.Finite k N := Module.Finite.of_finite
  Module.finite_of_finite k (M := W ⊗[k] N)

end DiagonalTensorModule

section ZMod

variable {R : Type u} [Ring R] {Δ : Type*} [Monoid Δ] {ℓ : ℕ} [Fact ℓ.Prime]

/-- In characteristic `ℓ`, if `y - 1` is injective then so is `y ^ ℓ ^ a - 1`, because
`y ^ ℓ ^ a - 1 = (y - 1) ^ ℓ ^ a`. -/
private theorem injective_pow_sub_one {N : Type*} [AddCommGroup N] [Module (ZMod ℓ) N]
    {y : Module.End (ZMod ℓ) N} (hy : Function.Injective ⇑(y - 1)) (a : ℕ) :
    Function.Injective ⇑(y ^ ℓ ^ a - 1) := by
  have h := congrArg (Polynomial.aeval y)
    (sub_pow_char_pow (p := ℓ) (n := a) (Polynomial.X : Polynomial (ZMod ℓ)) 1)
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one, one_pow] at h
  rw [← h, FunLike.coe_pow_eq_iterate]
  exact hy.iterate _

variable {W : Type w} [AddCommGroup W] [Module (ZMod ℓ) W] (σ : Representation (ZMod ℓ) Δ W)
  (N : ModuleCat.{v} R[Δ]) [Module (ZMod ℓ) N] [SMulCommClass R[Δ] (ZMod ℓ) N]

/-- **Fixed vectors of a central element.** If `z` fixes no nonzero vector of `N` and
`z ^ ℓ ^ a` acts trivially on `W`, then `z` fixes no nonzero vector of `W ⊗ N`. -/
theorem eq_zero_of_smul_eq_self_diagonalTensor {z : Δ}
    (hN : ∀ n : N, MonoidAlgebra.of R Δ z • n = n → n = 0) {a : ℕ} (hσ : σ (z ^ ℓ ^ a) = 1)
    (x : diagonalTensor σ N) (hx : MonoidAlgebra.of R Δ z • x = x) : x = 0 := by
  set y := Module.toModuleEnd (ZMod ℓ) (S := R[Δ]) N (MonoidAlgebra.of R Δ z)
  have hy : Function.Injective ⇑(y - 1) := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    exact hN n (by simpa [y, sub_eq_zero] using hn)
  have hpow : ∀ m : ℕ, MonoidAlgebra.of R Δ (z ^ m) • x = x := by
    intro m
    induction m with
    | zero => rw [pow_zero, map_one, one_smul]
    | succ m ih => rw [pow_succ, map_mul, mul_smul, hx, ih]
  have hact : diagonalTensorAction σ N (MonoidAlgebra.of R Δ (z ^ ℓ ^ a)) =
      (y ^ ℓ ^ a).lTensor W := by
    refine TensorProduct.ext' fun w n ↦ ?_
    rw [MonoidAlgebra.of_apply, diagonalTensorAction_single_tmul, hσ, LinearMap.lTensor_tmul,
      one_apply_eq_self, ← MonoidAlgebra.of_apply, map_pow,
      show y ^ ℓ ^ a = Module.toModuleEnd (ZMod ℓ) (S := R[Δ]) N (MonoidAlgebra.of R Δ z ^ ℓ ^ a)
        from (map_pow _ _ _).symm]
    rfl
  have h1 : (y ^ ℓ ^ a).lTensor W x = x := by rw [← hact, ← diagonalTensor_smul, hpow]
  have hx' : ((y ^ ℓ ^ a - 1).lTensor W) x = 0 := by
    rw [LinearMap.lTensor_sub, Module.End.one_eq_id, LinearMap.lTensor_id]
    exact sub_eq_zero_of_eq h1
  exact (injective_iff_map_eq_zero _).1
    (Module.Flat.lTensor_preserves_injective_linearMap _ (injective_pow_sub_one hy a)) x hx'

end ZMod

end TauCeti
