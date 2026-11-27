/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.LinearAlgebra.End.CharP

import TauCeti.LinearAlgebra.TensorProduct.Finiteness

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

* `Representation.diagonalTensorAction`: the ring homomorphism `R[Δ] → End_k(W ⊗[k] N)`.
* `Representation.diagonalTensor`: the `R[Δ]`-module `W ⊗[k] N` with this action.
* `Representation.diagonalTensorMap`: the morphism `f ⊗ 1` for an equivariant linear map `f`.
* `Representation.diagonalTensorTrivialEquiv`: the diagonal tensor product with a trivial line is
  `N`.

## Main results

* `Representation.shortExact_diagonalTensorMap`: for `N` flat over `k`, an equivariant short exact
  sequence of representations gives a short exact sequence of diagonal tensor products.
* `Representation.eq_zero_of_smul_eq_self_diagonalTensor`: over `ZMod ℓ`, if an element `z` of
  `Δ` fixes no nonzero vector of `N` and `z ^ ℓ ^ a` acts trivially on `W`, then `z` fixes no
  nonzero vector of `W ⊗ N`.
-/

public section

open CategoryTheory TensorProduct
open scoped MonoidAlgebra

namespace Representation

universe u v w

section DiagonalTensor

variable {R : Type u} [Semiring R] {Δ : Type*} [Monoid Δ] {k : Type*} [CommSemiring k]
  {W : Type w} [AddCommMonoid W] [Module k W] (σ : Representation k Δ W)
  (N : Type v) [AddCommMonoid N] [Module R[Δ] N] [Module k N] [SMulCommClass R[Δ] k N]

/-- The diagonal action of `R[Δ]` on `W ⊗[k] N`: an element `g` of `Δ` acts by `σ g ⊗ g`, and a
scalar of `R` acts on the second factor only. -/
noncomputable def diagonalTensorAction : R[Δ] →+* Module.End k (W ⊗[k] N) :=
  MonoidAlgebra.liftNCRingHom
    (RingHom.comp (RingHom.comp (Module.End.lTensorAlgHom k N W).toRingHom
      (Module.toModuleEnd k N)) (MonoidAlgebra.singleOneRingHom (R := R) (M := Δ)))
    (σ.tprod ((Module.toModuleEnd k N).toMonoidHom.comp (MonoidAlgebra.of R Δ)))
    fun r g ↦ by
      -- `single 1 r` commutes with `single g 1`, so `1 ⊗ single 1 r` commutes with
      -- `σ g ⊗ single g 1`.
      have h := ((MonoidAlgebra.single_commute_single (Commute.one_left g)
        (Commute.one_right r)).map (Module.toModuleEnd k (S := R[Δ]) N)).eq
      -- `lTensorAlgHom` sends `a` to `1 ⊗ a` by definition.
      have hl (a : Module.End k N) : Module.End.lTensorAlgHom k N W a = a.lTensor W := rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hl,
        Representation.tprod_apply, MonoidHom.comp_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.singleOneRingHom_apply, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        MonoidAlgebra.singleAddHom_apply, LinearMap.lTensor_def]
      rw [commute_iff_eq, ← TensorProduct.map_mul, ← TensorProduct.map_mul, ← Module.End.one_eq_id,
        one_mul, mul_one]
      exact congrArg (TensorProduct.map (σ g)) h

/-- On a pure tensor, `single g r` acts by `σ g` on the first factor and by `single g r` on the
second. -/
@[simp]
theorem diagonalTensorAction_single_tmul (g : Δ) (r : R) (w : W) (n : N) :
    diagonalTensorAction σ N (MonoidAlgebra.single g r) (w ⊗ₜ n) =
      σ g w ⊗ₜ (MonoidAlgebra.single g r • n) := by
  simp only [diagonalTensorAction, MonoidAlgebra.liftNCRingHom_single, mul_apply_eq_comp,
    Representation.tprod_apply, TensorProduct.map_tmul, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Module.End.lTensorAlgHom_apply_apply,
    TensorProduct.liftAux_tmul, LinearMap.compl₂_apply, TensorProduct.mk_apply,
    MonoidHom.comp_apply, Module.toModuleEnd_apply, MonoidAlgebra.of_apply]
  simp [MonoidAlgebra.singleOneRingHom, ← mul_smul, MonoidAlgebra.single_mul_single]

/-- An element `g` of `Δ` acting trivially on `W` acts on `W ⊗[k] N` through the second factor
only. -/
theorem diagonalTensorAction_of_eq_lTensor {g : Δ} (hg : σ g = 1) :
    diagonalTensorAction σ N (MonoidAlgebra.of R Δ g) =
      (Module.toModuleEnd k (S := R[Δ]) N (MonoidAlgebra.of R Δ g)).lTensor W := by
  refine TensorProduct.ext' fun w n ↦ ?_
  simp [hg]

/-- The diagonal action intertwines `f ⊗ 1` for an equivariant `f`. -/
theorem rTensor_comp_diagonalTensorAction {W' : Type*} [AddCommMonoid W'] [Module k W']
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
        exact LinearMap.congr_fun (rTensor_comp_diagonalTensorAction σ N f hf a) x }

/-- `diagonalTensorMap N f hf` is `f ⊗ 1`. -/
@[simp]
theorem diagonalTensorMap_hom_apply {W' : Type w} [AddCommGroup W'] [Module k W']
    {σ' : Representation k Δ W'} (f : W →ₗ[k] W') (hf : ∀ g, f ∘ₗ σ g = σ' g ∘ₗ f)
    (x : diagonalTensor σ N) : (diagonalTensorMap N f hf).hom x = f.rTensor N x :=
  (rfl)

/-- The map `id ⊗ 1` is the identity. -/
@[simp]
theorem diagonalTensorMap_id :
    diagonalTensorMap N LinearMap.id (fun g ↦ by rw [LinearMap.id_comp, LinearMap.comp_id]) =
      𝟙 (diagonalTensor σ N) := by
  ext x
  rw [diagonalTensorMap_hom_apply, ModuleCat.id_apply]
  exact LinearMap.rTensor_id_apply N W x

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
      simp only [diagonalTensorMap_hom_apply, hex.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      -- The carrier of `diagonalTensor σ'' N` is `W'' ⊗[k] N` by definition.
      exact LinearMap.zero_apply (M := W ⊗[k] N) (M₂ := W'' ⊗[k] N) x)).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (rTensor_exact N hex hsurj)
    (Module.Flat.rTensor_preserves_injective_linearMap f hinj)
    (LinearMap.rTensor_surjective N hsurj)

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

/-- The inverse of `diagonalTensorTrivialEquiv` sends `n` to `1 ⊗ n`. -/
@[simp]
theorem diagonalTensorTrivialEquiv_symm_apply {τ : Representation k Δ k} (hτ : ∀ g, τ g = 1)
    (n : N) : (diagonalTensorTrivialEquiv N hτ).symm n = (1 : k) ⊗ₜ[k] n :=
  TensorProduct.lid_symm_apply n

/-- The diagonal tensor product of a finitely generated module with a finite module is finite, as
the tensor product `W ⊗[k] N` is (`TauCeti.finite_tensorProduct`). -/
instance [Module.Finite k W] [Finite N] : Finite (diagonalTensor σ N) :=
  inferInstanceAs (Finite (W ⊗[k] N))

end DiagonalTensorModule

section ZMod

variable {R : Type u} [Ring R] {Δ : Type*} [Monoid Δ] {ℓ : ℕ} [Fact ℓ.Prime]

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
  have hpow (m : ℕ) : MonoidAlgebra.of R Δ (z ^ m) • x = x := by
    rw [map_pow, ← smul_iterate_apply]
    exact Function.iterate_fixed hx m
  have hact : diagonalTensorAction σ N (MonoidAlgebra.of R Δ (z ^ ℓ ^ a)) =
      (y ^ ℓ ^ a).lTensor W := by
    rw [diagonalTensorAction_of_eq_lTensor σ N hσ, map_pow, map_pow]
  have h1 : (y ^ ℓ ^ a).lTensor W x = x := by rw [← hact, ← diagonalTensor_smul, hpow]
  have hx' : ((y ^ ℓ ^ a - 1).lTensor W) x = 0 := by
    rw [LinearMap.lTensor_sub, Module.End.one_eq_id, LinearMap.lTensor_id]
    exact sub_eq_zero_of_eq h1
  exact (injective_iff_map_eq_zero _).1
    (Module.Flat.lTensor_preserves_injective_linearMap _
      (Module.End.injective_pow_char_pow_sub_one hy a)) x hx'

end ZMod

end Representation
