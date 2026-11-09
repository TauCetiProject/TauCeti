/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.TensorProduct.CentralBaseChange

/-!
# Base change of modules along a change of coefficients

Let `k` be a commutative ring and `Λ` a `k`-algebra, possibly noncommutative. For a commutative
`k`-algebra `R`, the `R`-algebra `R ⊗[k] Λ` is `Λ` with coefficients extended to `R`. For a
commutative `R`-algebra `S` and a module `N` over `R ⊗[k] Λ`, the `S`-module `S ⊗[R] N` is a
module over `S ⊗[k] Λ`, with

`(s ⊗ l) • (s' ⊗ n) = (s * s') ⊗ ((1 ⊗ l) • n)`.

This is the change of coefficients along `R → S` of modules over `Λ` with coefficients in `R`:
an `R ⊗[k] Λ`-module is a `Λ`-module carrying a commuting `R`-linear structure, and
`S ⊗[R] N` extends its coefficients to `S` while keeping the action of `Λ`. The action is the
central base change `TauCeti.CentralBaseChange.module` of `N` along `R → S`, restricted along
the algebra isomorphism `S ⊗[k] Λ ≃ S ⊗[R] (R ⊗[k] Λ)` of
`TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`.

Base change along the identity of `R` is the identity: `TensorProduct.lid` is linear over
`R ⊗[k] Λ`. Base change along a composite `R → S → T` is the composite of the base changes: the
`T`-linear isomorphism `T ⊗[S] (S ⊗[R] N) ≃ T ⊗[R] N` of Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange` is linear over `T ⊗[k] Λ`. These are the
comparison isomorphisms of the base-change functors `CommAlgCat.moduleCatBaseChange` between the
categories of modules over `R ⊗[k] Λ` for varying `R`.

## Main definitions

* `TauCeti.CoefficientBaseChange.module`: the `S ⊗[k] Λ`-module structure on `S ⊗[R] N`.
* `TauCeti.CoefficientBaseChange.map`: the `S ⊗[k] Λ`-linear map `S ⊗[R] N → S ⊗[R] P` induced
  by an `R ⊗[k] Λ`-linear map `N → P`. It is semilinear: `map (r • φ) = algebraMap R S r • map φ`
  (`TauCeti.CoefficientBaseChange.map_smul`).
* `TauCeti.CoefficientBaseChange.lid`: the `R ⊗[k] Λ`-linear isomorphism `R ⊗[R] N ≃ N`.
* `TauCeti.CoefficientBaseChange.cancelBaseChange`: for a tower `R → S → T` and a module `M`
  over `S ⊗[k] Λ` identified with `S ⊗[R] N` by `e`, the `T ⊗[k] Λ`-linear isomorphism
  `T ⊗[S] M ≃ T ⊗[R] N`, `t ⊗ e (s ⊗ n) ↦ (s • t) ⊗ n`, with inverse `t ⊗ n ↦ t ⊗ e (1 ⊗ n)`.

## Implementation notes

The action `module` is an `abbrev`, so its body is exposed: it unfolds to `Module.compHom` along
the inverse of `TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`, and `smul_def` records
this. The definitions `map`, `lid` and `cancelBaseChange` are not exposed. Downstream
computations with them, including the comparison isomorphisms of
`CommAlgCat.moduleCatBaseChange`, go through the evaluation lemmas on tensors (`map_tmul`,
`lid_tmul`, `cancelBaseChange_tmul` and their inverses).

## References

* Edward Frenkel and Dennis Gaitsgory, *Local geometric Langlands correspondence and affine
  Kac–Moody algebras*, in *Algebraic Geometry and Number Theory*, Progress in Mathematics 253,
  Birkhäuser, 2006: categories of modules over a varying commutative base and their base change.
-/

public section

open scoped TensorProduct

namespace TauCeti.CoefficientBaseChange

open TauCeti.Algebra.TensorProduct (baseChangeTowerAlgEquiv baseChangeTowerAlgEquiv_symm_tmul)

variable (k : Type*) [CommRing k] (Λ : Type*) [Ring Λ] [Algebra k Λ]
  (R : Type*) [CommRing R] [Algebra k R]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

variable (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⊗[k] Λ) N]
  [IsScalarTower R (R ⊗[k] Λ) N]

/-- The `S ⊗[k] Λ`-module structure on `S ⊗[R] N`, with
`(s ⊗ l) • (s' ⊗ n) = (s * s') ⊗ ((1 ⊗ l) • n)` (`TauCeti.CoefficientBaseChange.tmul_smul_tmul`):
the central base change of `N` along `R → S`, restricted along the
`S`-algebra isomorphism `TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`.
Like `TauCeti.CentralBaseChange.module`, on which it is built, it is not a global instance;
activate it with `attribute [local instance low]`. -/
noncomputable abbrev module : Module (S ⊗[k] Λ) (S ⊗[R] N) :=
  Module.compHom _ ((CentralBaseChange.lsmul R S (R ⊗[k] Λ) N).comp
    (baseChangeTowerAlgEquiv k R Λ S).symm.toAlgHom).toRingHom

attribute [local instance low] module

variable {k Λ R S N}

theorem smul_def (t : S ⊗[k] Λ) (x : S ⊗[R] N) :
    t • x = CentralBaseChange.lsmul R S (R ⊗[k] Λ) N ((baseChangeTowerAlgEquiv k R Λ S).symm t) x :=
  (rfl)

@[simp]
theorem tmul_smul_tmul (s s' : S) (l : Λ) (n : N) :
    (s ⊗ₜ[k] l) • (s' ⊗ₜ[R] n) = (s * s') ⊗ₜ[R] (((1 : R) ⊗ₜ[k] l) • n) := by
  rw [smul_def, baseChangeTowerAlgEquiv_symm_tmul, ← CentralBaseChange.smul_def (A := R),
    CentralBaseChange.tmul_smul_tmul]

/-- The `S`-action on `S ⊗[R] N` is the action of `S ⊗[k] Λ` through `s ↦ s ⊗ 1`. -/
instance : IsScalarTower S (S ⊗[k] Λ) (S ⊗[R] N) where
  smul_assoc s t x := by simp only [smul_def, map_smul, LinearMap.smul_apply]

/-- `S` acts centrally, so `S ⊗[k] Λ`-linear maps between such modules form an `S`-module. -/
instance : SMulCommClass (S ⊗[k] Λ) S (S ⊗[R] N) where
  smul_comm t s x := by simp only [smul_def, LinearMap.map_smul]

/-- An `S ⊗[k] Λ`-linear map out of `S ⊗[R] N` is determined by its values on the tensors
`1 ⊗ n`. -/
@[ext]
theorem hom_ext {P : Type*} [AddCommGroup P] [Module (S ⊗[k] Λ) P]
    {f g : S ⊗[R] N →ₗ[S ⊗[k] Λ] P} (h : ∀ n, f ((1 : S) ⊗ₜ n) = g ((1 : S) ⊗ₜ n)) : f = g := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
    have hs : s ⊗ₜ[R] n = (s ⊗ₜ[k] (1 : Λ)) • ((1 : S) ⊗ₜ[R] n) := by
      rw [tmul_smul_tmul, mul_one, ← Algebra.TensorProduct.one_def, one_smul]
    rw [hs, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The scalars of `R` act on `S ⊗[R] N` through `S ⊗[k] Λ`: on `1 ⊗ n` they act as their images
`algebraMap R S r ⊗ 1`. -/
theorem one_tmul_smul (r : R) (n : N) :
    (1 : S) ⊗ₜ[R] (r • n) = algebraMap S (S ⊗[k] Λ) (algebraMap R S r) • ((1 : S) ⊗ₜ[R] n) := by
  rw [algebraMap_smul, TensorProduct.tmul_smul, algebraMap_smul]

variable {P : Type*} [AddCommGroup P] [Module R P] [Module (R ⊗[k] Λ) P]
  [IsScalarTower R (R ⊗[k] Λ) P]
  {Q : Type*} [AddCommGroup Q] [Module R Q] [Module (R ⊗[k] Λ) Q]
  [IsScalarTower R (R ⊗[k] Λ) Q]

variable (k Λ S) in
/-- The `S ⊗[k] Λ`-linear map `S ⊗[R] N → S ⊗[R] P`, `s ⊗ n ↦ s ⊗ φ n`, induced by an
`R ⊗[k] Λ`-linear map `φ : N → P`. Its underlying function is `LinearMap.lTensor` (`coe_map`). -/
noncomputable def map (φ : N →ₗ[R ⊗[k] Λ] P) : S ⊗[R] N →ₗ[S ⊗[k] Λ] S ⊗[R] P where
  toFun := (φ.restrictScalars R).lTensor S
  map_add' := map_add _
  map_smul' t x := by
    let _ := CentralBaseChange.module R S (R ⊗[k] Λ) N
    let _ := CentralBaseChange.module R S (R ⊗[k] Λ) P
    simpa only [CentralBaseChange.coe_map, CentralBaseChange.smul_def, smul_def,
      RingHom.id_apply] using
      (CentralBaseChange.map S φ).map_smul ((baseChangeTowerAlgEquiv k R Λ S).symm t) x

theorem coe_map (φ : N →ₗ[R ⊗[k] Λ] P) :
    ⇑(map k Λ S φ) = (φ.restrictScalars R).lTensor S := (rfl)

@[simp]
theorem map_tmul (φ : N →ₗ[R ⊗[k] Λ] P) (s : S) (n : N) :
    map k Λ S φ (s ⊗ₜ[R] n) = s ⊗ₜ φ n := (rfl)

@[simp]
theorem map_id : map k Λ S (LinearMap.id : N →ₗ[R ⊗[k] Λ] N) = LinearMap.id := by
  ext; simp

theorem map_comp (ψ : P →ₗ[R ⊗[k] Λ] Q) (φ : N →ₗ[R ⊗[k] Λ] P) :
    map k Λ S (ψ ∘ₗ φ) = map k Λ S ψ ∘ₗ map k Λ S φ := by
  ext; simp

@[simp]
theorem map_add (φ ψ : N →ₗ[R ⊗[k] Λ] P) :
    map k Λ S (φ + ψ) = map k Λ S φ + map k Λ S ψ := by
  ext; simp [TensorProduct.tmul_add]

/-- Base change is semilinear along `algebraMap R S`. -/
@[simp]
theorem map_smul (r : R) (φ : N →ₗ[R ⊗[k] Λ] P) :
    map k Λ S (r • φ) = algebraMap R S r • map k Λ S φ := by
  ext n
  simp [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

variable (k Λ R N) in
/-- Base change along the identity of `R` is the identity: the `R ⊗[k] Λ`-linear isomorphism
`R ⊗[R] N ≃ N`, `r ⊗ n ↦ r • n`, whose underlying `R`-linear isomorphism is
`TensorProduct.lid`. -/
noncomputable def lid : R ⊗[R] N ≃ₗ[R ⊗[k] Λ] N where
  __ := TensorProduct.lid R N
  map_smul' t x := by
    induction t using TensorProduct.inductionOn with
    | tmul c l =>
      induction x using TensorProduct.inductionOn with
      | tmul r n =>
        simp only [tmul_smul_tmul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, TensorProduct.lid_tmul, RingHom.id_apply, smul_comm _ r, mul_smul]
        rw [← smul_assoc c, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy =>
        simp_all only [smul_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          _root_.map_add]
    | add t t' ht ht' =>
      simp_all only [add_smul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        _root_.map_add]

@[simp]
theorem lid_tmul (r : R) (n : N) : lid k Λ R N (r ⊗ₜ n) = r • n := (rfl)

@[simp]
theorem lid_symm_apply (n : N) : (lid k Λ R N).symm n = 1 ⊗ₜ n := (rfl)

section Cancel

variable (T : Type*) [CommRing T] [Algebra k T] [Algebra R T] [Algebra S T]
  [IsScalarTower k R T] [IsScalarTower k S T] [IsScalarTower R S T]
  {M : Type*} [AddCommGroup M] [Module S M] [Module (S ⊗[k] Λ) M]
  [IsScalarTower S (S ⊗[k] Λ) M]

variable (k Λ) in
/-- Base change along a composite `R → S → T` is the composite of the base changes: the
`T ⊗[k] Λ`-linear isomorphism `T ⊗[S] M ≃ T ⊗[R] N`, `t ⊗ e (s ⊗ n) ↦ (s • t) ⊗ n`, for an
`S ⊗[k] Λ`-module `M` identified with `S ⊗[R] N` by `e`. Its underlying `T`-linear
isomorphism is the base change of `e⁻¹` followed by Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable def cancelBaseChange (e : S ⊗[R] N ≃ₗ[S ⊗[k] Λ] M) :
    T ⊗[S] M ≃ₗ[T ⊗[k] Λ] T ⊗[R] N where
  __ := (e.symm.restrictScalars S).baseChange S T _ _ ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N
  map_smul' t x := by
    induction t using TensorProduct.inductionOn with
    | tmul t' l =>
      induction x using TensorProduct.inductionOn with
      | tmul t m =>
        obtain ⟨y, rfl⟩ := e.surjective m
        induction y using TensorProduct.inductionOn with
        | tmul s n => simp [← _root_.map_smul e]
        | add y y' hy hy' =>
          simp_all only [_root_.map_add, TensorProduct.tmul_add, smul_add, AddHom.toFun_eq_coe,
            LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
      | add x y hx hy =>
        simp_all only [smul_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          _root_.map_add]
    | add t t' ht ht' =>
      simp_all only [add_smul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        _root_.map_add]

@[simp]
theorem cancelBaseChange_symm_tmul (e : S ⊗[R] N ≃ₗ[S ⊗[k] Λ] M) (t : T) (n : N) :
    (cancelBaseChange k Λ T e).symm (t ⊗ₜ n) = t ⊗ₜ e (1 ⊗ₜ n) := (rfl)

@[simp]
theorem cancelBaseChange_tmul (e : S ⊗[R] N ≃ₗ[S ⊗[k] Λ] M) (t : T) (s : S) (n : N) :
    cancelBaseChange k Λ T e (t ⊗ₜ e (s ⊗ₜ n)) = (s • t) ⊗ₜ n := by
  have he : e (s ⊗ₜ n) = s • e (1 ⊗ₜ n) := by
    simpa [TensorProduct.smul_tmul'] using
      _root_.map_smul (e.restrictScalars S) s ((1 : S) ⊗ₜ[R] n)
  rw [← LinearEquiv.eq_symm_apply, cancelBaseChange_symm_tmul, he,
    TensorProduct.smul_tmul]

end Cancel

end TauCeti.CoefficientBaseChange
