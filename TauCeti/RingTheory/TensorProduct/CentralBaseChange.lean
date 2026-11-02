/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import TauCeti.LinearAlgebra.Exact

/-!
# Central base change of modules over an algebra

Let `A` be a commutative ring, `Λ` an `A`-algebra (possibly noncommutative, so `A` acts
centrally), and `S` a commutative `A`-algebra. For a left `Λ`-module `M` whose `A`-module
structure is the restriction of its `Λ`-module structure, the `S`-module `S ⊗[A] M` is a module
over the ring `S ⊗[A] Λ`, with `(s ⊗ l) • (s' ⊗ m) = (s * s') ⊗ (l • m)`.

The main result is that, when `S` is flat over `A` and `M` is finitely presented over `Λ`, the
canonical `S`-linear map `S ⊗[A] Hom_Λ(M, N) → Hom_{S ⊗[A] Λ}(S ⊗[A] M, S ⊗[A] N)`,
`s ⊗ φ ↦ s • (1 ⊗ φ)`, is an isomorphism for every `Λ`-module `N`. As a consequence,
projectivity of `S ⊗[A] M` over `S ⊗[A] Λ` descends to `M`, both along a single faithfully flat
`S`, and along a family of flat `A`-algebras that jointly detects the vanishing of finitely
generated `A`-modules. Such families, for instance the completions of a Dedekind domain at its
primes, are how lattices over orders are compared with their local completions.

The `S ⊗[A] Λ`-module structure on `S ⊗[A] M` is the definition `TauCeti.CentralBaseChange.module`,
which is not an instance: for `M = Λ` it agrees with the multiplication of `S ⊗[A] Λ` only
propositionally. Files that use it activate it with `attribute [local instance low]`, so that the
multiplication of `S ⊗[A] Λ` on itself is still found first. Mathlib's
`TensorProduct.Algebra.module` builds the same kind of action from commuting `S`- and
`Λ`-actions, but `S ⊗[A] M` carries no `Λ`-action instance, so the two actions are packaged
together here as an `S`-algebra map `TauCeti.CentralBaseChange.lsmul` into
`Module.End S (S ⊗[A] M)`.

## Main definitions

* `TauCeti.CentralBaseChange.lsmul`: the action of `S ⊗[A] Λ` on `S ⊗[A] M`, as an `S`-algebra map.
* `TauCeti.CentralBaseChange.module`: the resulting `S ⊗[A] Λ`-module structure on `S ⊗[A] M`.
* `TauCeti.CentralBaseChange.map`: the `S ⊗[A] Λ`-linear map `S ⊗[A] M → S ⊗[A] N` induced by a
  `Λ`-linear map `M → N`, and `TauCeti.CentralBaseChange.mapHom`, the same as an `A`-linear map
  of `Hom` modules.
* `TauCeti.CentralBaseChange.homEquiv`: for flat `S` and finitely presented `M`, the `S`-linear
  equivalence `S ⊗[A] (M →ₗ[Λ] N) ≃ₗ[S] (S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N)`.

## Main results

* `TauCeti.CentralBaseChange.isBaseChange_mapHom`: for flat `S` and finitely presented `M`,
  `mapHom` exhibits the `Hom` module over `S ⊗[A] Λ` as the base change of the `Hom` module
  over `Λ`.
* `TauCeti.CentralBaseChange.projective_of_faithfullyFlat`: projectivity descends along a
  faithfully flat `S`.
* `TauCeti.CentralBaseChange.projective_of_forall_projective`: projectivity descends along a
  family of flat `A`-algebras that jointly detects the vanishing of finitely generated
  `A`-modules, when `A` is noetherian and `M` is finite over `A`.

## Implementation notes

For `M = Λⁿ` the comparison is the base change `Nⁿ → (S ⊗[A] N)ⁿ`. For general `M` one chooses
a finite presentation `Λᵐ → Λⁿ → M → 0`; then `Hom_Λ(M, N)` is the kernel of
`Hom_Λ(Λⁿ, N) → Hom_Λ(Λᵐ, N)`, and flatness of `S` preserves this kernel. This is the argument
of Mathlib's `Module.FinitePresentation.isBaseChange_map`, the case `Λ = A`, which the proof of
`isBaseChange_mapHom` follows. No localization theory of the noncommutative ring `Λ` is used.

## References

* C. A. Weibel, *The K-book*, Chapter I, §2, Locally free modules 2.4 and its proof, pp. 10–11.
-/

public section

open scoped TensorProduct

namespace TauCeti.CentralBaseChange

variable (A : Type*) [CommRing A] (S : Type*) [CommRing S] [Algebra A S]
  (Λ : Type*) [Ring Λ] [Algebra A Λ]
  (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]

/-- The action of `S ⊗[A] Λ` on `S ⊗[A] M`, as an `S`-algebra map to the `S`-linear
endomorphisms: `s ⊗ l` acts as `s` on the left factor and as `l` on the right factor. -/
noncomputable def lsmul : S ⊗[A] Λ →ₐ[S] Module.End S (S ⊗[A] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    ((Module.End.baseChangeHom A S M).comp (Algebra.lsmul A A M))
    fun s _ ↦ by simpa only [Algebra.ofId_apply] using Algebra.commute_algebraMap_left s _

/-- The `S ⊗[A] Λ`-module structure on `S ⊗[A] M` given by `TauCeti.CentralBaseChange.lsmul`,
with `(s ⊗ l) • (s' ⊗ m) = (s * s') ⊗ (l • m)`. It is not an instance, since for `M = Λ` it is
only propositionally equal to the multiplication of `S ⊗[A] Λ`; activate it with
`attribute [local instance low]`. -/
noncomputable abbrev module : Module (S ⊗[A] Λ) (S ⊗[A] M) :=
  Module.compHom _ (lsmul A S Λ M).toRingHom

attribute [local instance low] module

variable {A S Λ M}

theorem smul_def (t : S ⊗[A] Λ) (x : S ⊗[A] M) : t • x = lsmul A S Λ M t x := (rfl)

theorem lsmul_tmul (s : S) (l : Λ) :
    lsmul A S Λ M (s ⊗ₜ[A] l) = s • (Algebra.lsmul A A M l).baseChange S := by
  rw [lsmul, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, AlgHom.comp_apply]
  -- `Module.End.baseChangeHom` is `LinearMap.baseChange` bundled as an algebra map.
  rfl

@[simp]
theorem tmul_smul_tmul (s s' : S) (l : Λ) (m : M) :
    (s ⊗ₜ[A] l) • (s' ⊗ₜ[A] m) = (s * s') ⊗ₜ[A] (l • m) := by
  simp [smul_def, lsmul_tmul, TensorProduct.smul_tmul']

/-- The `S`-action on `S ⊗[A] M` is the action of `S ⊗[A] Λ` through `s ↦ s ⊗ 1`. -/
instance : IsScalarTower S (S ⊗[A] Λ) (S ⊗[A] M) where
  smul_assoc s t x := by simp only [smul_def, map_smul, LinearMap.smul_apply]

/-- `S` acts centrally, so `S ⊗[A] Λ`-linear maps between such modules form an `S`-module. -/
instance : SMulCommClass (S ⊗[A] Λ) S (S ⊗[A] M) where
  smul_comm t s x := by simp only [smul_def, LinearMap.map_smul]

/-- `A` acts centrally, so `S ⊗[A] Λ`-linear maps between such modules form an `A`-module. -/
instance : SMulCommClass (S ⊗[A] Λ) A (S ⊗[A] M) where
  smul_comm t a x := by rw [← algebraMap_smul S a x, smul_comm, algebraMap_smul]

/-- An `S ⊗[A] Λ`-linear map out of `S ⊗[A] M` is determined by its values on the tensors
`1 ⊗ m`. -/
@[ext]
theorem hom_ext {P : Type*} [AddCommGroup P] [Module (S ⊗[A] Λ) P]
    {f g : S ⊗[A] M →ₗ[S ⊗[A] Λ] P} (h : ∀ m, f ((1 : S) ⊗ₜ m) = g ((1 : S) ⊗ₜ m)) : f = g := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    have hs : s ⊗ₜ[A] m = (s ⊗ₜ[A] (1 : Λ)) • ((1 : S) ⊗ₜ[A] m) := by simp
    rw [hs, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {N : Type*} [AddCommGroup N] [Module A N] [Module Λ N] [IsScalarTower A Λ N]
  {P : Type*} [AddCommGroup P] [Module A P] [Module Λ P] [IsScalarTower A Λ P]

variable (S) in
/-- The `S ⊗[A] Λ`-linear map `S ⊗[A] M → S ⊗[A] N`, `s ⊗ m ↦ s ⊗ φ m`, induced by a `Λ`-linear
map `φ : M → N`. Its underlying function is `LinearMap.lTensor` (`coe_map`). -/
noncomputable def map (φ : M →ₗ[Λ] N) : S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N where
  toFun := (φ.restrictScalars A).lTensor S
  map_add' := map_add _
  map_smul' t x := by
    induction t using TensorProduct.inductionOn with
    | tmul s l =>
      induction x using TensorProduct.inductionOn with
      | tmul s' m => simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add t t' ht ht' => simp only [add_smul, map_add, ht, ht']

theorem coe_map (φ : M →ₗ[Λ] N) :
    ⇑(map S φ : S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N) = (φ.restrictScalars A).lTensor S := (rfl)

@[simp]
theorem map_tmul (φ : M →ₗ[Λ] N) (s : S) (m : M) : map S φ (s ⊗ₜ[A] m) = s ⊗ₜ φ m := (rfl)

@[simp]
theorem map_id :
    map S (LinearMap.id : M →ₗ[Λ] M) = (LinearMap.id : S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] M) := by
  ext; simp

theorem map_comp (ψ : N →ₗ[Λ] P) (φ : M →ₗ[Λ] N) :
    map S (ψ ∘ₗ φ) = (map S ψ ∘ₗ map S φ : S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] P) := by
  ext; simp

variable (S) in
/-- `map` preserves surjectivity, since `S ⊗[A] -` is right exact. -/
theorem map_surjective {φ : M →ₗ[Λ] N} (hφ : Function.Surjective φ) :
    Function.Surjective (map S φ : S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N) := by
  rw [coe_map]
  exact LinearMap.lTensor_surjective S hφ

variable (A S Λ M N) in
/-- `TauCeti.CentralBaseChange.map` as an `A`-linear map
`Hom_Λ(M, N) → Hom_{S ⊗[A] Λ}(S ⊗[A] M, S ⊗[A] N)`. For flat `S` and finitely presented `M` it
exhibits its target as the base change of its source (`isBaseChange_mapHom`). -/
noncomputable def mapHom : (M →ₗ[Λ] N) →ₗ[A] S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N where
  toFun := map S
  map_add' φ ψ := by ext; simp [TensorProduct.tmul_add]
  map_smul' a φ := by ext; simp [TensorProduct.tmul_smul]

@[simp]
theorem mapHom_apply (φ : M →ₗ[Λ] N) : mapHom A S Λ M N φ = map S φ := (rfl)

section Free

/-! ### The comparison for finite free modules -/

variable {ι : Type*}

/-- The coordinates of `S ⊗[A] (ι → Λ)` in `S ⊗[A] Λ` are `S ⊗[A] Λ`-linear. -/
private theorem piRightHom_smul (t : S ⊗[A] Λ) (x : S ⊗[A] (ι → Λ)) (i : ι) :
    TensorProduct.piRightHom A S S (fun _ : ι ↦ Λ) (t • x) i =
      t * TensorProduct.piRightHom A S S (fun _ : ι ↦ Λ) x i := by
  induction t using TensorProduct.inductionOn with
  | tmul s l =>
    induction x using TensorProduct.inductionOn with
    | tmul s' v => simp
    | add x y hx hy => simp only [smul_add, map_add, Pi.add_apply, hx, hy, mul_add]
  | add t t' ht ht' => simp only [add_smul, map_add, Pi.add_apply, ht, ht', add_mul]

variable [Fintype ι] [DecidableEq ι]

/-- Every element of `S ⊗[A] (ι → Λ)` is the combination of the basis vectors `1 ⊗ Pi.single i 1`
with its coordinates in `S ⊗[A] Λ`. -/
private theorem sum_piRightHom_smul (x : S ⊗[A] (ι → Λ)) :
    ∑ i, TensorProduct.piRightHom A S S (fun _ : ι ↦ Λ) x i •
      ((1 : S) ⊗ₜ[A] (Pi.single i 1 : ι → Λ)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    simp only [TensorProduct.piRightHom_tmul, tmul_smul_tmul, mul_one, ← Pi.single_smul',
      smul_eq_mul, ← TensorProduct.tmul_sum, Finset.univ_sum_single]
  | add x y hx hy => simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, hx, hy]

variable (A S Λ N ι) in
/-- An `S ⊗[A] Λ`-linear map out of `S ⊗[A] (ι → Λ)` is determined by its values on the basis
vectors `1 ⊗ Pi.single i 1`, and these values are arbitrary. -/
private noncomputable def freeHomEquiv :
    (S ⊗[A] (ι → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N) ≃ₗ[S] (ι → S ⊗[A] N) where
  toFun ψ i := ψ ((1 : S) ⊗ₜ Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v :=
    { toFun x := ∑ i, TensorProduct.piRightHom A S S (fun _ : ι ↦ Λ) x i • v i
      map_add' x y := by simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' t x := by simp only [piRightHom_smul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  left_inv ψ := by
    ext m
    conv_rhs => rw [← sum_piRightHom_smul ((1 : S) ⊗ₜ m)]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  right_inv v := by
    funext j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.piRightHom_tmul]
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by simp [Pi.single_eq_of_ne hij]) (by simp),
      Pi.single_eq_same, ← Algebra.TensorProduct.one_def, one_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- The comparison map is a base change for a finite free module: under evaluation at the
standard basis it is the base change `Nⁱ → (S ⊗[A] N)ⁱ`. -/
private theorem isBaseChange_mapHom_pi [Finite ι] : IsBaseChange S (mapHom A S Λ (ι → Λ) N) := by
  classical
  cases nonempty_fintype ι
  let e : ((ι → Λ) →ₗ[Λ] N) ≃ₗ[A] (ι → N) := ((Pi.basisFun Λ ι).constr A).symm
  refine (IsBaseChange.iff_of_equiv_comm e (freeHomEquiv A S Λ N ι) ?_).mpr
    (IsBaseChange.pi (fun _ ↦ TensorProduct.mk A S N 1) fun _ ↦ TensorProduct.isBaseChange A N S)
  refine LinearMap.ext fun φ ↦ funext fun i ↦ ?_
  simp [e, freeHomEquiv]

end Free

section Flat

variable [Module.Flat A S]

variable (A S Λ M N) in
/-- **Central flat base change of `Hom`.** For a flat `A`-algebra `S` and a finitely presented
`Λ`-module `M`, the `S ⊗[A] Λ`-linear maps `S ⊗[A] M → S ⊗[A] N` are the base change to `S` of
the `Λ`-linear maps `M → N`, through `φ ↦ 1 ⊗ φ`. -/
theorem isBaseChange_mapHom [Module.FinitePresentation Λ M] :
    IsBaseChange S (mapHom A S Λ M N) := by
  obtain ⟨n, m, π, g, hπ, hgπ⟩ := Module.FinitePresentation.exists_fin' Λ M
  -- `Hom(-, N)` turns the presentation `Λᵐ → Λⁿ → M → 0` and its base change into left exact
  -- sequences, and the comparison is a base change on the two free terms.
  have hgπ' : Function.Exact (map S g : _ →ₗ[S ⊗[A] Λ] S ⊗[A] (Fin n → Λ))
      (map S π : _ →ₗ[S ⊗[A] Λ] S ⊗[A] M) := by
    rw [coe_map, coe_map]
    exact lTensor_exact S hgπ hπ
  let f' : (S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N) →ₗ[S]
      (S ⊗[A] (Fin n → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N) := LinearMap.lcomp S _ (map S π)
  let g' : (S ⊗[A] (Fin n → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N) →ₗ[S]
      (S ⊗[A] (Fin m → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N) := LinearMap.lcomp S _ (map S g)
  have c₁ : (mapHom A S Λ (Fin n → Λ) N).comp (LinearMap.lcomp A N π) =
      (f'.restrictScalars A).comp (mapHom A S Λ M N) := LinearMap.ext fun φ ↦ map_comp φ π
  have c₂ : (mapHom A S Λ (Fin m → Λ) N).comp (LinearMap.lcomp A N g) =
      (g'.restrictScalars A).comp (mapHom A S Λ (Fin n → Λ) N) := LinearMap.ext fun φ ↦ map_comp φ g
  -- The targets are named: inferring them from the comparison maps is very slow.
  exact IsBaseChange.of_left_exact (N₁ := S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N)
    (N₂ := S ⊗[A] (Fin n → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N)
    (N₃ := S ⊗[A] (Fin m → Λ) →ₗ[S ⊗[A] Λ] S ⊗[A] N) S _ _ _ c₁ c₂ isBaseChange_mapHom_pi
    isBaseChange_mapHom_pi (hgπ.lcomp_of_surjective N hπ)
    (LinearMap.lcomp_injective_of_surjective π hπ)
    (hgπ'.lcomp_of_surjective _ (map_surjective S hπ))
    (LinearMap.lcomp_injective_of_surjective _ (map_surjective S hπ))

variable (A S Λ M N) in
/-- The `S`-linear equivalence `S ⊗[A] Hom_Λ(M, N) ≃ Hom_{S ⊗[A] Λ}(S ⊗[A] M, S ⊗[A] N)` for a
flat `A`-algebra `S` and a finitely presented `Λ`-module `M`, sending `s ⊗ φ` to `s • map S φ`. -/
noncomputable def homEquiv [Module.FinitePresentation Λ M] :
    S ⊗[A] (M →ₗ[Λ] N) ≃ₗ[S] (S ⊗[A] M →ₗ[S ⊗[A] Λ] S ⊗[A] N) :=
  (isBaseChange_mapHom A S Λ M N).equiv

@[simp]
theorem homEquiv_tmul [Module.FinitePresentation Λ M] (s : S) (φ : M →ₗ[Λ] N) :
    homEquiv A S Λ M N (s ⊗ₜ φ) = s • map S φ :=
  IsBaseChange.equiv_tmul _ s φ

@[simp]
theorem homEquiv_symm_map [Module.FinitePresentation Λ M] (φ : M →ₗ[Λ] N) :
    (homEquiv A S Λ M N).symm (map S φ) = 1 ⊗ₜ φ :=
  IsBaseChange.equiv_symm_apply _ φ

/-- `homEquiv` is compatible with composition by a `Λ`-linear map `ψ : N → P`. -/
theorem homEquiv_lTensor_compRight [Module.FinitePresentation Λ M] (ψ : N →ₗ[Λ] P)
    (x : S ⊗[A] (M →ₗ[Λ] N)) :
    homEquiv A S Λ M P ((LinearMap.compRight A ψ).lTensor S x) =
      map S ψ ∘ₗ homEquiv A S Λ M N x := by
  induction x using TensorProduct.inductionOn with
  | tmul s φ => simp [map_comp, LinearMap.comp_smul]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]

/-- If `S ⊗[A] M` is projective and `π : Λⁿ → M` is onto, then composition with `π` becomes onto
after base change: `Hom(S ⊗[A] M, S ⊗[A] Λⁿ) → Hom(S ⊗[A] M, S ⊗[A] M)` is onto. -/
private theorem surjective_lTensor_compRight [Module.FinitePresentation Λ M]
    [Module.Projective (S ⊗[A] Λ) (S ⊗[A] M)] {n : ℕ} {π : (Fin n → Λ) →ₗ[Λ] M}
    (hπ : Function.Surjective π) :
    Function.Surjective ((LinearMap.compRight A π :
      (M →ₗ[Λ] (Fin n → Λ)) →ₗ[A] (M →ₗ[Λ] M)).lTensor S) := by
  intro y
  obtain ⟨χ, hχ⟩ :=
    Module.projective_lifting_property (map S π) (homEquiv A S Λ M M y) (map_surjective S hπ)
  refine ⟨(homEquiv A S Λ M (Fin n → Λ)).symm χ, (homEquiv A S Λ M M).injective ?_⟩
  rw [homEquiv_lTensor_compRight, LinearEquiv.apply_symm_apply, hχ]

end Flat

variable (S) in
/-- **Faithfully flat descent of projectivity.** A finitely presented `Λ`-module `M` is
projective if `S ⊗[A] M` is a projective `S ⊗[A] Λ`-module for a faithfully flat `A`-algebra
`S`. -/
theorem projective_of_faithfullyFlat [Module.FaithfullyFlat A S] [Module.FinitePresentation Λ M]
    [Module.Projective (S ⊗[A] Λ) (S ⊗[A] M)] : Module.Projective Λ M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  -- `π` splits as soon as composition with `π` is onto `Hom(M, M)`, which faithful flatness
  -- reflects from the base change.
  obtain ⟨σ, hσ⟩ := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A S _).mp
    (surjective_lTensor_compRight (S := S) hπ) LinearMap.id
  exact Module.Projective.of_split σ π hσ

universe v in
/-- **Descent of projectivity along a detecting family.** Let `A` be noetherian, and let `S i`
be flat `A`-algebras that jointly detect the vanishing of finitely generated `A`-modules: a
finitely generated `A`-module `C` vanishes as soon as every `S i ⊗[A] C` does. For flat `S i`
this is the same as jointly detecting exactness of sequences of finitely generated
`A`-modules. A finitely presented `Λ`-module `M` that is finite over `A` is projective if every
`S i ⊗[A] M` is a projective `S i ⊗[A] Λ`-module.

The detection hypothesis is only used for `A`-modules in the universe of `M`. -/
theorem projective_of_forall_projective {M : Type v} [AddCommGroup M] [Module A M] [Module Λ M]
    [IsScalarTower A Λ M] {ι : Type*} (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra A (S i)] [∀ i, Module.Flat A (S i)]
    (hS : ∀ (C : Type v) [AddCommGroup C] [Module A C] [Module.Finite A C],
      (∀ i, Subsingleton (S i ⊗[A] C)) → Subsingleton C)
    [IsNoetherianRing A] [Module.Finite A M] [Module.FinitePresentation Λ M]
    [∀ i, Module.Projective (S i ⊗[A] Λ) (S i ⊗[A] M)] : Module.Projective Λ M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  let c : (M →ₗ[Λ] (Fin n → Λ)) →ₗ[A] (M →ₗ[Λ] M) := LinearMap.compRight A π
  -- `M →ₗ[Λ] M` embeds into the finitely generated `A`-module `(Fin n → Λ) →ₗ[Λ] M`.
  have : IsNoetherian A (M →ₗ[Λ] M) :=
    isNoetherian_of_injective (LinearMap.lcomp A M π) (LinearMap.lcomp_injective_of_surjective π hπ)
  -- The cokernel of `c` is finitely generated and vanishes after every base change, since `c`
  -- becomes onto there.
  have hc : LinearMap.range c = ⊤ := by
    refine Submodule.Quotient.subsingleton_iff.mp (hS _ fun i ↦ ?_)
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (S i) (LinearMap.range c).mkQ_surjective y
    obtain ⟨z, rfl⟩ := surjective_lTensor_compRight (S := S i) hπ x
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨σ, hσ⟩ := LinearMap.range_eq_top.mp hc LinearMap.id
  exact Module.Projective.of_split σ π hσ

end TauCeti.CentralBaseChange
