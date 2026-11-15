/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Module.Injective.Dual
import TauCeti.Algebra.Module.Injective.DivisionRing

/-!
# Projective and injective modules over a Frobenius algebra coincide

Let `A` be a finite-dimensional algebra over a field `k` with a Frobenius functional `φ`. This file
proves that an arbitrary left `A`-module, not necessarily finitely generated, is projective if and
only if it is injective.

The key point is that over a Frobenius algebra induced and coinduced modules agree: for every
`k`-vector space `V` the map `a ⊗ v ↦ (x ↦ φ (x * a) • v)` is an isomorphism of left `A`-modules
`A ⊗[k] V ≅ Hom_k(A, V)`, where `A` acts on `A ⊗[k] V` through the left factor and on
`Hom_k(A, V)` by `(a • f) x = f (x * a)`. Consequently:

* induced modules `A ⊗[k] V` are injective, since coinduced modules are, see
  `TauCeti.Algebra.Module.Injective.Dual`; every free module is induced, so projective modules,
  being retracts of free modules, are injective;
* every module `M` embeds into the coinduced module `Hom_k(A, M)` by `m ↦ (x ↦ x • m)`, hence into
  the free module `A ⊗[k] M`; when `M` is injective this embedding splits, so `M` is projective.

For finite-dimensional modules this is also a consequence of self-injectivity alone, see
`TauCeti.Algebra.Category.FGModuleCat.Frobenius`; the point here is that no finiteness is
assumed on the module.

## Main definitions

* `LinearMap.IsFrobeniusFunctional.tensorEquivLinearMap`: the isomorphism
  `A ⊗[k] V ≃ₗ[k] (A →ₗ[k] V)` between the induced and the coinduced module.

## Main results

* `LinearMap.IsFrobeniusFunctional.tensorEquivLinearMap_smul_apply`: the isomorphism is
  `A`-linear.
* `LinearMap.IsFrobeniusFunctional.moduleInjective_tensor`: induced modules are injective.
* `LinearMap.IsFrobeniusFunctional.moduleInjective_of_projective`: projective modules are
  injective.
* `LinearMap.IsFrobeniusFunctional.moduleProjective_of_injective`: injective modules are
  projective.
* `LinearMap.IsFrobeniusFunctional.moduleProjective_iff_moduleInjective`: the two classes
  coincide.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Section 15 (quasi-Frobenius rings, where projective
  and injective modules coincide) and Section 16 (Frobenius algebras).
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
-/

public section

open TensorProduct

namespace LinearMap.IsFrobeniusFunctional

universe u v w

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
  {φ : A →ₗ[k] k}

variable (hφ : φ.IsFrobeniusFunctional)
include hφ

section Tensor

variable (V : Type*) [AddCommGroup V] [Module k V]

/-- **Induced and coinduced modules agree over a Frobenius algebra.** The `k`-linear isomorphism
`A ⊗[k] V ≃ₗ[k] (A →ₗ[k] V)` sending `a ⊗ v` to `x ↦ φ (x * a) • v`. It intertwines the action of
`A` on the left factor of `A ⊗[k] V` with the action `(a • f) x = f (x * a)` on `Hom_k(A, V)`, see
`LinearMap.IsFrobeniusFunctional.tensorEquivLinearMap_smul_apply`. -/
noncomputable def tensorEquivLinearMap : A ⊗[k] V ≃ₗ[k] (A →ₗ[k] V) :=
  TensorProduct.congr
      (LinearEquiv.ofBijective ((mul k A).compr₂ φ).flip hφ.isPerfPair.bijective_right)
      (LinearEquiv.refl k V) ≪≫ₗ dualTensorHomEquiv k A V

@[simp]
theorem tensorEquivLinearMap_tmul_apply (a : A) (v : V) (x : A) :
    hφ.tensorEquivLinearMap V (a ⊗ₜ v) x = φ (x * a) • v := by
  simp [tensorEquivLinearMap, LinearEquiv.ofBijective_apply]

/-- The isomorphism `A ⊗[k] V ≃ₗ[k] (A →ₗ[k] V)` is `A`-linear, for the action of `A` on the left
factor of the tensor product and the action `(c • f) x = f (x * c)` on linear maps. -/
@[simp]
theorem tensorEquivLinearMap_smul_apply (c : A) (t : A ⊗[k] V) (x : A) :
    hφ.tensorEquivLinearMap V (c • t) x = hφ.tensorEquivLinearMap V t (x * c) := by
  induction t with
  | tmul a v => simp [smul_tmul', mul_assoc]
  | add t u ht hu => simp only [smul_add, map_add, LinearMap.add_apply, ht, hu]

end Tensor

/-- **Induced modules over a Frobenius algebra are injective.** For every `k`-vector space `V`
in a universe in which `k` is small, the left `A`-module `A ⊗[k] V` is injective. -/
theorem moduleInjective_tensor [Small.{w} k] (V : Type w) [AddCommGroup V] [Module k V] :
    Module.Injective A (A ⊗[k] V) :=
  (hφ.tensorEquivLinearMap V).moduleInjective_of_dual_regular
    (hφ.tensorEquivLinearMap_smul_apply V)

/-- **Projective modules over a Frobenius algebra are injective.** No finiteness is assumed on
the module. -/
theorem moduleInjective_of_projective (P : Type w) [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.Injective A P := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A P)
  -- The free module `P →₀ A` is the induced module `A ⊗[k] (P →₀ k)`.
  let b := Algebra.TensorProduct.basis A (Finsupp.basisSingleOne : Module.Basis P k (P →₀ k))
  have : Small.{max w u} k := small_max.{w} k
  have : Small.{max u v w} A := small_max.{max u w} A
  have hB : Module.Baer A (P →₀ A) :=
    (Module.Baer.of_injective (hφ.moduleInjective_tensor (P →₀ k))).of_equiv b.repr
  have hP : Module.Baer A P :=
    hB.of_leftInverse s (Finsupp.linearCombination A fun p : P ↦ p) (LinearMap.congr_fun hs)
  exact hP.injective

/-- **Injective modules over a Frobenius algebra are projective.** No finiteness is assumed on
the module; the universe hypothesis `Small.{w} A` is the one under which `Module.Injective`
quantifies over enough modules. -/
theorem moduleProjective_of_injective [Small.{w} A] (M : Type w) [AddCommGroup M]
    [Module A M] [Module.Injective A M] : Module.Projective A M := by
  -- `M` is a `k`-vector space through the structure map `k → A`.
  let : Module k M := Module.compHom M (algebraMap k A)
  have : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := hφ.tensorEquivLinearMap M
  -- The embedding `m ↦ (x ↦ x • m)` of `M` into the coinduced module, read in `A ⊗[k] M`.
  let ι : M →ₗ[A] A ⊗[k] M :=
    { toFun m := e.symm ((LinearMap.toSpanSingleton A M m).restrictScalars k)
      map_add' m n := by apply e.injective; ext x; simp
      map_smul' c m := by
        apply e.injective
        ext x
        simp [e, tensorEquivLinearMap_smul_apply, mul_smul] }
  have hι : Function.Injective ι := fun m n h ↦ by
    simpa [ι] using LinearMap.congr_fun (congrArg e h) 1
  have : Module.Free A (A ⊗[k] M) :=
    .of_basis (Algebra.TensorProduct.basis A (Module.Free.chooseBasis k M))
  obtain ⟨g, hg⟩ := Module.Injective.extension_property A M _ _ ι hι LinearMap.id
  exact .of_split ι g hg

/-- **Projective and injective modules over a Frobenius algebra coincide**: a left module over a
finite-dimensional algebra with a Frobenius functional, not necessarily finitely generated, is
projective if and only if it is injective. -/
theorem moduleProjective_iff_moduleInjective [Small.{w} A] (M : Type w) [AddCommGroup M]
    [Module A M] : Module.Projective A M ↔ Module.Injective A M :=
  ⟨fun _ ↦ hφ.moduleInjective_of_projective M, fun _ ↦ hφ.moduleProjective_of_injective M⟩

end LinearMap.IsFrobeniusFunctional
