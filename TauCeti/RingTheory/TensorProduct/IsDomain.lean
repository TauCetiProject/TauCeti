/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.FiniteType.PointSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Adjoin.FG
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Tensor products over a field that are domains

Let `K` be a field. If `A` is a `K`-algebra and `L` a `K`-algebra with `A ⊗[K] L` a domain, then
`B ⊗[K] L` is again a domain for every localization `B` of `A` at nonzero elements, since it is the
localization of `A ⊗[K] L` at their images, which stay nonzero because `A ⟶ A ⊗[K] L` is injective.
In particular this passes from a domain `A` to its fraction field: if `A ⊗[K] L` is a domain then
so is `Frac(A) ⊗[K] L`. This is how the function field of an integral scheme over `K` inherits
"geometric integrality" from the coordinate rings of its affine opens.

As an instance of this, for any `K`-algebra `D` that is a domain and any set of variables `σ`, the
tensor product `K(X_σ) ⊗[K] D` of `D` with the rational function field
`K(X_σ) = FractionRing (MvPolynomial σ K)` is again a domain. Indeed, `K[X_σ] ⊗[K] D` is the
polynomial ring `D[X_σ]`, a domain.

Since every field extension is algebraic over a purely transcendental one, this is the purely
transcendental half of the comparison between the irreducible components of a scheme over `K`
and those of its extension of scalars to a field extension of `K`.

Over an algebraically closed field `K`, the tensor product of a commutative domain with any domain
`K`-algebra is a domain (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`); the second factor need
not be commutative. In particular, the spectrum of a commutative domain over `K` stays
irreducible after any extension of scalars, which is why
the irreducible components of a geometric fibre do not depend on the chosen algebraically closed
field.

## Main results

* `TauCeti.isDomain_tensorProduct_of_isLocalization`: localizing the first factor at nonzero
  divisors preserves domains.
* `TauCeti.isDomain_fractionRing_mvPolynomial_tensorProduct`: a rational function field over `K`
  tensored with a domain is a domain.
* `TauCeti.isDomain_tensorProduct_of_isAlgClosed`: over an algebraically closed field, the tensor
  product of two domains is a domain.

## References

* The Stacks Project, Chapter *Commutative Algebra*, Section *Geometrically irreducible
  algebras*.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K]

/-- Let `B` be a localization of the `K`-algebra `A` at a submonoid of nonzero divisors. If
`A ⊗[K] L` is a domain, then so is `B ⊗[K] L`. -/
theorem isDomain_tensorProduct_of_isLocalization {A : Type*} [CommRing A] [Algebra K A]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) (B : Type*) [CommRing B] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [IsLocalization M B] (L : Type*) [CommRing L]
    [Algebra K L] [IsDomain (A ⊗[K] L)] : IsDomain (B ⊗[K] L) := by
  have : Nontrivial A :=
    (Algebra.TensorProduct.includeLeft (R := K) (S := K) (B := L)).domain_nontrivial
  have : Nontrivial L := (Algebra.TensorProduct.includeRight (R := K) (A := A)).domain_nontrivial
  let φ : A ⊗[K] L →ₐ[K] B ⊗[K] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A B) (AlgHom.id K L)
  algebraize [φ.toRingHom]
  have : IsScalarTower A (A ⊗[K] L) (B ⊗[K] L) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] L) M) (B ⊗[K] L) :=
    IsLocalization.tensorProduct_tensorProduct K L M B
      (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  -- `A ⟶ A ⊗[K] L` is injective, so it carries the nonzero divisors `M` to nonzero elements.
  have hinj : Function.Injective (algebraMap A (A ⊗[K] L)) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Algebra.algebraMapSubmonoid (A ⊗[K] L) M) (map_le_nonZeroDivisors_of_injective _ hinj hM)

/-- The tensor product of a domain over a field `K` with a rational function field over `K` is a
domain. -/
instance isDomain_fractionRing_mvPolynomial_tensorProduct {σ D : Type*} [CommRing D] [IsDomain D]
    [Algebra K D] : IsDomain (FractionRing (MvPolynomial σ K) ⊗[K] D) := by
  have : IsDomain (MvPolynomial σ K ⊗[K] D) :=
    ((Algebra.TensorProduct.comm K _ D).trans
      ((MvPolynomial.algebraTensorAlgEquiv K D).restrictScalars K)).toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (MvPolynomial σ K)) le_rfl _ D

/-- Over an algebraically closed field, a finitely generated domain tensored with a domain has no
zero divisors. This is the finitely generated case of `isDomain_tensorProduct_of_isAlgClosed`. -/
private theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType [IsAlgClosed K]
    {A B : Type*} [CommRing A] [NoZeroDivisors A] [Algebra K A] [Algebra.FiniteType K A]
    [Ring B] [NoZeroDivisors B] [Algebra K B] {x y : A ⊗[K] B} (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  -- The proof is the weak Nullstellensatz. If `x` and `y` are nonzero, linear functionals on `B`
  -- give nonzero coefficients `a` and `c` of `x` and `y` in `A`. A `K`-point `φ` of `A` with
  -- `φ (a * c) ≠ 0` then specializes `x` and `y` to nonzero elements of the domain `B`.
  -- The coefficient in `A` of a tensor along a linear functional `ℓ` on `B`.
  let c (ℓ : Module.Dual K B) : A ⊗[K] B →ₗ[K] A :=
    (TensorProduct.lid K A).toLinearMap ∘ₗ ℓ.rTensor A ∘ₗ (TensorProduct.comm K A B).toLinearMap
  have hc (z : A ⊗[K] B) (hz : z ≠ 0) : ∃ ℓ, c ℓ z ≠ 0 := by
    by_contra! H
    refine hz ((TensorProduct.comm K A B).injective ?_)
    rw [map_zero]
    refine tensor_eq_zero_of_forall_rTensor_eq_zero (fun ℓ : Module.Dual K B ↦ ℓ)
      (fun b hb ↦ (Module.forall_dual_apply_eq_zero_iff K b).mp hb) _ fun ℓ ↦ ?_
    simpa [c] using H ℓ
  -- The specialization of the first factor at a `K`-point `φ` of `A`.
  let Φ (φ : A →ₐ[K] K) : A ⊗[K] B →ₐ[K] B :=
    (Algebra.TensorProduct.lid K B).toAlgHom.comp (Algebra.TensorProduct.map φ (AlgHom.id K B))
  have hΦ (φ : A →ₐ[K] K) (ℓ : Module.Dual K B) (z : A ⊗[K] B) : ℓ (Φ φ z) = φ (c ℓ z) := by
    induction z with
    | tmul a b => simp [Φ, c, mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  by_contra! hxy
  obtain ⟨ℓ, hℓ⟩ := hc x hxy.1
  obtain ⟨ℓ', hℓ'⟩ := hc y hxy.2
  obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_ne_zero (k := K) (K := K)
    (mul_ne_zero hℓ hℓ')
  rw [map_mul] at hφ
  have hx : Φ φ x ≠ 0 := fun h0 ↦ left_ne_zero_of_mul hφ (by rw [← hΦ, h0, map_zero])
  have hy : Φ φ y ≠ 0 := fun h0 ↦ right_ne_zero_of_mul hφ (by rw [← hΦ, h0, map_zero])
  exact mul_ne_zero hx hy (by rw [← map_mul, h, map_zero])

/-- Tensoring a commutative domain over an algebraically closed field with any domain algebra
gives a domain. The second factor need not be commutative. -/
instance isDomain_tensorProduct_of_isAlgClosed [IsAlgClosed K] (A B : Type*) [CommRing A]
    [IsDomain A] [Algebra K A] [Ring B] [IsDomain B] [Algebra K B] :
    IsDomain (A ⊗[K] B) := by
  have : Nontrivial (A ⊗[K] B) :=
    (Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K B).injective).nontrivial
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} h ↦ ?_⟩
  -- Both factors come from `A₀ ⊗[K] B` for a finitely generated subalgebra `A₀` of `A`.
  obtain ⟨M, hM, hxy⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {x, y} (Set.toFinite _)
  obtain ⟨s, rfl⟩ := Module.Finite.iff_fg.mp hM
  let A₀ := Algebra.adjoin K (s : Set A)
  have : Algebra.FiniteType K A₀ :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  have hle : Submodule.span K (s : Set A) ≤ Subalgebra.toSubmodule A₀ := Algebra.span_le_adjoin K _
  let ι : A₀ ⊗[K] B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.map A₀.val (AlgHom.id K B)
  have hι : Function.Injective ι :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) A₀.val.toLinearMap
      Subtype.val_injective
  have hcomp (w : Submodule.span K (s : Set A) ⊗[K] B) :
      ι ((Submodule.inclusion hle).rTensor B w) =
        (Submodule.span K (s : Set A)).subtype.rTensor B w := by
    induction w with
    | tmul m b => simp [ι]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  have hrange (z : A ⊗[K] B) (hz : z ∈ ({x, y} : Set (A ⊗[K] B))) : ∃ z₀, ι z₀ = z := by
    obtain ⟨w, rfl⟩ := hxy hz
    exact ⟨_, hcomp w⟩
  obtain ⟨x₀, rfl⟩ := hrange x (by simp)
  obtain ⟨y₀, rfl⟩ := hrange y (by simp)
  rw [← map_mul, ← map_zero ι] at h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType (hι h) with h0 | h0
  · exact .inl (by rw [h0, map_zero])
  · exact .inr (by rw [h0, map_zero])

end TauCeti
