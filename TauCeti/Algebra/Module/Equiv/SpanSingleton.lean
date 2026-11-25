/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Ideal.Span

/-!
# Generators of a module isomorphic to the base ring

A generator of a module `N`, that is an element `x` with `span K {x} = ⊤`, is carried by a linear
isomorphism `N ≃ₗ[K] K` to a generator of the ideal `⊤`, that is to a unit of `K`
(`Submodule.span_image_linearEquiv`, `Ideal.span_singleton_eq_top`). So when `1` is the only unit
of the semiring `K`, as for `ZMod 2`, and one-sided inverses in `K` are inverses, a module
isomorphic to `K` has exactly one generator. This is what makes Thom classes with such
coefficients unique on every fibre, without any orientation.

Conversely, a linear functional `Ψ` on a module `N ≃ₗ[K] K` taking the value `1` on `x` makes `x`
a generator: `Ψ` factors through the isomorphism as multiplication by `Ψ (e⁻¹ 1)`, so `e x` is a
unit of `K` and `a ↦ a • x` is bijective.

## Main results

* `LinearEquiv.span_singleton_apply_eq_top_iff`: a linear equivalence carries generators to
  generators.
* `LinearEquiv.span_singleton_eq_top_iff_isUnit`: an element of a module isomorphic to the base
  ring generates it exactly when its image is a unit.
* `LinearEquiv.span_singleton_tmul_eq_top_iff`: a pure tensor generates a tensor product of two
  modules isomorphic to the base ring exactly when both factors generate.
* `LinearEquiv.exists_units_smul_eq_of_span_singleton_eq_top`: any two generators of a module
  isomorphic to the base ring differ by a unit.
* `LinearEquiv.eq_of_span_singleton_eq_top`: a module isomorphic to a Dedekind-finite semiring
  (for instance a commutative one) whose only unit is `1` has a single generator.
* `LinearEquiv.isUnit_apply_of_apply_eq_one`, `LinearEquiv.bijective_smul_of_apply_eq_one`: an
  element on which a linear functional takes the value `1` is carried to a unit, and generates
  freely.
* `LinearMap.span_singleton_apply_eq_top_of_leftInverse`: a linear map between modules isomorphic
  to the base ring which has a left inverse carries generators to generators.
* `LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top`: any linear map between
  modules isomorphic to the base ring reflects generators.
* `LinearMap.eq_id_of_apply_eq_self`: over a domain, an endomorphism of a module isomorphic to the
  base ring which fixes a nonzero element is the identity.

An endomorphism of a module isomorphic to the base ring is right multiplication by an element in
coordinates, which is how the last result is proved. The last two results are used to compare top
and local homology of manifolds, where local homology is a copy of the coefficient ring.
-/

public section

namespace LinearEquiv

/-- A linear equivalence carries generators to generators: `e x` spans the codomain if and only if
`x` spans the domain. -/
theorem span_singleton_apply_eq_top_iff {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) {x : M} :
    Submodule.span R {e x} = ⊤ ↔ Submodule.span R {x} = ⊤ := by
  rw [← Set.image_singleton, Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

/-- **Generators of a module isomorphic to the base ring are units**: for `e : M ≃ₗ[R] R`, an
element `x` spans `M` if and only if `e x` is a unit of `R`. Over a noncommutative ring this needs
every left inverse to be a two-sided inverse. -/
theorem span_singleton_eq_top_iff_isUnit {R M : Type*} [Semiring R] [IsDedekindFiniteMonoid R]
    [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] R) {x : M} :
    Submodule.span R {x} = ⊤ ↔ IsUnit (e x) := by
  rw [← e.span_singleton_apply_eq_top_iff, Ideal.eq_top_iff_one, Submodule.mem_span_singleton,
    isUnit_iff_exists_inv']
  simp only [smul_eq_mul]

/-- **Any two generators of a module isomorphic to the base ring differ by a unit**: for
`e : M ≃ₗ[R] R`, if `x` and `y` both span `M`, then `(u : R) • x = y` for some unit `u : Rˣ`. -/
theorem exists_units_smul_eq_of_span_singleton_eq_top {R M : Type*} [Semiring R]
    [IsDedekindFiniteMonoid R] [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] R) {x y : M}
    (hx : Submodule.span R {x} = ⊤) (hy : Submodule.span R {y} = ⊤) :
    ∃ u : Rˣ, (u : R) • x = y := by
  have hux : IsUnit (e x) := e.span_singleton_eq_top_iff_isUnit.1 hx
  have huy : IsUnit (e y) := e.span_singleton_eq_top_iff_isUnit.1 hy
  refine ⟨huy.unit * hux.unit⁻¹, e.injective ?_⟩
  simp [smul_eq_mul, mul_assoc]

/-- **A module isomorphic to `K` has a single generator when `1` is the only unit of `K`**: two
elements `x` and `y` of a module `N ≃ₗ[K] K` with `span K {x} = ⊤` and `span K {y} = ⊤` are
equal. Over a noncommutative ring this needs every left inverse to be a two-sided inverse. -/
theorem eq_of_span_singleton_eq_top {K N : Type*} [Semiring K] [IsDedekindFiniteMonoid K]
    [Subsingleton Kˣ] [AddCommMonoid N] [Module K N] (φ : N ≃ₗ[K] K) {x y : N}
    (hx : Submodule.span K {x} = ⊤) (hy : Submodule.span K {y} = ⊤) : x = y := by
  obtain ⟨u, rfl⟩ := φ.exists_units_smul_eq_of_span_singleton_eq_top hx hy
  rw [Subsingleton.elim u 1, Units.val_one, one_smul]

/-- If a linear functional `Ψ` on a module `N ≃ₗ[K] K` takes the value `1` on `x`, then `e x` is a
unit of `K`, with inverse `Ψ (e⁻¹ 1)`. -/
theorem isUnit_apply_of_apply_eq_one {K N : Type*} [CommSemiring K] [AddCommMonoid N]
    [Module K N] (e : N ≃ₗ[K] K) (Ψ : N →ₗ[K] K) {x : N} (hx : Ψ x = 1) : IsUnit (e x) := by
  -- `x = e x • e⁻¹ 1`, so `Ψ x = e x * Ψ (e⁻¹ 1)`.
  have hxe : x = e x • e.symm 1 := by simp [← map_smul]
  exact IsUnit.of_mul_eq_one (Ψ (e.symm 1)) <| by simpa [hx] using (congrArg Ψ hxe).symm

/-- If a linear functional `Ψ` on a module `N ≃ₗ[K] K` takes the value `1` on `x`, then
`a ↦ a • x` is bijective. -/
theorem bijective_smul_of_apply_eq_one {K N : Type*} [CommSemiring K] [AddCommMonoid N]
    [Module K N] (e : N ≃ₗ[K] K) (Ψ : N →ₗ[K] K) {x : N} (hx : Ψ x = 1) :
    Function.Bijective fun a : K ↦ a • x := by
  -- `a ↦ a • x` is `a ↦ e⁻¹ (a * e x)`, a composite of bijections.
  convert e.symm.bijective.comp
    (Units.mulRight (e.isUnit_apply_of_apply_eq_one Ψ hx).unit).bijective using 1
  funext a
  simp [← smul_eq_mul]

open scoped TensorProduct in
/-- **A pure tensor generates a tensor product of modules isomorphic to the base ring exactly when
both factors generate.** For `eM : M ≃ₗ[R] R` and `eN : N ≃ₗ[R] R`, the pure tensor `x ⊗ y` spans
`M ⊗[R] N` if and only if `x` spans `M` and `y` spans `N`. -/
theorem span_singleton_tmul_eq_top_iff {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R) {x : M}
    {y : N} :
    Submodule.span R {x ⊗ₜ[R] y} = ⊤ ↔
      Submodule.span R {x} = ⊤ ∧ Submodule.span R {y} = ⊤ := by
  rw [span_singleton_eq_top_iff_isUnit ((TensorProduct.congr eM eN).trans (TensorProduct.lid R R)),
    span_singleton_eq_top_iff_isUnit eM, span_singleton_eq_top_iff_isUnit eN]
  simp [IsUnit.mul_iff]

end LinearEquiv

namespace LinearMap

/-- **Split monomorphisms between modules isomorphic to the base ring carry generators to
generators.** If `f : M →ₗ[R] N` has a left inverse `g` and `M` and `N` are both isomorphic to the
commutative semiring `R`, then `f x` spans `N` whenever `x` spans `M`: the coordinate `eM x` is a
unit `u`, and the functional `u⁻¹ • (eM ∘ g)` takes the value `1` on `f x`
(`LinearEquiv.isUnit_apply_of_apply_eq_one`). -/
theorem span_singleton_apply_eq_top_of_leftInverse {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R) {g : N →ₗ[R] M} (hgf : Function.LeftInverse g f) {x : M}
    (hx : Submodule.span R {x} = ⊤) : Submodule.span R {f x} = ⊤ := by
  obtain ⟨u, hu⟩ := eM.span_singleton_eq_top_iff_isUnit.1 hx
  refine eN.span_singleton_eq_top_iff_isUnit.2
    (eN.isUnit_apply_of_apply_eq_one ((↑u⁻¹ : R) • (eM.toLinearMap ∘ₗ g)) ?_)
  simp [hgf x, ← hu]

/-- **Linear maps between modules isomorphic to the base ring reflect generators.** If
`f : M →ₗ[R] N` and both `M` and `N` are isomorphic to the commutative semiring `R`, then `x`
spans `M` whenever `f x` spans `N`: in coordinates `f` is multiplication by `eN (f (eM⁻¹ 1))`, so
the unit `eN (f x)` is the product of `eM x` with it, and `eM x` is a unit. -/
theorem span_singleton_eq_top_of_span_singleton_apply_eq_top {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R) {x : M} (hx : Submodule.span R {f x} = ⊤) :
    Submodule.span R {x} = ⊤ := by
  have hxe : x = eM x • eM.symm 1 := by simp [← map_smul]
  have hu := eN.span_singleton_eq_top_iff_isUnit.1 hx
  rw [hxe, map_smul, map_smul, smul_eq_mul] at hu
  exact eM.span_singleton_eq_top_iff_isUnit.2 (isUnit_of_mul_isUnit_left hu)

/-- **An endomorphism of a module isomorphic to the base ring fixing a nonzero element is the
identity**, over a domain: in coordinates it is right multiplication by an element `a`, and
`t * a = t` with `t ≠ 0` forces `a = 1`. -/
theorem eq_id_of_apply_eq_self {R M : Type*} [Semiring R] [IsDomain R] [AddCommMonoid M]
    [Module R M] (T : M →ₗ[R] M) (e : M ≃ₗ[R] R) {x : M} (hx : x ≠ 0) (hTx : T x = x) :
    T = LinearMap.id := by
  set T' : R →ₗ[R] R := e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap
  have hT' (t : R) : T' t = t * T' 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hT'e (y : M) : T' (e y) = e (T y) := by simp [T']
  -- `T' 1 = 1`, by cancelling the nonzero coordinate of `x`.
  have h1 : T' 1 = 1 := by
    have h := hT'e x
    rw [hTx, hT'] at h
    exact mul_left_cancel₀ ((LinearEquiv.map_ne_zero_iff e).2 hx) (h.trans (mul_one (e x)).symm)
  ext y
  apply e.injective
  rw [← hT'e, hT', h1, mul_one, LinearMap.id_apply]

end LinearMap
