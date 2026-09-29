/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The tame-frame module

For two elements `σ, τ` of a monoid `G` and two coefficients `a, b` in a ring `R`, the
**tame-frame module** is the left `R[G]`-module with two generators and one relation,

`M₀ = R[G]² / R[G]·(σ - a, τ - b)`.

In the computation of the generator rank of the absolute Galois group of a `p`-adic field
(NSW (7.4.1)), `R = ℤ_p`, `σ, τ` are the images in a finite Galois group of the two tame
generators of the absolute Galois group, and `a, b` are exponents through which they act on the
`p`-power roots of unity. The module is a quotient of `R[G]²`, which is where the `2` in the
generator count `[K : ℚ_p] + 2` comes from.

The module is characterised by its universal property: a left `R[G]`-linear map out of `M₀` is a
pair of elements `x, y` of the target with `(σ - a) x + (τ - b) y = 0`, the images of the two
generators `e₀, e₁`, the classes of the standard basis vectors of `R[G]²`.

## Main definitions

* `TauCeti.MonoidAlgebra.TameFrameModule`: the quotient `R[G]² / R[G]·(σ - a, τ - b)`.
* `TauCeti.MonoidAlgebra.TameFrameModule.lift`: the linear map out of `M₀` sending the generators
  to `x, y`.

## Main statements

* `TauCeti.MonoidAlgebra.TameFrameModule.mk_relation`: the generators satisfy
  `(σ - a) e₀ + (τ - b) e₁ = 0`.
* `TauCeti.MonoidAlgebra.TameFrameModule.lift_mk`: the defining equation of `lift`.
* `TauCeti.MonoidAlgebra.TameFrameModule.hom_ext`: a linear map out of `M₀` is determined by the
  images of the two generators.

## Implementation notes

Mathlib's `Module.Relations` presents the same module, with generator type `Fin 2` and one
relation. Its generator type is a structure field: for a semireducible system it unfolds to
`Fin 2` only at default transparency, so terms such as `Finsupp.single (0 : Fin 2) 1` indexing the
generators are not type-correct at the transparency `simp` works at; for a reducible system the
field reduces to `Fin 2` and no longer matches the keys of the `Module.Relations.Quotient` simp
lemmas such as `Module.Relations.Solution.fromQuotient_toQuotient`. The quotient of `Fin 2 → R[G]`
is used directly instead, and its universal property is proved here.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

universe u v

variable (R : Type u) [Ring R] (G : Type v) [Monoid G]

/-- The **tame-frame module** `M₀ = R[G]² / R[G]·(σ - a, τ - b)` of two elements `σ, τ` of `G` and
two coefficients `a, b` of `R`: the left `R[G]`-module on two generators `e₀, e₁` subject to the
single relation `(σ - a) e₀ + (τ - b) e₁ = 0`. -/
abbrev TameFrameModule (σ τ : G) (a b : R) : Type (max u v) :=
  (Fin 2 → MonoidAlgebra R G) ⧸ Submodule.span (MonoidAlgebra R G)
    {![single σ (1 : R) - single 1 a, single τ (1 : R) - single 1 b]}

namespace TameFrameModule

variable {R G} {σ τ : G} {a b : R}

/-- The two generators `e₀, e₁` of the tame-frame module satisfy `(σ - a) e₀ + (τ - b) e₁ = 0`. -/
theorem mk_relation :
    (single σ (1 : R) - single 1 a) •
        (Submodule.Quotient.mk (Pi.single 0 1) : TameFrameModule R G σ τ a b) +
      (single τ (1 : R) - single 1 b) •
        (Submodule.Quotient.mk (Pi.single 1 1) : TameFrameModule R G σ τ a b) = 0 := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_eq_zero]
  convert Submodule.mem_span_singleton_self _ using 1
  ext i
  fin_cases i <;> simp

variable {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra R G) M]

/-- The left `R[G]`-linear map out of the tame-frame module sending the generators `e₀, e₁` to
`x, y`, for `x, y` satisfying the relation `(σ - a) x + (τ - b) y = 0`. -/
noncomputable def lift (x y : M)
    (h : (single σ (1 : R) - single 1 a) • x + (single τ (1 : R) - single 1 b) • y = 0) :
    TameFrameModule R G σ τ a b →ₗ[MonoidAlgebra R G] M :=
  Submodule.liftQ _ (Fintype.linearCombination (MonoidAlgebra R G) ![x, y]) <| by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      Fintype.linearCombination_apply, Fin.sum_univ_two]
    simpa using h

/-- The defining equation of `TameFrameModule.lift`: the class of `(c₀, c₁)` is sent to
`c₀ x + c₁ y`. -/
@[simp]
theorem lift_mk (x y : M)
    (h : (single σ (1 : R) - single 1 a) • x + (single τ (1 : R) - single 1 b) • y = 0)
    (c : Fin 2 → MonoidAlgebra R G) :
    lift x y h (Submodule.Quotient.mk c : TameFrameModule R G σ τ a b) = c 0 • x + c 1 • y := by
  simp [lift, Fintype.linearCombination_apply, Fin.sum_univ_two]

/-- A left `R[G]`-linear map out of the tame-frame module is determined by the images of the two
generators `e₀, e₁`. -/
theorem hom_ext {f f' : TameFrameModule R G σ τ a b →ₗ[MonoidAlgebra R G] M}
    (h₀ : f (Submodule.Quotient.mk (Pi.single 0 1)) = f' (Submodule.Quotient.mk (Pi.single 0 1)))
    (h₁ : f (Submodule.Quotient.mk (Pi.single 1 1)) = f' (Submodule.Quotient.mk (Pi.single 1 1))) :
    f = f' := by
  apply Submodule.linearMap_qext
  refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
  fin_cases i
  exacts [h₀, h₁]

end TameFrameModule

end TauCeti.MonoidAlgebra
