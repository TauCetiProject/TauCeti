/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.Coalgebra.Star

/-!
# The antipode of a Hopf star algebra

A Hopf star algebra is a Hopf algebra `A` over a commutative star ring `R` with a compatible
star algebra structure (`StarRing A`, `StarModule R A`) whose comultiplication is a star map
(`TauCeti.StarCoalgebra R A`). In such an algebra the antipode is always bijective, with inverse
`a ↦ S(a*)*`:

`S(S(a*)*) = a` and `S(S(a)*)* = a`.

The first identity says that `S ∘ T` is the identity for `T(a) = S(a*)*`. Writing
`Δ a = ∑ xᵢ ⊗ yᵢ`, the star of the antipode law `∑ xᵢ* S(yᵢ*) = ε(a*)` together with
`ε(a*) = conj (ε a)` gives `∑ T(yᵢ) xᵢ = ε(a)`. Applying the antimultiplicative `S` shows
that `S ∘ T` is a right convolution inverse of `S`, and `id` is a left convolution inverse of `S`,
so `S ∘ T = id`. The second identity is the first one conjugated by `star`.

No positivity is involved: these are the purely algebraic consequences of the axioms, used
before any Haar state or completion is constructed.

## Main declarations

* `TauCeti.HopfAlgebra.antipode_star_antipode_star`: `S(S(a*)*) = a`.
* `TauCeti.HopfAlgebra.star_antipode_star_antipode`: `S(S(a)*)* = a`.
* `TauCeti.HopfAlgebra.antipode_bijective`: the antipode of a Hopf star algebra is bijective.
* `TauCeti.HopfAlgebra.antipodeAlgEquivOp`: the antipode as an algebra isomorphism `A ≃ Aᵐᵒᵖ`,
  whose inverse is `a ↦ S(a*)*` (`TauCeti.HopfAlgebra.antipodeAlgEquivOp_symm_apply`).

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.2.7.
-/

public section

open Coalgebra HopfAlgebra WithConv

namespace TauCeti.HopfAlgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [_root_.HopfAlgebra R A] [StarModule R A]

variable [StarCoalgebra R A]

/-- For `Δ a = ∑ xᵢ ⊗ yᵢ`, the star of the antipode law for `a*` reads `∑ S(yᵢ*)* xᵢ = ε(a)`. -/
private theorem sum_star_antipode_star_mul {ι : Type*} {a : A} (𝓡 : Repr R a ι) :
    ∑ i ∈ 𝓡.index, star (antipode R (star (𝓡.right i))) * 𝓡.left i =
      algebraMap R A (counit a) := by
  simpa [star_sum, ← algebraMap_star_comm] using
    congr(star $(sum_mul_antipode_eq_algebraMap_counit 𝓡.star))

/-- In a Hopf star algebra, `S(S(a*)*) = a`. -/
@[simp]
theorem antipode_star_antipode_star (a : A) : antipode R (star (antipode R (star a))) = a := by
  -- `S ∘ T` is a right convolution inverse of `S`, for `T(a) = S(a*)*` the intrinsic star of `S`.
  have h : toConv (antipode R) * toConv (antipode R ∘ₗ (star (toConv (antipode R))).ofConv) =
      (1 : WithConv (A →ₗ[R] A)) := by
    ext x
    rw [(ℛ R x).convMul_apply, LinearMap.convOne_apply]
    simp only [LinearMap.comp_apply, LinearMap.intrinsicStar_apply, ← antipode_mul_antidistrib,
      ← map_sum, sum_star_antipode_star_mul, Algebra.algebraMap_eq_smul_one, map_smul,
      antipode_one]
  -- The identity is a left convolution inverse of `S`, so `S ∘ T = id`.
  have hid : LinearMap.id = antipode R ∘ₗ (star (toConv (antipode R))).ofConv :=
    toConv_injective (left_inv_eq_right_inv LinearMap.id_mul_antipode h)
  simpa using (LinearMap.congr_fun hid a).symm

/-- In a Hopf star algebra, `S(S(a)*)* = a`. -/
@[simp]
theorem star_antipode_star_antipode (a : A) : star (antipode R (star (antipode R a))) = a := by
  simpa using congr(star $(antipode_star_antipode_star (R := R) (star a)))

/-- The antipode of a Hopf star algebra is bijective. -/
theorem antipode_bijective : Function.Bijective (antipode R : A → A) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun a => star (antipode R (star a)), star_antipode_star_antipode,
      antipode_star_antipode_star⟩

variable (R A) in
/-- The antipode of a Hopf star algebra as an algebra isomorphism onto the opposite algebra.
Its inverse is `a ↦ S(a*)*`. -/
noncomputable def antipodeAlgEquivOp : A ≃ₐ[R] Aᵐᵒᵖ :=
  { antipodeAlgHomOp R A with
    invFun a := star (antipode R (star a.unop))
    left_inv := star_antipode_star_antipode
    right_inv a := MulOpposite.unop_injective (antipode_star_antipode_star a.unop) }

@[simp]
theorem antipodeAlgEquivOp_toAlgHom :
    (antipodeAlgEquivOp R A).toAlgHom = antipodeAlgHomOp R A := (rfl)

@[simp]
theorem antipodeAlgEquivOp_apply (a : A) :
    antipodeAlgEquivOp R A a = MulOpposite.op (antipode R a) := (rfl)

/-- The inverse of the antipode of a Hopf star algebra is `a ↦ S(a*)*`. -/
@[simp]
theorem antipodeAlgEquivOp_symm_apply (a : Aᵐᵒᵖ) :
    (antipodeAlgEquivOp R A).symm a = star (antipode R (star a.unop)) := (rfl)

end TauCeti.HopfAlgebra
