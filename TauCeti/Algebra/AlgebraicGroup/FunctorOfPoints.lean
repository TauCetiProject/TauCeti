/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The functor of points of an affine group scheme is group-valued

For a Hopf algebra `H` over `R`, the affine group scheme `Spec H` has functor of points
`R-Alg ⥤ Grp`, `A ↦ H →ₐ[R] A`. This file equips that set of `R`-algebra homomorphisms
with its group structure, for `A` a commutative `R`-algebra. The source `H` need only be a
Hopf algebra; it is *not* required to be commutative.

Mathlib already constructs the convolution `Monoid` on `WithConv (H →ₐ[R] A)` for `H` a
bialgebra (`Mathlib/RingTheory/Bialgebra/Convolution.lean`): multiplication is the
convolution product `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and the unit is `algebraMap ∘ ε`.
What is added here is the **inverse** and hence the **group** structure, available exactly
when `H` carries an antipode `S`: the inverse of `f` is `f ∘ S`. This is the first concrete
target of the reductive-groups roadmap (Layer 0, "R-points as a group"), which records
that the group structure on the functor of points is by convolution with the counit as
identity and `f ∘ S` as inverse.

## Main results

* `AlgHom.convInv_def`, `AlgHom.convInv_apply`: the convolution inverse of `f` is `f ∘ S`.
* `AlgHom.instGroup`, `AlgHom.instCommGroup`: for `H` a Hopf algebra over `R` and `A` a
  commutative `R`-algebra, `WithConv (H →ₐ[R] A)` is a group, commutative when `H` is
  cocommutative.
* `AlgHom.mapValue_id`, `AlgHom.mapValue_comp`: the functor of points is functorial in the
  value algebra (`mapValue` preserves identities and composition).

## References

This realizes the "R-points as a group via convolution" milestone of the Tau Ceti
reductive-groups roadmap (Layer 0). The convolution monoid it builds on is the work of
Yaël Dillies, Michał Mrugała and Yunzhou Xie in Mathlib.
-/

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The antipode is a left convolution inverse of the identity in the convolution ring of
linear maps: `S * id = 1`. This is a restatement of the antipode axiom
`HopfAlgebra.mul_antipode_rTensor_comul`. -/
lemma antipode_convMul_id :
    (toConv (antipode R) : WithConv (H →ₗ[R] H)) * toConv LinearMap.id = 1 := by
  refine WithConv.ext ?_
  ext h
  simp only [LinearMap.convMul_apply, LinearMap.convOne_apply,
    ← LinearMap.rTensor_def]
  exact mul_antipode_rTensor_comul_apply h

end HopfAlgebra

namespace AlgHom

variable {R H A : Type*} [CommSemiring R]

section Hopf

variable [Semiring H] [_root_.HopfAlgebra R H] [CommSemiring A] [Algebra R A]

/-- Post-composition of an algebra homomorphism `f : H →ₐ[R] A` with the antipode `S` of
`H`, as an `R`-algebra homomorphism `H →ₐ[R] A`. Its underlying linear map is
`f.toLinearMap ∘ₗ HopfAlgebra.antipode R`. This is well-defined even when `H` is
noncommutative: `S` is an antihomomorphism (`HopfAlgebra.antipode_mul`), and `A` is
commutative, so `f ∘ S` is a homomorphism. -/
private noncomputable def antipodeComp (f : H →ₐ[R] A) : H →ₐ[R] A :=
  AlgHom.ofLinearMap (f.toLinearMap ∘ₗ antipode R)
    (by simp only [LinearMap.coe_comp, Function.comp_apply, antipode_one, f.toLinearMap_apply,
      map_one])
    fun x y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, antipode_mul, f.toLinearMap_apply,
        map_mul]
      rw [mul_comm]

private lemma toLinearMap_antipodeComp (f : H →ₐ[R] A) :
    (antipodeComp f).toLinearMap = f.toLinearMap ∘ₗ antipode R := rfl

/-- The convolution inverse of an `R`-algebra homomorphism `f : H →ₐ[R] A` out of a Hopf
algebra is `f ∘ S`, where `S` is the antipode. -/
noncomputable instance : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (antipodeComp f.ofConv)

/-- The convolution inverse of `f` is `f ∘ S`, where `S` is the antipode: definitionally,
`f⁻¹ = toConv (antipodeComp f.ofConv)`. -/
lemma convInv_def (f : WithConv (H →ₐ[R] A)) :
    f⁻¹ = toConv (antipodeComp f.ofConv) := rfl

/-- Pointwise, the convolution inverse of `f` sends `h` to `f (S h)`, where `S` is the
antipode. -/
@[simp]
lemma convInv_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    f⁻¹ h = f.ofConv (antipode R h) := rfl

private lemma convInv_mul_cancel (f : WithConv (H →ₐ[R] A)) : f⁻¹ * f = 1 := by
  -- It suffices to check the equality after passing to the convolution ring of linear
  -- maps, where Mathlib already has the structure; the algebra-hom convolution monoid is
  -- transported from the linear one along the underlying-linear-map injection.
  refine WithConv.ofConv_injective (AlgHom.toLinearMap_injective (WithConv.toConv_injective ?_))
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne, convInv_def, toConv_ofConv,
    toLinearMap_antipodeComp]
  -- Now in `WithConv (H →ₗ[R] A)`: `(f ∘ S) * f = 1`. Pass to underlying linear maps.
  refine WithConv.ofConv_injective ?_
  -- Distribute `f` over the convolution product `S * id`.
  have key := LinearMap.algHom_comp_convMul_distrib f.ofConv
    (toConv (antipode R)) (toConv LinearMap.id)
  -- `key : f ∘ (S * id) = ((f ∘ S) * (f ∘ id)).ofConv`. Use `S * id = 1` and `f ∘ id = f`.
  rw [HopfAlgebra.antipode_convMul_id, ofConv_toConv, ofConv_toConv, LinearMap.comp_id] at key
  -- So `((f ∘ S) * f).ofConv = f ∘ 1`, the linear unit `1` being `algebraMap ∘ counit`.
  rw [← key, LinearMap.convOne_def, ofConv_toConv]
  -- Finally `f ∘ (algebraMap ∘ counit) = algebraMap ∘ counit`, since `f` is an algebra hom.
  ext h
  exact f.ofConv.commutes (counit h)

/-- For a Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` (the functor of points of `Spec H`
evaluated at `A`) is a group, with inverse `f ↦ f ∘ S`. -/
noncomputable instance instGroup : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel := convInv_mul_cancel

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The functor of points `A ↦ (H →ₐ[R] A)` of `Spec H` is functorial in the value algebra:
an `R`-algebra homomorphism `φ : A →ₐ[R] B` induces, by post-composition, a group
homomorphism between the convolution groups of points. -/
noncomputable def mapValue (φ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (φ.comp f.ofConv)
  map_one' := by
    rw [AlgHom.convOne_def, toConv_ofConv, ← AlgHom.comp_assoc, Algebra.comp_ofId,
      AlgHom.convOne_def]
  map_mul' f g := by
    rw [toConv_ofConv, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv, toConv_ofConv]

@[simp]
lemma mapValue_apply (φ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    mapValue φ f = toConv (φ.comp f.ofConv) := rfl

@[simp]
lemma mapValue_id :
    mapValue (H := H) (AlgHom.id R A) = MonoidHom.id (WithConv (H →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [mapValue_apply, AlgHom.id_comp, toConv_ofConv, MonoidHom.id_apply]

variable {C : Type*} [CommSemiring C] [Algebra R C]

lemma mapValue_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    mapValue (H := H) (ψ.comp φ) = (mapValue ψ).comp (mapValue φ) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, mapValue_apply, mapValue_apply, mapValue_apply, toConv_ofConv,
    AlgHom.comp_assoc]

end Hopf

section CommHopf

variable [Semiring H] [_root_.HopfAlgebra R H] [IsCocomm R H] [CommSemiring A] [Algebra R A]

/-- When `H` is moreover cocommutative, the convolution group of `R`-algebra homomorphisms
`H →ₐ[R] A` is abelian. -/
noncomputable instance instCommGroup : CommGroup (WithConv (H →ₐ[R] A)) where
  mul_comm := mul_comm

end CommHopf

end AlgHom

end TauCeti
