/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Charpoly.Basic
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# The norm modulo an ideal and along algebra homomorphisms

Let `S` be a free `R`-algebra and `I` an ideal of `R`. The norm of `S ⧸ IS` over `R ⧸ I`
of the class of `x` is the class of the norm of `x`. This is the norm counterpart of
`TauCeti.Algebra.trace_quotient_map_mk`. It lets a norm equation over `R` be solved first over the
quotient: taking `I` to be the maximal ideal of a local ring, it supplies the residual norm input
for lifting norm equations with Hensel's lemma (`TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem`).

By Cayley–Hamilton, if an `R`-algebra homomorphism `τ : S →ₐ[R] T` kills `b ∈ S`, then
`algebraMap R T (Algebra.norm R b) = 0` (`AlgHom.algebraMap_norm_eq_zero_of_map_eq_zero`); in
particular `Algebra.norm R b = 0` when `T = R` and `Algebra.norm R b ∈ I` when `T = R ⧸ I`.

## Main results

* `TauCeti.Algebra.norm_quotient_mk`: the norm of `S ⧸ IS` over `R ⧸ I` of the class of `x` is
  the class of the norm of `x`.
* `TauCeti.Algebra.norm_mk_map_mkₐ_eq_norm`: for ideals `J ≤ I`, the norm of a class in
  `(V ⧸ J) ⧸ I (V ⧸ J)` is its norm in any quotient of `V` by `I`, over any quotient of the base.
* `AlgHom.algebraMap_norm_eq_zero_of_map_eq_zero`, `AlgHom.norm_eq_zero_of_map_eq_zero`, and
  `AlgHom.norm_mem_of_map_eq_zero`: vanishing of `Algebra.norm R b` under `R`-algebra maps killing
  `b`.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]

/-- **The norm commutes with reduction modulo an ideal.** For a free algebra `S` over `R`
and an ideal `I` of `R`, the norm of `S ⧸ IS` over `R ⧸ I` of the class of `x` is the class of the
norm of `x`. -/
@[simp]
theorem Algebra.norm_quotient_mk (I : Ideal R) (x : S) :
    Algebra.norm (R ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk I (Algebra.norm R x) := by
  -- `S ⧸ IS` is the base change `(R ⧸ I) ⊗[R] S`, and the norm of `1 ⊗ x` is the image of the norm
  -- of `x`.
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.norm_baseChange_tmul,
    Ideal.Quotient.algebraMap_eq]

/-- **The norm in a double quotient.** Let `J ≤ I` be ideals of an `R`-algebra `V`, let `k` be a
quotient of `R` acting compatibly on `V ⧸ J` and on `B`, and let `f : V → B` be a surjective
`R`-algebra map with kernel `I`. Then the norm over `k` of the class of `v` in
`(V ⧸ J) ⧸ I (V ⧸ J)` is the norm of `f v`. -/
theorem Algebra.norm_mk_map_mkₐ_eq_norm {R k V B : Type*} [CommRing R] [CommRing k] [CommRing V]
    [CommRing B] [Algebra R k] [Algebra R V] [Algebra R B] [Algebra k B] [IsScalarTower R k B]
    {J I : Ideal V} [Algebra k (V ⧸ J)] [IsScalarTower R k (V ⧸ J)]
    (hk : Function.Surjective (algebraMap R k)) (f : V →ₐ[R] B) (hf : Function.Surjective f)
    (hker : RingHom.ker f = I) (hJI : J ≤ I) (v : V) :
    Algebra.norm k (Ideal.Quotient.mk (I.map (Ideal.Quotient.mkₐ R J)) (Ideal.Quotient.mk J v)) =
      Algebra.norm k (f v) := by
  subst hker
  let φ := (DoubleQuot.quotQuotEquivQuotOfLEₐ R hJI).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)
  rw [← Algebra.norm_eq_of_algEquiv (φ.extendScalarsOfSurjective hk),
    AlgEquiv.coe_extendScalarsOfSurjective, AlgEquiv.trans_apply,
    DoubleQuot.coe_quotQuotEquivQuotOfLEₐ]
  -- The class of `mk J v` is `DoubleQuot.quotQuotMk J I v`, which is `mk J` followed by `mk`.
  exact congrArg _ ((congrArg _ (DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk v hJI)).trans
    (Ideal.quotientKerAlgEquivOfSurjective_mk hf v))

end TauCeti

namespace AlgHom

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- **Cayley–Hamilton vanishing of the norm along an algebra homomorphism.** Over a commutative
ring `R`, if `S` is a finite free `R`-algebra and an `R`-algebra homomorphism `τ : S →ₐ[R] T`
vanishes at `b : S`, then `algebraMap R T (Algebra.norm R b) = 0`. -/
theorem algebraMap_norm_eq_zero_of_map_eq_zero {T : Type*} [Semiring T] [Algebra R T]
    (τ : S →ₐ[R] T) {b : S} (hb : τ b = 0) :
    algebraMap R T (Algebra.norm R b) = 0 := by
  have hτ := congrArg τ (Algebra.aeval_self_charpoly_lmul (R := R) b)
  rw [map_zero, ← Polynomial.aeval_algHom_apply, hb, Polynomial.aeval_def,
    Polynomial.eval₂_at_zero] at hτ
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, hτ, mul_zero]

/-- **Cayley–Hamilton vanishing of the norm at a retraction.** Over a commutative ring `R`, if `S`
is a finite free `R`-algebra and an `R`-algebra homomorphism `τ : S →ₐ[R] R` vanishes at `b : S`,
then `Algebra.norm R b = 0`. -/
theorem norm_eq_zero_of_map_eq_zero (τ : S →ₐ[R] R) {b : S} (hb : τ b = 0) :
    Algebra.norm R b = 0 := by
  simpa using τ.algebraMap_norm_eq_zero_of_map_eq_zero hb

/-- **Congruence vanishing of the norm at a quotient map.** If `S` is a finite free `R`-algebra,
`I` is an ideal of `R`, and `τ : S →ₐ[R] R ⧸ I` vanishes at `b : S`, then `Algebra.norm R b ∈ I`. -/
theorem norm_mem_of_map_eq_zero {I : Ideal R} (τ : S →ₐ[R] R ⧸ I) {b : S} (hb : τ b = 0) :
    Algebra.norm R b ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp (τ.algebraMap_norm_eq_zero_of_map_eq_zero hb)

end AlgHom
