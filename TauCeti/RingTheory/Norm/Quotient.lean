/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Charpoly.Basic
import TauCeti.RingTheory.Norm.NonZeroDivisors
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

For a finite free algebra `S` and a maximal ideal `p` of `R`, the norm of `x` lies in `p` exactly
when `x` lies in a prime of `S` over `p` (`Algebra.norm_mem_iff_exists_liesOver`): the class of
`x` in the finite-dimensional algebra `S ⧸ pS` over the field `R ⧸ p` is a unit exactly when its
norm is nonzero. When a single prime `P` lies over `p`, this says that `x` vanishes in the
residue ring `S ⧸ P` exactly when its norm vanishes in `R ⧸ p`.

## Main results

* `TauCeti.Algebra.norm_quotient_mk`: the norm of `S ⧸ IS` over `R ⧸ I` of the class of `x` is
  the class of the norm of `x`.
* `AlgHom.algebraMap_norm_eq_zero_of_map_eq_zero`, `AlgHom.norm_eq_zero_of_map_eq_zero`, and
  `AlgHom.norm_mem_of_map_eq_zero`: vanishing of `Algebra.norm R b` under `R`-algebra maps killing
  `b`.
* `Algebra.norm_mem_iff_exists_liesOver`: the norm lies in a maximal ideal `p` exactly when the
  element lies in a prime over `p`.
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

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S]

/-- **The norm lies in a maximal ideal exactly over the primes containing the element.** For a
finite free algebra `S` over `R` and a maximal ideal `p` of `R`, the norm of `x` lies in `p`
exactly when `x` lies in some prime ideal of `S` lying over `p`. -/
theorem norm_mem_iff_exists_liesOver (p : Ideal R) [p.IsMaximal] (x : S) :
    norm R x ∈ p ↔ ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver p ∧ x ∈ P := by
  constructor
  · intro hx
    let I := p.map (algebraMap R S)
    let : Field (R ⧸ p) := Ideal.Quotient.field p
    have : Module.Finite (R ⧸ p) (S ⧸ I) := .of_restrictScalars_finite R _ _
    -- The class of `x` in `S ⧸ pS` is not a unit: its norm over the field `R ⧸ p` vanishes.
    have hnu : Ideal.Quotient.mk I x ∈ nonunits (S ⧸ I) := fun hu => by
      have := (isUnit_norm_iff (R := R ⧸ p)).2 hu
      rw [TauCeti.Algebra.norm_quotient_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx] at this
      exact not_isUnit_zero this
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hnu
    have hMp := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := M)
    refine ⟨M.comap (Ideal.Quotient.mk I), hMp.isPrime, ⟨?_⟩, hxM⟩
    refine ‹p.IsMaximal›.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun r hr => ?_
    rw [Ideal.under, Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_map_of_mem _ hr)]
    exact M.zero_mem
  · rintro ⟨P, -, hP, hxP⟩
    rw [Ideal.mem_of_liesOver P p]
    exact Ideal.mem_of_dvd _ (dvd_algebraMap_norm x) hxP

end Algebra
