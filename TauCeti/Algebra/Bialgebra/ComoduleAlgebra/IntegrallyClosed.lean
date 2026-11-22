/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.RingTheory.TensorProduct.MulRight

/-!
# Invariants of a normal affine scheme are normal

Let `H` be a bialgebra over a commutative semiring `R`, flat as an `R`-module, and let `A` be a
commutative `H`-comodule algebra: an action of the affine monoid scheme
`G = Spec H` on the affine scheme `X = Spec A`. A quotient of invariant functions which
lies in `A` is itself invariant (`TauCeti.ComoduleAlgebra.mem_coinvariants_of_mul_mem`, stated for
any comodule algebra `A` that is a ring): if `b`
and `a * b` are invariant and `b` is a non-zero-divisor, then `a` is invariant, because
multiplication by `b ⊗ 1` is injective on `A ⊗[R] H` by flatness of `H`.

Consequently, if `A` is an integrally closed domain, so is the ring of invariants `A^{co H}`
(`TauCeti.ComoduleAlgebra.isIntegrallyClosed_coinvariants`): an element of the fraction field of
`A^{co H}` which is integral over `A^{co H}` is integral over `A`, hence lies in `A`, and it is then
a quotient of invariants lying in `A`. Geometrically, the affine quotient `X // G` of a normal
integral affine scheme is normal. No reductivity hypothesis is needed. Over a field every `H` is
flat.

## Main results

* `TauCeti.ComoduleAlgebra.mem_coinvariants_of_mul_mem`: invariants are closed under division
  inside `A`.
* `TauCeti.ComoduleAlgebra.isIntegrallyClosed_coinvariants`: the invariants of an integrally closed
  domain are integrally closed.

## References

* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, third edition, Springer (1994),
  Chapter 0, §2.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

section Ring

variable {R : Type*} {H : Type*} {A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Module.Flat R H] [Ring A] [Algebra R A] [ComoduleAlgebra R H A]

/-- **Invariants are closed under division inside `A`**: if a non-zero-divisor `b` and `a * b` are
invariant, then so is `a`. -/
theorem mem_coinvariants_of_mul_mem {a b : A} (hb : b ∈ coinvariants R H A)
    (hb0 : b ∈ nonZeroDivisors A) (hab : a * b ∈ coinvariants R H A) :
    a ∈ coinvariants R H A := by
  rw [mem_coinvariants] at hb hab ⊢
  have hinj : Function.Injective ((LinearMap.mulRight R b).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ fun x y h ↦ sub_eq_zero.1 <|
      (mul_right_mem_nonZeroDivisors_eq_zero_iff hb0).1 (by simpa [sub_mul, sub_eq_zero] using h)
  apply hinj
  rw [LinearMap.rTensor_mulRight_apply, LinearMap.rTensor_mulRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hab, coact_mul, hb]

end Ring

variable {R : Type*} {H : Type*} {A : Type*} [CommRing R] [Semiring H] [Bialgebra R H]
  [Module.Flat R H] [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

/-- **The invariants of an integrally closed domain are integrally closed**: the affine quotient
of a normal integral affine scheme by a flat affine monoid scheme is normal. -/
theorem isIntegrallyClosed_coinvariants [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (coinvariants R H A) := by
  let B := coinvariants R H A
  let K := FractionRing B
  let L := FractionRing A
  let g : B →+* L := (algebraMap A L).comp (algebraMap B A)
  have hg : Function.Injective g :=
    (IsFractionRing.injective A L).comp Subtype.val_injective
  let ψ : K →+* L := IsFractionRing.lift hg
  rw [isIntegrallyClosed_iff K]
  intro x hx
  -- The image of `x` in the fraction field of `A` is integral over `A`, so it comes from `A`.
  have hcomp : (algebraMap A L).comp (algebraMap B A) = ψ.comp (algebraMap B K) :=
    RingHom.ext fun b ↦ (IsFractionRing.lift_algebraMap (K := K) hg b).symm
  have hψx : IsIntegral A (ψ x) := IsIntegral.map_of_comp_eq (algebraMap B A) ψ hcomp hx
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hψx
  obtain ⟨⟨b₁, b₂⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors B) x
  have hb₂ : (b₂ : B) ≠ 0 := nonZeroDivisors.ne_zero b₂.property
  -- `a * b₂ = b₁` in `A`, so `a` is a quotient of invariants.
  have hab : a * (b₂ : B) = (b₁ : A) := by
    apply IsFractionRing.injective A L
    have := congrArg ψ hb
    rw [map_mul, IsFractionRing.lift_algebraMap (K := K) hg,
      IsFractionRing.lift_algebraMap (K := K) hg, ← ha] at this
    simpa [g] using this
  have hmem : a ∈ B :=
    mem_coinvariants_of_mul_mem (b₂ : B).property
      (mem_nonZeroDivisors_of_ne_zero fun h ↦ hb₂ (Subtype.ext h)) (hab ▸ b₁.property)
  refine ⟨⟨a, hmem⟩, ψ.injective ?_⟩
  rw [IsFractionRing.lift_algebraMap (K := K) hg, ← ha]
  rfl

end TauCeti.ComoduleAlgebra
