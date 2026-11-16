/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The spectrum point defined by an augmentation

An algebra homomorphism `f : H →ₐ[k] k` from a commutative `k`-algebra to an integral domain `k`
determines a point of the algebra's prime spectrum, whose prime ideal is `ker f`: the image of the
generic point of `Spec k`. When `k` is a field this is the `k`-rational point cut out by `f`. This
file records that point and its underlying prime ideal.

## Main declarations

* `AlgHom.kernelPoint`: the point cut out by the kernel of an augmentation.
* `AlgHom.comap_kernelPoint`: contraction of a kernel point is the kernel point of the
  composite algebra homomorphism.
-/

public section

open AlgebraicGeometry

namespace AlgHom

universe u v w

variable {k : Type u} [CommRing k] [IsDomain k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

/-- The point of `Spec H` defined by an augmentation `f : H →ₐ[k] k` to an integral domain: the
contraction of the zero ideal of `k`. Its prime ideal is `ker f`. -/
def kernelPoint : Spec (CommRingCat.of H) :=
  PrimeSpectrum.comap (f : H →+* k) ⊥

/-- The prime ideal of an augmentation point is the kernel of the augmentation. -/
@[simp]
theorem kernelPoint_asIdeal :
    (kernelPoint f).asIdeal = RingHom.ker (f : H →+* k) := by
  rw [kernelPoint, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot,
    RingHom.ker_eq_comap_bot]

/-- A kernel point belongs to a basic open exactly when its defining homomorphism is
nonzero on the defining element. -/
@[simp]
theorem kernelPoint_mem_basicOpen_iff (a : H) :
    (kernelPoint f : PrimeSpectrum H) ∈ PrimeSpectrum.basicOpen a ↔ f a ≠ 0 := by
  -- Expose ideal membership to bridge the scheme carrier and the prime-spectrum basic open.
  change a ∉ (kernelPoint f).asIdeal ↔ f a ≠ 0
  rw [kernelPoint_asIdeal, RingHom.mem_ker, AlgHom.coe_toRingHom]

/-- Contracting a kernel point along an algebra homomorphism gives the kernel point of the
composite algebra homomorphism. -/
@[simp]
theorem comap_kernelPoint {A : Type w} [CommRing A] [Algebra k A] (g : A →ₐ[k] H) :
    PrimeSpectrum.comap (g : A →+* H) (kernelPoint f) = kernelPoint (f.comp g) :=
  PrimeSpectrum.comap_comp_apply (g : A →+* H) (f : H →+* k) ⊥

end AlgHom
