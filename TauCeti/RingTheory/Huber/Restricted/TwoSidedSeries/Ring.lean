/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Convolution
public import TauCeti.Topology.Algebra.InfiniteSum.ConvolutionRing

/-!
# The ring of two-sided restricted series `A⟨X, X⁻¹⟩`

`TauCeti.Huber.twoSidedRestrictedSubmodule A A` is the `A`-module of coefficient families
underlying Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). Over a complete nonarchimedean ring it satisfies
`TauCeti.IsConvolutionRing`, which equips it with the convolution product
`(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ`: when `A` is moreover `T0` it is a ring
(`TauCeti.IsConvolutionRing.instRing`), and a commutative `A`-algebra when `A` is commutative
(`TauCeti.IsConvolutionRing.instCommRing`, `TauCeti.IsConvolutionRing.instAlgebra`), in which the
Laurent variable `X = TauCeti.IsConvolutionRing.monomial 1 1` is a unit
(`TauCeti.IsConvolutionRing.isUnit_monomial`).

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule.instIsConvolutionRing`: `A⟨X, X⁻¹⟩` is a convolution
  ring.

## Main results

* `TauCeti.Huber.twoSidedRestrictedMul_apply`: the bilinear map
  `TauCeti.Huber.twoSidedRestrictedMul` is the ring multiplication.

## Implementation notes

The product is not the pointwise product of `ℤ → A`, so `A⟨X, X⁻¹⟩` is not a subring of `ℤ → A`;
the multiplication is installed directly on the submodule's coercion to a type. Each coefficient of
a product is a `tsum`, so the ring structure assumes `A` complete, and `T0` for the ring axioms,
so that these sums converge to unique limits; this is Wedhorn's convention, his "complete"
including Hausdorff (Definition 5.31).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open scoped DiscreteConvolution

namespace TauCeti.Huber

section IsConvolutionRing

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A]

/-- **`A⟨X, X⁻¹⟩` is a convolution ring** (Wedhorn, Example 6.39): over a complete nonarchimedean
ring the two-sided restricted families contain the monomials, are closed under convolution, and
their convolution sums and triple products converge. -/
instance twoSidedRestrictedSubmodule.instIsConvolutionRing :
    IsConvolutionRing (twoSidedRestrictedSubmodule A A) where
  single_mem := single_mem_twoSidedRestrictedSubmodule
  addRingConvolution_mem := addRingConvolution_mem_twoSidedRestrictedSubmodule
  addConvolutionExists := addConvolutionExists_of_mem_twoSidedRestrictedSubmodule
  summable_sigma_addFiber_mul_mul hf hg hh :=
    (mem_twoSidedRestrictedSubmodule.mp hf).summable_sigma_addFiber_mul_mul
      (mem_twoSidedRestrictedSubmodule.mp hg) (mem_twoSidedRestrictedSubmodule.mp hh)

end IsConvolutionRing

section CommRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

/-- The bilinear convolution `twoSidedRestrictedMul` is the multiplication of `A⟨X, X⁻¹⟩`. -/
-- Not `@[simp]`: it would rewrite the left-hand side of `coe_twoSidedRestrictedMul`.
theorem twoSidedRestrictedMul_apply (f g : twoSidedRestrictedSubmodule A A) :
    twoSidedRestrictedMul f g = f * g := Subtype.ext <| coe_twoSidedRestrictedMul f g

end CommRing

end TauCeti.Huber
