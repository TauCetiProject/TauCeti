/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Convolution
import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# The ring of two-sided restricted series `A⟨X, X⁻¹⟩`

`TauCeti.Huber.twoSidedRestrictedSubmodule A A` is the `A`-module of coefficient families
underlying Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). This module equips it with the convolution
product `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ`, making it a ring, and a commutative `A`-algebra when `A` is
commutative, in which the Laurent variable `X = twoSidedMonomial 1 1` is a unit.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule.instMul` and
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instOne`: the product and the unit.
* `TauCeti.Huber.twoSidedRestrictedSubmodule.instRing`,
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instCommRing` and
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instAlgebra`: the ring structure of `A⟨X, X⁻¹⟩`, and
  its commutative `A`-algebra structure when `A` is commutative.
* `TauCeti.Huber.twoSidedMonomial`: the monomial `a Xⁿ`.

## Main results

* `TauCeti.Huber.twoSidedMonomial_mul_twoSidedMonomial`: monomials multiply by adding degrees,
  `(a Xᵐ)(b Xⁿ) = ab X^{m+n}`.
* `TauCeti.Huber.isUnit_twoSidedMonomial`: a monomial with a unit coefficient is a unit.
* `TauCeti.Huber.twoSidedRestrictedMul_apply`: the bilinear map
  `TauCeti.Huber.twoSidedRestrictedMul` is the ring multiplication.

## Implementation notes

The product is not the pointwise product of `ℤ → A`, so `A⟨X, X⁻¹⟩` is not a subring of `ℤ → A`;
the multiplication is installed directly on the submodule's coercion to a type.

The unit and the monomials, with their additive and scalar laws, need only continuous addition
and scalar multiplication. The product and the monomial rule need a nonarchimedean ring
topology; each coefficient of a product is a `tsum`, which is `0` if the sum diverges. The ring
axioms assume `A` complete and `T0`, so that these sums converge; this is Wedhorn's convention, his
"complete" including Hausdorff (Definition 5.31).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open scoped DiscreteConvolution

namespace TauCeti.Huber

section Monomial

variable {A : Type*} [Semiring A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]

/-- **The unit of `A⟨X, X⁻¹⟩`**: the constant series `1 = 1 · X⁰`. -/
instance twoSidedRestrictedSubmodule.instOne : One (twoSidedRestrictedSubmodule A A) where
  one := ⟨Pi.single 0 1, single_mem_twoSidedRestrictedSubmodule 0 1⟩

/-- The coefficient family of the unit is supported at degree `0` with value `1`. -/
@[simp, norm_cast]
theorem coe_one_twoSidedRestrictedSubmodule :
    ((1 : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single 0 1 := rfl

/-- **The monomial `a Xⁿ`** of `A⟨X, X⁻¹⟩`: the family supported at degree `n` with value `a`.
The Laurent variable `X` is `twoSidedMonomial 1 1`. -/
def twoSidedMonomial (n : ℤ) (a : A) : twoSidedRestrictedSubmodule A A :=
  ⟨Pi.single n a, single_mem_twoSidedRestrictedSubmodule n a⟩

/-- The coefficient family of the monomial `a Xⁿ` is `Pi.single n a`. -/
@[simp, norm_cast]
theorem coe_twoSidedMonomial (n : ℤ) (a : A) : (twoSidedMonomial n a : ℤ → A) = Pi.single n a :=
  (rfl)

/-- The degree-`0` monomial with coefficient `1` is the unit: `1 · X⁰ = 1`. -/
@[simp]
theorem twoSidedMonomial_zero_one : twoSidedMonomial 0 (1 : A) = 1 :=
  Subtype.ext <| (coe_twoSidedMonomial 0 1).trans coe_one_twoSidedRestrictedSubmodule.symm

/-- The monomial with coefficient `0` is `0`. -/
@[simp]
theorem twoSidedMonomial_zero_right (n : ℤ) : twoSidedMonomial n (0 : A) = 0 :=
  Subtype.ext <| by simp

/-- The monomial `a Xⁿ` is additive in its coefficient. -/
@[simp]
theorem twoSidedMonomial_add (n : ℤ) (a b : A) :
    twoSidedMonomial n (a + b) = twoSidedMonomial n a + twoSidedMonomial n b :=
  Subtype.ext <| by simp [Pi.single_add]

/-- Scaling a monomial scales its coefficient: `a • b Xⁿ = (ab) Xⁿ`. -/
@[simp]
theorem smul_twoSidedMonomial (a : A) (n : ℤ) (b : A) :
    a • twoSidedMonomial n b = twoSidedMonomial n (a * b) :=
  Subtype.ext <| by simp [← smul_eq_mul, Pi.single_smul']

end Monomial

section Neg

variable {A : Type*} [Ring A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]

/-- The monomial `a Xⁿ` commutes with negating its coefficient. -/
@[simp]
theorem twoSidedMonomial_neg (n : ℤ) (a : A) : twoSidedMonomial n (-a) = -twoSidedMonomial n a :=
  Subtype.ext <| by simp [Pi.single_neg]

end Neg

section Mul

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The product on `A⟨X, X⁻¹⟩`**: the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ`. -/
noncomputable instance twoSidedRestrictedSubmodule.instMul :
    Mul (twoSidedRestrictedSubmodule A A) where
  mul f g := ⟨f ⋆ᵣ₊ g, addRingConvolution_mem_twoSidedRestrictedSubmodule f.2 g.2⟩

/-- The coefficient family of a product is the convolution of the coefficient families. -/
@[simp, norm_cast]
theorem coe_mul_twoSidedRestrictedSubmodule (f g : twoSidedRestrictedSubmodule A A) :
    (↑(f * g) : ℤ → A) = ↑f ⋆ᵣ₊ ↑g := rfl

/-- **Monomials multiply by adding degrees**: `(a Xᵐ)(b Xⁿ) = ab X^{m+n}`. -/
@[simp]
theorem twoSidedMonomial_mul_twoSidedMonomial (m n : ℤ) (a b : A) :
    twoSidedMonomial m a * twoSidedMonomial n b = twoSidedMonomial (m + n) (a * b) :=
  Subtype.ext <| DiscreteConvolution.single_addRingConvolution_single m n a b

end Mul

section Ring

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

/-- **`A⟨X, X⁻¹⟩` is a ring** (Wedhorn, Example 6.39): the additive group of the submodule, with
the convolution product `instMul` and the unit `instOne`. -/
noncomputable instance twoSidedRestrictedSubmodule.instRing :
    Ring (twoSidedRestrictedSubmodule A A) where
  mul_assoc f g h := Subtype.ext <| ZeroAtFilter.addRingConvolution_assoc
    (mem_twoSidedRestrictedSubmodule.mp f.2) (mem_twoSidedRestrictedSubmodule.mp g.2)
    (mem_twoSidedRestrictedSubmodule.mp h.2)
  one_mul _ := Subtype.ext <| by simp
  mul_one _ := Subtype.ext <| by simp
  left_distrib f g h := Subtype.ext <| DiscreteConvolution.addRingConvolution_add _ _ _
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2)
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2)
  right_distrib f g h := Subtype.ext <| DiscreteConvolution.add_addRingConvolution _ _ _
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2)
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule g.2 h.2)
  zero_mul _ := Subtype.ext <| DiscreteConvolution.zero_addRingConvolution _
  mul_zero _ := Subtype.ext <| DiscreteConvolution.addRingConvolution_zero _

/-- **A monomial with a unit coefficient is a unit** of `A⟨X, X⁻¹⟩`: the inverse of `a Xⁿ` is
`b X⁻ⁿ` for the inverse `b` of `a`. In particular the Laurent variable `twoSidedMonomial 1 1` is a
unit (Wedhorn, Example 6.39). -/
theorem isUnit_twoSidedMonomial (n : ℤ) {a : A} (ha : IsUnit a) :
    IsUnit (twoSidedMonomial n a) := by
  obtain ⟨u, rfl⟩ := ha
  exact isUnit_iff_exists.2 ⟨twoSidedMonomial (-n) ↑u⁻¹, by simp⟩

end Ring

section CommRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

/-- The bilinear convolution `twoSidedRestrictedMul` is the multiplication of `A⟨X, X⁻¹⟩`. -/
-- Not `@[simp]`: it would rewrite the left-hand side of `coe_twoSidedRestrictedMul`.
theorem twoSidedRestrictedMul_apply (f g : twoSidedRestrictedSubmodule A A) :
    twoSidedRestrictedMul f g = f * g := Subtype.ext <| coe_twoSidedRestrictedMul f g

/-- **`A⟨X, X⁻¹⟩` is commutative when `A` is** (Wedhorn, Example 6.39). -/
noncomputable instance twoSidedRestrictedSubmodule.instCommRing :
    CommRing (twoSidedRestrictedSubmodule A A) where
  mul_comm _ _ := Subtype.ext <| DiscreteConvolution.addRingConvolution_comm _ _

/-- **`A⟨X, X⁻¹⟩` is an `A`-algebra** (Wedhorn, Example 6.39), with the coefficientwise scalar
action it carries as a submodule of `ℤ → A`. -/
noncomputable instance twoSidedRestrictedSubmodule.instAlgebra :
    Algebra A (twoSidedRestrictedSubmodule A A) :=
  .ofModule (by simp [← twoSidedRestrictedMul_apply]) (by simp [← twoSidedRestrictedMul_apply])

/-- The structure map sends `a` to the constant series `a = a · X⁰`. -/
@[simp, norm_cast]
theorem coe_algebraMap_twoSidedRestrictedSubmodule (a : A) :
    (algebraMap A (twoSidedRestrictedSubmodule A A) a : ℤ → A) = Pi.single 0 a := by
  simp [Algebra.algebraMap_eq_smul_one, ← Pi.single_smul]

/-- The degree-`0` monomial `a X⁰` is the constant series `a`, the image of `a` under the structure
map. -/
@[simp]
theorem twoSidedMonomial_zero_left (a : A) :
    twoSidedMonomial 0 a = algebraMap A (twoSidedRestrictedSubmodule A A) a :=
  Subtype.ext <| by simp

end CommRing

end TauCeti.Huber
