/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.DiscreteConvolution

/-!
# Convolution of two-sided restricted series

The coefficient family underlying a two-sided restricted series is closed under additive
convolution.  For restricted families `f g : ℤ → A`, the coefficient at `n` is

```text
∑' (i,j), i + j = n, f i * g j.
```

The products `f i * g j` tend to zero cofinitely on `ℤ × ℤ`; completeness of `A` upgrades this
to summability on every addition fiber. The resulting coefficients again tend to zero: modulo an
open additive subgroup, only finitely many pairs contribute, hence only their finitely many degrees
can contribute.

This supplies the analytic part of multiplication on Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39).
The ring laws require rearranging iterated unconditional sums and are deliberately left to the
subsequent construction of that ring.

## Main results

* `TauCeti.Huber.addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`: every coefficient
  convolution is summable.
* `TauCeti.Huber.addRingConvolution_mem_twoSidedRestrictedSubmodule`: convolution preserves the
  two-sided restricted condition.
* `TauCeti.Huber.twoSidedRestrictedMul`: convolution as a bilinear map on the restricted
  coefficient module.
* `TauCeti.Huber.twoSidedRestrictedMul_comm`: commutativity of this multiplication.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.39 and Lemma 8.33.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti.Huber

section Convergence

section Summability

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A]

/-- In a complete nonarchimedean ring, the convolution coefficients of two two-sided restricted
families are summable. -/
theorem addConvolutionExists_of_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g :=
  TauCeti.addConvolutionExists_of_zeroAtFilter_cofinite
    (mem_twoSidedRestrictedSubmodule.mp hf) (mem_twoSidedRestrictedSubmodule.mp hg)

end Summability

section Preservation

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Additive ring convolution preserves two-sided restrictedness. -/
theorem addRingConvolution_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    f ⋆ᵣ₊ g ∈ twoSidedRestrictedSubmodule A A :=
  mem_twoSidedRestrictedSubmodule.mpr <|
    TauCeti.ZeroAtFilter.addRingConvolution
      (mem_twoSidedRestrictedSubmodule.mp hf) (mem_twoSidedRestrictedSubmodule.mp hg)

end Preservation

end Convergence

section Bilinear

variable {A : Type*} [CommRing A] [UniformSpace A] [hA : IsUniformAddGroup A]
  [NonarchimedeanRing A] [hComplete : CompleteSpace A] [T2Space A]

/-- **Multiplication convolution on two-sided restricted coefficients**, as a bilinear map.

Its value is Mathlib's additive discrete convolution, restricted to the coefficient submodule by
`addRingConvolution_mem_twoSidedRestrictedSubmodule`. -/
noncomputable def twoSidedRestrictedMul :
    twoSidedRestrictedSubmodule A A →ₗ[A]
      twoSidedRestrictedSubmodule A A →ₗ[A] twoSidedRestrictedSubmodule A A :=
  LinearMap.mk₂ A
    (fun f g ↦ ⟨(f : ℤ → A) ⋆ᵣ₊ (g : ℤ → A),
      addRingConvolution_mem_twoSidedRestrictedSubmodule f.2 g.2⟩)
    (fun f₁ f₂ g ↦ Subtype.ext <| DiscreteConvolution.add_addRingConvolution
      (f₁ : ℤ → A) (f₂ : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f₁.2 g.2)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f₂.2 g.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.smul_addRingConvolution c
      (f : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2))
    (fun f g₁ g₂ ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_add
      (f : ℤ → A) (g₁ : ℤ → A) (g₂ : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g₁.2)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g₂.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_smul c
      (f : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2))

include hA hComplete in
/-- The coefficient family of `twoSidedRestrictedMul f g` is the additive ring convolution of
the coefficient families of `f` and `g`. -/
@[simp]
theorem coe_twoSidedRestrictedMul (f g : twoSidedRestrictedSubmodule A A) :
    ((twoSidedRestrictedMul f g : twoSidedRestrictedSubmodule A A) : ℤ → A) =
      (f : ℤ → A) ⋆ᵣ₊ (g : ℤ → A) := (rfl)

include hA hComplete in
/-- The `n`-th coefficient of `twoSidedRestrictedMul f g` is the sum over pairs of degrees adding
to `n`. -/
theorem coe_twoSidedRestrictedMul_apply (f g : twoSidedRestrictedSubmodule A A) (n : ℤ) :
    ((twoSidedRestrictedMul f g : twoSidedRestrictedSubmodule A A) : ℤ → A) n =
      ∑' p : DiscreteConvolution.addFiber n,
        (f : ℤ → A) p.1.1 * (g : ℤ → A) p.1.2 := by
  rw [coe_twoSidedRestrictedMul, DiscreteConvolution.addRingConvolution_apply]

include hA hComplete in
/-- Multiplication convolution of two-sided restricted coefficient families is commutative. -/
theorem twoSidedRestrictedMul_comm (f g : twoSidedRestrictedSubmodule A A) :
    twoSidedRestrictedMul f g = twoSidedRestrictedMul g f :=
  Subtype.ext <| by
    rw [coe_twoSidedRestrictedMul, coe_twoSidedRestrictedMul,
      DiscreteConvolution.addRingConvolution_comm]

end Bilinear

end TauCeti.Huber

end
