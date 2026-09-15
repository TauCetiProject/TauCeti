/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Convolution of two-sided restricted series

The coefficient family underlying a two-sided restricted series is closed under additive
convolution.  For restricted families `f g : ℤ → A`, the coefficient at `n` is

```text
∑' (i,j), i + j = n, f i * g j.
```

Each coefficient sum exists because the products `f i * g j` tend to zero off a finite subset of
`ℤ × ℤ`.  The resulting coefficients again tend to zero: modulo an open additive subgroup,
only finitely many pairs contribute, hence only their finitely many degrees can contribute.

This supplies the analytic part of multiplication on Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39).
The ring laws require rearranging iterated unconditional sums and are deliberately left to the
subsequent construction of that ring.

## Main results

* `TauCeti.Huber.addConvolutionExists_twoSidedRestricted`: every coefficient convolution is
  summable.
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

variable {A : Type*} [Ring A] [UniformSpace A] [NonarchimedeanRing A]

/-- **The additive convolution of two restricted coefficient families exists at every degree.**

The product family on `ℤ × ℤ` tends to zero along the cofinite filter.  Restricting it to an
addition fiber preserves this convergence because the fiber inclusion is injective; completeness
then turns cofinite convergence to zero into unconditional summability. -/
theorem addConvolutionExists_twoSidedRestricted
    [IsUniformAddGroup A] [CompleteSpace A]
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g := by
  have hf' : ZeroAtFilter cofinite f := mem_twoSidedRestrictedSubmodule.mp hf
  have hg' : ZeroAtFilter cofinite g := mem_twoSidedRestrictedSubmodule.mp hg
  intro n
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  exact (tendsto_mul_cofinite_nhds_zero hf' hg').comp
    (Function.Injective.tendsto_cofinite Subtype.val_injective)

/-- **Convolution preserves two-sided restrictedness.** If `f` and `g` tend to zero away from
finite sets of degrees, then so does their additive multiplication convolution.

For an open additive subgroup `W`, only finitely many pairs `(i,j)` have `f i * g j ∉ W`.
Outside the finite image of those pairs under addition, every term in the coefficient sum belongs
to `W`; closedness of `W` then puts the sum itself in `W`. -/
theorem addRingConvolution_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    f ⋆ᵣ₊ g ∈ twoSidedRestrictedSubmodule A A := by
  have hf' : ZeroAtFilter cofinite f := mem_twoSidedRestrictedSubmodule.mp hf
  have hg' : ZeroAtFilter cofinite g := mem_twoSidedRestrictedSubmodule.mp hg
  rw [mem_twoSidedRestrictedSubmodule_iff_finite_notMem]
  intro W
  let bad : Set (ℤ × ℤ) := {p | f p.1 * g p.2 ∉ (W : Set A)}
  have hbad : bad.Finite :=
    NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mp
      (tendsto_mul_cofinite_nhds_zero hf' hg') W
  apply (hbad.image fun p : ℤ × ℤ ↦ p.1 + p.2).subset
  intro n hn
  by_contra hnim
  apply hn
  rw [DiscreteConvolution.addRingConvolution_apply]
  have hW : IsClosed (W : Set A) :=
    AddSubgroup.isClosed_of_isOpen W.toAddSubgroup W.isOpen
  apply tsum_mem (S := OpenAddSubgroup A) (s := W)
    hW
  intro p
  by_contra hp
  exact hnim ⟨(p.1.1, p.1.2), hp, DiscreteConvolution.mem_addFiber.mp p.2⟩

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
      (addConvolutionExists_twoSidedRestricted f₁.2 g.2)
      (addConvolutionExists_twoSidedRestricted f₂.2 g.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.smul_addRingConvolution c
      (f : ℤ → A) (g : ℤ → A) (addConvolutionExists_twoSidedRestricted f.2 g.2))
    (fun f g₁ g₂ ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_add
      (f : ℤ → A) (g₁ : ℤ → A) (g₂ : ℤ → A)
      (addConvolutionExists_twoSidedRestricted f.2 g₁.2)
      (addConvolutionExists_twoSidedRestricted f.2 g₂.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_smul c
      (f : ℤ → A) (g : ℤ → A) (addConvolutionExists_twoSidedRestricted f.2 g.2))

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
@[simp]
theorem twoSidedRestrictedMul_apply (f g : twoSidedRestrictedSubmodule A A) (n : ℤ) :
    ((twoSidedRestrictedMul f g : twoSidedRestrictedSubmodule A A) : ℤ → A) n =
      ∑' p : DiscreteConvolution.addFiber n,
        (f : ℤ → A) p.1.1 * (g : ℤ → A) p.1.2 := (rfl)

include hA hComplete in
/-- Multiplication convolution of two-sided restricted coefficient families is commutative. -/
theorem twoSidedRestrictedMul_comm (f g : twoSidedRestrictedSubmodule A A) :
    twoSidedRestrictedMul f g = twoSidedRestrictedMul g f :=
  Subtype.ext <| DiscreteConvolution.addRingConvolution_comm (f : ℤ → A) (g : ℤ → A)

end Bilinear

end TauCeti.Huber

end
