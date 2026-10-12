/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# Discrete convolution of cofinite-zero families

In a nonarchimedean ring, additive convolution preserves families that tend to zero along the
cofinite filter, without requiring a unit or associative multiplication. When the ring is also
complete, every coefficient sum in the convolution is summable. If multiplication is associative
and the ring is `T0`, convolution of such families is associative.

## Main results

* `Filter.ZeroAtFilter.addConvolutionExists`: cofinite-zero families have summable
  additive convolution coefficients in a complete nonarchimedean ring.
* `Filter.ZeroAtFilter.addRingConvolution`: additive ring convolution preserves convergence to
  zero along the cofinite filter.
* `Filter.ZeroAtFilter.summable_sigma_addFiber_mul_mul`: the triple products of cofinite-zero
  families are summable over each fibre of `a + b + c = n`.
* `Filter.ZeroAtFilter.addRingConvolution_assoc`: additive ring convolution of cofinite-zero
  families is associative in a complete `T0` nonarchimedean ring.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace Filter

variable {ι A : Type*} [AddMonoid ι]

/-- In a complete nonarchimedean ring, not necessarily unital or associative, every additive
convolution coefficient of two families that tend to zero cofinitely is summable. -/
theorem ZeroAtFilter.addConvolutionExists
    [NonUnitalNonAssocRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
    [ContinuousMul A] [CompleteSpace A]
    {f g : ι → A} (hf : ZeroAtFilter cofinite f) (hg : ZeroAtFilter cofinite g) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g := by
  intro n
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Function.comp_def, LinearMap.mul_apply'] using
    (tendsto_mul_cofinite_nhds_zero hf hg).comp
      (Function.Injective.tendsto_cofinite Subtype.val_injective)

/-- Additive ring convolution preserves convergence to zero along the cofinite filter in a
nonarchimedean ring, not necessarily unital or associative. -/
theorem ZeroAtFilter.addRingConvolution
    [NonUnitalNonAssocRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A] [ContinuousMul A]
    {f g : ι → A} (hf : ZeroAtFilter cofinite f) (hg : ZeroAtFilter cofinite g) :
    ZeroAtFilter cofinite (f ⋆ᵣ₊ g) := by
  rw [NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem]
  intro W
  let bad : Set (ι × ι) := {p | f p.1 * g p.2 ∉ (W : Set A)}
  have hbad : bad.Finite :=
    NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mp
      (tendsto_mul_cofinite_nhds_zero hf hg) W
  apply (hbad.image fun p : ι × ι ↦ p.1 + p.2).subset
  intro n hn
  by_contra hnim
  apply hn
  rw [DiscreteConvolution.addRingConvolution_apply]
  apply tsum_mem (S := OpenAddSubgroup A) (s := W) W.isClosed
  intro p
  by_contra hp
  exact hnim ⟨(p.1.1, p.1.2), hp, DiscreteConvolution.mem_addFiber.mp p.2⟩

open DiscreteConvolution in
/-- In a complete nonarchimedean ring, not necessarily unital or associative, the family
`f a * g b * h c` over the triples with `a + b + c = n`, indexed as pairs `((a, b), c)` with
`a + b = m` and `m + c = n`, is summable when `f`, `g` and `h` tend to zero cofinitely. -/
theorem ZeroAtFilter.summable_sigma_addFiber_mul_mul [NonUnitalNonAssocRing A]
    [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A] [ContinuousMul A]
    [CompleteSpace A] {f g h : ι → A} (hf : ZeroAtFilter cofinite f)
    (hg : ZeroAtFilter cofinite g) (hh : ZeroAtFilter cofinite h) (n : ι) :
    Summable fun σ : Σ p : addFiber n, addFiber p.1.1 ↦ f σ.2.1.1 * g σ.2.1.2 * h σ.1.1.2 := by
  -- `((a, b), c) ↦ f a * g b * h c` tends to zero cofinitely, and `σ ↦ ((a, b), c)` is injective
  have hj : Function.Injective fun σ : Σ p : addFiber n, addFiber p.1.1 ↦ (σ.2.1, σ.1.1.2) :=
    fun _ _ _ ↦ by grind
  have ht := (tendsto_mul_cofinite_nhds_zero (tendsto_mul_cofinite_nhds_zero hf hg) hh).comp
    hj.tendsto_cofinite
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht

open DiscreteConvolution in
/-- In a complete `T0` nonarchimedean ring, not necessarily unital, additive ring convolution of
families that tend to zero cofinitely is associative. The index monoid `ι` need not be commutative;
to rebracket longer products, `ZeroAtFilter.addRingConvolution` supplies the hypotheses for the
partial products. -/
theorem ZeroAtFilter.addRingConvolution_assoc [NonUnitalRing A] [UniformSpace A]
    [IsUniformAddGroup A] [NonarchimedeanAddGroup A] [ContinuousMul A] [CompleteSpace A] [T0Space A]
    {f g h : ι → A}
    (hf : ZeroAtFilter cofinite f) (hg : ZeroAtFilter cofinite g) (hh : ZeroAtFilter cofinite h) :
    (f ⋆ᵣ₊ g) ⋆ᵣ₊ h = f ⋆ᵣ₊ g ⋆ᵣ₊ h := by
  let : IsTopologicalRing A := { toIsTopologicalSemiring := ⟨⟩ }
  exact DiscreteConvolution.addRingConvolution_assoc (hf.addConvolutionExists hg)
    (hg.addConvolutionExists hh) (hf.summable_sigma_addFiber_mul_mul hg hh)

end Filter

end
