/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Discrete convolution of cofinite-zero families

In a nonarchimedean ring, additive convolution preserves families that tend to zero along the
cofinite filter. When the ring is also complete, every coefficient sum in the convolution is
summable.

## Main results

* `TauCeti.addConvolutionExists_of_zeroAtFilter_cofinite`: cofinite-zero families have summable
  additive convolution coefficients in a complete nonarchimedean ring.
* `TauCeti.ZeroAtFilter.addRingConvolution`: additive ring convolution preserves convergence to
  zero along the cofinite filter.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti

variable {ι A : Type*} [AddMonoid ι]

/-- In a complete nonarchimedean ring, every additive convolution coefficient of two families
that tend to zero cofinitely is summable. -/
theorem addConvolutionExists_of_zeroAtFilter_cofinite
    [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
    {f g : ι → A} (hf : ZeroAtFilter cofinite f) (hg : ZeroAtFilter cofinite g) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g := by
  intro n
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Function.comp_def, LinearMap.mul_apply'] using
    (tendsto_mul_cofinite_nhds_zero hf hg).comp
      (Function.Injective.tendsto_cofinite Subtype.val_injective)

/-- Additive ring convolution preserves convergence to zero along the cofinite filter in a
nonarchimedean ring. -/
theorem ZeroAtFilter.addRingConvolution
    [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]
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
  have hW : IsClosed (W : Set A) :=
    AddSubgroup.isClosed_of_isOpen W.toAddSubgroup W.isOpen
  apply tsum_mem (S := OpenAddSubgroup A) (s := W) hW
  intro p
  by_contra hp
  exact hnim ⟨(p.1.1, p.1.2), hp, DiscreteConvolution.mem_addFiber.mp p.2⟩

end TauCeti

end
