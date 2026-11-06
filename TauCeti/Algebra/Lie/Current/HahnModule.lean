/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Topology
public import TauCeti.RingTheory.HahnSeries.TensorProduct
public import TauCeti.RingTheory.LaurentSeries.Lattice

import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Tensor currents and their coefficientwise completion

The canonical map from tensor currents `R((t)) ⊗[R] V` to `V`-valued Laurent series
preserves the order filtration. For free coefficients it is a uniform embedding, and its
image is dense because it contains all Laurent monomials. The target is Hausdorff and complete
even when `V` is not finitely generated.

Consequently, over a nontrivial commutative ring with free coefficients, the order topology
on tensor currents is complete exactly when `V` is finitely generated. Over a field this says
that tensor currents are complete exactly in finite dimension. The obstruction in infinite
dimension is not a missing lower bound on the exponents: a tensor has all its coefficients
in one finitely generated submodule, whereas a general vector-valued Laurent series need not.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.1, for the topology on
  tensor currents and the finite-dimensional comparison with vector-valued Laurent series.
-/

public section

noncomputable section

open Filter Topology
open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

-- Match the coefficientwise scalar action used by the tensor-current comparison.
attribute [local instance 1100] HahnSeries.instAlgebra

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The coefficient comparison pulls the Laurent lattice back to the tensor-current order
submodule. Freeness is needed to detect tensor currents by their coefficients. -/
@[simp]
theorem tensorProductToHahnModule_mem_lattice_iff [Module.Free R V]
    (u : currentAlgebra R V) (N : ℤ) :
    _root_.HahnModule.tensorProductToHahnModule ℤ R V u ∈ HahnModule.lattice R V N ↔
      u ∈ orderSubmodule R V N := by
  simp only [HahnModule.mem_lattice_iff, _root_.HahnModule.coeff_tensorProductToHahnModule,
    mem_orderSubmodule_iff]

/-- The order topology on tensor currents is induced by the lattice topology on vector-valued
Laurent series, without a finite-generation hypothesis. -/
theorem isInducing_tensorProductToHahnModule [Module.Free R V] :
    IsInducing (_root_.HahnModule.tensorProductToHahnModule ℤ R V) := by
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  apply (hasBasis_nhds_zero R V).eq_of_same_basis
  convert (HahnModule.hasBasis_nhds_zero_lattice R V).comap
    (_root_.HahnModule.tensorProductToHahnModule ℤ R V) using 1
  ext N u
  simp

/-- Tensor currents embed uniformly into vector-valued Laurent series. In particular, this
comparison preserves and reflects Cauchy filters. -/
theorem isUniformEmbedding_tensorProductToHahnModule [Module.Free R V] :
    IsUniformEmbedding (_root_.HahnModule.tensorProductToHahnModule ℤ R V) where
  toIsUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing
    (isInducing_tensorProductToHahnModule R V)
  injective := _root_.HahnModule.tensorProductToHahnModule_injective

/-- Tensor currents are dense in vector-valued Laurent series, even for nonfree coefficient
modules: their image contains the dense span of Laurent monomials. -/
theorem denseRange_tensorProductToHahnModule :
    DenseRange (_root_.HahnModule.tensorProductToHahnModule ℤ R V) := by
  apply (HahnModule.dense_span_single R V).mono
  have hspan : Submodule.span R (Set.range fun p : ℤ × V ↦
      _root_.HahnModule.of R (HahnSeries.single p.1 p.2)) ≤
      ((_root_.HahnModule.tensorProductToHahnModule ℤ R V).restrictScalars R).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n, v⟩, rfl⟩
    exact ⟨HahnSeries.single n 1 ⊗ₜ[R] v, by simp⟩
  exact hspan

/-- Tensor currents with free coefficients are complete precisely when the coefficient module
is finitely generated. Over a field this is exactly finite-dimensionality. -/
theorem completeSpace_iff_moduleFinite [Nontrivial R] [Module.Free R V] :
    CompleteSpace (currentAlgebra R V) ↔ Module.Finite R V := by
  constructor
  · intro h
    let := h
    apply _root_.HahnModule.tensorProductToHahnModule_int_surjective_iff.mp
    have hc := (isUniformEmbedding_tensorProductToHahnModule R V).isClosedEmbedding.isClosed_range
    have hd := denseRange_tensorProductToHahnModule R V
    intro x
    exact hc.closure_subset (hd x)
  · intro h
    let := h
    infer_instance

end TauCeti.CurrentAlgebra
