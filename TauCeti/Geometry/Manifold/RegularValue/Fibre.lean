/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Topology.DiscreteSubset
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# Fibres over regular values of equidimensional maps

Let `f : M → N` be a `C^n` map, `n ≠ 0`, between manifolds over `ℝ` or `ℂ` (more generally, over
a field `𝕜` with `IsRCLikeNormedField 𝕜`) modelled on finite-dimensional spaces of the same
dimension. At a regular point the manifold derivative of `f` is bijective, so `f` is injective
near that point. Hence the fibre of `f` over a regular value is a discrete subset of `M`, and it is
finite when `M` is compact. These finite fibres are what the mapping degree of a
map between compact oriented manifolds counts with signs.

The manifolds may have boundary or corners: local injectivity at a regular point is proved in
charts, within the range of the model with corners, rather than through the inverse function
theorem.

## Main results

* `TauCeti.IsRegularValue.isDiscrete_preimage`: the fibre over a regular value is discrete.
* `TauCeti.IsRegularValue.finite_preimage`: on a compact manifold, the fibre over a regular value
  is finite.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory, the finiteness of fibres over regular values
  used to define the degree.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §1, where the number of preimages of a regular value is shown to be finite.
-/

public section

open Function Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H M E' H' N : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {x : M} {y : N} {n : WithTop ℕ∞}

/-- The fibre of a `C^n` map, `n ≠ 0`, between manifolds modelled on finite-dimensional spaces of
the same dimension over a regular value is a discrete subset. -/
theorem IsRegularValue.isDiscrete_preimage (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E')
    (hf : ContMDiff I J n f) (hn : n ≠ 0) (hy : IsRegularValue I J f y) :
    IsDiscrete (f ⁻¹' {y}) := by
  refine IsDiscrete.of_nhdsWithin fun x hx ↦ ?_
  obtain ⟨t, ht, hinj⟩ := (hf x).exists_mem_nhds_injOn hn
    ((isRegularPoint_iff_injective_mfderiv hdim).1 (hy.isRegularPoint hx))
  -- On `t` the map `f` is injective, so `x` is the only point of `t` in the fibre.
  refine le_pure_iff.2 (mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨t, ht, fun z hz ↦ ?_⟩)
  exact hinj hz.1 (mem_of_mem_nhds ht) (hz.2.trans hx.symm)

/-- The fibre of a `C^n` map, `n ≠ 0`, from a compact manifold, between manifolds modelled on
finite-dimensional spaces of the same dimension, over a regular value is finite. -/
theorem IsRegularValue.finite_preimage [CompactSpace M] [T1Space N]
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E') (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hy : IsRegularValue I J f y) : (f ⁻¹' {y}).Finite :=
  (isClosed_singleton.preimage hf.continuous).isCompact.finite
    (hy.isDiscrete_preimage hdim hf hn)

end TauCeti
