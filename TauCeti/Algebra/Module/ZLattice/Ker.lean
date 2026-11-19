/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import TauCeti.Algebra.Module.ZLattice.Rank

/-!
# The lattice induced on the kernel of a lattice-preserving map

Let `L` be a full lattice in a finite-dimensional real normed space `E`, and let `f : E → E'` be a
linear map, over a normed field `K` such as `ℝ` or `ℂ`, which carries `L` into a discrete subgroup
`L'` of `E'`. Then `L ∩ ker f` is a full lattice in the subspace `ker f`.

For complex tori this is the lattice of the identity component of the kernel: when `f` is
complex linear, the kernel `f⁻¹(L') / L` of the induced homomorphism `E / L → E' / L'` has
identity component the complex torus `ker f / (L ∩ ker f)`, and this file supplies its full
lattice. That identity component is the image of `ker f / (L ∩ ker f) → E / L`
(`Submodule.range_orbitRelQuotientMap_ker_subtype`), and this map is a closed embedding
(`Submodule.isClosedEmbedding_orbitRelQuotientMap_subtype`) once `L ∩ ker f` is a full lattice.

The hypothesis on `f` cannot be dropped: an irrational line through the lattice `ℤ²` in `ℝ²` is
the kernel of a linear form, and it meets the lattice only in `0`.

## Main results

* `ZLattice.isZLattice_comap_ker_subtype`: if `f(L) ⊆ L'` with `L'` discrete, then `L ∩ ker f`
  is a full lattice in `ker f`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1.
-/

public section

open Module Submodule

namespace ZLattice

variable {K : Type*} [NormedField K] [NormedSpace ℝ K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace K E] [IsScalarTower ℝ K E]
  [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedSpace K E']
  [IsScalarTower ℝ K E']
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- If a linear map `f` carries a full lattice `L` into a discrete subgroup `L'`, then
`L ∩ ker f` is a full lattice in the subspace `ker f`. Taking `L' = f(L)`, it suffices that
`f(L)` be discrete. For complex linear `f` this is the lattice of the complex torus
`ker f / (L ∩ ker f)`. -/
theorem isZLattice_comap_ker_subtype {L' : Submodule ℤ E'} [DiscreteTopology L'] (f : E →ₗ[K] E')
    (hf : L.map (f.restrictScalars ℤ) ≤ L') :
    IsZLattice ℝ (ZLattice.comap K L (LinearMap.ker f).subtype) where
  span_top := by
    let g := f.restrictScalars ℤ
    let fR := f.restrictScalars ℝ
    -- `M = L ∩ ker f`, as a subgroup of `E`.
    let M := L ⊓ (LinearMap.ker f).restrictScalars ℤ
    have : DiscreteTopology M := DiscreteTopology.of_subset (s := (L : Set E)) ‹_› inf_le_left
    have : DiscreteTopology (L.map g) := DiscreteTopology.of_subset (s := (L' : Set E')) ‹_› hf
    -- Rank count: `rank f(L) ≤ dim (range f)` and `rank L = dim E`, so
    -- `dim (ker f) ≤ rank M = dim (span ℝ M)`.
    have hrange : finrank ℤ (L.map g) ≤ finrank ℝ (LinearMap.range fR) := by
      rw [TauCeti.discreteTopology_iff_finrank_eq_finrank_span.mp ‹_›]
      refine Submodule.finrank_mono (span_le.2 ?_)
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    have hker : finrank ℤ (LinearMap.ker (g.domRestrict L)) = finrank ℝ (span ℝ (M : Set E)) := by
      have : LinearMap.ker (g.domRestrict L) = comap L.subtype M := by
        simp [M, g, LinearMap.ker_domRestrict, comap_inf]
      rw [this, (comapSubtypeEquivOfLe inf_le_left).finrank_eq]
      exact TauCeti.discreteTopology_iff_finrank_eq_finrank_span.mp ‹_›
    have hR := LinearMap.finrank_range_add_finrank_ker fR
    have hZ := LinearMap.finrank_range_add_finrank_ker (g.domRestrict L)
    rw [LinearMap.ker_restrictScalars] at hR
    rw [LinearMap.range_domRestrict, ZLattice.rank ℝ L] at hZ
    have hS : span ℝ (M : Set E) = (LinearMap.ker f).restrictScalars ℝ :=
      eq_of_le_of_finrank_le (span_le.2 fun x hx ↦ hx.2) (by omega)
    -- The inclusion `ker f → E` maps `L ∩ ker f`, as a subgroup of `ker f`, onto `M`.
    let ι := (LinearMap.ker f).subtype.restrictScalars ℝ
    have himage : ι '' (ZLattice.comap K L (LinearMap.ker f).subtype : Set (LinearMap.ker f)) =
        (M : Set E) := by
      ext x
      simp [ι, M, and_comm]
    -- Transport `span ℝ M = ker f` along `ι`.
    refine map_injective_of_injective (f := ι) (LinearMap.ker f).injective_subtype ?_
    rw [map_span, himage, hS, Submodule.map_top, LinearMap.range_restrictScalars, range_subtype]

end ZLattice
