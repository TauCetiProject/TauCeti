/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic

/-!
# Compactness from truncated fundamental sets

The compactness argument for a cusp compactification uses a compact part of a fundamental polygon
after removing sufficiently high cusp
horodiscs. This file isolates that argument: if, at every choice of cusp heights, one compact
subset of the upper half-plane meets all remaining orbits, then the compactified quotient is
compact. Finiteness of the cusp orbits allows an arbitrary open cover to be reduced to finitely
many cusp neighbourhoods and a finite cover of that compact subset.

The hypothesis is the compact truncation property expected of a fundamental polygon. It is
independent of the definition of the compactification.

## Main result

* `Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations`: compactness from a
  compact truncated fundamental set at every family of cusp heights.
-/

public section

open MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] [Finite Γ.CuspOrbit]

/-- If every truncation of the orbit space outside horodiscs has a compact set of
representatives in the upper half-plane, then adjoining the finitely many cusp orbits makes the
quotient compact. The datum `D C` may use any scaling at each cusp orbit. -/
theorem compactSpace_of_compact_truncations
    (D : Γ.CuspOrbit → Γ.CuspDatum) (hD : ∀ C, (D C).cuspOrbit = C)
    (htrunc : ∀ A : Γ.CuspOrbit → ℝ, ∃ K : Set ℍ, IsCompact K ∧
      ∀ q : orbitRel.Quotient Γ ℍ,
        q ∈ (Quotient.mk (orbitRel Γ ℍ)) '' K ∨
          ∃ C : Γ.CuspOrbit,
            q ∈ (Quotient.mk (orbitRel Γ ℍ)) '' horodisc (D C) (A C)) :
    CompactSpace Γ.CompactifiedQuotient := by
  classical
  have : Fintype Γ.CuspOrbit := Fintype.ofFinite _
  apply isCompact_univ_iff.mp
  refine isCompact_of_finite_subcover fun U hU hcover ↦ ?_
  have hcusp (C : Γ.CuspOrbit) : ∃ i, ∃ A : ℝ,
      cuspNhd (D C) A ⊆ U i := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (ofCusp C)))
    have hmem : U i ∈ 𝓝 (ofCusp (D C).cuspOrbit) := by
      rw [hD C]
      exact (hU i).mem_nhds hi
    obtain ⟨A, hA⟩ := (mem_nhds_ofCusp_iff (D C)).mp hmem
    exact ⟨i, A, hA⟩
  choose i A hA using hcusp
  obtain ⟨K, hK, hcoverK⟩ := htrunc A
  have hcompact : IsCompact ((fun z : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) z)) '' K) :=
    hK.image (continuous_ofQuotient.comp continuous_quotient_mk')
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover U hU fun x hx ↦
    hcover (mem_univ x)
  refine ⟨t ∪ Finset.univ.image i, ?_⟩
  intro x _
  cases x with
  | ofCusp C =>
      apply mem_iUnion.mpr
      refine ⟨i C, mem_iUnion.mpr ⟨by simp, ?_⟩⟩
      exact hA C (by simp [hD C])
  | ofQuotient q =>
      rcases hcoverK q with hq | ⟨C, hq⟩
      · obtain ⟨z, hz, rfl⟩ := hq
        obtain ⟨j, hj⟩ := mem_iUnion.mp (ht ⟨z, hz, rfl⟩)
        obtain ⟨hjmem, hjU⟩ := mem_iUnion.mp hj
        exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr
          ⟨Finset.mem_union_left _ hjmem, hjU⟩⟩
      · apply mem_iUnion.mpr
        refine ⟨i C, mem_iUnion.mpr ⟨by simp, ?_⟩⟩
        exact hA C ((ofQuotient_mem_cuspNhd_iff (D C) (A C)).mpr hq)

end Subgroup.CompactifiedQuotient
