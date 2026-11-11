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

Conversely, finiteness of the cusp orbits is a consequence of compactness: the cusp orbits form a
closed subset of the compactified quotient, and each of them is isolated in it by its cusp
neighbourhoods.

## Main results

* `Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations`: compactness from a
  compact truncated fundamental set at every family of cusp heights.
* `Subgroup.CompactifiedQuotient.finite_cuspOrbit`: a compact compactified quotient has only
  finitely many cusp orbits.
-/

public section

open MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-- A compact cusp compactification has only finitely many cusp orbits. The adjoined cusps form a
closed, hence compact, subset, and a cusp neighbourhood of a cusp orbit contains no other cusp
orbit. -/
theorem finite_cuspOrbit [CompactSpace Γ.CompactifiedQuotient] : Finite Γ.CuspOrbit := by
  have hdisc : IsDiscrete (range (ofCusp (Γ := Γ))) := by
    refine isDiscrete_iff_forall_mem_exists_isOpen.mpr ?_
    rintro _ ⟨C, rfl⟩
    obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
    refine ⟨cuspNhd D 0, isOpen_cuspNhd D 0, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨hx, C', rfl⟩
      rw [(ofCusp_mem_cuspNhd_iff D 0).mp hx]
    · rintro rfl
      exact ⟨ofCusp_mem_cuspNhd D 0, _, rfl⟩
  exact (finite_range_iff fun _ _ h ↦ ofCusp.inj h).mp
    (isClosed_range_ofCusp.isCompact.finite hdisc)

variable [Finite Γ.CuspOrbit]

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
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover U hU fun x _ ↦
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
