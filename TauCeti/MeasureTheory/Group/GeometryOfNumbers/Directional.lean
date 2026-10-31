/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima

/-!
# Directional families for the successive minima

A compact convex neighbourhood of zero admits independent lattice vectors attaining all of its
successive minima simultaneously. `MeasureTheory.exists_directional_set'` works for a discrete
integer submodule of any rank, including zero; `MeasureTheory.exists_directional_set` gives the
vectors in the submodule itself. For a full lattice, `MeasureTheory.exists_directional_basis`
packages the vectors as a real ambient basis. These vectors need not be an integral lattice basis.

The lower-rank construction applies the convex-body minimum theorem inside the real span of the
submodule. Thus it requires neither symmetry of the neighbourhood nor fullness in the original
ambient space.

## References

The names and statements follow Kevin H. Wilson's successive-minima proposal for Mathlib,
`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` at revision `8423d1c` of
<https://github.com/khwilson/mathlib4> (Apache 2.0, by Alex J. Best, Yaël Dillies and Kevin H. Wilson).
The proof reuses Tau Ceti's convex-body minima, whose greedy construction follows Cassels,
*An Introduction to the Geometry of Numbers*, Chapter VIII, §1.
-/

public section

open Module Submodule
open scoped NNReal Pointwise Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}

/-- A compact convex neighbourhood of zero admits a real basis of lattice vectors attaining all
successive minima. The basis need not span the lattice over `ℤ`. -/
theorem exists_directional_basis [IsZLattice ℝ L] (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E,
      ∀ i, b i ∈ successiveMin L s i.val • s ∩ L := by
  let K : ConvexBody E := ⟨s, hsc, hs, ⟨0, mem_of_mem_nhds hs₀⟩⟩
  have hK : (0 : E) ∈ interior (K : Set E) := mem_interior_iff_mem_nhds.2 hs₀
  obtain ⟨b, hbL, -, hbK, -⟩ := ZLattice.exists_basis_gauge_eq_successiveMin L hK
  have hKs : (K : Set E) = s := ConvexBody.coe_mk _ _ _ _
  refine ⟨b, fun i ↦ ⟨?_, hbL i⟩⟩
  rw [← hKs, NNReal.smul_def, coe_successiveMin L K i]
  exact hbK i

/-- A compact convex neighbourhood of zero admits a real-independent family of lattice vectors
attaining all successive minima below the integer rank of the lattice. Fullness is not required.
The family spans the real span of the lattice, but need not span it over `ℤ`. -/
theorem exists_directional_set' (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → E,
      (∀ j, v j ∈ successiveMin L s j.val • s ∩ L) ∧ LinearIndependent ℝ v := by
  let W := span ℝ (L : Set E)
  let L' : Submodule ℤ W := L.comap (W.restrictScalars ℤ).subtype
  let s' : Set W := Subtype.val ⁻¹' s
  let e : L' ≃ₗ[ℤ] L := comapSubtypeEquivOfLe (p := L) (q := W.restrictScalars ℤ) subset_span
  -- The equivalence forgets only the proof of membership in the real span.
  have he : Continuous e := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : DiscreteTopology L' := DiscreteTopology.of_continuous_injective he e.injective
  have : IsZLattice ℝ L' := ⟨span_span_coe_preimage⟩
  have hs' : IsCompact s' :=
    (W.isClosedEmbedding_subtype W.closed_of_finiteDimensional).isCompact_preimage hs
  have hs₀' : s' ∈ 𝓝 (0 : W) := continuous_subtype_val.continuousAt.preimage_mem_nhds hs₀
  have hsc' : Convex ℝ s' := hsc.linear_preimage W.subtype
  -- Dilating the slice agrees with slicing the dilate, also at scalar zero.
  have hdilate (r : ℝ≥0) (x : W) : x ∈ r • s' ↔ (x : E) ∈ r • s := by
    by_cases hr : r = 0
    · subst r
      simp [Set.zero_smul_set ⟨0, mem_of_mem_nhds hs₀'⟩,
        Set.zero_smul_set ⟨0, mem_of_mem_nhds hs₀⟩]
    · simp only [NNReal.smul_def, Set.mem_smul_set_iff_inv_smul_mem₀
        (NNReal.coe_ne_zero.mpr hr), Set.mem_preimage, s', Submodule.coe_smul_of_tower]
  -- The threshold ranks are unchanged by the inclusion of the real span into E.
  have himage (r : ℝ≥0) : W.subtype '' (r • s' ∩ (L' : Set W)) = r • s ∩ L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hdilate r y).1 hy.1, hy.2⟩
    · rintro ⟨hxs, hxL⟩
      exact ⟨⟨x, subset_span hxL⟩, ⟨(hdilate r _).2 hxs, hxL⟩, rfl⟩
  have hmin (i : ℕ) : successiveMin L' s' i = successiveMin L s i := by
    simp only [successiveMin_def]
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq]
    rw [← himage r, Set.finrank, Set.finrank, ← map_span, finrank_map_subtype_eq]
  have hn : finrank ℤ L = finrank ℝ W := e.finrank_eq.symm.trans (ZLattice.rank ℝ L')
  obtain ⟨b, hb⟩ := exists_directional_basis L' hsc' hs' hs₀'
  let v : Fin (finrank ℤ L) → E := fun j ↦ b (Fin.cast hn j)
  refine ⟨v, fun j ↦ ?_, ?_⟩
  · obtain ⟨hbs, hbL⟩ := hb (Fin.cast hn j)
    rw [hmin] at hbs
    exact ⟨(hdilate _ _).1 hbs, hbL⟩
  · exact (b.linearIndependent.comp _ (Fin.cast_injective _)).map'
      W.subtype (Submodule.ker_subtype W)

/-- A compact convex neighbourhood of zero admits an integrally independent family in the
lattice, with each vector in the dilate by its corresponding successive minimum. The family
need not be an integral basis. -/
theorem exists_directional_set (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → L,
      (∀ j, (v j : E) ∈ successiveMin L s j.val • s) ∧ LinearIndependent ℤ v := by
  obtain ⟨v, hv, hli⟩ := exists_directional_set' L hsc hs hs₀
  refine ⟨fun j ↦ ⟨v j, (hv j).2⟩, fun j ↦ (hv j).1, ?_⟩
  exact (hli.restrict_scalars' ℤ).of_comp L.subtype

end MeasureTheory
