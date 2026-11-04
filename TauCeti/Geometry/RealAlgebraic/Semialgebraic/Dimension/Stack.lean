/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Fiber

/-!
# Dimensions and fibers of cylindrical cells

A section of a continuous ordered stack has the dimension of its base, while a sector has
one additional dimension. The fibers of a section are finite; those of a sector are infinite
at exactly the points of its base. Thus the dimension contribution of a cylindrical cell is
detected by its actual fibers, including the unbounded sectors and stacks without sections.
These facts allow dimension formulas for coordinate projections to be read from an adapted
cylindrical algebraic decomposition.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Section 2.8.
-/

public section

open Function Set Topology

namespace TauCeti

variable {n k d : ℕ} {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

/-- A continuous section over a nonempty Euclidean cell has the dimension of its base. -/
theorem semialgebraicDim_image_cylinder_sectionSet (hC : C.Nonempty)
    {f : C → Fin d → ℝ} (hf : IsOpenEmbedding f) (i : Fin k) (hc : Continuous (θ i)) :
    semialgebraicDim (cylinder C '' sectionSet θ i) = d := by
  have := hC.to_subtype
  exact semialgebraicDim_eq_of_isOpenEmbedding ((sectionSet_nonempty θ i).image _)
    (hf.comp (isOpenEmbedding_tail_image_cylinder_sectionSet i hc))

/-- A sector over a nonempty Euclidean cell has one more dimension than its base. -/
theorem semialgebraicDim_image_cylinder_sectorSet (hC : C.Nonempty)
    {f : C → Fin d → ℝ} (hf : IsOpenEmbedding f) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) :
    semialgebraicDim (cylinder C '' sectorSet θ j) = (d + 1 : ℕ) := by
  have := hC.to_subtype
  exact semialgebraicDim_eq_of_isOpenEmbedding ((sectorSet_nonempty hθ j).image _)
    (isOpenEmbedding_cons_image_cylinder_sectorSet hf hc j)

namespace IsCAD

/-- Each cylindrical cell either has finite fibers and its base dimension, or has infinite
fibers over its entire base and dimension one larger than that base. -/
theorem semialgebraicDim_setOf_cons_mem_cases {𝒞 : Set (Set (Fin (n + 1) → ℝ))}
    (h : IsCAD (n + 1) 𝒞) {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ 𝒞) :
    (semialgebraicDim E = semialgebraicDim (Fin.tail '' E) ∧
      ∀ x, {t : ℝ | Fin.cons t x ∈ E}.Finite) ∨
    (semialgebraicDim E = semialgebraicDim (Fin.tail '' E) + 1 ∧
      ∀ x, {t : ℝ | Fin.cons t x ∈ E}.Infinite ↔ x ∈ Fin.tail '' E) := by
  cases h with
  | @succ n 𝒟 k θ h𝒟 hθ =>
    obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    obtain ⟨d, hdim, f, hf⟩ := h𝒟.exists_semialgebraicDim_eq hC
    have hne := (h𝒟.isConnected hC).nonempty
    have hbase := image_tail_of_mem_stackCells (hθ C hC).strictMono hE
    rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine Or.inl ⟨?_, finite_setOf_cons_mem_image_cylinder_sectionSet (θ C) i⟩
      rw [semialgebraicDim_image_cylinder_sectionSet hne hf i ((hθ C hC).continuous i),
        hbase, hdim]
    · refine Or.inr ⟨?_, fun x ↦ ?_⟩
      · rw [semialgebraicDim_image_cylinder_sectorSet hne hf (hθ C hC).continuous
          (hθ C hC).strictMono j, hbase, hdim, Nat.cast_add, Nat.cast_one]
      · rw [hbase]
        exact infinite_setOf_cons_mem_image_cylinder_sectorSet_iff (hθ C hC).strictMono j x

end IsCAD
end TauCeti
