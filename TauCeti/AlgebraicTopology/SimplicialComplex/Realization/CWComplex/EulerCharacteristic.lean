/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic

/-!
# The Euler characteristic of a finite simplicial realization

The realization of a simplicial complex on a finite vertex type is a finite CW complex, with one
`n`-cell for each face with `n + 1` vertices (`AbstractSimplicialComplex.realizationCWComplex`).
Hence it has finite CW type, and so does every space homeomorphic to it, that is, every space
triangulated by a finite simplicial complex. Its Euler characteristic is the alternating count of
the faces,

```text
χ(|K|) = ∑_{σ ∈ K} (-1) ^ (#σ + 1) = #(vertices) - #(edges) + #(triangles) - ⋯ .
```

The count does not depend on the triangulation: by `TauCeti.eulerChar_eq_cwEulerChar`, the
Euler characteristic of a space of finite CW type is determined by its homotopy type. This is how
a triangulation of a compact manifold computes its Euler characteristic.

## Main results

* `AbstractSimplicialComplex.finite_realizationCWComplex`: the CW structure on the realization of
  a complex on a finite vertex type has finitely many cells.
* `AbstractSimplicialComplex.cwEulerChar_realizationCWComplex`: its alternating cell count is the
  alternating count of the faces.
* `AbstractSimplicialComplex.instFiniteCWTypeRealization`: the realization of a complex on a finite
  vertex type has finite CW type. A space `M` with a homeomorphism `f : Realization K ≃ₜ M` then
  has finite CW type by `f.symm.finiteCWType`.
* `AbstractSimplicialComplex.eulerChar_realization`: the Euler characteristic of the realization
  is the alternating count of the faces.
* `AbstractSimplicialComplex.eulerChar_eq_finsum_of_homeomorph`: the same for every space
  triangulated by `K`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (simplicial complexes as CW complexes) and Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open Finset Topology TauCeti TauCeti.SetLike

universe u

namespace AbstractSimplicialComplex

variable {ι : Type u} (K : AbstractSimplicialComplex ι)

/-- A simplicial cell is determined by its face: the dimension is one less than the number of
vertices. -/
private theorem injective_sigma_realizationCell_val :
    Function.Injective fun c : Σ n, RealizationCell K n => c.2.1 := by
  rintro ⟨n, c⟩ ⟨m, d⟩ h
  have hnm : n = m := by
    have hc := c.2
    have hd := d.2
    simp only at h
    rw [h] at hc
    omega
  subst hnm
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  exact Subtype.ext h

section LinearOrder

variable [LinearOrder ι]

/-- The CW structure on the realization of a complex on a finite vertex type is finite. -/
theorem finite_realizationCWComplex [Finite ι] :
    letI := realizationCWComplex K
    Topology.RelCWComplex.Finite (Set.univ : Set (Realization K)) := by
  let := realizationCWComplex K
  exact Topology.RelCWComplex.finite_of_finite_cells (Finite.of_injective _
    ((injective_sigma_realizationCell_val K).comp
      (Function.injective_id.sigma_map fun n => (realizationCellEquiv K n).injective)))

/-- The alternating cell count of the CW structure on the realization of a complex on a finite
vertex type is the alternating count of the faces: a face with `n + 1` vertices is an `n`-cell. -/
theorem cwEulerChar_realizationCWComplex [Finite ι] :
    letI := realizationCWComplex K
    cwEulerChar (Set.univ : Set (Realization K)) = ∑ᶠ σ : Face K, (-1 : ℤ) ^ (σ.1.card + 1) := by
  let := realizationCWComplex K
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite (Face K)
  -- Faces have at most `card ι` vertices, so there are no cells in dimensions `n ≥ card ι`.
  have hempty (n : ℕ) (hn : Fintype.card ι ≤ n) :
      IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set (Realization K)) n) := by
    refine ⟨fun c => ?_⟩
    have hc := (realizationCellEquiv K n c).2
    have hle := card_le_univ (realizationCellEquiv K n c).1.1
    omega
  -- Group the faces by their number of vertices; no face is empty.
  rw [cwEulerChar_eq_sum_range _ hempty, finsum_eq_sum_of_fintype,
    ← sum_fiberwise_of_maps_to (t := range (Fintype.card ι + 1)) (g := fun σ : Face K => σ.1.card)
      fun σ _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ σ.1)),
    sum_range_succ', sum_eq_zero (s := {σ : Face K | σ.1.card = 0}) fun σ hσ => ?_, add_zero]
  · refine sum_congr rfl fun n _ => ?_
    rw [sum_congr rfl fun σ hσ => by rw [(mem_filter.mp hσ).2], sum_const, nsmul_eq_mul,
      Nat.card_congr (realizationCellEquiv K n), Nat.card_eq_fintype_card, Fintype.card_subtype]
    ring
  · exact absurd (mem_filter.mp hσ).2
      (card_ne_zero.mpr (K.isRelLowerSet_faces.prop_of_mem σ.2))

end LinearOrder

/-- The realization of a simplicial complex on a finite vertex type has finite CW type: it is a
finite CW complex. -/
instance instFiniteCWTypeRealization [Finite ι] : FiniteCWType (Realization K) := by
  let : LinearOrder ι := LinearOrder.lift' _ (Finite.equivFin ι).injective
  let := realizationCWComplex K
  have := finite_realizationCWComplex K
  exact (Homeomorph.Set.univ (Realization K)).symm.finiteCWType

/-- The Euler characteristic of the realization of a simplicial complex on a finite vertex type
is the alternating count of its faces: `#(vertices) - #(edges) + #(triangles) - ⋯`. -/
theorem eulerChar_realization [Finite ι] :
    eulerChar (Realization K) = ∑ᶠ σ : Face K, (-1 : ℤ) ^ (σ.1.card + 1) := by
  let : LinearOrder ι := LinearOrder.lift' _ (Finite.equivFin ι).injective
  let := realizationCWComplex K
  have := finite_realizationCWComplex K
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ (Realization K)).symm.toHomotopyEquiv,
    cwEulerChar_realizationCWComplex]

/-- The Euler characteristic of a space triangulated by a simplicial complex on a finite vertex
type is the alternating count of the faces of the complex. The space has finite CW type by
`f.symm.finiteCWType`. -/
theorem eulerChar_eq_finsum_of_homeomorph [Finite ι] {M : Type u} [TopologicalSpace M]
    [FiniteCWType M] (f : Realization K ≃ₜ M) :
    eulerChar M = ∑ᶠ σ : Face K, (-1 : ℤ) ^ (σ.1.card + 1) := by
  rw [f.symm.eulerChar_eq, eulerChar_realization]

end AbstractSimplicialComplex
