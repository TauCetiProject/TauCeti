/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Partition
public import TauCeti.Geometry.RealAlgebraic.Stack.Map

/-!
# Restricting a cylindrical algebraic decomposition over a finer base

Let `𝒞` be a cylindrical algebraic decomposition of `ℝ ^ (n + 1)`, whose cells project, forgetting
the distinguished coordinate `0`, onto the cells of a CAD of `ℝ ^ n`. If `𝒟` is a CAD of `ℝ ^ n`
refining that projection, so that each cell of `𝒟` lies under some cell of `𝒞`, then cutting
every cell `E ∈ 𝒞` down to the cylinder over each cell `D ∈ 𝒟` lying under it gives a CAD of
`ℝ ^ (n + 1)` refining `𝒞` and projecting onto `𝒟`. Over each `D ∈ 𝒟` it is the stack of `𝒞` over
the base cell containing `D`, restricted to `D` (`TauCeti.IsSemialgebraicStack.restrict`).
Restricting a CAD over its own projection gives it back.

This lets the base of a CAD be refined, for instance to make further polynomials sign-invariant
on the base cells, without recomputing the stacks above it.

## Main definitions

* `TauCeti.restrictCells`: the parts `E ∩ Fin.tail ⁻¹' D` of the cells `E ∈ 𝒞` over the sets
  `D ∈ 𝒟` lying under them.

## Main results

* `TauCeti.isCAD_restrictCells`: restricting a CAD of `ℝ ^ (n + 1)` over a CAD of `ℝ ^ n` refining
  its projection gives a CAD.
* `TauCeti.image_image_tail_restrictCells`: the restricted cells project onto the finer base.
* `TauCeti.IsCAD.restrictCells_image_tail`: restricting a CAD over its own projection gives it
  back.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (cylindrical algebraic decomposition).
-/

public section

open Function Set

namespace TauCeti

variable {α : Type*} {n : ℕ}

/-- The cells of `𝒞 ⊆ 𝒫(α ^ (n + 1))` restricted over `𝒟 ⊆ 𝒫(α ^ n)`: the sets
`E ∩ Fin.tail ⁻¹' D` with `E ∈ 𝒞` and `D ∈ 𝒟` lying under `E`, that is, `D ⊆ Fin.tail '' E`. -/
def restrictCells (𝒞 : Set (Set (Fin (n + 1) → α))) (𝒟 : Set (Set (Fin n → α))) :
    Set (Set (Fin (n + 1) → α)) :=
  {E' | ∃ E ∈ 𝒞, ∃ D ∈ 𝒟, D ⊆ Fin.tail '' E ∧ E ∩ Fin.tail ⁻¹' D = E'}

variable {𝒞 : Set (Set (Fin (n + 1) → α))} {𝒟 : Set (Set (Fin n → α))}

/-- Membership in `TauCeti.restrictCells`. -/
@[simp]
theorem mem_restrictCells {E' : Set (Fin (n + 1) → α)} :
    E' ∈ restrictCells 𝒞 𝒟 ↔ ∃ E ∈ 𝒞, ∃ D ∈ 𝒟, D ⊆ Fin.tail '' E ∧ E ∩ Fin.tail ⁻¹' D = E' :=
  Iff.rfl

/-- If every set of `𝒟` lies under some set of `𝒞`, the restricted cells project exactly onto
`𝒟`. -/
theorem image_image_tail_restrictCells (h : ∀ D ∈ 𝒟, ∃ E ∈ 𝒞, D ⊆ Fin.tail '' E) :
    image Fin.tail '' restrictCells 𝒞 𝒟 = 𝒟 := by
  ext D
  constructor
  · rintro ⟨_, ⟨E, -, D, hD, hDE, rfl⟩, rfl⟩
    rwa [image_inter_preimage, inter_eq_right.2 hDE]
  · intro hD
    obtain ⟨E, hE, hDE⟩ := h D hD
    exact ⟨_, ⟨E, hE, D, hD, hDE, rfl⟩, by rw [image_inter_preimage, inter_eq_right.2 hDE]⟩

/-- **Restriction of a CAD over a finer base.** If `𝒞` is a cylindrical algebraic decomposition of
`ℝ ^ (n + 1)` and `𝒟` is a cylindrical algebraic decomposition of `ℝ ^ n` each of whose cells lies
under some cell of `𝒞`, then the parts `E ∩ Fin.tail ⁻¹' D` of the cells `E ∈ 𝒞` over the cells
`D ∈ 𝒟` lying under them form a cylindrical algebraic decomposition of `ℝ ^ (n + 1)`. -/
theorem isCAD_restrictCells {𝒞 : Set (Set (Fin (n + 1) → ℝ))} {𝒟 : Set (Set (Fin n → ℝ))}
    (h𝒞 : IsCAD (n + 1) 𝒞) (h𝒟 : IsCAD n 𝒟) (h : ∀ D ∈ 𝒟, ∃ E ∈ 𝒞, D ⊆ Fin.tail '' E) :
    IsCAD (n + 1) (restrictCells 𝒞 𝒟) := by
  rw [isCAD_succ_iff_exists_isSemialgebraicStack, image_image_tail_restrictCells h]
  refine ⟨h𝒟, fun D hD ↦ ?_⟩
  -- Restrict the stack of `𝒞` over the base cell `C` containing `D`.
  obtain ⟨E₀, hE₀, hDC⟩ := h D hD
  obtain ⟨k, θ, hθ, hθ𝒞⟩ :=
    (isCAD_succ_iff_exists_isSemialgebraicStack.1 h𝒞).2 _ (mem_image_of_mem _ hE₀)
  refine ⟨k, fun i ↦ θ i ∘ inclusion hDC, hθ.restrict (h𝒟.isSemialgebraic hD) hDC, ?_⟩
  rw [stackCells_inclusion, ← hθ𝒞]
  -- The projected cells partition `ℝ ^ n`, so a cell of `𝒞` lying over `D` lies over `C`.
  obtain ⟨x, hx⟩ := (h𝒟.isConnected hD).nonempty
  have hbase {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ 𝒞) (hDE : D ⊆ Fin.tail '' E) :
      Fin.tail '' E = Fin.tail '' E₀ := by
    refine h𝒞.image_tail.isPartition.pairwiseDisjoint.elim (mem_image_of_mem _ hE)
      (mem_image_of_mem _ hE₀) (not_disjoint_iff.2 ⟨x, ?_, hDC hx⟩)
    exact hDE hx
  ext E'
  constructor
  · rintro ⟨⟨E, hE, D', -, hD'E, rfl⟩, hE'D⟩
    rw [image_inter_preimage, inter_eq_right.2 hD'E] at hE'D
    subst hE'D
    exact ⟨E, ⟨hE, hbase hE hD'E⟩, rfl⟩
  · rintro ⟨E, ⟨hE, hEC⟩, rfl⟩
    have hDE : D ⊆ Fin.tail '' E := hEC ▸ hDC
    exact ⟨⟨E, hE, D, hD, hDE, rfl⟩, by rw [image_inter_preimage, inter_eq_right.2 hDE]⟩

/-- Restricting a cylindrical algebraic decomposition over its own projection gives it back. -/
theorem IsCAD.restrictCells_image_tail {𝒞 : Set (Set (Fin (n + 1) → ℝ))}
    (h𝒞 : IsCAD (n + 1) 𝒞) : restrictCells 𝒞 (image Fin.tail '' 𝒞) = 𝒞 := by
  ext E'
  constructor
  · rintro ⟨E, hE, _, ⟨E'', hE'', rfl⟩, hsub, rfl⟩
    -- Projected cells are equal or disjoint, and the projection of `E''` meets that of `E`.
    obtain ⟨x, hx⟩ := ((h𝒞.isConnected hE'').nonempty).image Fin.tail
    rw [h𝒞.image_tail.isPartition.pairwiseDisjoint.elim (mem_image_of_mem _ hE'')
      (mem_image_of_mem _ hE) (not_disjoint_iff.2 ⟨x, hx, hsub hx⟩),
      inter_eq_left.2 (subset_preimage_image _ _)]
    exact hE
  · intro hE
    exact ⟨E', hE, _, mem_image_of_mem _ hE, subset_rfl,
      inter_eq_left.2 (subset_preimage_image _ _)⟩

end TauCeti
