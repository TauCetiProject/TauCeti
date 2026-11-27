/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Induction
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.PGroup
import TauCeti.Algebra.Group.Subgroup.Centralizer
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Block induction and the Brauer correspondent on `𝔽₂[S₃]`

Let `τ = (0 1)` and `D = ⟨τ⟩ ≤ S₃`, of order `2`. Then `N_{S₃}(D) = C_{S₃}(D) = D`, and `𝔽₂[D]`
has the single block `1` (`TauCeti.isBlockIdempotent_iff_eq_one_of_isPGroup`), of defect group
`D`. With `ρ` the `3`-cycle `finRotate 3`:

* the Brauer correspondent `Br_D(1 + ρ + ρ²)` of the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]`
  is `1`, and the block `1` of `𝔽₂[D]` induces `1 + ρ + ρ²`, so `1` is the Brauer correspondent
  of the principal block;
* the block `ρ + ρ²` of defect zero has `Br_D(ρ + ρ²) = 0`: its defect group `1` is not `D`.
-/

public section

namespace TauCeti.BlockInductionExamples

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockDefectExamples

/-- The subgroup `D = ⟨τ⟩` of order `2`. -/
abbrev D : Subgroup S₃ := Subgroup.zpowers τ

/-- The elements of `D = ⟨τ⟩` are `1` and `τ`. -/
theorem mem_D_iff {g : S₃} : g ∈ D ↔ g = 1 ∨ g = τ :=
  Subgroup.mem_zpowers_iff_of_sq_eq_one (by decide)

/-- `D = ⟨τ⟩` is a `2`-group. -/
theorem isPGroup_D : IsPGroup 2 D :=
  IsPGroup.of_card card_zpowers_τ

/-- `C_{S₃}(D) = D`. -/
theorem centralizer_D : Subgroup.centralizer (D : Set S₃) = D := by
  ext g
  rw [Subgroup.mem_centralizer_zpowers_iff, mem_D_iff]
  revert g
  decide

/-- `N_{S₃}(D) = D`: `D` is self-normalizing. -/
theorem normalizer_D : Subgroup.normalizer (D : Set S₃) = D := by
  refine le_antisymm (fun g hg ↦ ?_) Subgroup.le_normalizer
  have h := (Subgroup.mem_normalizer_iff.1 hg τ).1 (Subgroup.mem_zpowers τ)
  rw [mem_D_iff] at h ⊢
  clear hg
  revert g
  decide

/-- `ρ` does not centralize `D`. -/
private theorem ρ_notMem : ρ ∉ Subgroup.centralizer (D : Set S₃) :=
  mt Subgroup.mem_centralizer_zpowers_iff.1 (by decide)

/-- `ρ²` does not centralize `D`. -/
private theorem ρ_sq_notMem : ρ ^ 2 ∉ Subgroup.centralizer (D : Set S₃) :=
  mt Subgroup.mem_centralizer_zpowers_iff.1 (by decide)

/-- **The Brauer correspondent of the principal block**: `Br_D(1 + ρ + ρ²) = 1` in `𝔽₂[D]`. -/
theorem brauerCorrespondent_blockOneS₃ :
    brauerCorrespondent centralizer_D.le (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) = 1 := by
  simp [coe_blockOneS₃, of_apply, brauerCorrespondent_single_of_notMem _ ρ_notMem,
    brauerCorrespondent_single_of_notMem _ ρ_sq_notMem]

/-- `Br_D(1 + ρ + ρ²) = 1` in the centre of `𝔽₂[D]`. -/
theorem centerBrauerCorrespondent_blockOneS₃ :
    centerBrauerCorrespondent centralizer_D.le Subgroup.le_normalizer blockOneS₃ = 1 :=
  Subtype.ext (by simpa using brauerCorrespondent_blockOneS₃)

/-- **The block of defect zero vanishes under `Br_D`**: `Br_D(ρ + ρ²) = 0`. -/
theorem brauerCorrespondent_blockTwoS₃ :
    brauerCorrespondent centralizer_D.le (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 := by
  simp [coe_blockTwoS₃, of_apply, brauerCorrespondent_single_of_notMem _ ρ_notMem,
    brauerCorrespondent_single_of_notMem _ ρ_sq_notMem]

/-- `2` is not a unit of `𝔽₂`. -/
private theorem not_isUnit_two : ¬IsUnit ((2 : ℕ) : ZMod 2) := by
  rw [ZMod.natCast_self]
  exact not_isUnit_zero

/-- `𝔽₂[D]` has the single block `1`. -/
theorem isBlockIdempotent_iff_eq_one_D {b : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) D)} :
    IsBlockIdempotent b ↔ b = 1 :=
  isBlockIdempotent_iff_eq_one_of_isPGroup not_isUnit_two isPGroup_D

/-- **`1` is the Brauer correspondent of the principal block of `𝔽₂[S₃]` at `D`**: the block `1` of
`𝔽₂[D] = 𝔽₂[N_{S₃}(D)]` induces the block `1 + ρ + ρ²` of `𝔽₂[S₃]`. -/
theorem isInducedBlock_one_blockOneS₃ :
    IsInducedBlock (ZMod 2) D.subtype D.subtype_injective 1 blockOneS₃ := by
  obtain ⟨B, hB, hchar⟩ :=
    (isBlockIdempotent_iff_eq_one_D.2 rfl).exists_isInducedBlock_apply_centerBrauerCorrespondent
      isPGroup_D le_rfl centralizer_D.le Subgroup.le_normalizer
      (φ := centerAugmentation (ZMod 2) D) (map_one _)
  obtain ⟨-, ψ, -, hψ, -⟩ := hB.exists_algHom
  have h1 : ψ blockOneS₃ = 1 := by
    rw [← hchar ψ hψ, centerBrauerCorrespondent_blockOneS₃, map_one]
  rwa [hB.isBlockIdempotent_right.eq_of_apply_eq_one ψ isBlockIdempotent_blockOneS₃ hψ h1] at hB

end TauCeti.BlockInductionExamples
