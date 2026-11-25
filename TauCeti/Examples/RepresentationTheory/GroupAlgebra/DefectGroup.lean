/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.BrauerProjection
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
import TauCeti.GroupTheory.PGroup
import TauCeti.GroupTheory.Sylow.Basic

/-!
# Defect groups of small blocks

Checks for `TauCeti.IsDefectGroup` on the blocks of `𝔽₂[S₃]`, `𝔽₂[C₃]` and `k[1]` computed in
`TauCeti/Examples/RepresentationTheory/GroupAlgebra/Block.lean`.

* **`𝔽₂[S₃]`.** `Br_Q(1 + ρ + ρ²) ≠ 0` for every subgroup `Q`, and the defect groups of the
  principal block `1 + ρ + ρ²` are exactly the three subgroups of order `2`, the Sylow
  `2`-subgroups. For the block `ρ + ρ²` and `P = ⟨(0 1)⟩`, `Br_P(ρ + ρ²) = 0`, and the defect
  group is `1`: every nontrivial `2`-subgroup contains an element of order `2`, a transposition,
  which commutes with neither `ρ` nor `ρ²`.
* **`𝔽₂[C₃]`.** The block `1 + r + r²` has nonzero Brauer projection at the whole group `C₃`, so
  without the `p`-group condition `C₃` would be the maximal subgroup with nonzero projection; the
  only `2`-subgroup of `C₃` is `1`, which is the defect group.
* **`G = 1`.** The unique defect group of the block `1` of `k[1]` is `1`, the unique Sylow
  subgroup.
-/

public section

namespace TauCeti.GroupAlgebraDefectGroupExamples

open _root_.MonoidAlgebra GroupAlgebraBlockExamples Examples

/-! ### `𝔽₂[S₃]` -/

/-- An element of `S₃` commuting with some `q` with `q³ ≠ 1` is not a `3`-cycle. -/
private theorem not_ne_one_and_cube_eq_one_of_commute :
    ∀ c q : S₃, q * q * q ≠ 1 → c * q = q * c → ¬(c ≠ 1 ∧ c * c * c = 1) := by
  decide +kernel

/-- **Check.** `Br_{⟨(0 1)⟩}(ρ + ρ²) = 0`: neither `ρ` nor `ρ²` commutes with `(0 1)`. -/
theorem brauerProjection_blockTwoS₃_eq_zero :
    brauerProjection BrauerProjectionS3.P (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 := by
  rw [coe_blockTwoS₃, of_apply, of_apply, pow_two]
  exact BrauerProjectionS3.brauerProjection_x (ZMod 2)

/-- **Check.** The defect group of the block `ρ + ρ²` of `𝔽₂[S₃]` is `1`: a nontrivial
`2`-subgroup `Q` contains an element `q ≠ 1` with `q³ ≠ 1`, a transposition, and no element of
`C_{S₃}(Q)` is a `3`-cycle, so `Br_Q(ρ + ρ²) = 0`. -/
theorem isDefectGroup_blockTwoS₃_bot :
    IsDefectGroup (ZMod 2) 2 (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) ⊥ := by
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q hQ hQe _ => ?_⟩
  · rw [Ne, brauerProjection_bot_eq_zero_iff]
    exact ne_zero_of_coeff_ne_zero ρ (by rw [coeff_blockTwoS₃]; decide +kernel)
  · by_contra hne
    obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have h3 : (q : S₃) * q * q ≠ 1 := fun h3 => hq1 (IsPGroup.eq_one_of_pow_eq_one_of_coprime hQ
      (n := 3) (by norm_num) (Subtype.ext (by simpa [pow_succ, mul_assoc] using h3)))
    refine hQe (brauerProjection_eq_zero_iff.2 fun c hc => ?_)
    have hcq : c * q = q * c :=
      (Subgroup.mem_centralizer_iff.1 hc q (SetLike.mem_coe.2 q.property)).symm
    rw [coeff_blockTwoS₃]
    exact ite_eq_right (not_ne_one_and_cube_eq_one_of_commute c q h3 hcq)

/-- **Check.** `Br_Q(1 + ρ + ρ²) ≠ 0` for every subgroup `Q` of `S₃`: its coefficient at
`1 ∈ C_{S₃}(Q)` is `1`. -/
theorem brauerProjection_blockOneS₃_ne_zero (Q : Subgroup S₃) :
    brauerProjection Q (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) ≠ 0 :=
  ne_zero_of_coeff_ne_zero 1 (by
    rw [coeff_brauerProjection, OneMemClass.coe_one, coeff_blockOneS₃]
    decide)

/-- **Check.** The defect groups of the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]` are exactly the
three subgroups of order `2`: `1 + ρ + ρ²` is central of augmentation `1`, so its defect groups are
the Sylow `2`-subgroups, which have order `2` since `|S₃| = 2 · 3`. -/
theorem isDefectGroup_blockOneS₃_iff {D : Subgroup S₃} :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) D ↔ Nat.card D = 2 := by
  have h6 : Nat.card S₃ = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have hcard (S : Sylow 2 S₃) : Nat.card S = 2 :=
    S.card_eq_of_dvd_of_not_sq_dvd (by rw [h6]; decide) (by rw [h6]; decide)
  rw [isDefectGroup_iff_sylow_of_augmentation_ne_zero blockOneS₃.property (by
    rw [coe_blockOneS₃, map_add, map_add, map_one, of_apply, of_apply, augmentation_single,
      augmentation_single]
    decide)]
  refine ⟨fun ⟨S, hS⟩ => hS ▸ hcard S, fun hD => ⟨Sylow.ofCard D (hD.trans
    ((hcard default).symm.trans (default : Sylow 2 S₃).card_eq_multiplicity)), rfl⟩⟩

/-! ### `𝔽₂[C₃]` -/

/-- The coefficient function of `1 + r + r²` in `𝔽₂[C₃]` is constantly `1`. -/
theorem coeff_one_add_r_add_r_sq :
    ⇑(1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)).coeff = fun _ ↦ 1 := by
  funext g
  revert g
  simp only [coeff_add, Finsupp.add_apply, of_apply, one_def, coeff_single, Finsupp.single_apply]
  decide

/-- **Check.** `Br_{C₃}(1 + r + r²) ≠ 0`: without the `p`-group condition, the whole group `C₃`
would be the maximal subgroup with nonzero Brauer projection. -/
theorem brauerProjection_top_one_add_r_add_r_sq_ne_zero :
    brauerProjection (⊤ : Subgroup C₃)
      (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) ≠ 0 :=
  ne_zero_of_coeff_ne_zero 1 (by
    rw [coeff_brauerProjection, OneMemClass.coe_one, coeff_one_add_r_add_r_sq]
    exact one_ne_zero)

/-- **Check.** The defect group of the block `1 + r + r²` of `𝔽₂[C₃]` is `1`, the only
`2`-subgroup of `C₃`. -/
theorem isDefectGroup_one_add_r_add_r_sq_bot :
    IsDefectGroup (ZMod 2) 2 (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) ⊥ := by
  refine (isDefectGroup_iff_sylow_of_augmentation_ne_zero
    (by rw [Subalgebra.center_eq_top]; exact Algebra.mem_top) ?_).2
    ⟨Sylow.ofCard ⊥ ?_, rfl⟩
  · rw [map_add, map_add, map_one, of_apply, of_apply, augmentation_single, augmentation_single]
    decide
  · rw [Subgroup.card_bot, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
      Nat.factorization_eq_zero_of_not_dvd (by decide), pow_zero]

/-! ### The trivial group -/

/-- **Check.** For `G = 1`, the unique defect group of the block `1` of `k[1]` is `1`, which is
also the unique Sylow `p`-subgroup. -/
theorem isDefectGroup_unit_iff (k : Type*) [Field k] (p : ℕ) (D : Subgroup Unit) :
    IsDefectGroup k p (1 : MonoidAlgebra k Unit) D ↔ D = ⊥ := by
  refine ⟨fun _ => Subsingleton.elim _ _, ?_⟩
  rintro rfl
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q _ _ _ => Subsingleton.elim _ _⟩
  rw [Ne, brauerProjection_bot_eq_zero_iff]
  exact one_ne_zero

end TauCeti.GroupAlgebraDefectGroupExamples
