/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.BrauerProjection
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup

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

/-- An element `q` of a `2`-subgroup with `q³ = 1` is `1`. -/
private theorem eq_one_of_isPGroup_of_pow_three_eq_one {G : Type*} [Group G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {q : G} (hq : q ∈ Q) (h3 : q ^ 3 = 1) : q = 1 := by
  have h3' : (⟨q, hq⟩ : Q) ^ 3 = 1 := Subtype.ext h3
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 ((hQ.orderOf_coprime (n := 3) (by norm_num)
    _).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h3')))

/-- A nonzero coefficient makes an element of a monoid algebra nonzero. -/
private theorem ne_zero_of_coeff_ne_zero {k G : Type*} [Semiring k] {x : MonoidAlgebra k G} (g : G)
    (h : x.coeff g ≠ 0) : x ≠ 0 :=
  ne_of_apply_ne (·.coeff g) (by simpa using h)

/-- An element of `S₃` commuting with some `q` with `q³ ≠ 1` is not a `3`-cycle. -/
private theorem not_ne_one_and_cube_eq_one_of_commute :
    ∀ c q : S₃, q * q * q ≠ 1 → c * q = q * c → ¬(c ≠ 1 ∧ c * c * c = 1) := by
  decide +kernel

/-- A `2`-subgroup of `S₃` has order `1` or `2`: its order is a power of `2` dividing `6`. -/
private theorem card_eq_one_or_two_of_isPGroup {Q : Subgroup S₃} (hQ : IsPGroup 2 Q) :
    Nat.card Q = 1 ∨ Nat.card Q = 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : 2 ^ n ∣ 6 := hn ▸ (Subgroup.card_subgroup_dvd_card Q).trans
    (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide)
  have hn1 : n ≤ 1 := (Nat.pow_dvd_pow_iff_le_right one_lt_two).1
    ((Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right hdvd)
  interval_cases n <;> simp [hn]

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
    have h3 : (q : S₃) * q * q ≠ 1 := fun h3 => hq1 (Subtype.ext
      (eq_one_of_isPGroup_of_pow_three_eq_one hQ q.property
        (by simpa [pow_succ, mul_assoc] using h3)))
    refine hQe (brauerProjection_eq_zero_iff.2 fun c hc => ?_)
    have hcq : c * q = q * c :=
      (Subgroup.mem_centralizer_iff.1 hc q (SetLike.mem_coe.2 q.property)).symm
    rw [coeff_blockTwoS₃]
    exact ite_eq_right (not_ne_one_and_cube_eq_one_of_commute c q h3 hcq)

/-- `⟨(0 1)⟩` has order `2`. -/
private theorem card_P : Nat.card BrauerProjectionS3.P = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by decide) (by decide)

/-- **Check.** `Br_Q(1 + ρ + ρ²) ≠ 0` for every subgroup `Q` of `S₃`: its coefficient at
`1 ∈ C_{S₃}(Q)` is `1`. -/
theorem brauerProjection_blockOneS₃_ne_zero (Q : Subgroup S₃) :
    brauerProjection Q (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) ≠ 0 :=
  ne_zero_of_coeff_ne_zero 1 (by
    rw [coeff_brauerProjection, OneMemClass.coe_one, coeff_blockOneS₃]
    decide)

/-- **Check.** The defect groups of the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]` are exactly the
three subgroups of order `2`: every subgroup has nonzero Brauer projection, and a `2`-subgroup of
`S₃` has order `1` or `2`. -/
theorem isDefectGroup_blockOneS₃_iff {D : Subgroup S₃} :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) D ↔ Nat.card D = 2 := by
  refine ⟨fun hD => (card_eq_one_or_two_of_isPGroup hD.isPGroup).resolve_left fun h1 => ?_,
    fun hD => isDefectGroup_iff.2 ⟨IsPGroup.of_card (n := 1) (by rw [hD, pow_one]),
      brauerProjection_blockOneS₃_ne_zero D, fun Q hQ _ hDQ =>
        (Subgroup.eq_of_le_of_card_ge hDQ ?_).symm⟩⟩
  · have hPD := (isDefectGroup_iff.1 hD).2.2 _ (IsPGroup.of_card (n := 1)
      (by rw [card_P, pow_one])) (brauerProjection_blockOneS₃_ne_zero _)
      (Subgroup.eq_bot_of_card_eq D h1 ▸ bot_le)
    rw [← hPD, card_P] at h1
    exact absurd h1 (by decide)
  · rw [hD]
    exact (card_eq_one_or_two_of_isPGroup hQ).elim (fun h => h.trans_le (by decide)) le_of_eq

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
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q hQ _ _ => ?_⟩
  · rw [Ne, brauerProjection_bot_eq_zero_iff]
    exact ne_zero_of_coeff_ne_zero 1 (by rw [coeff_one_add_r_add_r_sq]; exact one_ne_zero)
  · exact (Subgroup.eq_bot_iff_forall Q).2 fun q hq =>
      eq_one_of_isPGroup_of_pow_three_eq_one hQ hq (by simpa using pow_card_eq_one (x := q))

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
