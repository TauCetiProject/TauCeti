/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Centralizer
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup

/-!
# Defect groups of small blocks

Checks for `TauCeti.IsDefectGroup` on the blocks of `𝔽₂[S₃]`, `𝔽₂[C₃]` and `k[1]` computed in
`TauCeti/Examples/RepresentationTheory/GroupAlgebra/Block.lean`.

* **`𝔽₂[S₃]`, `t = (0 1)`.** `Br_{⟨t⟩}(1 + ρ + ρ²) = 1 ≠ 0`, and `⟨t⟩`, a Sylow `2`-subgroup,
  is a defect group of the principal block `1 + ρ + ρ²`. For the block `ρ + ρ²`,
  `Br_{⟨t⟩}(ρ + ρ²) = 0`, and the defect group is `1`: every nontrivial `2`-subgroup contains an
  element of order `2`, a transposition, which commutes with neither `ρ` nor `ρ²`.
* **`𝔽₂[C₃]`.** The block `1 + r + r²` has nonzero Brauer projection at the whole group `C₃`, so
  without the `p`-group condition `C₃` would be the maximal subgroup with nonzero projection; the
  only `2`-subgroup of `C₃` is `1`, which is the defect group.
* **`G = 1`.** The unique defect group of the block `1` of `k[1]` is `1`, the unique Sylow
  subgroup.
-/

public section

namespace TauCeti.Examples.DefectGroupS3

open _root_.MonoidAlgebra GroupAlgebraBlockExamples

/-! ### `𝔽₂[S₃]` -/

/-- The transposition `t = (0 1)` of `S₃`. -/
abbrev t : S₃ := Equiv.swap 0 1

/-- The subgroup `⟨t⟩` of order `2`. -/
abbrev T : Subgroup S₃ := Subgroup.zpowers t

/-- An element of a `2`-subgroup of `S₃` other than `1` is not of order dividing `3`. -/
private theorem pow_three_ne_one_of_isPGroup {Q : Subgroup S₃} (hQ : IsPGroup 2 Q) {q : Q}
    (hq : q ≠ 1) : (q : S₃) * q * q ≠ 1 := by
  intro h3
  obtain ⟨n, hn⟩ := hQ q
  have h3' : q ^ 3 = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using h3)
  have hcop : Nat.Coprime (orderOf q) (2 ^ n) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3')
      (Nat.Coprime.pow_right n (by norm_num))
  exact hq (orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hn)))

/-- An element of `S₃` commuting with some `q` with `q³ ≠ 1` is not a `3`-cycle. -/
private theorem coeff_blockTwoS₃_eq_zero_of_commute :
    ∀ c q : S₃, q * q * q ≠ 1 → c * q = q * c →
      (if c ≠ 1 ∧ c * c * c = 1 then (1 : ZMod 2) else 0) = 0 := by
  decide +kernel

/-- **Check.** `Br_{⟨t⟩}(ρ + ρ²) = 0`: neither `ρ` nor `ρ²` commutes with `t`. -/
theorem brauerProjection_blockTwoS₃ :
    brauerProjection T (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 := by
  rw [brauerProjection_eq_zero_iff, coeff_blockTwoS₃]
  exact fun c hc => coeff_blockTwoS₃_eq_zero_of_commute c t (by decide)
    (Subgroup.mem_centralizer_zpowers_iff.1 hc)

/-- **Check.** The defect group of the block `ρ + ρ²` of `𝔽₂[S₃]` is `1`: a nontrivial
`2`-subgroup `Q` contains an element `q ≠ 1` with `q³ ≠ 1`, a transposition, and no element of
`C_{S₃}(Q)` is a `3`-cycle, so `Br_Q(ρ + ρ²) = 0`. -/
theorem isDefectGroup_blockTwoS₃_bot :
    IsDefectGroup (ZMod 2) 2 (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) ⊥ := by
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q hQ hQe _ => ?_⟩
  · rw [Ne, brauerProjection_bot_eq_zero_iff]
    intro h
    have := congrArg (fun x : MonoidAlgebra (ZMod 2) S₃ => x.coeff ρ) h
    simp only [coeff_blockTwoS₃, coeff_zero, Finsupp.zero_apply] at this
    revert this
    decide +kernel
  · by_contra hne
    obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have h3 := pow_three_ne_one_of_isPGroup hQ hq1
    refine hQe (brauerProjection_eq_zero_iff.2 fun c hc => ?_)
    have hcq : c * q = q * c :=
      (Subgroup.mem_centralizer_iff.1 hc q (SetLike.mem_coe.2 q.property)).symm
    rw [coeff_blockTwoS₃]
    exact coeff_blockTwoS₃_eq_zero_of_commute c q h3 hcq

/-- `t` has order `2`. -/
theorem orderOf_t : orderOf t = 2 :=
  orderOf_eq_prime (by decide) (by decide)

/-- `⟨t⟩` is a `2`-group: it has order `2`. -/
theorem isPGroup_T : IsPGroup 2 T :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one, orderOf_t])

/-- **Check.** `Br_{⟨t⟩}(1 + ρ + ρ²) ≠ 0`: its coefficient at `1 ∈ C_{S₃}(⟨t⟩)` is `1`. -/
theorem brauerProjection_blockOneS₃_ne_zero :
    brauerProjection T (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) ≠ 0 := by
  intro h
  have := congrArg (fun x => x.coeff 1) h
  simp only [coeff_brauerProjection, OneMemClass.coe_one, coeff_blockOneS₃, coeff_zero,
    Finsupp.zero_apply] at this
  revert this
  decide

/-- **Check.** `⟨t⟩` is a defect group of the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]`: it is a
`2`-group with nonzero Brauer projection, and a `2`-subgroup of `S₃` has order dividing `6`, so
at most `2`. -/
theorem isDefectGroup_blockOneS₃_T :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) T := by
  refine isDefectGroup_iff.2 ⟨isPGroup_T, brauerProjection_blockOneS₃_ne_zero,
    fun Q hQ _ hTQ => (Subgroup.eq_of_le_of_card_ge hTQ ?_).symm⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : 2 ^ n ∣ 6 := hn ▸ (Subgroup.card_subgroup_dvd_card Q).trans
    (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide)
  have hn1 : n ≤ 1 := by
    by_contra h
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)).trans hdvd) (by decide)
  rw [hn, Nat.card_zpowers, orderOf_t]
  exact (Nat.pow_le_pow_right (by norm_num) hn1).trans_eq (pow_one 2)

/-! ### `𝔽₂[C₃]` -/

/-- **Check.** `Br_{C₃}(1 + r + r²) ≠ 0`: without the `p`-group condition, the whole group `C₃`
would be the maximal subgroup with nonzero Brauer projection. -/
theorem brauerProjection_top_one_add_r_add_r_sq_ne_zero :
    brauerProjection (⊤ : Subgroup C₃)
      (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) ≠ 0 := by
  intro h
  have := congrArg (fun x => x.coeff 1) h
  simp only [coeff_brauerProjection, OneMemClass.coe_one, coeff_add, Finsupp.add_apply,
    of_apply, one_def, coeff_single, Finsupp.single_apply, coeff_zero, Finsupp.zero_apply] at this
  revert this
  decide

/-- **Check.** The defect group of the block `1 + r + r²` of `𝔽₂[C₃]` is `1`, the only
`2`-subgroup of `C₃`. -/
theorem isDefectGroup_one_add_r_add_r_sq_bot :
    IsDefectGroup (ZMod 2) 2 (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) ⊥ := by
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q hQ _ _ => ?_⟩
  · rw [Ne, brauerProjection_bot_eq_zero_iff]
    intro h
    have := congrArg (fun x => x.coeff 1) h
    simp only [coeff_add, Finsupp.add_apply, of_apply, one_def, coeff_single,
      Finsupp.single_apply, coeff_zero, Finsupp.zero_apply] at this
    revert this
    decide
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hdvd : 2 ^ n ∣ 3 := hn ▸ (Subgroup.card_subgroup_dvd_card Q).trans
      (by rw [Nat.card_eq_fintype_card]; decide)
    have hn0 : n = 0 := by
      by_contra h
      exact absurd ((pow_dvd_pow 2 (Nat.one_le_iff_ne_zero.2 h)).trans hdvd) (by decide)
    exact Subgroup.eq_bot_of_card_eq Q (by rw [hn, hn0, pow_zero])

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

end TauCeti.Examples.DefectGroupS3
