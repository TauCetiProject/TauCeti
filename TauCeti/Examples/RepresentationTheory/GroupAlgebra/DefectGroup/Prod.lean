/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNormal
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Prod

/-!
# Defect groups of direct products: `S₃ × C₂` and `𝔽₂[C₃ × C₃]`

Checks of ModularCharactersAndBlocks §6.2 "Direct products", for the defect groups of `x ⊗ y`
(`TauCeti.isDefectGroup_tensorEquiv_tmul_iff`).

* **`S₃ × C₂` at `p = 3`.** `1` is the only block of `𝔽₃[S₃]`
  (`TauCeti.GroupAlgebraBlockExamples.isBlockIdempotent_iff_eq_one_zmod_three_s₃`), with defect
  group the Sylow `3`-subgroup `C₃ = ⟨ρ⟩`, and `e₊ = (1 + t)/2`, `e₋ = (1 - t)/2` are the blocks
  of `𝔽₃[C₂]`, with defect group `1`. The idempotents `1 ⊗ e₊`, `1 ⊗ e₋` of `𝔽₃[S₃ × C₂]` each
  have the single defect group `C₃ × 1`.
* **The splitting is needed.** Over `𝔽₂`, `e = r + r²` is a block of `𝔽₂[C₃]`, but `e ⊗ e` is
  not a block of `𝔽₂[C₃ × C₃]`: it is the sum of the two orthogonal nonzero idempotents
  `f₁ = ∑_{ab ≠ 1} (a, b)` and `f₂ = ∑_{a ≠ b} (a, b)`. (Over `𝔽₄`, writing `e = ε + ε'` for the
  two blocks of `𝔽₄[C₃]`, `f₁ = ε ⊗ ε + ε' ⊗ ε'` and `f₂ = ε ⊗ ε' + ε' ⊗ ε`.)
-/

public section

namespace TauCeti.DefectGroupProdExamples

open _root_.MonoidAlgebra TensorProduct GroupAlgebraBlockExamples

/-! ### `S₃ × C₂` at `p = 3` -/

/-- The subgroup `⟨ρ⟩` has order `3 = |S₃|₃`. -/
theorem card_zpowers_ρ : Nat.card (Subgroup.zpowers ρ) = 3 ^ (Nat.card S₃).factorization 3 := by
  have hρ : Nat.card (Subgroup.zpowers ρ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) (by decide) (by decide)]
  -- `|S₃| = 3! = 6`, and `3 ∣ 6` while `3 ^ 2 ∤ 6`.
  have hS₃ : (Nat.card S₃).factorization 3 = 1 := by
    rw [Nat.card_perm, Nat.card_fin, Nat.factorization_def _ Nat.prime_three]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  rw [hρ, hS₃, pow_one]

/-- `⟨ρ⟩` is the only Sylow `3`-subgroup of `S₃`: it has index `2`, so it is normal. -/
theorem sylow_eq_zpowers_ρ (S : Sylow 3 S₃) : (S : Subgroup S₃) = Subgroup.zpowers ρ := by
  set P := Sylow.ofCard _ card_zpowers_ρ
  have hindex : (Subgroup.zpowers ρ).index = 2 := by
    have h := (Subgroup.zpowers ρ).card_mul_index
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) (by decide) (by decide), Nat.card_perm,
      Nat.card_fin] at h
    have h6 : Nat.factorial 3 = 3 * 2 := rfl
    rw [h6] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hP : (P : Subgroup S₃).Normal := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.normal_of_index_eq_two hindex
  have := Sylow.unique_of_normal P hP
  rw [Subsingleton.elim S P, Sylow.coe_ofCard]

/-- **The defect group of `1` in `𝔽₃[S₃]`** is the Sylow `3`-subgroup `⟨ρ⟩`: `1` is central with
augmentation `1`. -/
theorem isDefectGroup_one_s₃_iff {D : Subgroup S₃} :
    IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D ↔ D = Subgroup.zpowers ρ := by
  rw [isDefectGroup_iff_sylow_of_augmentation_ne_zero (Subalgebra.one_mem _)
    (by rw [map_one]; exact one_ne_zero)]
  refine ⟨fun ⟨S, hS⟩ ↦ hS.trans (sylow_eq_zpowers_ρ S), fun hD ↦ ?_⟩
  exact ⟨Sylow.ofCard _ card_zpowers_ρ, by rw [hD, Sylow.coe_ofCard]⟩

/-- Every `3`-subgroup of `C₂` is trivial. -/
theorem eq_bot_of_isPGroup_three {Q : Subgroup C₂} (hQ : IsPGroup 3 Q) : Q = ⊥ := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have h2 : Nat.card Q ∣ 2 := by
    simpa using Subgroup.card_subgroup_dvd_card Q
  rw [hn] at h2
  exact Subgroup.eq_bot_of_card_eq Q <| hn.trans <|
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n (by norm_num)) h2

/-- **Defect groups in `𝔽₃[C₂]`**: every nonzero element has the single defect group `1`. -/
theorem isDefectGroup_c₂_iff {y : MonoidAlgebra (ZMod 3) C₂} (hy : y ≠ 0) {D : Subgroup C₂} :
    IsDefectGroup (ZMod 3) 3 y D ↔ D = ⊥ := by
  refine ⟨fun hD ↦ eq_bot_of_isPGroup_three hD.isPGroup, ?_⟩
  rintro rfl
  exact isDefectGroup_iff.2 ⟨IsPGroup.of_bot, mt brauerProjection_bot_eq_zero_iff.1 hy,
    fun Q hQ _ _ ↦ eq_bot_of_isPGroup_three hQ⟩

/-- **Defect groups of `1 ⊗ y` in `𝔽₃[S₃ × C₂]`**: for nonzero `y ∈ 𝔽₃[C₂]`, the single defect
group of `1 ⊗ y` is `C₃ × 1`. -/
theorem isDefectGroup_one_tmul_iff {y : MonoidAlgebra (ZMod 3) C₂} (hy : y ≠ 0)
    {Q : Subgroup (S₃ × C₂)} :
    IsDefectGroup (ZMod 3) 3 (tensorEquiv (ZMod 3) ((1 : MonoidAlgebra (ZMod 3) S₃) ⊗ₜ y)) Q ↔
      Q = (Subgroup.zpowers ρ).prod ⊥ := by
  simp_rw [isDefectGroup_tensorEquiv_tmul_iff, isDefectGroup_one_s₃_iff, isDefectGroup_c₂_iff hy]
  exact ⟨fun ⟨_, _, h₁, h₂, h⟩ ↦ h₁ ▸ h₂ ▸ h, fun h ↦ ⟨_, _, rfl, rfl, h⟩⟩

/-- `e₊ = (1 + t)/2` is nonzero. -/
theorem ePlus_ne_zero : ePlus ≠ 0 := fun h ↦
  isBlockIdempotent_ePlus.ne_zero (by rw [h, map_zero])

/-- `e₋ = (1 - t)/2` is nonzero. -/
theorem eMinus_ne_zero : eMinus ≠ 0 := fun h ↦
  isBlockIdempotent_eMinus.ne_zero (by rw [h, map_zero])

/-- **Check.** The defect group of `1 ⊗ e₊` in `𝔽₃[S₃ × C₂]` is `C₃ × 1`. -/
theorem isDefectGroup_one_tmul_ePlus_iff {Q : Subgroup (S₃ × C₂)} :
    IsDefectGroup (ZMod 3) 3 (tensorEquiv (ZMod 3) ((1 : MonoidAlgebra (ZMod 3) S₃) ⊗ₜ ePlus))
      Q ↔ Q = (Subgroup.zpowers ρ).prod ⊥ :=
  isDefectGroup_one_tmul_iff ePlus_ne_zero

/-- **Check.** The defect group of `1 ⊗ e₋` in `𝔽₃[S₃ × C₂]` is `C₃ × 1`. -/
theorem isDefectGroup_one_tmul_eMinus_iff {Q : Subgroup (S₃ × C₂)} :
    IsDefectGroup (ZMod 3) 3 (tensorEquiv (ZMod 3) ((1 : MonoidAlgebra (ZMod 3) S₃) ⊗ₜ eMinus))
      Q ↔ Q = (Subgroup.zpowers ρ).prod ⊥ :=
  isDefectGroup_one_tmul_iff eMinus_ne_zero

/-! ### `𝔽₂[C₃ × C₃]`: the splitting is needed -/

/-- The block `e = r + r²` of `𝔽₂[C₃]`. -/
noncomputable abbrev e : MonoidAlgebra (ZMod 2) C₃ := of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)

/-- `f₁ = ∑_{ab ≠ 1} (a, b)` in `𝔽₂[C₃ × C₃]`. -/
noncomputable def f₁ : MonoidAlgebra (ZMod 2) (C₃ × C₃) :=
  ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ if g.1 * g.2 = 1 then 0 else 1)

/-- `f₂ = ∑_{a ≠ b} (a, b)` in `𝔽₂[C₃ × C₃]`. -/
noncomputable def f₂ : MonoidAlgebra (ZMod 2) (C₃ × C₃) :=
  ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ if g.1 = g.2 then 0 else 1)

/-- The coefficients of `f₁`. -/
theorem coeff_f₁ : ⇑f₁.coeff = fun g ↦ if g.1 * g.2 = 1 then 0 else 1 := by
  funext g
  simp [f₁]

/-- The coefficients of `f₂`. -/
theorem coeff_f₂ : ⇑f₂.coeff = fun g ↦ if g.1 = g.2 then 0 else 1 := by
  funext g
  simp [f₂]

/-- `e ⊗ e = f₁ + f₂` in `𝔽₂[C₃ × C₃]`. -/
theorem tensorEquiv_e_tmul_e : tensorEquiv (ZMod 2) (e ⊗ₜ e) = f₁ + f₂ := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  revert g
  simp only [coeff_tensorEquiv_tmul, coeff_add, Finsupp.add_apply, coeff_f₁, coeff_f₂, of_apply,
    coeff_single, Finsupp.single_apply]
  decide

/-- `f₁` is idempotent. -/
theorem isIdempotentElem_f₁ : IsIdempotentElem f₁ := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  revert g
  simp only [coeff_mul_eq_sum, coeff_f₁]
  decide

/-- `f₂` is idempotent. -/
theorem isIdempotentElem_f₂ : IsIdempotentElem f₂ := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  revert g
  simp only [coeff_mul_eq_sum, coeff_f₂]
  decide

/-- `f₁` and `f₂` are orthogonal. -/
theorem f₁_mul_f₂ : f₁ * f₂ = 0 := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  revert g
  simp only [coeff_mul_eq_sum, coeff_f₁, coeff_f₂, coeff_zero, Finsupp.zero_apply]
  decide

/-- `f₁` is nonzero: its coefficient at `(r, 1)` is `1`. -/
theorem f₁_ne_zero : f₁ ≠ 0 := fun h ↦ by
  have := congrArg (fun x : MonoidAlgebra (ZMod 2) (C₃ × C₃) ↦ x.coeff (r, 1)) h
  simp only [coeff_f₁, coeff_zero, Finsupp.zero_apply] at this
  exact absurd this (by decide)

/-- `f₂` is nonzero: its coefficient at `(r, 1)` is `1`. -/
theorem f₂_ne_zero : f₂ ≠ 0 := fun h ↦ by
  have := congrArg (fun x : MonoidAlgebra (ZMod 2) (C₃ × C₃) ↦ x.coeff (r, 1)) h
  simp only [coeff_f₂, coeff_zero, Finsupp.zero_apply] at this
  exact absurd this (by decide)

/-- **Check.** `e ⊗ e` is not a block of `𝔽₂[C₃ × C₃]`, although `e = r + r²` is a block of
`𝔽₂[C₃]` (`TauCeti.GroupAlgebraBlockExamples.isBlockIdempotent_r_add_r_sq`): `𝔽₂` does not split
`C₃`, and `e ⊗ e = f₁ + f₂` with `f₁`, `f₂` orthogonal nonzero idempotents. -/
theorem not_isBlockIdempotent_tensorEquiv_e_tmul_e :
    ¬ IsBlockIdempotent (toCenter (tensorEquiv (ZMod 2) (e ⊗ₜ e))) := by
  intro h
  have := h.eq_zero_or_eq_zero_of_add (isIdempotentElem_f₁.map toCenter)
    (isIdempotentElem_f₂.map toCenter) (by rw [← map_mul, f₁_mul_f₂, map_zero])
    (by rw [← map_mul, mul_comm, f₁_mul_f₂, map_zero]) (by rw [← map_add, tensorEquiv_e_tmul_e])
  rcases this with h₁ | h₂
  · exact f₁_ne_zero (toCenter.injective (h₁.trans (map_zero _).symm))
  · exact f₂_ne_zero (toCenter.injective (h₂.trans (map_zero _).symm))

end TauCeti.DefectGroupProdExamples
