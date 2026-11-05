/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.GroupTheory.QuotientGroup.Index
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Index

/-!
# The projective images of `Γ₀(N)`, `Γ₁(N)`, and `Γ(N)` in `PSL₂(ℤ)`

The compactified modular curve is a quotient by a subgroup of `PSL₂(ℤ)`, while congruence
subgroups are defined inside `SL₂(ℤ)`. Passing to the image in `PSL₂(ℤ) = SL₂(ℤ) ⧸ {±I}` replaces
a subgroup `H ≤ SL₂(ℤ)` with a subgroup of index `[SL₂(ℤ) : ±H]`:
* Since `Γ₀(N)` always contains `{±I}`, its projective image `Gamma0Projective N` has the same
  index as `Γ₀(N)` at every level.
* Since `Γ₁(N)` and `Γ(N)` contain `-I` precisely when `N ∣ 2`, their projective images
  `Gamma1Projective N` and `GammaProjective N` have the same index as `Γ₁(N)` and `Γ(N)` for
  `N ∣ 2`, and half the index whenever `¬ N ∣ 2` (in particular for all `N ≥ 3`).

## Main definitions

* `TauCeti.CongruenceSubgroup.Gamma0Projective`: the image of `Γ₀(N)` in `PSL₂(ℤ)`.
* `TauCeti.CongruenceSubgroup.Gamma1Projective`: the image of `Γ₁(N)` in `PSL₂(ℤ)`.
* `TauCeti.CongruenceSubgroup.GammaProjective`: the image of `Γ(N)` in `PSL₂(ℤ)`.

## Main results

* `TauCeti.CongruenceSubgroup.mem_Gamma0Projective_mk`,
  `TauCeti.CongruenceSubgroup.mem_Gamma1Projective_mk`,
  `TauCeti.CongruenceSubgroup.mem_GammaProjective_mk`: membership of a projected matrix in the
  three projective congruence subgroups.
* `TauCeti.CongruenceSubgroup.Gamma0Projective_index`,
  `TauCeti.CongruenceSubgroup.two_mul_Gamma1Projective_index_of_not_dvd_two`,
  `TauCeti.CongruenceSubgroup.two_mul_GammaProjective_index_of_not_dvd_two`: the indices of the
  projective congruence subgroups in `PSL₂(ℤ)`.
-/

public section

open scoped MatrixGroups

namespace TauCeti.CongruenceSubgroup

/-! ### Projective `Γ₀(N)` -/

/-- The image of `Γ₀(N)` in `PSL₂(ℤ)`, the group acting effectively on the upper half-plane. -/
def Gamma0Projective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma0 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The projective image is the image under the quotient map by the center. -/
theorem Gamma0Projective_def (N : ℕ) :
    Gamma0Projective N =
      (CongruenceSubgroup.Gamma0 N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- For `N ≠ 0`, `Gamma0Projective N` has finite index in `PSL₂(ℤ)`. -/
instance instFiniteIndexGamma0Projective (N : ℕ) [NeZero N] :
    (Gamma0Projective N).FiniteIndex :=
  inferInstanceAs ((CongruenceSubgroup.Gamma0 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).FiniteIndex

/-- At level one, `Gamma0Projective 1` is all of `PSL₂(ℤ)`. -/
@[simp]
theorem Gamma0Projective_one_top : Gamma0Projective 1 = ⊤ := by
  rw [Gamma0Projective_def, CongruenceSubgroup.Gamma0_one_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The center of `SL₂(ℤ)` is contained in every congruence subgroup `Γ₀(N)`. -/
theorem center_le_Gamma0 (N : ℕ) :
    Subgroup.center SL(2, ℤ) ≤ CongruenceSubgroup.Gamma0 N := by
  intro z hz
  rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hz with hz | hz
  · simp [hz]
  · simp [hz]

/-- Membership of the image of a matrix in `Γ₀(N)` is unchanged by projectivization. -/
@[simp]
theorem mem_Gamma0Projective_mk (N : ℕ) (A : SL(2, ℤ)) :
    (↑A : PSL(2, ℤ)) ∈ Gamma0Projective N ↔
      A ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Gamma0Projective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨C, hC, hBC⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp hBA
    rw [← hBC]
    exact mul_mem hB (center_le_Gamma0 N hC)
  · intro hA
    exact ⟨A, hA, rfl⟩

/-- A projective element belongs to the image of `Γ₀(N)` exactly when one of its
representatives belongs to `Γ₀(N)`. -/
theorem mem_Gamma0Projective_iff (N : ℕ) (g : PSL(2, ℤ)) :
    g ∈ Gamma0Projective N ↔
    ∃ A : SL(2, ℤ), QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) A = g ∧
        A ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Gamma0Projective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, rfl, hA⟩
  · rintro ⟨A, rfl, hA⟩
    exact ⟨A, hA, rfl⟩

/-- `Gamma0Projective` is antitone in the level under divisibility. -/
theorem Gamma0Projective_le_Gamma0Projective_of_dvd {M N : ℕ} (h : M ∣ N) :
    Gamma0Projective N ≤ Gamma0Projective M :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma0_le_Gamma0_of_dvd h)

/-- The projective image of `Γ₀(N)` has the same index as `Γ₀(N)`: the quotient map's kernel,
the center of `SL₂(ℤ)`, is already contained in `Γ₀(N)`. -/
theorem Gamma0Projective_index (N : ℕ) :
    (Gamma0Projective N).index = (CongruenceSubgroup.Gamma0 N).index := by
  rw [Gamma0Projective_def, Subgroup.index_map_mk'_eq_index_sup,
    sup_eq_left.mpr (center_le_Gamma0 N)]

/-! ### Projective `Γ₁(N)` -/

/-- The image of `Γ₁(N)` in `PSL₂(ℤ)`. -/
def Gamma1Projective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma1 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Unfolding: `Gamma1Projective N` is the image of `Γ₁(N)` under `SL₂(ℤ) →* PSL₂(ℤ)`. -/
theorem Gamma1Projective_def (N : ℕ) :
    Gamma1Projective N =
      (CongruenceSubgroup.Gamma1 N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- For `N ≠ 0`, `Gamma1Projective N` has finite index in `PSL₂(ℤ)`. -/
instance instFiniteIndexGamma1Projective (N : ℕ) [NeZero N] :
    (Gamma1Projective N).FiniteIndex :=
  inferInstanceAs ((CongruenceSubgroup.Gamma1 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).FiniteIndex

/-- At level one, `Gamma1Projective 1` is all of `PSL₂(ℤ)`. -/
@[simp]
theorem Gamma1Projective_one_top : Gamma1Projective 1 = ⊤ := by
  rw [Gamma1Projective_def, CongruenceSubgroup.Gamma1_one_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- A projected matrix `↑A ∈ PSL₂(ℤ)` lies in `Gamma1Projective N` iff `A ∈ Γ₁(N)` or
`-A ∈ Γ₁(N)`. -/
@[simp]
theorem mem_Gamma1Projective_mk (N : ℕ) (A : SL(2, ℤ)) :
    (↑A : PSL(2, ℤ)) ∈ Gamma1Projective N ↔
      A ∈ CongruenceSubgroup.Gamma1 N ∨ -A ∈ CongruenceSubgroup.Gamma1 N := by
  rw [Gamma1Projective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨C, hC, hBC⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp hBA
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hC with rfl | rfl
    · exact Or.inl (by rwa [← hBC, mul_one])
    · exact Or.inr (by rwa [← hBC, mul_neg_one, neg_neg])
  · rintro (hA | hnegA)
    · exact ⟨A, hA, rfl⟩
    · refine ⟨-A, hnegA, (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mpr
        ⟨-1, Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl), ?_⟩⟩
      simp

/-- A projective element belongs to `Gamma1Projective N` iff one of its lifts belongs to `Γ₁(N)`. -/
theorem mem_Gamma1Projective_iff (N : ℕ) (g : PSL(2, ℤ)) :
    g ∈ Gamma1Projective N ↔
      ∃ A : SL(2, ℤ), QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) A = g ∧
        A ∈ CongruenceSubgroup.Gamma1 N := by
  rw [Gamma1Projective_def, Subgroup.mem_map]
  exact ⟨fun ⟨A, hA, hg⟩ ↦ ⟨A, hg, hA⟩, fun ⟨A, hg, hA⟩ ↦ ⟨A, hA, hg⟩⟩

/-- `Gamma1Projective N` sits inside `Gamma0Projective N`. -/
theorem Gamma1Projective_le_Gamma0Projective (N : ℕ) :
    Gamma1Projective N ≤ Gamma0Projective N :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 N)

/-- `Gamma1Projective` is antitone in the level under divisibility. -/
theorem Gamma1Projective_le_Gamma1Projective_of_dvd {M N : ℕ} (h : M ∣ N) :
    Gamma1Projective N ≤ Gamma1Projective M :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma1_le_Gamma1_of_dvd h)

/-- The index of `Gamma1Projective N` in `PSL₂(ℤ)` is `[SL₂(ℤ) : ±Γ₁(N)]`. -/
theorem Gamma1Projective_index_eq_withCenter_index (N : ℕ) :
    (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).withCenter.index := by
  rw [Gamma1Projective_def, Subgroup.index_map_mk'_eq_index_sup, Subgroup.withCenter_def]

/-- For `N ∣ 2`, `Gamma1Projective N` has the same index as `Γ₁(N)`. -/
theorem Gamma1Projective_index_of_dvd_two {N : ℕ} (hN : N ∣ 2) :
    (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).index := by
  rw [Gamma1Projective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma1_withCenter_index_of_dvd_two hN]

/-- When `¬ N ∣ 2`, twice the index of `Gamma1Projective N` in `PSL₂(ℤ)` is `[SL₂(ℤ) : Γ₁(N)]`. -/
theorem two_mul_Gamma1Projective_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    2 * (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).index := by
  rw [Gamma1Projective_index_eq_withCenter_index,
    CongruenceSubgroup.two_mul_Gamma1_withCenter_index_of_not_dvd_two hN]

/-- When `¬ N ∣ 2`, `[PSL₂(ℤ) : Gamma1Projective N] = [SL₂(ℤ) : Γ₁(N)] / 2`. -/
theorem Gamma1Projective_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).index / 2 := by
  rw [Gamma1Projective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma1_withCenter_index_of_not_dvd_two hN]

/-- For `N ≥ 3`, `2 · [PSL₂(ℤ) : Gamma1Projective N] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem two_mul_Gamma1Projective_index {N : ℕ} (hN : 3 ≤ N) :
    2 * (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).index := by
  rw [Gamma1Projective_index_eq_withCenter_index,
    CongruenceSubgroup.two_mul_Gamma1_withCenter_index hN]

/-- For `N ≥ 3`, `[PSL₂(ℤ) : Gamma1Projective N] = [SL₂(ℤ) : Γ₁(N)] / 2`. -/
theorem Gamma1Projective_index_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (Gamma1Projective N).index = (CongruenceSubgroup.Gamma1 N).index / 2 := by
  rw [Gamma1Projective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma1_withCenter_index_of_three_le hN]

/-! ### Projective `Γ(N)` -/

/-- The image of the principal congruence subgroup `Γ(N)` in `PSL₂(ℤ)`. -/
def GammaProjective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Unfolding: `GammaProjective N` is the image of `Γ(N)` under `SL₂(ℤ) →* PSL₂(ℤ)`. -/
theorem GammaProjective_def (N : ℕ) :
    GammaProjective N =
      (CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- `GammaProjective N` is normal in `PSL₂(ℤ)`. -/
instance instNormalGammaProjective (N : ℕ) : (GammaProjective N).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- For `N ≠ 0`, `GammaProjective N` has finite index in `PSL₂(ℤ)`. -/
instance instFiniteIndexGammaProjective (N : ℕ) [NeZero N] :
    (GammaProjective N).FiniteIndex :=
  inferInstanceAs ((CongruenceSubgroup.Gamma N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).FiniteIndex

/-- At level one, `GammaProjective 1` is all of `PSL₂(ℤ)`. -/
@[simp]
theorem GammaProjective_one_top : GammaProjective 1 = ⊤ := by
  rw [GammaProjective_def, CongruenceSubgroup.Gamma_one_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- A projected matrix `↑A ∈ PSL₂(ℤ)` lies in `GammaProjective N` iff `A ∈ Γ(N)` or
`-A ∈ Γ(N)`. -/
@[simp]
theorem mem_GammaProjective_mk (N : ℕ) (A : SL(2, ℤ)) :
    (↑A : PSL(2, ℤ)) ∈ GammaProjective N ↔
      A ∈ CongruenceSubgroup.Gamma N ∨ -A ∈ CongruenceSubgroup.Gamma N := by
  rw [GammaProjective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨C, hC, hBC⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp hBA
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hC with rfl | rfl
    · exact Or.inl (by rwa [← hBC, mul_one])
    · exact Or.inr (by rwa [← hBC, mul_neg_one, neg_neg])
  · rintro (hA | hnegA)
    · exact ⟨A, hA, rfl⟩
    · refine ⟨-A, hnegA, (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mpr
        ⟨-1, Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl), ?_⟩⟩
      simp

/-- A projective element belongs to `GammaProjective N` iff one of its lifts belongs to `Γ(N)`. -/
theorem mem_GammaProjective_iff (N : ℕ) (g : PSL(2, ℤ)) :
    g ∈ GammaProjective N ↔
      ∃ A : SL(2, ℤ), QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) A = g ∧
        A ∈ CongruenceSubgroup.Gamma N := by
  rw [GammaProjective_def, Subgroup.mem_map]
  exact ⟨fun ⟨A, hA, hg⟩ ↦ ⟨A, hg, hA⟩, fun ⟨A, hg, hA⟩ ↦ ⟨A, hA, hg⟩⟩

/-- `GammaProjective N` sits inside `Gamma1Projective N`. -/
theorem GammaProjective_le_Gamma1Projective (N : ℕ) :
    GammaProjective N ≤ Gamma1Projective N :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma_le_Gamma1 N)

/-- `GammaProjective N` sits inside `Gamma0Projective N`. -/
theorem GammaProjective_le_Gamma0Projective (N : ℕ) :
    GammaProjective N ≤ Gamma0Projective N :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma_le_Gamma0 N)

/-- `GammaProjective` is antitone in the level under divisibility. -/
theorem GammaProjective_le_GammaProjective_of_dvd {M N : ℕ} (h : M ∣ N) :
    GammaProjective N ≤ GammaProjective M :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma_le_Gamma_of_dvd h)

/-- The index of `GammaProjective N` in `PSL₂(ℤ)` is `[SL₂(ℤ) : ±Γ(N)]`. -/
theorem GammaProjective_index_eq_withCenter_index (N : ℕ) :
    (GammaProjective N).index = (CongruenceSubgroup.Gamma N).withCenter.index := by
  rw [GammaProjective_def, Subgroup.index_map_mk'_eq_index_sup, Subgroup.withCenter_def]

/-- For `N ∣ 2`, `GammaProjective N` has the same index as `Γ(N)`. -/
theorem GammaProjective_index_of_dvd_two {N : ℕ} (hN : N ∣ 2) :
    (GammaProjective N).index = (CongruenceSubgroup.Gamma N).index := by
  rw [GammaProjective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma_withCenter_index_of_dvd_two hN]

/-- When `¬ N ∣ 2`, twice the index of `GammaProjective N` in `PSL₂(ℤ)` is `[SL₂(ℤ) : Γ(N)]`. -/
theorem two_mul_GammaProjective_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    2 * (GammaProjective N).index = (CongruenceSubgroup.Gamma N).index := by
  rw [GammaProjective_index_eq_withCenter_index,
    CongruenceSubgroup.two_mul_Gamma_withCenter_index_of_not_dvd_two hN]

/-- When `¬ N ∣ 2`, `[PSL₂(ℤ) : GammaProjective N] = [SL₂(ℤ) : Γ(N)] / 2`. -/
theorem GammaProjective_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    (GammaProjective N).index = (CongruenceSubgroup.Gamma N).index / 2 := by
  rw [GammaProjective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma_withCenter_index_of_not_dvd_two hN]

/-- For `N ≥ 3`, `2 · [PSL₂(ℤ) : GammaProjective N] = [SL₂(ℤ) : Γ(N)]`. -/
theorem two_mul_GammaProjective_index {N : ℕ} (hN : 3 ≤ N) :
    2 * (GammaProjective N).index = (CongruenceSubgroup.Gamma N).index := by
  rw [GammaProjective_index_eq_withCenter_index,
    CongruenceSubgroup.two_mul_Gamma_withCenter_index hN]

/-- For `N ≥ 3`, `[PSL₂(ℤ) : GammaProjective N] = [SL₂(ℤ) : Γ(N)] / 2`. -/
theorem GammaProjective_index_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (GammaProjective N).index = (CongruenceSubgroup.Gamma N).index / 2 := by
  rw [GammaProjective_index_eq_withCenter_index,
    CongruenceSubgroup.Gamma_withCenter_index_of_three_le hN]

end TauCeti.CongruenceSubgroup
