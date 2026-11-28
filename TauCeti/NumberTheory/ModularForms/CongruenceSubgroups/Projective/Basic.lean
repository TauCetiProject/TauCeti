/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

/-!
# The projective images of `Γ₀(N)` and `Γ(N)`

The compactified modular curve is a quotient by a subgroup of `PSL₂(ℤ)`, while congruence
subgroups are defined inside `SL₂(ℤ)`. Since `Γ₀(N)` contains the center `{±I}`, passing to its
projective image does not change its index, and lifting that image back to `SL₂(ℤ)` recovers
`Γ₀(N)`. This identifies the arithmetic index with the degree input used by the compactified
quotient map.

This module provides the subgroup-image definitions `Gamma0Projective` and `GammaProjective`
along with membership, lift, and antitonicity lemmas. Finite-quotient identifications and index
formulas for `GammaProjective` live in
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Principal`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.2 (the index of `Γ(N)` and of `±Γ(N)`).
-/

public section

open scoped MatrixGroups

namespace TauCeti.CongruenceSubgroup

/-- The image of `Γ₀(N)` in `PSL₂(ℤ)`, the group acting effectively on the upper half-plane. -/
def Gamma0Projective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma0 N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The projective image is the image under the quotient map by the center. -/
theorem Gamma0Projective_def (N : ℕ) :
    Gamma0Projective N =
      (CongruenceSubgroup.Gamma0 N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- The center of `SL₂(ℤ)` is contained in every congruence subgroup `Γ₀(N)`. -/
theorem center_le_Gamma0 (N : ℕ) :
    Subgroup.center SL(2, ℤ) ≤ CongruenceSubgroup.Gamma0 N :=
  Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr CongruenceSubgroup.neg_one_mem_Gamma0

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

/-- The projective image of `Γ₀(N)` has the same index as `Γ₀(N)`: the quotient map's kernel,
the center of `SL₂(ℤ)`, is already contained in `Γ₀(N)`. -/
theorem Gamma0Projective_index (N : ℕ) :
    (Gamma0Projective N).index = (CongruenceSubgroup.Gamma0 N).index :=
  Matrix.SpecialLinearGroup.index_map_mk'_of_neg_one_mem CongruenceSubgroup.neg_one_mem_Gamma0

/-- The lift of the projective image of `Γ₀(N)` to `SL₂(ℤ)` is `Γ₀(N)`, which contains `-I`. -/
@[simp]
theorem liftSL_Gamma0Projective (N : ℕ) :
    (Gamma0Projective N).liftSL = CongruenceSubgroup.Gamma0 N :=
  Matrix.SpecialLinearGroup.liftSL_map_of_neg_one_mem CongruenceSubgroup.neg_one_mem_Gamma0

/-! ### The projective principal congruence subgroup `GammaProjective N` -/

/-- The projective principal congruence subgroup `GammaProjective N ≤ PSL₂(ℤ)`: the image of `Γ(N)`
under the projection `SL₂(ℤ) →* PSL₂(ℤ)`. -/
def GammaProjective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (CongruenceSubgroup.Gamma N).map
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The projective principal congruence subgroup is the image of `Γ(N)` under the quotient map by
the center of `SL₂(ℤ)`. -/
theorem GammaProjective_def (N : ℕ) :
    GammaProjective N =
      (CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := (rfl)

/-- A matrix's class in `PSL₂(ℤ)` belongs to `GammaProjective N` if and only if either the matrix or
its negation belongs to `Γ(N)`. -/
@[simp]
theorem mem_GammaProjective_mk (N : ℕ) (A : SL(2, ℤ)) :
    (↑A : PSL(2, ℤ)) ∈ GammaProjective N ↔
      A ∈ CongruenceSubgroup.Gamma N ∨ -A ∈ CongruenceSubgroup.Gamma N := by
  rw [GammaProjective_def, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨C, hC, rfl⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp hBA
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hC with rfl | rfl
    · exact Or.inl (by simpa using hB)
    · exact Or.inr (by simpa using hB)
  · rintro (hA | hA)
    · exact ⟨A, hA, rfl⟩
    · exact ⟨-A, hA, Matrix.ProjectiveSpecialLinearGroup.mk_neg A⟩

/-- A projective element belongs to `GammaProjective N` if and only if it has a lift in `Γ(N)`. -/
theorem mem_GammaProjective_iff (N : ℕ) (g : PSL(2, ℤ)) :
    g ∈ GammaProjective N ↔
      ∃ A : SL(2, ℤ), QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) A = g ∧
        A ∈ CongruenceSubgroup.Gamma N := by
  rw [GammaProjective_def, Subgroup.mem_map]
  exact ⟨fun ⟨A, hA, hAg⟩ ↦ ⟨A, hAg, hA⟩, fun ⟨A, hAg, hA⟩ ↦ ⟨A, hA, hAg⟩⟩

instance GammaProjective_normal (N : ℕ) : (GammaProjective N).Normal :=
  (CongruenceSubgroup.Gamma_normal N).map _ (QuotientGroup.mk'_surjective _)

/-- Lifting `GammaProjective N` back to `SL₂(ℤ)` adjoins the center `{±I}`, yielding `±Γ(N)`. -/
@[simp]
theorem liftSL_GammaProjective (N : ℕ) :
    (GammaProjective N).liftSL = (CongruenceSubgroup.Gamma N).withCenter :=
  Subgroup.liftSL_map (CongruenceSubgroup.Gamma N)

/-- `GammaProjective N ≤ Γ` in `PSL₂(ℤ)` if and only if `Γ(N) ≤ Γ.liftSL` in `SL₂(ℤ)`. -/
theorem GammaProjective_le_iff {N : ℕ} {Γ : Subgroup PSL(2, ℤ)} :
    GammaProjective N ≤ Γ ↔ CongruenceSubgroup.Gamma N ≤ Γ.liftSL := by
  rw [GammaProjective_def, Subgroup.liftSL_def]
  exact Subgroup.map_le_iff_le_comap

/-- `GammaProjective` is antitone in the level: `GammaProjective N ≤ GammaProjective M` whenever
`M ∣ N`. -/
theorem GammaProjective_le_GammaProjective_of_dvd {M N : ℕ} (h : M ∣ N) :
    GammaProjective N ≤ GammaProjective M :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma_le_Gamma_of_dvd h)

end TauCeti.CongruenceSubgroup
