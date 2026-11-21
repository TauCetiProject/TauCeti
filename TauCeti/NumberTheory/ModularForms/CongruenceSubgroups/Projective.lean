/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# The projective images of `Γ₀(N)` and `Γ(N)`

The compactified modular curve is a quotient by a subgroup of `PSL₂(ℤ)`, while congruence
subgroups are defined inside `SL₂(ℤ)`. Since `Γ₀(N)` contains the center `{±I}`, passing to its
projective image does not change its index, and lifting that image back to `SL₂(ℤ)` recovers
`Γ₀(N)`. This identifies the arithmetic index with the degree input used by the compactified
quotient map.

The principal congruence subgroup `Γ(N)` behaves differently: for `N ≥ 3` it does not contain
`-I`, so its projective image `GammaProjective N` has half its index: the quotient
`PSL₂(ℤ) ⧸ GammaProjective N` is canonically isomorphic to the signed finite quotient
`TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) = SL₂(ℤ/Nℤ) ⧸ {±I}`, of order `|SL₂(ℤ/Nℤ)| / 2`
for `N ≥ 3` (and `1`, `6` at `N = 1, 2`). At `N = 3` the two indices are `24` and `12`.

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

/-! ### The projective principal congruence subgroup `GammaProjective N` and its finite quotient -/

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

/-- Reduction modulo `N` descended from `PSL₂(ℤ)` to the signed quotient
`TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) = SL₂(ℤ/Nℤ) ⧸ {±I}`. -/
noncomputable def psl2zToSignedQuotient (N : ℕ) :
    PSL(2, ℤ) →* TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) :=
  (TauCeti.Matrix.SignedQuotient.map (Int.castRingHom (ZMod N))).comp
    (TauCeti.Matrix.SignedQuotient.equivPSL ℤ).symm.toMonoidHom

/-- `psl2zToSignedQuotient N` evaluates on coset representatives by entrywise reduction modulo `N`.
-/
@[simp]
theorem psl2zToSignedQuotient_mk (N : ℕ) (g : SL(2, ℤ)) :
    psl2zToSignedQuotient N (QuotientGroup.mk g) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g) := by
  rw [psl2zToSignedQuotient, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← TauCeti.Matrix.SignedQuotient.equivPSL_mk ℤ g, MulEquiv.symm_apply_apply,
    TauCeti.Matrix.SignedQuotient.map_mk]

/-- By strong approximation for `SL₂(ℤ)`, `psl2zToSignedQuotient N` is surjective at every level. -/
theorem psl2zToSignedQuotient_surjective (N : ℕ) :
    Function.Surjective (psl2zToSignedQuotient N) :=
  (TauCeti.Matrix.SignedQuotient.map_surjective
    Matrix.SpecialLinearGroup.map_intCast_zmod_surjective).comp
    (TauCeti.Matrix.SignedQuotient.equivPSL ℤ).symm.surjective

/-- The kernel of `PSL₂(ℤ) →* SL₂(ℤ/Nℤ) ⧸ {±I}` is precisely `GammaProjective N`. -/
theorem ker_psl2zToSignedQuotient (N : ℕ) :
    (psl2zToSignedQuotient N).ker = GammaProjective N := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, psl2zToSignedQuotient_mk, QuotientGroup.eq_one_iff,
    TauCeti.Matrix.SpecialLinearGroup.negOneSubgroup_def, Subgroup.mem_zpowers_neg_one_iff,
    mem_GammaProjective_mk, CongruenceSubgroup.Gamma_mem', CongruenceSubgroup.Gamma_mem']
  have hneg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (-g) =
      -Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g :=
    Matrix.SpecialLinearGroup.coe_int_neg (R := ZMod N) g
  rw [hneg, neg_eq_iff_eq_neg]

/-- **Canonical isomorphism `PSL₂(ℤ) ⧸ GammaProjective N ≃* SL₂(ℤ/Nℤ) ⧸ {±I}`.** -/
noncomputable def quotientGammaProjectiveEquiv (N : ℕ) :
    (PSL(2, ℤ) ⧸ GammaProjective N) ≃* TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) :=
  QuotientGroup.liftEquiv (GammaProjective N)
    (psl2zToSignedQuotient_surjective N) (ker_psl2zToSignedQuotient N).symm

/-- Evaluation of `quotientGammaProjectiveEquiv N` on coset representatives. -/
@[simp]
theorem quotientGammaProjectiveEquiv_mk (N : ℕ) (x : PSL(2, ℤ)) :
    quotientGammaProjectiveEquiv N (QuotientGroup.mk x) = psl2zToSignedQuotient N x :=
  QuotientGroup.liftEquiv_mk _ _ _ x

/-- At every level `N : ℕ`, `[PSL₂(ℤ) : GammaProjective N] = |SL₂(ℤ/Nℤ) ⧸ {±I}|`. -/
theorem GammaProjective_index_eq_card (N : ℕ) :
    (GammaProjective N).index = Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (quotientGammaProjectiveEquiv N).toEquiv]

/-- At level `1`, `GammaProjective 1 = ⊤`, so `[PSL₂(ℤ) : GammaProjective 1] = 1`. -/
@[simp]
theorem GammaProjective_index_one : (GammaProjective 1).index = 1 := by
  rw [GammaProjective_index_eq_card, TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_one]

/-- At level `2`, `[PSL₂(ℤ) : GammaProjective 2] = |SL₂(𝔽₂)| = 6` since `-I = I` modulo `2`. -/
@[simp]
theorem GammaProjective_index_two : (GammaProjective 2).index = 6 := by
  rw [GammaProjective_index_eq_card, TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_two]

/-- **The projective index of `Γ(N)`** for `N ≥ 3`: since `-I ∉ Γ(N)`, the image of `Γ(N)` in
`PSL₂(ℤ)` has index `|SL₂(ℤ/Nℤ)| / 2`. -/
theorem two_mul_index_map_Gamma {N : ℕ} (hN : 3 ≤ N) :
    2 * ((CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = Nat.card SL(2, ZMod N) := by
  rw [← GammaProjective_def, GammaProjective_index_eq_card,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod hN]

/-- **Cleared Euler product for `[PSL₂(ℤ) : GammaProjective N]`** (`N ≥ 3`):
`2 · [PSL₂(ℤ) : GammaProjective N] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_GammaProjective_index_mul_prod_primeFactors_sq {N : ℕ} (hN : 3 ≤ N) :
    2 * (GammaProjective N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [GammaProjective_index_eq_card,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod_mul_prod_primeFactors_sq hN]

/-- The image of `Γ(3)` in `PSL₂(ℤ)` has index `12`, half the index of `Γ(3)`, since `-I ∉ Γ(3)`. -/
theorem index_map_Gamma_three :
    ((CongruenceSubgroup.Gamma 3).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 12 := by
  have h := two_mul_index_map_Gamma le_rfl
  rw [← CongruenceSubgroup.index_Gamma, CongruenceSubgroup.index_Gamma_three] at h
  omega

end TauCeti.CongruenceSubgroup
