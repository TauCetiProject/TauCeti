/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
public import TauCeti.NumberTheory.Modular.ConjugateTranslation
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Cusp widths of `Γ₀(N)`

At the cusp `γ ∞ = a / c` represented by `γ = [a,b;c,d] ∈ SL₂(ℤ)`, the width of `Γ₀(N)` is
`TauCeti.cuspWidthGamma0 N γ = N / gcd(N,c²)`. The formula holds at every positive level and
every integral representative, including infinity and negative denominators. Since
`-I ∈ Γ₀(N)`, the full-coset translation width is also the classical projective cusp width.

The translation-membership criterion is stated for integer exponents, and the
width formula uses the existing `CuspTranslationOrbit` carrier. This supplies the
arithmetic width in the cusp q-parameter and in the ramification of the finite
map from level `N` to level one.

The conjugate `γ T^w γ⁻¹ = [1 - wac, wa²; -wc², 1 + wac]` by `w = cuspWidthGamma0 N γ` is the
element `TauCeti.cuspGeneratorGamma0 N γ` of `Γ₀(N)`. It fixes `γ ∞`, and it acts in the
coordinate `γ⁻¹ z` as the translation by `w`. The width and the lower-right entry of the
generator modulo `N` depend only on the `Γ₀(N)`-orbit of the cusp (see also
`TauCeti.cuspWidthGamma0_eq_of_cuspOrbitOfSL2Z_eq`).

## Main declarations

* `TauCeti.cuspWidthGamma0`: the width `N / gcd(N,c²)` of the cusp `γ ∞`.
* `TauCeti.conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd`: the translations in `Γ₀(N)` fixing
  `γ ∞` are the powers of `T` with exponent divisible by the width.
* `TauCeti.cuspGeneratorGamma0`: the element `γ T^w γ⁻¹` of `Γ₀(N)`.
* `TauCeti.cuspWidthGamma0_mul_mul` and `TauCeti.Gamma0Map_cuspGeneratorGamma0_mul_mul`: the
  width and the lower-right entry of the generator modulo `N` are unchanged when `γ` is multiplied
  on the left by an element of `Γ₀(N)` and on the right by an element fixing `∞`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

/-- A translation fixing `γ ∞` lies in `Γ₀(N)` exactly when its exponent times the
square of the cusp denominator is divisible by the level. -/
theorem conj_T_zpow_mem_Gamma0_iff (N : ℕ) (γ : SL(2, ℤ)) (j : ℤ) :
    γ * ModularGroup.T ^ j * γ⁻¹ ∈ Gamma0 N ↔ (N : ℤ) ∣ j * γ 1 0 ^ 2 := by
  rw [mem_Gamma0_iff_dvd]
  rw [γ.coe_conj_T_zpow j]
  simp [neg_mul]

/-- **The width of the cusp `γ ∞` of `Γ₀(N)`**: `N / gcd(N,c²)` for `c = γ₁₀` the lower-left
entry of `γ`, so that `γ ∞ = a / c`. At positive level, the translations in `Γ₀(N)` fixing
`γ ∞` are the conjugates `γ Tʲ γ⁻¹` with `j` a multiple of the width
(`conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd`). At level `0` the width is `0`
(`cuspWidthGamma0_zero`). -/
def cuspWidthGamma0 (N : ℕ) (γ : SL(2, ℤ)) : ℕ :=
  N / Nat.gcd N ((γ 1 0).natAbs ^ 2)

theorem cuspWidthGamma0_def (N : ℕ) (γ : SL(2, ℤ)) :
    cuspWidthGamma0 N γ = N / Nat.gcd N ((γ 1 0).natAbs ^ 2) := (rfl)

/-- The width of a cusp divides the level. -/
theorem cuspWidthGamma0_dvd (N : ℕ) (γ : SL(2, ℤ)) : cuspWidthGamma0 N γ ∣ N :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

/-- The width of a cusp is positive at positive level. -/
theorem cuspWidthGamma0_pos (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) : 0 < cuspWidthGamma0 N γ :=
  Nat.div_pos (Nat.gcd_le_left _ (NeZero.pos N)) (Nat.gcd_pos_of_pos_left _ (NeZero.pos N))

/-- The width times the square of the cusp denominator is a multiple of the level. -/
theorem natCast_dvd_cuspWidthGamma0_mul_sq (N : ℕ) (γ : SL(2, ℤ)) :
    (N : ℤ) ∣ cuspWidthGamma0 N γ * γ 1 0 ^ 2 := by
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, cuspWidthGamma0]
  have h := mul_dvd_mul_left (N / Nat.gcd N ((γ 1 0).natAbs ^ 2))
    (Nat.gcd_dvd_right N ((γ 1 0).natAbs ^ 2))
  rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)] at h

/-- For a divisor `δ` of the level, the width `w` of the cusp `γ ∞ = a / c` of `Γ₀(N)` times
`gcd(δ, c)²` is a multiple of `δ`. So `w gcd(δ, c)² / δ` is an integer, and `e(gcd(δ, c)² τ / δ)`
is an integral power of the local parameter `e(τ / w)` of the cusp. -/
theorem dvd_cuspWidthGamma0_mul_gcd_sq {N δ : ℕ} (hδ : δ ∣ N) (γ : SL(2, ℤ)) :
    δ ∣ cuspWidthGamma0 N γ * Nat.gcd δ (γ 1 0).natAbs ^ 2 := by
  have h₁ : δ ∣ cuspWidthGamma0 N γ * (γ 1 0).natAbs ^ 2 :=
    hδ.trans (by simpa [Int.natAbs_mul, Int.natAbs_pow] using
      Int.natAbs_dvd_natAbs.mpr (natCast_dvd_cuspWidthGamma0_mul_sq N γ))
  have h₂ : δ ∣ cuspWidthGamma0 N γ * δ ^ 2 := (dvd_pow_self δ two_ne_zero).mul_left _
  simpa [Nat.gcd_mul_left, Nat.pow_gcd_pow, Nat.gcd_comm] using Nat.dvd_gcd h₁ h₂

/-- At level `0` every cusp has width `0`. -/
@[simp]
theorem cuspWidthGamma0_zero (γ : SL(2, ℤ)) : cuspWidthGamma0 0 γ = 0 := by
  simp [cuspWidthGamma0]

/-- The cusp `∞ = 1 ∞` has width `1`. -/
@[simp]
theorem cuspWidthGamma0_one (N : ℕ) [NeZero N] : cuspWidthGamma0 N 1 = 1 := by
  simp [cuspWidthGamma0, Nat.div_self (NeZero.pos N)]

/-- At level `1` every cusp has width `1`. -/
@[simp]
theorem cuspWidthGamma0_level_one (γ : SL(2, ℤ)) : cuspWidthGamma0 1 γ = 1 := by
  simp [cuspWidthGamma0]

/-- The cusps `γ ∞` and `γ⁻¹ ∞` have the same width: their denominators agree up to sign. -/
@[simp]
theorem cuspWidthGamma0_inv (N : ℕ) (γ : SL(2, ℤ)) :
    cuspWidthGamma0 N γ⁻¹ = cuspWidthGamma0 N γ := by
  simp [cuspWidthGamma0]

/-- The exponents of the translations in `Γ₀(N)` fixing `γ ∞` are precisely the
multiples of the width `N / gcd(N,c²)`, where `c = γ₁₀`. -/
theorem conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd (N : ℕ) [NeZero N]
    (γ : SL(2, ℤ)) (j : ℤ) :
    γ * ModularGroup.T ^ j * γ⁻¹ ∈ Gamma0 N ↔ (cuspWidthGamma0 N γ : ℤ) ∣ j := by
  rw [conj_T_zpow_mem_Gamma0_iff, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow,
    Int.natCast_dvd, cuspWidthGamma0]
  have hg : 0 < Nat.gcd N ((γ 1 0).natAbs ^ 2) := Nat.gcd_pos_of_pos_left _ (NeZero.pos N)
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _) hg]
  simpa only [gcd_eq_nat_gcd, mul_comm j.natAbs] using
    (dvd_gcd_mul_iff_dvd_mul (k := N) (m := (γ 1 0).natAbs ^ 2) (n := j.natAbs)).symm

/-- The width is unchanged when `γ` is multiplied on the left by an element of `Γ₀(N)` and on
the right by an element fixing `∞`: the translations of `Γ₀(N)` fixing the two cusps are
conjugate by an element of `Γ₀(N)`. -/
theorem cuspWidthGamma0_mul_mul (N : ℕ) {h : SL(2, ℤ)} (hh : h ∈ Gamma0 N)
    (γ : SL(2, ℤ)) {M : SL(2, ℤ)} (hM : M 1 0 = 0) :
    cuspWidthGamma0 N (h * γ * M) = cuspWidthGamma0 N γ := by
  rcases eq_zero_or_neZero N with rfl | _
  · simp
  refine Nat.dvd_antisymm ?_ ?_ <;> rw [← Int.natCast_dvd_natCast]
  · rw [← conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd,
      ModularGroup.mul_mul_T_zpow_mul_inv_of_c_eq_zero h γ hM]
    exact mul_mem
      (mul_mem hh ((conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd N γ _).mpr dvd_rfl))
      (inv_mem hh)
  · rw [← conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd]
    have hmem := (conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd N (h * γ * M) _).mpr dvd_rfl
    rw [ModularGroup.mul_mul_T_zpow_mul_inv_of_c_eq_zero h γ hM] at hmem
    exact (Subgroup.mul_mem_cancel_left _ hh).mp
      ((Subgroup.mul_mem_cancel_right _ (inv_mem hh)).mp hmem)

/-- **The generator of the stabilizer of the cusp `γ ∞` in `Γ₀(N)`** at positive level, up to
sign: the conjugate `γ T^w γ⁻¹ = [1 - wac, wa²; -wc², 1 + wac]` of the translation by the width
`w = cuspWidthGamma0 N γ`. In the coordinate `γ⁻¹ z` it acts as `z ↦ z + w`
(`cuspGeneratorGamma0_smul_smul`). At level `0` the width is `0`, so this element is the
identity. -/
def cuspGeneratorGamma0 (N : ℕ) (γ : SL(2, ℤ)) : Gamma0 N :=
  ⟨γ * ModularGroup.T ^ (cuspWidthGamma0 N γ : ℤ) * γ⁻¹,
    (conj_T_zpow_mem_Gamma0_iff N γ _).mpr (natCast_dvd_cuspWidthGamma0_mul_sq N γ)⟩

@[simp]
theorem coe_cuspGeneratorGamma0 (N : ℕ) (γ : SL(2, ℤ)) :
    (cuspGeneratorGamma0 N γ : SL(2, ℤ)) =
      γ * ModularGroup.T ^ (cuspWidthGamma0 N γ : ℤ) * γ⁻¹ := (rfl)

/-- The entries of the generator: `[1 - wac, wa²; -wc², 1 + wac]` for `γ = [a,b;c,d]` and
`w = cuspWidthGamma0 N γ`. -/
theorem coe_cuspGeneratorGamma0_matrix (N : ℕ) (γ : SL(2, ℤ)) :
    ((cuspGeneratorGamma0 N γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - cuspWidthGamma0 N γ * γ 0 0 * γ 1 0, cuspWidthGamma0 N γ * γ 0 0 ^ 2;
        -cuspWidthGamma0 N γ * γ 1 0 ^ 2, 1 + cuspWidthGamma0 N γ * γ 0 0 * γ 1 0] :=
  γ.coe_conj_T_zpow _

/-- The lower-right entry of the generator modulo `N` is `1 + wac`. -/
theorem Gamma0Map_cuspGeneratorGamma0 (N : ℕ) (γ : SL(2, ℤ)) :
    Gamma0Map N (cuspGeneratorGamma0 N γ) =
      ((1 + cuspWidthGamma0 N γ * γ 0 0 * γ 1 0 : ℤ) : ZMod N) := by
  rw [Gamma0Map_apply, coe_cuspGeneratorGamma0_matrix]
  simp

/-- The generator of the cusp `∞` is `T ^ w`, whose lower-right entry is `1`. -/
@[simp]
theorem Gamma0Map_cuspGeneratorGamma0_one (N : ℕ) :
    Gamma0Map N (cuspGeneratorGamma0 N 1) = 1 := by
  simp [Gamma0Map_cuspGeneratorGamma0]

/-- In the coordinate `γ⁻¹ z` the generator acts as the translation by the width:
`γ T^w γ⁻¹ • γ • z = γ • (z + w)`. -/
theorem cuspGeneratorGamma0_smul_smul (N : ℕ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    (cuspGeneratorGamma0 N γ : SL(2, ℤ)) • γ • z =
      γ • ((cuspWidthGamma0 N γ : ℝ) +ᵥ z) := by
  rw [coe_cuspGeneratorGamma0, mul_smul, mul_smul, inv_smul_smul,
    UpperHalfPlane.modular_T_zpow_smul, Int.cast_natCast]

/-- The generator of `h γ M`, for `h ∈ Γ₀(N)` and `M` fixing `∞`, is the conjugate of the
generator of `γ` by `h`. -/
theorem coe_cuspGeneratorGamma0_mul_mul (N : ℕ) {h : SL(2, ℤ)} (hh : h ∈ Gamma0 N)
    (γ : SL(2, ℤ)) {M : SL(2, ℤ)} (hM : M 1 0 = 0) :
    (cuspGeneratorGamma0 N (h * γ * M) : SL(2, ℤ)) = h * cuspGeneratorGamma0 N γ * h⁻¹ := by
  rw [coe_cuspGeneratorGamma0, cuspWidthGamma0_mul_mul N hh γ hM,
    ModularGroup.mul_mul_T_zpow_mul_inv_of_c_eq_zero h γ hM, coe_cuspGeneratorGamma0]

/-- The lower-right entry modulo `N` of the generator of `h γ M`, for `h ∈ Γ₀(N)` and `M`
fixing `∞`, is that of the generator of `γ`. -/
theorem Gamma0Map_cuspGeneratorGamma0_mul_mul (N : ℕ) {h : SL(2, ℤ)} (hh : h ∈ Gamma0 N)
    (γ : SL(2, ℤ)) {M : SL(2, ℤ)} (hM : M 1 0 = 0) :
    Gamma0Map N (cuspGeneratorGamma0 N (h * γ * M)) = Gamma0Map N (cuspGeneratorGamma0 N γ) := by
  have : cuspGeneratorGamma0 N (h * γ * M) =
      ⟨h, hh⟩ * cuspGeneratorGamma0 N γ * (⟨h, hh⟩)⁻¹ :=
    Subtype.ext (coe_cuspGeneratorGamma0_mul_mul N hh γ hM)
  -- `Gamma0Map` is a monoid hom into `ZMod N`, so `map_inv` needs its corestriction to units
  rw [this, ← MonoidHom.coe_toHomUnits, map_mul, map_mul, map_inv, mul_inv_cancel_comm,
    MonoidHom.coe_toHomUnits]

namespace ModularForm

/-- **The width of a `Γ₀(N)` cusp translation orbit.** The coset of `γ` represents
`γ⁻¹ ∞` in the full-coset convention. Its denominator is `-γ₁₀`, so its width is
`N / gcd(N,γ₁₀²)`. This is also the projective width because `Γ₀(N)` contains `-I`. -/
@[simp↓ high]
theorem cuspTranslationOrbitWidth_Gamma0 (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    cuspTranslationOrbitWidth
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
        𝒮ℒ ⧸ ((Gamma0 N).map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit ((Gamma0 N).map (mapGL ℝ))) =
      cuspWidthGamma0 N γ := by
  refine Nat.dvd_right_iff_eq.mp fun m ↦ ?_
  rw [cuspTranslationOrbitWidth_mk_dvd_iff, ← zpow_natCast]
  simpa only [inv_inv, cuspWidthGamma0_inv, Int.natCast_dvd_natCast] using
    conj_T_zpow_mem_Gamma0_iff_cuspWidthGamma0_dvd N γ⁻¹ (m : ℤ)

end ModularForm

end TauCeti
