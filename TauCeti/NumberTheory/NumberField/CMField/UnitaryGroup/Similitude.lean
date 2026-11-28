/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FrameFor
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel

/-!
# Unitary similitudes with rational multipliers over the finite adeles of a CM field

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `Ô_ℚ` the integral finite
adeles of `ℚ` and `n` a finite type. Complex conjugation makes `𝔸_f` a star ring
(`NumberField.IsCMField.instStarRingFiniteAdeleRing`), and `g* = star g` is the conjugate
transpose of a matrix `g` over `𝔸_f`. The units `Ô_ℚ^×` map to `𝔸_f^×` along `ℚ ⊆ E`
(`NumberField.zhatUnitsMap`).

* The *unitary similitudes* `GU ⊆ GL_n(𝔸_f)` of this file are the `g` with `c·g*g = ε·1` for
  some rational `c > 0` and some `ε ∈ Ô_ℚ^×`: the similitudes of the standard hermitian form whose
  multiplier `ε/c` is a rational finite idele. The full group of unitary similitudes allows any
  multiplier in the finite ideles of the maximal totally real subfield `E⁺`, so for `E⁺ ≠ ℚ` this
  subgroup can be strictly smaller. They form a subgroup by the closure properties of twisted
  similitudes (`Matrix.smul_transpose_map_mul_mul_mul_eq`,
  `Matrix.smul_transpose_map_mul_mul_eq_of_mul_eq_one`) for complex conjugation and the Gram
  matrix `1`, and contain the finite adelic unitary group `U(1_n)(𝔸_f)`
  (`TauCeti.finiteAdelicUnitaryGroup`).
* `GU⁺ ⊆ GU` is the monoid of those `g` with `g⁻¹ ∈ M_n(Ô)`.
* For an ideal `𝔑` of `𝓞 E`, the *principal level* is
  `K(𝔑) = GU ∩ {g ∈ GL_n(Ô) : g ≡ 1 mod 𝔑Ô}`, the intersection of `GU` with the principal
  congruence level `IsDedekindDomain.FiniteAdeleRing.principalLevel` of `GL_n(𝔸_f)`. Its trace on
  the unitary group is the principal level `TauCeti.principalUnitaryLevel` of `U(1_n)(𝔸_f)`.
* A frame for `β` multiplied by `g ∈ GU` is a frame for a positive rational multiple of `β`.

## Main definitions

* `TauCeti.unitarySimilitudes`: the subgroup `GU`.
* `TauCeti.unitarySimilitudesPlus`: the submonoid `GU⁺`.
* `TauCeti.similitudePrincipalLevel`: the subgroup `K(𝔑)`.

## Main results

* `TauCeti.finiteAdelicUnitaryGroup_le_unitarySimilitudes`: `U(1_n)(𝔸_f) ⊆ GU`.
* `TauCeti.mem_similitudePrincipalLevel_iff_forall`: the entrywise description of `K(𝔑)`;
  `TauCeti.similitudePrincipalLevel_mono`, `TauCeti.similitudePrincipalLevel_bot`.
* `TauCeti.principalUnitaryLevel_eq_subgroupOf`: the unitary principal level is the trace of
  `K(𝔑)` on `U(1_n)(𝔸_f)`.
* `TauCeti.IsFrameFor.exists_pos_isFrameFor_mul`: frames under `GU`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Variety.GU`, `New.Variety.GUPlus`,
  `New.Variety.levelGU`).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n]

/-- `g* g` as the twisted congruence of the Gram matrix `1` by `g`, for complex conjugation. -/
private theorem star_mul_self_eq (g : Matrix n n 𝔸ᶠ[E]) :
    star g * g = (g.map (finiteAdeleConj E : 𝔸ᶠ[E] →+* 𝔸ᶠ[E]))ᵀ * 1 * g := by
  rw [Matrix.mul_one, star_eq_transpose_map_finiteAdeleConj]

variable (E n) in
/-- The **unitary similitudes with rational multipliers** `GU ⊆ GL_n(𝔸_f)`: the `g` with
`c·g*g = ε·1` for some rational `c > 0` and some `ε ∈ Ô_ℚ^×`. This is the subgroup of the unitary
similitudes whose multiplier is a rational finite idele, which can be strictly smaller than the
group of all unitary similitudes, whose multipliers are finite ideles of `E⁺`. -/
def unitarySimilitudes : Subgroup (GL n 𝔸ᶠ[E]) where
  carrier := {g | ∃ c : ℚ, 0 < c ∧ ∃ ε : (integralAdeles ℤ ℚ)ˣ,
    algebraMap E 𝔸ᶠ[E] c • (star (g : Matrix n n 𝔸ᶠ[E]) * g) = (zhatUnitsMap E ε : 𝔸ᶠ[E]) • 1}
  one_mem' := ⟨1, one_pos, 1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc, ε, hg⟩ ⟨c', hc', ε', hh⟩
    refine ⟨c * c', mul_pos hc hc', ε * ε', ?_⟩
    rw [star_mul_self_eq] at hg hh ⊢
    simpa only [GeneralLinearGroup.coe_mul, Units.val_mul, Rat.cast_mul, map_mul] using
      smul_transpose_map_mul_mul_mul_eq _ hg hh
  inv_mem' := by
    rintro g ⟨c, hc, ε, hg⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, ε⁻¹, ?_⟩
    set g' : Matrix n n 𝔸ᶠ[E] := ↑g⁻¹
    have h : (zhatUnitsMap E ε : 𝔸ᶠ[E]) • (star g' * g') = algebraMap E 𝔸ᶠ[E] c • 1 := by
      rw [star_mul_self_eq] at hg ⊢
      exact smul_transpose_map_mul_mul_eq_of_mul_eq_one _ g.mul_inv hg
    have hca : algebraMap E 𝔸ᶠ[E] (c⁻¹ : ℚ) * algebraMap E 𝔸ᶠ[E] c = 1 := by
      simp [← map_mul, hc.ne']
    calc algebraMap E 𝔸ᶠ[E] (c⁻¹ : ℚ) • (star g' * g')
        = (algebraMap E 𝔸ᶠ[E] (c⁻¹ : ℚ) * ↑(zhatUnitsMap E ε)⁻¹) •
            ((zhatUnitsMap E ε : 𝔸ᶠ[E]) • (star g' * g')) := by
          rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]
      _ = _ := by rw [h, smul_smul, mul_right_comm, hca, one_mul, map_inv]

theorem mem_unitarySimilitudes_iff {g : GL n 𝔸ᶠ[E]} :
    g ∈ unitarySimilitudes E n ↔ ∃ c : ℚ, 0 < c ∧ ∃ ε : (integralAdeles ℤ ℚ)ˣ,
      algebraMap E 𝔸ᶠ[E] c • (star (g : Matrix n n 𝔸ᶠ[E]) * g) =
        (zhatUnitsMap E ε : 𝔸ᶠ[E]) • 1 :=
  Iff.rfl

/-- The finite adelic unitary group `U(1_n)(𝔸_f)` consists of unitary similitudes, with `c = 1`
and `ε = 1`. -/
theorem finiteAdelicUnitaryGroup_le_unitarySimilitudes :
    finiteAdelicUnitaryGroup E n ≤ unitarySimilitudes E n := fun g hg ↦
  ⟨1, one_pos, 1, by
    simp [mem_unitaryGroup_iff'.1 (mem_unitarySubgroup_GL_iff_mem_unitaryGroup.1 hg)]⟩

/-- **Frames under unitary similitudes**: if `x` is a frame for `β` and `g ∈ GU`, then `x g` is a
frame for `c β` for some rational `c > 0`. -/
theorem IsFrameFor.exists_pos_isFrameFor_mul {β : Matrix n n E} {x g : GL n 𝔸ᶠ[E]}
    (hx : IsFrameFor E β x) (hg : g ∈ unitarySimilitudes E n) :
    ∃ c : ℚ, 0 < c ∧ IsFrameFor E ((c : E) • β) (x * g) :=
  let ⟨c, hc, _, h⟩ := hg
  ⟨c, hc, hx.mul_of_smul_star_mul_self_eq h⟩

variable (E n) in
/-- The monoid `GU⁺ ⊆ GU` of unitary similitudes `g` with integral inverse `g⁻¹ ∈ M_n(Ô)`. -/
def unitarySimilitudesPlus : Submonoid (GL n 𝔸ᶠ[E]) where
  carrier := {g | g ∈ unitarySimilitudes E n ∧
    ∀ i j, (↑g⁻¹ : Matrix n n 𝔸ᶠ[E]) i j ∈ integralAdeles (𝓞 E) E}
  one_mem' := ⟨one_mem _, fun i j ↦ by
    rw [inv_one, Units.val_one, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, fun i j ↦ ?_⟩
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (hh' i k) (hg' k j)

theorem mem_unitarySimilitudesPlus_iff {g : GL n 𝔸ᶠ[E]} :
    g ∈ unitarySimilitudesPlus E n ↔ g ∈ unitarySimilitudes E n ∧
      ∀ i j, (↑g⁻¹ : Matrix n n 𝔸ᶠ[E]) i j ∈ integralAdeles (𝓞 E) E :=
  Iff.rfl

theorem unitarySimilitudesPlus_le :
    unitarySimilitudesPlus E n ≤ (unitarySimilitudes E n).toSubmonoid :=
  fun _ hg ↦ hg.1

variable (E n) in
/-- The **principal level** `K(𝔑) = GU ∩ {g ∈ GL_n(Ô) : g ≡ 1 mod 𝔑Ô}` of an ideal `𝔑` of `𝓞 E`:
the intersection of `GU` with the principal congruence level `principalLevel E n 𝔑` of
`GL_n(𝔸_f)`. For `𝔑 = 0` it is trivial. -/
def similitudePrincipalLevel (𝔑 : Ideal (𝓞 E)) : Subgroup (GL n 𝔸ᶠ[E]) :=
  unitarySimilitudes E n ⊓ principalLevel E n 𝔑

theorem mem_similitudePrincipalLevel_iff {𝔑 : Ideal (𝓞 E)} {g : GL n 𝔸ᶠ[E]} :
    g ∈ similitudePrincipalLevel E n 𝔑 ↔
      g ∈ unitarySimilitudes E n ∧ g ∈ principalLevel E n 𝔑 :=
  Subgroup.mem_inf

/-- **Entrywise description of the principal level**: `g ∈ K(𝔑)` exactly when `g ∈ GU`, the
entries of `g` and of `g⁻¹` are integral, and every entry of `g - 1` lies in `𝔑Ô`. -/
theorem mem_similitudePrincipalLevel_iff_forall {𝔑 : Ideal (𝓞 E)} {g : GL n 𝔸ᶠ[E]} :
    g ∈ similitudePrincipalLevel E n 𝔑 ↔ g ∈ unitarySimilitudes E n ∧
      ∃ (hg : ∀ i j, (g : Matrix n n 𝔸ᶠ[E]) i j ∈ integralAdeles (𝓞 E) E),
        (∀ i j, (↑g⁻¹ : Matrix n n 𝔸ᶠ[E]) i j ∈ integralAdeles (𝓞 E) E) ∧
          ∀ i j, (⟨_, hg i j⟩ - (1 : Matrix n n (integralAdeles (𝓞 E) E)) i j :
            integralAdeles (𝓞 E) E) ∈ completedIdeal E 𝔑 := by
  rw [mem_similitudePrincipalLevel_iff, mem_principalLevel_iff]

theorem similitudePrincipalLevel_le (𝔑 : Ideal (𝓞 E)) :
    similitudePrincipalLevel E n 𝔑 ≤ unitarySimilitudes E n :=
  inf_le_left

variable (E n) in
/-- `K(𝔐) ≤ K(𝔑)` whenever `𝔐 ⊆ 𝔑`. -/
theorem similitudePrincipalLevel_mono : Monotone (similitudePrincipalLevel E n) :=
  fun _ _ h ↦ inf_le_inf_left _ (principalLevel_mono E n h)

variable (E n) in
/-- At the zero ideal the principal level is trivial. -/
@[simp]
theorem similitudePrincipalLevel_bot : similitudePrincipalLevel E n ⊥ = ⊥ := by
  rw [similitudePrincipalLevel, principalLevel_bot, inf_bot_eq]

variable (E n) in
/-- The principal level `principalUnitaryLevel E n 𝔑` of the finite adelic unitary group is the
trace of `similitudePrincipalLevel E n 𝔑` on `U(1_n)(𝔸_f) ⊆ GU`. -/
theorem principalUnitaryLevel_eq_subgroupOf (𝔑 : Ideal (𝓞 E)) :
    principalUnitaryLevel E n 𝔑 =
      (similitudePrincipalLevel E n 𝔑).subgroupOf (finiteAdelicUnitaryGroup E n) := by
  ext g
  rw [principalUnitaryLevel_def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    similitudePrincipalLevel, Subgroup.mem_inf, principalLevel_eq_map_ker,
    and_iff_right (finiteAdelicUnitaryGroup_le_unitarySimilitudes g.property)]

end TauCeti
