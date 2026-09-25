/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.PowerSubgroup
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

import TauCeti.Algebra.Group.Units.Basic
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# Deep units are squares, at the sharp depth

In a nonarchimedean local field of characteristic different from two, every unit in
`U(K, 2 v_K(2) + 1)` is a square. In particular the subgroup of squares is open, including
in residue characteristic two. This supplies the neighborhoods in which a nonzero value
stays in one square class, used in approximation arguments for quadratic forms.

The exponent is `natCastValuation K 2 h2`, so no choice of a dyadic base field is needed.
The proof identifies `𝓂[K]^(2 v_K(2) + 1)` with `4 𝓂[K]` and applies Hensel's lemma to
`X² + X - c` at zero: if `c ∈ 𝓂[K]`, then `c = t² + t` and `1 + 4c = (1 + 2t)²`.

The depth is sharp: `U(K, 2 v_K(2))` is not contained in the squares. Since
`𝓂[K]^(2 v_K(2)) = 4 𝒪[K]`, an element `1 + 4c` of that depth is a square exactly when
`c = t² + t` for some integral `t`, so any `c` whose residue lies outside the image of the
Artin–Schreier map `t ↦ t² + t` of `𝓀[K]` gives a non-square. That map identifies `0` and `-1`,
so on the finite residue field it is not surjective. The argument is uniform in the residue
characteristic: when it is odd, `v_K(2) = 0` and the statement is that some unit is not a square.

## Main results

* `TauCeti.unitFiltration_le_range_powMonoidHom_two`: `U(K, 2 v_K(2) + 1) ⊆ (Kˣ)²`.
* `TauCeti.normalizedValuation_even_of_isSquare`: squares have even normalized valuation.
* `TauCeti.not_unitFiltration_le_range_powMonoidHom_two`: `U(K, 2 v_K(2)) ⊄ (Kˣ)²`.
* `TauCeti.exists_mem_unitFiltration_not_isSquare`: a nonsquare witness in
  `U(K, 2 v_K(2))`.
* `TauCeti.unitFiltration_le_range_powMonoidHom_two_iff`: `U(K, n) ⊆ (Kˣ)²` exactly when
  `2 v_K(2) + 1 ≤ n`.
* `TauCeti.dyadicLevel`: the valuation `v_K(2)` used in the square interface.
* `TauCeti.unitFiltration_le_square` and `TauCeti.not_unitFiltration_le_square`: the same sharp
  square theorem expressed using `Subgroup.square Kˣ`.
* `TauCeti.valuation_sq_sub_one_ne_pow_odd` and `TauCeti.not_isSquare_one_add_pow_odd`: below depth
  `2 v_K(2)`, a square cannot differ from one to exact odd order, so `1 + π^(2k+1)` is not a
  square when `k < v_K(2)`.
* `TauCeti.exists_integerUnit_residue_not_isSquare`: away from residue characteristic two there
  is a unit of `𝒪[K]` whose residue is a nonsquare.
* `TauCeti.isSquare_zpow_mul_iff`: for `w` of even valuation, `π ^ m * w` is a square exactly
  when `m` is even and `w` is a square.
* `TauCeti.not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation`: a uniformizer
  times an element of even valuation is not a square.
* `TauCeti.not_isSquare_of_isUniformizer`: a uniformizer is not a square.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, local square theorem.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3, for the case `K = ℚ₂`.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A square in a nonarchimedean local field has even normalized valuation. -/
theorem normalizedValuation_even_of_isSquare {a : Kˣ} (ha : IsSquare a) :
    Even (normalizedValuation K a).toAdd := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨(normalizedValuation K b).toAdd, ?_⟩
  simp

/-- The dyadic level `v_K(2)`, expressed using the supplied natural-valued valuation. -/
noncomputable def dyadicLevel (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (h2 : (2 : K) ≠ 0) : ℕ :=
  natCastValuation K 2 h2

@[simp]
theorem dyadicLevel_def (h2 : (2 : K) ≠ 0) :
    dyadicLevel K h2 = natCastValuation K 2 h2 :=
  by simp only [dyadicLevel]

/-- In characteristic different from two, the ideal `(4)` of `𝒪[K]` is `𝓂[K] ^ (2 v_K(2))`. -/
theorem span_four_eq_maximalIdeal_pow (h2 : (2 : K) ≠ 0) :
    Ideal.span {(4 : 𝒪[K])} = 𝓂[K] ^ (2 * natCastValuation K 2 h2) := by
  have h4 : ((4 : ℕ) : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have he : natCastValuation K 4 h4 = 2 * natCastValuation K 2 h2 := by
    simpa using natCastValuation_pow K 2 h2
  rw [← he, ← span_natCast_eq_maximalIdeal_pow K 4 h4]
  norm_num

/-- Every unit of depth `2 v_K(2) + 1` is a square. This includes dyadic local fields;
only characteristic two itself is excluded. -/
theorem unitFiltration_le_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    unitFiltration K (2 * natCastValuation K 2 h2 + 1) ≤
      (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  intro x hx
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  rw [pow_succ, ← span_four_eq_maximalIdeal_pow h2] at hu
  obtain ⟨c, hc, hcu⟩ := Ideal.mem_span_singleton_mul.mp hu
  have hsq : IsSquare (u : 𝒪[K]) := by
    have hu' : (u : 𝒪[K]) = 1 + 4 * c := by linear_combination -hcu
    rw [hu']
    exact HenselianRing.isSquare_one_add_four_mul_of_mem hc
  obtain ⟨a, ha⟩ := hsq
  have haU : IsUnit a := isUnit_mul_self_iff.mp (ha ▸ u.isUnit)
  refine ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom haU.unit, ?_⟩
  apply Units.ext
  simpa [pow_two, haU.unit_spec, ← hux] using congrArg (fun z : 𝒪[K] ↦ (z : K)) ha.symm

/-- The local square theorem is sharp: not every unit of depth `2 v_K(2)` is a square. In
residue characteristic two the witness is `1 + 4c` for any `c` whose residue is not of the form
`t² + t`; for `K = ℚ₂` this says that `5 ∈ 1 + 4ℤ₂` is not a square. In odd residue
characteristic the depth is zero and the statement is that some unit is not a square. -/
theorem not_unitFiltration_le_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    ¬ unitFiltration K (2 * natCastValuation K 2 h2) ≤ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  obtain ⟨a, ha_range⟩ := exists_not_mem_range_sq_add_self (𝓀[K])
  have ha : ∀ t : 𝓀[K], t ^ 2 + t ≠ a := fun t ht => ha_range ⟨t, ht⟩
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective a
  -- `1 + 4c` is a unit: otherwise `2c` would reduce to a solution of `t ^ 2 + t = c`.
  have hu : IsUnit (1 + 4 * c) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    exact ha (2 * IsLocalRing.residue 𝒪[K] c) (by
      simp only [map_add, map_mul, map_one, map_ofNat] at h0
      linear_combination (IsLocalRing.residue 𝒪[K] c) * h0)
  intro hle
  obtain ⟨y, hy⟩ := hle (x := Units.map (𝒪[K].subtype : 𝒪[K] →* K) hu.unit) <|
    mem_unitFiltration_iff_exists.mpr ⟨hu.unit, by
      rw [← span_four_eq_maximalIdeal_pow h2]
      simp only [IsUnit.unit_spec, add_sub_cancel_left]
      exact Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self 4), rfl⟩
  have h4 : ((4 : 𝒪[K]) : K) = 4 := map_ofNat 𝒪[K].subtype 4
  have hyK : (y : K) ^ 2 = 1 + 4 * (c : K) := by
    simpa [h4] using congrArg Units.val hy
  -- A square root of the integral element `1 + 4c` is integral.
  have hyO : (y : K) ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, ← pow_le_one_iff two_ne_zero, ← map_pow, hyK]
    exact (1 + 4 * c).2
  have h2' : (2 : 𝒪[K]) ≠ 0 := fun h ↦ h2 <| by
    rw [← map_ofNat 𝒪[K].subtype 2, h, map_zero]
  obtain ⟨t, ht⟩ :=
    (ValuationRing.isSquare_one_add_four_mul_iff (IsRegular.of_ne_zero h2')).mp
    ⟨⟨y, hyO⟩, Subtype.ext (by simpa [pow_two, h4] using hyK.symm)⟩
  exact ha (IsLocalRing.residue 𝒪[K] t) (by rw [← ht]; simp)

/-- There is a nonsquare in the last unit-filtration step not entirely contained in the
squares. -/
theorem exists_mem_unitFiltration_not_isSquare (h2 : (2 : K) ≠ 0) :
    ∃ u : Kˣ, u ∈ unitFiltration K (2 * natCastValuation K 2 h2) ∧ ¬IsSquare u := by
  obtain ⟨u, hu, hsq⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_unitFiltration_le_range_powMonoidHom_two h2)
  exact ⟨u, hu, by
    simpa only [MonoidHom.mem_range, powMonoidHom_apply, isSquare_iff_exists_sq, eq_comm]
      using hsq⟩

/-- Every unit of depth `2 * dyadicLevel K + 1` is a square. -/
theorem unitFiltration_le_square (h2 : (2 : K) ≠ 0) :
    unitFiltration K (2 * dyadicLevel K h2 + 1) ≤ Subgroup.square Kˣ := by
  rw [square_eq_powMonoidHom_two_range]
  simpa only [dyadicLevel_def] using unitFiltration_le_range_powMonoidHom_two h2

/-- The sharp depth cannot be decreased: units at `2 * dyadicLevel K` are not all squares. -/
theorem not_unitFiltration_le_square (h2 : (2 : K) ≠ 0) :
    ¬ (unitFiltration K (2 * dyadicLevel K h2) ≤ Subgroup.square Kˣ) := by
  rw [square_eq_powMonoidHom_two_range]
  simpa only [dyadicLevel_def] using not_unitFiltration_le_range_powMonoidHom_two h2

/-- The exact depth of the local square theorem: `U(K, n)` consists of squares if and only if
`n ≥ 2 v_K(2) + 1`. -/
theorem unitFiltration_le_range_powMonoidHom_two_iff (h2 : (2 : K) ≠ 0) {n : ℕ} :
    unitFiltration K n ≤ (powMonoidHom 2 : Kˣ →* Kˣ).range ↔
      2 * natCastValuation K 2 h2 + 1 ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (unitFiltration_antitone h).trans (unitFiltration_le_range_powMonoidHom_two h2)⟩
  by_contra! hn
  exact not_unitFiltration_le_range_powMonoidHom_two h2
    ((unitFiltration_antitone (Nat.le_of_lt_succ hn)).trans h)

/-- Below twice the valuation of two, a square cannot differ from one to exact odd order. -/
theorem valuation_sq_sub_one_ne_pow_odd (h2 : (2 : K) ≠ 0) {π : 𝒪[K]}
    (hπ : Irreducible π) {k : ℕ} (hk : k < natCastValuation K 2 h2) (ξ : K) :
    valuation K (ξ ^ 2 - 1) ≠ valuation K (π : K) ^ (2 * k + 1) := by
  intro hξ
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hπv : valuation K (π : K) ≠ 0 := by simpa using hπ0
  have hz0 : ξ ^ 2 - 1 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hξ
    exact (pow_ne_zero _ hπv) hξ.symm
  have hx0 : ξ - 1 ≠ 0 := by
    intro hx
    apply hz0
    rw [sub_eq_zero.mp hx]
    simp
  have hy0 : ξ + 1 ≠ 0 := by
    intro hy
    apply hz0
    have hξneg : ξ = -1 := eq_neg_of_add_eq_zero_left hy
    rw [hξneg]
    norm_num
  let x : Kˣ := Units.mk0 (ξ - 1) hx0
  let y : Kˣ := Units.mk0 (ξ + 1) hy0
  let z : Kˣ := Units.mk0 (ξ ^ 2 - 1) hz0
  have hz : z = x * y := by
    apply Units.ext
    simp only [z, x, y, Units.val_mk0, Units.val_mul]
    ring
  have hzadd : (normalizedValuation K z).toAdd = ((2 * k + 1 : ℕ) : ℤ) :=
    (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) _ z).mpr
        (by simpa only [z, Units.val_mk0, zpow_natCast] using hξ)
  rw [hz, map_mul, toAdd_mul] at hzadd
  have hsmall : (normalizedValuation K x).toAdd < natCastValuation K 2 h2 ∨
      (normalizedValuation K y).toAdd < natCastValuation K 2 h2 := by
    omega
  have htwo : (normalizedValuation K (Units.mk0 (2 : K) h2)).toAdd =
      (natCastValuation K 2 h2 : ℤ) := toAdd_normalizedValuation_natCast K 2 h2
  have hvaluation_two_lt (a : Kˣ)
      (ha : (normalizedValuation K a).toAdd < natCastValuation K 2 h2) :
      valuation K (2 : K) < valuation K (a : K) := by
    have hnle : ¬(normalizedValuation K (Units.mk0 (2 : K) h2)).toAdd ≤
        (normalizedValuation K a).toAdd := by
      rw [htwo]
      exact not_le.mpr ha
    rw [toAdd_normalizedValuation_le_iff_valuation_le] at hnle
    exact lt_of_not_ge hnle
  have hadd_of_valuation_eq (a b : Kˣ)
      (hab : valuation K (b : K) = valuation K (a : K)) :
      (normalizedValuation K a).toAdd = (normalizedValuation K b).toAdd :=
    le_antisymm
      ((toAdd_normalizedValuation_le_iff_valuation_le a b).mpr hab.le)
      ((toAdd_normalizedValuation_le_iff_valuation_le b a).mpr hab.ge)
  rcases hsmall with hxsmall | hysmall
  · have hvlt := hvaluation_two_lt x hxsmall
    have hxy : valuation K (y : K) = valuation K (x : K) := by
      simp only [x, y, Units.val_mk0]
      calc
        valuation K (ξ + 1) = valuation K ((ξ - 1) + 2) := by congr 1; ring
        _ = valuation K (ξ - 1) := (valuation K).map_add_eq_of_lt_left (by simpa [x] using hvlt)
    have hxyadd := hadd_of_valuation_eq x y hxy
    omega
  · have hvlt := hvaluation_two_lt y hysmall
    have hxy : valuation K (x : K) = valuation K (y : K) := by
      simp only [x, y, Units.val_mk0]
      calc
        valuation K (ξ - 1) = valuation K ((ξ + 1) - 2) := by congr 1; ring
        _ = valuation K (ξ + 1) := (valuation K).map_sub_eq_of_lt_left (by simpa [y] using hvlt)
    have hxyadd := hadd_of_valuation_eq y x hxy
    omega

/-- For `k < v_K(2)`, the unit represented by `1 + π^(2k+1)` is not a square. -/
theorem not_isSquare_one_add_pow_odd (h2 : (2 : K) ≠ 0) {π : 𝒪[K]}
    (hπ : Irreducible π) {k : ℕ} (hk : k < natCastValuation K 2 h2) :
    ¬IsSquare (Units.mk0 (1 + (π : K) ^ (2 * k + 1))
      (one_add_pow_ne_zero_of_valuation_lt_one
        (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ) (by omega))) := by
  let hu0 : 1 + (π : K) ^ (2 * k + 1) ≠ 0 := one_add_pow_ne_zero_of_valuation_lt_one
    (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ) (by omega)
  -- Proof irrelevance identifies the nonzero proof in the statement with the named proof `hu0`.
  change ¬IsSquare (Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0)
  intro hsq
  obtain ⟨ξ, hξ⟩ := isSquare_units_val_iff.mpr hsq
  apply valuation_sq_sub_one_ne_pow_odd h2 hπ hk ξ
  have hξ' : ((Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0 : Kˣ) : K) = ξ ^ 2 := by
    simpa [pow_two] using hξ
  rw [← hξ']
  simp only [Units.val_mk0, add_sub_cancel_left, map_pow]

/-- The square subgroup of a nonarchimedean local field of characteristic different from two
is open in its unit group, also at dyadic places. -/
theorem isOpen_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    IsOpen ((powMonoidHom 2 : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isOpen_mono (unitFiltration_le_range_powMonoidHom_two h2)
    (isOpen_unitFiltration _)

/-- The square subgroup is closed in the unit group of a nonarchimedean local field of
characteristic different from two. -/
theorem isClosed_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    IsClosed ((powMonoidHom 2 : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_range_powMonoidHom_two h2)

/-- **Squares in a nonarchimedean local field.** Written against a uniformizer `π`, an element
`π ^ m * w` with `w` of even valuation is a square exactly when `m` is even and `w` is a square.
No hypothesis on the residue characteristic is needed. -/
theorem isSquare_zpow_mul_iff {π w : Kˣ} (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) (m : ℤ) :
    IsSquare (π ^ m * w) ↔ Even m ∧ IsSquare w := by
  have hπ' := (isUniformizer_def π).mp hπ
  refine ⟨fun hsq ↦ ?_, ?_⟩
  · -- The valuation of `π ^ m * w` is `m` plus the even valuation of `w`, so `m` is even.
    have hm : Even m := by
      have hev := even_toAdd_normalizedValuation_of_isSquare hsq
      rw [map_mul, toAdd_mul, normalizedValuation_zpow_of_eq_ofAdd_one hπ', toAdd_ofAdd] at hev
      exact (Int.even_add.mp hev).mpr hw
    refine ⟨hm, ?_⟩
    have h := hsq.mul ((even_neg.mpr hm).isSquare_zpow π)
    rwa [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at h
  · rintro ⟨hm, hw'⟩
    exact (hm.isSquare_zpow π).mul hw'

/-- A uniformizer times an element of even valuation has odd valuation, so it is not a
square. -/
theorem not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation {π w : Kˣ}
    (hπ : IsUniformizer K π)
    (hw : Even (normalizedValuation K w).toAdd) : ¬IsSquare (π * w) := fun h ↦
  Int.not_even_one ((isSquare_zpow_mul_iff hπ hw 1).mp (by simpa using h)).1

/-- A uniformizer is not a square. -/
theorem not_isSquare_of_isUniformizer {π : Kˣ} (hπ : IsUniformizer K π) : ¬IsSquare π := by
  simpa using not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation
    hπ (w := 1) (by simp)

/-- Away from residue characteristic two, there is a unit of `𝒪[K]` whose residue is a
nonsquare. -/
theorem exists_integerUnit_residue_not_isSquare (h2 : IsUnit (2 : 𝒪[K])) :
    ∃ u : 𝒪[K]ˣ, ¬IsSquare (Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_isUnit_two h2
  obtain ⟨x, hx, hxsq⟩ := exists_mem_unitFiltration_not_isSquare h2K
  have hx0 : x ∈ unitFiltration K 0 := unitFiltration_antitone (Nat.zero_le _) hx
  let x0 : unitFiltration K 0 := ⟨x, hx0⟩
  let u : 𝒪[K]ˣ := unitFiltrationToIntegerUnits 0 x0
  have hu_map : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u = x := by
    simp [u, x0]
  refine ⟨u, ?_⟩
  rw [← not_congr (isSquare_unitsMap_subtype_iff h2 u), hu_map]
  exact hxsq

end TauCeti
