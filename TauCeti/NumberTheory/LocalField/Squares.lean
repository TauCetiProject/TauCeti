/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Square
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

import TauCeti.Algebra.Group.Units.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# Deep units are squares, at the sharp depth

In a nonarchimedean local field of characteristic different from two, every unit in
`U(K, 2 v_K(2) + 1)` is a square. The resulting openness of the square subgroup, including
in residue characteristic two, is proved in `PowerSubgroup.Open` and supplies neighborhoods
in which a nonzero value stays in one square class.

The exponent is `natCastValuation K 2 h2`, so no choice of a dyadic base field is needed.
The inclusion is the case `p = 2`, `i = v_K(2) + 1` of
`TauCeti.map_powMonoidHom_unitFiltration_of_prime`: squaring carries `U(K, v_K(2) + 1)` onto
`U(K, 2 v_K(2) + 1)`.

The depth is sharp: `U(K, 2 v_K(2))` is not contained in the squares. Since
`𝓂[K]^(2 v_K(2)) = 4 𝒪[K]`, an element `1 + 4c` of that depth is a square exactly when
`c = t² + t` for some integral `t`, so any `c` whose residue lies outside the image of the
Artin–Schreier map `t ↦ t² + t` of `𝓀[K]` gives a non-square. That map identifies `0` and `-1`,
so on the finite residue field it is not surjective. The argument is uniform in the residue
characteristic: when it is odd, `v_K(2) = 0` and the statement is that some unit is not a square.

## Main results

* `TauCeti.unitFiltration_le_range_powMonoidHom_two`: `U(K, 2 v_K(2) + 1) ⊆ (Kˣ)²`.
* `TauCeti.isSquare_of_eq_one_add_four_mul`: a residue Artin–Schreier condition makes
  `1 + 4m` a square.
* `TauCeti.valuation_one_add_four_mul`: in residue characteristic two, `1 + 4m` is a unit.
* `TauCeti.not_mem_range_of_eq_sq_mul_one_add_four_mul`: a nonsquare of the form
  `ζ² (1 + 4m)` has residue of `m` outside the Artin–Schreier range.
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
* `TauCeti.artinSchreierMaximalIdealQuotientEquiv`,
  `TauCeti.maximalIdealQuotientEquivUnitFiltrationQuotient`, and
  `TauCeti.natCard_artinSchreier_square_maximalIdeal_quotient`: Artin–Schreier and unit-coset
  bijections on `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)` and the count of square classes of `1 + β (s² - s)` below
  `2 v_K(2)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, local square theorem.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3, for the case `K = ℚ₂`.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

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

/-- In characteristic different from two, the valuation of `4` is that of `π ^ (2 v_K(2))`, for
an irreducible element `π` of `𝒪[K]`. -/
theorem valuation_four_eq_pow (h2 : (2 : K) ≠ 0) {π : 𝒪[K]} (hπ : Irreducible π) :
    valuation K (4 : K) = valuation K (π : K) ^ (2 * natCastValuation K 2 h2) := by
  have h := valuation_natCast_eq_pow hπ 2 h2
  rw [Nat.cast_ofNat] at h
  rw [show (4 : K) = 2 * 2 by norm_num, map_mul, pow_mul', sq, h]

/-- Every unit of depth `2 v_K(2) + 1` is a square. This includes dyadic local fields;
only characteristic two itself is excluded. -/
theorem unitFiltration_le_range_powMonoidHom_two (h2 : (2 : K) ≠ 0) :
    unitFiltration K (2 * natCastValuation K 2 h2 + 1) ≤
      (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  -- Put the depth in the `i + v_K(2)` form expected by the general deep-unit theorem.
  have hdepth : 2 * natCastValuation K 2 h2 + 1 =
      natCastValuation K 2 h2 + 1 + natCastValuation K 2 h2 := by omega
  rw [hdepth]
  exact unitFiltration_le_range_powMonoidHom h2 fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_lt_of_dvd h2 (Nat.lt_succ_self _) hp hpK hpn

/-- A unit `w = 1 + 4m` is a square if the residue of `m` lies in the range of
`t ↦ t² + t`. -/
theorem isSquare_of_eq_one_add_four_mul (h2 : (2 : K) ≠ 0) {w : Kˣ} {m : 𝒪[K]}
    (hw : (w : K) = 1 + 4 * m) (hwv : valuation K (w : K) = 1)
    (hm : residue 𝒪[K] m ∈ Set.range (fun t : 𝓀[K] => t ^ 2 + t)) : IsSquare w := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  obtain ⟨t, ht⟩ := hm
  obtain ⟨s, rfl⟩ := residue_surjective t
  simp only at ht
  -- `μ = m - (s² + s)` lies in `𝓂[K]`.
  have hμ : m - (s ^ 2 + s) ∈ 𝓂[K] := by
    rw [← residue_eq_zero_iff, map_sub, map_add, map_pow, ht, sub_self]
  set μ : K := ((m - (s ^ 2 + s) : 𝒪[K]) : K) with hμdef
  have hμv : valuation K μ ≤ valuation K (π : K) := by
    have h := (Set.ext_iff.mp (hπ.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) _).mp hμ
    simpa [hμdef] using h
  have h4 := valuation_four_eq_pow h2 hπ
  have h4μ : valuation K (4 * μ) ≤ valuation K (π : K) ^ (2 * natCastValuation K 2 h2 + 1) := by
    rw [map_mul, h4, pow_succ]
    exact mul_le_mul' le_rfl hμv
  have h4μlt : valuation K (4 * μ) < 1 :=
    h4μ.trans_lt (pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero _))
  have hid : (w : K) = (1 + 2 * (s : K)) ^ 2 + 4 * μ := by
    rw [hw, hμdef]
    push_cast
    ring
  -- Hence `1 + 2s` is a unit.
  have hsv : valuation K ((1 + 2 * (s : K)) ^ 2) = 1 := by
    rw [show (1 + 2 * (s : K)) ^ 2 = (w : K) - 4 * μ by rw [hid]; ring,
      Valuation.map_sub_eq_of_lt_left _ (hwv ▸ h4μlt), hwv]
  have hs0 : 1 + 2 * (s : K) ≠ 0 := by
    rintro h
    simp [h] at hsv
  set σ : Kˣ := Units.mk0 _ hs0 with hσ
  -- `w / (1 + 2s)²` has depth `2 v_K(2) + 1`, so it is a square by the local square theorem.
  have hmem : w * (σ ^ 2)⁻¹ ∈ unitFiltration K (2 * natCastValuation K 2 h2 + 1) := by
    rw [mem_unitFiltration_succ_valuation _ _ π hπ]
    have hsub : ((w * (σ ^ 2)⁻¹ : Kˣ) : K) - 1 = 4 * μ / (1 + 2 * (s : K)) ^ 2 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hσ, Units.val_mk0,
        hid]
      field_simp
      ring
    rw [hsub, map_div₀, hsv, div_one, map_pow]
    exact h4μ
  obtain ⟨z, hz⟩ := unitFiltration_le_range_powMonoidHom_two h2 hmem
  rw [powMonoidHom_apply] at hz
  refine ⟨z * σ, ?_⟩
  rw [← sq, mul_pow, hz]
  group

/-- In residue characteristic two, `4 ∈ 𝓂[K]`, so every `1 + 4n` with `n ∈ 𝒪[K]` is a unit. -/
@[simp]
theorem valuation_one_add_four_mul (h2 : (2 : K) ≠ 0) (he : 0 < natCastValuation K 2 h2)
    (n : 𝒪[K]) : valuation K (1 + 4 * (n : K)) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  refine (valuation K).map_one_add_of_lt ?_
  rw [map_mul, valuation_four_eq_pow h2 hπ]
  calc valuation K (π : K) ^ (2 * natCastValuation K 2 h2) * valuation K (n : K)
      ≤ valuation K (π : K) ^ (2 * natCastValuation K 2 h2) * 1 :=
        mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).mp n.2)
    _ < 1 := by
        rw [mul_one]
        exact pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ) (by omega)

/-- In residue characteristic two, if a nonsquare is `ζ² (1 + 4n)` with `n ∈ 𝒪[K]`, the residue of
`n` lies outside the range of `t ↦ t² + t`. -/
theorem not_mem_range_of_eq_sq_mul_one_add_four_mul (h2 : (2 : K) ≠ 0)
    (he : 0 < natCastValuation K 2 h2) {a ζ : Kˣ} {n : 𝒪[K]} (ha : ¬IsSquare a)
    (hn : (a : K) = (ζ : K) ^ 2 * (1 + 4 * n)) :
    residue 𝒪[K] n ∉ Set.range (fun t : 𝓀[K] => t ^ 2 + t) := by
  intro hmem
  have hval : ((a * (ζ ^ 2)⁻¹ : Kˣ) : K) = 1 + 4 * n := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hn]
    field_simp
  have h := isSquare_of_eq_one_add_four_mul h2 hval
    (hval ▸ valuation_one_add_four_mul h2 he n) hmem
  exact ha (by simpa using h.mul (IsSquare.sq ζ))

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
  rw [square_eq_range_powMonoidHom]
  simpa only [dyadicLevel_def] using unitFiltration_le_range_powMonoidHom_two h2

/-- The sharp depth cannot be decreased: units at `2 * dyadicLevel K` are not all squares. -/
theorem not_unitFiltration_le_square (h2 : (2 : K) ≠ 0) :
    ¬ (unitFiltration K (2 * dyadicLevel K h2) ≤ Subgroup.square Kˣ) := by
  rw [square_eq_range_powMonoidHom]
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
  obtain ⟨ξ, hξ⟩ := Units.isSquare_coe_iff.mpr hsq
  apply valuation_sq_sub_one_ne_pow_odd h2 hπ hk ξ
  have hξ' : ((Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0 : Kˣ) : K) = ξ ^ 2 := by
    simpa [pow_two] using hξ
  rw [← hξ']
  simp only [Units.val_mk0, add_sub_cancel_left, map_pow]

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

section ArtinSchreierQuotient

private theorem finite_quotient_maximalIdeal_pow (N : ℕ) : Finite (𝒪[K] ⧸ 𝓂[K] ^ N) :=
  Nat.finite_of_card_ne_zero <| by
    rw [TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]
    exact (pow_pos Finite.card_pos N).ne'

/-- On the maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)`, the Artin–Schreier polynomial
`y ↦ y ^ 2 - y` is a bijection. -/
noncomputable def artinSchreierMaximalIdealQuotientEquiv (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (m : ℕ) :
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} ≃
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} :=
  Equiv.ofBijective
    (fun x ↦ ⟨x.1 ^ 2 - x.1, by rw [map_sub, map_pow, x.2, zero_pow two_ne_zero, sub_self]⟩)
    (by
      have : Finite (𝒪[K] ⧸ 𝓂[K] ^ (m + 1)) := finite_quotient_maximalIdeal_pow (m + 1)
      refine Finite.injective_iff_bijective.mp fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ h ↦ ?_
      obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      have hmem : (s₁ - s₂) * (s₁ + s₂ - 1) ∈ 𝓂[K] ^ (m + 1) := by
        have hq := Ideal.Quotient.eq.mp
          (by simpa [← map_pow, ← map_sub] using congrArg Subtype.val h)
        rwa [show (s₁ ^ 2 - s₁) - (s₂ ^ 2 - s₂) = (s₁ - s₂) * (s₁ + s₂ - 1) by ring] at hq
      have hw : IsUnit (s₁ + s₂ - 1) := by
        simpa only [neg_sub] using (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (s₁ + s₂)
          ((IsLocalRing.mem_maximalIdeal _).mp (add_mem
            (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy₁))
            (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy₂))))).neg
      exact Subtype.ext
        (Ideal.Quotient.eq.mpr (((𝓂[K] ^ (m + 1)).mul_unit_mem_iff_mem hw).mp hmem)))

/-- Evaluating `artinSchreierMaximalIdealQuotientEquiv` applies `y ↦ y ^ 2 - y`. -/
@[simp]
theorem coe_artinSchreierMaximalIdealQuotientEquiv_apply (m : ℕ)
    (x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0}) :
    (artinSchreierMaximalIdealQuotientEquiv K m x : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1)) = x.1 ^ 2 - x.1 := by
  simp only [artinSchreierMaximalIdealQuotientEquiv, Equiv.ofBijective_apply]

/-- For `v(β) = v(c)^n`, `n₁ = n + 1`, and `s ∈ 𝓂[K]`, the unit `1 + β s` lies in `U(K, n₁)`. -/
noncomputable def mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) : unitFiltration K n₁ :=
  have hle : valuation K ((β : K) * (s : K)) ≤ valuation K (c : K) ^ (n + 1) := by
    rw [map_mul, hvβ, pow_succ]
    exact mul_le_mul' le_rfl
      ((Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) s).mp hs)
  ⟨Units.mk0 (1 + (β : K) * (s : K)) fun h0 ↦ by
      have hlt := hle.trans_lt
        (pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hc) (by omega))
      simpa [h0] using (valuation K).map_one_add_of_lt hlt,
    (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mpr
      (by simpa only [Units.val_mk0, add_sub_cancel_left, hn₁] using hle)⟩

/-- Coercing `mkScaledUnit hc hvβ hn₁ hs` to `K` gives `1 + β s`. -/
@[simp]
theorem coe_mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) :
    (((mkScaledUnit hc hvβ hn₁ hs : unitFiltration K n₁) : Kˣ) : K) = 1 + (β : K) * (s : K) := by
  simp only [mkScaledUnit, Units.val_mk0]

private noncomputable def scaledElemOfUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (u : unitFiltration K n₁) : 𝒪[K] :=
  ⟨(((u : Kˣ) : K) - 1) / (β : K), by
    have hu := (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mp u.2
    rw [Valuation.mem_integer_iff, map_div₀, hvβ]
    refine ((div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n)).mpr ?_).trans
      (Valuation.integer.v_irreducible_lt_one hc).le
    rwa [mul_comm, ← pow_succ, ← hn₁]⟩

private theorem scaledElemOfUnit_mem_maximalIdeal {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (u : unitFiltration K n₁) : scaledElemOfUnit hc hvβ hn₁ u ∈ 𝓂[K] := by
  refine (Set.ext_iff.mp (hc.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) _).mpr ?_
  change valuation K ((((u : Kˣ) : K) - 1) / (β : K)) ≤ valuation K (c : K)
  rw [map_div₀, hvβ, div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n),
    mul_comm, ← pow_succ, ← hn₁]
  exact (mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc).mp u.2

private theorem scaledElemOfUnit_mkScaledUnit {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    {s : 𝒪[K]} (hs : s ∈ 𝓂[K]) :
    scaledElemOfUnit hc hvβ hn₁ (mkScaledUnit hc hvβ hn₁ hs) = s := by
  have hβ0 : (β : K) ≠ 0 := (Valuation.pos_iff _).mp
    (hvβ ▸ pow_pos (Valuation.integer.v_irreducible_pos hc) n)
  ext
  simp only [scaledElemOfUnit, coe_mkScaledUnit, add_sub_cancel_left, mul_div_cancel_left₀ _ hβ0]

private theorem scaledElemOfUnit_sub_mem_iff {c β : 𝒪[K]} (hc : Irreducible c) {n n₁ n₂ m : ℕ}
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (hn₁ : n₁ = n + 1)
    (hn₂ : n₂ = n + m + 1) (u₁ u₂ : unitFiltration K n₁) :
    scaledElemOfUnit hc hvβ hn₁ u₁ - scaledElemOfUnit hc hvβ hn₁ u₂ ∈ 𝓂[K] ^ (m + 1) ↔
      u₁⁻¹ * u₂ ∈ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) := by
  have hu₁ : valuation K ((u₁ : Kˣ) : K) = 1 :=
    (mem_unitFiltration_zero _).mp (unitFiltration_antitone (Nat.zero_le _) u₁.2)
  rw [← SetLike.mem_coe,
    Set.ext_iff.mp (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) (m + 1)) _,
    Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc]
  have hid : ((scaledElemOfUnit hc hvβ hn₁ u₁ - scaledElemOfUnit hc hvβ hn₁ u₂ : 𝒪[K]) : K) =
      -((u₁ : Kˣ) : K) * ((((u₁ : Kˣ)⁻¹ * (u₂ : Kˣ) : Kˣ) : K) - 1) / (β : K) := by
    have : ((u₁ : Kˣ) : K) ≠ 0 := (u₁ : Kˣ).ne_zero
    dsimp only [scaledElemOfUnit]; push_cast; field_simp; ring
  rw [hid, map_div₀, map_mul, Valuation.map_neg, hu₁, one_mul, hvβ,
    div_le_iff₀ (pow_pos (Valuation.integer.v_irreducible_pos hc) n), ← pow_add,
    show m + 1 + n = n₂ by omega]

/-- When `v(β) = v(c)^n`, `n₁ = n + 1`, and `n₂ = n + m + 1`, the map `[s] ↦ [1 + β s]` is a
bijection between the maximal-ideal classes in `𝒪[K] ⧸ 𝓂[K] ^ (m + 1)` and
`U(K, n₁) ⧸ U(K, n₂)`. -/
noncomputable def maximalIdealQuotientEquivUnitFiltrationQuotient {c β : 𝒪[K]} (hc : Irreducible c)
    {n n₁ n₂ : ℕ} (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (m : ℕ)
    (hn₁ : n₁ = n + 1) (hn₂ : n₂ = n + m + 1) :
    {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} ≃
    unitFiltration K n₁ ⧸ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) := by
  let invMap : unitFiltration K n₁ ⧸ (unitFiltration K n₂).subgroupOf (unitFiltration K n₁) →
      {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} :=
    Quotient.lift
      (fun u ↦ ⟨Ideal.Quotient.mk _ (scaledElemOfUnit hc hvβ hn₁ u), by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact scaledElemOfUnit_mem_maximalIdeal hc hvβ hn₁ u⟩)
      fun u₁ u₂ h ↦ Subtype.ext <| Ideal.Quotient.eq.mpr <|
        (scaledElemOfUnit_sub_mem_iff hc hvβ hn₁ hn₂ u₁ u₂).mpr (QuotientGroup.leftRel_apply.mp h)
  refine (Equiv.ofBijective invMap ⟨fun q₁ q₂ h ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩).symm
  · obtain ⟨u₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨u₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.mpr ((scaledElemOfUnit_sub_mem_iff hc hvβ hn₁ hn₂ u₁ u₂).mp
      (Ideal.Quotient.eq.mp (congrArg Subtype.val h)))
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs : s ∈ 𝓂[K] := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy)
    exact ⟨QuotientGroup.mk (mkScaledUnit hc hvβ hn₁ hs),
      Subtype.ext (congrArg (Ideal.Quotient.mk _) (scaledElemOfUnit_mkScaledUnit hc hvβ hn₁ hs))⟩

/-- `maximalIdealQuotientEquivUnitFiltrationQuotient` sends the class of `s ∈ 𝓂[K]` to the coset
of `mkScaledUnit hc hvβ hn₁ hs`. -/
theorem maximalIdealQuotientEquivUnitFiltrationQuotient_mk {c β : 𝒪[K]} (hc : Irreducible c)
    {n n₁ n₂ : ℕ} (hvβ : valuation K (β : K) = valuation K (c : K) ^ n) (m : ℕ)
    (hn₁ : n₁ = n + 1) (hn₂ : n₂ = n + m + 1) {s : 𝒪[K]} (hs : s ∈ 𝓂[K])
    (hs0 : Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m))
      (Ideal.Quotient.mk (𝓂[K] ^ (m + 1)) s) = 0) :
    maximalIdealQuotientEquivUnitFiltrationQuotient hc hvβ m hn₁ hn₂
        ⟨Ideal.Quotient.mk (𝓂[K] ^ (m + 1)) s, hs0⟩ =
      QuotientGroup.mk (mkScaledUnit hc hvβ hn₁ hs) := by
  unfold maximalIdealQuotientEquivUnitFiltrationQuotient
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext
    (congrArg (Ideal.Quotient.mk _) (scaledElemOfUnit_mkScaledUnit hc hvβ hn₁ hs).symm)

/-- Below `2 v_K(2)`, if `v(β) = v(c) ^ (2e - 2k - 1)` (`k < e = v_K(2)`) and `1 + β (s² - s)` is a
square in `K`, then either `s ∈ 𝓂[K]` or `1 - s ∈ 𝓂[K]`. -/
theorem mem_maximalIdeal_or_one_sub_mem_of_isSquare_one_add_mul_sq_sub (h2 : (2 : K) ≠ 0)
    {c β : 𝒪[K]} (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    {s : 𝒪[K]} (hs : IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))) :
    s ∈ 𝓂[K] ∨ 1 - s ∈ 𝓂[K] := by
  by_contra! hnot
  obtain ⟨ξ, hξ⟩ := hs
  have hsv : valuation K (s : K) = 1 := le_antisymm ((Valuation.mem_integer_iff _ _).mp s.2)
    (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr hnot.1))
  have h1sv : valuation K ((s : K) - 1) = 1 := by
    rw [show (s : K) - 1 = -((1 - s : 𝒪[K]) : K) by push_cast; ring, Valuation.map_neg]
    exact le_antisymm ((Valuation.mem_integer_iff _ _).mp (1 - s).2)
      (not_lt.mp (mt (valuation K).mem_maximalIdeal_iff.mpr hnot.2))
  apply valuation_sq_sub_one_ne_pow_odd h2 hc (by omega : natCastValuation K 2 h2 - k - 1 < _) ξ
  rw [show ξ ^ 2 - 1 = (β : K) * (s : K) * ((s : K) - 1) by rw [← sq] at hξ; linear_combination -hξ,
    map_mul, map_mul, hvβ, hsv, h1sv, mul_one, mul_one]
  congr 1; omega

private theorem natCard_subtype_eq_two_mul_of_symm (m : ℕ)
    {P : (𝒪[K] ⧸ 𝓂[K] ^ (m + 1)) → Prop} (hsym : ∀ y, P (1 - y) ↔ P y)
    (hdich : ∀ y, P y →
      Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0 ∨
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) (1 - y) = 0) :
    Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) // P y} =
      2 * Nat.card {x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (m + 1) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero m)) y = 0} // P x.1} := by
  let fac := Ideal.Quotient.factor (Ideal.pow_le_self (I := 𝓂[K]) (Nat.succ_ne_zero m))
  have : Nontrivial (𝒪[K] ⧸ 𝓂[K]) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
  have hnot_both : ∀ y, ¬ (fac y = 0 ∧ fac (1 - y) = 0) := fun y ⟨hy, h1y⟩ ↦ by
    rw [map_sub, map_one, hy, sub_zero] at h1y; exact one_ne_zero h1y
  let splitFn : Bool × {x : {y // fac y = 0} // P x.1} → {y // P y} :=
    fun ⟨b, x⟩ ↦ if b then ⟨x.1.1, x.2⟩ else ⟨1 - x.1.1, (hsym x.1.1).mpr x.2⟩
  refine (Nat.card_congr (Equiv.ofBijective splitFn ⟨?_, fun ⟨y, hyP⟩ ↦ ?_⟩).symm).trans
    (by rw [Nat.card_prod]; simp [fac])
  · rintro ⟨b₁, ⟨⟨y₁, hy₁⟩, _⟩⟩ ⟨b₂, ⟨⟨y₂, hy₂⟩, _⟩⟩ heq
    cases b₁ <;> cases b₂ <;>
      simp only [splitFn, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at heq
    · obtain rfl : y₁ = y₂ := by linear_combination -heq
      rfl
    · exact (hnot_both y₁ ⟨hy₁, heq ▸ hy₂⟩).elim
    · exact (hnot_both y₂ ⟨hy₂, heq.symm ▸ hy₁⟩).elim
    · subst heq; rfl
  · rcases hdich y hyP with hy0 | h1y0
    · exact ⟨⟨true, ⟨⟨y, hy0⟩, hyP⟩⟩, rfl⟩
    · exact ⟨⟨false, ⟨⟨1 - y, h1y0⟩, (hsym y).mpr hyP⟩⟩, by ext; simp [splitFn]⟩

private theorem isSquare_one_add_mul_sq_sub_congr (h2 : (2 : K) ≠ 0) {c β : 𝒪[K]}
    (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1))
    {s₁ s₂ : 𝒪[K]} (h : s₁ - s₂ ∈ 𝓂[K] ^ (2 * k + 2)) :
    IsSquare (1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K))) ↔
      IsSquare (1 + (β : K) * ((s₂ : K) ^ 2 - (s₂ : K))) := by
  have hc1 : valuation K (c : K) < 1 := Valuation.integer.v_irreducible_lt_one hc
  have hlt : ∀ s : 𝒪[K], valuation K ((β : K) * ((s : K) ^ 2 - (s : K))) < 1 := fun s ↦ by
    rw [map_mul, hvβ]
    exact (mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).mp
      (sub_mem (pow_mem s.2 2) s.2))).trans_lt (by simpa using pow_lt_one₀ zero_le hc1 (by omega))
  let u : 𝒪[K] → Kˣ := fun s ↦ Units.mk0 (1 + (β : K) * ((s : K) ^ 2 - (s : K))) fun h0 ↦ by
    simpa [h0] using (valuation K).map_one_add_of_lt (hlt s)
  have hdiff : (u s₁)⁻¹ * u s₂ ∈ unitFiltration K (2 * dyadicLevel K h2 + 1) := by
    rw [dyadicLevel_def, mem_unitFiltration_iff_valuation_sub_one_le (by omega) hc]
    have hd0 : 1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K)) ≠ 0 := (u s₁).ne_zero
    have hid : (((u s₁)⁻¹ * u s₂ : Kˣ) : K) - 1 =
        (β : K) * (((s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) : 𝒪[K]) : K) /
          (1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K))) := by
      simp only [u, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [eq_div_iff hd0, sub_mul, inv_mul_eq_div, div_mul_cancel₀ _ hd0, one_mul]; push_cast; ring
    have hmem : (s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) ∈ 𝓂[K] ^ (2 * k + 2) := by
      rw [show (s₂ ^ 2 - s₂) - (s₁ ^ 2 - s₁) = -(s₁ - s₂) * (s₁ + s₂ - 1) by ring]
      exact Ideal.mul_mem_right _ _ (neg_mem h)
    rw [hid, map_div₀, (valuation K).map_one_add_of_lt (hlt s₁), div_one, map_mul, hvβ]
    refine (mul_le_mul' le_rfl (Set.mem_ofPred_eq.mp ((Set.ext_iff.mp
      (hc.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) (2 * k + 2)) _).mp
        hmem))).trans_eq ?_
    rw [← pow_add]; congr 1; omega
  have hsq : IsSquare ((u s₁)⁻¹ * u s₂) :=
    Subgroup.mem_square.mp (unitFiltration_le_square h2 hdiff)
  rw [show 1 + (β : K) * ((s₁ : K) ^ 2 - (s₁ : K)) = ((u s₁ : Kˣ) : K) from rfl,
    show 1 + (β : K) * ((s₂ : K) ^ 2 - (s₂ : K)) = ((u s₂ : Kˣ) : K) from rfl,
    Units.isSquare_coe_iff, Units.isSquare_coe_iff]
  exact ⟨fun h1 ↦ by simpa only [mul_inv_cancel_left] using h1.mul hsq,
    fun h2' ↦ by simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h2'.mul hsq.inv⟩

private noncomputable def artinSchreierMaximalIdealSquareEquiv (h2 : (2 : K) ≠ 0)
    {c β : 𝒪[K]} (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1)) :
    {x : {y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2) //
        Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero (2 * k + 1))) y = 0} //
      ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = x.1 ∧
        IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} ≃
    {q : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k) ⧸
        (unitFiltration K (2 * natCastValuation K 2 h2 + 1)).subgroupOf
          (unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k)) //
      ∃ u : unitFiltration K (2 * natCastValuation K 2 h2 - 2 * k),
        QuotientGroup.mk u = q ∧ IsSquare (u : Kˣ)} := by
  let e := natCastValuation K 2 h2
  let E := (artinSchreierMaximalIdealQuotientEquiv K (2 * k + 1)).trans
    (maximalIdealQuotientEquivUnitFiltrationQuotient hc hvβ (2 * k + 1)
      (n₁ := 2 * e - 2 * k) (n₂ := 2 * e + 1) (by omega) (by omega))
  refine Equiv.subtypeEquiv E fun ⟨y, hy⟩ ↦ ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hs : s ∈ 𝓂[K] := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hy)
  have hsm : s ^ 2 - s ∈ 𝓂[K] := by
    rw [show s ^ 2 - s = s * (s - 1) by ring]; exact Ideal.mul_mem_right _ _ hs
  have hsm0 : Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero (2 * k + 1)))
      (Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) (s ^ 2 - s)) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hsm
  let u_s : unitFiltration K (2 * e - 2 * k) := mkScaledUnit hc hvβ (by omega) hsm
  have hE_eq : E ⟨Ideal.Quotient.mk _ s, hy⟩ = QuotientGroup.mk u_s := by
    dsimp only [E, Equiv.trans_apply]
    rw [show artinSchreierMaximalIdealQuotientEquiv K (2 * k + 1) ⟨Ideal.Quotient.mk _ s, hy⟩ =
        ⟨Ideal.Quotient.mk _ (s ^ 2 - s), hsm0⟩ by ext; simp [map_sub, map_pow],
      maximalIdealQuotientEquivUnitFiltrationQuotient_mk hc hvβ (2 * k + 1)
        (by omega) (by omega) hsm hsm0]
  rw [hE_eq, show (∃ s' : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s' = Ideal.Quotient.mk _ s ∧
      IsSquare (1 + (β : K) * ((s' : K) ^ 2 - (s' : K)))) ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) from
    ⟨fun ⟨s', hs', hsq⟩ ↦ (isSquare_one_add_mul_sq_sub_congr h2 hc hk hvβ
      (Ideal.Quotient.eq.mp hs')).mp hsq, fun hsq ↦ ⟨s, rfl, hsq⟩⟩]
  refine ⟨fun hsq ↦ ⟨u_s, rfl,
    Units.isSquare_coe_iff.mp (by simpa [u_s, coe_mkScaledUnit] using hsq)⟩, ?_⟩
  rintro ⟨u, hu_eq, hsq_u⟩
  have hdiff : (u : Kˣ)⁻¹ * (u_s : Kˣ) ∈ unitFiltration K (2 * dyadicLevel K h2 + 1) := by
    rw [dyadicLevel_def]; simpa only [e, Subgroup.coe_mul, Subgroup.coe_inv] using
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hu_eq)
  have hsq_mk : IsSquare ((u_s : Kˣ) : K) := Units.isSquare_coe_iff.mpr <| by
    simpa only [mul_inv_cancel_left] using
      hsq_u.mul (Subgroup.mem_square.mp (unitFiltration_le_square h2 hdiff))
  simpa [u_s, coe_mkScaledUnit] using hsq_mk

/-- Counting the Artin–Schreier square locus in `𝒪[K] ⧸ 𝓂[K] ^ (2k + 2)`: when
`v(β) = v(c) ^ (2e - 2k - 1)` (`k < e = v_K(2)`), there are `#𝓀[K] ^ (k + 1)` classes `[s]` for
which `1 + β (s² - s)` is a square in `K`. -/
theorem natCard_artinSchreier_square_maximalIdeal_quotient (h2 : (2 : K) ≠ 0)
    {c β : 𝒪[K]} (hc : Irreducible c) {k : ℕ} (hk : k < natCastValuation K 2 h2)
    (hvβ : valuation K (β : K) = valuation K (c : K) ^ (2 * natCastValuation K 2 h2 - 2 * k - 1)) :
    Nat.card {y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2) //
      ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = y ∧
        IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))} =
      Nat.card 𝓀[K] ^ (k + 1) := by
  let P : (𝒪[K] ⧸ 𝓂[K] ^ (2 * k + 2)) → Prop := fun y ↦
    ∃ s : 𝒪[K], Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s = y ∧
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K)))
  have hP_mk : ∀ s : 𝒪[K], P (Ideal.Quotient.mk (𝓂[K] ^ (2 * k + 2)) s) ↔
      IsSquare (1 + (β : K) * ((s : K) ^ 2 - (s : K))) := fun s ↦
    ⟨fun ⟨s', hs', hsq⟩ ↦ (isSquare_one_add_mul_sq_sub_congr h2 hc hk hvβ
      (Ideal.Quotient.eq.mp hs')).mp hsq, fun hsq ↦ ⟨s, rfl, hsq⟩⟩
  have hsplit := natCard_subtype_eq_two_mul_of_symm (2 * k + 1) (P := P)
    (fun y ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_one (Ideal.Quotient.mk _), ← map_sub, hP_mk, hP_mk,
        show ((1 - s : 𝒪[K]) : K) ^ 2 - ((1 - s : 𝒪[K]) : K) = (s : K) ^ 2 - (s : K) by
          push_cast; ring])
    (fun y hy ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      simpa only [← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem] using
        mem_maximalIdeal_or_one_sub_mem_of_isSquare_one_add_mul_sq_sub h2 hc hk hvβ
          ((hP_mk s).mp hy))
  rw [hsplit, Nat.card_congr (artinSchreierMaximalIdealSquareEquiv h2 hc hk hvβ)]
  exact two_mul_natCard_squareCosets_unitFiltration h2 hk

end ArtinSchreierQuotient

end TauCeti
