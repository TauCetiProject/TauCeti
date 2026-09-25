/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect
public import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass

import TauCeti.NumberTheory.LocalField.SquareClass
import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# The ramification dictionary for the quadratic defect

Let `K` be a nonarchimedean local field with `2 ≠ 0`, and write `e = v_K(2)`. Call `a ∈ Kˣ` an
*unramified class* when an element `b ∈ Kˣ` is a norm from `K(√a)`, that is `b = x² - a y²` for
some `x y : K`, exactly when `v_K(b)` is even. `TauCeti.exists_unramified_class` produces one. This
file shows that the unramified class is unique up to squares and identifies it through the
quadratic defect: for a nonsquare `a`, the extension `K(√a)/K` is unramified, in this norm-equation
sense, exactly when the defect exponent `δ(a)` is even, and among the unit square classes exactly
one has defect `4 𝒪[K] = 𝓂[K]^{2e}`, namely the unramified one.

The arithmetic input is the following. A unit `u` of defect exponent `2e` can be written
`u = ξ² (1 + 4m)` with `m ∈ 𝒪[K]`, and `1 + 4m` is a square as soon as the residue of `m` has the
form `t² + t`: then `1 + 4m = (1 + 2t)² + 4μ` with `μ ∈ 𝓂[K]`, and the local square theorem
applies to `1 + 4μ/(1 + 2t)²`, of depth `2e + 1`. In residue characteristic two the range of
`t ↦ t² + t` has index two in the residue field (`TauCeti.add_mem_range_sq_add_self`), so two
such units multiply to a square. In odd residue characteristic the unit square classes are
`1` and one nonsquare class, and there is nothing to prove. Conversely, if every norm from
`K(√a)` has even valuation, then the defect exponent of `a` is even, because `ξ² - a` is a norm of
valuation `δ(a)` for an optimal approximation `ξ²` of `a`.

## Main results

* `TauCeti.exists_defectExponent_mul_sq_eq_two_mul_natCastValuation`: a nonsquare of even defect
  exponent is, up to squares, a unit of defect exponent `2 v_K(2)`.
* `TauCeti.isSquare_mul_of_even_defectExponent`: the nonsquares of even defect exponent form a
  single square class.
* `TauCeti.unramified_class_iff_even_defectExponent`: the ramification dictionary, `a` is an
  unramified class exactly when `δ(a)` is even.
* `TauCeti.unramified_class_unique`: the unramified class is unique up to squares.
* `TauCeti.defectExponent_eq_two_mul_natCastValuation_iff_isSquare_mul`: a unit has defect
  `4 𝒪[K]` exactly when it lies in the unramified class.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A unit of the form `1 + 4m` is a square when the residue of `m` lies in the range of
`t ↦ t² + t`: writing `m = s² + s + μ` with `μ ∈ 𝓂[K]`, `1 + 4m = (1 + 2s)² + 4μ`, and the quotient
by `(1 + 2s)²` has depth `2 v_K(2) + 1`. -/
private theorem isSquare_of_eq_one_add_four_mul (h2 : (2 : K) ≠ 0) {w : Kˣ} {m : 𝒪[K]}
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

/-- In residue characteristic two, a unit of defect exponent `2 v_K(2)` is `ξ² (1 + 4m)` for some
`ξ ∈ Kˣ` and `m ∈ 𝒪[K]`: an optimal approximation `ξ²` of it is itself a unit. -/
private theorem exists_eq_sq_mul_one_add_four_mul (h2 : (2 : K) ≠ 0)
    (he : 0 < natCastValuation K 2 h2) {u : Kˣ} (hu : valuation K (u : K) = 1)
    (hδ : defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ)) :
    ∃ (ξ : Kˣ) (m : 𝒪[K]), (u : K) = (ξ : K) ^ 2 * (1 + 4 * m) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hsq : ¬IsSquare u := by
    rw [← defectExponent_eq_top_iff, hδ]
    exact WithTop.coe_ne_top
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hsq
  rw [hδ, WithTop.coe_inj] at hxd
  have hxv : valuation K (x : K) = valuation K (π : K) ^ (2 * natCastValuation K 2 h2) := by
    have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) x).mp hxd
    simpa only [zpow_natCast, Units.val_mk0] using h
  have hxlt : valuation K (x : K) < 1 := hxv ▸ pow_lt_one₀ zero_le hπ1 (by omega)
  have hξv : valuation K (ξ ^ 2) = 1 := by
    rw [show ξ ^ 2 = (u : K) - (x : K) by rw [hx]; ring,
      Valuation.map_sub_eq_of_lt_left _ (hu ▸ hxlt), hu]
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp at hξv
  have h40 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4 := valuation_four_eq_pow h2 hπ
  have hmem : (x : K) / (4 * ξ ^ 2) ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_div₀, map_mul, hξv, mul_one, hxv, h4, div_self]
    exact pow_ne_zero _ (by simpa using hπ.ne_zero)
  obtain ⟨m, hm⟩ : ∃ m : 𝒪[K], (m : K) = (x : K) / (4 * ξ ^ 2) := ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨Units.mk0 ξ hξ0, m, ?_⟩
  rw [Units.val_mk0, hm, hx]
  field_simp
  ring

/-- In residue characteristic two, `4 ∈ 𝓂[K]`, so every `1 + 4n` with `n ∈ 𝒪[K]` is a unit. -/
private theorem valuation_one_add_four_mul (h2 : (2 : K) ≠ 0) (he : 0 < natCastValuation K 2 h2)
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
private theorem not_mem_range_of_eq_sq_mul_one_add_four_mul (h2 : (2 : K) ≠ 0)
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

/-- **The unit classes of maximal defect.** Two units of `𝒪[K]` of defect exponent `2 v_K(2)`,
that is of defect `4 𝒪[K]`, differ by a square. -/
theorem isSquare_mul_of_defectExponent_eq_two_mul (h2 : (2 : K) ≠ 0) {u w : Kˣ}
    (hu : valuation K (u : K) = 1) (hw : valuation K (w : K) = 1)
    (hδu : defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ))
    (hδw : defectExponent w = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ)) :
    IsSquare (u * w) := by
  have hsq : ∀ {a : Kˣ}, defectExponent a = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) →
      ¬IsSquare a := fun h => by
    rw [← defectExponent_eq_top_iff, h]
    exact WithTop.coe_ne_top
  rcases Nat.eq_zero_or_pos (natCastValuation K 2 h2) with he | he
  · -- In odd residue characteristic there is a single nonsquare unit class.
    have h2' : IsUnit (2 : 𝒪[K]) := by
      simpa using (natCastValuation_eq_zero_iff K 2 h2).mp he
    have hev : ∀ a : Kˣ, valuation K (a : K) = 1 → Even (normalizedValuation K a).toAdd :=
      fun a ha => by simp [(normalizedValuation_eq_one_iff a).mpr ha]
    rcases isSquare_or_isSquare_mul_of_isUnit_two h2' (hev u hu) (hsq hδu) (hev w hw) with h | h
    · exact absurd h (hsq hδw)
    · rwa [mul_comm]
  · -- In residue characteristic two, write both units as `ξ² (1 + 4m)`.
    have : CharP 𝓀[K] 2 := by
      rw [← ringChar.eq_iff]
      exact (natCastValuation_ne_zero_iff_ringChar_eq K Nat.prime_two h2).mp he.ne'
    obtain ⟨ξ, m, hm⟩ := exists_eq_sq_mul_one_add_four_mul h2 he hu hδu
    obtain ⟨η, m', hm'⟩ := exists_eq_sq_mul_one_add_four_mul h2 he hw hδw
    -- The residue of `m + m' + 4 m m'` is the sum of the two residues, hence in the range.
    have hsum := add_mem_range_sq_add_self
      (not_mem_range_of_eq_sq_mul_one_add_four_mul h2 he (hsq hδu) hm)
      (not_mem_range_of_eq_sq_mul_one_add_four_mul h2 he (hsq hδw) hm')
    have h4 : residue 𝒪[K] (4 : 𝒪[K]) = 0 := by
      rw [map_ofNat, show (4 : 𝓀[K]) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
    have hprod : ((u * w * ((ξ * η) ^ 2)⁻¹ : Kˣ) : K) =
        1 + 4 * ((m + m' + 4 * m * m' : 𝒪[K]) : K) := by
      have h4K : ((4 : 𝒪[K]) : K) = 4 := map_ofNat 𝒪[K].subtype 4
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_mul, hm, hm']
      push_cast [h4K]
      field_simp
      ring
    have h := isSquare_of_eq_one_add_four_mul h2 hprod
      (hprod ▸ valuation_one_add_four_mul h2 he _)
      (by rw [map_add, map_add, map_mul, map_mul, h4]; simpa using hsum)
    simpa using h.mul (IsSquare.sq (ξ * η))

/-- **Normalization of an even defect exponent.** A nonsquare `a` of even defect exponent is, up
to squares, a unit of `𝒪[K]` of defect exponent `2 v_K(2)`, that is of defect `4 𝒪[K]`. -/
theorem exists_defectExponent_mul_sq_eq_two_mul_natCastValuation (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    ∃ c : Kˣ, valuation K ((a * c ^ 2 : Kˣ) : K) = 1 ∧
      defectExponent (a * c ^ 2) = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) := by
  have hsq : ¬IsSquare a := by
    rw [← defectExponent_eq_top_iff, hd]
    exact WithTop.coe_ne_top
  -- `a` has even valuation: an element of odd valuation is its own defect exponent.
  obtain ⟨k, hk⟩ : Even (normalizedValuation K a).toAdd := by
    by_contra h
    rw [Int.not_even_iff_odd] at h
    rw [defectExponent_of_odd h, WithTop.coe_inj] at hd
    exact (Int.not_even_iff_odd.mpr h) (hd ▸ hev)
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  rw [isUniformizer_def] at hϖ
  have hc : (normalizedValuation K (ϖ ^ (-k))).toAdd = -k := by
    rw [normalizedValuation_zpow_of_eq_ofAdd_one hϖ, toAdd_ofAdd]
  have hv : valuation K ((a * (ϖ ^ (-k)) ^ 2 : Kˣ) : K) = 1 := by
    rw [← normalizedValuation_eq_one_iff, ← toAdd_eq_zero, map_mul, map_pow, toAdd_mul,
      toAdd_pow, hk, hc, nsmul_eq_mul]
    push_cast
    ring
  have hnsq : ¬IsSquare (a * (ϖ ^ (-k)) ^ 2) := fun h => hsq <| by
    simpa using h.mul (IsSquare.sq (ϖ ^ (-k))⁻¹)
  refine ⟨ϖ ^ (-k), hv, ?_⟩
  -- The unit `a ϖ^{-2k}` has even defect exponent `d - 2k`, so it is not one of the odd ones.
  rcases defectExponent_eq_two_mul_natCastValuation_or_odd h2 hv hnsq with h | ⟨j, -, hj⟩
  · exact h
  · rw [defectExponent_mul_sq, hd, hc, ← WithTop.coe_add, WithTop.coe_inj] at hj
    obtain ⟨r, hr⟩ := hev
    omega

/-- **The nonsquares of even defect exponent form one square class.** Two elements of `Kˣ` whose
defect exponents are even integers differ by a square. -/
theorem isSquare_mul_of_even_defectExponent (h2 : (2 : K) ≠ 0) {a a' : Kˣ} {d d' : ℤ}
    (hd : defectExponent a = d) (hd' : defectExponent a' = d') (hev : Even d) (hev' : Even d') :
    IsSquare (a * a') := by
  obtain ⟨c, hc, hδ⟩ := exists_defectExponent_mul_sq_eq_two_mul_natCastValuation h2 hd hev
  obtain ⟨c', hc', hδ'⟩ := exists_defectExponent_mul_sq_eq_two_mul_natCastValuation h2 hd' hev'
  have h := (isSquare_mul_of_defectExponent_eq_two_mul h2 hc hc' hδ hδ').mul
    (IsSquare.sq (c * c')⁻¹)
  have heq : a * a' = a * c ^ 2 * (a' * c' ^ 2) * ((c * c')⁻¹) ^ 2 := by
    ext
    push_cast
    field_simp
  rwa [heq]

/-- If every norm from `K(√a)` has even valuation, the defect exponent of `a` is even: for an
optimal approximation `ξ²` of `a`, the norm `ξ² - a` has valuation `δ(a)`. -/
private theorem even_of_defectExponent_eq {a : Kˣ} {d : ℤ} (hd : defectExponent a = d)
    (h : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2) →
      Even (normalizedValuation K b).toAdd) :
    Even d := by
  have hsq : ¬IsSquare a := by
    rw [← defectExponent_eq_top_iff, hd]
    exact WithTop.coe_ne_top
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hsq
  rw [hd, WithTop.coe_inj] at hxd
  have hneg := h (-x) ⟨ξ, 1, by rw [Units.val_neg, hx]; ring⟩
  rwa [← neg_one_mul, map_mul, (normalizedValuation_eq_one_iff (-1)).mpr (by simp), one_mul,
    hxd] at hneg

/-- **The ramification dictionary.** For `a ∈ Kˣ` of finite defect exponent `δ(a) = d`, that is
for a nonsquare `a`, the extension `K(√a)/K` is unramified in norm-equation form, meaning that
`b ∈ Kˣ` is a norm `x² - a y²` exactly when `v_K(b)` is even, if and only if `d` is even. -/
theorem unramified_class_iff_even_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) :
    (∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) ↔ Even d := by
  refine ⟨fun h => even_of_defectExponent_eq hd fun b hb => (h b).mp hb, fun hev => ?_⟩
  obtain ⟨Δ, hΔsq, -, hΔ⟩ := exists_unramified_class h2
  obtain ⟨dΔ, hdΔ⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp hΔsq)
  exact unramified_class_of_isSquare_mul (isSquare_mul_of_even_defectExponent h2 hd hdΔ.symm hev
    (even_of_defectExponent_eq hdΔ.symm fun b hb => (hΔ b).mp hb)) hΔ

/-- **The unramified class is unique.** If both `u` and `u'` have the elements of even valuation
as their norms, then `u` and `u'` differ by a square. -/
theorem unramified_class_unique (h2 : (2 : K) ≠ 0) (u u' : Kˣ)
    (hu : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - u * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hu' : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - u' * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    IsSquare (u * u') := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    (mt defectExponent_eq_top_iff.mp (not_isSquare_of_unramified_class h2 hu))
  obtain ⟨d', hd'⟩ := WithTop.ne_top_iff_exists.mp
    (mt defectExponent_eq_top_iff.mp (not_isSquare_of_unramified_class h2 hu'))
  exact isSquare_mul_of_even_defectExponent h2 hd.symm hd'.symm
    ((unramified_class_iff_even_defectExponent h2 hd.symm).mp hu)
    ((unramified_class_iff_even_defectExponent h2 hd'.symm).mp hu')

/-- **The unit class of defect `4 𝒪[K]`.** Among the units of `𝒪[K]`, the ones of defect
exponent `2 v_K(2)`, that is of defect `4 𝒪[K]`, are exactly the ones in the square class of the
unramified class `Δ`. -/
theorem defectExponent_eq_two_mul_natCastValuation_iff_isSquare_mul (h2 : (2 : K) ≠ 0)
    {Δ u : Kˣ} (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hu : valuation K (u : K) = 1) :
    defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) ↔ IsSquare (u * Δ) := by
  obtain ⟨dΔ, hdΔ⟩ := WithTop.ne_top_iff_exists.mp
    (mt defectExponent_eq_top_iff.mp (not_isSquare_of_unramified_class h2 hΔ))
  refine ⟨fun h => isSquare_mul_of_even_defectExponent h2 h hdΔ.symm
    ⟨natCastValuation K 2 h2, by push_cast; ring⟩
    ((unramified_class_iff_even_defectExponent h2 hdΔ.symm).mp hΔ), fun h => ?_⟩
  have hu' := unramified_class_of_isSquare_mul h hΔ
  have hsq := not_isSquare_of_unramified_class h2 hu'
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp hsq)
  obtain ⟨r, hr⟩ := (unramified_class_iff_even_defectExponent h2 hd.symm).mp hu'
  rcases defectExponent_eq_two_mul_natCastValuation_or_odd h2 hu hsq with h' | ⟨k, -, hk⟩
  · exact h'
  · rw [← hd, WithTop.coe_inj] at hk
    omega

end TauCeti
