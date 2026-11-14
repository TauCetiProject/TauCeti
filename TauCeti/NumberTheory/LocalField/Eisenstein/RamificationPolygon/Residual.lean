/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.RamificationPolygon.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Analysis.Convex.Sequence.Rationality

/-!
# Residual polynomials of segments of the ramification polygon

Let `φ ∈ 𝒪[K][X]` be a polynomial of degree `n` and `α` an element of a nonarchimedean local field
`L` extending `K`, with ramification polynomial `ρ = ramificationPolynomial φ α`. Following Ore, to
a segment `[k, k + l]` of `(ramificationPolynomial φ α).newtonPolygon (realAddValuation L)` of
slope `-h / m` in lowest terms (`0 < m`, `h.Coprime m`) one attaches the *residual polynomial*

`A(X) = ∑_{j = 0}^{l / m} \overline{ρ_{j m + k} α^{j h - v_L(ρ_k)}} X ^ j ∈ 𝓀[L][X]`,

where `v_L(ρ_k) = WithZero.log (normalizedValuationWithZero L ρ_k)` and the bar denotes
`IsLocalRing.residue 𝒪[L]`.

This file defines `TauCeti.residualPolynomial` and establishes its structural properties on polygon
faces:

* Denominator divisibility (`TauCeti.dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial`): on
  any finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m`, `m ∣ l`.
* Integrality and contact (`TauCeti.mem_integer_mul_zpow_of_isFiniteFace` and
  `TauCeti.coeff_residualPolynomial_ne_zero_iff`): when `α` is a uniformizer of `L`, every
  rescaled coefficient `ρ_{j m + k} α^{j h - v_L(ρ_k)}` lies in `𝒪[L]`, and `A.coeff j ≠ 0` if and
  only if `j ≤ l / m` and the point `(j m + k, v_L(ρ_{j m + k}))` lies on the face's supporting
  line.
* Degree and endpoints (`TauCeti.coeff_zero_residualPolynomial_ne_zero`,
  `TauCeti.coeff_div_residualPolynomial_ne_zero`, `TauCeti.natDegree_residualPolynomial`, and
  `TauCeti.coeff_zero_residualPolynomial_eq_leadingCoeff`): `A(0) ≠ 0`, `A` has degree `l / m` with
  nonzero leading coefficient, and the constant coefficient of a segment starting at `k + l₁`
  equals the leading coefficient of the preceding segment `[k, k + l₁]` (so in the right-to-left
  segment ordering from `n` down to `1`, each constant term equals the next segment's leading
  coefficient).
* Additivity on wild segments (`TauCeti.exists_eq_pow_of_coeff_residualPolynomial_ne_zero` and
  `TauCeti.aeval_add_X_pow_mul_comp_residualPolynomial`): for a monic Eisenstein generator `(φ, α)`
  and positive ram (`0 < h`), every nonzero coefficient of `A` sits at an index `j` where
  `k + j * m` is a power of `ringChar 𝓀[K]`, so `X ^ k * A.comp (X ^ m)` is an additive polynomial
  over every commutative `𝓀[L]`-algebra.
* The tame segment (`TauCeti.coeff_tame_residualPolynomial` and
  `TauCeti.coeff_X_pow_mul_tame_residualPolynomial`): on `[p ^ w, n]` (`w = padicValNat p n`,
  `h = 0`, `m = 1`), `X ^ (p ^ w) * A` agrees coefficientwise with the reduction of `ρ` modulo
  `𝓂[L]`.

## Main definitions

* `TauCeti.residualPolynomial`: Ore's residual polynomial in `𝓀[L][X]` attached to `(φ, α)` and
  segment parameters `(k, l, h, m)`.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Mathematische Zeitschrift 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, International Journal of Number Theory 8 (2012), 1401–1424, §3.
* S. Pauli and C. Sinclair, *Enumerating extensions of `(π)`-adic fields with given invariants*,
  International Journal of Number Theory 13 (2017), 2007–2038, §4.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField WithZero

namespace TauCeti

section GeneralFace

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]

open Classical in
/-- Ore's residual polynomial of the segment of the ramification polygon with left abscissa `k`,
width `l`, and slope `-h / m` in lowest terms, with respect to `(φ, α)`:
`A(X) = ∑_{j = 0}^{l / m} \overline{ρ_{j m + k} α^{j h - v_L(ρ_k)}} X ^ j ∈ 𝓀[L][X]`.
Terms outside `𝒪[L]` are mapped to `0`; on any finite face of slope `-h / m` with `0 < m` and a
uniformizer `α`, every term lies in `𝒪[L]` (`mem_integer_mul_zpow_of_isFiniteFace`). -/
def residualPolynomial (φ : 𝒪[K][X]) (α : L) (k l h m : ℕ) : 𝓀[L][X] :=
  ∑ j ∈ Finset.range (l / m + 1),
    C (let x : L := (ramificationPolynomial φ α).coeff (j * m + k) *
          α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
            ((ramificationPolynomial φ α).coeff k)))
        if hx : x ∈ 𝒪[L] then residue 𝒪[L] ⟨x, hx⟩ else 0) * X ^ j

open Classical in
/-- Definitional unfolding of `residualPolynomial`. -/
theorem residualPolynomial_def (φ : 𝒪[K][X]) (α : L) (k l h m : ℕ) :
    residualPolynomial φ α k l h m =
      ∑ j ∈ Finset.range (l / m + 1),
        C (let x : L := (ramificationPolynomial φ α).coeff (j * m + k) *
              α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
                ((ramificationPolynomial φ α).coeff k)))
            if hx : x ∈ 𝒪[L] then residue 𝒪[L] ⟨x, hx⟩ else 0) * X ^ j := by
  rfl

open Classical in
/-- Explicit `j`-th coefficient of `residualPolynomial φ α k l h m`. -/
theorem coeff_residualPolynomial (φ : 𝒪[K][X]) (α : L) (k l h m j : ℕ) :
    (residualPolynomial φ α k l h m).coeff j =
      if j ≤ l / m then
        let x : L := (ramificationPolynomial φ α).coeff (j * m + k) *
          α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
            ((ramificationPolynomial φ α).coeff k)))
        if hx : x ∈ 𝒪[L] then residue 𝒪[L] ⟨x, hx⟩ else 0
      else 0 := by
  rw [residualPolynomial_def, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

/-- Above `l / m`, the coefficients of `residualPolynomial φ α k l h m` vanish. -/
theorem coeff_residualPolynomial_eq_zero_of_lt (φ : 𝒪[K][X]) (α : L) (k l h m : ℕ) {j : ℕ}
    (hj : l / m < j) :
    (residualPolynomial φ α k l h m).coeff j = 0 := by
  simp [coeff_residualPolynomial, not_le.mpr hj]

/-- When `j ≤ l / m` and the rescaled `j`-th coefficient lies in `𝒪[L]`, its residue in `𝓀[L]` is
`(residualPolynomial φ α k l h m).coeff j`. -/
theorem coeff_residualPolynomial_of_mem_integer {φ : 𝒪[K][X]} {α : L} {k l h m j : ℕ}
    (hj : j ≤ l / m)
    (hx : (ramificationPolynomial φ α).coeff (j * m + k) *
      α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L]) :
    (residualPolynomial φ α k l h m).coeff j =
      residue 𝒪[L] ⟨(ramificationPolynomial φ α).coeff (j * m + k) *
        α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k))), hx⟩ := by
  simp [coeff_residualPolynomial, hj, hx]

/-- The degree of `residualPolynomial φ α k l h m` is at most `l / m`. -/
theorem natDegree_residualPolynomial_le (φ : 𝒪[K][X]) (α : L) (k l h m : ℕ) :
    (residualPolynomial φ α k l h m).natDegree ≤ l / m :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hj ↦
    coeff_residualPolynomial_eq_zero_of_lt φ α k l h m hj

/-- On any finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` (`0 < m`,
`h.Coprime m`) of the ramification polygon, the denominator `m` divides the width `l`. -/
theorem dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial {φ : 𝒪[K][X]} {α : L}
    {k l h m : ℕ} (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    m ∣ l := by
  have henv := (ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  obtain ⟨q, hq, hdvd⟩ := henv.exists_rat_eq_and_den_dvd_of_isFiniteFace
    (fun _ hi ↦ exists_int_realAddValuation (realAddValuation_eq_top_iff.not.mp hi))
    hface (Nat.lt_add_of_pos_right hl)
  have hq_eq : q = (-(h : ℤ) : ℚ) / (m : ℤ) := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hq
  have hden : q.den = m := by
    apply Int.ofNat.inj
    rw [hq_eq]
    exact Rat.den_div_eq_of_coprime (Int.natCast_pos.mpr hm) (by simpa using hcop)
  simpa [hden] using hdvd

private theorem realAddValuation_mul_zpow_of_isFiniteFace {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l))
    (j : ℕ) :
    0 ≤ realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k) *
          α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
            ((ramificationPolynomial φ α).coeff k)))) ∧
      (realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k) *
          α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
            ((ramificationPolynomial φ α).coeff k)))) = 0 ↔
        realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k)) =
          (((WithZero.log (normalizedValuationWithZero L
            ((ramificationPolynomial φ α).coeff k)) - (j * h : ℤ) : ℤ) : ℝ) : WithTop ℝ)) := by
  set ρ := ramificationPolynomial φ α
  set N := ρ.newtonPolygon (realAddValuation L)
  set v₀ : ℤ := WithZero.log (normalizedValuationWithZero L (ρ.coeff k))
  set e : ℤ := (j * h : ℤ) - v₀
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hNk : N k = realAddValuation L (ρ.coeff k) := henv.eq_left_of_isFiniteFace hface
  have huntop : (N k).untop₀ = (v₀ : ℝ) := by
    rw [hNk, untop₀_realAddValuation]
  have hsupp : IsSupportingLine N (-(h : ℝ) / m) ((N k).untop₀ - (-(h : ℝ) / m) * k) :=
    hface.isSupportingLine_untop₀_sub ⟨le_rfl, hface.left_le_right⟩
  have hbound : (((N k).untop₀ - (-(h : ℝ) / m) * k +
      (-(h : ℝ) / m) * (j * m + k : ℕ) : ℝ) : WithTop ℝ) ≤
      realAddValuation L (ρ.coeff (j * m + k)) :=
    (isSupportingLine_iff_forall.mp hsupp (j * m + k)).trans (henv.le (j * m + k))
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hlin : (N k).untop₀ - (-(h : ℝ) / m) * k + (-(h : ℝ) / m) * (j * m + k : ℕ) =
      ((v₀ - (j * h : ℤ) : ℤ) : ℝ) := by
    rw [huntop]
    push_cast
    field_simp [hm0]
    ring
  rw [hlin] at hbound
  have hzpow : realAddValuation L (α ^ e) = ((e : ℝ) : WithTop ℝ) := by
    rw [realAddValuation_zpow_of_ne_zero hα0 e, hα, WithTop.untop₀_one, mul_one]
  rw [(realAddValuation L).map_mul, hzpow]
  cases hv : realAddValuation L (ρ.coeff (j * m + k)) with
  | top =>
    exact ⟨le_top, ⟨fun h0 ↦ absurd (top_add (a := ((e : ℝ) : WithTop ℝ)) ▸ h0) WithTop.top_ne_coe,
      fun h0 ↦ absurd h0 WithTop.top_ne_coe⟩⟩
  | coe r =>
    rw [hv, WithTop.coe_le_coe] at hbound
    simp only [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_eq_coe, e]
    push_cast at hbound ⊢
    exact ⟨by linarith, ⟨fun h0 ↦ by linarith, fun h0 ↦ by linarith⟩⟩

/-- On any finite face `[k, k + l]` of slope `-h / m` (`0 < m`) of the ramification polygon with a
uniformizer `α`, every rescaled term `ρ_{j m + k} α^{j h - v_L(ρ_k)}` lies in `𝒪[L]`. -/
theorem mem_integer_mul_zpow_of_isFiniteFace {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l))
    (j : ℕ) :
    (ramificationPolynomial φ α).coeff (j * m + k) *
      α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L] :=
  mem_integer_iff_realAddValuation_nonneg.mpr
    (realAddValuation_mul_zpow_of_isFiniteFace hm hα hface j).1

/-- On a finite face `[k, k + l]` of slope `-h / m` (`0 < m`) with a uniformizer `α`, the `j`-th
coefficient of `residualPolynomial φ α k l h m` is nonzero if and only if `j ≤ l / m` and the
coefficient height `realAddValuation L (ρ.coeff (j * m + k))` lies on the face's supporting line,
taking the value `v_L(ρ_k) - j * h`. -/
theorem coeff_residualPolynomial_ne_zero_iff {φ : 𝒪[K][X]} {α : L} {k l h m j : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).coeff j ≠ 0 ↔
      j ≤ l / m ∧ realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k)) =
        (((WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k)) - (j * h : ℤ) : ℤ) : ℝ) : WithTop ℝ) := by
  rcases le_or_gt j (l / m) with hj | hj
  · have hx := mem_integer_mul_zpow_of_isFiniteFace hm hα hface j
    obtain ⟨h0, hiff⟩ := realAddValuation_mul_zpow_of_isFiniteFace hm hα hface j
    have hle0 : realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k) *
        α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k)))) ≤ 0 ↔
      realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k) *
        α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k)))) = 0 :=
      ⟨fun h ↦ le_antisymm h h0, fun h ↦ h.le⟩
    rw [coeff_residualPolynomial_of_mem_integer hj hx, ne_eq, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_iff_realAddValuation_pos, Subtype.coe_mk, not_lt, hle0, hiff]
    exact ⟨fun h ↦ ⟨hj, h⟩, fun h ↦ h.2⟩
  · rw [coeff_residualPolynomial_eq_zero_of_lt _ _ _ _ _ _ hj]
    exact ⟨fun h ↦ absurd rfl h, fun h ↦ absurd h.1 (not_le.mpr hj)⟩

/-- On any finite face starting at `k`, the constant coefficient of `residualPolynomial φ α k l h m`
is nonzero whenever `α` is a uniformizer of `L`. -/
theorem coeff_zero_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hα : realAddValuation L α = 1) {σ : ℝ}
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      σ k (k + l)) :
    (residualPolynomial φ α k l h m).coeff 0 ≠ 0 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  set c := (ramificationPolynomial φ α).coeff k
  have henv := (ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hc_top : realAddValuation L c ≠ ⊤ :=
    henv.eq_left_of_isFiniteFace hface ▸ hface.left_ne_top
  have hc0 : c ≠ 0 := realAddValuation_eq_top_iff.not.mp hc_top
  set v₀ : ℤ := WithZero.log (normalizedValuationWithZero L c)
  have hval : realAddValuation L (c * α ^ (-v₀)) = 0 := by
    rw [(realAddValuation L).map_mul, realAddValuation_of_ne_zero hc0,
      realAddValuation_zpow_of_ne_zero hα0 (-v₀), hα, WithTop.untop₀_one, mul_one,
      ← WithTop.coe_add]
    simp [v₀]
  have hx : c * α ^ (-v₀) ∈ 𝒪[L] := mem_integer_iff_realAddValuation_nonneg.mpr hval.ge
  have hres : residue 𝒪[L] ⟨c * α ^ (-v₀), hx⟩ ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_realAddValuation_pos,
      Subtype.coe_mk, hval]
    exact lt_irrefl 0
  have hx0 : (ramificationPolynomial φ α).coeff (0 * m + k) *
      α ^ ((0 * h : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L] := by
    simpa [c, v₀] using hx
  rw [coeff_residualPolynomial_of_mem_integer (Nat.zero_le _) hx0]
  convert hres using 2
  ext
  simp [c, v₀]

private theorem realAddValuation_coeff_right_of_isFiniteFace {φ : 𝒪[K][X]} {α : L}
    {k l h m : ℕ} (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    realAddValuation L ((ramificationPolynomial φ α).coeff (k + l)) =
      (((WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k)) -
          ((l / m : ℕ) * (h : ℤ)) : ℤ) : ℝ) : WithTop ℝ) := by
  have hdvd : m ∣ l := dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl hm hcop hface
  set q := l / m
  have hmul : q * m = l := Nat.div_mul_cancel hdvd
  set ρ := ramificationPolynomial φ α
  set N := ρ.newtonPolygon (realAddValuation L)
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  obtain ⟨c, _, hset⟩ := hface.exists_intercept
  have hk_mem : k ∈ supportingFace N (-(h : ℝ) / m) c :=
    hset.symm.subset ⟨le_rfl, hface.left_le_right⟩
  have hkl_mem : k + l ∈ supportingFace N (-(h : ℝ) / m) c :=
    hset.symm.subset ⟨hface.left_le_right, le_rfl⟩
  have hk_val : N k = ((c + (-(h : ℝ) / m) * k : ℝ) : WithTop ℝ) :=
    mem_supportingFace.mp hk_mem
  have hkl_val : N (k + l) = ((c + (-(h : ℝ) / m) * (k + q * m : ℕ) : ℝ) : WithTop ℝ) := by
    simpa only [hmul] using mem_supportingFace.mp hkl_mem
  have hc_eq : c = ((WithZero.log (normalizedValuationWithZero L (ρ.coeff k)) : ℤ) : ℝ) -
      (-(h : ℝ) / m) * k := by
    have h1 : (N k).untop₀ = c + (-(h : ℝ) / m) * k := by
      rw [hk_val, WithTop.untop₀_coe]
    dsimp only [N] at h1
    rw [henv.eq_left_of_isFiniteFace hface, untop₀_realAddValuation] at h1
    linarith
  dsimp only [N] at hkl_val
  rw [← henv.eq_right_of_isFiniteFace hface, hkl_val, WithTop.coe_eq_coe, hc_eq]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp [hm0]
  ring

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m`, the `(l / m)`-th
coefficient of `residualPolynomial φ α k l h m` is nonzero whenever `α` is a uniformizer of `L`. -/
theorem coeff_div_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).coeff (l / m) ≠ 0 := by
  have hdvd : m ∣ l := dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl hm hcop hface
  have hidx : (l / m) * m + k = k + l := by rw [Nat.div_mul_cancel hdvd, add_comm]
  rw [coeff_residualPolynomial_ne_zero_iff hm hα hface]
  exact ⟨le_rfl, hidx.symm ▸ realAddValuation_coeff_right_of_isFiniteFace hl hm hcop hface⟩

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` with a
uniformizer `α`, the degree of `residualPolynomial φ α k l h m` is `l / m`. -/
theorem natDegree_residualPolynomial {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).natDegree = l / m :=
  le_antisymm (natDegree_residualPolynomial_le φ α k l h m)
    (le_natDegree_of_ne_zero (coeff_div_residualPolynomial_ne_zero hl hm hcop hα hface))

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` with a
uniformizer `α`, the leading coefficient of `residualPolynomial φ α k l h m` is nonzero. -/
theorem leadingCoeff_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).leadingCoeff ≠ 0 := by
  rw [Polynomial.leadingCoeff, natDegree_residualPolynomial hl hm hcop hα hface]
  exact coeff_div_residualPolynomial_ne_zero hl hm hcop hα hface

/-- **Matching of adjacent residual polynomials.** If `[k, k + l₁]` is a finite face of positive
width `l₁` and reduced slope `-h₁ / m₁` with a uniformizer `α`, then for any segment parameters
`(l₂, h₂, m₂)` starting at `k + l₁`, the constant coefficient of
`residualPolynomial φ α (k + l₁) l₂ h₂ m₂` equals the leading coefficient of
`residualPolynomial φ α k l₁ h₁ m₁`. In the right-to-left ordering of segments from `n` down to `1`,
this says that each segment's constant term equals the next segment's leading coefficient. -/
theorem coeff_zero_residualPolynomial_eq_leadingCoeff {φ : 𝒪[K][X]} {α : L} {k l₁ h₁ m₁ : ℕ}
    (hl₁ : 0 < l₁) (hm₁ : 0 < m₁) (hcop₁ : h₁.Coprime m₁) (hα : realAddValuation L α = 1)
    (hface₁ : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h₁ : ℝ) / m₁) k (k + l₁))
    (l₂ h₂ m₂ : ℕ) :
    (residualPolynomial φ α (k + l₁) l₂ h₂ m₂).coeff 0 =
      (residualPolynomial φ α k l₁ h₁ m₁).leadingCoeff := by
  have hdvd : m₁ ∣ l₁ :=
    dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl₁ hm₁ hcop₁ hface₁
  have hidx : (l₁ / m₁) * m₁ + k = k + l₁ := by rw [Nat.div_mul_cancel hdvd, add_comm]
  have hval := realAddValuation_coeff_right_of_isFiniteFace hl₁ hm₁ hcop₁ hface₁
  have hlog : WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff (k + l₁))) =
      WithZero.log (normalizedValuationWithZero L ((ramificationPolynomial φ α).coeff k)) -
        ((l₁ / m₁ : ℕ) * (h₁ : ℤ)) := by
    have huntop := congrArg WithTop.untop₀ hval
    rw [untop₀_realAddValuation, WithTop.untop₀_coe] at huntop
    exact Int.cast_injective huntop
  have hx_eq : (ramificationPolynomial φ α).coeff (0 * m₂ + (k + l₁)) *
        α ^ (((0 : ℕ) * (h₂ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff (k + l₁)))) =
      (ramificationPolynomial φ α).coeff ((l₁ / m₁) * m₁ + k) *
        α ^ (((l₁ / m₁ : ℕ) * (h₁ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k))) := by
    have hexp : ((0 : ℕ) * (h₂ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff (k + l₁))) =
        ((l₁ / m₁ : ℕ) * (h₁ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k)) := by
      omega
    rw [zero_mul, zero_add, hidx, hexp]
  have hx₁ := mem_integer_mul_zpow_of_isFiniteFace hm₁ hα hface₁ (l₁ / m₁)
  have hx₀ := hx_eq.symm ▸ hx₁
  rw [Polynomial.leadingCoeff, natDegree_residualPolynomial hl₁ hm₁ hcop₁ hα hface₁,
    coeff_residualPolynomial_of_mem_integer (Nat.zero_le _) hx₀,
    coeff_residualPolynomial_of_mem_integer le_rfl hx₁]
  congr 1
  exact Subtype.ext hx_eq

end GeneralFace

section Eisenstein

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Additivity exponents on wild faces.** Let `[k, k + l]` be a finite face of slope `-h / m` of
the ramification polygon of a monic Eisenstein generator `(φ, α)` with `0 < h` and `0 < m` (so the
corresponding ram `h / m` is strictly positive). Then every nonzero coefficient of
`residualPolynomial φ α k l h m` sits at an index `j` such that `k + j * m` is a power of
`ringChar 𝓀[K]`; equivalently, `X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)` has only
`p`-power exponents. -/
theorem exists_eq_pow_of_coeff_residualPolynomial_ne_zero {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {k l h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l))
    {j : ℕ} (hj : (residualPolynomial φ α k l h m).coeff j ≠ 0) :
    ∃ i : ℕ, k + j * m = (ringChar 𝓀[K]) ^ i := by
  obtain ⟨-, -, -, hα, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  obtain ⟨-, hjval⟩ := (coeff_residualPolynomial_ne_zero_iff hm hα hface).mp hj
  set ρ := ramificationPolynomial φ α
  set N := ρ.newtonPolygon (realAddValuation L)
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  set c : ℝ := (N k).untop₀ - (-(h : ℝ) / m) * k
  have hcN : IsSupportingLine N (-(h : ℝ) / m) c :=
    hface.isSupportingLine_untop₀_sub ⟨le_rfl, hface.left_le_right⟩
  have hca : IsSupportingLine (fun i ↦ realAddValuation L (ρ.coeff i)) (-(h : ℝ) / m) c :=
    isSupportingLine_iff_forall.mpr fun i ↦
      (isSupportingLine_iff_forall.mp hcN i).trans (henv.le i)
  have hneg : -(h : ℝ) / m < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr (Nat.cast_pos.mpr hh)) (Nat.cast_pos.mpr hm)
  have hmem : j * m + k ∈
      supportingFace (fun i ↦ realAddValuation L (ρ.coeff i)) (-(h : ℝ) / m) c := by
    rw [mem_supportingFace, hjval, WithTop.coe_eq_coe]
    have huntop : (N k).untop₀ =
        ((WithZero.log (normalizedValuationWithZero L (ρ.coeff k)) : ℤ) : ℝ) := by
      dsimp only [N]
      rw [henv.eq_left_of_isFiniteFace hface, untop₀_realAddValuation]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    simp only [c, huntop]
    push_cast
    field_simp [hm0]
    ring
  obtain ⟨i, hi⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen hneg hca hmem
  exact ⟨i, (add_comm k (j * m)).trans hi⟩

/-- **Additivity of the expanded residual polynomial on wild faces.** Under the hypotheses of
`exists_eq_pow_of_coeff_residualPolynomial_ne_zero`, the polynomial
`X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)` evaluates additively on every commutative
`𝓀[L]`-algebra `B`. -/
theorem aeval_add_X_pow_mul_comp_residualPolynomial
    {B : Type*} [CommSemiring B] [Algebra 𝓀[L] B]
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {k l h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l))
    (x y : B) :
    aeval (x + y) (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) =
      aeval x (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) +
        aeval y (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) := by
  set A := residualPolynomial φ α k l h m
  have hp : (ringChar 𝓀[K]).Prime := CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])
  have hsum_eq : A = ∑ j ∈ Finset.range (l / m + 1), monomial j (A.coeff j) :=
    A.as_sum_range' (l / m + 1) (Nat.lt_succ_of_le (natDegree_residualPolynomial_le φ α k l h m))
  have heval (z : B) : aeval z (X ^ k * A.comp (X ^ m)) =
      ∑ j ∈ Finset.range (l / m + 1), algebraMap 𝓀[L] B (A.coeff j) * z ^ (k + j * m) := by
    rw [map_mul, map_pow, aeval_X, aeval_comp, aeval_X_pow]
    conv_lhs => rw [hsum_eq]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [aeval_monomial, ← pow_mul, mul_comm m j, mul_left_comm (z ^ k), ← pow_add]
  rw [heval, heval, heval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne (A.coeff j) 0 with hj0 | hj
  · simp [hj0]
  · obtain ⟨i, hi⟩ :=
      exists_eq_pow_of_coeff_residualPolynomial_ne_zero hmonic hφ hroot hgen hh hm hface hj
    rw [hi, ← mul_add]
    congr 1
    rcases subsingleton_or_nontrivial B with _ | _
    · exact Subsingleton.elim _ _
    · have : Fact (ringChar 𝓀[K]).Prime := ⟨hp⟩
      have : CharP 𝓀[L] (ringChar 𝓀[K]) :=
        Algebra.ringChar_eq 𝓀[K] 𝓀[L] ▸ ringChar.charP 𝓀[L]
      have : CharP B (ringChar 𝓀[K]) :=
        charP_of_injective_algebraMap (algebraMap 𝓀[L] B).injective (ringChar 𝓀[K])
      exact add_pow_char_pow x y (ringChar 𝓀[K]) i

/-- **Tame residual polynomial coefficients.** On the tame segment
`[(ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree, φ.natDegree]` (`h = 0`, `m = 1`), the
`j`-th coefficient of the residual polynomial for `j ≤ n - p ^ w` is the residue of
`(ramificationPolynomial φ α).coeff (p ^ w + j)` in `𝓀[L]`. -/
theorem coeff_tame_residualPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {j : ℕ}
    (hj : j ≤ φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) :
    (residualPolynomial φ α
        ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)
        (φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) 0 1).coeff j =
      residue 𝒪[L] ⟨(ramificationPolynomial φ α).coeff
          ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree + j),
        coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen _⟩ := by
  set k := (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree
  have hval0 : realAddValuation L ((ramificationPolynomial φ α).coeff k) = 0 :=
    realAddValuation_coeff_pow_padicValNat_ramificationPolynomial hmonic hφ hroot hgen
  have hlog0 : WithZero.log (normalizedValuationWithZero L
      ((ramificationPolynomial φ α).coeff k)) = 0 := by
    have h := congrArg WithTop.untop₀ hval0
    rw [untop₀_realAddValuation, WithTop.untop₀_zero] at h
    exact_mod_cast h
  have hx : (ramificationPolynomial φ α).coeff (j * 1 + k) *
      α ^ ((j * 0 : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L] := by
    simpa [hlog0, add_comm] using
      coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen (k + j)
  rw [coeff_residualPolynomial_of_mem_integer (by simpa using hj) hx]
  congr 1
  ext
  simp [hlog0, add_comm]

/-- **Congruence of the tame residual polynomial with `ρ` modulo `𝓂[L]`.** Multiplying the tame
residual polynomial by `X ^ (p ^ w)` recovers the coefficientwise reduction of
`ramificationPolynomial φ α` modulo `𝓂[L]`. -/
theorem coeff_X_pow_mul_tame_residualPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (j : ℕ) :
    (X ^ ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) *
      residualPolynomial φ α
        ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)
        (φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) 0 1).coeff j =
      residue 𝒪[L] ⟨(ramificationPolynomial φ α).coeff j,
        coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen j⟩ := by
  obtain ⟨-, -, -, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set n := φ.natDegree
  have hnpos : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  set w := padicValNat p n
  have hfac : n.factorization p = w := (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  have hpwn : p ^ w ≤ n := hfac ▸ Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p)
  rw [coeff_X_pow_mul']
  split_ifs with hle
  · rcases le_or_gt j n with hjn | hgt
    · have hsub : j - p ^ w ≤ n - p ^ w := Nat.sub_le_sub_right hjn _
      rw [coeff_tame_residualPolynomial hmonic hφ hroot hgen hsub]
      congr 1
      ext
      dsimp only [p, w, n] at hle ⊢
      rw [Nat.add_sub_of_le hle]
    · have hsub : (n - p ^ w) / 1 < j - p ^ w := by omega
      rw [coeff_residualPolynomial_eq_zero_of_lt _ _ _ _ _ _ hsub]
      symm
      rw [IsLocalRing.residue_eq_zero_iff]
      have h0 : (⟨(ramificationPolynomial φ α).coeff j,
          coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen j⟩ : 𝒪[L]) = 0 := by
        ext
        exact coeff_ramificationPolynomial_eq_zero_of_lt hgt
      rw [h0]
      exact Ideal.zero_mem _
  · symm
    rw [IsLocalRing.residue_eq_zero_iff]
    rcases eq_or_ne j 0 with rfl | hj0
    · have h0 : (⟨(ramificationPolynomial φ α).coeff 0,
          coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen 0⟩ : 𝒪[L]) = 0 := by
        ext
        exact coeff_zero_ramificationPolynomial_of_isRoot hroot
      rw [h0]
      exact Ideal.zero_mem _
    · exact mem_maximalIdeal_iff_one_le_realAddValuation.mpr
        (one_le_realAddValuation_coeff_of_lt_pow_padicValNat hmonic hφ hroot hgen
          (Nat.one_le_iff_ne_zero.mpr hj0) (not_le.mp hle))

end Eisenstein

end TauCeti
