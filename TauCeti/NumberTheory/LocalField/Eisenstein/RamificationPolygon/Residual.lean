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

To a segment `[k, k + l]` of `(ramificationPolynomial φ α).newtonPolygon (realAddValuation L)` of
reduced slope `-h / m` (`0 < m`, `h.Coprime m`), Ore attaches the *residual polynomial*
`A(X) = ∑_{j = 0}^{l / m} \overline{ρ_{j m + k} α^{j h - v_L(ρ_k)}} X ^ j ∈ 𝓀[L][X]`.

## Main definitions

* `TauCeti.residualPolynomial`: Ore's residual polynomial in `𝓀[L][X]`.

## Main results

* `TauCeti.dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial`,
  `TauCeti.mem_integer_mul_zpow_of_isFiniteFace`, `TauCeti.coeff_residualPolynomial_ne_zero_iff`,
  `TauCeti.natDegree_residualPolynomial` and
  `TauCeti.coeff_zero_residualPolynomial_eq_leadingCoeff`: divisibility `m ∣ l`, integrality,
  contact characterization, degree `l / m`, and segment matching.
* `TauCeti.exists_eq_pow_of_coeff_residualPolynomial_ne_zero`,
  `TauCeti.aeval_add_X_pow_mul_comp_residualPolynomial`, `TauCeti.coeff_tame_residualPolynomial`
  and `TauCeti.coeff_X_pow_mul_tame_residualPolynomial`: wild additivity and tame reduction.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012), 1401–1424, §3.
* S. Pauli and C. Sinclair, *Enumerating extensions of `(π)`-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017), 2007–2038, §4.
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
width `l`, and slope `-h / m` in lowest terms, with respect to `(φ, α)`. -/
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
            if hx : x ∈ 𝒪[L] then residue 𝒪[L] ⟨x, hx⟩ else 0) * X ^ j := by rfl

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
    (hj : l / m < j) : (residualPolynomial φ α k l h m).coeff j = 0 := by
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
  natDegree_le_iff_coeff_eq_zero.mpr fun _ ↦ coeff_residualPolynomial_eq_zero_of_lt φ α k l h m

/-- On any finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` (`0 < m`,
`h.Coprime m`), `m ∣ l`. -/
theorem dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial {φ : 𝒪[K][X]} {α : L}
    {k l h m : ℕ} (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) : m ∣ l := by
  obtain ⟨q, hq, hdvd⟩ :=
    ((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).exists_rat_eq_and_den_dvd_of_isFiniteFace
      (fun _ hi ↦ exists_int_realAddValuation (realAddValuation_eq_top_iff.not.mp hi))
      hface (Nat.lt_add_of_pos_right hl)
  have hq_eq : q = (-(h : ℤ) : ℚ) / (m : ℤ) :=
    Rat.cast_injective (α := ℝ) (by push_cast; exact hq)
  have hden : q.den = m := Int.ofNat.inj
    (hq_eq ▸ Rat.den_div_eq_of_coprime (Int.natCast_pos.mpr hm) (by simpa using hcop))
  simpa [hden] using hdvd

private theorem realAddValuation_mul_zpow_of_isFiniteFace {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) (j : ℕ) :
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
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hbound := (isSupportingLine_iff_forall.mp
    (hface.isSupportingLine_untop₀_sub ⟨le_rfl, hface.left_le_right⟩) (j * m + k)).trans
    (henv.le (j * m + k))
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show (N k).untop₀ - (-(h : ℝ) / m) * k + (-(h : ℝ) / m) * (j * m + k : ℕ) =
      ((v₀ - (j * h : ℤ) : ℤ) : ℝ) by
    dsimp only [N]; rw [henv.eq_left_of_isFiniteFace hface, untop₀_realAddValuation]
    push_cast; field_simp [hm0]; ring] at hbound
  rw [(realAddValuation L).map_mul, realAddValuation_zpow_of_ne_zero hα0, hα,
    WithTop.untop₀_one, mul_one]
  cases hv : realAddValuation L (ρ.coeff (j * m + k)) with
  | top =>
    exact ⟨le_top, ⟨fun h0 ↦ absurd (top_add (a := ((((j * h : ℤ) - v₀ : ℤ) : ℝ) : WithTop ℝ)) ▸ h0)
      WithTop.top_ne_coe, fun h0 ↦ absurd h0 WithTop.top_ne_coe⟩⟩
  | coe r =>
    rw [hv, WithTop.coe_le_coe] at hbound
    simp only [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_eq_coe]
    push_cast at hbound ⊢
    exact ⟨by linarith, ⟨fun _ ↦ by linarith, fun _ ↦ by linarith⟩⟩

/-- On any finite face `[k, k + l]` of slope `-h / m` (`0 < m`) with a uniformizer `α`, every
rescaled term `ρ_{j m + k} α^{j h - v_L(ρ_k)}` lies in `𝒪[L]`. -/
theorem mem_integer_mul_zpow_of_isFiniteFace {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) (j : ℕ) :
    (ramificationPolynomial φ α).coeff (j * m + k) *
      α ^ ((j * h : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L] :=
  mem_integer_iff_realAddValuation_nonneg.mpr
    (realAddValuation_mul_zpow_of_isFiniteFace hm hα hface j).1

/-- On a finite face `[k, k + l]` of slope `-h / m` (`0 < m`) with a uniformizer `α`,
`(residualPolynomial φ α k l h m).coeff j ≠ 0` iff `j ≤ l / m` and `(j * m + k, v_L(ρ_{j m + k}))`
lies on the face's supporting line. -/
theorem coeff_residualPolynomial_ne_zero_iff {φ : 𝒪[K][X]} {α : L} {k l h m j : ℕ}
    (hm : 0 < m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).coeff j ≠ 0 ↔
      j ≤ l / m ∧ realAddValuation L ((ramificationPolynomial φ α).coeff (j * m + k)) =
        (((WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k)) - (j * h : ℤ) : ℤ) : ℝ) : WithTop ℝ) := by
  rcases le_or_gt j (l / m) with hj | hj
  · obtain ⟨h0, hiff⟩ := realAddValuation_mul_zpow_of_isFiniteFace hm hα hface j
    rw [coeff_residualPolynomial_of_mem_integer hj
        (mem_integer_mul_zpow_of_isFiniteFace hm hα hface j),
      ne_eq, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_realAddValuation_pos,
      Subtype.coe_mk, not_lt]
    exact ⟨fun h ↦ ⟨hj, hiff.mp (le_antisymm h h0)⟩, fun h ↦ (hiff.mpr h.2).le⟩
  · simp [coeff_residualPolynomial_eq_zero_of_lt _ _ _ _ _ _ hj, not_le.mpr hj]

/-- On any finite face starting at `k`, `(residualPolynomial φ α k l h m).coeff 0 ≠ 0` whenever `α`
is a uniformizer of `L`. -/
theorem coeff_zero_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hα : realAddValuation L α = 1) {σ : ℝ}
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      σ k (k + l)) : (residualPolynomial φ α k l h m).coeff 0 ≠ 0 := by
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα
  have hc0 : (ramificationPolynomial φ α).coeff k ≠ 0 := realAddValuation_eq_top_iff.not.mp
    (((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).eq_left_of_isFiniteFace hface ▸ hface.left_ne_top)
  have hval : realAddValuation L ((ramificationPolynomial φ α).coeff (0 * m + k) *
      α ^ (((0 : ℕ) * (h : ℤ)) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k)))) = 0 := by
    simp only [zero_mul, zero_add, Nat.cast_zero, zero_sub, (realAddValuation L).map_mul,
      realAddValuation_of_ne_zero hc0, realAddValuation_zpow_of_ne_zero hα0, hα,
      WithTop.untop₀_one, mul_one, ← WithTop.coe_add, Int.cast_neg, add_neg_cancel,
      WithTop.coe_zero]
  rw [coeff_residualPolynomial_of_mem_integer (Nat.zero_le _)
      (mem_integer_iff_realAddValuation_nonneg.mpr hval.ge), ne_eq,
    IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_realAddValuation_pos, Subtype.coe_mk,
    hval]
  exact lt_irrefl 0

private theorem log_coeff_right_of_isFiniteFace {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    WithZero.log (normalizedValuationWithZero L ((ramificationPolynomial φ α).coeff (k + l))) =
      WithZero.log (normalizedValuationWithZero L ((ramificationPolynomial φ α).coeff k)) -
        ((l / m : ℕ) * (h : ℤ)) := by
  obtain ⟨q, rfl⟩ := dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl hm hcop hface
  have henv := (ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hw := hface.mul_width_eq_sub
  rw [Nat.add_sub_cancel_left, henv.eq_left_of_isFiniteFace hface,
    henv.eq_right_of_isFiniteFace hface, untop₀_realAddValuation, untop₀_realAddValuation] at hw
  rw [Nat.mul_div_right q hm]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  exact Int.cast_injective (α := ℝ) (by push_cast at hw ⊢; field_simp [hm0] at hw; linarith)

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m`, the `(l / m)`-th
coefficient of `residualPolynomial φ α k l h m` is nonzero whenever `α` is a uniformizer of `L`. -/
theorem coeff_div_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).coeff (l / m) ≠ 0 := by
  have hc0 : (ramificationPolynomial φ α).coeff (k + l) ≠ 0 := realAddValuation_eq_top_iff.not.mp
    (((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).eq_right_of_isFiniteFace hface ▸ hface.right_ne_top)
  have hidx : (l / m) * m + k = k + l := by
    rw [Nat.div_mul_cancel
      (dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl hm hcop hface), add_comm]
  rw [coeff_residualPolynomial_ne_zero_iff hm hα hface, hidx, realAddValuation_of_ne_zero hc0,
    log_coeff_right_of_isFiniteFace hl hm hcop hface]
  exact ⟨le_rfl, rfl⟩

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` with a
uniformizer `α`, `(residualPolynomial φ α k l h m).natDegree = l / m`. -/
theorem natDegree_residualPolynomial {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).natDegree = l / m :=
  le_antisymm (natDegree_residualPolynomial_le φ α k l h m)
    (le_natDegree_of_ne_zero (coeff_div_residualPolynomial_ne_zero hl hm hcop hα hface))

/-- On a finite face `[k, k + l]` of positive width `l` and reduced slope `-h / m` with a
uniformizer `α`, `(residualPolynomial φ α k l h m).leadingCoeff ≠ 0`. -/
theorem leadingCoeff_residualPolynomial_ne_zero {φ : 𝒪[K][X]} {α : L} {k l h m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hcop : h.Coprime m) (hα : realAddValuation L α = 1)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) :
    (residualPolynomial φ α k l h m).leadingCoeff ≠ 0 := by
  rw [Polynomial.leadingCoeff, natDegree_residualPolynomial hl hm hcop hα hface]
  exact coeff_div_residualPolynomial_ne_zero hl hm hcop hα hface

/-- **Matching of adjacent residual polynomials.** If `[k, k + l₁]` is a finite face of positive
width `l₁` and reduced slope `-h₁ / m₁` with a uniformizer `α`, then the constant coefficient of
`residualPolynomial φ α (k + l₁) l₂ h₂ m₂` equals
`(residualPolynomial φ α k l₁ h₁ m₁).leadingCoeff`. -/
theorem coeff_zero_residualPolynomial_eq_leadingCoeff {φ : 𝒪[K][X]} {α : L} {k l₁ h₁ m₁ : ℕ}
    (hl₁ : 0 < l₁) (hm₁ : 0 < m₁) (hcop₁ : h₁.Coprime m₁) (hα : realAddValuation L α = 1)
    (hface₁ : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h₁ : ℝ) / m₁) k (k + l₁)) (l₂ h₂ m₂ : ℕ) :
    (residualPolynomial φ α (k + l₁) l₂ h₂ m₂).coeff 0 =
      (residualPolynomial φ α k l₁ h₁ m₁).leadingCoeff := by
  have hdvd := dvd_of_isFiniteFace_newtonPolygon_ramificationPolynomial hl₁ hm₁ hcop₁ hface₁
  have hx_eq : (ramificationPolynomial φ α).coeff (0 * m₂ + (k + l₁)) *
        α ^ (((0 : ℕ) * (h₂ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff (k + l₁)))) =
      (ramificationPolynomial φ α).coeff ((l₁ / m₁) * m₁ + k) *
        α ^ (((l₁ / m₁ : ℕ) * (h₁ : ℤ)) - WithZero.log (normalizedValuationWithZero L
          ((ramificationPolynomial φ α).coeff k))) := by
    rw [zero_mul, zero_add, Nat.div_mul_cancel hdvd, add_comm l₁ k,
      log_coeff_right_of_isFiniteFace hl₁ hm₁ hcop₁ hface₁]
    congr 2; omega
  have hx₁ := mem_integer_mul_zpow_of_isFiniteFace hm₁ hα hface₁ (l₁ / m₁)
  rw [Polynomial.leadingCoeff, natDegree_residualPolynomial hl₁ hm₁ hcop₁ hα hface₁,
    coeff_residualPolynomial_of_mem_integer (Nat.zero_le _) (hx_eq.symm ▸ hx₁),
    coeff_residualPolynomial_of_mem_integer le_rfl hx₁]
  exact congrArg (residue 𝒪[L]) (Subtype.ext hx_eq)

end GeneralFace

section Eisenstein

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Additivity exponents on wild faces.** On a finite face `[k, k + l]` of slope `-h / m` with
`0 < h` and `0 < m`, every nonzero coefficient of `residualPolynomial φ α k l h m` sits at an index
`j` where `k + j * m` is a power of `ringChar 𝓀[K]`. -/
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
  have hca : IsSupportingLine (fun i ↦ realAddValuation L (ρ.coeff i)) (-(h : ℝ) / m) c :=
    henv.isSupportingLine_iff.mp (hface.isSupportingLine_untop₀_sub ⟨le_rfl, hface.left_le_right⟩)
  have hmem : j * m + k ∈
      supportingFace (fun i ↦ realAddValuation L (ρ.coeff i)) (-(h : ℝ) / m) c := by
    rw [mem_supportingFace, hjval, WithTop.coe_eq_coe]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    simp only [c, N, henv.eq_left_of_isFiniteFace hface, untop₀_realAddValuation]
    push_cast; field_simp [hm0]; ring
  obtain ⟨i, hi⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr (Nat.cast_pos.mpr hh)) (Nat.cast_pos.mpr hm)) hca hmem
  exact ⟨i, (add_comm k (j * m)).trans hi⟩

/-- **Additivity of the expanded residual polynomial on wild faces.** On a finite face `[k, k + l]`
of slope `-h / m` (`0 < h`, `0 < m`), `X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)`
evaluates additively on every commutative `𝓀[L]`-algebra `B`. -/
theorem aeval_add_X_pow_mul_comp_residualPolynomial {B : Type*} [CommSemiring B] [Algebra 𝓀[L] B]
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {k l h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L))
      (-(h : ℝ) / m) k (k + l)) (x y : B) :
    aeval (x + y) (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) =
      aeval x (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) +
        aeval y (X ^ k * (residualPolynomial φ α k l h m).comp (X ^ m)) := by
  set A := residualPolynomial φ α k l h m
  have hsum_eq : A = ∑ j ∈ Finset.range (l / m + 1), monomial j (A.coeff j) :=
    A.as_sum_range' (l / m + 1) (Nat.lt_succ_of_le (natDegree_residualPolynomial_le φ α k l h m))
  have heval (z : B) : aeval z (X ^ k * A.comp (X ^ m)) =
      ∑ j ∈ Finset.range (l / m + 1), algebraMap 𝓀[L] B (A.coeff j) * z ^ (k + j * m) := by
    rw [map_mul, map_pow, aeval_X, aeval_comp, aeval_X_pow]
    conv_lhs => rw [hsum_eq]
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [aeval_monomial, ← pow_mul, mul_comm m j, mul_left_comm (z ^ k), ← pow_add]
  rw [heval, heval, heval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne (A.coeff j) 0 with hj0 | hj
  · simp [hj0]
  · obtain ⟨i, hi⟩ :=
      exists_eq_pow_of_coeff_residualPolynomial_ne_zero hmonic hφ hroot hgen hh hm hface hj
    rw [hi, ← mul_add]; congr 1
    rcases subsingleton_or_nontrivial B with _ | _
    · exact Subsingleton.elim _ _
    · have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
      have : CharP 𝓀[L] (ringChar 𝓀[K]) := Algebra.ringChar_eq 𝓀[K] 𝓀[L] ▸ ringChar.charP 𝓀[L]
      have : CharP B (ringChar 𝓀[K]) :=
        charP_of_injective_algebraMap (algebraMap 𝓀[L] B).injective (ringChar 𝓀[K])
      exact add_pow_char_pow x y (ringChar 𝓀[K]) i

/-- **Tame residual polynomial coefficients.** On the tame segment `[p ^ w, φ.natDegree]`
(`h = 0`, `m = 1`), the `j`-th coefficient of the residual polynomial for `j ≤ n - p ^ w` is the
residue of `(ramificationPolynomial φ α).coeff (p ^ w + j)`. -/
theorem coeff_tame_residualPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) {j : ℕ}
    (hj : j ≤ φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) :
    (residualPolynomial φ α ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)
        (φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) 0 1).coeff j =
      residue 𝒪[L] ⟨(ramificationPolynomial φ α).coeff
          ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree + j),
        coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen _⟩ := by
  set k := (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree
  have hlog0 : WithZero.log (normalizedValuationWithZero L
      ((ramificationPolynomial φ α).coeff k)) = 0 := by
    have h := congrArg WithTop.untop₀
      (realAddValuation_coeff_pow_padicValNat_ramificationPolynomial hmonic hφ hroot hgen)
    rw [untop₀_realAddValuation, WithTop.untop₀_zero] at h
    exact_mod_cast h
  have hx : (ramificationPolynomial φ α).coeff (j * 1 + k) *
      α ^ ((j * 0 : ℤ) - WithZero.log (normalizedValuationWithZero L
        ((ramificationPolynomial φ α).coeff k))) ∈ 𝒪[L] := by
    simpa [hlog0, add_comm] using
      coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen (k + j)
  rw [coeff_residualPolynomial_of_mem_integer (by simpa using hj) hx]
  exact congrArg (residue 𝒪[L]) (Subtype.ext (by simp [hlog0, add_comm]))

/-- **Congruence of the tame residual polynomial with `ρ` modulo `𝓂[L]`.** Multiplying the tame
residual polynomial by `X ^ (p ^ w)` recovers the coefficientwise reduction of
`ramificationPolynomial φ α` modulo `𝓂[L]`. -/
theorem coeff_X_pow_mul_tame_residualPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (j : ℕ) :
    (X ^ ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) *
      residualPolynomial φ α ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)
        (φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) 0 1).coeff j =
      residue 𝒪[L] ⟨(ramificationPolynomial φ α).coeff j,
        coeff_ramificationPolynomial_mem_integer hmonic hφ hroot hgen j⟩ := by
  have hkn : (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree ≤ φ.natDegree :=
    (isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen).left_le_right
  set k := (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree
  rw [coeff_X_pow_mul']
  split_ifs with hle
  · rcases le_or_gt j φ.natDegree with hjn | hgt
    · rw [coeff_tame_residualPolynomial hmonic hφ hroot hgen (Nat.sub_le_sub_right hjn _)]
      exact congrArg (residue 𝒪[L])
        (Subtype.ext (by dsimp only [k] at hle ⊢; rw [Nat.add_sub_of_le hle]))
    · rw [coeff_residualPolynomial_eq_zero_of_lt _ _ _ _ _ _ (by omega)]
      symm; rw [IsLocalRing.residue_eq_zero_iff, show (⟨(ramificationPolynomial φ α).coeff j, _⟩ :
        𝒪[L]) = 0 from Subtype.ext (coeff_ramificationPolynomial_eq_zero_of_lt hgt)]
      exact Ideal.zero_mem _
  · symm; rw [IsLocalRing.residue_eq_zero_iff]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [show (⟨(ramificationPolynomial φ α).coeff 0, _⟩ : 𝒪[L]) = 0 from
        Subtype.ext (coeff_zero_ramificationPolynomial_of_isRoot hroot)]
      exact Ideal.zero_mem _
    · exact mem_maximalIdeal_iff_one_le_realAddValuation.mpr
        (one_le_realAddValuation_coeff_of_lt_pow_padicValNat hmonic hφ hroot hgen
          (Nat.one_le_iff_ne_zero.mpr hj0) (not_le.mp hle))

end Eisenstein

end TauCeti
