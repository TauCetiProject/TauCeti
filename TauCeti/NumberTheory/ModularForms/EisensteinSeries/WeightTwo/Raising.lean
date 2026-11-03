/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Character
import TauCeti.Data.ZMod.Divisibility

/-!
# Raised weight-two series as weighted series

For a weight `W : (Fin 2 → ZMod M) → ℂ` and `t ≥ 1`, the raised weight
`TauCeti.EisensteinSeries.raisedWeight t W` of level `t M` puts `W(c / t, d)` at the residue pairs
`(c, d)` modulo `t M` with `t ∣ c`. Its series is `z ↦ G₂^W(t z) + M⁻² (∑ W) (G₂(t z) - t⁻¹ G₂(z))`:
both series are compared along their rows (`TauCeti.EisensteinSeries.tsum_weightedG2Row`), the rows
of the raised weight being those of `W` at `t z`, placed at the multiples of `t`, and the
correction is the difference of the regularizations by `G₂` of the two sides. For weights of total
mass zero the correction vanishes, and the series of the raised weight is exactly `z ↦ G₂^W(t z)`.

This identifies the two families of weight-two Eisenstein series used for the decomposition of
`M₂(N, χ)` with weighted series of level dividing `N`.

* The raised series with character `G₂^{ψ,φ,t}` (`TauCeti.EisensteinSeries.charG2MFRaise`), for a
  pair `(ψ, φ)` other than the trivial one, is the series of the raised weight of `charWeight`.
* The corrected series `E₂(z) - t E₂(t z)` (`TauCeti.EisensteinSeries.correctedE2`) is
  `-t / (2 ζ(2))` times the series of the raised weight of the constant weight `1` of level one.
  For that weight the regularization does not vanish, and it is exactly
  `G₂(t z) - t⁻¹ G₂(z)`.

## Main definitions

* `TauCeti.EisensteinSeries.raisedWeight`: the weight of the raised series.

## Main results

* `TauCeti.EisensteinSeries.sum_raisedWeight`: its total mass is `t` times that of `W`.
* `TauCeti.EisensteinSeries.weightedG2_raisedWeight`: the series of the raised weight.
* `TauCeti.EisensteinSeries.coe_charG2MFRaise`: `G₂^{ψ,φ,t}` as a weighted series.
* `TauCeti.EisensteinSeries.coe_correctedE2_eq_smul_weightedG2`: `E₂(z) - t E₂(t z)` as a
  weighted series.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6, where
  the raised series of level `N` are written as combinations of the series `G₂^v` of `Γ(N)`.
-/

public noncomputable section

open Matrix UpperHalfPlane Complex
open _root_.EisensteinSeries

namespace TauCeti.EisensteinSeries

section Raise

variable {M : ℕ} [NeZero M]

/-- The raised weight of level `t M`: the weight `W` of the pair `(c / t, d)` modulo `M` at a
residue pair `(c, d)` modulo `t M` with `t ∣ c`, and `0` at the others. Its series is
`z ↦ G₂^W(t z)` corrected by `M⁻² (∑ W) (G₂(t z) - t⁻¹ G₂(z))` (`weightedG2_raisedWeight`), so
exactly `z ↦ G₂^W(t z)` when `W` has total mass zero. -/
def raisedWeight (t : ℕ) (W : (Fin 2 → ZMod M) → ℂ) (a : Fin 2 → ZMod (t * M)) : ℂ :=
  if t ∣ (a 0).val then W ![(((a 0).val / t : ℕ) : ZMod M), ((a 1).val : ZMod M)] else 0

variable (t : ℕ) [NeZero t] (W : (Fin 2 → ZMod M) → ℂ)

omit [NeZero M] [NeZero t] in
/-- The defining formula of the raised weight. -/
lemma raisedWeight_def (a : Fin 2 → ZMod (t * M)) :
    raisedWeight t W a =
      if t ∣ (a 0).val then W ![(((a 0).val / t : ℕ) : ZMod M), ((a 1).val : ZMod M)] else 0 :=
  (rfl)

omit [NeZero M] [NeZero t] in
/-- The raised weight is linear in `W`: the zero weight. -/
@[simp]
lemma raisedWeight_zero : raisedWeight t (0 : (Fin 2 → ZMod M) → ℂ) = 0 := by
  ext a
  simp [raisedWeight]

omit [NeZero M] [NeZero t] in
/-- The raised weight is linear in `W`: sums. -/
lemma raisedWeight_add (W' : (Fin 2 → ZMod M) → ℂ) :
    raisedWeight t (W + W') = raisedWeight t W + raisedWeight t W' := by
  ext a
  simp only [raisedWeight, Pi.add_apply]
  split_ifs <;> simp

omit [NeZero M] [NeZero t] in
/-- The raised weight is linear in `W`: scalar multiples. -/
@[simp]
lemma raisedWeight_smul (c : ℂ) : raisedWeight t (c • W) = c • raisedWeight t W := by
  ext a
  simp only [raisedWeight, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The raised weight at the reduction of an integer pair `x`: `W(x₀ / t, x₁)` if `t ∣ x₀`, and
`0` otherwise. -/
theorem raisedWeight_intCast (x : Fin 2 → ℤ) :
    raisedWeight t W ((↑) ∘ x) = if (t : ℤ) ∣ x 0 then W ((↑) ∘ ![x 0 / t, x 1]) else 0 := by
  have hM : M ∣ t * M := dvd_mul_left M t
  simp only [raisedWeight, Function.comp_apply]
  have h1 : (((x 1 : ZMod (t * M)).val : ℕ) : ZMod M) = (x 1 : ZMod M) := by
    rw [ZMod.natCast_val, ZMod.cast_intCast hM]
  have hdvd : t ∣ (x 0 : ZMod (t * M)).val ↔ (t : ℤ) ∣ x 0 := by
    rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_val, ZMod.cast_intCast (dvd_mul_right t M),
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hdvd]
  split_ifs with h
  · rw [h1, ZMod.natCast_val_div_eq_intCast_div (mul_comm M t).dvd h]
    congr 1
    ext i
    fin_cases i <;> rfl
  · rfl

/-- **The total mass of the raised weight** is `t` times that of `W`: the residue pairs `(c, d)`
modulo `t M` with `t ∣ c` lying over a pair modulo `M` are the `t` lifts of `d`. -/
theorem sum_raisedWeight : ∑ a, raisedWeight t W a = t * ∑ e, W e := by
  have ht : 0 < t := NeZero.pos t
  have hM : 0 < M := NeZero.pos M
  -- the residue pairs `(t e₀, e₁ + M j)` modulo `t M`
  let ι : (Fin 2 → ZMod M) × ZMod t → Fin 2 → ZMod (t * M) := fun p ↦
    ![((t * (p.1 0).val : ℕ) : ZMod (t * M)), (((p.1 1).val + M * p.2.val : ℕ) : ZMod (t * M))]
  have hlt₀ (p : (Fin 2 → ZMod M) × ZMod t) : t * (p.1 0).val < t * M :=
    Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) ht
  have hlt₁ (p : (Fin 2 → ZMod M) × ZMod t) : (p.1 1).val + M * p.2.val < t * M := by
    have h₁ := ZMod.val_lt (p.1 1)
    have h₂ := ZMod.val_lt p.2
    nlinarith
  have hval₀ (p) : (ι p 0).val = t * (p.1 0).val := ZMod.val_cast_of_lt (hlt₀ p)
  have hval₁ (p) : (ι p 1).val = (p.1 1).val + M * p.2.val := ZMod.val_cast_of_lt (hlt₁ p)
  have hinj : Function.Injective ι := by
    intro p q hpq
    have h₀ : t * (p.1 0).val = t * (q.1 0).val := by rw [← hval₀, ← hval₀, hpq]
    have h₁ : (p.1 1).val + M * p.2.val = (q.1 1).val + M * q.2.val := by
      rw [← hval₁, ← hval₁, hpq]
    have hmod : (p.1 1).val = (q.1 1).val := by
      have := congrArg (· % M) h₁
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)] using this
    have hdiv : p.2.val = q.2.val := by
      rw [hmod] at h₁
      exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel h₁)
    refine Prod.ext (funext fun i ↦ ?_) (ZMod.val_injective _ hdiv)
    fin_cases i
    · exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left ht h₀)
    · exact ZMod.val_injective _ hmod
  have hoff (a : Fin 2 → ZMod (t * M)) (ha : a ∉ Set.range ι) : raisedWeight t W a = 0 := by
    refine ite_eq_right_iff.mpr fun ⟨k, hk⟩ ↦ absurd ?_ ha
    have hkM : k < M := by
      have := ZMod.val_lt (a 0)
      rw [hk] at this
      exact (Nat.mul_lt_mul_left ht).mp this
    have hq : (a 1).val / M < t :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (ZMod.val_lt (a 1)) (mul_comm t M))
    refine ⟨(![(k : ZMod M), ((a 1).val : ZMod M)], (((a 1).val / M : ℕ) : ZMod t)), ?_⟩
    have h₀ : ((t * (k : ZMod M).val : ℕ) : ZMod (t * M)) = a 0 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hkM, ← hk, ZMod.natCast_zmod_val]
    have h₁ : ((((a 1).val : ZMod M).val + M * (((a 1).val / M : ℕ) : ZMod t).val : ℕ) :
        ZMod (t * M)) = a 1 := by
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hq, Nat.mod_add_div,
        ZMod.natCast_zmod_val]
    ext i
    fin_cases i
    exacts [h₀, h₁]
  have hon (p : (Fin 2 → ZMod M) × ZMod t) : W p.1 = raisedWeight t W (ι p) := by
    rw [raisedWeight_def, ite_eq_left (by rw [hval₀]; exact dvd_mul_right _ _), hval₀, hval₁,
      Nat.mul_div_cancel_left _ ht]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [← Fintype.sum_of_injective ι hinj _ _ hoff hon, Fintype.sum_prod_type]
  simp [Finset.sum_const, ZMod.card, Finset.mul_sum]


/-- The rows of the raised weight are those of `W` at `t z`, placed at the multiples of `t`. -/
theorem weightedG2Row_raisedWeight (z : ℍ) (c : ℤ) :
    weightedG2Row (raisedWeight t W) z c =
      if (t : ℤ) ∣ c then weightedG2Row W (scaleGL t • z) (c / t) else 0 := by
  have ht : (t : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne t
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Int.mul_ediv_cancel_left _ ht, weightedG2Row_def, weightedG2Row_def]
    refine tsum_congr fun d ↦ ?_
    rw [raisedWeight_intCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      dvd_mul_right, ↓reduceIte, Int.mul_ediv_cancel_left _ ht, eisSummand, coe_scaleGL_smul]
    push_cast
    ring_nf
  · rw [weightedG2Row_def]
    refine (tsum_congr fun d ↦ ?_).trans tsum_zero
    rw [raisedWeight_intCast]
    simp [h]

/-- **Raising the level of a weighted weight-two series.** For a weight `W` modulo `M`, the
series of the raised weight modulo `t M` is `z ↦ G₂^W(t z)`, corrected by the multiple
`M⁻² (∑ W) (G₂(t z) - t⁻¹ G₂(z))` of the level-`t` combination of Mathlib's
`EisensteinSeries.G2`. -/
theorem weightedG2_raisedWeight (z : ℍ) :
    weightedG2 (raisedWeight t W) z = weightedG2 W (scaleGL t • z) +
      ((M : ℂ) ^ 2)⁻¹ * (∑ e, W e) * (G2 (scaleGL t • z) - G2 z / t) := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hrows : ∑' c, weightedG2Row (raisedWeight t W) z c =
      ∑' q, weightedG2Row W (scaleGL t • z) q := by
    have hinj : Function.Injective fun q : ℤ ↦ (t : ℤ) * q :=
      mul_right_injective₀ (by exact_mod_cast NeZero.ne t)
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun q ↦ ?_
      rw [weightedG2Row_raisedWeight, ite_eq_left (dvd_mul_right _ _),
        Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne t)]
    · intro c hc
      rw [Function.mem_support, weightedG2Row_raisedWeight] at hc
      split_ifs at hc with h
      · obtain ⟨q, rfl⟩ := h
        exact ⟨q, rfl⟩
      · exact absurd rfl hc
  have h₁ := tsum_weightedG2Row (raisedWeight t W) z
  have h₂ := tsum_weightedG2Row W (scaleGL t • z)
  rw [hrows, h₂, sum_raisedWeight] at h₁
  push_cast at h₁
  rw [← sub_eq_iff_eq_add] at h₁ ⊢
  rw [← h₁]
  field_simp
  ring

/-- For a weight of total mass zero, the raised weight gives `z ↦ G₂^W(t z)` exactly. -/
theorem weightedG2_raisedWeight_of_sum_eq_zero {W : (Fin 2 → ZMod M) → ℂ} (hW : ∑ e, W e = 0)
    (z : ℍ) : weightedG2 (raisedWeight t W) z = weightedG2 W (scaleGL t • z) := by
  rw [weightedG2_raisedWeight, hW, mul_zero, zero_mul, add_zero]

end Raise

section Series

variable {u v N t : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The raised weight-two series with character as a weighted series**: unless `ψ` and `φ` are
both trivial, `G₂^{ψ,φ,t}` is the weighted series of the raised weight of `charWeight (u v) ψ φ`,
of level `t u v`. -/
theorem coe_charG2MFRaise (htuv : t * (u * v) ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    ⇑(charG2MFRaise ψ φ t htuv) = weightedG2 (raisedWeight t (charWeight (u * v) ψ φ)) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  ext z
  rw [charG2MFRaise_apply, coe_charG2MF,
    weightedG2_raisedWeight_of_sum_eq_zero t (sum_charWeight_eq_zero ψ φ dvd_rfl h)]

end Series

/-- **The corrected series as a weighted series**: `E₂(z) - t E₂(t z)` is `-t / (2 ζ(2))` times
the weighted series of the raised weight of the constant weight `1` of level one, the indicator
of the residue pairs `(c, d)` modulo `t` with `t ∣ c`. -/
theorem coe_correctedE2_eq_smul_weightedG2 (t : ℕ) [NeZero t] :
    ⇑(correctedE2 t) = (-(t : ℂ) / (2 * riemannZeta 2)) •
      weightedG2 (raisedWeight t (1 : (Fin 2 → ZMod 1) → ℂ)) := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hζ : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]
    exact div_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)
  have h₀ : weightedG2 (1 : (Fin 2 → ZMod 1) → ℂ) = 0 :=
    weightedG2_eq_zero_of_forall_vecMul_eq fun _ _ ↦ rfl
  ext z
  rw [correctedE2_apply, Pi.smul_apply, weightedG2_raisedWeight, h₀]
  simp only [E2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_unique, one_smul, Nat.cast_one, one_pow, inv_one, one_mul,
    zero_add]
  field_simp
  ring

end TauCeti.EisensteinSeries
