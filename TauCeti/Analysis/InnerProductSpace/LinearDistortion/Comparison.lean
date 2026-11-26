/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Submultiplicativity and comparison of the linear distortions

Let `V`, `W`, `X` be oriented real inner product spaces of the same finite dimension `n`, and let
`q_O` and `q_I` be the outer and inner distortions of a linear map (`Orientation.outerDistortion`,
`Orientation.innerDistortion`). This file proves:

* **Submultiplicativity.** `q_O(B ∘ A) ≤ q_O(B) q_O(A)` for all `A`, `B` (in positive dimension,
  with `0 · ∞ = 0`), and `q_I(B ∘ A) ≤ q_I(B) q_I(A)` when `J(A) ≥ 0`. Some sign hypothesis is
  needed: a reflection `R` of the plane has `q_I(R) = 0` while `q_I(R ∘ R) = q_I(id) = 1`.
* **The case `q_O ≤ 1`.** `q_O(A) ≤ 1` holds exactly when `A = 0` or
  `A = c U` with `c > 0` and `U` a linear isometry with `J(U) = 1`; then `q_O(A) = 1` exactly in
  the second case.
* **The distortion inequalities.** For a real `K ≥ 0`, `q_O(A) ≤ K` iff `‖A‖ⁿ ≤ K J(A)` (in
  positive dimension), and `q_I(A) ≤ K` iff `J(A) ≤ K ℓ(A)ⁿ`. The hypothesis `K ≥ 0` is needed:
  a reflection `R` of the plane has `‖R‖² = 1 ≤ (-1) J(R)` while `q_O(R) = ∞`.
* **Comparison of the exponents.** `q_I(A) ≤ q_O(A)ⁿ⁻¹`, and `q_O(A) ≤ q_I(A)ⁿ⁻¹` if `J(A) > 0`:
  for such `A` both distortions lie between `‖A‖ / ℓ(A)` and its `(n - 1)`-st power.
  In dimension `2` the two distortions of a map with `J(A) > 0` agree, and in every dimension
  `q_I(A) = 1` iff `q_O(A) = 1`.

## Main declarations

* `Orientation.outerDistortion_comp_le`, `Orientation.innerDistortion_comp_le`:
  submultiplicativity.
* `Orientation.outerDistortion_le_one_iff`, `Orientation.outerDistortion_eq_one_iff`: the maps of
  outer distortion at most `1`, and exactly `1`.
* `Orientation.outerDistortion_le_ofReal_iff`, `Orientation.innerDistortion_le_iff`: the
  distortion inequalities `‖A‖ⁿ ≤ K J(A)` and `J(A) ≤ K ℓ(A)ⁿ`.
* `Orientation.ofReal_innerDistortion_le_outerDistortion_pow`,
  `Orientation.outerDistortion_le_ofReal_innerDistortion_pow`: `q_I ≤ q_Oⁿ⁻¹` and `q_O ≤ q_Iⁿ⁻¹`.
* `Orientation.outerDistortion_eq_ofReal_innerDistortion_of_fin_two`: `q_O = q_I` in dimension `2`.
* `Orientation.innerDistortion_eq_one_iff_outerDistortion_eq_one`: `q_I(A) = 1` iff `q_O(A) = 1`.

## References

* O. Martio, S. Rickman and J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), Section 2, (2.21)–(2.22) and (2.25).
-/

public section

noncomputable section

open Module
open scoped ENNReal

namespace Orientation

variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] [Fact (finrank ℝ X = n)]
  (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n)) (oX : Orientation ℝ X (Fin n))

/-! ### Submultiplicativity -/

omit [FiniteDimensional ℝ X] in
/-- **Submultiplicativity of the outer distortion**: in positive dimension,
`q_O(B ∘ A) ≤ q_O(B) q_O(A)`, with the convention `0 · ∞ = 0` of `ℝ≥0∞`. In dimension `0` it
fails for two orientation-reversing maps, which have `q_O = 0` while their composition has
`q_O = 1`. -/
theorem outerDistortion_comp_le (hn : 0 < n) (A : V →ₗ[ℝ] W) (B : W →ₗ[ℝ] X) :
    oV.outerDistortion oX (B ∘ₗ A) ≤ oW.outerDistortion oX B * oV.outerDistortion oW A := by
  by_cases hBA : B ∘ₗ A = 0
  · simp [hBA, oV.outerDistortion_zero oX hn]
  have hA : A ≠ 0 := by rintro rfl; simp at hBA
  have hB : B ≠ 0 := by rintro rfl; simp at hBA
  have hJ := oV.orientedJacobian_comp oW oX A B
  by_cases hpos : 0 < oV.orientedJacobian oX (B ∘ₗ A)
  · rcases lt_or_ge 0 (oW.orientedJacobian oX B) with hJB | hJB
    · have hJA : 0 < oV.orientedJacobian oW A := by
        rw [hJ] at hpos
        exact pos_of_mul_pos_right hpos hJB.le
      rw [oV.outerDistortion_of_pos oX hpos, oW.outerDistortion_of_pos oX hJB,
        oV.outerDistortion_of_pos oW hJA,
        ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (norm_nonneg _) n) hJB.le), hJ,
        div_mul_div_comm, ← mul_pow]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (by
          rw [LinearMap.toContinuousLinearMap_comp]
          exact ContinuousLinearMap.opNorm_comp_le _ _) n)
        (mul_pos hJB hJA).le)
    · rw [oW.outerDistortion_of_nonpos oX hJB hB,
        ENNReal.top_mul (oV.outerDistortion_ne_zero oW hA)]
      exact le_top
  · rw [oV.outerDistortion_of_nonpos oX (not_lt.mp hpos) hBA]
    rw [hJ, not_lt] at hpos
    rcases le_or_gt (oW.orientedJacobian oX B) 0 with hJB | hJB
    · rw [oW.outerDistortion_of_nonpos oX hJB hB,
        ENNReal.top_mul (oV.outerDistortion_ne_zero oW hA)]
    · have hJA : oV.orientedJacobian oW A ≤ 0 := by
        by_contra h
        exact (mul_pos hJB (not_le.mp h)).not_ge hpos
      rw [oV.outerDistortion_of_nonpos oW hJA hA,
        ENNReal.mul_top (oW.outerDistortion_ne_zero oX hB)]

/-- **Submultiplicativity of the inner distortion**: `q_I(B ∘ A) ≤ q_I(B) q_I(A)` when
`J(A) ≥ 0`. Some sign hypothesis is needed: a reflection `R` has `q_I(R) = 0`, while
`q_I(R ∘ R) = 1`. No hypothesis on `J(B)` is needed: if `J(B ∘ A) = J(B) J(A) > 0` and
`J(A) ≥ 0`, then both factors are positive. -/
theorem innerDistortion_comp_le {A : V →ₗ[ℝ] W} {B : W →ₗ[ℝ] X}
    (hA : 0 ≤ oV.orientedJacobian oW A) :
    oV.innerDistortion oX (B ∘ₗ A) ≤ oW.innerDistortion oX B * oV.innerDistortion oW A := by
  have hJ := oV.orientedJacobian_comp oW oX A B
  by_cases hpos : 0 < oV.orientedJacobian oX (B ∘ₗ A)
  swap
  · rw [oV.innerDistortion_of_nonpos oX (not_lt.mp hpos)]
    exact mul_nonneg (oW.innerDistortion_nonneg oX B) (oV.innerDistortion_nonneg oW A)
  have hJB : 0 < oW.orientedJacobian oX B := by
    rw [hJ] at hpos
    exact pos_of_mul_pos_left hpos hA
  have hJA : 0 < oV.orientedJacobian oW A := by
    rw [hJ] at hpos
    exact pos_of_mul_pos_right hpos hJB.le
  have hℓA := oV.minimalStretch_pow_pos_of_orientedJacobian_ne_zero oW hJA.ne'
  have hℓB := oW.minimalStretch_pow_pos_of_orientedJacobian_ne_zero oX hJB.ne'
  rw [oV.innerDistortion_of_pos oX hpos, oW.innerDistortion_of_pos oX hJB,
    oV.innerDistortion_of_pos oW hJA, hJ, div_mul_div_comm, ← mul_pow]
  refine div_le_div_of_nonneg_left (mul_pos hJB hJA).le (by rw [mul_pow]; exact mul_pos hℓB hℓA) ?_
  exact pow_le_pow_left₀
    (mul_nonneg B.minimalStretch_nonneg A.minimalStretch_nonneg)
    (B.minimalStretch_mul_le_minimalStretch_comp A) n

/-! ### Maps of outer distortion at most one -/

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- `q_O(A) ≤ 1` exactly when `A = 0` or `A` is a positive multiple of a
linear isometry of oriented Jacobian `1`. -/
theorem outerDistortion_le_one_iff {A : V →ₗ[ℝ] W} :
    oV.outerDistortion oW A ≤ 1 ↔
      A = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∃ U : V →ₗᵢ[ℝ] W,
        oV.orientedJacobian oW U.toLinearMap = 1 ∧ A = c • U.toLinearMap := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases hA : A = 0
    · exact .inl hA
    right
    have hJ : 0 < oV.orientedJacobian oW A := by
      by_contra hJ
      rw [oV.outerDistortion_of_nonpos oW (not_lt.mp hJ) hA] at h
      exact absurd h (by simp)
    rw [oV.outerDistortion_of_pos oW hJ, ENNReal.ofReal_le_one, div_le_one hJ] at h
    set f := LinearMap.toContinuousLinearMap A
    have hfA : f.toLinearMap = A := LinearMap.coe_toContinuousLinearMap A
    have heq : |oV.orientedJacobian oW f.toLinearMap| = ‖f‖ ^ n := by
      rw [hfA, abs_of_pos hJ]
      exact le_antisymm ((le_abs_self _).trans (oV.abs_orientedJacobian_le oW A)) h
    rcases (oV.abs_orientedJacobian_toLinearMap_eq_norm_pow_iff oW f).mp heq with hf0 | hconf
    · exact absurd (by rw [← hfA, hf0, ContinuousLinearMap.toLinearMap_zero]) hA
    obtain ⟨c, hc, li, hli⟩ := hconf
    -- Replace `(c, li)` by `(|c|, ± li)`.
    obtain ⟨d, hd, U, hU⟩ : ∃ d : ℝ, 0 < d ∧ ∃ U : V →ₗᵢ[ℝ] W, A = d • U.toLinearMap := by
      rcases lt_or_gt_of_ne hc with hc | hc
      · refine ⟨-c, neg_pos.mpr hc, (LinearIsometryEquiv.neg ℝ).toLinearIsometry.comp li, ?_⟩
        ext v
        simp [← hfA, hli]
      · exact ⟨c, hc, li, by ext v; simp [← hfA, hli]⟩
    refine ⟨d, hd, U, ?_, hU⟩
    have habs := oV.abs_orientedJacobian_linearIsometry oW U
    have hJU : 0 < oV.orientedJacobian oW U.toLinearMap := by
      rw [hU, oV.orientedJacobian_smul oW] at hJ
      exact pos_of_mul_pos_right hJ (pow_pos hd n).le
    rwa [abs_of_pos hJU] at habs
  · rintro (rfl | ⟨c, hc, U, hU, rfl⟩)
    · rcases n.eq_zero_or_pos with rfl | hn
      · rcases lt_or_ge 0 (oV.orientedJacobian oW 0) with h | h
        · simp [oV.outerDistortion_of_pos oW h, oV.orientedJacobian_eq_one_of_fin_zero oW h]
        · simp [oV.outerDistortion_zero_of_nonpos oW h]
      · simp [oV.outerDistortion_zero oW hn]
    · exact (oV.outerDistortion_smul_linearIsometry oW (pow_pos hc n) U hU).le

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- `q_O(A) = 1` exactly when `A` is a positive multiple of a linear
isometry of oriented Jacobian `1`. -/
theorem outerDistortion_eq_one_iff {A : V →ₗ[ℝ] W} :
    oV.outerDistortion oW A = 1 ↔
      ∃ c : ℝ, 0 < c ∧ ∃ U : V →ₗᵢ[ℝ] W,
        oV.orientedJacobian oW U.toLinearMap = 1 ∧ A = c • U.toLinearMap := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, U, hU, hA⟩ ↦
    hA ▸ oV.outerDistortion_smul_linearIsometry oW (pow_pos hc n) U hU⟩
  rcases (oV.outerDistortion_le_one_iff oW).mp h.le with rfl | hA
  · rcases n.eq_zero_or_pos with rfl | hn
    · -- In dimension `0`, `q_O(0) = 1` forces `J(0) = 1`, and `0 = 1 • 0` with `0` an isometry.
      have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
      have hJ : 0 < oV.orientedJacobian oW 0 :=
        oV.orientedJacobian_pos_of_outerDistortion_ne_zero_of_ne_top oW (by simp [h])
          (by simp [h])
      let U : V →ₗᵢ[ℝ] W := ⟨0, fun x ↦ by simp [Subsingleton.elim x 0]⟩
      have hU : U.toLinearMap = 0 := rfl
      exact ⟨1, one_pos, U, by rw [hU]; exact oV.orientedJacobian_eq_one_of_fin_zero oW hJ,
        by rw [hU, smul_zero]⟩
    · simp [oV.outerDistortion_zero oW hn] at h
  · exact hA

/-! ### The distortion inequalities -/

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- In positive dimension and for real `K ≥ 0`, `q_O(A) ≤ K` exactly when `‖A‖ⁿ ≤ K J(A)`. The
hypothesis `K ≥ 0` is needed: an orientation-reversing isometry `R` of the plane satisfies
`‖R‖² = 1 ≤ (-1) J(R)`, while `q_O(R) = ∞`. -/
theorem outerDistortion_le_ofReal_iff (hn : 0 < n) {K : ℝ} (hK : 0 ≤ K) {A : V →ₗ[ℝ] W} :
    oV.outerDistortion oW A ≤ ENNReal.ofReal K ↔
      ‖LinearMap.toContinuousLinearMap A‖ ^ n ≤ K * oV.orientedJacobian oW A := by
  by_cases hJ : 0 < oV.orientedJacobian oW A
  · rw [oV.outerDistortion_of_pos oW hJ, ENNReal.ofReal_le_ofReal_iff hK, div_le_iff₀ hJ]
  by_cases hA : A = 0
  · subst hA
    simp [oV.outerDistortion_zero oW hn, oV.orientedJacobian_zero_of_pos oW hn, hn.ne']
  rw [oV.outerDistortion_of_nonpos oW (not_lt.mp hJ) hA]
  simp only [top_le_iff, ENNReal.ofReal_ne_top, false_iff, not_le]
  exact (mul_nonpos_of_nonneg_of_nonpos hK (not_lt.mp hJ)).trans_lt
    (pow_pos (LinearMap.norm_toContinuousLinearMap_pos hA) n)

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- For real `K ≥ 0`, `q_I(A) ≤ K` exactly when `J(A) ≤ K ℓ(A)ⁿ`. -/
theorem innerDistortion_le_iff {K : ℝ} (hK : 0 ≤ K) {A : V →ₗ[ℝ] W} :
    oV.innerDistortion oW A ≤ K ↔ oV.orientedJacobian oW A ≤ K * A.minimalStretch ^ n := by
  by_cases hJ : 0 < oV.orientedJacobian oW A
  · rw [oV.innerDistortion_of_pos oW hJ,
      div_le_iff₀ (oV.minimalStretch_pow_pos_of_orientedJacobian_ne_zero oW hJ.ne')]
  · rw [oV.innerDistortion_of_nonpos oW (not_lt.mp hJ)]
    exact iff_of_true hK
      ((not_lt.mp hJ).trans (mul_nonneg hK (pow_nonneg A.minimalStretch_nonneg n)))

/-! ### Comparison of the exponents -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The inner distortion is at most `(‖A‖ / ℓ(A))ⁿ⁻¹`, which is `(σ₁ / σₙ)ⁿ⁻¹` when `J(A) > 0`. -/
theorem innerDistortion_le_norm_div_minimalStretch_pow (A : V →ₗ[ℝ] W) :
    oV.innerDistortion oW A ≤
      (‖LinearMap.toContinuousLinearMap A‖ / A.minimalStretch) ^ (n - 1) := by
  rcases le_or_gt (oV.orientedJacobian oW A) 0 with h | h
  · rw [oV.innerDistortion_of_nonpos oW h]
    exact pow_nonneg (div_nonneg (norm_nonneg _) A.minimalStretch_nonneg) _
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [oV.innerDistortion_of_pos oW h, oV.orientedJacobian_eq_one_of_fin_zero oW h]
    simp
  have hℓ := oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW hn h.ne'
  have hpow : A.minimalStretch ^ n = A.minimalStretch ^ (n - 1) * A.minimalStretch := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [oV.innerDistortion_of_pos oW h, div_pow, div_le_div_iff₀ (pow_pos hℓ n)
    (pow_pos hℓ (n - 1)), hpow]
  calc oV.orientedJacobian oW A * A.minimalStretch ^ (n - 1)
      ≤ (‖LinearMap.toContinuousLinearMap A‖ ^ (n - 1) * A.minimalStretch) *
          A.minimalStretch ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (oV.orientedJacobian_le_norm_pow_mul_minimalStretch oW hn A)
          (pow_nonneg hℓ.le _)
    _ = _ := by ring

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- When `J(A) > 0`, the outer distortion is at most `(‖A‖ / ℓ(A))ⁿ⁻¹ = (σ₁ / σₙ)ⁿ⁻¹`. -/
theorem outerDistortion_le_ofReal_norm_div_minimalStretch_pow {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A ≤
      ENNReal.ofReal ((‖LinearMap.toContinuousLinearMap A‖ / A.minimalStretch) ^ (n - 1)) := by
  rw [oV.outerDistortion_of_pos oW h]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [oV.orientedJacobian_eq_one_of_fin_zero oW h]
  have hℓ := oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW hn h.ne'
  set a := ‖LinearMap.toContinuousLinearMap A‖
  have hpow : a ^ n = a * a ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  rw [div_pow, div_le_div_iff₀ h (pow_pos hℓ (n - 1)), hpow]
  calc a * a ^ (n - 1) * A.minimalStretch ^ (n - 1)
      = (a * A.minimalStretch ^ (n - 1)) * a ^ (n - 1) := by ring
    _ ≤ oV.orientedJacobian oW A * a ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (oV.norm_mul_minimalStretch_pow_le_orientedJacobian oW h.le)
          (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- **The inner distortion is at most the `(n - 1)`-st power of the outer distortion**: when
`J(A) > 0`, each of the `n - 1` factors `σᵢ / σₙ` of `q_I(A)` is at most `σ₁ / σₙ ≤ q_O(A)`, and
when `J(A) ≤ 0`, `q_I(A) = 0`. -/
theorem ofReal_innerDistortion_le_outerDistortion_pow (A : V →ₗ[ℝ] W) :
    ENNReal.ofReal (oV.innerDistortion oW A) ≤ oV.outerDistortion oW A ^ (n - 1) := by
  refine (ENNReal.ofReal_le_ofReal (oV.innerDistortion_le_norm_div_minimalStretch_pow oW A)).trans
    ?_
  rw [ENNReal.ofReal_pow (div_nonneg (norm_nonneg _) A.minimalStretch_nonneg)]
  exact pow_le_pow_left₀ (by simp) (oV.ofReal_norm_div_minimalStretch_le_outerDistortion oW A) _

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- **The outer distortion is at most the `(n - 1)`-st power of the inner distortion** when
`J(A) > 0`: each of the `n - 1` factors `σ₁ / σᵢ` of `q_O(A)` is at most
`σ₁ / σₙ ≤ q_I(A)`. For a nonzero `A` with `J(A) ≤ 0` it fails, since `q_O(A) = ∞`. -/
theorem outerDistortion_le_ofReal_innerDistortion_pow {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A ≤ ENNReal.ofReal (oV.innerDistortion oW A ^ (n - 1)) :=
  (oV.outerDistortion_le_ofReal_norm_div_minimalStretch_pow oW h).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (div_nonneg (norm_nonneg _) A.minimalStretch_nonneg)
      (oV.norm_div_minimalStretch_le_innerDistortion oW h) _))

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- In dimension `2` the outer and inner distortions of a map with `J(A) > 0` agree: both are
`σ₁ / σ₂`. -/
theorem outerDistortion_eq_ofReal_innerDistortion_of_fin_two [Fact (finrank ℝ V = 2)]
    [Fact (finrank ℝ W = 2)] (oV : Orientation ℝ V (Fin 2)) (oW : Orientation ℝ W (Fin 2))
    {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A = ENNReal.ofReal (oV.innerDistortion oW A) :=
  le_antisymm ((oV.outerDistortion_le_ofReal_innerDistortion_pow oW h).trans_eq (by simp))
    ((oV.ofReal_innerDistortion_le_outerDistortion_pow oW A).trans_eq (by simp))

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The inner distortion is `1` exactly when the outer distortion is `1`. -/
theorem innerDistortion_eq_one_iff_outerDistortion_eq_one {A : V →ₗ[ℝ] W} :
    oV.innerDistortion oW A = 1 ↔ oV.outerDistortion oW A = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hJ : 0 < oV.orientedJacobian oW A := (oV.innerDistortion_pos_iff oW).mp (by simp [h])
    refine le_antisymm ?_ (oV.one_le_outerDistortion oW hJ)
    simpa [h] using oV.outerDistortion_le_ofReal_innerDistortion_pow oW hJ
  · have hJ := oV.orientedJacobian_pos_of_outerDistortion_ne_zero_of_ne_top oW (A := A)
      (by simp [h]) (by simp [h])
    refine le_antisymm ?_ (oV.one_le_innerDistortion oW hJ)
    have := oV.ofReal_innerDistortion_le_outerDistortion_pow oW A
    rwa [h, one_pow, ENNReal.ofReal_le_one] at this

end Orientation
