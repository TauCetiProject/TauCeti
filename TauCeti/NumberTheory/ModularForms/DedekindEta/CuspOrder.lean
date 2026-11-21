/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.NumberTheory.ModularForms.Cusps.LevelRaise
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Leading exponents of eta quotients at cusps

At a cusp `a/c` represented by `γ ∈ SL₂(ℤ)`, remove the principal square root of
`cτ + d` from `η(t · γτ)`. The resulting function has a nonzero leading coefficient
with exponent `gcd(c,t)²/(24t)` in `exp(2πiτ)`. The exponents add with the prescribed
integer multiplicities in an eta quotient. No modularity condition on that quotient is needed.

## References

* K. Ono, *The Web of Modularity*, Theorem 1.65 (Ligozat's cusp order formula).
* J. Rouse and J. J. Webb, *On spaces of modular forms spanned by eta-quotients*, §1.
-/

public section

open Complex Filter Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped BigOperators MatrixGroups Real Topology ModularForm

namespace TauCeti.ModularForm

/-- After removing its initial exponential on a positive affine argument, eta tends to `1`.
The limit is taken as the imaginary part tends to infinity, with no restriction on the real part. -/
theorem tendsto_eta_affine_mul_exp_neg {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Tendsto (fun z : ℍ ↦ η (x * (z : ℂ) + y) *
      cexp (-(2 * π * I * (x * (z : ℂ) + y) / 24))) atImInfty (𝓝 1) := by
  have hq := UpperHalfPlane.tendsto_exp_two_pi_I_mul_add hx y
  refine (tendsto_tprod_one_sub_pow_mul (w := fun _ ↦ 1) hq (by simpa using hq)).congr fun z ↦ ?_
  simp only [eta_eq_exp_mul_tprod, Complex.exp_neg, mul_one]
  field_simp [exp_ne_zero]

/-- For the affine factor of the reduced cusp, its slope is the determinant divided by
its lower-right entry squared. The shift is the upper-right entry divided by that entry. -/
private lemma coe_scaled_cusp_affine (γ δ : SL(2, ℤ)) {t : ℕ} [NeZero t]
    (ha : (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t)
    (hc : γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t) (z : ℍ) :
    let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
    (↑(β • z) : ℂ) = (Int.gcd (γ 1 0) t : ℂ) ^ 2 / t * z + β 0 1 / β 1 1 := by
  intro β
  have hβ : β 1 0 = 0 ∧ β 1 1 = (t : ℝ) / Int.gcd (γ 1 0) t :=
    γ.scaled_cusp_upperTriangular δ ha hc
  obtain ⟨h10, h11⟩ := hβ
  have hd : β.det.val = t := by simp [β]
  have hg : 0 < Int.gcd (γ 1 0) t := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast NeZero.ne t)
  have h00 : β 0 0 = Int.gcd (γ 1 0) t := by
    have h := hd
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11, mul_zero, sub_zero] at h
    have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
    have hg' : (Int.gcd (γ 1 0) t : ℝ) ≠ 0 := by positivity
    field_simp [hg', ht] at h
    exact h
  rw [coe_smul_of_det_pos (hd ▸ (by exact_mod_cast NeZero.pos t : 0 < (t : ℝ))), num, denom]
  simp only [h00, h10, ofReal_natCast, ofReal_zero, zero_mul, zero_add, add_div]
  congr 1
  rw [h11, ofReal_div, ofReal_natCast, ofReal_natCast, div_div_eq_mul_div]
  ring

/-- In the reduced cusp coordinate the linear automorphy factor differs by the positive
scalar `gcd(c,t)/t`, so the same scalar can be separated under the principal root. -/
private lemma scaled_cusp_automorphy (γ δ : SL(2, ℤ)) {t : ℕ} [NeZero t]
    (ha : (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t)
    (hc : γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t) (z : ℍ) :
    let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
    (δ 1 0 : ℂ) * (β • z : ℍ) + δ 1 1 =
      ((Int.gcd (γ 1 0) t : ℝ) / t : ℝ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  intro β
  let g := Int.gcd (γ 1 0) t
  obtain ⟨h10, h11⟩ : β 1 0 = 0 ∧ β 1 1 = (t : ℝ) / g :=
    γ.scaled_cusp_upperTriangular δ ha hc
  have hfactor : mapGL ℝ δ * β = scaleGL t * mapGL ℝ γ := mul_inv_cancel_left ..
  have h := denom_cocycle_σ (mapGL ℝ δ) β z
  have hβpos : 0 < β.det.val := by simpa [β] using (Nat.cast_pos.mpr (NeZero.pos t) : 0 < (t : ℝ))
  rw [hfactor, denom_cocycle_σ, denom_scaleGL, map_one, one_mul,
    σ_eq_refl_of_det_pos (by rwa [← GeneralLinearGroup.val_det_apply]),
    ContinuousAlgEquiv.refl_apply] at h
  have h' : (γ 1 0 : ℂ) * z + γ 1 1 =
      ((δ 1 0 : ℂ) * (β • z : ℍ) + δ 1 1) * ((t : ℂ) / g) := by
    simpa [denom, h10, h11] using h
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hg : (g : ℂ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (γ 1 0) (by exact_mod_cast NeZero.ne t)).ne'
  push_cast
  rw [h']
  field_simp
  simp only [g]

/-- At the cusp represented by `γ`, the dilation `η(tz)` has leading exponent
`gcd(γ₁₀,t)²/(24t)` in `exp(2πiz)` after dividing by the principal root of the
linear automorphy factor. The leading coefficient is nonzero. -/
theorem exists_tendsto_eta_dilate_at_cusp (γ : SL(2, ℤ)) {t : ℕ} (ht : 0 < t) :
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun z : ℍ ↦
      η ((t : ℂ) * (γ • z : ℍ)) / Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) *
        cexp (-(2 * π * I * ((Int.gcd (γ 1 0) t : ℂ) ^ 2 / (24 * t)) * z)))
      atImInfty (𝓝 C) := by
  have : NeZero t := ⟨ht.ne'⟩
  obtain ⟨δ, ha, hc⟩ := γ.exists_scaled_cusp_reduction (t := t)
  let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
  let g := Int.gcd (γ 1 0) t
  let y : ℝ := β 0 1 / β 1 1
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast ht.ne')
  have hx : 0 < (g : ℝ) ^ 2 / t :=
    div_pos (pow_pos (Nat.cast_pos.mpr hg) _) (Nat.cast_pos.mpr ht)
  have hfactor : mapGL ℝ δ * β = scaleGL t * mapGL ℝ γ := mul_inv_cancel_left ..
  let K := etaMultiplier δ * Complex.sqrt ((g : ℝ) / t : ℝ) * cexp (2 * π * I * y / 24)
  have hratio : 0 < (g : ℝ) / t := div_pos (Nat.cast_pos.mpr hg) (Nat.cast_pos.mpr ht)
  refine ⟨K, mul_ne_zero (mul_ne_zero (etaMultiplier_ne_zero _)
    (Complex.sqrt_eq_zero_iff.not.2 (ofReal_ne_zero.mpr hratio.ne'))) (exp_ne_zero _), ?_⟩
  have hlim := (tendsto_eta_affine_mul_exp_neg hx y).const_mul K
  refine (mul_one K ▸ hlim).congr fun z ↦ ?_
  have hβ : (↑(β • z) : ℂ) = (g : ℂ) ^ 2 / t * z + y := by
    simpa [β, g, y] using coe_scaled_cusp_affine γ δ ha hc z
  have hz : (↑(δ • (β • z) : ℍ) : ℂ) = t * (γ • z : ℍ) := by
    rw [← coe_scaleGL_smul (d := t), MulAction.compHom_smul_def (f := mapGL ℝ),
      MulAction.compHom_smul_def (f := mapGL ℝ), ← mul_smul, ← mul_smul, hfactor]
  have hden : (δ 1 0 : ℂ) * (β • z : ℍ) + δ 1 1 =
      ((g : ℝ) / t : ℝ) * ((γ 1 0 : ℂ) * z + γ 1 1) := scaled_cusp_automorphy γ δ ha hc z
  have hsqrt : Complex.sqrt ((δ 1 0 : ℂ) * (β • z : ℍ) + δ 1 1) =
      Complex.sqrt ((g : ℝ) / t : ℝ) * Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
    simp only [hden, Complex.sqrt, ofReal_mul_cpow (by positivity : 0 ≤ (g : ℝ) / t)]
  have hne : Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := by
    apply Complex.sqrt_eq_zero_iff.not.2
    simpa [denom] using denom_ne_zero (mapGL ℝ γ) z
  have hexp : 2 * π * I * ((g : ℂ) ^ 2 / t * z + y) / 24 =
      2 * π * I * y / 24 + 2 * π * I * ((g : ℂ) ^ 2 / (24 * t)) * z := by ring
  rw [← hz, eta_smul, hsqrt, hβ]
  push_cast
  rw [hexp, neg_add, Complex.exp_add, Complex.exp_neg]
  dsimp only [K, g]
  push_cast
  -- Cancel the automorphy root on the right and the exponential of the shift on the left.
  rw [← mul_assoc (etaMultiplier δ), mul_right_comm _ _ (η _), mul_div_cancel_right₀ _ hne]
  field_simp [exp_ne_zero]

/-- The leading exponents of the scaled eta factors add with their integer multiplicities.
The normalizing power of the principal square root is `∑ t ∈ s, r t`, which need not be even. -/
theorem exists_tendsto_eta_prod_at_cusp (γ : SL(2, ℤ)) (s : Finset ℕ) (r : ℕ → ℤ)
    (hs : ∀ t ∈ s, 0 < t) :
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun z : ℍ ↦
      (∏ t ∈ s, η ((t : ℂ) * (γ • z : ℍ)) ^ r t) /
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) ^ (∑ t ∈ s, r t) *
        cexp (-(2 * π * I * (∑ t ∈ s, (r t : ℂ) * (Int.gcd (γ 1 0) t : ℂ) ^ 2 /
          (24 * t)) * z))) atImInfty (𝓝 C) := by
  classical
  choose C hC hlim using fun t (ht : t ∈ s) ↦ exists_tendsto_eta_dilate_at_cusp γ (hs t ht)
  let C' (t : ℕ) := if h : t ∈ s then C t h else 1
  refine ⟨∏ t ∈ s, C' t ^ r t, Finset.prod_ne_zero_iff.mpr fun t ht ↦ ?_, ?_⟩
  · simpa only [C', dite_eq_left ht] using zpow_ne_zero (r t) (hC t ht)
  let F (t : ℕ) (z : ℍ) :=
    (η ((t : ℂ) * (γ • z : ℍ)) / Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) *
      cexp (-(2 * π * I * ((Int.gcd (γ 1 0) t : ℂ) ^ 2 / (24 * t)) * z))) ^ r t
  have hp := tendsto_finsetProd (f := F) (a := fun t ↦ C' t ^ r t) s fun t ht ↦ by
    simpa only [C', dite_eq_left ht] using (hlim t ht).zpow₀ (r t) (Or.inl (hC t ht))
  refine hp.congr fun z ↦ ?_
  have hroot : Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) ≠ 0 := by
    apply Complex.sqrt_eq_zero_iff.not.2
    simpa [denom] using denom_ne_zero (mapGL ℝ γ) z
  simp only [F, mul_zpow, div_zpow, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ hroot.isUnit, ← Complex.exp_intCast_mul]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Ligozat's cusp-order formula.** At a cusp represented by a matrix `γ` with positive
denominator `d = |γ₁₀|` dividing the positive level `N`, remove the indicated exponential
in the width-`w` parameter `exp(2πiz/w)` and the principal square root to the power `∑ r`.
The eta quotient then has a finite nonzero limit. No congruence or parity condition on the
exponents is imposed. At `N = 0` the statement reduces to the empty product. -/
theorem exists_tendsto_etaQuotient_at_cusp (N : ℕ) (γ : SL(2, ℤ)) (r : ℕ → ℤ)
    (hdN : (γ 1 0).natAbs ∣ N) :
    let d := (γ 1 0).natAbs
    let w := N / Nat.gcd N (d ^ 2)
    let a : ℂ := (N / 24 : ℂ) * ∑ t ∈ N.divisors,
      (r t : ℂ) * (Nat.gcd d t : ℂ) ^ 2 / ((Nat.gcd d (N / d) : ℂ) * d * t)
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun z : ℍ ↦
      (∏ t ∈ N.divisors, η ((t : ℂ) * (γ • z : ℍ)) ^ r t) /
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) ^ (∑ t ∈ N.divisors, r t) *
        cexp (-(2 * π * I * a * z / w))) atImInfty (𝓝 C) := by
  intro d w a
  obtain ⟨C, hC, hlim⟩ := exists_tendsto_eta_prod_at_cusp γ N.divisors r
    (fun t ht ↦ Nat.pos_of_mem_divisors ht)
  refine ⟨C, hC, hlim.congr fun z ↦ ?_⟩
  rcases eq_or_ne N 0 with rfl | hN
  · simp [a]
  have hd : 0 < d := Nat.pos_of_ne_zero fun h ↦ hN (Nat.zero_dvd.mp (h ▸ hdN))
  have hg : Nat.gcd N (d ^ 2) = d * Nat.gcd d (N / d) := by
    calc
      Nat.gcd N (d ^ 2) = Nat.gcd (d * (N / d)) (d * d) := by
        rw [Nat.mul_div_cancel' hdN, sq]
      _ = _ := by rw [Nat.gcd_mul_left, Nat.gcd_comm (N / d)]
  have hgpos : 0 < Nat.gcd N (d ^ 2) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)
  have hgc : (Nat.gcd N (d ^ 2) : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hw : (w : ℂ) = (N : ℂ) / Nat.gcd N (d ^ 2) :=
    Nat.cast_div (Nat.gcd_dvd_left _ _) hgc
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hg' : (Nat.gcd d (N / d) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left _ hd).ne'
  have ha : a = (w : ℂ) * ∑ t ∈ N.divisors,
      (r t : ℂ) * (Nat.gcd d t : ℂ) ^ 2 / (24 * t) := by
    dsimp only [a]
    rw [hw, hg, Nat.cast_mul, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht ↦ by
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ht).ne'
      field_simp
  have hw' : (w : ℂ) ≠ 0 := by
    rw [hw]
    exact div_ne_zero hN' hgc
  rw [ha]
  simp only [Int.gcd, Int.natAbs_natCast]
  congr 2
  field_simp
  dsimp only [d]
  ring

/-- In integral weight, the leading term calculation applies directly to the native slash
translate. No modularity assumption is needed to take this slash or its limit. -/
theorem exists_tendsto_slash_eta_prod_at_cusp (γ : SL(2, ℤ)) (s : Finset ℕ) (r : ℕ → ℤ)
    (hs : ∀ t ∈ s, 0 < t) {k : ℤ} (hk : ∑ t ∈ s, r t = 2 * k) :
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun z : ℍ ↦
      ((fun τ : ℍ ↦ ∏ t ∈ s, η ((t : ℂ) * τ) ^ r t) ∣[k] γ) z *
        cexp (-(2 * π * I * (∑ t ∈ s, (r t : ℂ) * (Int.gcd (γ 1 0) t : ℂ) ^ 2 /
          (24 * t)) * z))) atImInfty (𝓝 C) := by
  obtain ⟨C, hC, hlim⟩ := exists_tendsto_eta_prod_at_cusp γ s r hs
  refine ⟨C, hC, hlim.congr fun z ↦ ?_⟩
  rw [_root_.ModularForm.SL_slash_apply, hk, _root_.zpow_mul, zpow_two, ← pow_two,
    Complex.sq_sqrt, _root_.zpow_neg, div_eq_mul_inv]
  simp [denom]

-- At the cusp 0 of Γ₀(23), η(z)η(23z) has order 1 in the parameter of width 23.
example : ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun z : ℍ ↦
    ((fun τ : ℍ ↦ η τ * η (23 * (τ : ℂ))) ∣[(1 : ℤ)] ModularGroup.S) z *
      cexp (-(2 * π * I * z / 23))) atImInfty (𝓝 C) := by
  have hs : ∀ t ∈ ({1, 23} : Finset ℕ), 0 < t := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide
  obtain ⟨C, hC, hlim⟩ := exists_tendsto_slash_eta_prod_at_cusp
    ModularGroup.S {1, 23} (fun _ ↦ 1) hs (k := 1) (by norm_num)
  refine ⟨C, hC, hlim.congr fun z ↦ ?_⟩
  norm_num [ModularGroup.coe_S, Int.gcd, Nat.gcd_succ, mul_comm (23 : ℂ)]
  left
  congr 1
  ring

end TauCeti.ModularForm
