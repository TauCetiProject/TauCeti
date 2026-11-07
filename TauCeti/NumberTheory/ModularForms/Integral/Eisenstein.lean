/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Dimension

import TauCeti.Analysis.Fourier.ZMod
import TauCeti.NumberTheory.LSeries.ZMod
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Eisenstein series are integral at every cusp

Let `R ⊆ ℂ` be a subring containing the `N`-th roots of unity, and let `W` be an `R`-valued
function of residue pairs modulo `N`. For `k ≥ 3`, a nonzero multiple of the weighted Eisenstein
series `G_W(z) = ∑_{x ∈ ℤ²} W(x mod N) (x₀ z + x₁)^(-k)` has all its `q`-expansion coefficients
at all cusps in `R` (`TauCeti.EisensteinSeries.exists_smul_mem_integralAtCusps`). Slashing
by `γ ∈ SL₂(ℤ)` only replaces `W` by another `R`-valued weight, so it suffices to look at the
expansion at `∞`, read at the period `N`. There, by
`TauCeti.EisensteinSeries.qExpansion_coeff_of_coe_eq_weightedEisensteinSeries`, the
nonconstant coefficients are `(-2πi)^k / ((k-1)! N^k)` times sums of discrete Fourier
coefficients of `R`-valued functions, which lie in `R`. The constant coefficient
`∑_{d ∈ ℤ} W(0, d) d^(-k)` is, by `ZMod.hasSum_mul_zpow_neg_bernoulli`, `(2πi)^k` times a
combination of discrete Fourier coefficients with rational coefficients that depend only on `N` and
`k`, so one denominator clears it for every weight (`ZMod.exists_natCast_mul_tsum_div_mem`). This
gives one multiplier that works at every cusp at once.

The Eisenstein series with character that span the Eisenstein subspace of `M_k(Γ₁(N))` are
weighted series of this kind, with weights given by character values. Hence, once `R` also
contains the values of the Dirichlet characters modulo divisors of `N`, the Eisenstein subspace is
contained in the `ℂ`-span of the forms integral at every cusp
(`TauCeti.EisensteinSeries.congruenceEisensteinSubspace_le_span_integralAtCusps`). By the
cusp–Eisenstein decomposition, the forms integral at every cusp then span `M_k(Γ₁(N))` exactly
when their span contains the cusp forms
(`TauCeti.ModularForm.span_integralAtCusps_Gamma1_eq_top_iff`). Deligne and Serre need that
spanning statement to make the forms integral at every cusp a lattice carrying the Hecke
eigenvalues.

## Main results

* `TauCeti.EisensteinSeries.exists_smul_mem_integralAtCusps`: a form whose values are
  those of a weighted Eisenstein series with `R`-valued weight has a nonzero multiple integral
  at every cusp.
* `TauCeti.EisensteinSeries.CharIndex.exists_smul_form_mem_integralAtCusps`: the same for the
  normalized raised Eisenstein series with character.
* `TauCeti.EisensteinSeries.congruenceEisensteinSubspace_le_span_integralAtCusps`: the
  Eisenstein subspace of `M_k(Γ₁(N))` lies in the span of the forms integral at every cusp.
* `TauCeti.ModularForm.span_integralAtCusps_Gamma1_eq_top_iff`: in weight `k ≥ 3`, the forms
  integral at every cusp span `M_k(Γ₁(N))` exactly when their span contains the cusp forms.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2, §4.5.
-/

public section

open Complex ZMod Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.EisensteinSeries

variable {R : Subring ℂ} {N : ℕ} [NeZero N]

/-- **Weighted Eisenstein series are integral at every cusp, up to a scalar.** Let `k ≥ 3`, let
`Γ ⊇ Γ(N)`, let `R ⊆ ℂ` be a subring containing the `N`-th roots of unity, and let `f` be a
modular form on `Γ` whose values are those of the weighted Eisenstein series
`∑_{x ∈ ℤ²} W(x mod N) (x₀ z + x₁)^(-k)` for an `R`-valued weight `W`. Then a nonzero multiple of
`f` has all the coefficients of its `q`-expansions at all cusps in `R`. -/
theorem exists_smul_mem_integralAtCusps {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    [Γ.IsArithmetic] (hΓ : (Gamma N : Subgroup (GL (Fin 2) ℝ)) ≤ Γ) {k : ℕ} (hk : 3 ≤ k)
    (hR : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ R) {W : (Fin 2 → ZMod N) → ℂ} (hW : ∀ a, W a ∈ R)
    {f : ModularForm Γ k} (hf : ⇑f = weightedEisensteinSeries W k) :
    ∃ c : ℂ, c ≠ 0 ∧ c • f ∈ ModularForm.integralAtCusps R Γ k := by
  -- a common denominator `D` of the constant terms, which depends only on `N` and `k`
  obtain ⟨D, hD0, hD⟩ := exists_natCast_mul_tsum_div_mem hR (by omega : 2 ≤ k)
  set C : ℂ := (-2 * π * I) ^ k / ((k - 1).factorial * N ^ k) with hCdef
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hfac : ((k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow : (-2 * π * I : ℂ) ^ k = (2 * π * I) ^ k * (-1) ^ k := by
    rw [← mul_pow]
    ring
  have hs0 : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hC : C ≠ 0 := by
    rw [hCdef, hpow]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hπ) hs0) (mul_ne_zero hfac (pow_ne_zero _ hN))
  refine ⟨D / C, div_ne_zero (Nat.cast_ne_zero.mpr hD0) hC, ?_⟩
  rw [ModularForm.mem_integralAtCusps_iff_qExpansion_coeff_mem hΓ]
  intro γ n
  have hNγ := natCast_mem_strictPeriods_conjAct_of_Gamma_le hΓ γ
  -- the translate by `γ` is the weighted series of the translated weight, again `R`-valued
  obtain ⟨W', hW', hfγ⟩ : ∃ W' : (Fin 2 → ZMod N) → ℂ, (∀ a, W' a ∈ R) ∧
      ⇑(translate f (mapGL ℝ γ)) = weightedEisensteinSeries W' k := by
    refine ⟨_, ?_, by
      rw [ModularForm.coe_translate, hf]
      exact (ModularForm.SL_slash _ γ).symm.trans (weightedEisensteinSeries_slash_apply W k γ)⟩
    exact fun a ↦ hW _
  have htr : translate ((D / C : ℂ) • f) (mapGL ℝ γ) =
      (D / C : ℂ) • translate f (mapGL ℝ γ) := by
    have h := (translateₗ (k := k) (mapGL ℝ γ) (by simp)).map_smul (D / C : ℂ) f
    rwa [translateₗ_apply, translateₗ_apply] at h
  rw [htr, FunLike.coe_smul, ModularForm.qExpansion_smul (Nat.cast_pos.mpr (NeZero.pos N)) hNγ,
    PowerSeries.coeff_smul, smul_eq_mul,
    qExpansion_coeff_of_coe_eq_weightedEisensteinSeries _ hNγ hk hfγ]
  split_ifs with hn
  · -- the constant term: `D / C = ± (k-1)! N^k D (2πi)⁻ᵏ`
    set S := ∑' d : ℤ, W' ![0, (d : ZMod N)] * (d : ℂ) ^ (-(k : ℤ))
    have hsq : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have h : (D / C : ℂ) * S =
        ((k - 1).factorial * N ^ k * (-1) ^ k) * (D * S / (2 * π * I) ^ k) := by
      rw [hCdef, hpow]
      field_simp
      linear_combination (-S) * hsq
    rw [h]
    exact R.mul_mem (R.mul_mem (R.mul_mem (natCast_mem R _) (R.pow_mem (natCast_mem R _) _))
      (R.pow_mem (R.neg_mem R.one_mem) _)) (hD (fun d ↦ W' ![0, d]) fun _ ↦ hW' _)
  · -- the nonconstant coefficients are `C` times sums of Fourier coefficients
    rw [← mul_assoc, div_mul_cancel₀ _ hC]
    refine R.mul_mem (natCast_mem R D) (R.sum_mem fun x _ ↦ R.mul_mem (dft_apply_mem hR (fun d ↦
      R.add_mem (hW' _) (R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) k) (hW' _))) _)
      (R.pow_mem (natCast_mem R _) _))

namespace CharIndex

/-- **The Eisenstein series with character are integral at every cusp, up to a scalar.** If
the subring `R ⊆ ℂ` contains the roots of unity of order dividing `N φ(N)`, a nonzero multiple of
each normalized raised Eisenstein series `E_k^(ψ, φ, t)` of level `N` and weight `k ≥ 3` has all
the coefficients of its `q`-expansions at all cusps in `R`. These roots of unity contain the
`N`-th roots of unity and all values of Dirichlet characters modulo divisors of `N`. -/
theorem exists_smul_form_mem_integralAtCusps {k : ℕ} (a : CharIndex N k) (hk : 3 ≤ (k : ℤ))
    (hR : ∀ ζ : ℂ, ζ ^ (N * N.totient) = 1 → ζ ∈ R) :
    ∃ c : ℂ, c ≠ 0 ∧
      c • a.form hk ∈ ModularForm.integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k := by
  -- the values of a Dirichlet character modulo a divisor of `N` lie in `R`
  have hchar {m : ℕ} (hm : m ∣ N) (χ : DirichletCharacter ℂ m) (x : ZMod m) : χ x ∈ R := by
    by_cases hx : IsUnit x
    · obtain ⟨u, rfl⟩ := hx
      refine hR _ ?_
      obtain ⟨e, he⟩ := (Nat.totient_dvd_of_dvd hm).mul_left N
      rw [he, pow_mul, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
        Units.val_one, map_one, one_pow]
    · rw [χ.map_nonunit hx]
      exact R.zero_mem
  have hW (x : Fin 2 → ZMod N) : raisedCharWeight N a.t a.psi a.phi x ∈ R := by
    rw [raisedCharWeight_def]
    split_ifs
    · exact R.mul_mem (hchar a.u_dvd _ _) (hchar a.v_dvd _ _)
    · exact R.zero_mem
  have hf : ⇑(charEisensteinSeriesMFRaise a.psi a.phi a.t hk a.level_dvd) =
      weightedEisensteinSeries (raisedCharWeight N a.t a.psi a.phi) k := by
    rw [← ModularForm.coe_restrict (Subgroup.map_mono (Gamma_le_Gamma1 N)),
      restrict_charEisensteinSeriesMFRaise, coe_weightedEisensteinSeriesMF]
  obtain ⟨c, hc, hmem⟩ := exists_smul_mem_integralAtCusps
    (Subgroup.map_mono (Gamma_le_Gamma1 N)) (by exact_mod_cast hk)
    (fun ζ hζ ↦ hR ζ (by rw [pow_mul, hζ, one_pow])) hW hf
  -- the normalized series is a scalar multiple of the raw one
  have := NeZero.of_dvd (a.v_dvd)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ,
      a.form hk = c₀ • charEisensteinSeriesMFRaise a.psi a.phi a.t hk a.level_dvd :=
    ⟨_, by rw [a.form_def, normalizedCharEisensteinSeriesMFRaise_eq_smul]⟩
  rcases eq_or_ne c₀ 0 with h0 | h0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [hc₀, h0, zero_smul, smul_zero]
    exact zero_mem _
  · refine ⟨c / c₀, div_ne_zero hc h0, ?_⟩
    rwa [hc₀, smul_smul, div_mul_cancel₀ _ h0]

end CharIndex

/-- **The Eisenstein subspace is spanned by integral forms.** If the subring `R ⊆ ℂ` contains
the roots of unity of order dividing `N φ(N)`, then in weight `k ≥ 3` the Eisenstein subspace of
`M_k(Γ₁(N))` lies in the `ℂ`-span of the forms whose `q`-expansions at all cusps have
coefficients in `R`. -/
theorem congruenceEisensteinSubspace_le_span_integralAtCusps {k : ℕ} (hk : 3 ≤ (k : ℤ))
    (hR : ∀ ζ : ℂ, ζ ^ (N * N.totient) = 1 → ζ ∈ R) :
    congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk ≤ Submodule.span ℂ
      (ModularForm.integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k :
        Set (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  rw [← span_range_form_eq_congruenceEisensteinSubspace hk, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, hc, hmem⟩ := a.exists_smul_form_mem_integralAtCusps hk hR
  have := Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (R := ℂ) hmem)
  rwa [inv_smul_smul₀ hc] at this

end TauCeti.EisensteinSeries

namespace TauCeti.ModularForm

open TauCeti.EisensteinSeries

variable {R : Subring ℂ} {N : ℕ} [NeZero N]

/-- **Spanning by integral forms reduces to the cusp forms.** If the subring `R ⊆ ℂ` contains the
roots of unity of order dividing `N φ(N)`, then in weight `k ≥ 3` the forms whose `q`-expansions
at all cusps have coefficients in `R` span `M_k(Γ₁(N))` over `ℂ` exactly when their span contains
the cusp forms: the Eisenstein subspace is always in their span. -/
theorem span_integralAtCusps_Gamma1_eq_top_iff {k : ℕ} (hk : 3 ≤ (k : ℤ))
    (hR : ∀ ζ : ℂ, ζ ^ (N * N.totient) = 1 → ζ ∈ R) :
    Submodule.span ℂ (integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k :
        Set (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = ⊤ ↔
      cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k ≤ Submodule.span ℂ
        (integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k :
          Set (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  refine ⟨fun h ↦ h ▸ le_top, fun h ↦ eq_top_iff.mpr ?_⟩
  rw [← sup_congruenceEisensteinSubspace_cuspFormSubmodule_eq_top (Gamma_le_Gamma1 N) hk]
  exact sup_le (congruenceEisensteinSubspace_le_span_integralAtCusps hk hR) h

end TauCeti.ModularForm
