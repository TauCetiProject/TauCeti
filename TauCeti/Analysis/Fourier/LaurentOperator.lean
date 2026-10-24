/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.MeasureTheory.Function.LpSeminorm.Multiplier

/-!
# Laurent operators on circle `L²`

A *Laurent operator* is multiplication by an essentially bounded symbol on `L²` of the circle;
in the Fourier basis `e_n = exp (2πinx/T)` it has the bi-infinite Toeplitz matrix of the Fourier
coefficients of its symbol. This file characterizes Laurent operators in two ways.

* `TauCeti.eLpNorm_top_le_of_forall_mem_span_fourier`: the **multiplier criterion**. If a
  measurable function `a` satisfies `‖a q‖_p ≤ C ‖q‖_p` for every trigonometric polynomial `q`,
  for some `1 ≤ p < ∞`, then `a` is essentially bounded with `‖a‖∞ ≤ C`. No integrability of
  `a` is assumed.
* `TauCeti.commute_multiplicationOperator_fourierLp_one_iff`: a bounded operator on circle `L²`
  commutes with the bilateral shift, multiplication by `e_1`, if and only if it is the
  multiplication operator of an essentially bounded symbol.

For the second statement, an operator `W` commuting with the bilateral shift sends `e_n` to
`e_n b` with `b = W e_0`, hence sends every trigonometric polynomial `q` to `b q`. Since
`‖b q‖₂ ≤ ‖W‖ ‖q‖₂`, the multiplier criterion makes `b` essentially bounded, and `W` agrees
with multiplication by `b` on the dense span of the Fourier basis.

These are the characterizations of bounded Laurent matrices through which Toeplitz operators on
the Hardy space are recognized, as in the Brown–Halmos theorem. See A. Brown and P. R. Halmos,
*Algebraic properties of Toeplitz operators*, J. Reine Angew. Math. 213 (1964), and
A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.
-/

public section

open MeasureTheory AddCircle Set Submodule
open scoped ENNReal

namespace TauCeti

variable {T : ℝ} [Fact (0 < T)]

/-- **Multiplier criterion on the circle.** If multiplication by a measurable function `a` on
the circle satisfies `‖a q‖_p ≤ C ‖q‖_p` for every trigonometric polynomial `q`, for some
exponent `1 ≤ p < ∞`, then `a` is essentially bounded by `C`. -/
theorem eLpNorm_top_le_of_forall_mem_span_fourier {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {a : AddCircle T → ℂ} (ha : AEStronglyMeasurable a haarAddCircle) {C : ℝ≥0∞}
    (h : ∀ q ∈ span ℂ (range (fourier (T := T))),
      eLpNorm (a * ⇑q) p haarAddCircle ≤ C * eLpNorm (⇑q) p haarAddCircle) :
    eLpNorm a ∞ haarAddCircle ≤ C := by
  refine eLpNorm_top_le_of_dense_of_eLpNorm_mul_le hp ha
    (D := span ℂ (range (fourierLp (T := T) p)))
    (dense_iff_topologicalClosure_eq_top.2 (span_fourierLp_closure_eq_top hp)) fun f hf ↦ ?_
  -- The Fourier monomials in `Lᵖ` are the images of the continuous ones; `fourierLp` is an
  -- abbreviation for `ContinuousMap.toLp` applied to `fourier`, which closes the goal by `rfl`.
  have hspan : span ℂ (range (fourierLp (T := T) p)) =
      (span ℂ (range (fourier (T := T)))).map
        (ContinuousMap.toLp (E := ℂ) (α := AddCircle T) p haarAddCircle ℂ).toLinearMap := by
    rw [map_span, ← range_comp]
    rfl
  rw [hspan] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  have hae := ContinuousMap.coeFn_toLp (E := ℂ) (p := p) (𝕜 := ℂ) haarAddCircle q
  rw [ContinuousLinearMap.coe_coe, eLpNorm_congr_ae hae,
    eLpNorm_congr_ae (Filter.EventuallyEq.rfl.mul hae)]
  exact h q hq

/-- Multiplying an `L²` function successively by the Fourier monomials `e_n` and `e_m` is
multiplying it by `e_(m + n)`. -/
private theorem fourierLp_smul_fourierLp_smul (m n : ℤ) (f : Lp ℂ 2 (haarAddCircle (T := T))) :
    (fourierLp (T := T) ∞ m • (fourierLp (T := T) ∞ n • f) :
        Lp ℂ 2 (haarAddCircle (T := T))) = fourierLp (T := T) ∞ (m + n) • f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ m) (fourierLp (T := T) ∞ n • f),
    Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ n) f,
    Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ (m + n)) f,
    coeFn_fourierLp (T := T) ∞ m, coeFn_fourierLp (T := T) ∞ n,
    coeFn_fourierLp (T := T) ∞ (m + n)] with x h₁ h₂ h₃ hm hn hmn
  simp only [h₁, h₂, h₃, Pi.smul_apply', hm, hn, hmn, fourier_add, smul_eq_mul, mul_assoc]

/-- **Commutant of the bilateral shift.** A bounded operator on circle `L²` commutes with the
bilateral shift, multiplication by the Fourier monomial `e_1`, if and only if it is
multiplication by an essentially bounded symbol. -/
theorem commute_multiplicationOperator_fourierLp_one_iff
    {W : Lp ℂ 2 (haarAddCircle (T := T)) →L[ℂ] Lp ℂ 2 (haarAddCircle (T := T))} :
    Commute W (Lp.multiplicationOperator (fourierLp (T := T) ∞ 1)) ↔
      ∃ a : Lp ℂ ∞ (haarAddCircle (T := T)), W = Lp.multiplicationOperator a := by
  refine ⟨fun hW ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ Lp.commute_multiplicationOperator a _⟩
  set U := Lp.multiplicationOperator (E := ℂ) (fourierLp (T := T) ∞ 1)
  set b := W (fourierBasis 0)
  have hU (f : Lp ℂ 2 (haarAddCircle (T := T))) : U f = fourierLp (T := T) ∞ 1 • f :=
    Lp.multiplicationOperator_apply _ f
  have hU_inj : Function.Injective U :=
    (AddMonoidHomClass.isometry_of_norm U
      (Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one
        (ae_norm_fourierLp_eq_one ∞ 1))).injective
  -- Commuting with the shift, `W` sends each Fourier monomial `e_n` to `e_n b`.
  have hW_basis (n : ℤ) : W (fourierBasis n) = fourierLp (T := T) ∞ n • b := by
    induction n using Int.induction_on with
    | zero =>
      apply Lp.ext
      filter_upwards [Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ 0) b,
        coeFn_fourierLp (T := T) ∞ 0] with x h h₀
      rw [h, Pi.smul_apply', h₀, fourier_zero, one_smul]
    | succ n ih =>
      rw [← add_comm 1, ← fourierLp_smul_fourierBasis, ← hU, ← mul_apply_eq_comp,
        hW.eq, mul_apply_eq_comp, ih, hU, fourierLp_smul_fourierLp_smul]
    | pred n ih =>
      apply hU_inj
      rw [← mul_apply_eq_comp, ← hW.eq, mul_apply_eq_comp, hU,
        fourierLp_smul_fourierBasis, hU, fourierLp_smul_fourierLp_smul]
      convert ih using 3 <;> ring
  -- By linearity, `W` multiplies every trigonometric polynomial by `b`.
  have hW_span : ∀ q ∈ span ℂ (range (fourier (T := T))),
      ⇑(W (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ q)) =ᵐ[haarAddCircle] ⇑b * ⇑q := by
    intro q hq
    induction hq using span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      have hn : ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ (fourier (T := T) n) =
          fourierBasis n := by
        rw [coe_fourierBasis]
      rw [hn, hW_basis]
      filter_upwards [Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ n) b,
        coeFn_fourierLp (T := T) ∞ n] with x h hx
      rw [h, Pi.smul_apply', hx, smul_eq_mul, Pi.mul_apply, mul_comm]
    | zero =>
      rw [map_zero, map_zero]
      filter_upwards [Lp.coeFn_zero ℂ 2 (haarAddCircle (T := T))] with x hx
      rw [hx, Pi.zero_apply, Pi.mul_apply, ContinuousMap.zero_apply, mul_zero]
    | add q r _ _ hq hr =>
      rw [map_add, map_add]
      filter_upwards [Lp.coeFn_add (W (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ q))
        (W (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ r)), hq, hr] with x h hqx hrx
      rw [h, Pi.add_apply, hqx, hrx]
      simp only [Pi.mul_apply, ContinuousMap.add_apply, mul_add]
    | smul c q _ hq =>
      rw [map_smul, map_smul]
      filter_upwards [Lp.coeFn_smul c (W (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ q)),
        hq] with x h hqx
      rw [h, Pi.smul_apply, hqx]
      simp only [Pi.mul_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm]
  -- The multiplier criterion makes `b` essentially bounded by `‖W‖`.
  have hb : eLpNorm (⇑b) ∞ haarAddCircle ≤ ‖W‖ₑ := by
    refine eLpNorm_top_le_of_forall_mem_span_fourier (p := 2) ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable b) fun q hq ↦ ?_
    rw [← eLpNorm_congr_ae (hW_span q hq), ← Lp.enorm_def,
      ← eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) haarAddCircle q),
      ← Lp.enorm_def]
    exact W.le_opENorm _
  have hb_mem : MemLp (⇑b) ∞ haarAddCircle := memLp_iff.2 (hb.trans_lt enorm_lt_top)
  refine ⟨hb_mem.toLp b, ContinuousLinearMap.ext_on
    (dense_iff_topologicalClosure_eq_top.2 (fourierBasis (T := T)).dense_span) ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [hW_basis, Lp.multiplicationOperator_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (fourierLp (T := T) ∞ n) b,
    Lp.coeFn_lpSMul (r := 2) (hb_mem.toLp b) (fourierBasis n), hb_mem.coeFn_toLp,
    coeFn_fourierLp (T := T) ∞ n, coeFn_fourierLp (T := T) 2 n] with x h₁ h₂ hbx hinf h₂'
  rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', hbx, coe_fourierBasis, hinf, h₂', smul_eq_mul,
    smul_eq_mul, mul_comm]

end TauCeti
