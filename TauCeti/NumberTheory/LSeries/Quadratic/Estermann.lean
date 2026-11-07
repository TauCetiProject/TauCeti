/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
public import TauCeti.NumberTheory.LSeries.Quadratic.Character
public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.LSeries.Estermann
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# Estermann's comparison of two quadratic characters

For quadratic Dirichlet characters `χ` and `ψ` such that `χ`, `ψ` and `χ.mul ψ` are all
nonprincipal, set `F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`. Its Dirichlet coefficients are
nonnegative and its only pole is a simple one at `1`, of residue
`λ = L(1, χ) L(1, ψ) L(1, χ.mul ψ)`. Estermann's inequality therefore bounds `λ` from below at any
`σ ∈ [7/8, 1)` with `F(σ) ≤ 0`, in terms of a bound for the three `L`-functions on the disc
`|s - 2| ≤ 3/2`.

Such a `σ` can be chosen once and for all, together with one character `χ`, for every `ψ`. Either
some nontrivial quadratic `L`-function has a real zero `β` just to the left of `1`, in which case
`F(β) = 0` for every `ψ` once `χ` is that character; or none has, so all of them are positive on
that interval, and `F(β) < 0` for every `β` there because `ζ(β) < 0`. Which case holds is not
decided, and this is the source of the ineffectivity of Siegel's theorem: `β` and `χ` are not
computed.

## Main results

* `TauCeti.exists_estermann_lower_bound`: the lower bound for the product of the
  three values at `1`, with an absolute constant, at any point where `F` is nonpositive.
* `TauCeti.exists_forall_re_riemannZeta_mul_LFunction_nonpos`: for every `δ > 0` there are
  `β ∈ (1 - δ, 1)` and a nontrivial quadratic character `χ` with `F(β) ≤ 0` for all `ψ`.

## References

* T. Estermann, *On Dirichlet's L functions*, J. London Math. Soc. 23 (1948), 275–279.
* H. Davenport, *Multiplicative Number Theory*, chapter on Siegel's theorem.
-/

public section

open Complex Metric Filter Set
open scoped ComplexOrder Topology

namespace DirichletCharacter

/-- The function `(s - 1) ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`, which is entire when `χ`, `ψ` and
`χ.mul ψ` are all nonprincipal. -/
private noncomputable def pairProduct {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  LFunctionTrivChar₁ 1 s * (χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s)

section Pair

variable {M N : ℕ} [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M}
  {ψ : DirichletCharacter ℂ N}

private lemma differentiable_pairProduct (hχ₁ : χ ≠ 1) (hψ₁ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) :
    Differentiable ℂ (pairProduct χ ψ) :=
  (differentiable_LFunctionTrivChar₁ 1).mul
    (((differentiable_LFunction hχ₁).mul (differentiable_LFunction hψ₁)).mul
      (differentiable_LFunction hχψ))

private lemma pairProduct_of_ne {s : ℂ} (hs : s ≠ 1) :
    pairProduct χ ψ s =
      (s - 1) * (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) := by
  rw [pairProduct, LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar,
    LFunction_modOne_eq]
  ring

private lemma re_pairProduct_one (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) :
    (pairProduct χ ψ 1).re =
      (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
  have him {L : ℕ} [NeZero L] {ρ : DirichletCharacter ℂ L} (hρ : ρ.IsQuadratic) (hρ₁ : ρ ≠ 1) :
      (ρ.LFunction 1).im = 0 := by
    simpa using LFunction_im_eq_zero_of_isQuadratic hρ 1 (.inr hρ₁)
  simp [pairProduct, mul_re, mul_im, him hχ hχ₁, him hψ hψ₁, him (isQuadratic_mul hχ hψ) hχψ]

end Pair

end DirichletCharacter

namespace TauCeti

open DirichletCharacter

/-- **The two-character comparison.** There is an absolute constant `C > 0` with the following
property. Let `χ` and `ψ` be nontrivial quadratic characters with `χ.mul ψ` nonprincipal, let `B`
bound the product of their three `L`-functions on the disc `|s - 2| ≤ 3/2`, and let `σ ∈ [7/8, 1)`
be a point where `F(σ) = ζ(σ) L(σ, χ) L(σ, ψ) L(σ, χ.mul ψ)` is nonpositive. Then
`L(1, χ) L(1, ψ) L(1, χ.mul ψ) ≥ (1 - σ) / (4 (C B)^{4 (1 - σ)})`. -/
theorem exists_estermann_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M)
      (ψ : DirichletCharacter ℂ N), χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
      χ.mul ψ ≠ 1 → ∀ {B σ : ℝ}, (∀ s ∈ closedBall (2 : ℂ) (3 / 2),
          ‖χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤ B) →
        7 / 8 ≤ σ → σ < 1 →
        (riemannZeta σ * χ.LFunction σ * ψ.LFunction σ * (χ.mul ψ).LFunction σ).re ≤ 0 →
        (1 - σ) / (4 * (C * B) ^ (4 * (1 - σ))) ≤
          (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
  obtain ⟨Z₀, hZ₀⟩ := (isCompact_closedBall (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn
    (differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn
  have hZ : 0 < max Z₀ 1 := by positivity
  refine ⟨32 * max Z₀ 1, by positivity, ?_⟩
  intro M N _ _ χ ψ hχ hψ hχ₁ hψ₁ hχψ B σ hB hσ hσ₁ hF
  have hσne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ₁.ne
  have hHa (s : ℂ) (hs : 1 < s.re) :
      pairProduct χ ψ s = (s - 1) * LSeries (χ.zetaMulPairCoeffs ψ) s := by
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    rw [pairProduct_of_ne hs1, (LSeriesHasSum_zetaMulPairCoeffs χ ψ hs).LSeries_eq]
  have habs : LSeries.abscissaOfAbsConv (χ.zetaMulPairCoeffs ψ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      (LSeriesHasSum_zetaMulPairCoeffs χ ψ (by simpa using hy)).LSeriesSummable
  have hHB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖pairProduct χ ψ s‖ ≤ max Z₀ 1 * B := fun s hs ↦ by
    rw [pairProduct, norm_mul]
    exact mul_le_mul ((hZ₀ s hs).trans (le_max_left _ _)) (hB s hs) (norm_nonneg _) hZ.le
  have hdiv : (pairProduct χ ψ σ).re / (σ - 1) ≤ 0 := by
    have hσ' : σ - 1 ≠ 0 := by linarith
    rw [pairProduct_of_ne hσne, ← ofReal_one, ← ofReal_sub, re_ofReal_mul,
      mul_div_cancel_left₀ _ hσ']
    exact hF
  have h := TauCeti.LSeries.estermann_lower_bound (a := χ.zetaMulPairCoeffs ψ)
    (zetaMulPairCoeffs_nonneg hχ hψ) (zetaMulPairCoeffs_one χ ψ) habs
    (differentiable_pairProduct hχ₁ hψ₁ hχψ) hHa hHB hσ hσ₁ hdiv
  rw [re_pairProduct_one hχ hψ hχ₁ hψ₁ hχψ] at h
  rwa [mul_assoc 32]

/-- **The exceptional alternative.** For every `δ > 0` there are a point `β ∈ (1 - δ, 1)` with
`β ≥ 7/8` and a nontrivial quadratic character `χ` such that for every nontrivial quadratic
character `ψ` with `χ.mul ψ` nonprincipal, `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)` is nonpositive. -/
theorem exists_forall_re_riemannZeta_mul_LFunction_nonpos {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : ℝ, 1 - δ < β ∧ 7 / 8 ≤ β ∧ β < 1 ∧
      ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsQuadratic ∧ χ ≠ 1 ∧
        ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsQuadratic → ψ ≠ 1 →
          χ.mul ψ ≠ 1 →
          (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 := by
  obtain ⟨σ₀, hσ₀, hζ⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp TauCeti.eventually_re_riemannZeta_neg
  have hσ₀' : σ₀ < 1 := hσ₀
  set β₀ := max σ₀ (max (1 - δ) (7 / 8))
  have hβ₀ : β₀ < 1 := max_lt hσ₀' (max_lt (by linarith) (by norm_num))
  have hβ₀σ : σ₀ ≤ β₀ := le_max_left _ _
  have hβ₀δ : 1 - δ ≤ β₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hβ₀78 : 7 / 8 ≤ β₀ := (le_max_right _ _).trans (le_max_right _ _)
  by_cases hzero : ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
      χ.IsQuadratic ∧ χ ≠ 1 ∧ β ∈ Ioo β₀ 1 ∧ χ.LFunction β = 0
  · obtain ⟨q, hq, χ, β, hχ, hχ₁, hβ, h0⟩ := hzero
    refine ⟨β, by linarith [hβ.1], by linarith [hβ.1], hβ.2, q, hq, χ, hχ, hχ₁, fun ψ _ _ _ ↦ ?_⟩
    simp [h0]
  · push Not at hzero
    let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
    have hχ : χ.IsQuadratic := ZMod.isQuadratic_χ₄.comp _
    have hχ₁ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr fun h ↦ by
      have h3 : ZMod.χ₄ (3 : ZMod 4) = 1 := by rw [h, MulChar.one_apply (by decide)]
      exact absurd h3 (by decide)
    set β := (β₀ + 1) / 2 with hβdef
    have hβ₁ : β₀ < β := by linarith
    have hβ₂ : β < 1 := by linarith
    have hpos {q : ℕ} [NeZero q] {ρ : DirichletCharacter ℂ q} (hρ : ρ.IsQuadratic)
        (hρ₁ : ρ ≠ 1) : 0 < ρ.LFunction β :=
      LFunction_pos_of_forall_ne_zero hρ hρ₁ hβ₂.le fun x hx ↦
        hzero q _ ρ x hρ hρ₁ ⟨hβ₁.trans_le hx.1, hx.2⟩
    refine ⟨β, by linarith, by linarith, hβ₂, 4, inferInstance, χ, hχ, hχ₁,
      fun ψ hψ hψ₁ hχψ ↦ ?_⟩
    have hP : 0 < χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β :=
      mul_pos (mul_pos (hpos hχ hχ₁) (hpos hψ hψ₁)) (hpos (isQuadratic_mul hχ hψ) hχψ)
    obtain ⟨hPre, hPim⟩ := Complex.pos_iff.mp hP
    have hζβ : (riemannZeta β).re < 0 := hζ ⟨hβ₀σ.trans_lt hβ₁, hβ₂⟩
    rw [show riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β =
      riemannZeta β * (χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) by ring,
      mul_re, ← hPim, mul_zero, sub_zero]
    exact (mul_neg_of_neg_of_pos hζβ hPre).le

end TauCeti
