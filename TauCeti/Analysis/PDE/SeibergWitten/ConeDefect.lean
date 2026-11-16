/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature

/-!
# The distance of the cutoff current to the cone of positive `(1,1)`-forms

In Taubes's passage from solutions of the large-parameter Seiberg–Witten equations on a symplectic
four-manifold to pseudoholomorphic curves, the curvature `i F_a` of the connection on the line `E`
is replaced by the **cutoff current** `Θ = i F_a + d(χ(|α|²) τ)`
(`TauCeti.SeibergWitten.cutoffCurrent`), whose weak limits are the currents of the limiting
curves. Such a limit is a positive `(1,1)`-current because the integrated distance of `Θ` to the
cone of positive `(1,1)`-forms (`TauCeti.AlmostComplexStructure.positiveCone`) tends to zero. This
file proves the coarse form of that estimate: with `h = (2 r)^(-1/2)`,

`∫ dist(Θ, positiveCone) = O(r^(-1/2)) = O(h)`,

using only Taubes's coarse a priori bounds, before any refined estimate of the anti-self-dual
curvature.

At a point where `s = |α|²`, the cutoff current is
`Θ(v, w) = (1 - χ(s)) i F_a(v, w) + 2 χ'(s) Im (conj (∇_v α) ∇_w α)`
(`TauCeti.SeibergWitten.cutoffCurrent_apply_pair`). The distance to a pointed cone is subadditive
and positively homogeneous (`AddSubmonoidClass.infDist_add_le`, `PointedCone.infDist_smul`), so
the two terms are estimated separately:

* the two-form `Im (conj (∇_v α) ∇_w α)` is at distance at most
  `‖∂bar_a α‖ (‖∇_a α‖ + ‖∂_a α‖)` from the cone, since its `J`-linear part is positive
  (`TauCeti.AlmostComplexStructure.infDist_positiveCone_le_of_inner_ιMulti_eq_im`);
* the curvature `i F_a` is at distance `O(r |α| |β| + √r + 1)` from the cone
  (`TauCeti.SeibergWitten.infDist_positiveCone_le_of_add_hodgeStar_eq`): its anti-`J`-invariant
  part is `r q'(φ, β)`, and the negative part of its Hermitian form is `O(√r)` under the coarse
  anti-self-dual bound `|F_a⁻| ≤ (r / (4 √2)) (1 + C r^(-1/2)) w₊ + C`.

The pointwise splitting is
`TauCeti.AlmostComplexStructure.infDist_positiveCone_le_of_inner_ιMulti_eq`, and
`TauCeti.SeibergWitten.infDist_positiveCone_cutoffCurrent_le` is its form for the cutoff current
of a pair on a finite-dimensional inner product space with an orthogonal `J`:

`dist(Θ, positiveCone) ≤ (1 - χ(s)) dist(i F_a, positiveCone) + 4 χ'(s) |∂bar_a α| |∇_a α|`.

The curvature term only contributes where `χ(s) < 1`, that is on `{|α|² ≤ 1 / 2}`, a region of
volume `O(1 / r)`, where `|1 - |α|² - |β|²| ≥ 1 / 4`. There
`r |β| / 2 ≤ √r |1 - |α|² - |β|²| + r^(3/2) |β|² / 4`, so `∫ r |β| = O(r^(-1/2))` by
`∫ |1 - |α|² - |β|²| = O(1 / r)` and `‖β‖₂² = O(1 / r²)`, and the `O(√r)` negative Hermitian
density integrates to `O(r^(-1/2))`. The derivative term is `O(r^(-1/2))`
by `‖∂bar_a α‖₂ = O(r^(-1/2))` and `‖∇_a α‖₂ = O(1)`. These coarse bounds are those of
`TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds`, and the integrated estimate is
`TauCeti.SeibergWitten.integral_infDist_positiveCone_le`. As there, the fields are functions on
an arbitrary finite measure space, written at each point in a unitary frame of the tangent space,
and Taubes's coarse estimates are hypotheses; the constant depends only on their constants, the
volume, the bound on the forcing term and the bound on `χ'`, so it is uniform in `r` and in the
solution.

## Main results

* `TauCeti.SeibergWitten.infDist_positiveCone_cutoffCurrent_le`: the pointwise bound for the cutoff
  current.
* `TauCeti.SeibergWitten.integral_infDist_positiveCone_le`: the integrated distance of the cutoff
  current to the positive cone is `O(r^(-1/2))`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open CliffordAlgebra Module Metric MeasureTheory Filter Set exteriorPower
open scoped RealInnerProductSpace ComplexConjugate

namespace TauCeti.SeibergWitten

/-! ### The pointwise estimate -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V}

/-- **The distance of the cutoff current to the positive cone.** Let `J` be an orthogonal almost
complex structure on a finite-dimensional inner product space, `(b, α)` an abelian Higgs pair with
curvature `i F_a = -db`, and `χ` a cutoff vanishing near `0` with `χ(s) ≤ 1` and `χ'(s) ≥ 0` at
`s = |α(x)|²`. Then, at `x`, the cutoff current `Θ = i F_a + d(χ(|α|²) τ)` satisfies

`dist(Θ, positiveCone) ≤ (1 - χ(s)) dist(i F_a, positiveCone) + 4 χ'(s) ‖∂bar_a α‖ ‖∇_a α‖`.

Two-forms are identified with two-vectors through the inner product
(`TauCeti.alternatingFormEquiv`). -/
theorem infDist_positiveCone_cutoffCurrent_le (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    {χ : ℝ → ℝ} {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : V → ℂ} {x : V} (hα : ContDiffAt ℝ 2 α x)
    (hb : DifferentiableAt ℝ b x) (hχ : DifferentiableAt ℝ χ (Complex.normSq (α x)))
    (hχ₀ : χ =ᶠ[nhds 0] 0) (hχ₁ : χ (Complex.normSq (α x)) ≤ 1)
    (hχ' : 0 ≤ deriv χ (Complex.normSq (α x))) :
    infDist ((alternatingFormEquiv V 2).symm (cutoffCurrent χ b α x))
        (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      (1 - χ (Complex.normSq (α x))) *
          infDist ((alternatingFormEquiv V 2).symm (-extDeriv b x))
            (J.positiveCone : Set (⋀[ℝ]^2 V)) +
        4 * deriv χ (Complex.normSq (α x)) *
          (‖covariantDBar J b α x‖ * ‖covariantDeriv b α x‖) := by
  have h := AlmostComplexStructure.infDist_positiveCone_le_of_inner_ιMulti_eq hJ
    (sub_nonneg.2 hχ₁) (mul_nonneg zero_le_two hχ')
    (covariantDeriv_sub_covariantDBar_isComplexLinear J b α x)
    (Θ := (alternatingFormEquiv V 2).symm (cutoffCurrent χ b α x))
    (F := (alternatingFormEquiv V 2).symm (-extDeriv b x)) fun u w ↦ by
      rw [inner_alternatingFormEquiv_symm_ιMulti, inner_alternatingFormEquiv_symm_ιMulti,
        cutoffCurrent_apply_pair hα hb hχ hχ₀, ContinuousAlternatingMap.neg_apply]
      ring
  refine h.trans ?_
  have hn :=
    norm_covariantDeriv_sub_covariantDBar_le J (AlmostComplexStructure.norm_apply hJ) b α x
  have hDbar := norm_nonneg (covariantDBar J b α x)
  have := mul_le_mul_of_nonneg_left hn (mul_nonneg (mul_nonneg zero_le_two hχ') hDbar)
  nlinarith

end Pointwise

/-! ### The integrated estimate -/

section Arithmetic

/-- The derivative term of the cutoff current, by the arithmetic-geometric mean inequality:
if `0 ≤ c ≤ 2 M` and `a' ≤ a`, then `c b (a + a') ≤ 2 M (q b² + a² / q)` for `q > 0`. -/
private theorem mul_mul_add_le {a a' b c q M : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a' ≤ a) (hc : 0 ≤ c) (hcM : c ≤ 2 * M) :
    c * (b * (a + a')) ≤ 2 * M * (q * b ^ 2 + a ^ 2 / q) := by
  have hamgm : 2 * (b * a) ≤ q * b ^ 2 + a ^ 2 / q := by
    have h : q * b ^ 2 + a ^ 2 / q - 2 * (b * a) = (q * b - a) ^ 2 / q := by
      field_simp
      ring
    linarith [div_nonneg (sq_nonneg (q * b - a)) hq.le]
  have hba : b * (a + a') ≤ 2 * (b * a) := by nlinarith
  calc c * (b * (a + a')) ≤ c * (2 * (b * a)) := mul_le_mul_of_nonneg_left hba hc
    _ ≤ 2 * M * (2 * (b * a)) := mul_le_mul_of_nonneg_right hcM (by positivity)
    _ ≤ 2 * M * (q * b ^ 2 + a ^ 2 / q) := by
        gcongr
        linarith

/-- The curvature term of the cutoff current, by crude bounds. Here `d` stands for the distance
of the curvature to the positive cone, `p = |φ| ≤ 1`, `t = |β|`, `w = w₊ ≤ 1`, `n = |η| ≤ N`,
`q = √r` and `δ = 1 - |φ|² - |β|²`, with `|δ| ≥ 1 / 4`. The term `r t / 2` is split as
`q / 4 + r q t² / 4` by `2 q t ≤ 1 + r t²`. -/
private theorem mul_le_of_quarter_le_abs {a d p t w n δ r q C N : ℝ} (ha1 : a ≤ 1)
    (hqq : q * q = r) (hq : 0 < q) (hC : 0 ≤ C) (hp1 : p ≤ 1) (ht : 0 ≤ t) (hw1 : w ≤ 1)
    (hn0 : 0 ≤ n) (hn : n ≤ N) (hδ : 1 / 4 ≤ |δ|) (hd0 : 0 ≤ d)
    (hd : d ≤ r * p * t / (2 * √2) + C * q * w / (4 * √2) + C + C / (2 * √2) + n) :
    a * d ≤ (q + 4 * (C * q + 2 * C + N)) * |δ| + r * q / 4 * t ^ 2 := by
  have hs2 : 1 ≤ √2 := Real.one_le_sqrt.2 one_le_two
  have hr0 : 0 ≤ r := by rw [← hqq]; positivity
  have e1 : r * p * t / (2 * √2) ≤ r * t / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have h1 : r * p * t ≤ r * t := by
      have := mul_le_mul_of_nonneg_left hp1 (mul_nonneg hr0 ht)
      linarith
    have h2 : 0 ≤ r * t := mul_nonneg hr0 ht
    nlinarith
  have e2 : C * q * w / (4 * √2) ≤ C * q := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : C * q * w ≤ C * q := mul_le_of_le_one_right (by positivity) hw1
    have h2 : 0 ≤ C * q := by positivity
    nlinarith
  have e3 : C / (2 * √2) ≤ C := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e4 : r * t / 2 ≤ q * |δ| + r * q / 4 * t ^ 2 := by
    have hb : 2 * q * t ≤ 1 + r * t ^ 2 := by
      rw [← hqq]
      nlinarith [sq_nonneg (q * t - 1)]
    have h : r * t / 2 = q * (2 * q * t) / 4 := by rw [← hqq]; ring
    rw [h]
    have h1 := mul_le_mul_of_nonneg_left hb hq.le
    have h2 := mul_le_mul_of_nonneg_left hδ hq.le
    have h3 : r * q / 4 * t ^ 2 = q * (r * t ^ 2) / 4 := by ring
    rw [h3]
    linarith
  have e5 : C * q + 2 * C + N ≤ 4 * (C * q + 2 * C + N) * |δ| := by
    have h0 : 0 ≤ C * q + 2 * C + N := by
      have : 0 ≤ N := hn0.trans hn
      positivity
    nlinarith
  calc a * d ≤ d := mul_le_of_le_one_left hd0 ha1
    _ ≤ (q + 4 * (C * q + 2 * C + N)) * |δ| + r * q / 4 * t ^ 2 := by nlinarith

/-- The final arithmetic: with `q = √r ≥ 1`, the integrals `I₁ = ∫ |δ| ≤ C / r`,
`I₂ = ∫ |β|² ≤ A / r²`, `I₃ = ∫ |Dbar|² ≤ B / r` and `I₄ = ∫ |Dα|² ≤ A` give the bound
`(C + A / 4 + 12 C² + 4 C N + 2 M (A + B)) / q` on the integral of the dominating function. -/
private theorem add_add_le_div {q r C N M A B I₁ I₂ I₃ I₄ : ℝ} (hq1 : 1 ≤ q) (hqq : q * q = r)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hM : 0 ≤ M) (hI₁ : I₁ ≤ C / r) (hI₂ : I₂ ≤ A / r ^ 2)
    (hI₃ : I₃ ≤ B / r) (hI₄ : I₄ ≤ A) :
    (q + 4 * (C * q + 2 * C + N)) * I₁ + r * q / 4 * I₂ + 2 * M * (q * I₃ + I₄ / q) ≤
      (C + A / 4 + 12 * C ^ 2 + 4 * C * N + 2 * M * (A + B)) / q := by
  have b1 : (q + 4 * (C * q + 2 * C + N)) * I₁ ≤ (C + 4 * C ^ 2 + 8 * C ^ 2 + 4 * C * N) / q := by
    calc (q + 4 * (C * q + 2 * C + N)) * I₁ ≤ (q + 4 * (C * q + 2 * C + N)) * (C / r) := by
          gcongr
      _ = (C + 4 * C ^ 2) / q + (8 * C ^ 2 + 4 * C * N) / (q * q) := by
          rw [← hqq]
          field_simp
          ring
      _ ≤ (C + 4 * C ^ 2) / q + (8 * C ^ 2 + 4 * C * N) / q := by
          gcongr
          nlinarith
      _ = (C + 4 * C ^ 2 + 8 * C ^ 2 + 4 * C * N) / q := by ring
  have b2 : r * q / 4 * I₂ ≤ A / 4 / q := by
    calc r * q / 4 * I₂ ≤ r * q / 4 * (A / r ^ 2) := by
          gcongr
          rw [← hqq]
          positivity
      _ = A / 4 / q := by
          rw [← hqq]
          field_simp
  have b3 : 2 * M * (q * I₃ + I₄ / q) ≤ 2 * M * (A + B) / q := by
    calc 2 * M * (q * I₃ + I₄ / q) ≤ 2 * M * (q * (B / r) + A / q) := by gcongr
      _ = 2 * M * (A + B) / q := by
          rw [← hqq]
          field_simp
          ring
  calc _ ≤ (C + 4 * C ^ 2 + 8 * C ^ 2 + 4 * C * N) / q + A / 4 / q + 2 * M * (A + B) / q := by
        linarith
    _ = (C + A / 4 + 12 * C ^ 2 + 4 * C * N + 2 * M * (A + B)) / q := by ring

end Arithmetic

section Integrated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

attribute [local instance] finiteDimensional_of_finrank_four

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  {χ : ℝ → ℝ} {r C M N : ℝ}

include h₀ h₂₃ hQ he hρ h₂

/-- The pointwise domination of the distance of the cutoff current to the positive cone, under
the coarse bounds at one point, by a function whose integral is controlled by the coarse
integral bounds. -/
private theorem infDist_positiveCone_le_add_add {Θ F η : ⋀[ℝ]^2 V}
    {φ β : positiveHalfSpinors o ρ} {Dα Dbar : V →L[ℝ] ℂ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hCr : 8 * C ≤ r) (hχ : ∀ s, χ s ∈ Icc 0 1) (hχ₁ : ∀ s, 1 / 2 < s → χ s = 1)
    (hχ' : ∀ s, deriv χ s ∈ Icc 0 M)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    (hη : ‖η‖ ≤ N)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C)
    (hΘ : ∀ u w, ⟪Θ, ιMulti ℝ 2 ![u, w]⟫ =
      (1 - χ (‖φ‖ ^ 2)) * ⟪F, ιMulti ℝ 2 ![u, w]⟫ +
        2 * deriv χ (‖φ‖ ^ 2) * (conj (Dα u) * Dα w).im)
    (hJlin : IsComplexLinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ Complex.I)
      ((Dα - Dbar : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ))
    (hDα' : ‖Dα - Dbar‖ ≤ ‖Dα‖)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + C / r)
    (hβK : ‖β‖ ^ 2 ≤ C / r * max (1 - ‖φ‖ ^ 2) 0 + C / r ^ 2) :
    infDist Θ (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      (√r + 4 * (C * √r + 2 * C + N)) * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| + r * √r / 4 * ‖β‖ ^ 2 +
        2 * M * (√r * ‖Dbar‖ ^ 2 + ‖Dα‖ ^ 2 / √r) := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < √r := Real.sqrt_pos.2 hr0
  have hqq : √r * √r = r := Real.mul_self_sqrt hr0.le
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  set s := ‖φ‖ ^ 2
  have ha : 0 ≤ 1 - χ s := sub_nonneg.2 (hχ s).2
  have hc : 0 ≤ 2 * deriv χ s := mul_nonneg zero_le_two (hχ' s).1
  have hdiff := mul_mul_add_le (M := M) hq0 (norm_nonneg Dα) (norm_nonneg Dbar) hDα' hc
    (by linarith [(hχ' s).2])
  refine (AlmostComplexStructure.infDist_positiveCone_le_of_inner_ιMulti_eq hJ ha hc hJlin
    hΘ).trans ?_
  -- The curvature term vanishes unless `|φ|² ≤ 1 / 2`.
  suffices hcurv : (1 - χ s) * infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      (√r + 4 * (C * √r + 2 * C + N)) * |1 - s - ‖β‖ ^ 2| + r * √r / 4 * ‖β‖ ^ 2 by
    linarith
  have hN : 0 ≤ N := (norm_nonneg η).trans hη
  rcases lt_or_ge (1 / 2) s with hs | hs
  · rw [hχ₁ s hs, sub_self, zero_mul]
    positivity
  have hw1 : max (1 - s) 0 ≤ 1 := max_le (by linarith [sq_nonneg ‖φ‖]) zero_le_one
  -- On `{|φ|² ≤ 1 / 2}`, `|β|² ≤ 1 / 4`, so `|1 - |φ|² - |β|²| ≥ 1 / 4`.
  have hβ4 : ‖β‖ ^ 2 ≤ 1 / 4 := by
    have h1 : C / r ^ 2 ≤ C / r := div_le_div_of_nonneg_left hC hr0 (by nlinarith)
    have h2 : C / r * max (1 - s) 0 ≤ C / r := mul_le_of_le_one_right (by positivity) hw1
    have h3 : C / r ≤ 1 / 8 := by rw [div_le_iff₀ hr0]; linarith
    linarith
  have hδ : 1 / 4 ≤ |1 - s - ‖β‖ ^ 2| := le_abs.2 (Or.inl (by linarith))
  have hφ1 : ‖φ‖ ≤ 1 := by nlinarith [norm_nonneg φ]
  exact mul_le_of_quarter_le_abs (by linarith [(hχ s).1]) hqq hq0 hC hφ1 (norm_nonneg β) hw1
    (norm_nonneg η) hη hδ infDist_nonneg
    (infDist_positiveCone_le_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hφ hβ hρ h₂ hr hβK hφβ hF hC
      hFm)

variable {X Fβ : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup Fβ]

/-- **The coarse distance of the cutoff current to the positive cone is `O(r^(-1/2))`.** On a
finite measure space `X`, consider at each point, written in a unitary frame `e` with
`J e₀ = e₁`, `J e₂ = e₃`, the fields of a solution of the large-parameter Seiberg–Witten equations:
the spinor components `φ = α u₀` and `β`, the curvature `F = i F_a`, the forcing `η`, the
covariant derivatives `Dα = ∇_a α` and `Dβ = ∇β`, the antilinear part `Dbar = ∂bar_a α`, and the
cutoff current `Θ`, so that

* `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` with `‖η‖ ≤ N`,
* `Θ(u, w) = (1 - χ(|φ|²)) F(u, w) + 2 χ'(|φ|²) Im (conj (Dα u) Dα w)`, for a cutoff `χ` with
  values in `[0, 1]`, equal to `1` on `(1 / 2, ∞)` and with `0 ≤ χ' ≤ M`,
* `Dα - Dbar` is `J`-linear and no longer than `Dα`.

Assume Taubes's coarse bounds with constant `C ≥ 0`, where `w₊ = max (1 - |φ|²) 0`:
`r ∫ |1 - |φ|² - |β|²| ≤ C`, `|φ|² + |β|² ≤ 1 + C / r`, `|β|² ≤ (C / r) w₊ + C / r²`,
`|Dα|² + r |Dβ|² ≤ C r w₊ + C`, `‖Dbar‖₂ ≤ C r^(-1/2) (‖Dα - Dbar‖₂ + 1)` and the coarse
anti-self-dual bound `|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`. If `r ≥ 1` and `r ≥ 8 C`, then

`∫ dist(Θ, positiveCone) ≤ (C + A / 4 + 12 C² + 4 C N + 2 M (A + B)) / √r`,

where `A = 2 C (C + Vol X)` and `B = C² (√A + 1)²`. With `h = (2 r)^(-1/2)` the right side is
`O(h)`, uniformly in the solution. -/
theorem integral_infDist_positiveCone_le [IsFiniteMeasure μ] {F η Θ : X → ⋀[ℝ]^2 V}
    {φ β : X → positiveHalfSpinors o ρ} {Dα Dbar : X → V →L[ℝ] ℂ} {Dβ : X → Fβ}
    (hr : 1 ≤ r) (hC : 0 ≤ C) (hCr : 8 * C ≤ r) (hN : 0 ≤ N)
    (hχ : ∀ s, χ s ∈ Icc 0 1) (hχ₁ : ∀ s, 1 / 2 < s → χ s = 1) (hχ' : ∀ s, deriv χ s ∈ Icc 0 M)
    (hφ : ∀ᵐ x ∂μ, cliffordProjection o ρ J.kahlerForm (φ x) = φ x)
    (hβ : ∀ᵐ x ∂μ, cliffordProjection o ρ J.kahlerForm (β x) = 0)
    (hF : ∀ᵐ x ∂μ, F x + o.hodgeStar hkl (F x) = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 V) - η x)
    (hη : ∀ᵐ x ∂μ, ‖η x‖ ≤ N)
    (hFm : ∀ᵐ x ∂μ, ‖(2⁻¹ : ℝ) • (F x - o.hodgeStar hkl (F x))‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C)
    (hΘ : ∀ᵐ x ∂μ, ∀ u w, ⟪Θ x, ιMulti ℝ 2 ![u, w]⟫ =
      (1 - χ (‖φ x‖ ^ 2)) * ⟪F x, ιMulti ℝ 2 ![u, w]⟫ +
        2 * deriv χ (‖φ x‖ ^ 2) * (conj (Dα x u) * Dα x w).im)
    (hJlin : ∀ᵐ x ∂μ, IsComplexLinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ Complex.I)
      ((Dα x - Dbar x : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ))
    (hDα' : ∀ᵐ x ∂μ, ‖Dα x - Dbar x‖ ≤ ‖Dα x‖)
    (hδ : Integrable (fun x ↦ 1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hβ2 : Integrable (fun x ↦ ‖β x‖ ^ 2) μ) (hDα2 : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ)
    (hDbar2 : Integrable (fun x ↦ ‖Dbar x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hφβ : ∀ᵐ x ∂μ, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + C / r)
    (hβK : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖φ x‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 + r * ‖Dβ x‖ ^ 2 ≤ C * r * max (1 - ‖φ x‖ ^ 2) 0 + C)
    (hDbar : √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ≤ C / √r * (√(∫ x, ‖Dα x - Dbar x‖ ^ 2 ∂μ) + 1)) :
    ∫ x, infDist (Θ x) (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ ≤
      (C + 2 * C * (C + μ.real univ) / 4 + 12 * C ^ 2 + 4 * C * N +
        2 * M * (2 * C * (C + μ.real univ) +
          C ^ 2 * (√(2 * C * (C + μ.real univ)) + 1) ^ 2)) / √r := by
  have hr0 : 0 < r := by linarith
  have hM : 0 ≤ M := (hχ' 0).1.trans (hχ' 0).2
  -- Dominate the distance by an integrable function and integrate.
  have hgi : Integrable (fun x ↦ (√r + 4 * (C * √r + 2 * C + N)) * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| +
      r * √r / 4 * ‖β x‖ ^ 2 + 2 * M * (√r * ‖Dbar x‖ ^ 2 + ‖Dα x‖ ^ 2 / √r)) μ :=
    ((hδ.abs.const_mul _).add (hβ2.const_mul _)).add
      (((hDbar2.const_mul _).add (hDα2.div_const _)).const_mul _)
  have hpt : ∀ᵐ x ∂μ, infDist (Θ x) (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      (√r + 4 * (C * √r + 2 * C + N)) * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| +
        r * √r / 4 * ‖β x‖ ^ 2 + 2 * M * (√r * ‖Dbar x‖ ^ 2 + ‖Dα x‖ ^ 2 / √r) := by
    filter_upwards [hφ, hβ, hF, hη, hFm, hΘ, hJlin, hDα', hφβ, hβK] with x hφx hβx hFx hηx
      hFmx hΘx hJx hDx hφβx hβKx
    exact infDist_positiveCone_le_add_add h₀ h₂₃ hQ hkl he hρ h₂ hr hC hCr hχ hχ₁ hχ' hφx hβx
      hFx hηx hFmx hΘx hJx hDx hφβx hβKx
  have hI₁ : ∫ x, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C / r := by
    rw [le_div_iff₀ hr0, mul_comm]
    exact hL1
  calc ∫ x, infDist (Θ x) (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ
      ≤ ∫ x, ((√r + 4 * (C * √r + 2 * C + N)) * |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| +
          r * √r / 4 * ‖β x‖ ^ 2 + 2 * M * (√r * ‖Dbar x‖ ^ 2 + ‖Dα x‖ ^ 2 / √r)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ infDist_nonneg) hgi hpt
    _ = (√r + 4 * (C * √r + 2 * C + N)) * ∫ x, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ +
          r * √r / 4 * ∫ x, ‖β x‖ ^ 2 ∂μ +
            2 * M * (√r * ∫ x, ‖Dbar x‖ ^ 2 ∂μ + (∫ x, ‖Dα x‖ ^ 2 ∂μ) / √r) := by
        rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
          integral_add, integral_const_mul, integral_div]
        -- The side goals are the integrability of the summands.
        all_goals first
          | exact hDbar2.const_mul _
          | exact hDα2.div_const _
          | exact hδ.abs.const_mul _
          | exact hβ2.const_mul _
          | exact (hδ.abs.const_mul _).add (hβ2.const_mul _)
          | exact ((hDbar2.const_mul _).add (hDα2.div_const _)).const_mul _
    _ ≤ _ := add_add_le_div (Real.one_le_sqrt.2 hr) (Real.mul_self_sqrt hr0.le) hC hN hM hI₁
        (integral_norm_sq_le_div_sq hr0 hC (by linarith) hδ hL1 hβK)
        (integral_norm_sq_le_div (Dα' := fun x ↦ Dα x - Dbar x) hr0 hC (by linarith) hδ hL1 hβK
          hgrad hDα' hDbar)
        (integral_norm_sq_le_of_add_mul_norm_sq_le hr0 hC (by linarith) hδ hL1 hβK hgrad)

end Integrated

end TauCeti.SeibergWitten
