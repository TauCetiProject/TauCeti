/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.Analysis.Sobolev.Wkp.Mollification
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Krylov–Safonov estimates for strong supersolutions

The measure estimate and the power decay of Krylov and Safonov in
`TauCeti.Analysis.PDE.Regularity.KrylovSafonov` are proved for classical supersolutions: `C²`
functions with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` at every point. Their constants depend only on the dimension
and on the ellipticity ratio, and nothing is assumed of the coefficients beyond uniform
ellipticity, not even measurability. This file transfers such estimates to strong
supersolutions: functions `u ∈ W^{2,n}(B(c, R))`, `n` the dimension, with a representative `ū`
continuous on `closedBall c R`, satisfying `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` only almost everywhere, for the
weak Hessian `D²u`.

## The approximation

A strong supersolution is approximated by classical ones on the same closed ball
(`TauCeti.PDE.exists_forall_abs_sub_le_and_eLpNorm_posPart_le_of_wkp`). Mollifying `u` at radius
`δ` gives a smooth function `w` whose Hessian is the mollified weak Hessian
(`TauCeti.Wkp.fderiv_gradient_smoothField_value`), but only at points whose `δ`-ball lies in
`B(c, R)`. To keep the full ball, the mollification is precomposed with the homothety
`A = AffineMap.homothety c s`, `A x = c + s • (x - c)`, `s < 1`, which maps `closedBall c R`
into the region where this holds:
`v = w ∘ A` is smooth near `closedBall c R`, and for the coefficients `a ∘ A`, which are
uniformly elliptic with the same constants,

`∑ᵢⱼ aⁱʲ(A x) ∂ᵢ∂ⱼv(x) = s² ∑ᵢⱼ aⁱʲ(A x) (D²w)ᵢⱼ(A x) ≤ s² (f + K |D²w - D²u|)(A x)`

almost everywhere, with `K = n² Λ` (`Matrix.abs_sum_sum_mul_apply_single_le`). The `Lⁿ` norm of
the right-hand side over `B(c, R)` is at
most `s (‖f⁺‖_{Lⁿ} + K ‖D²w - D²u‖_{Lⁿ})`: precomposing with `A` costs the factor `s⁻¹` in `Lⁿ`,
since `A` contracts volume by `sⁿ`. As `δ → 0` the mollified Hessians converge to `D²u` in `Lⁿ`
(`TauCeti.Wkp.tendsto_eLpNorm_smoothField_sub`), and as `s → 1` the functions `v` converge to
`ū` uniformly on `closedBall c R`, by the uniform continuity of `ū` there. The factor `s < 1` on
`‖f⁺‖` leaves room for the error term, so a smallness condition `R ‖f⁺‖_{Lⁿ} ≤ ε₀ λ` survives the
approximation with the same `ε₀`.

## The power decay

For the `L^ε` estimate (`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`)
the approximant `v`, within `η` of `ū`, is normalized to `(v + η) / (1 + 2η)`. This is
nonnegative where `ū` is, at most `1` where `ū ≤ 1`, and at least `ū / (1 + 2η)`, so the classical
power decay for it bounds `|{ū ≥ t} ∩ Q₀|` by `C (t / (1 + 2η))^(-ε) |Q₀|`. Letting `η → 0` gives
the estimate for `ū` with the constants of the classical statement.

## Main declarations

* `TauCeti.PDE.exists_forall_abs_sub_le_and_eLpNorm_posPart_le_of_wkp`: a strong supersolution on
  a ball is a uniform limit of `C²` functions which are classical supersolutions for homothetic
  coefficients, with right-hand sides whose positive parts are controlled in `Lⁿ`.
* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp`: **the power decay of
  Krylov and Safonov for strong supersolutions**.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions).
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6.
* L. C. Evans, *Partial Differential Equations*, §5.3.1 (interior mollification).
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

namespace PDE

section Smallness

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The smallness condition `R ‖F⁺‖ ≤ ε₀ λ` survives scaling `F` by `0 ≤ b ≤ 1`, when
`‖F⁺‖ ≤ s ‖f⁺‖ + (1 - s) ε₀ λ / R` with `0 < s < 1` and `R ‖f⁺‖ ≤ ε₀ λ`. -/
private theorem ofReal_mul_eLpNorm_posPart_const_mul_le {F f : α → ℝ} {b R s ε₀ lam : ℝ}
    {q : ℝ≥0∞} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hR : 0 < R) (hs0 : 0 < s) (hs1 : s < 1)
    (hε₀lam : 0 ≤ ε₀ * lam)
    (hF : eLpNorm (fun x ↦ (F x)⁺) q μ ≤
      ENNReal.ofReal s * eLpNorm (fun x ↦ (f x)⁺) q μ + ENNReal.ofReal ((1 - s) * ε₀ * lam / R))
    (hf : ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) q μ ≤ ENNReal.ofReal (ε₀ * lam)) :
    ENNReal.ofReal R * eLpNorm (fun x ↦ (b * F x)⁺) q μ ≤ ENNReal.ofReal (ε₀ * lam) := by
  have hscale : (fun x ↦ (b * F x)⁺) = b • fun x ↦ (F x)⁺ := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _ hb0, mul_zero]
  have hle1 : ‖b‖ₑ ≤ 1 := by
    rw [Real.enorm_of_nonneg hb0, ENNReal.ofReal_le_one]
    exact hb1
  rw [hscale, eLpNorm_const_smul]
  calc ENNReal.ofReal R * (‖b‖ₑ * eLpNorm (fun x ↦ (F x)⁺) q μ)
      ≤ ENNReal.ofReal R * (ENNReal.ofReal s * eLpNorm (fun x ↦ (f x)⁺) q μ +
          ENNReal.ofReal ((1 - s) * ε₀ * lam / R)) := by
        gcongr
        exact (mul_le_of_le_one_left zero_le hle1).trans hF
    _ = ENNReal.ofReal s * (ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) q μ) +
          ENNReal.ofReal ((1 - s) * ε₀ * lam) := by
        rw [mul_add, ← ENNReal.ofReal_mul hR.le, mul_div_cancel₀ _ hR.ne']
        ring
    _ ≤ ENNReal.ofReal s * ENNReal.ofReal (ε₀ * lam) + ENNReal.ofReal ((1 - s) * ε₀ * lam) := by
        gcongr
    _ = ENNReal.ofReal (ε₀ * lam) := by
        rw [← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_add (by positivity)
          (by rw [mul_assoc]; exact mul_nonneg (sub_pos.2 hs1).le hε₀lam)]
        congr 1
        ring

end Smallness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Precomposition with the homothety of ratio `0 < s ≤ 1` about `c` costs at most the factor
`s⁻¹` in `Lⁿ(B(c, R))`, `n` the dimension. -/
private theorem eLpNorm_comp_homothety_ball_le {c : EuclideanSpace ℝ ι} {R s : ℝ} (hR : 0 ≤ R)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hn : Fintype.card ι ≠ 0) (q : EuclideanSpace ℝ ι → ℝ) :
    eLpNorm (q ∘ AffineMap.homothety c s) (Fintype.card ι) (volume.restrict (ball c R)) ≤
      ENNReal.ofReal s⁻¹ * eLpNorm q (Fintype.card ι) (volume.restrict (ball c R)) := by
  set n := Fintype.card ι
  have hpre : AffineMap.homothety c s ⁻¹' ball c (s * R) = ball c R := by
    ext x
    simp only [mem_preimage, mem_ball, dist_homothety_center, Real.norm_eq_abs, abs_of_pos hs0]
    rw [dist_comm c x]
    exact mul_lt_mul_iff_right₀ hs0
  have hC : (ENNReal.ofReal |(s ^ Module.finrank ℝ (EuclideanSpace ℝ ι))⁻¹|) ^
      (1 / (n : ℝ≥0∞)).toReal =
      ENNReal.ofReal s⁻¹ := by
    rw [finrank_euclideanSpace, abs_of_pos (by positivity), one_div, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hs0.le,
      mul_inv_cancel₀ (by exact_mod_cast hn), Real.rpow_one]
  rw [← hpre, Measure.eLpNorm_comp_homothety_restrict_preimage volume q c hs0.ne', hC, hpre]
  exact mul_le_mul_right (eLpNorm_mono_measure q (Measure.restrict_mono
    (ball_subset_ball (x := c) (mul_le_of_le_one_left hR hs1)) le_rfl)) _

/-- **The homothetic mollification of a strong supersolution.** Let `u ∈ W^{2,n}(B(c, R))` satisfy
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere in `B(c, R)` for its weak Hessian `H`, with `|aⁱʲ| ≤ Λ`,
let `0 < s < 1`, and let `ψ` be a bump of radius below `(1 - s) R`. Then the mollification
`w = ψ * u` composed with the homothety `A` of ratio `s` about `c` is a classical supersolution in
`B(c, R)` for the coefficients `a ∘ A`, with a right-hand side `F` such that
`‖F⁺‖_{Lⁿ} ≤ s ‖f⁺‖_{Lⁿ} + s n² Λ ‖ψ * H - H‖_{Lⁿ}`, all norms on `B(c, R)`. -/
private theorem exists_sum_mul_fderiv_fderiv_smoothField_comp_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p = Fintype.card ι) {R Lam s : ℝ} {c : EuclideanSpace ℝ ι}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (u : Wkp volume ⟨ball c R, isOpen_ball⟩ p 2) (hs0 : 0 < s) (hs1 : s < 1)
    (ψ : ContDiffBump (0 : EuclideanSpace ℝ ι)) (hψ : ψ.rOut < (1 - s) * R)
    (ha : ∀ x ∈ ball c R, ∀ i j, |a x i j| ≤ Lam)
    (hsuper : ∀ᵐ x ∂volume.restrict (ball c R),
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) :
    ∃ F : EuclideanSpace ℝ ι → ℝ,
      (∀ x ∈ ball c R, ∑ i, ∑ j, a (AffineMap.homothety c s x) i j *
          fderiv ℝ (fderiv ℝ (Wkp.smoothField ψ (Wkp.value 2 u) ∘ AffineMap.homothety c s)) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ F x) ∧
      eLpNorm (fun x ↦ (F x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) ≤
        ENNReal.ofReal s * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) + ENNReal.ofReal (s * ((Fintype.card ι : ℝ) ^ 2 * Lam)) *
            eLpNorm (Wkp.smoothField ψ (Wkp.iteratedGradient 1 u) -
              (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ ι → _)) (Fintype.card ι)
              (volume.restrict (ball c R)) := by
  subst hp
  set n := Fintype.card ι
  have hn1 : 1 ≤ (n : ℝ≥0∞) := Fact.out
  have hR : 0 < R := pos_of_mul_pos_right (ψ.rOut_pos.trans hψ) (sub_pos.2 hs1).le
  have : Nonempty ι := Fintype.card_pos_iff.1 (by exact_mod_cast hn1)
  have hLam : 0 ≤ Lam := (abs_nonneg _).trans
    (ha c (mem_ball_self hR) (Classical.arbitrary ι) (Classical.arbitrary ι))
  set K := (n : ℝ) ^ 2 * Lam
  have hK : 0 ≤ K := by positivity
  set A := AffineMap.homothety c s
  have hAc (x : EuclideanSpace ℝ ι) : dist (A x) c = s * dist x c := by
    rw [dist_homothety_center, Real.norm_eq_abs, abs_of_pos hs0, dist_comm]
  set H := Wkp.iteratedGradient 1 u
  set w := Wkp.smoothField ψ (Wkp.value 2 u)
  have hw : ContDiff ℝ 2 w := contDiff_infty.1 (Wkp.contDiff_smoothField _ _) 2
  -- On `B(c, R)`, the Hessian of `w ∘ A` is `s²` times the mollified weak Hessian at `A x`: the
  -- points `A x` lie in `B(c, s R)`, whose `ψ.rOut`-neighbourhood stays in `B(c, R)`.
  set Hψ := Wkp.smoothField ψ H
  have hhess {x : EuclideanSpace ℝ ι} (hx : x ∈ ball c R) (i j : ι) :
      fderiv ℝ (fderiv ℝ (w ∘ A)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        s ^ 2 * Hψ (A x) (EuclideanSpace.single j 1) i := by
    have hAx : dist (A x) c < R - ψ.rOut := by
      rw [mem_ball] at hx
      rw [hAc]
      nlinarith
    rw [fderiv_fderiv_comp_homothety_apply c s hw.contDiffAt, smul_eq_mul,
      ← hessianOperator_single_apply hw.contDiffAt i j, ← fderiv_gradient,
      Wkp.fderiv_gradient_smoothField_value u ψ
        (Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball.2 hAx)) fun y hy z hz ↦ by
          rw [TopologicalSpace.Opens.coe_mk, mem_ball]
          rw [mem_ball] at hy
          rw [mem_closedBall] at hz
          linarith [dist_triangle z y c])]
  -- Almost everywhere in `B(c, R)`, the mollified Hessian satisfies the inequality up to the
  -- error `K ‖D y‖`, where `D = Hψ - H`.
  set D := Hψ - (H : EuclideanSpace ℝ ι → _)
  have hsuper' : ∀ᵐ y ∂volume.restrict (ball c R),
      ∑ i, ∑ j, a y i j * Hψ y (EuclideanSpace.single j 1) i ≤ f y + K * ‖D y‖ := by
    filter_upwards [hsuper, ae_restrict_mem measurableSet_ball] with y hy hyB
    have hsplit : ∑ i, ∑ j, a y i j * Hψ y (EuclideanSpace.single j 1) i =
        ∑ i, ∑ j, a y i j * H y (EuclideanSpace.single j 1) i +
          ∑ i, ∑ j, a y i j * D y (EuclideanSpace.single j 1) i := by
      simp only [D, Pi.sub_apply, sub_apply, PiLp.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
      ring
    have hsum : ∑ i, ∑ j, |a y i j| ≤ K := by
      refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ha y hyB i j).trans_eq ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K, n]
      ring
    have hD := (le_abs_self _).trans (Matrix.abs_sum_sum_mul_apply_single_le (a y) (D y))
    rw [hsplit]
    nlinarith [norm_nonneg (D y)]
  -- `A` is quasi-measure-preserving and maps `B(c, R)` into itself, so the operator `G` of `w ∘ A`
  -- is at most `s² g ∘ A` almost everywhere in `B(c, R)`, with `g = f⁺ + K ‖D‖`.
  have hqmp : QuasiMeasurePreserving A volume volume := ⟨by
    rw [show ⇑A = fun y ↦ s • (y - c) + c by funext y; simp [A, AffineMap.homothety_apply]]
    fun_prop, Measure.absolutelyContinuous_of_le_smul
      (Measure.map_addHaar_homothety volume c hs0.ne').le⟩
  set G : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a (A x) i j *
    fderiv ℝ (fderiv ℝ (w ∘ A)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  set g : EuclideanSpace ℝ ι → ℝ := fun y ↦ (f y)⁺ + K * ‖D y‖
  have hg0 (y : EuclideanSpace ℝ ι) : 0 ≤ (s ^ 2 • g) y := by
    simp only [Pi.smul_apply, smul_eq_mul, g]
    positivity
  have hpt : ∀ᵐ x ∂volume.restrict (ball c R), G x ≤ (s ^ 2 • g) (A x) := by
    have h := hqmp.ae ((ae_restrict_iff' measurableSet_ball).1 hsuper')
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_ball] with x hx hxB
    have hAB : A x ∈ ball c R := by
      rw [mem_ball] at hxB ⊢
      rw [hAc]
      nlinarith [dist_nonneg (x := x) (y := c)]
    have hsum : G x = s ^ 2 * ∑ i, ∑ j, a (A x) i j * Hψ (A x) (EuclideanSpace.single j 1) i := by
      simp only [G, hhess hxB, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum, Pi.smul_apply, smul_eq_mul]
    gcongr
    exact (hx hAB).trans (by simp only [g]; gcongr; exact le_posPart _)
  -- Take `F = max G (s² g ∘ A)`, which is `s² g ∘ A` almost everywhere.
  refine ⟨fun x ↦ max (G x) ((s ^ 2 • g) (A x)), fun x _ ↦ le_max_left _ _, ?_⟩
  have hae : (fun x ↦ (max (G x) ((s ^ 2 • g) (A x)))⁺) =ᵐ[volume.restrict (ball c R)]
      (s ^ 2 • g) ∘ A := by
    filter_upwards [hpt] with x hx
    rw [max_eq_right hx, posPart_eq_self.2 (hg0 _), Function.comp_apply]
  rw [eLpNorm_congr_ae hae]
  have hDm : AEStronglyMeasurable D (volume.restrict (ball c R)) :=
    (Wkp.contDiff_smoothField _ _).continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable _)
  calc _ ≤ ENNReal.ofReal s⁻¹ * eLpNorm (s ^ 2 • g) n (volume.restrict (ball c R)) :=
        eLpNorm_comp_homothety_ball_le hR.le hs0 hs1.le (by positivity) _
    _ ≤ ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (s ^ 2) *
          (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R)) +
            ENNReal.ofReal K * eLpNorm D n (volume.restrict (ball c R)))) := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
        gcongr
        refine (eLpNorm_add_le hn1).trans_eq ?_
        rw [show (fun y ↦ K * ‖D y‖) = K • fun y ↦ ‖D y‖ from rfl, eLpNorm_const_smul,
          eLpNorm_norm _ hDm, Real.enorm_of_nonneg hK]
    _ = _ := by
        have h1 : ENNReal.ofReal s⁻¹ * ENNReal.ofReal (s ^ 2) = ENNReal.ofReal s := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        rw [← mul_assoc, h1, mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hs0.le]

/-- **Approximating a strong supersolution by classical ones.** Let `u ∈ W^{2,n}(B(c, R))`, `n`
the dimension, have a representative `ū` continuous on `closedBall c R`, and let
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere in `B(c, R)` for the weak Hessian of `u`, with coefficients
`|aⁱʲ| ≤ Λ` there. For every `η > 0` there is `0 < s < 1` such that, for every `ε > 0`, some
`C²` function `v` lies within `η` of `ū` on `closedBall c R` and is a classical supersolution,
`∑ᵢⱼ aⁱʲ(c + s • (x - c)) ∂ᵢ∂ⱼv(x) ≤ F x` at every point of `B(c, R)`, for the coefficients
precomposed with the homothety `AffineMap.homothety c s` and a right-hand side `F` with
`‖F⁺‖_{Lⁿ(B(c, R))} ≤ s ‖f⁺‖_{Lⁿ(B(c, R))} + ε`. -/
theorem exists_forall_abs_sub_le_and_eLpNorm_posPart_le_of_wkp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p = Fintype.card ι) {R Lam η : ℝ} {c : EuclideanSpace ℝ ι}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {ū f : EuclideanSpace ℝ ι → ℝ}
    (u : Wkp volume ⟨ball c R, isOpen_ball⟩ p 2) (hR : 0 < R) (hη : 0 < η)
    (ha : ∀ x ∈ ball c R, ∀ i j, |a x i j| ≤ Lam) (hcont : ContinuousOn ū (closedBall c R))
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (ball c R)] ū)
    (hsuper : ∀ᵐ x ∂volume.restrict (ball c R),
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ ε > 0, ∃ v F : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ 2 v ∧
      (∀ x ∈ closedBall c R, |v x - ū x| ≤ η) ∧
      (∀ x ∈ ball c R, ∑ i, ∑ j, a (AffineMap.homothety c s x) i j *
          fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ F x) ∧
      eLpNorm (fun x ↦ (F x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) ≤
        ENNReal.ofReal s * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) + ENNReal.ofReal ε := by
  subst hp
  -- `ū` is uniformly continuous on the compact ball.
  obtain ⟨ρ, hρ, hρū⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall c R).uniformContinuousOn_of_continuous hcont) (η / 2) (half_pos hη)
  -- The ratio `s` of the homothety `A`, close enough to `1` that `A` moves the points of
  -- `closedBall c R` by less than `ρ`.
  set s := max (1 / 2 : ℝ) (1 - ρ / (2 * R))
  have hs0 : 0 < s := lt_max_of_lt_left (by norm_num)
  have hs1 : s < 1 := max_lt (by norm_num) (by have : 0 < ρ / (2 * R) := (by positivity); linarith)
  have hsρ : (1 - s) * R < ρ := by
    have h : 1 - s ≤ ρ / (2 * R) := by linarith [le_max_right (1 / 2 : ℝ) (1 - ρ / (2 * R))]
    calc (1 - s) * R ≤ ρ / (2 * R) * R := mul_le_mul_of_nonneg_right h hR.le
      _ = ρ / 2 := by field_simp
      _ < ρ := half_lt_self hρ
  refine ⟨s, hs0, hs1, fun ε hε ↦ ?_⟩
  set A := AffineMap.homothety c s
  have hAc (x : EuclideanSpace ℝ ι) : dist (A x) c = s * dist x c := by
    rw [dist_homothety_center, Real.norm_eq_abs, abs_of_pos hs0, dist_comm]
  have hAx (x : EuclideanSpace ℝ ι) : dist (A x) x = (1 - s) * dist x c := by
    rw [dist_homothety_self, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hs1), dist_comm]
  -- Mollifiers whose radii decrease to `0`, all below `r = min ((1 - s) R) ρ`; choose one for
  -- which the error `s n² Λ ‖ψ * H - H‖_{Lⁿ}` of the homothetic mollification is below `ε`.
  set r := min ((1 - s) * R) ρ
  have hr : 0 < r := lt_min (mul_pos (sub_pos.2 hs1) hR) hρ
  set φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ ι) := fun k ↦
    ⟨r / (2 * ((k : ℝ) + 2)), r / ((k : ℝ) + 2), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      exact div_lt_div_of_pos_left hr this (by linarith)⟩
  have hφr (k : ℕ) : (φ k).rOut < r :=
    div_lt_self hr (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hφ0 : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set K := (Fintype.card ι : ℝ) ^ 2 * |Lam|
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1
    (Wkp.tendsto_eLpNorm_smoothField_sub (ENNReal.natCast_ne_top _) hφ0
      (Wkp.iteratedGradient 1 u))
    (ENNReal.ofReal (ε / (s * K + 1)))
    (by simp only [gt_iff_lt, ENNReal.ofReal_pos]; positivity)).exists
  set ψ := φ k
  have hψ : ψ.rOut < (1 - s) * R := (hφr k).trans_le (min_le_left _ _)
  obtain ⟨F, hF, hFn⟩ := exists_sum_mul_fderiv_fderiv_smoothField_comp_le rfl u hs0 hs1 ψ hψ
    (fun x hx i j ↦ (ha x hx i j).trans (le_abs_self Lam)) hsuper
  set w := Wkp.smoothField ψ (Wkp.value 2 u)
  have hAsmooth : ContDiff ℝ 2 A := by
    rw [show ⇑A = fun y ↦ s • (y - c) + c by funext y; simp [A, AffineMap.homothety_apply]]
    fun_prop
  refine ⟨w ∘ A, F, (contDiff_infty.1 (Wkp.contDiff_smoothField _ _) 2).comp hAsmooth,
    fun x hx ↦ ?_, hF, ?_⟩
  · -- `w (A x)` is within `η / 2` of `ū (A x)`, which is within `η / 2` of `ū x`.
    rw [mem_closedBall] at hx
    have hsub : ball (A x) ψ.rOut ⊆ ball c R := fun z hz ↦ by
      rw [mem_ball] at hz ⊢
      nlinarith [dist_triangle z (A x) c, hAc x]
    have hAB : A x ∈ closedBall c R := by
      rw [mem_closedBall, hAc]
      nlinarith
    have h1 : dist (w (A x)) (ū (A x)) ≤ η / 2 :=
      Wkp.dist_smoothField_le ψ hū hsub fun y hy ↦
        (hρū y (ball_subset_closedBall (hsub hy)) (A x) hAB (by
          rw [mem_ball] at hy
          linarith [hφr k, min_le_right ((1 - s) * R) ρ])).le
    have h2 : dist (ū (A x)) (ū x) < η / 2 :=
      hρū _ hAB _ (mem_closedBall.2 hx) (by rw [hAx]; nlinarith)
    rw [Function.comp_apply, ← Real.dist_eq]
    linarith [dist_triangle (w (A x)) (ū (A x)) (ū x)]
  · refine hFn.trans (add_le_add le_rfl ?_)
    refine (mul_le_mul_right hk _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hs0.le (by positivity : (0 : ℝ) ≤ K)]

/-- **Power decay of the superlevel sets of a strong supersolution**, the `L^ε` estimate of Krylov
and Safonov for `W^{2,n}` functions (Gilbarg–Trudinger, Section 9.7; Caffarelli–Cabré, Lemma 4.6).
Let `κ > 0`. There are constants `C > 0`, `ε > 0` and `ε₀ > 0`, depending only on the dimension
and on `κ`, with the following property. Let `Q₀` be a dyadic cube of level `k` with centre `c`,
and let `R ≥ 4 · 2ᵏ √n`. Let the coefficient matrix `a` be uniformly elliptic on `B(c, R)` with
constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(B(c, R))` have a representative `ū` continuous and
nonnegative on `closedBall c R`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere in `B(c, R)` for the
weak Hessian of `u` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `ū ≤ 1` somewhere in
`B(c, 2 · 2ᵏ √n)`, then `|{ū ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`. The constants are
those of the classical statement `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`.
-/
theorem exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul_of_wkp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p = Fintype.card ι) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume ⟨ball c R, isOpen_ball⟩ p 2),
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū (closedBall c R) →
        (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (ball c R)] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R), ∑ i, ∑ j, a x i j *
          Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), ū x ≤ 1) →
        ∀ ⦃t : ℝ⦄, 0 < t → volume ({x | t ≤ ū x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (C * t ^ (-ε)) *
            volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
  subst hp
  have hn1 : 1 ≤ (Fintype.card ι : ℝ≥0∞) := Fact.out
  have : Nonempty ι := Fintype.card_pos_iff.1 (by exact_mod_cast hn1)
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  refine ⟨C, ε, ε₀, hC, hε, hε₀, ?_⟩
  intro lam Lam R k m c a ū f u hc hR ha hLam hcont hū hnonneg hsuper hf hx t ht
  -- For each `η > 0`, apply the classical estimate to a normalized classical approximant at the
  -- level `t / (1 + 2η)` (`key`), then let `η → 0`.
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hlam : 0 < lam := ha.pos
  set Q := (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι))
  -- The cube lies in `B(c, R)`.
  have hQ : Q ⊆ ball c R := fun x hx ↦ by
    have h := dist_toLp_lt_of_mem_dyadicCube (show WithLp.ofLp x ∈ dyadicCube k m from hx)
      (centre_mem_dyadicCube k m)
    rw [WithLp.toLp_ofLp, ← hc] at h
    rw [mem_ball]
    nlinarith
  obtain ⟨x₀, hx₀, hux₀⟩ := hx
  have hx₀R : x₀ ∈ closedBall c R := by
    rw [mem_ball] at hx₀
    rw [mem_closedBall]
    nlinarith
  -- For every `η > 0`, the classical power decay for a normalized approximant `w` of `ū` bounds
  -- the superlevel set of `t` by `C (t / (1 + 2η))^(-ε) |Q₀|`.
  have key : ∀ η > 0, volume ({x | t ≤ ū x} ∩ Q) ≤
      ENNReal.ofReal (C * (t / (1 + 2 * η)) ^ (-ε)) * volume Q := by
    intro η hη
    obtain ⟨s, hs0, hs1, happrox⟩ := exists_forall_abs_sub_le_and_eLpNorm_posPart_le_of_wkp rfl u
      hR0 hη (fun x hx i j ↦ ha.abs_apply_le hx i j) hcont hū hsuper
    obtain ⟨v, F, hv, hvū, hvF, hF⟩ :=
      happrox ((1 - s) * ε₀ * lam / R) (by have := sub_pos.2 hs1; positivity)
    have hη2 : 0 < 1 + 2 * η := by positivity
    set w : EuclideanSpace ℝ ι → ℝ := (1 + 2 * η)⁻¹ • fun x ↦ v x + η
    have hw2 (x : EuclideanSpace ℝ ι) :
        fderiv ℝ (fderiv ℝ w) x = (1 + 2 * η)⁻¹ • fderiv ℝ (fderiv ℝ v) x := by
      rw [fderiv_fderiv_const_smul, show (fderiv ℝ fun x ↦ v x + η) = fderiv ℝ v from
        funext fun _ ↦ fderiv_add_const η]
    have hA (x : EuclideanSpace ℝ ι) (hx : x ∈ ball c R) :
        AffineMap.homothety c s x ∈ ball c R := by
      rw [mem_ball, dist_homothety_center, Real.norm_eq_abs, abs_of_pos hs0, dist_comm]
      rw [mem_ball] at hx
      nlinarith [dist_nonneg (x := x) (y := c)]
    have h := H (lam := lam) (Lam := Lam) (a := fun x ↦ a (AffineMap.homothety c s x)) (u := w)
      (f := fun x ↦ (1 + 2 * η)⁻¹ * F x) hc hR
      (UniformlyEllipticOn.of_bounds ha.pos ha.le (fun x hx ξ ↦ ha.lower_bound (hA x hx) ξ)
        fun x hx ζ ξ ↦ ha.upper_bound (hA x hx) ζ ξ) hLam
      ((continuous_const.smul (hv.continuous.add continuous_const)).continuousOn)
      ((contDiff_const.smul (hv.add contDiff_const)).contDiffOn)
      (fun x hx ↦ by
        have := (abs_le.1 (hvū x hx)).1
        have := hnonneg x hx
        simp only [w, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_pos.2 hη2).le (by linarith))
      (fun x hx ↦ by
        simp only [hw2, smul_apply, smul_eq_mul, mul_left_comm _ (1 + 2 * η)⁻¹, ← Finset.mul_sum]
        gcongr
        exact hvF x hx)
      (ofReal_mul_eLpNorm_posPart_const_mul_le (inv_pos.2 hη2).le
        (inv_le_one_of_one_le₀ (by linarith)) hR0 hs0 hs1 (by positivity) hF hf)
      ⟨x₀, hx₀, by
        have := (abs_le.1 (hvū x₀ hx₀R)).2
        simp only [w, Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_le_iff₀ hη2]
        linarith⟩
      (t := t / (1 + 2 * η)) (by positivity)
    refine (measure_mono ?_).trans h
    rintro x ⟨hxt, hxQ⟩
    refine ⟨?_, hxQ⟩
    have := (abs_le.1 (hvū x (ball_subset_closedBall (hQ hxQ)))).1
    simp only [mem_ofPred_eq, w, Pi.smul_apply, smul_eq_mul] at hxt ⊢
    rw [div_eq_inv_mul]
    gcongr
    linarith
  -- Let `η → 0`.
  have hQfin : volume Q ≠ ⊤ := ((measure_mono hQ).trans_lt measure_ball_lt_top).ne
  have hcontη : ContinuousAt (fun η : ℝ ↦ C * (t / (1 + 2 * η)) ^ (-ε)) 0 :=
    continuousAt_const.mul ((continuousAt_const.div (by fun_prop) (by norm_num)).rpow_const
      (Or.inl (by norm_num [ht.ne'])))
  have hlim : Tendsto (fun η : ℝ ↦ ENNReal.ofReal (C * (t / (1 + 2 * η)) ^ (-ε)) * volume Q)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (C * t ^ (-ε)) * volume Q)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hQfin)
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hcontη.tendsto
    simp only [mul_zero, add_zero, div_one, Function.comp_def] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη ↦ key η hη)

end PDE

end TauCeti
