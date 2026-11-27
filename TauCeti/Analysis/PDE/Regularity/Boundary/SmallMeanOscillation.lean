/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.MeanOscillation
public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.Analysis.Sobolev.W1p.HyperplaneReflection
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average.Oscillation
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The `W^{1,p}` estimate up to a flat boundary for coefficients of small mean oscillation

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}` and let `u ∈ H¹(ℝ^{n+1})` vanish
off `H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `H`,

that is `∫_H ⟨a ∇u, ∇φ⟩ = ∫_H ⟨G, ∇φ⟩` for every test function `φ` on `H`, so that `u` has zero
boundary values on the hyperplane. Suppose that `a` is measurable and bounded by `Λ` on `H` and has
small mean oscillation on the half-balls: for every ball `B` centred in the closed half-space, some
constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, not assumed symmetric or
invariant under the reflection in the hyperplane, has `⨍_{B ∩ H} ‖a - A‖ ≤ δ`, in the operator norm
of the attached bilinear forms. This file proves the a priori estimate

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ`, with `C` and the threshold `δ` depending only on
`n`, `p`, `λ` and `Λ` (`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_inter_le`). It is the
boundary counterpart of the whole-space estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`.

Asking instead for small mean oscillation of the coefficient reflected across the hyperplane
(`TauCeti.PDE.reflectPrincipal`) would reduce the problem to the whole space. That hypothesis fails
for coefficients of vanishing mean oscillation in general: on a ball centred on the hyperplane the
reflected coefficient is close to `A` above it and to the reflected matrix `R A R` below it, and
these differ unless the conormal of `A` is normal. Here only `a` on `H` enters, as in the boundary
mean oscillation estimate
`TauCeti.PDE.exists_setAverage_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`, which
freezes the coefficients at an arbitrary elliptic matrix.

## The argument

Let `ρ` be the reflection in the hyperplane and `R` its linear part. The field
`g = ∇u - R (∇u ∘ ρ)`, the gradient of the odd reflection `u - u ∘ ρ`, agrees with `∇u` on `H`,
satisfies `g ∘ ρ = -R g` and dominates `∇u` in `Lᵖ`. Krylov's sharp function method
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`) bounds `‖g‖_{Lᵖ}` by the
`Lᵖ` norm of the reflected datum `G' = 1_H G - 1_H (R G) ∘ ρ` once the square mean oscillation of
`g` on every ball `B(c, ρ)` is bounded by averages over `B(c, κρ)`, with a factor `κ⁻²` on the
average of `‖g‖²`.

* **Interior balls.** On a ball inside `H`, Krylov's interior mean oscillation estimate
  `TauCeti.PDE.setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`
  applies to `u` on `H`.
* **Balls centred on the hyperplane.** There the boundary mean oscillation estimate bounds the
  deviation of `∇u` from a multiple `P` of `ν` on a half-ball. Since `R P = -P`, the oddness of `g`
  makes `‖g - P‖²`, `‖g‖²` and `‖G'‖²` invariant under `ρ`, so their averages over a ball centred
  on the hyperplane are the averages over its upper half.
* **The case split.** For a centre `c` at distance `d` from the hyperplane and `κ ≥ 8`: if
  `d ≥ κρ/4` the interior estimate on `B(c, κρ/4) ⊆ H` suffices; if `d ≤ ρ` the boundary estimate at
  the foot `z` of the perpendicular from `c` applies on `B(z, 2ρ) ⊇ B(c, ρ)`; otherwise the interior
  estimate on `B(c, d) ⊆ H` is followed by the boundary estimate on `B(z, 2d) ⊇ B(c, d)`. Small
  `κ` is trivial, and centres below the hyperplane reduce to their reflections.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_inter_le`: the `W^{1,p}` estimate up to a
  flat boundary for coefficients of small mean oscillation on the half-balls, `2 < p < ∞`. Its
  special case for coefficients close to one elliptic matrix is
  `TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics **96**, AMS, 2008 (the sharp function method, and half-space problems).
* H. Dong, D. Kim, *Elliptic equations in divergence form with partially BMO coefficients*, Arch.
  Ration. Mech. Anal. **196** (2010), 25–70 (mean oscillation estimates on balls centred on a flat
  boundary, combined with interior ones).
-/

public section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Gradient NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The trivial bound: the square mean oscillation of `g ∈ Lᵖ`, `2 ≤ p`, on `B(c, t)` is at most
`(R/t)^(n+1)` times the average of `‖g‖²` over `B(c, R)`, for `t ≤ R`. -/
private theorem setAverage_norm_sub_setAverage_sq_le_mul {g : E → E} {p : ℝ≥0∞}
    (hg : MemLp g p volume) (h2p : 2 ≤ p) {c : E} {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    ⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2 ≤
      (R / t) ^ (n + 1) * ⨍ x in ball c R, ‖g x‖ ^ 2 := by
  refine (setAverage_norm_sub_setAverage_sq_le_setAverage_norm_sub_sq measure_ball_lt_top.ne
    ((hg.restrict (ball c t)).integrableOn_of_subset (one_le_two.trans h2p) subset_rfl
      measure_ball_lt_top.ne)
    ((hg.restrict (ball c t)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne 0)).trans ?_
  simp only [sub_zero]
  have h := (volume : Measure E).setAverage_ball_le_div_pow_mul_setAverage_ball
    (fun x => by positivity : ∀ x, 0 ≤ ‖g x‖ ^ 2) ht (ball_subset_ball htR)
    (by simpa using ((hg.restrict (ball c R)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne 0))
  rwa [finrank_euclideanSpace_fin] at h

/-- The factor `((2Λ)^(2q' - 1) δ)^(1/q')` of the coefficient deviation is nonnegative as soon as
`δ` bounds an average of a nonnegative function and some matrix is elliptic with upper constant
`Λ` on a nonempty ball. -/
private theorem deviation_factor_nonneg {lam Lam δ q' r : ℝ} {c : E}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {S : Set E} {θ : E → ℝ}
    (hA : UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam) (hr : 0 < r) (hθ : ∀ x, 0 ≤ θ x)
    (hδ : ⨍ x in S, θ x ≤ δ) : 0 ≤ ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ := by
  have hLam : 0 ≤ Lam :=
    (norm_nonneg (matrixBilinearForm A)).trans (hA.opNorm_matrixBilinearForm_le (mem_ball_self hr))
  exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    ((average_nonneg hθ).trans hδ)) _

/-- **Half-ball averages as ball averages.** Let `z` lie on the boundary hyperplane of
`H = {c₀ < ⟪x, ν⟫}`, and let `f'` agree with `f` almost everywhere on `H`. If `φ ∘ f'` is invariant
under the reflection `ρ` in the hyperplane and integrable on `B(z, t)`, its average there is the
average of `φ ∘ f` over the half-ball `B(z, t) ∩ H`. -/
private theorem setAverage_ball_inter_eq_setAverage_ball {H : Opens E} {ν : E} (hν : ν ≠ 0)
    {c₀ : ℝ} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {z : E} (hz : ⟪z, ν⟫_ℝ = c₀) {f f' : E → E}
    (hf : ∀ᵐ x, x ∈ H → f' x = f x) {φ : E → ℝ}
    (hφ : ∀ x, φ (f' (hyperplaneReflection ν c₀ x)) = φ (f' x)) {t : ℝ}
    (hi : IntegrableOn (fun x => φ (f' x)) (ball z t)) :
    ⨍ x in ball z t ∩ H, φ (f x) = ⨍ x in ball z t, φ (f' x) := by
  have hHs : (H : Set E) = {x | c₀ < ⟪x, ν⟫_ℝ} := Set.ext hH
  rw [setAverage_ball_eq_setAverage_setOf_lt_inner_inter_ball hν hz hφ hi, ← hHs,
    inter_comm (H : Set E)]
  refine average_congr ?_
  have h := (ae_restrict_iff' H.isOpen.measurableSet).2 hf
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_right
    (h.mono fun x hx => by simp only [hx])

/-- **The interior step.** On a ball `B(c, t) ⊆ H`, Krylov's mean oscillation estimate for the
weak solution `u` on `H`, read for any field `g` agreeing with `∇u` on `H` and any field `G'`
agreeing with `G` there. -/
private theorem exists_interior_step (lam Lam : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {H : Opens E} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : W1p volume (⊤ : Opens E) 2}
      {G g G' : E → E} {p : ℝ≥0∞} {c : E} {ρ t δ q q' : ℝ},
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) → (∀ x ∈ H, G' x = G x) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → 0 < ρ → ρ ≤ t → ball c t ⊆ H →
      UniformlyEllipticOn (ball c t) (fun _ => A) lam Lam →
      ⨍ x in ball c t, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ →
      ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2 ≤
        C * (ρ / t) ^ 2 * (⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2) +
          C * (t / ρ) ^ (n + 1) * ((⨍ x in ball c t, ‖G' x‖ ^ 2) +
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c t, ‖g x‖ ^ (2 * q)) ^ q⁻¹) := by
  set D : ℝ := 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)
  have hD : 0 ≤ D := by positivity
  refine ⟨4 * D + 2 * (4 * D + 2) / lam ^ 2 + 1, by positivity, ?_⟩
  intro H a A u G g G' p c ρ t δ q q' ham hbd hu hgH hG'H h2p hgp hG'p hq hqp hρ hρt hball hA hδ
  have ht : 0 < t := hρ.trans_le hρt
  have hLam : 0 ≤ Lam :=
    (norm_nonneg (matrixBilinearForm A)).trans (hA.opNorm_matrixBilinearForm_le (mem_ball_self ht))
  have : IsFiniteMeasure (volume.restrict (ball c t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uH := W1p.restrictL (le_top : H ≤ ⊤) u
  -- The gradient of the restriction agrees with `g` on `B(c, t)`, and `G` with `G'`.
  have hgB : (W1p.gradient uH : E → E) =ᵐ[volume.restrict (ball c t)] g := by
    have h1 := W1p.gradient_restrictL_ae (le_top : H ≤ ⊤) u
    simp only [Opens.coe_top] at h1
    have h2 : ∀ᵐ x ∂volume.restrict H, g x = W1p.gradient u x :=
      (ae_restrict_iff' H.isOpen.measurableSet).2 hgH
    exact ae_restrict_of_ae_restrict_of_subset hball (h1.trans (h2.mono fun x hx => hx.symm))
  have hGB : (fun x => G x - 0) =ᵐ[volume.restrict (ball c t)] G' :=
    (ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall fun x hx => by simp only [sub_zero, hG'H x (hball hx)])
  have haK : ∀ x ∈ ball c t, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun x hx => (norm_sub_le (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans (by
      linarith [hbd x (hball hx), hA.opNorm_matrixBilinearForm_le hx])
  have key := setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le
    hA (ham.mono_set hball) haK (u := uH) (G := G) (c := 0) hu hball
    (((hG'p.restrict _).mono_exponent h2p).ae_eq hGB.symm) hq
    (((hgp.restrict _).mono_exponent hqp).ae_eq hgB.symm) hρ hρt
  -- Transfer every average from `∇uH` and `G` to `g` and `G'`.
  have hosc (s : ℝ) (hs : s ≤ t) :
      ⨍ x in ball c s, ‖W1p.gradient uH x - ⨍ y in ball c s, W1p.gradient uH y‖ ^ 2 =
        ⨍ x in ball c s, ‖g x - ⨍ y in ball c s, g y‖ ^ 2 := by
    have h := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hs) hgB
    have havg := average_congr h
    exact average_congr (h.mono fun x hx => by simp only [hx, havg])
  have hpow : ⨍ x in ball c t, ‖W1p.gradient uH x‖ ^ (2 * q) = ⨍ x in ball c t, ‖g x‖ ^ (2 * q) :=
    average_congr (hgB.mono fun x hx => by simp only [hx])
  have hG2 : ⨍ x in ball c t, ‖G x - 0‖ ^ 2 = ⨍ x in ball c t, ‖G' x‖ ^ 2 :=
    average_congr (hGB.mono fun x hx => by simp only [hx])
  rw [hosc ρ hρt, hosc t le_rfl, hpow, hG2] at key
  refine key.trans ?_
  have hq'0 : 0 ≤ q'⁻¹ := inv_nonneg.2 hq.symm.pos.le
  have hosc0 : 0 ≤ ⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2 :=
    average_nonneg fun x => by positivity
  have hY0 : 0 ≤ ⨍ x in ball c t, ‖G' x‖ ^ 2 := average_nonneg fun x => by positivity
  have hZ0 : 0 ≤ (⨍ x in ball c t, ‖g x‖ ^ (2 * q)) ^ q⁻¹ :=
    Real.rpow_nonneg (average_nonneg fun x => by positivity) _
  have hθ0 : 0 ≤ ⨍ x in ball c t, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ :=
    average_nonneg fun x => by positivity
  -- Compare the constants with `C`, and the mean deviation of `a` with `δ`.
  gcongr ?_ * _ * _ + ?_ * _ * (_ + (_ * ?_) ^ _ * _)
  · linarith [(by positivity : 0 ≤ 2 * (4 * D + 2) / lam ^ 2)]
  · linarith

/-- **The boundary step.** On a ball `B(z, s)` centred on the boundary hyperplane, the boundary
mean oscillation estimate for `u`, read for a field `g` agreeing with `∇u` on `H` and odd under the
reflection, `g ∘ ρ = -R g`, and a field `G'` agreeing with `G` on `H` with `‖G' ∘ ρ‖ = ‖G'‖`. These
symmetries turn the averages over half-balls into averages over whole balls. -/
private theorem exists_boundary_step {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : W1p volume (⊤ : Opens E) 2}
      {G g G' : E → E} {p : ℝ≥0∞} {z : E} {s r δ q q' : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) →
      (∀ x, g (hyperplaneReflection ν c₀ x) = -(ℝ ∙ ν)ᗮ.reflection (g x)) →
      (∀ x ∈ H, G' x = G x) → (∀ x, ‖G' (hyperplaneReflection ν c₀ x)‖ = ‖G' x‖) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → ⟪z, ν⟫_ℝ = c₀ → 0 < s → s ≤ r →
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      ⨍ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ →
      ∃ P : E, ⨍ x in ball z s, ‖g x - P‖ ^ 2 ≤
        C * (s / r) ^ 2 * (⨍ x in ball z r, ‖g x‖ ^ 2) +
          C * (r / s) ^ (n + 1) * ((⨍ x in ball z r, ‖G' x‖ ^ 2) +
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball z r, ‖g x‖ ^ (2 * q)) ^ q⁻¹) := by
  obtain ⟨C, hC, hbdry⟩ :=
    exists_setAverage_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le (n := n)
      (Lam := Lam) hlam
  refine ⟨C, hC, ?_⟩
  intro H ν c₀ a A u G g G' p z s r δ q q' hν hH ham hbd hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq
    hqp hz hs hsr hA hδ
  have hr : 0 < r := hs.trans_le hsr
  have hLam : 0 ≤ Lam :=
    (norm_nonneg (matrixBilinearForm A)).trans (hA.opNorm_matrixBilinearForm_le (mem_ball_self hr))
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  set P : E := (⟪⨍ y in ball z s ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
  refine ⟨P, ?_⟩
  -- The data of the boundary estimate on `ball z r ∩ H`.
  have hgHr : ∀ t, (W1p.gradient u : E → E) =ᵐ[volume.restrict (ball z t ∩ H)] g := by
    intro t
    have h2 : ∀ᵐ x ∂volume.restrict H, g x = W1p.gradient u x :=
      (ae_restrict_iff' H.isOpen.measurableSet).2 hgH
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_right (h2.mono fun x hx => hx.symm)
  have hGHr : (fun x => G x - 0) =ᵐ[volume.restrict (ball z r ∩ H)] G' :=
    (ae_restrict_iff' (measurableSet_ball.inter H.isOpen.measurableSet)).2
      (Filter.Eventually.of_forall fun x hx => by simp only [sub_zero, hG'H x hx.2])
  have : IsFiniteMeasure (volume.restrict (ball z r ∩ (H : Set E))) :=
    isFiniteMeasure_restrict.2 (measure_ne_top_of_subset inter_subset_left measure_ball_lt_top.ne)
  have haK : ∀ x ∈ ball z r ∩ H,
      ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun x hx => (norm_sub_le (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans (by
      linarith [hbd x hx.2, hA.opNorm_matrixBilinearForm_le hx.1])
  -- The boundary estimate is stated on `U ⊓ H`; transport the weak formulation from `H` to
  -- `⊤ ⊓ H`, which equals `H` only propositionally.
  have hu' : ∀ V : Opens E, V = H → ∀ hV : V ≤ ⊤, ∀ φ : 𝓓(V, ℝ),
      energyFormH1 a 0 0 (W1p.restrictL hV u) (W1p.ofTestFunctionₗ volume V 2 φ) =
        ∫ x in V, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ := by
    rintro V rfl _ φ
    exact hu φ
  have hu'' := hu' (⊤ ⊓ H) (top_inf_eq H) inf_le_left
  have key := hbdry (U := ⊤) (H := H) (c := 0) hA (ham.mono_set inter_subset_right) haK hν hH hz
    (subset_univ _) (by simpa only [Opens.coe_top, Measure.restrict_univ] using hu0) hu''
    (((hG'p.restrict _).mono_exponent h2p).ae_eq hGHr.symm) hq
    (((hgp.restrict _).mono_exponent hqp).ae_eq (hgHr r).symm) hs hsr 0
  -- Transfer the averages over half-balls to averages over balls.
  have hRν : R ν = -ν := Submodule.reflection_orthogonalComplement_singleton_eq_neg ν
  have hRP : R P = -P := by simp only [P, map_smul, hRν, smul_neg]
  have hgnorm (Q : E) (hQ : R Q = -Q) (x : E) :
      ‖g (hyperplaneReflection ν c₀ x) - Q‖ = ‖g x - Q‖ := by
    rw [hgρ, show -R (g x) - Q = -R (g x - Q) by rw [map_sub, hQ]; abel, norm_neg,
      LinearIsometryEquiv.norm_map]
  have hgnorm0 (x : E) : ‖g (hyperplaneReflection ν c₀ x)‖ = ‖g x‖ := by
    simpa using hgnorm 0 (by simp) x
  have hgi (t : ℝ) (Q : E) : IntegrableOn (fun x => ‖g x - Q‖ ^ 2) (ball z t) :=
    (hgp.restrict (ball z t)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne Q
  have hLHS := setAverage_ball_inter_eq_setAverage_ball hν hH hz (t := s) (f := W1p.gradient u)
    (φ := fun v => ‖v - P‖ ^ 2) hgH (fun x => by simp only [hgnorm P hRP]) (hgi s P)
  have hg2r := setAverage_ball_inter_eq_setAverage_ball hν hH hz (t := r)
    (f := W1p.gradient u) (φ := fun v => ‖v - (0 : ℝ) • ν‖ ^ 2) hgH
    (fun x => by simp only [zero_smul, sub_zero, hgnorm0]) (by simpa using hgi r 0)
  have hG2r := setAverage_ball_inter_eq_setAverage_ball hν hH hz (t := r) (f := G) (f' := G')
    (φ := fun v => ‖v - 0‖ ^ 2) (Filter.Eventually.of_forall hG'H)
    (fun x => by simp only [sub_zero, hG'ρ])
    ((hG'p.restrict (ball z r)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne 0)
  have hgqr := setAverage_ball_inter_eq_setAverage_ball hν hH hz (t := r) (f := W1p.gradient u)
    (φ := fun v => ‖v‖ ^ (2 * q)) hgH (fun x => by simp only [hgnorm0])
    ((hgp.restrict (ball z r)).integrableOn_norm_rpow_of_subset (mul_pos two_pos hq.pos) hqp
      subset_rfl measure_ball_lt_top.ne)
  simp only [zero_smul, sub_zero] at hg2r hG2r
  simp only [zero_smul, sub_zero] at key
  rw [← hLHS]
  rw [hg2r, hG2r, hgqr] at key
  refine key.trans ?_
  have hθ0 : 0 ≤ ⨍ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ :=
    average_nonneg fun x => by positivity
  have hq'0 : 0 ≤ q'⁻¹ := inv_nonneg.2 hq.symm.pos.le
  gcongr
  exact Real.rpow_nonneg (average_nonneg fun x => by positivity) _

/-- **The boundary bound.** Let `c` lie in the closed half-space at distance `d` from the
hyperplane, and let `d ≤ t` and `4t ≤ R`. The square mean oscillation of `g` on `B(c, t)` is
bounded by the averages over `B(c, R)` of `‖g‖²`, `‖G'‖²` and `‖g‖^(2q)`, by the boundary step at
the foot `z` of the perpendicular from `c`, since `B(c, t) ⊆ B(z, 2t)` and `B(z, R/2) ⊆ B(c, R)`. -/
private theorem exists_boundary_bound {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {u : W1p volume (⊤ : Opens E) 2} {G g G' : E → E} {p : ℝ≥0∞} {c : E} {t R δ q q' : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ (c : E) (r : ℝ), c₀ ≤ ⟪c, ν⟫_ℝ → 0 < r →
        ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
          UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
            ⨍ x in ball c r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) →
      (∀ x, g (hyperplaneReflection ν c₀ x) = -(ℝ ∙ ν)ᗮ.reflection (g x)) →
      (∀ x ∈ H, G' x = G x) → (∀ x, ‖G' (hyperplaneReflection ν c₀ x)‖ = ‖G' x‖) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → c₀ ≤ ⟪c, ν⟫_ℝ → 0 < t → (⟪c, ν⟫_ℝ - c₀) / ‖ν‖ ≤ t →
      4 * t ≤ R →
      ⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2 ≤
        C * (t / R) ^ 2 * (⨍ x in ball c R, ‖g x‖ ^ 2) +
          C * (R / t) ^ (n + 1) * ((⨍ x in ball c R, ‖G' x‖ ^ 2) +
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹) := by
  obtain ⟨CB, hCB, hstep⟩ := exists_boundary_step (n := n) hlam Lam
  refine ⟨16 * 2 ^ (n + 1) * 2 ^ (n + 1) * CB, by positivity, ?_⟩
  intro H ν c₀ a u G g G' p c t R δ q q' hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p
    hq hqp hc ht hdt htR
  have hR : 0 < R := by linarith
  obtain ⟨z, hz, hcz⟩ := exists_inner_eq_and_dist_eq hν c c₀
  rw [abs_of_nonneg (sub_nonneg.2 hc)] at hcz
  -- The balls involved: `B(c, t) ⊆ B(z, 2t)` and `B(z, R/2) ⊆ B(c, R)`.
  have hsub₁ : ball c t ⊆ ball z (2 * t) := fun x hx => by
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle x c z]
  have hsub₂ : ball z (R / 2) ⊆ ball c R := fun x hx => by
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle x z c, dist_comm c z]
  obtain ⟨A, hA, hδ⟩ := hosc z (R / 2) hz.ge (by linarith)
  obtain ⟨P, hP⟩ := hstep hν hH ham hbd hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq hqp hz
    (by linarith : (0 : ℝ) < 2 * t) (by linarith : 2 * t ≤ R / 2) hA hδ
  -- The oscillation on `B(c, t)` is at most the deviation from `P` on `B(z, 2t)`.
  have hgi {f : E → E} (hf : MemLp f p volume) (x : E) (r : ℝ) (Q : E) :
      IntegrableOn (fun y => ‖f y - Q‖ ^ 2) (ball x r) :=
    (hf.restrict (ball x r)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne Q
  have h1 := (setAverage_norm_sub_setAverage_sq_le_setAverage_norm_sub_sq measure_ball_lt_top.ne
    ((hgp.restrict (ball c t)).integrableOn_of_subset (one_le_two.trans h2p) subset_rfl
      measure_ball_lt_top.ne) (hgi hgp c t P)).trans
    ((volume : Measure E).setAverage_ball_le_div_pow_mul_setAverage_ball (fun x => by positivity)
      ht hsub₁ (hgi hgp z (2 * t) P))
  rw [show 2 * t / t = 2 by field_simp, finrank_euclideanSpace_fin] at h1
  -- Pass from `B(z, R/2)` to `B(c, R)`.
  have hR2 : R / (R / 2) = 2 := by field_simp
  have hX := (volume : Measure E).setAverage_ball_le_div_pow_mul_setAverage_ball
    (fun x => by positivity : ∀ x, 0 ≤ ‖g x‖ ^ 2) (by linarith : 0 < R / 2) hsub₂
    (by simpa using hgi hgp c R 0)
  have hY := (volume : Measure E).setAverage_ball_le_div_pow_mul_setAverage_ball
    (fun x => by positivity : ∀ x, 0 ≤ ‖G' x‖ ^ 2) (by linarith : 0 < R / 2) hsub₂
    (by simpa using hgi hG'p c R 0)
  have hZ := (volume : Measure E).rpow_setAverage_ball_le_div_pow_rpow_mul
    (fun x => by positivity : ∀ x, 0 ≤ ‖g x‖ ^ (2 * q)) (by linarith : 0 < R / 2)
    hsub₂ ((hgp.restrict (ball c R)).integrableOn_norm_rpow_of_subset (mul_pos two_pos hq.pos)
      hqp subset_rfl measure_ball_lt_top.ne) (inv_nonneg.2 hq.pos.le)
  rw [hR2, finrank_euclideanSpace_fin] at hX hY hZ
  -- Weaken the factor `(2^(n+1))^(1/q)` to `2^(n+1)`, as `q ≥ 1`.
  replace hZ := hZ.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (one_le_pow₀ one_le_two) (inv_le_one_of_one_le₀ hq.lt.le))
    (Real.rpow_nonneg (average_nonneg fun x => by positivity) _))
  set D := ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹
  have hD : 0 ≤ D := deviation_factor_nonneg hA (by linarith) (fun x => by positivity) hδ
  set X := ⨍ x in ball c R, ‖g x‖ ^ 2
  set Y := ⨍ x in ball c R, ‖G' x‖ ^ 2
  set Z := (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹
  calc ⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2
      ≤ 2 ^ (n + 1) * (CB * (2 * t / (R / 2)) ^ 2 * (2 ^ (n + 1) * X) +
          CB * (R / 2 / (2 * t)) ^ (n + 1) * (2 ^ (n + 1) * Y + D * (2 ^ (n + 1) * Z))) := by
        refine h1.trans ?_
        gcongr
        exact hP.trans (by gcongr)
    _ = 16 * 2 ^ (n + 1) * 2 ^ (n + 1) * CB * (t / R) ^ 2 * X +
          CB * (R / t) ^ (n + 1) * (Y + D * Z) := by
        rw [show R / 2 / (2 * t) = (R / t) / 4 by field_simp; ring, div_pow (R / t) 4 (n + 1),
          show (4 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) by rw [← mul_pow]; norm_num]
        field_simp
        ring
    _ ≤ _ := by
        have hYZ : 0 ≤ Y + D * Z := by
          have : 0 ≤ Y := average_nonneg fun x => by positivity
          have : 0 ≤ Z := Real.rpow_nonneg (average_nonneg fun x => by positivity) _
          positivity
        gcongr
        calc CB = 1 * 1 * 1 * CB := by ring
          _ ≤ 16 * 2 ^ (n + 1) * 2 ^ (n + 1) * CB := by
            gcongr
            · norm_num
            · exact one_le_pow₀ one_le_two
            · exact one_le_pow₀ one_le_two

/-- **Chaining the interior step.** On a ball `B(c, t) ⊆ H` with `ρ ≤ t ≤ R`, a bound for the
square mean oscillation of `g` on `B(c, t)` by the averages over `B(c, R)` gives one on `B(c, ρ)`,
through the interior step. -/
private theorem exists_interior_chain (lam Lam : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {u : W1p volume (⊤ : Opens E) 2} {G g G' : E → E} {p : ℝ≥0∞} {c : E}
      {ρ t R δ q q' α β : ℝ},
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ (c : E) (r : ℝ), c₀ ≤ ⟪c, ν⟫_ℝ → 0 < r →
        ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
          UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
            ⨍ x in ball c r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) → (∀ x ∈ H, G' x = G x) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → c₀ ≤ ⟪c, ν⟫_ℝ → 0 < ρ → ρ ≤ t → t ≤ R → ball c t ⊆ H →
      0 ≤ β →
      ⨍ x in ball c t, ‖g x - ⨍ y in ball c t, g y‖ ^ 2 ≤
        α * (t / R) ^ 2 * (⨍ x in ball c R, ‖g x‖ ^ 2) +
          β * (R / t) ^ (n + 1) * ((⨍ x in ball c R, ‖G' x‖ ^ 2) +
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹) →
      ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2 ≤
        C * α * (ρ / R) ^ 2 * (⨍ x in ball c R, ‖g x‖ ^ 2) +
          C * (β + 1) * (R / ρ) ^ (n + 1) * ((⨍ x in ball c R, ‖G' x‖ ^ 2) +
            ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹) := by
  obtain ⟨CI, hCI, hstep⟩ := exists_interior_step (n := n) lam Lam
  refine ⟨CI, hCI, ?_⟩
  intro H ν c₀ a u G g G' p c ρ t R δ q q' α β ham hbd hosc hu hgH hG'H h2p hgp hG'p hq hqp hc hρ
    hρt htR hball hβ hbound
  have ht : 0 < t := hρ.trans_le hρt
  have hR : 0 < R := ht.trans_le htR
  obtain ⟨A, hA, hδ⟩ := hosc c t hc ht
  rw [inter_eq_left.2 hball] at hδ
  have h := hstep ham hbd hu hgH hG'H h2p hgp hG'p hq hqp hρ hρt hball hA hδ
  -- Pass from `B(c, t)` to `B(c, R)` in the forcing terms.
  have hY := (volume : Measure E).setAverage_ball_le_div_pow_mul_setAverage_ball
    (fun x => by positivity : ∀ x, 0 ≤ ‖G' x‖ ^ 2) ht (ball_subset_ball htR)
    (by simpa using ((hG'p.restrict (ball c R)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne 0))
  have hZ := (volume : Measure E).rpow_setAverage_ball_le_div_pow_rpow_mul
    (fun x => by positivity : ∀ x, 0 ≤ ‖g x‖ ^ (2 * q)) ht (ball_subset_ball htR)
    ((hgp.restrict (ball c R)).integrableOn_norm_rpow_of_subset (mul_pos two_pos hq.pos) hqp
      subset_rfl measure_ball_lt_top.ne) (inv_nonneg.2 hq.pos.le)
  rw [finrank_euclideanSpace_fin] at hY hZ
  -- Weaken the factor `((R/t)^(n+1))^(1/q)` to `(R/t)^(n+1)`, as `t ≤ R` and `q ≥ 1`.
  replace hZ := hZ.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (one_le_pow₀ ((one_le_div ht).2 htR))
      (inv_le_one_of_one_le₀ hq.lt.le))
    (Real.rpow_nonneg (average_nonneg fun x => by positivity) _))
  set D := ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹
  have hD : 0 ≤ D := deviation_factor_nonneg hA ht (fun x => by positivity) hδ
  set X := ⨍ x in ball c R, ‖g x‖ ^ 2
  set W := (⨍ x in ball c R, ‖G' x‖ ^ 2) + D * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹
  have hW : 0 ≤ W := by
    have : 0 ≤ ⨍ x in ball c R, ‖G' x‖ ^ 2 := average_nonneg fun x => by positivity
    have : 0 ≤ (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹ :=
      Real.rpow_nonneg (average_nonneg fun x => by positivity) _
    positivity
  -- The forcing averages over `B(c, t)` are at most `(R/t)^(n+1)` times those over `B(c, R)`.
  have hforce : (⨍ x in ball c t, ‖G' x‖ ^ 2) + D * (⨍ x in ball c t, ‖g x‖ ^ (2 * q)) ^ q⁻¹ ≤
      (R / t) ^ (n + 1) * W := by
    calc (⨍ x in ball c t, ‖G' x‖ ^ 2) + D * (⨍ x in ball c t, ‖g x‖ ^ (2 * q)) ^ q⁻¹
        ≤ (R / t) ^ (n + 1) * (⨍ x in ball c R, ‖G' x‖ ^ 2) +
            D * ((R / t) ^ (n + 1) * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹) :=
          add_le_add hY (mul_le_mul_of_nonneg_left hZ hD)
      _ = (R / t) ^ (n + 1) * W := by ring
  have hρt' : (ρ / t) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one ht).2 hρt)
  have hRt : (R / t) ^ (n + 1) ≤ (R / ρ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by linarith) hρ hρt) _
  calc ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2
      ≤ CI * (ρ / t) ^ 2 * (α * (t / R) ^ 2 * X + β * (R / t) ^ (n + 1) * W) +
          CI * (t / ρ) ^ (n + 1) * ((R / t) ^ (n + 1) * W) := by
        refine h.trans ?_
        gcongr
    _ = CI * α * (ρ / R) ^ 2 * X +
          CI * (β * ((ρ / t) ^ 2 * (R / t) ^ (n + 1)) + (R / ρ) ^ (n + 1)) * W := by
        rw [div_pow ρ t, div_pow t R, div_pow t ρ, div_pow R t, div_pow ρ R, div_pow R ρ]
        field_simp
        ring
    _ ≤ CI * α * (ρ / R) ^ 2 * X + CI * (β * (R / ρ) ^ (n + 1) + (R / ρ) ^ (n + 1)) * W := by
        gcongr
        calc (ρ / t) ^ 2 * (R / t) ^ (n + 1) ≤ 1 * (R / ρ) ^ (n + 1) :=
              mul_le_mul hρt' hRt (by positivity) zero_le_one
          _ = (R / ρ) ^ (n + 1) := one_mul _
    _ = _ := by ring

/-- The constant `16^(n+3) (C_I + 1) (C_B + 1)` dominates every constant arising in the case
split of `exists_upper_bound`. -/
private theorem le_sixteen_pow_mul_add_one_mul_add_one {CI CB : ℝ} (hCI : 0 < CI) (hCB : 0 < CB) :
    (8 : ℝ) ^ (n + 3) ≤ 16 ^ (n + 3) * (CI + 1) * (CB + 1) ∧
      CI * (16 * 4 ^ (n + 1)) ≤ 16 ^ (n + 3) * (CI + 1) * (CB + 1) ∧
      CB ≤ 16 ^ (n + 3) * (CI + 1) * (CB + 1) ∧
      CI * (CB + 1) ≤ 16 ^ (n + 3) * (CI + 1) * (CB + 1) := by
  have hK1 : (1 : ℝ) ≤ 16 ^ (n + 3) := one_le_pow₀ (by norm_num)
  have hK8 : (8 : ℝ) ^ (n + 3) ≤ 16 ^ (n + 3) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hK16 : (16 : ℝ) * 4 ^ (n + 1) ≤ 16 ^ (n + 3) := by
    calc (16 : ℝ) * 4 ^ (n + 1) ≤ 16 * 16 ^ (n + 1) := by gcongr; norm_num
      _ = 16 ^ (n + 2) := by ring
      _ ≤ 16 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hIB : (CI + 1) * (CB + 1) ≤ 16 ^ (n + 3) * (CI + 1) * (CB + 1) := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hK1
  refine ⟨?_, ?_, ?_, (by nlinarith : CI * (CB + 1) ≤ (CI + 1) * (CB + 1)).trans hIB⟩
  · calc (8 : ℝ) ^ (n + 3) ≤ 16 ^ (n + 3) * 1 * 1 := by rw [mul_one, mul_one]; exact hK8
      _ ≤ _ := by gcongr <;> linarith
  · calc CI * (16 * 4 ^ (n + 1)) ≤ 16 ^ (n + 3) * (CI + 1) * 1 := by
          rw [mul_one, mul_comm (16 ^ (n + 3) : ℝ)]
          gcongr
          linarith
      _ ≤ _ := by gcongr; linarith
  · exact (by nlinarith : CB ≤ (CI + 1) * (CB + 1)).trans hIB

/-- **The mean oscillation bound on balls centred in the closed half-space.** For `c` with
`c₀ ≤ ⟪c, ν⟫` and `κ ≥ 1`, the square mean oscillation of `g` on `B(c, ρ)` is bounded by the
averages over `B(c, κρ)`, in the form Krylov's sharp function method consumes. The proof splits
according to the distance `d` from `c` to the hyperplane: for `κ < 8` the trivial bound suffices;
if `d ≥ κρ/4` the interior step applies on `B(c, κρ/4) ⊆ H`; if `d ≤ ρ` the boundary bound applies
to `B(c, ρ)`; otherwise the interior step on `B(c, d) ⊆ H` is followed by the boundary bound for
`B(c, d)`. -/
private theorem exists_upper_bound {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) : ∃ M : ℝ, 0 < M ∧
    ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {u : W1p volume (⊤ : Opens E) 2} {G g G' : E → E} {p : ℝ≥0∞} {c : E} {ρ κ δ q q' : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ (c : E) (r : ℝ), c₀ ≤ ⟪c, ν⟫_ℝ → 0 < r →
        ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
          UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
            ⨍ x in ball c r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) →
      (∀ x, g (hyperplaneReflection ν c₀ x) = -(ℝ ∙ ν)ᗮ.reflection (g x)) →
      (∀ x ∈ H, G' x = G x) → (∀ x, ‖G' (hyperplaneReflection ν c₀ x)‖ = ‖G' x‖) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → c₀ ≤ ⟪c, ν⟫_ℝ → 0 < ρ → 1 ≤ κ →
      ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2 ≤
        M / κ ^ 2 * (⨍ x in ball c (κ * ρ), ‖g x‖ ^ 2) +
          M * κ ^ (n + 1) * (⨍ x in ball c (κ * ρ), ‖G' x‖ ^ 2) +
          M * κ ^ (n + 1) * ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ x in ball c (κ * ρ), ‖g x‖ ^ (2 * q)) ^ q⁻¹ := by
  obtain ⟨CB, hCB, hbdry⟩ := exists_boundary_bound (n := n) hlam Lam
  obtain ⟨CI, hCI, hchain⟩ := exists_interior_chain (n := n) lam Lam
  refine ⟨16 ^ (n + 3) * (CI + 1) * (CB + 1), by positivity, ?_⟩
  intro H ν c₀ a u G g G' p c ρ κ δ q q' hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p
    hq hqp hc hρ hκ
  set M := 16 ^ (n + 3) * (CI + 1) * (CB + 1)
  obtain ⟨hM8, hMI, hMB, hMIB⟩ := le_sixteen_pow_mul_add_one_mul_add_one (n := n) hCI hCB
  set R := κ * ρ with hR_def
  have hR : 0 < R := mul_pos (zero_lt_one.trans_le hκ) hρ
  have hρR : ρ / R = κ⁻¹ := by rw [hR_def]; field_simp
  have hRρ : R / ρ = κ := by rw [hR_def]; field_simp
  set D := ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹
  set X := ⨍ x in ball c R, ‖g x‖ ^ 2 with hX_def
  set W := (⨍ x in ball c R, ‖G' x‖ ^ 2) + D * (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹
  have hX : 0 ≤ X := average_nonneg fun x => by positivity
  have hW : 0 ≤ W := by
    obtain ⟨A, hA, hδ⟩ := hosc c 1 hc one_pos
    have hD : 0 ≤ D := deviation_factor_nonneg hA one_pos (fun x => by positivity) hδ
    have : 0 ≤ ⨍ x in ball c R, ‖G' x‖ ^ 2 := average_nonneg fun x => by positivity
    have : 0 ≤ (⨍ x in ball c R, ‖g x‖ ^ (2 * q)) ^ q⁻¹ :=
      Real.rpow_nonneg (average_nonneg fun x => by positivity) _
    positivity
  -- Every case gives a bound `α (ρ/R)² X + β (R/ρ)^(n+1) W` with `α, β ≤ M`.
  suffices h : ∃ α β : ℝ, α ≤ M ∧ β ≤ M ∧
      ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2 ≤
        α * (ρ / R) ^ 2 * X + β * (R / ρ) ^ (n + 1) * W by
    obtain ⟨α, β, hα, hβ, hbound⟩ := h
    refine hbound.trans ?_
    rw [hρR, hRρ]
    calc α * κ⁻¹ ^ 2 * X + β * κ ^ (n + 1) * W ≤ M * κ⁻¹ ^ 2 * X + M * κ ^ (n + 1) * W := by
          gcongr
      _ = _ := by simp only [W, inv_pow]; ring
  rcases lt_or_ge κ 8 with hκ8 | hκ8
  · -- `κ < 8`: the oscillation is at most `⨍_{B(c, ρ)} ‖g‖² ≤ κ^(n+1) X`.
    refine ⟨κ ^ (n + 3), 0, ?_, hCB.le.trans hMB, ?_⟩
    · exact hM8.trans' (pow_le_pow_left₀ (by linarith) hκ8.le _)
    refine (setAverage_norm_sub_setAverage_sq_le_mul (R := R) hgp h2p hρ
      (le_mul_of_one_le_left hρ.le hκ)).trans (le_of_eq ?_)
    rw [← hX_def, zero_mul, zero_mul, add_zero, hρR, hRρ]
    field_simp
    ring
  set d := (⟪c, ν⟫_ℝ - c₀) / ‖ν‖
  -- A ball about `c` of radius at most `d`, the distance from `c` to the hyperplane, lies in `H`.
  have hballH {r : ℝ} (hr : r ≤ d) : ball c r ⊆ H := fun x hx =>
    (hH x).2 (ball_subset_setOf_lt_inner hν
      (by linarith [(le_div_iff₀ (norm_pos_iff.2 hν)).1 hr]) hx)
  rcases le_or_gt (R / 4) d with hd | hd
  · -- `d ≥ R/4`: the interior step on `B(c, R/4) ⊆ H`, after the trivial bound there.
    have hball : ball c (R / 4) ⊆ H := hballH hd
    have hρt : ρ ≤ R / 4 := by rw [hR_def]; nlinarith
    have htriv : ⨍ x in ball c (R / 4), ‖g x - ⨍ y in ball c (R / 4), g y‖ ^ 2 ≤
        (16 * 4 ^ (n + 1)) * (R / 4 / R) ^ 2 * X + 0 * (R / (R / 4)) ^ (n + 1) * W := by
      refine (setAverage_norm_sub_setAverage_sq_le_mul (R := R) hgp h2p (by linarith)
        (by linarith : R / 4 ≤ R)).trans (le_of_eq ?_)
      rw [← hX_def, zero_mul, zero_mul, add_zero, show R / (R / 4) = 4 by field_simp,
        show R / 4 / R = 4⁻¹ by field_simp]
      field_simp
      ring
    have h := hchain ham hbd hosc hu hgH hG'H h2p hgp hG'p hq hqp hc hρ hρt (by linarith) hball
      le_rfl htriv
    exact ⟨CI * (16 * 4 ^ (n + 1)), CI * (0 + 1), hMI,
      (by nlinarith : CI * (0 + 1) ≤ CI * (CB + 1)).trans hMIB, h⟩
  rcases le_or_gt d ρ with hdρ | hdρ
  · -- `d ≤ ρ`: the boundary bound on `B(c, ρ)`.
    have h := hbdry (R := R) hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq hqp hc
      hρ hdρ (by rw [hR_def]; nlinarith)
    exact ⟨CB, CB, hMB, hMB, h⟩
  · -- `ρ < d < R/4`: the interior step on `B(c, d)`, then the boundary bound there.
    have hball : ball c d ⊆ H := hballH le_rfl
    have hb := hbdry (R := R) hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq hqp hc
      (hρ.trans hdρ) le_rfl (by linarith)
    have h := hchain ham hbd hosc hu hgH hG'H h2p hgp hG'p hq hqp hc hρ hdρ.le (by linarith)
      hball hCB.le hb
    exact ⟨CI * CB, CI * (CB + 1), (by nlinarith : CI * CB ≤ CI * (CB + 1)).trans hMIB, hMIB, h⟩

/-- **The mean oscillation bound on every ball.** The bound of `exists_upper_bound` holds for
balls centred anywhere: below the hyperplane, the reflection carries `B(c, ρ)` and `B(c, κρ)` onto
the balls about `ρ c`, and the symmetries of `g` and `G'` preserve every average involved. -/
private theorem exists_ball_bound {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) : ∃ M : ℝ, 0 < M ∧
    ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {u : W1p volume (⊤ : Opens E) 2} {G g G' : E → E} {p : ℝ≥0∞} {c : E} {ρ κ δ q q' : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
      AEStronglyMeasurable a (volume.restrict H) → (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      (∀ (c : E) (r : ℝ), c₀ ≤ ⟪c, ν⟫_ℝ → 0 < r →
        ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
          UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
            ⨍ x in ball c r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
          (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
      (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) →
      (∀ x, g (hyperplaneReflection ν c₀ x) = -(ℝ ∙ ν)ᗮ.reflection (g x)) →
      (∀ x ∈ H, G' x = G x) → (∀ x, ‖G' (hyperplaneReflection ν c₀ x)‖ = ‖G' x‖) →
      2 ≤ p → MemLp g p volume → MemLp G' p volume → q.HolderConjugate q' →
      ENNReal.ofReal (2 * q) ≤ p → 0 < ρ → 1 ≤ κ →
      ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ 2 ≤
        M / κ ^ 2 * (⨍ x in ball c (κ * ρ), ‖g x‖ ^ 2) +
          M * κ ^ (n + 1) * (⨍ x in ball c (κ * ρ), ‖G' x‖ ^ 2) +
          M * κ ^ (n + 1) * ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ x in ball c (κ * ρ), ‖g x‖ ^ (2 * q)) ^ q⁻¹ := by
  obtain ⟨M, hM, hup⟩ := exists_upper_bound (n := n) hlam Lam
  refine ⟨M, hM, ?_⟩
  intro H ν c₀ a u G g G' p c ρ κ δ q q' hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p
    hq hqp hρ hκ
  rcases le_or_gt c₀ ⟪c, ν⟫_ℝ with hc | hc
  · exact hup hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq hqp hc hρ hκ
  -- Below the hyperplane, reflect to the centre `c' = ρ c`.
  set σ := hyperplaneReflection ν c₀
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  set c' := σ c
  have hc' : c₀ ≤ ⟪c', ν⟫_ℝ := by
    rw [inner_hyperplaneReflection hν]
    linarith
  have hcc : σ c' = c := hyperplaneReflection_hyperplaneReflection ν c₀ c
  -- Averages of functions invariant under `σ` agree on the two balls.
  have hinv (f : E → ℝ) (hf : ∀ x, f (σ x) = f x) (s : ℝ) :
      ⨍ x in ball c s, f x = ⨍ x in ball c' s, f x := by
    rw [← setAverage_ball_comp_hyperplaneReflection ν c₀ f c' s, hcc]
    exact average_congr (Filter.Eventually.of_forall fun x => (hf x).symm)
  have hgσ (x : E) : ‖g (σ x)‖ = ‖g x‖ := by rw [hgρ, norm_neg, LinearIsometryEquiv.norm_map]
  have hgn (k : ℝ) : ∀ x, ‖g (σ x)‖ ^ k = ‖g x‖ ^ k := fun x => by rw [hgσ]
  have hgn2 : ∀ x, ‖g (σ x)‖ ^ 2 = ‖g x‖ ^ 2 := fun x => by rw [hgσ]
  have hG'n : ∀ x, ‖G' (σ x)‖ ^ 2 = ‖G' x‖ ^ 2 := fun x => by rw [hG'ρ]
  -- The oscillation about `-R m'`, with `m'` the average over `B(c', ρ)`, is the oscillation there.
  set m' := ⨍ y in ball c' ρ, g y
  have hosc_eq : ⨍ x in ball c ρ, ‖g x - -R m'‖ ^ 2 =
      ⨍ x in ball c' ρ, ‖g x - m'‖ ^ 2 := by
    rw [← setAverage_ball_comp_hyperplaneReflection ν c₀ (fun x => ‖g x - m'‖ ^ 2) c' ρ, hcc]
    refine average_congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hgρ, show -R (g x) - m' = -R (g x - -R m') by
      rw [map_sub, map_neg, Submodule.reflection_reflection]; abel, norm_neg,
      LinearIsometryEquiv.norm_map]
  refine (setAverage_norm_sub_setAverage_sq_le_setAverage_norm_sub_sq measure_ball_lt_top.ne
    ((hgp.restrict (ball c ρ)).integrableOn_of_subset (one_le_two.trans h2p) subset_rfl
      measure_ball_lt_top.ne)
    ((hgp.restrict (ball c ρ)).integrableOn_norm_sub_sq_of_two_le h2p subset_rfl
      measure_ball_lt_top.ne (-R m'))).trans ?_
  rw [hosc_eq, hinv _ hgn2, hinv _ hG'n, hinv _ (hgn (2 * q))]
  exact hup hν hH ham hbd hosc hu0 hu hgH hgρ hG'H hG'ρ h2p hgp hG'p hq hqp hc' hρ hκ

/-- **The odd reflection of the gradient.** If `u ∈ H¹(ℝ^{n+1})` vanishes off
`H = {c₀ < ⟪x, ν⟫}` and `∇u ∈ Lᵖ`, the field `g = ∇u - R (∇u ∘ ρ)`, the gradient of the odd
reflection `u - u ∘ ρ`, agrees with `∇u` on `H`, satisfies `g ∘ ρ = -R g`, lies in `Lᵖ` and
dominates `∇u` in `Lᵖ`. Here `ρ` is the reflection in the boundary hyperplane and `R` its linear
part. -/
private theorem exists_odd_reflection_gradient {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {u : W1p volume (⊤ : Opens E) 2}
    (hu0 : ∀ᵐ x, x ∉ H → W1p.value u x = 0) {p : ℝ≥0∞}
    (hgp : MemLp (W1p.gradient u : E → E) p volume) :
    ∃ g : E → E, (∀ᵐ x, x ∈ H → g x = W1p.gradient u x) ∧
      (∀ x, g (hyperplaneReflection ν c₀ x) = -(ℝ ∙ ν)ᗮ.reflection (g x)) ∧
      MemLp g p volume ∧ eLpNorm (W1p.gradient u : E → E) p volume ≤ eLpNorm g p volume := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  have hσ := measurePreserving_hyperplaneReflection (volume : Measure E) ν c₀
  have h0 : ∀ᵐ x, ⟪x, ν⟫_ℝ < c₀ → W1p.gradient u x = 0 := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      W1p.gradient_ae_eq_zero_of_value_ae_eq_zero_of_inner_lt (u := u) hH
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using hu0)
  set g : E → E := fun x => W1p.gradient u x - R (W1p.gradient u (hyperplaneReflection ν c₀ x))
  have hgH : ∀ᵐ x, x ∈ H → g x = W1p.gradient u x := by
    filter_upwards [hσ.quasiMeasurePreserving.ae h0] with x hx hxH
    simp only [g]
    rw [hx ((inner_hyperplaneReflection_lt_iff hν c₀).2 ((hH x).1 hxH)), map_zero, sub_zero]
  refine ⟨g, hgH, fun x => ?_, hgp.sub (R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hgp.comp_measurePreserving hσ)), eLpNorm_mono_ae hgp.aestronglyMeasurable ?_⟩
  · simp only [g, hyperplaneReflection_hyperplaneReflection, map_sub,
      Submodule.reflection_reflection, R]
    abel
  -- `∇u` agrees with `g` on `H` and vanishes below the hyperplane, which is null.
  filter_upwards [hgH, h0, measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_setOf_inner_eq volume hν c₀)] with x h1 h2 h3
  rcases lt_or_gt_of_ne h3 with hlt | hgt
  · rw [h2 hlt, norm_zero]
    exact norm_nonneg _
  · rw [h1 ((hH x).2 hgt)]

/-- **The reflected datum.** For `G ∈ Lᵖ(H)`, `1 ≤ p`, the field
`G' = 1_H G - 1_H (R G) ∘ ρ` agrees with `G` on `H`, satisfies `‖G' ∘ ρ‖ = ‖G'‖`, and lies in `Lᵖ`
with `‖G'‖_{Lᵖ} ≤ 2 ‖G‖_{Lᵖ(H)}`. -/
private theorem exists_reflected_datum {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) {G : E → E}
    (hGp : MemLp G p (volume.restrict H)) :
    ∃ G' : E → E, (∀ x ∈ H, G' x = G x) ∧
      (∀ x, ‖G' (hyperplaneReflection ν c₀ x)‖ = ‖G' x‖) ∧
      MemLp G' p volume ∧ eLpNorm G' p volume ≤ 2 * eLpNorm G p (volume.restrict H) := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  have hHm : MeasurableSet (H : Set E) := H.isOpen.measurableSet
  have hRGp : MemLp (fun y => R (G y)) p (volume.restrict H) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hGp
  have hRG : eLpNorm (fun y => R (G y)) p (volume.restrict H) = eLpNorm G p (volume.restrict H) :=
    eLpNorm_congr_norm_ae hRGp.aestronglyMeasurable hGp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => R.norm_map (G y))
  refine ⟨fun x => (H : Set E).indicator G x -
      (H : Set E).indicator (fun y => R (G y)) (hyperplaneReflection ν c₀ x), fun x hx => ?_,
    fun x => ?_, ?_, ?_⟩
  · -- The reflection of a point of `H` lies outside `H`.
    have hnotH : hyperplaneReflection ν c₀ x ∉ H := by
      rw [hH, not_lt]
      exact ((inner_hyperplaneReflection_lt_iff hν c₀).2 ((hH x).1 hx)).le
    simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem hnotH, sub_zero]
  · rw [← LinearIsometryEquiv.norm_map R, ← norm_neg]
    congr 1
    simp only [hyperplaneReflection_hyperplaneReflection]
    by_cases h1 : x ∈ (H : Set E) <;> by_cases h2 : hyperplaneReflection ν c₀ x ∈ (H : Set E) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, R,
        Submodule.reflection_reflection]
  · simpa only [Measure.restrict_univ, univ_inter] using
      memLp_indicator_sub_indicator_comp_hyperplaneReflection (μ := (volume : Measure E))
        (ν := ν) (c := c₀) hHm MeasurableSet.univ (mapsTo_univ _ _) (f := G)
        (g := fun y => R (G y)) (by rwa [univ_inter]) (by rwa [univ_inter])
  · have h' := eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le
      (μ := (volume : Measure E)) (ν := ν) (c := c₀) hp hHm
      MeasurableSet.univ (mapsTo_univ _ _) (f := G) (g := fun y => R (G y))
    simp only [Measure.restrict_univ, univ_inter, hRG] at h'
    exact h'.trans_eq (two_mul _).symm

/-- **The `W^{1,p}` estimate up to a flat boundary for coefficients of small mean oscillation.**
Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`,
`λ` and `Λ`, with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `a` be
a coefficient matrix, measurable on `H` and bounded by `Λ` there, of small mean oscillation on the
half-balls: for every ball `B` centred in the closed half-space `{c₀ ≤ ⟪x, ν⟫}`, some constant
matrix `A`, uniformly elliptic with constants `λ, Λ`, has `⨍_{B ∩ H} ‖a - A‖ ≤ δ`. Let
`u ∈ H¹(ℝ^{n+1})` vanish off `H` and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`, that is
`∫_H ⟨a ∇u, ∇φ⟩ = ∫_H ⟨G, ∇φ⟩` for every test function `φ` on `H`, with `G ∈ Lᵖ(H)`, and let `∇u`
lie in `Lᵖ`. Then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`.

Only `a` on `H` matters, and the frozen matrices `A` are arbitrary elliptic matrices: neither
continuity, symmetry nor any invariance under the reflection in the boundary hyperplane is
assumed. -/
theorem exists_eLpNorm_gradient_le_of_setAverage_inter_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict H) →
        (∀ x ∈ H, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : E) (r : ℝ), c₀ ≤ ⟪c, ν⟫_ℝ → 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
          (∀ φ : 𝓓(H, ℝ), energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u)
              (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
          MemLp (W1p.gradient u : E → E) p volume → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  -- Without a positive ellipticity constant the hypothesis on the coefficients cannot hold.
  rcases le_or_gt lam 0 with hlam | hlam
  · refine ⟨0, 1, one_pos, fun {H ν c₀ a} hν _ _ _ hosc => ?_⟩
    have hz : c₀ ≤ ⟪(c₀ / ‖ν‖ ^ 2) • ν, ν⟫_ℝ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hν))]
    obtain ⟨A, hA, -⟩ := hosc _ 1 hz one_pos
    exact absurd hA.pos (not_lt.2 hlam)
  obtain ⟨M, -, hball⟩ := exists_ball_bound (n := n) hlam Lam
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le (n := n)
    («E» := E) (F := E) one_le_two (by rwa [ENNReal.ofReal_ofNat]) hp_top M M M (2 * Lam)
  refine ⟨2 * C, δ, hδ, ?_⟩
  intro H ν c₀ a hν hH ham hbd hosc u G hu0 hu hgp hGp
  obtain ⟨g, hgH, hgσ, hgp', hdom⟩ := exists_odd_reflection_gradient hν hH hu0 hgp
  obtain ⟨G', hG'H, hG'σ, hG'p, hG'le⟩ :=
    exists_reflected_datum hν hH (one_le_two.trans hp.le) hGp
  -- The sharp function method applies to `g`, by the mean oscillation bound on every ball.
  have hg := h hgp' hG'p fun q q' hq hqp c ρ κ hρ hκ => by
    simp only [Real.rpow_two]
    exact hball hν hH ham hbd hosc hu0 hu hgH hgσ hG'H hG'σ hp.le hgp' hG'p hq hqp hρ hκ
  calc eLpNorm (W1p.gradient u : E → E) p volume ≤ eLpNorm g p volume := hdom
    _ ≤ C * (2 * eLpNorm G p (volume.restrict H)) := hg.trans (by gcongr)
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * eLpNorm G p (volume.restrict H) := by
      push_cast
      ring

end PDE

end TauCeti
