/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.VariableCoefficientDecay
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Scaled
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.W1p.Multiplication
import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates up to a flat boundary for divergence-form equations

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, let `z₀` lie on its boundary
hyperplane, and let `u ∈ H¹(U)`, `B(z₀, R) ⊆ U`, vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`,

that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩ + ∫ f φ` for every test function `φ` on `U ∩ H`. So `u` has zero
boundary values on the flat part `B(z₀, R) ∩ ∂H` of the boundary. Suppose that `a` is uniformly
elliptic with constants `λ`, `Λ` on `B(z₀, R)`, that `a` and `G` are `α`-Hölder there with
constants `K_a` and `K_G`, where `K_a R^α ≤ M`, and that `f ∈ L^q(B(z₀, R) ∩ H)` with `q ≥ 2`. This
file proves the `C^{1,γ}` estimate up to the flat boundary: for `0 < γ < 1` with `γ ≤ α` and
`γ ≤ 1 - (n + 1) / q`, the precise representative of `∇u` for the Lebesgue measure on `H` is
`γ`-Hölder on `B(z₀, R / 4) ∩ closure H` with constant

`C (K_G R^{α-γ} + R^{1-(n+1)/q-γ} ‖f‖_{L^q(B_R⁺)} + R^{-(n+1)/2-γ} ‖∇u‖_{L²(B_R⁺)})`,

with `B_R⁺ = B(z₀, R) ∩ H`,

where `C` depends only on `n`, `α`, `γ`, `q`, `λ`, `Λ` and `M`
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith`). The
coefficients need no symmetry and no compatibility with the reflection in `∂H`; compare
`TauCeti.Analysis.PDE.Regularity.Boundary.GradientHolder`, where `a` is invariant under that
reflection and the odd reflection of `u` reduces the estimate to the interior one. The Hölder set
contains the boundary points: the gradient extends `γ`-Hölder continuously to the flat boundary.
This is the boundary counterpart of the interior estimate
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`
in the `TauCeti.PDE` namespace.

## The argument

By Campanato's theorem on the half-space, which has density at least one half in every ball
centred in its closure (in the `TauCeti.MeasureTheory` namespace,
`holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le`), it suffices
to show that the mean oscillation of `∇u` on `B(x, t) ∩ H` is `O(t^γ)` for every centre
`x ∈ B(z₀, R / 4) ∩ closure H` and every small radius `t`. Let `d` be the distance from `x` to
`∂H` and `z` the foot of the perpendicular. On a half-ball `B(z, s) ∩ H` the gradient lies in
square mean within `O(s^{(n+1)/2+γ})` of a multiple `p_s` of the normal `ν`, by
`exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith`.

* If `t` is not small compared with `d`, then `B(x, t) ∩ H` lies in a half-ball `B(z, s) ∩ H` with
  `s` comparable to `t`, and the boundary decay at `z` bounds the oscillation.
* If `t` is small compared with `d`, then `B(x, d) ⊆ H` and the interior decay applies. It is
  applied to `u - ⟪p, ·⟫` with `p = p_{2d}`, which solves the equation with `G` replaced by the
  field `G - a p`, of Hölder constant `K_G + K_a ‖p‖`. Its energy on `B(x, d)` is the square mean
  distance of `∇u` from `p`, which the boundary decay at `z` bounds by `O(d^{n+1+2γ})`, so the
  interior excess decay from scale `d` down to scale `t`
  (`TauCeti.PDE.exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith`) gives
  `O(t^{n+1+2γ})`. The size of `p` is controlled by the Morrey decay at `z`
  (`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le_of_holderOnWith`). Points far from
  `∂H` compared with `R` are handled by the interior decay applied to `u` itself.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith`: the `C^{1,γ}`
  estimate up to a flat boundary.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Affine

variable {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} {α Ka KG : ℝ≥0}

/-- The field `x ↦ a(x) p` of a constant vector `p`, written through the Riesz representation: its
inner product with `ξ` is `ξᵀ a(x) p`. -/
private def coefficientField
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p : EuclideanSpace ℝ (Fin (n + 1))) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm ((matrixBilinearForm (a x)).flip p)

private theorem inner_coefficientField (p x ξ : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪coefficientField a p x, ξ⟫_ℝ = matrixBilinearForm (a x) ξ p := by
  rw [coefficientField, toDual_symm_apply, ContinuousLinearMap.flip_apply]

/-- If the bilinear forms of `a` are `α`-Hölder with constant `K_a`, then `x ↦ a(x) p` is `α`-Hölder
with constant `K_a ‖p‖`. -/
private theorem holderOnWith_coefficientField {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) s)
    (p : EuclideanSpace ℝ (Fin (n + 1))) :
    HolderOnWith (Ka * ‖p‖₊) α (coefficientField a p) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  rw [dist_eq_norm, coefficientField, coefficientField, ← map_sub, LinearIsometryEquiv.norm_map]
  have hle : ‖(matrixBilinearForm (a x)).flip p - (matrixBilinearForm (a y)).flip p‖ ≤
      ‖matrixBilinearForm (a x) - matrixBilinearForm (a y)‖ * ‖p‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
    have h := (matrixBilinearForm (a x) - matrixBilinearForm (a y)).le_opNorm₂ ξ p
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.flip_apply] at h ⊢
    linarith
  calc _ ≤ _ := hle
    _ ≤ (Ka : ℝ) * dist x y ^ (α : ℝ) * ‖p‖ := by
        have hd := haK.dist_le hx hy
        rw [dist_eq_norm] at hd
        exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ = _ := by push_cast; ring

/-- **Subtracting a linear function.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on
`Ω`, and let `B ⊆ Ω ∩ B(z₀, R)` be open, with `a` uniformly elliptic on `B` and `a`, `G` Hölder on
`B(z₀, R)`. For a constant vector `p`, the restriction of `u - ⟪p, ·⟫` to `B` lies in `H¹(B)`, has
gradient `∇u - p`, and solves `-∂ᵢ(aⁱʲ ∂ⱼv) = f - div (G - a p)` weakly on `B`. -/
private theorem exists_gradient_ae_eq_sub_and_energyFormH1
    {Omega B : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hB : B ≤ Omega)
    (hBR : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z₀ R) {lam Lam : ℝ}
    (h : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam) (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R))
    (hGK : HolderOnWith KG α G (ball z₀ R)) {u : W1p volume Omega 2}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ v : W1p volume B 2,
      (W1p.gradient v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          =ᵐ[volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        (fun x => W1p.gradient u x - p) ∧
      ∀ φ : 𝓓(B, ℝ), energyFormH1 a 0 0 v (W1p.ofTestFunctionₗ volume B 2 φ) =
        (∫ x in B, ⟪G x - coefficientField a p x,
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in B, f x * φ x := by
  -- The Sobolev class `ℓ` on `B` of the linear function `⟪p, ·⟫`, whose gradient is `p`.
  obtain ⟨ℓ, -, hℓ⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (p := 2) (Omega := B) (u := fun y => ⟪p, y⟫_ℝ) isOpen_univ
    (contDiff_const.inner ℝ contDiff_id).contDiffOn (isBounded_ball.subset hBR).isCompact_closure
    subset_closure (subset_univ _)
  rw [show ∇ (fun y => ⟪p, y⟫_ℝ) = fun _ => p from funext (gradient_inner_const_left p)] at hℓ
  refine ⟨W1p.restrictL hB u - ℓ, ?_, fun φ => ?_⟩
  · rw [← W1p.gradientL_apply, map_sub, W1p.gradientL_apply, W1p.gradientL_apply]
    filter_upwards [Lp.coeFn_sub (W1p.gradient (W1p.restrictL hB u)) (W1p.gradient ℓ),
      W1p.gradient_restrictL_ae hB u, hℓ] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  · have hcoeff := memLp_energyIntegrand_of_holderOnWith (mu := volume) hBR h hα haK
    have hGc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) B.isOpen.measurableSet hBR hα hGK
    rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff,
      energyFormH1_restrictL_ofTestFunctionₗ_eq_setIntegral_inner_add_setIntegral hB hcoeff hu hGc
        hf φ,
      energyFormH1_zero_zero_eq_setIntegral]
    -- The energy of `ℓ` against `φ` is `∫_B ⟪a p, ∇φ⟫`.
    have hℓφ : ∫ x in B,
        matrixBilinearForm (a x) (W1p.gradient (W1p.ofTestFunctionₗ volume B 2 φ) x)
        (W1p.gradient ℓ x) =
        ∫ x in B, ⟪coefficientField a p x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
      refine integral_congr_ae ?_
      filter_upwards [hℓ, gradientTestFunctionLp_apply_ae (mu := volume) (2 : ℝ≥0∞) φ] with y h1 h2
      rw [W1p.gradient_ofTestFunctionₗ, h1, h2, inner_coefficientField]
    rw [hℓφ]
    -- Split `∫_B ⟪G - a p, ∇φ⟫` through the `L²` pairings.
    have hwK := holderOnWith_coefficientField haK p
    have hwc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) B.isOpen.measurableSet hBR hα hwK
    have hGwc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) B.isOpen.measurableSet hBR hα
      (hGK.sub hwK)
    have h1 := inner_toLp_gradient_ofTestFunctionₗ hGc φ
    have h2 := inner_toLp_gradient_ofTestFunctionₗ hwc φ
    have h3 := inner_toLp_gradient_ofTestFunctionₗ hGwc φ
    have hsub : hGwc.toLp = hGc.toLp - hwc.toLp := by
      rw [← MemLp.toLp_sub]
      exact MemLp.toLp_congr _ _ (ae_of_all _ fun y => by simp only [Pi.sub_apply]; abel)
    rw [hsub, inner_sub_left, h1, h2] at h3
    simp only [Pi.sub_apply] at h3
    rw [← h3]
    ring


/-- **Interior decay of the excess over a constant vector.** Let `0 < γ < 1` with `γ ≤ α`. There are
`θ ∈ (0, 1]` and `C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that the following
holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `Ω`, with `a` uniformly elliptic
on `B(z₀, R)`, `a` and `G` `α`-Hölder there with constants `K_a`, `K_G`, `K_a R^α ≤ M`. Let
`B(x, r) ⊆ Ω ∩ B(z₀, R)` and let `p` be a constant vector. If the data with the field `G - a p`
decay like `s^{2α} (K_G + K_a ‖p‖)² s^{n+1} + 4 s² ∫_{B(x, s)} f² ≤ W (s / r)^{n+1+2γ}` for
`0 < s ≤ r`, and `∫_{B(x, r)} ‖∇u - p‖² ≤ W`, then for `0 < t ≤ θ r` some constant vector `c` has
`∫_{B(x, t)} ‖∇u - c‖² ≤ C W (t / r)^{n+1+2γ}`. -/
private theorem exists_setIntegral_ball_norm_gradient_sub_sq_le_of_sub {α : ℝ≥0} {γ : ℝ}
    (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {z₀ x p : EuclideanSpace ℝ (Fin (n + 1))}
      {R r W : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball z₀ R) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R) →
      HolderOnWith KG α G (ball z₀ R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      MemLp f 2 (volume.restrict (ball x r)) → 0 < r → r ≤ R → ball x r ⊆ ball z₀ R →
      ball x r ⊆ Omega →
      (∀ s, 0 < s → s ≤ r → s ^ (2 * (α : ℝ)) * (((KG : ℝ) + Ka * ‖p‖) ^ 2 * s ^ ((n : ℝ) + 1)) +
        4 * s ^ 2 * ∫ y in ball x s, f y ^ 2 ≤ W * (s / r) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ y in ball x r, ‖W1p.gradient u y - p‖ ^ 2 ≤ W →
      ∀ t, 0 < t → t ≤ θ * r → ∃ c : EuclideanSpace ℝ (Fin (n + 1)),
        ∫ y in ball x t, ‖W1p.gradient u y - c‖ ^ 2 ≤
          C * W * (t / r) ^ (2 * γ + ((n : ℝ) + 1)) := by
  obtain ⟨θ, C, hθ, hθ1, hC, hdec⟩ :=
    exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith (n := n) hγ hγα hγ1
      (lam := lam) (Lam := Lam) (M := M)
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro Omega u a G f z₀ x p R r W Ka KG h haK hGK hM hu hf hr hrR hxR hxΩ hD hW t ht htθ
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x r, isOpen_ball⟩
  obtain ⟨v, hv, hveq⟩ :=
    exists_gradient_ae_eq_sub_and_energyFormH1 (B := B) hxΩ hxR (h.mono_set hxR) hα haK hGK hf hu p
  have hKG' : HolderOnWith (KG + Ka * ‖p‖₊) α (fun y => G y - coefficientField a p y)
      (ball x r) := (hGK.sub (holderOnWith_coefficientField haK p)).mono hxR
  have hMr : (Ka : ℝ) * r ^ (α : ℝ) ≤ M := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hr.le hrR α.property) Ka.property).trans hM
  -- The energy of `v` on `B(x, r)` is the square mean distance of `∇u` from `p`.
  have hvW : ∫ y in ball x r, ‖W1p.gradient v y‖ ^ 2 ≤ W := by
    refine le_of_eq_of_le (integral_congr_ae ?_) hW
    filter_upwards [hv] with y hy
    rw [hy]
  have h' := hdec (Omega := B) (u := v) (G := fun y => G y - coefficientField a p y)
    (s := ball z₀ R) (z := x) (R := r) (V := W) (KG := KG + Ka * ‖p‖₊) h (hxR (mem_ball_self hr))
    (haK.mono hxR)
    hKG' hveq hf subset_rfl hr hMr (fun s hs hsr => by push_cast; exact hD s hs hsr) hvW t ht htθ
  refine ⟨(⨍ y in ball x t, W1p.gradient v y) + p, le_of_eq_of_le (integral_congr_ae ?_) h'⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (htθ.trans
    (mul_le_of_le_one_left hr.le hθ1))) hv] with y hy
  rw [hy, sub_add_eq_sub_sub_swap]

end Affine

section Decay

/-- **The data on a ball, for a datum on a half-ball.** Let `f ∈ L^q(B(z₀, R) ∩ H)` with `q ≥ 2`,
let `γ ≤ α` and `γ ≤ 1 - (n + 1) / q`, and let `Q` bound both `ρ^{α-γ} K` and
`ρ^{1-(n+1)/q-γ} ‖f‖_{L^q(B(z₀, R) ∩ H)}`. If `B(w, r) ⊆ B(z₀, R)` with `0 < r ≤ ρ`, then

`r^{2α} K² r^{n+1} + 4 r² ∫_{B(w, r) ∩ H} f²`
`  ≤ (1 + 4 ω^{1-2/q}) (ρ^{(n+1)/2+γ} Q)² (r / ρ)^{n+1+2γ}`,

where `ω` is the volume of the unit ball. This is
`TauCeti.PDE.rpow_mul_add_mul_setIntegral_sq_le` for the extension of `f` by zero off `H`. -/
private theorem rpow_mul_add_mul_setIntegral_inter_sq_le
    {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {z₀ w : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hf : MemLp f q (volume.restrict (ball z₀ R ∩ H))) {α γ K Q ρ r : ℝ} (hγα : γ ≤ α)
    (hγq : γ ≤ 1 - ((n : ℝ) + 1) / q.toReal) (hK : 0 ≤ K) (hKQ : ρ ^ (α - γ) * K ≤ Q)
    (hfQ : ρ ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
      (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal ≤ Q)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hsub : ball w r ⊆ ball z₀ R) :
    r ^ (2 * α) * (K ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * ∫ x in ball w r ∩ H, f x ^ 2 ≤
      (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^ (1 - 2 / q.toReal)) *
        (ρ ^ (((n : ℝ) + 1) / 2 + γ) * Q) ^ 2 * (r / ρ) ^ ((n : ℝ) + 1 + 2 * γ) := by
  have hHm : MeasurableSet (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) := H.isOpen.measurableSet
  have hf' : MemLp ((H : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator f) q
      (volume.restrict (ball z₀ R)) := by
    rw [memLp_indicator_iff_restrict hHm.nullMeasurableSet, Measure.restrict_restrict hHm,
      inter_comm]
    exact hf
  have hnorm : eLpNorm ((H : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator f) q
      (volume.restrict (ball z₀ R)) = eLpNorm f q (volume.restrict (ball z₀ R ∩ H)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hHm.nullMeasurableSet,
      Measure.restrict_restrict hHm, inter_comm]
  have hint : ∫ x in ball w r ∩ H, f x ^ 2 =
      ∫ x in ball w r, (H : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator f x ^ 2 := by
    rw [← setIntegral_indicator hHm]
    congr 1
    funext x
    by_cases hx : x ∈ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) <;> simp [hx]
  rw [hint]
  exact rpow_mul_add_mul_setIntegral_sq_le hq hf' hγα hγq hK hKQ (by rwa [hnorm]) hr hrρ hsub


/-- **Decay at the boundary points of a half-ball.** In the setting of the main theorem, there are
`θ ∈ (0, 1]` and `C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that at every point
`z` of the boundary hyperplane in `B(z₀, R / 2)` and for `0 < s ≤ θ R / 2`, with
`B_s⁺ = B(z, s) ∩ H` and `p_s` the multiple of `ν` closest to `∇u` in `L²(B_s⁺)`,

`∫_{B_s⁺} ‖∇u - p_s‖² ≤ C V (2 s / R)^{n+1+2γ}` and `∫_{B_s⁺} ‖∇u‖² ≤ C V (2 s / R)^{n+1}`,

where `V = ∫_{B(z₀, R) ∩ H} ‖∇u‖² + c₁ (R^{(n+1)/2+γ} Q₀)²` with
`Q₀ = K_G R^{α-γ} + R^{1-(n+1)/q-γ} ‖f‖_{L^q(B(z₀, R) ∩ H)}` and `c₁ = 1 + 4 ω^{1-2/q}`. -/
private theorem exists_boundary_decay {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1)
    {q : ℝ≥0∞} (hq : 2 ≤ q) (hγq : γ ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν z₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ R : ℝ} {Ka KG : ℝ≥0},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
      UniformlyEllipticOn (ball z₀ R) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R) →
      HolderOnWith KG α G (ball z₀ R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball z₀ R ∩ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      ball z₀ R ⊆ U → 0 < R →
      ∀ z, ⟪z, ν⟫_ℝ = c₀ → z ∈ ball z₀ (R / 2) → ∀ s, 0 < s → s ≤ θ * (R / 2) →
        (∫ x in ball z s ∩ H, ‖W1p.gradient u x -
            (⟪⨍ y in ball z s ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
          C * ((∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2) +
            (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^
              (1 - 2 / q.toReal)) * (R ^ (((n : ℝ) + 1) / 2 + γ) *
                (KG * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
                  (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal)) ^ 2) *
            (s / (R / 2)) ^ ((n : ℝ) + 1 + 2 * γ)) ∧
        ∫ x in ball z s ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤
          C * ((∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2) +
            (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^
              (1 - 2 / q.toReal)) * (R ^ (((n : ℝ) + 1) / 2 + γ) *
                (KG * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
                  (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal)) ^ 2) *
            (s / (R / 2)) ^ ((n : ℝ) + 1) := by
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  obtain ⟨θ₁, C₁, hθ₁, hθ₁1, hC₁, h₁⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith
      (n := n) hγ hγα hγ1 (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨θ₂, C₂, hθ₂, -, hC₂, h₂⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sq_le_of_holderOnWith (n := n) hα hγ (lam := lam)
      (Lam := Lam) (M := M)
  refine ⟨min θ₁ θ₂, C₁ + C₂, lt_min hθ₁ hθ₂, (min_le_left _ _).trans hθ₁1, by positivity, ?_⟩
  intro U H u a G f ν z₀ c₀ R Ka KG hν hH h haK hGK hM hf hvan hu hU hR z hz hzR s hs hsθ
  set Kf := (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal
  set c₁ := 1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^ (1 - 2 / q.toReal)
  set Q₀ := (KG : ℝ) * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf
  set V := (∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2) +
    c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2 with hVdef
  have hR2 : 0 < R / 2 := half_pos hR
  have hR2R : R / 2 ≤ R := half_le_self hR.le
  have hsub : ball z (R / 2) ⊆ ball z₀ R := ball_subset_ball' (by
    rw [mem_ball] at hzR
    linarith)
  have hΦ0 : 0 ≤ ∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have hKf : 0 ≤ Kf := ENNReal.toReal_nonneg
  have hpow : ∀ {e : ℝ}, 0 ≤ e → (R / 2) ^ e ≤ R ^ e := fun he =>
    Real.rpow_le_rpow hR2.le hR2R he
  have hγα' : (0 : ℝ) ≤ (α : ℝ) - γ := sub_nonneg.2 hγα
  have hγq' : (0 : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal - γ := by linarith
  -- The data at the boundary point `z` decay with the exponent `n + 1 + 2γ`.
  have hD : ∀ r, 0 < r → r ≤ R / 2 → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / (R / 2)) ^ ((n : ℝ) + 1 + 2 * γ) := by
    intro r hr hrR
    have hKQ : (R / 2) ^ ((α : ℝ) - γ) * KG ≤ Q₀ := by
      refine le_add_of_le_of_nonneg ?_ (by positivity)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hpow hγα') KG.coe_nonneg
    have hfQ : (R / 2) ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf ≤ Q₀ :=
      le_add_of_nonneg_of_le (by positivity) (mul_le_mul_of_nonneg_right (hpow hγq') hKf)
    have hdat := rpow_mul_add_mul_setIntegral_inter_sq_le (w := z) hq hf hγα hγq KG.coe_nonneg
      hKQ hfQ hr hrR ((ball_subset_ball hrR).trans hsub)
    refine hdat.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc c₁ * ((R / 2) ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2
        ≤ c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2 := by
          gcongr
      _ ≤ V := by rw [hVdef]; linarith
  have hΦ : ∫ x in ball z (R / 2) ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V :=
    (setIntegral_mono_set (by
        simpa only [sub_zero] using (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
          (inter_subset_left.trans hU) measure_ball_inter_ne_top
          (0 : EuclideanSpace ℝ (Fin (n + 1))))
      (ae_of_all _ fun _ => by positivity)
      (inter_subset_inter_left _ hsub).eventuallySubset).trans (by
        rw [hVdef]; exact le_add_of_nonneg_right (by positivity))
  have hfin : IsFiniteMeasure (volume.restrict (ball z₀ R ∩ H)) :=
    isFiniteMeasure_restrict.2 measure_ball_inter_ne_top
  have hf2 : MemLp f 2 (volume.restrict (ball z (R / 2) ∩ H)) :=
    (hf.mono_exponent hq).mono_measure (Measure.restrict_mono (inter_subset_inter_left _ hsub)
      le_rfl)
  have hMR : (Ka : ℝ) * (R / 2) ^ (α : ℝ) ≤ M :=
    (mul_le_mul_of_nonneg_left (hpow α.property) Ka.property).trans hM
  have hzs : z ∈ ball z₀ R := hsub (mem_ball_self hR2)
  constructor
  · refine (h₁ h hzs hν hH hz (haK.mono hsub) (hGK.mono hsub) hvan hu hf2
      (hsub.trans hU) hR2 hMR
      hD hΦ s hs (hsθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hR2.le))).trans ?_
    gcongr
    exact le_add_of_nonneg_right hC₂
  · refine (h₂ h hzs hν hH hz (haK.mono hsub) (hGK.mono hsub) hvan hu hf2
      (hsub.trans hU) hR2 hMR
      (fun r hr hrR => (hD r hr hrR)) hΦ s hs
      (hsθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hR2.le))).trans ?_
    gcongr
    exact le_add_of_nonneg_left hC₁


/-- **Decay at the interior balls of a half-ball.** In the setting of the main theorem, there are
`θ ∈ (0, 1]` and `C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that the following
holds for every ball `B(x, r) ⊆ B(z₀, R) ∩ H` and every constant vector `p`. Let
`Q₀ = K_G R^{α-γ} + R^{1-(n+1)/q-γ} ‖f‖_{L^q(B(z₀, R) ∩ H)}` and `c₁ = 1 + 4 ω^{1-2/q}`. If
`c₁ (r^{(n+1)/2+γ} (Q₀ + R^{α-γ} K_a ‖p‖))² ≤ W` and `∫_{B(x, r)} ‖∇u - p‖² ≤ W`, then for
`0 < t ≤ θ r` some constant vector `c` has `∫_{B(x, t)} ‖∇u - c‖² ≤ C W (t / r)^{n+1+2γ}`. -/
private theorem exists_interior_decay {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1)
    {q : ℝ≥0∞} (hq : 2 ≤ q) (hγq : γ ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {z₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {R : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball z₀ R) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R) →
      HolderOnWith KG α G (ball z₀ R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball z₀ R ∩ H)) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      ball z₀ R ⊆ U →
      ∀ (x p : EuclideanSpace ℝ (Fin (n + 1))) (r W : ℝ), ball x r ⊆ ball z₀ R ∩ H → 0 < r →
        r ≤ R →
        (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^ (1 - 2 / q.toReal)) *
          (r ^ (((n : ℝ) + 1) / 2 + γ) * ((KG * R ^ ((α : ℝ) - γ) +
            R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
              (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal) +
            R ^ ((α : ℝ) - γ) * Ka * ‖p‖)) ^ 2 ≤ W →
        ∫ y in ball x r, ‖W1p.gradient u y - p‖ ^ 2 ≤ W →
        ∀ t, 0 < t → t ≤ θ * r → ∃ c : EuclideanSpace ℝ (Fin (n + 1)),
          ∫ y in ball x t, ‖W1p.gradient u y - c‖ ^ 2 ≤
            C * W * (t / r) ^ ((n : ℝ) + 1 + 2 * γ) := by
  obtain ⟨θ, C, hθ, hθ1, hC, hI⟩ :=
    exists_setIntegral_ball_norm_gradient_sub_sq_le_of_sub (n := n) hγ hγα hγ1 (lam := lam)
      (Lam := Lam) (M := M)
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro U H u a G f z₀ R Ka KG h haK hGK hM hf hu hU x p r W hxr hr hrR hW hΦ t ht htθ
  set Kf := (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal
  have hxR : ball x r ⊆ ball z₀ R := hxr.trans inter_subset_left
  have hxH : ball x r ⊆ H := hxr.trans inter_subset_right
  have hxUH : ball x r ⊆ ((U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
      Set (EuclideanSpace ℝ (Fin (n + 1)))) := fun y hy => ⟨hU (hxR hy), hxH hy⟩
  have hfin : IsFiniteMeasure (volume.restrict (ball z₀ R ∩ H)) :=
    isFiniteMeasure_restrict.2 measure_ball_inter_ne_top
  have hf2 : MemLp f 2 (volume.restrict (ball x r)) :=
    (hf.mono_exponent hq).mono_measure (Measure.restrict_mono hxr le_rfl)
  have hgrad := W1p.gradient_restrictL_ae
    (inf_le_left : (U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ U) u
  have hgradr := ae_restrict_of_ae_restrict_of_subset hxUH hgrad
  have hpowR : ∀ {e : ℝ}, 0 ≤ e → r ^ e ≤ R ^ e := fun he => Real.rpow_le_rpow hr.le hrR he
  have hγα' : (0 : ℝ) ≤ (α : ℝ) - γ := sub_nonneg.2 hγα
  have hγq' : (0 : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal - γ := by linarith
  have hKf : 0 ≤ Kf := ENNReal.toReal_nonneg
  -- The data with the field `G - a p` decay with the exponent `n + 1 + 2γ` from scale `r`.
  have hD : ∀ s, 0 < s → s ≤ r → s ^ (2 * (α : ℝ)) * (((KG : ℝ) + Ka * ‖p‖) ^ 2 *
      s ^ ((n : ℝ) + 1)) + 4 * s ^ 2 * ∫ y in ball x s, f y ^ 2 ≤
        W * (s / r) ^ ((n : ℝ) + 1 + 2 * γ) := by
    intro s hs hsr
    have hint : ∫ y in ball x s, f y ^ 2 = ∫ y in ball x s ∩ H, f y ^ 2 := by
      rw [inter_eq_left.2 ((ball_subset_ball hsr).trans hxH)]
    have hKQ : r ^ ((α : ℝ) - γ) * ((KG : ℝ) + Ka * ‖p‖) ≤
        (KG * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf) +
          R ^ ((α : ℝ) - γ) * Ka * ‖p‖ := by
      have := hpowR hγα'
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ KG + Ka * ‖p‖),
        mul_nonneg (Real.rpow_nonneg (hr.le.trans hrR) (1 - ((n : ℝ) + 1) / q.toReal - γ)) hKf]
    have hfQ : r ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf ≤
        (KG * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf) +
          R ^ ((α : ℝ) - γ) * Ka * ‖p‖ := by
      have := mul_le_mul_of_nonneg_right (hpowR hγq') hKf
      have hR0 : 0 ≤ R := hr.le.trans hrR
      have h0 : 0 ≤ (KG : ℝ) * R ^ ((α : ℝ) - γ) :=
        mul_nonneg KG.coe_nonneg (Real.rpow_nonneg hR0 _)
      have h1 : 0 ≤ R ^ ((α : ℝ) - γ) * Ka * ‖p‖ :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hR0 _) Ka.coe_nonneg) (norm_nonneg _)
      linarith
    rw [hint]
    exact (rpow_mul_add_mul_setIntegral_inter_sq_le (w := x) hq hf hγα hγq (by positivity) hKQ hfQ
      hs hsr ((ball_subset_ball hsr).trans hxR)).trans
      (mul_le_mul_of_nonneg_right hW (by positivity))
  have hΦ' : ∫ y in ball x r, ‖W1p.gradient (W1p.restrictL inf_le_left u) y - p‖ ^ 2 ≤ W :=
    le_of_eq_of_le (integral_congr_ae (hgradr.mono fun y hy => by dsimp only; rw [hy])) hΦ
  obtain ⟨c, hc⟩ := hI (Omega := U ⊓ H) (u := W1p.restrictL inf_le_left u) h haK hGK hM hu hf2 hr
    hrR hxR hxUH hD hΦ' t ht htθ
  refine ⟨c, le_of_eq_of_le (integral_congr_ae ?_) (hc.trans_eq ?_)⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset
      ((ball_subset_ball (htθ.trans (mul_le_of_le_one_left hr.le hθ1))).trans hxUH) hgrad]
      with y hy
    rw [hy]
  · rw [show 2 * γ + ((n : ℝ) + 1) = (n : ℝ) + 1 + 2 * γ by ring]

end Decay

section Oscillation

variable {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {H : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x z : EuclideanSpace ℝ (Fin (n + 1))}

/-- **Balls large compared with the distance to the boundary.** If `x` lies at distance `d` from a
boundary point `z` and `θ' d < t`, then `B(x, t) ∩ H` lies in the half-ball `B(z, 2 t / θ') ∩ H`,
where the boundary decay at `z` applies. -/
private theorem exists_setIntegral_sub_sq_le_of_lt {P : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    {R θ θ' C V t d e : ℝ} (hθ' : 0 < θ') (hθ'1 : θ' ≤ 1) (hR : 0 < R) (ht : 0 < t)
    (hxz : dist x z = d) (hdt : θ' * d < t) (htκ : t ≤ θ' * θ / 4 * R)
    (hB : ∀ s, 0 < s → s ≤ θ * (R / 2) →
      ∫ y in ball z s ∩ H, ‖g y - P s‖ ^ 2 ≤ C * V * (s / (R / 2)) ^ e) :
    ball x t ∩ H ⊆ ball z (2 * t / θ') ∩ H ∧ 2 * t / θ' ≤ θ * (R / 2) ∧
      ∫ y in ball z (2 * t / θ') ∩ H, ‖g y - P (2 * t / θ')‖ ^ 2 ≤
        C * (4 / θ') ^ e * V * (t / R) ^ e := by
  have hs : 0 < 2 * t / θ' := by positivity
  have hsθ : 2 * t / θ' ≤ θ * (R / 2) := by
    rw [div_le_iff₀ hθ']
    nlinarith
  refine ⟨inter_subset_inter_left _ fun y hy => ?_, hsθ, (hB _ hs hsθ).trans_eq ?_⟩
  · rw [mem_ball] at hy ⊢
    have hd : d < t / θ' := by rwa [lt_div_iff₀ hθ', mul_comm]
    have htt : t ≤ t / θ' := le_div_self ht.le hθ' hθ'1
    calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ < t + t / θ' := by rw [hxz]; linarith
      _ ≤ 2 * t / θ' := by rw [mul_div_assoc, two_mul]; linarith
  · rw [show 2 * t / θ' / (R / 2) = 4 / θ' * (t / R) by field_simp; ring,
      Real.mul_rpow (by positivity) (by positivity)]
    ring


/-- **The shifted data at a ball of radius `d`.** With `m = n + 1` and `a = m / 2 + γ`, if
`0 ≤ R^α K ≤ M`, `R^m P² ≤ K_p V` and `c₁ (R^a Q₀)² ≤ V`, then

`c₁ (d^a (Q₀ + R^{α-γ} K P))² ≤ (2 + 2 c₁ M² K_p) V (d / R)^{m+2γ}`.

This is the data term of the equation for `u - ⟪p, ·⟫`, whose field `G - a p` has the Hölder
constant `K_G + K_a ‖p‖`. -/
private theorem mul_sq_rpow_mul_add_le {c₁ d R Q₀ K P M V Kp γ α : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hc₁ : 0 ≤ c₁) (hK : 0 ≤ K) (hKM : K * R ^ α ≤ M)
    (hPV : R ^ ((n : ℝ) + 1) * P ^ 2 ≤ Kp * V)
    (hV : c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2 ≤ V) :
    c₁ * (d ^ (((n : ℝ) + 1) / 2 + γ) * (Q₀ + R ^ (α - γ) * K * P)) ^ 2 ≤
      (2 + 2 * c₁ * M ^ 2 * Kp) * V * (d / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  set a := ((n : ℝ) + 1) / 2 + γ
  have hdR : 0 < d / R := div_pos hd hR
  have h1 : d ^ a = R ^ a * (d / R) ^ a := by
    rw [Real.div_rpow hd.le hR.le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hR a).ne']
  have h2 : ((d / R) ^ a) ^ 2 = (d / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdR.le]
    congr 1
    push_cast
    ring
  have h3 : R ^ a * (R ^ (α - γ) * K * P) = R ^ (((n : ℝ) + 1) / 2) * (K * R ^ α) * P := by
    rw [show R ^ a * (R ^ (α - γ) * K * P) = (R ^ a * R ^ (α - γ)) * K * P by ring,
      ← Real.rpow_add hR, show a + (α - γ) = ((n : ℝ) + 1) / 2 + α by ring, Real.rpow_add hR]
    ring
  have h4 : (R ^ (((n : ℝ) + 1) / 2)) ^ 2 = R ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    ring
  have hKR : 0 ≤ K * R ^ α := mul_nonneg hK (Real.rpow_nonneg hR.le α)
  have hsq : (K * R ^ α) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hKR hKM 2
  set x := R ^ a * Q₀
  set y := R ^ (((n : ℝ) + 1) / 2) * (K * R ^ α) * P
  have hy : y ^ 2 ≤ M ^ 2 * (Kp * V) := by
    have : y ^ 2 = (K * R ^ α) ^ 2 * (R ^ ((n : ℝ) + 1) * P ^ 2) := by
      simp only [y]
      rw [← h4]
      ring
    rw [this]
    exact mul_le_mul hsq hPV (mul_nonneg (Real.rpow_nonneg hR.le _) (sq_nonneg _)) (sq_nonneg _)
  have hxy : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have heq : c₁ * (d ^ a * (Q₀ + R ^ (α - γ) * K * P)) ^ 2 =
      c₁ * (x + y) ^ 2 * (d / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
    rw [← h2, h1, ← h3]
    simp only [x]
    ring
  rw [heq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hdR.le _)
  calc c₁ * (x + y) ^ 2 ≤ c₁ * (2 * x ^ 2 + 2 * y ^ 2) := mul_le_mul_of_nonneg_left hxy hc₁
    _ = 2 * (c₁ * x ^ 2) + 2 * c₁ * y ^ 2 := by ring
    _ ≤ 2 * V + 2 * c₁ * (M ^ 2 * (Kp * V)) := by
        gcongr
    _ = (2 + 2 * c₁ * M ^ 2 * Kp) * V := by ring

/-- **The size of the normal part of the average gradient.** If `p` is at most the average of `g`
over a set `S` with `|S| ≥ ω (2d)^{n+1} / 2`, and `∫_S ‖g‖² ≤ C V (2d / (R / 2))^{n+1}`, then
`R^{n+1} ‖p‖² ≤ 2^{n+2} C V / ω`, here written `w₁`. -/
private theorem rpow_mul_norm_sq_le {S : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p : EuclideanSpace ℝ (Fin (n + 1))} {d R C V w₁ : ℝ} (hd : 0 < d) (hR : 0 < R) (hw₁ : 0 < w₁)
    (hS : volume S ≠ ⊤) (hg : MemLp g 2 (volume.restrict S))
    (hSd : 2⁻¹ * (w₁ * (2 * d) ^ (n + 1)) ≤ volume.real S)
    (hint : ∫ y in S, ‖g y‖ ^ 2 ≤ C * V * (2 * d / (R / 2)) ^ ((n : ℝ) + 1))
    (hp : ‖p‖ ≤ ‖⨍ y in S, g y‖) :
    R ^ ((n : ℝ) + 1) * ‖p‖ ^ 2 ≤ 2 ^ (n + 2) * C * V / w₁ := by
  have hm := (measureReal_mul_sq_norm_setAverage_le hS hg).trans hint
  have hpow : (2 * d / (R / 2)) ^ ((n : ℝ) + 1) = (2 * d) ^ (n + 1) * 2 ^ (n + 1) /
      R ^ ((n : ℝ) + 1) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.div_rpow hR.le zero_le_two,
      show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  have hRpos : 0 < R ^ ((n : ℝ) + 1) := Real.rpow_pos_of_pos hR _
  have hp2 : ‖p‖ ^ 2 ≤ ‖⨍ y in S, g y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hkey : 2⁻¹ * (w₁ * (2 * d) ^ (n + 1)) * ‖p‖ ^ 2 ≤
      C * V * ((2 * d) ^ (n + 1) * 2 ^ (n + 1) / R ^ ((n : ℝ) + 1)) := by
    rw [← hpow]
    exact (mul_le_mul hSd hp2 (sq_nonneg _) measureReal_nonneg).trans hm
  have hd' : 0 < (2 * d) ^ (n + 1) := by positivity
  rw [le_div_iff₀ hw₁]
  rw [mul_div_assoc', le_div_iff₀ hRpos] at hkey
  have : (2 * d) ^ (n + 1) * (2⁻¹ * (w₁ * (R ^ ((n : ℝ) + 1) * ‖p‖ ^ 2))) ≤
      (2 * d) ^ (n + 1) * (2 ^ (n + 1) * C * V) := by
    nlinarith
  have h' := le_of_mul_le_mul_left this hd'
  rw [pow_succ 2 (n + 1)]
  nlinarith


/-- **Small balls near the boundary.** Let `x` be at distance `d` from the boundary point `z`, with
`B(x, d) ⊆ B(z, 2d) ∩ H`, and let `p` be at most the average of `g` over `S = B(z, 2d) ∩ H`, with
`|S| ≥ ω (2d)^{n+1} / 2`. Suppose that the boundary decay at `z` bounds `∫_S ‖g - p‖²` and
`∫_S ‖g‖²`, and that the interior decay holds on `B(x, d)` for the excess over `p`, with the shifted
data of `mul_sq_rpow_mul_add_le`, at the radius `t ≥ 0`. Then some constant vector `c` has
`∫_{B(x, t)} ‖g - c‖² ≤ C' V (t / R)^{n+1+2γ}`, with `C'` depending only on the constants. -/
private theorem exists_setIntegral_ball_sub_sq_le_of_near {p : EuclideanSpace ℝ (Fin (n + 1))}
    {R C Ci V d c₁ Q₀ Ka M w₁ γ α t : ℝ} (hd : 0 < d) (hR : 0 < R) (hw₁ : 0 < w₁) (ht : 0 ≤ t)
    (hc₁ : 0 ≤ c₁) (hKa : 0 ≤ Ka) (hKaM : Ka * R ^ α ≤ M) (hC : 0 ≤ C)
    (hV : c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2 ≤ V)
    (hsub : ball x d ⊆ ball z (2 * d) ∩ H) (hSfin : volume (ball z (2 * d) ∩ H) ≠ ⊤)
    (hgS : MemLp g 2 (volume.restrict (ball z (2 * d) ∩ H)))
    (hSd : 2⁻¹ * (w₁ * (2 * d) ^ (n + 1)) ≤ volume.real (ball z (2 * d) ∩ H))
    (hp : ‖p‖ ≤ ‖⨍ y in ball z (2 * d) ∩ H, g y‖)
    (hBz : ∫ y in ball z (2 * d) ∩ H, ‖g y - p‖ ^ 2 ≤
      C * V * (2 * d / (R / 2)) ^ ((n : ℝ) + 1 + 2 * γ))
    (hMz : ∫ y in ball z (2 * d) ∩ H, ‖g y‖ ^ 2 ≤ C * V * (2 * d / (R / 2)) ^ ((n : ℝ) + 1))
    (hI : ∀ W, c₁ * (d ^ (((n : ℝ) + 1) / 2 + γ) * (Q₀ + R ^ (α - γ) * Ka * ‖p‖)) ^ 2 ≤ W →
      ∫ y in ball x d, ‖g y - p‖ ^ 2 ≤ W → ∃ c : EuclideanSpace ℝ (Fin (n + 1)),
        ∫ y in ball x t, ‖g y - c‖ ^ 2 ≤ Ci * W * (t / d) ^ ((n : ℝ) + 1 + 2 * γ)) :
    ∃ c : EuclideanSpace ℝ (Fin (n + 1)), ∫ y in ball x t, ‖g y - c‖ ^ 2 ≤
      Ci * (C * 4 ^ ((n : ℝ) + 1 + 2 * γ) + 2 + 2 * c₁ * M ^ 2 * (2 ^ (n + 2) * C / w₁)) * V *
        (t / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  set e := (n : ℝ) + 1 + 2 * γ
  set K := C * 4 ^ e + 2 + 2 * c₁ * M ^ 2 * (2 ^ (n + 2) * C / w₁)
  have hV0 : 0 ≤ V := (mul_nonneg hc₁ (sq_nonneg _)).trans hV
  have hdR : 0 < d / R := div_pos hd hR
  have hPV : R ^ ((n : ℝ) + 1) * ‖p‖ ^ 2 ≤ 2 ^ (n + 2) * C / w₁ * V :=
    (rpow_mul_norm_sq_le hd hR hw₁ hSfin hgS hSd hMz hp).trans_eq (by ring)
  have hdata := mul_sq_rpow_mul_add_le hd hR hc₁ hKa hKaM hPV hV
  have h4 : (2 * d / (R / 2)) ^ e = 4 ^ e * (d / R) ^ e := by
    rw [show 2 * d / (R / 2) = 4 * (d / R) by field_simp; ring,
      Real.mul_rpow (by norm_num) hdR.le]
  have hΦ : ∫ y in ball x d, ‖g y - p‖ ^ 2 ≤ C * 4 ^ e * V * (d / R) ^ e := by
    refine (setIntegral_mono_set (hgS.integrableOn_norm_sub_sq_of_subset subset_rfl hSfin p)
      (ae_of_all _ fun _ => by positivity) hsub.eventuallySubset).trans (hBz.trans_eq ?_)
    rw [h4]
    ring
  have hde : 0 ≤ (d / R) ^ e := Real.rpow_nonneg hdR.le e
  have hc₁M : 0 ≤ 2 * c₁ * M ^ 2 * (2 ^ (n + 2) * C / w₁) := by positivity
  have hC4 : 0 ≤ C * 4 ^ e := by positivity
  obtain ⟨c, hc⟩ := hI (K * V * (d / R) ^ e)
    (hdata.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by
      simp only [K]; linarith) hV0) hde))
    (hΦ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by
      simp only [K]; linarith) hV0) hde))
  refine ⟨c, hc.trans_eq ?_⟩
  have hmul : (d / R) ^ e * (t / d) ^ e = (t / R) ^ e := by
    rw [← Real.mul_rpow hdR.le (div_nonneg ht hd.le)]
    congr 1
    field_simp
  rw [← hmul]
  ring

end Oscillation

section Constants

/-- The mean oscillation bound in scaled form: with `a = (n + 1) / 2 + γ`,
`√(K V (t / R)^{n+1+2γ} / (|B(0, t)| / 2)) = √(2 K / ω) (√V R^{-a}) t^γ`, where
`|B(0, t)| = t^{n+1} ω`. -/
private theorem sqrt_mul_rpow_div_eq {K V t R w₁ γ : ℝ} (hK : 0 ≤ K) (hV : 0 ≤ V) (ht : 0 < t)
    (hR : 0 < R) (hw₁ : 0 < w₁) :
    √(K * V * (t / R) ^ ((n : ℝ) + 1 + 2 * γ) / (2⁻¹ * (t ^ (n + 1) * w₁))) =
      √(2 * K / w₁) * (√V * R ^ (-(((n : ℝ) + 1) / 2 + γ))) * t ^ γ := by
  rw [← Real.sqrt_sq (by positivity : 0 ≤ √(2 * K / w₁) * (√V * R ^ (-(((n : ℝ) + 1) / 2 + γ))) *
    t ^ γ)]
  congr 1
  have h1 : (R ^ (-(((n : ℝ) + 1) / 2 + γ))) ^ 2 = (R ^ ((n : ℝ) + 1 + 2 * γ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_neg hR.le]
    congr 1
    push_cast
    ring
  have h2 : (t ^ γ) ^ 2 * t ^ (n + 1) = t ^ ((n : ℝ) + 1 + 2 * γ) := by
    rw [← Real.rpow_natCast (t ^ γ), ← Real.rpow_mul ht.le, ← Real.rpow_natCast t,
      ← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hV, h1,
    Real.div_rpow ht.le hR.le, ← h2]
  have : 0 < t ^ (n + 1) := by positivity
  have : 0 < R ^ ((n : ℝ) + 1 + 2 * γ) := Real.rpow_pos_of_pos hR _
  field_simp

/-- The average bound in scaled form: with `ρ = κ R` and `a = (n + 1) / 2 + γ`,
`√(Φ / (|B(0, ρ)| / 2)) ρ^{-γ} = √(2 / ω) κ^{-a} (R^{-a} √Φ)`, where `|B(0, ρ)| = ρ^{n+1} ω`. -/
private theorem sqrt_div_mul_rpow_neg_eq {Φ κ R w₁ γ : ℝ} (hΦ : 0 ≤ Φ) (hκ : 0 < κ) (hR : 0 < R)
    (hw₁ : 0 < w₁) :
    √(Φ / (2⁻¹ * ((κ * R) ^ (n + 1) * w₁))) * (κ * R) ^ (-γ) =
      √(2 / w₁) * κ ^ (-(((n : ℝ) + 1) / 2 + γ)) *
        (R ^ (-(((n : ℝ) + 1) / 2 + γ)) * √Φ) := by
  have hρ : 0 < κ * R := mul_pos hκ hR
  have hk : (κ * R) ^ (-γ) = √((κ * R) ^ (-(2 * γ))) := by
    rw [show -(2 * γ) = (-γ) * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast hρ.le,
      Real.sqrt_sq (Real.rpow_nonneg hρ.le _)]
  have hk' : κ ^ (-(((n : ℝ) + 1) / 2 + γ)) * R ^ (-(((n : ℝ) + 1) / 2 + γ)) =
      √((κ * R) ^ (-((n : ℝ) + 1 + 2 * γ))) := by
    rw [← Real.mul_rpow hκ.le hR.le, show -((n : ℝ) + 1 + 2 * γ) =
      (-(((n : ℝ) + 1) / 2 + γ)) * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast hρ.le,
      Real.sqrt_sq (Real.rpow_nonneg hρ.le _)]
  rw [hk, show √(2 / w₁) * κ ^ (-(((n : ℝ) + 1) / 2 + γ)) *
      (R ^ (-(((n : ℝ) + 1) / 2 + γ)) * √Φ) =
      √(2 / w₁) * (κ ^ (-(((n : ℝ) + 1) / 2 + γ)) * R ^ (-(((n : ℝ) + 1) / 2 + γ))) * √Φ by ring,
    hk', ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  have h1 : (κ * R) ^ (-((n : ℝ) + 1 + 2 * γ)) = ((κ * R) ^ (n + 1))⁻¹ * (κ * R) ^ (-(2 * γ)) := by
    rw [show -((n : ℝ) + 1 + 2 * γ) = -((n + 1 : ℕ) : ℝ) + -(2 * γ) by push_cast; ring,
      Real.rpow_add hρ, Real.rpow_neg hρ.le, Real.rpow_natCast]
  rw [h1]
  have : 0 < (κ * R) ^ (n + 1) := by positivity
  field_simp

/-- `√(Φ + c (R^a Q)²) R^{-a} ≤ (1 + √c) (Q + R^{-a} √Φ)` for `R > 0` and nonnegative `Φ`, `c`,
`Q`. -/
private theorem sqrt_add_mul_sq_mul_rpow_neg_le {Φ c R Q a : ℝ} (hΦ : 0 ≤ Φ) (hc : 0 ≤ c)
    (hR : 0 < R) (hQ : 0 ≤ Q) :
    √(Φ + c * (R ^ a * Q) ^ 2) * R ^ (-a) ≤ (1 + √c) * (Q + R ^ (-a) * √Φ) := by
  have hRa : 0 < R ^ a := Real.rpow_pos_of_pos hR a
  have hRna : R ^ (-a) * R ^ a = 1 := by rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  have hsq : √(Φ + c * (R ^ a * Q) ^ 2) ≤ √Φ + √c * (R ^ a * Q) := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hΦ
    have := Real.sq_sqrt hc
    nlinarith [Real.sqrt_nonneg Φ, Real.sqrt_nonneg c, mul_nonneg hRa.le hQ,
      mul_nonneg (Real.sqrt_nonneg Φ) (mul_nonneg (Real.sqrt_nonneg c) (mul_nonneg hRa.le hQ))]
  have hRn : 0 ≤ R ^ (-a) := Real.rpow_nonneg hR.le _
  calc √(Φ + c * (R ^ a * Q) ^ 2) * R ^ (-a) ≤ (√Φ + √c * (R ^ a * Q)) * R ^ (-a) :=
        mul_le_mul_of_nonneg_right hsq hRn
    _ = R ^ (-a) * √Φ + √c * Q * (R ^ (-a) * R ^ a) := by ring
    _ = R ^ (-a) * √Φ + √c * Q := by rw [hRna, mul_one]
    _ ≤ (1 + √c) * (Q + R ^ (-a) * √Φ) := by
        nlinarith [Real.sqrt_nonneg c, mul_nonneg hRn (Real.sqrt_nonneg Φ)]

end Constants

/-- **Oscillation at the points of a half-ball.** In the setting of the main theorem, there are
`K ≥ 0` and `κ ∈ (0, 1 / 4]`, depending only on `n`, `α`, `γ`, `q`, `λ`, `Λ` and `M`, such that for
every `x ∈ B(z₀, R / 4)` in the closed half-space and every `0 < t ≤ κ R` some set
`D ⊆ B(z₀, R)` containing `B(x, t) ∩ H` and some constant vector `p` have

`∫_D ‖∇u - p‖² ≤ K V (t / R)^{n+1+2γ}`,

where `V = ∫_{B(z₀, R) ∩ H} ‖∇u‖² + c₁ (R^{(n+1)/2+γ} Q₀)²` with
`Q₀ = K_G R^{α-γ} + R^{1-(n+1)/q-γ} ‖f‖_{L^q(B(z₀, R) ∩ H)}` and `c₁ = 1 + 4 ω^{1-2/q}`.

Let `d` be the distance from `x` to the boundary hyperplane and `z` the foot of the perpendicular.
If `t` is large compared with `d`, then `D` is a half-ball around `z`
(`exists_setIntegral_sub_sq_le_of_lt`). Otherwise `D = B(x, t)`: for `d` small compared with `R`
the interior decay applies to the excess over the normal vector `p_{2d}` of the boundary decay at
`z` (`exists_setIntegral_ball_sub_sq_le_of_near`), and for `d` comparable with `R` it applies on a
ball of radius comparable with `R` to the gradient itself. -/
private theorem exists_setIntegral_norm_gradient_sub_sq_le {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ)
    (hγα : γ ≤ α) (hγ1 : γ < 1) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hγq : γ ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ κ ≤ 1 / 4 ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν z₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ R : ℝ} {Ka KG : ℝ≥0},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z₀, ν⟫_ℝ = c₀ →
      UniformlyEllipticOn (ball z₀ R) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R) →
      HolderOnWith KG α G (ball z₀ R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball z₀ R ∩ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      ball z₀ R ⊆ U → 0 < R →
      ∀ x ∈ ball z₀ (R / 4), c₀ ≤ ⟪x, ν⟫_ℝ → ∀ t, 0 < t → t ≤ κ * R →
        ∃ (D : Set (EuclideanSpace ℝ (Fin (n + 1)))) (p : EuclideanSpace ℝ (Fin (n + 1))),
          ball x t ∩ H ⊆ D ∧ D ⊆ ball z₀ R ∧
          ∫ y in D, ‖W1p.gradient u y - p‖ ^ 2 ≤
            K * ((∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2) +
              (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^
                (1 - 2 / q.toReal)) * (R ^ (((n : ℝ) + 1) / 2 + γ) *
                  (KG * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
                    (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal)) ^ 2) *
              (t / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  obtain ⟨θ, C, hθ, hθ1, hC, hBd⟩ := exists_boundary_decay (n := n) hγ hγα hγ1 hq hγq
    (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨θ', Ci, hθ', hθ'1, hCi, hId⟩ := exists_interior_decay (n := n) hγ hγα hγ1 hq hγq
    (lam := lam) (Lam := Lam) (M := M)
  set e := (n : ℝ) + 1 + 2 * γ
  set w₁ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hw₁ : 0 < w₁ := measureReal_ball_pos volume _ one_pos
  set c₁ := 1 + 4 * w₁ ^ (1 - 2 / q.toReal)
  have hc₁ : 0 ≤ c₁ := by positivity
  set K₁ := C * (4 / θ') ^ e
  set K₂ := Ci * (C * 4 ^ e + 2 + 2 * c₁ * M ^ 2 * (2 ^ (n + 2) * C / w₁))
  set K₃ := Ci * (4 / θ) ^ e
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hK₃ : 0 ≤ K₃ := by positivity
  refine ⟨K₁ + K₂ + K₃, θ' * θ / 4, by positivity, by positivity, by nlinarith, ?_⟩
  intro U H u a G f ν z₀ c₀ R Ka KG hν hH hz₀ h haK hGK hM hf hvan hu hU hR x hx hxc t ht htκ
  set Kf := (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal
  set Q₀ := (KG : ℝ) * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf
  set Φ₀ := ∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2
  set V := Φ₀ + c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2
  have hΦ₀ : 0 ≤ Φ₀ := integral_nonneg fun _ => by positivity
  have hVc : c₁ * (R ^ (((n : ℝ) + 1) / 2 + γ) * Q₀) ^ 2 ≤ V := le_add_of_nonneg_left hΦ₀
  have hV0 : 0 ≤ V := by positivity
  have htR : 0 ≤ (t / R) ^ e := Real.rpow_nonneg (div_nonneg ht.le hR.le) e
  -- The foot `z` of the perpendicular from `x`, at the distance `d`.
  set z := x - ((⟪x, ν⟫_ℝ - c₀) / ‖ν‖ ^ 2) • ν
  set d := (⟪x, ν⟫_ℝ - c₀) / ‖ν‖
  have hzc : ⟪z, ν⟫_ℝ = c₀ := real_inner_sub_div_norm_sq_smul_self_eq hν x c₀
  have hxz : dist x z = d := by
    rw [dist_eq_norm, sub_sub_cancel, norm_div_norm_sq_smul_self, abs_of_nonneg (sub_nonneg.2 hxc)]
  have hballH : ball x d ⊆ H := fun y hy => (hH y).2 <| ball_subset_setOf_lt_inner hν
    (by rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hν), add_sub_cancel]) hy
  have hxz₀ : dist x z₀ < R / 4 := mem_ball.1 hx
  have hdx : d ≤ dist x z₀ := div_norm_le_dist_of_inner_eq hz₀
  have hzR : z ∈ ball z₀ (R / 2) := by
    rw [mem_ball]
    linarith [dist_triangle z x z₀, dist_comm x z]
  have hBz := hBd hν hH h haK hGK hM hf hvan hu hU hR z hzc hzR
  have hIx := hId h haK hGK hM hf hu hU
  have hθR : θ * (R / 2) ≤ R / 2 := mul_le_of_le_one_left (by positivity) hθ1
  have hκR : θ' * θ / 4 * R ≤ R / 4 := by
    have : θ' * θ ≤ 1 := by nlinarith
    nlinarith
  have htx : ball x t ⊆ ball z₀ R := ball_subset_ball' (by linarith)
  rcases lt_or_ge (θ' * d) t with hdt | htd
  · -- `B(x, t) ∩ H` lies in a half-ball around `z`.
    obtain ⟨hsub, hsθ, hint⟩ := exists_setIntegral_sub_sq_le_of_lt hθ' hθ'1 hR ht hxz hdt htκ
      fun s hs hsθ => (hBz s hs hsθ).1
    refine ⟨_, _, hsub, inter_subset_left.trans (ball_subset_ball' ?_), hint.trans ?_⟩
    · linarith [mem_ball.1 hzR]
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hV0) htR
  have hd : 0 < d := by
    by_contra hd
    nlinarith
  have hxd : ball x d ⊆ ball z₀ R ∩ H :=
    subset_inter (ball_subset_ball' (by linarith)) hballH
  rcases le_or_gt (2 * d) (θ * (R / 2)) with hnear | hfar
  · -- `x` is near the boundary: the interior decay of the excess over `p_{2d}`.
    obtain ⟨hB2, hM2⟩ := hBz (2 * d) (by positivity) hnear
    have hS : ball z (2 * d) ⊆ ball z₀ R := ball_subset_ball' (by linarith [mem_ball.1 hzR])
    have hsub : ball x d ⊆ ball z (2 * d) ∩ H := subset_inter (fun y hy => by
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y x z]) hballH
    have hSd : 2⁻¹ * (w₁ * (2 * d) ^ (n + 1)) ≤ volume.real (ball z (2 * d) ∩ H) := by
      have h := volume.mul_measureReal_ball_le_measureReal_ball_inter
        (volume.inv_two_mul_addHaar_closedBall_le_addHaar_closedBall_inter_setOf_lt_inner
          (r := 2 * d) hν hzc.ge)
      rw [Measure.addHaar_real_ball_of_pos volume z (by positivity), finrank_euclideanSpace_fin,
        NNReal.coe_inv, NNReal.coe_ofNat, show {y | c₀ < ⟪y, ν⟫_ℝ} = (H : Set _) from
          Set.ext fun y => (hH y).symm] at h
      exact (le_of_eq (by ring)).trans h
    obtain ⟨c, hc⟩ := exists_setIntegral_ball_sub_sq_le_of_near hd hR hw₁ ht.le hc₁
      Ka.coe_nonneg hM hC hVc hsub measure_ball_inter_ne_top
      ((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono
        (inter_subset_left.trans (hS.trans hU)) le_rfl)) hSd
      (norm_inner_div_norm_sq_smul_self_le _ _) hB2 hM2
      fun W hW hΦ => hIx x _ d W hxd hd (by linarith) hW hΦ t ht htd
    exact ⟨ball x t, c, inter_subset_left, htx,
      hc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hV0) htR)⟩
  · -- `x` is far from the boundary: the interior decay on a ball of radius `θ R / 4`.
    have hr : 0 < θ * R / 4 := by positivity
    have hrR : θ * R / 4 ≤ R := by linarith [mul_le_of_le_one_left hR.le hθ1]
    have hxr : ball x (θ * R / 4) ⊆ ball z₀ R ∩ H := (ball_subset_ball (by linarith)).trans hxd
    have hdata : c₁ * ((θ * R / 4) ^ (((n : ℝ) + 1) / 2 + γ) *
        (Q₀ + R ^ ((α : ℝ) - γ) * Ka * ‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖)) ^ 2 ≤ V := by
      rw [norm_zero, mul_zero, add_zero]
      refine le_trans ?_ hVc
      gcongr
    have hΦ : ∫ y in ball x (θ * R / 4), ‖W1p.gradient u y - 0‖ ^ 2 ≤ V := by
      simp only [sub_zero]
      refine (setIntegral_mono_set ?_ (ae_of_all _ fun _ => by positivity)
        hxr.eventuallySubset).trans (le_add_of_nonneg_right (by positivity))
      simpa only [sub_zero] using (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        (inter_subset_left.trans hU) measure_ball_inter_ne_top 0
    obtain ⟨c, hc⟩ := hIx x 0 (θ * R / 4) V hxr hr hrR hdata hΦ t ht
      (htκ.trans_eq (by ring))
    have hc' : ∫ y in ball x t, ‖W1p.gradient u y - c‖ ^ 2 ≤ K₃ * V * (t / R) ^ e := by
      refine hc.trans_eq ?_
      rw [show t / (θ * R / 4) = 4 / θ * (t / R) by field_simp,
        Real.mul_rpow (by positivity) (div_nonneg ht.le hR.le)]
      ring
    exact ⟨ball x t, c, inter_subset_left, htx,
      hc'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hV0) htR)⟩

/-- **The `C^{1,γ}` estimate up to a flat boundary for divergence-form equations.** Let `0 < γ < 1`
with `γ ≤ α`, let `2 ≤ q ≤ ∞` and `γ ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`. There is a
constant `C`, depending only on `n`, `α`, `γ`, `q`, `λ`, `Λ` and `M`, such that the following holds.
Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z₀` lie on its boundary hyperplane, and let
`u ∈ H¹(U)`, `B(z₀, R) ⊆ U`, vanish on `U ∖ H` and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on
`U ∩ H`, that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩ + ∫ f φ` for every test function `φ` on `U ∩ H`. Let `a`
be uniformly elliptic with constants `λ`, `Λ` on `B(z₀, R)`, let `a` and `G` be `α`-Hölder there
with constants `K_a` and `K_G`, the oscillation of `a` measured in the operator norm of the attached
bilinear forms, where `K_a R^α ≤ M`, and let `f ∈ L^q(B(z₀, R) ∩ H)`. Then the precise
representative of `∇u` for the Lebesgue measure on `H` is `γ`-Hölder on
`B(z₀, R / 4) ∩ closure H`, the part of the ball in the closed half-space, with constant

`C (K_G R^{α-γ} + R^{1-(n+1)/q-γ} ‖f‖_{L^q(B_R⁺)} + R^{-(n+1)/2-γ} ‖∇u‖_{L²(B_R⁺)})`,

where `B_R⁺ = B(z₀, R) ∩ H`.

Every term scales like `[∇u]_γ`, so the estimate is invariant under dilations. The coefficients
need no symmetry. At the points of `B(z₀, R) ∩ H` the precise representative is the limit of the
averages of `∇u` over small balls, which is `∇u` almost everywhere by Lebesgue's differentiation
theorem, so `∇u` extends `γ`-Hölder continuously up to the flat part of the boundary. The largest
admissible exponent is `γ = min α (1 - (n + 1) / q)` when this is less
than `1`, which needs `q > n + 1`. -/
theorem exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith
    {α γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ < 1) (hγα : γ ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hγq : (γ : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν z₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ R : ℝ} {Ka KG : ℝ≥0},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z₀, ν⟫_ℝ = c₀ →
      UniformlyEllipticOn (ball z₀ R) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z₀ R) →
      HolderOnWith KG α G (ball z₀ R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball z₀ R ∩ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      ball z₀ R ⊆ U → 0 < R →
      HolderOnWith (C * (KG * R ^ ((α : ℝ) - γ) +
          R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) *
            (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal +
          R ^ (-(((n : ℝ) + 1) / 2 + γ)) *
            √(∫ x in ball z₀ R ∩ H, ‖W1p.gradient u x‖ ^ 2))).toNNReal γ
        (preciseRepresentative (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball z₀ (R / 4) ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) := by
  have hγ' : (0 : ℝ) < γ := hγ
  obtain ⟨K, κ, hK, hκ, hκ4, hosc⟩ := exists_setIntegral_norm_gradient_sub_sq_le (n := n) hγ'
    (by exact_mod_cast hγα) (by exact_mod_cast hγ1) hq hγq (lam := lam) (Lam := Lam) (M := M)
  set w₁ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hw₁ : 0 < w₁ := measureReal_ball_pos volume _ one_pos
  set c₁ := 1 + 4 * w₁ ^ (1 - 2 / q.toReal)
  have hc₁ : 0 ≤ c₁ := by positivity
  set A := ((n : ℝ) + 1) / 2 + (γ : ℝ)
  set cc := 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
    ((((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) * (1 - 2 ^ (-(γ : ℝ))))
  have hcc : 0 ≤ cc := div_nonneg (by positivity) (mul_nonneg (by positivity)
    (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith))))
  refine ⟨2 * 2 ^ (γ : ℝ) * (cc * (√(2 * K / w₁) * (1 + √c₁)) + √(2 / w₁) * κ ^ (-A)),
    by positivity, ?_⟩
  intro U H u a G f ν z₀ c₀ R Ka KG hν hH hz₀ h haK hGK hM hf hvan hu hU hR
  set Kf := (eLpNorm f q (volume.restrict (ball z₀ R ∩ H))).toReal
  set Q₀ := (KG : ℝ) * R ^ ((α : ℝ) - γ) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - γ) * Kf
  set Φ₀ := ∫ y in ball z₀ R ∩ H, ‖W1p.gradient u y‖ ^ 2
  set V := Φ₀ + c₁ * (R ^ A * Q₀) ^ 2
  have hΦ₀ : 0 ≤ Φ₀ := integral_nonneg fun _ => by positivity
  have hQ₀ : 0 ≤ Q₀ := by positivity
  have hV : 0 ≤ V := by positivity
  set ρ := κ * R
  have hρ : 0 < ρ := mul_pos hκ hR
  have hρR : ρ ≤ R / 4 := by simp only [ρ]; nlinarith
  have hg := Lp.memLp (W1p.gradient u)
  -- The half-space has density at least one half around the points of the closed half-space.
  have hdens : ∀ x ∈ ball z₀ (R / 4) ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ∀ r, 0 < r → r ≤ ρ →
      (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall x r) ≤ volume (closedBall x r ∩ H) :=
    fun x hx r _ _ => by
      rw [show (H : Set _) = {y | c₀ < ⟪y, ν⟫_ℝ} from Set.ext hH]
      exact volume.inv_two_mul_addHaar_closedBall_le_addHaar_closedBall_inter_setOf_lt_inner hν hx.2
  have hsubU : ∀ x ∈ ball z₀ (R / 4) ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ∀ r ≤ ρ, ball x r ⊆ ball z₀ R :=
    fun x hx r hr => ball_subset_ball' (by linarith [mem_ball.1 hx.1])
  have hCamp := holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le
    (μ := volume) (Ω := (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (f := (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
    (M := √(2 * K / w₁) * (√V * R ^ (-A))) (B := √(Φ₀ / (2⁻¹ * (ρ ^ (n + 1) * w₁))))
    hγ (by norm_num) hρ hdens ?_ ?_ ?_
  rotate_left
  · -- Integrability on the balls.
    intro x hx
    have : IsFiniteMeasure (volume.restrict (ball x ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))
      := isFiniteMeasure_restrict.2 measure_ball_inter_ne_top
    rw [IntegrableOn, volume.restrict_restrict_closedBall_eq_restrict_ball_inter]
    exact (hg.mono_measure (Measure.restrict_mono (inter_subset_left.trans
      ((hsubU x hx ρ le_rfl).trans hU)) le_rfl)).integrable one_le_two
  · -- The mean oscillation bound.
    intro x hx r hr hrρ
    obtain ⟨D, p, hD, hDR, hint⟩ := hosc hν hH hz₀ h haK hGK hM hf hvan hu hU hR x hx.1 hx.2 r hr
      hrρ
    have hm := setAverage_closedBall_restrict_norm_sub_le_sqrt (μ := volume) (c := 2⁻¹)
      (by norm_num) hr (hdens x hx r hr hrρ) hD
      (hg.mono_measure (Measure.restrict_mono (inter_subset_left.trans
        ((hsubU x hx r hrρ).trans hU)) le_rfl))
      (hg.integrableOn_norm_sub_sq_of_subset (hDR.trans hU)
        (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hDR)) p)
    refine hm.trans ?_
    rw [← sqrt_mul_rpow_div_eq hK hV hr hR hw₁, Measure.addHaar_real_ball_of_pos volume x hr,
      finrank_euclideanSpace_fin, NNReal.coe_inv, NNReal.coe_ofNat]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hint (by positivity))
  · -- The bound on the averages at the scale `ρ`.
    intro x hx
    have h := norm_setAverage_closedBall_restrict_le_sqrt (by norm_num) hρ (hdens x hx ρ hρ le_rfl)
      (inter_subset_inter_left _ (hsubU x hx ρ le_rfl)) measure_ball_inter_ne_top
      (hg.mono_measure (Measure.restrict_mono (inter_subset_left.trans hU) le_rfl)) le_rfl
    rwa [Measure.addHaar_real_ball_of_pos volume x hρ, finrank_euclideanSpace_fin, NNReal.coe_inv,
      NNReal.coe_ofNat] at h
  refine hCamp.mono_const (Real.toNNReal_le_toNNReal ?_)
  -- The constant of Campanato's theorem is at most `C` times the scaled data.
  have hMo : √(2 * K / w₁) * (√V * R ^ (-A)) ≤
      √(2 * K / w₁) * ((1 + √c₁) * (Q₀ + R ^ (-A) * √Φ₀)) :=
    mul_le_mul_of_nonneg_left (sqrt_add_mul_sq_mul_rpow_neg_le hΦ₀ hc₁ hR hQ₀)
      (Real.sqrt_nonneg _)
  have hBρ : √(Φ₀ / (2⁻¹ * (ρ ^ (n + 1) * w₁))) * ρ ^ (-(γ : ℝ)) ≤
      √(2 / w₁) * κ ^ (-A) * (Q₀ + R ^ (-A) * √Φ₀) := by
    rw [sqrt_div_mul_rpow_neg_eq hΦ₀ hκ hR hw₁]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hQ₀) (by positivity)
  refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hMo hcc) hBρ)
    (by positivity)).trans_eq ?_
  ring

end PDE

end TauCeti
