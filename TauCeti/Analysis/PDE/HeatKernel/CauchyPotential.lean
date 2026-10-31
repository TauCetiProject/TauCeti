/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.PDE.HeatKernel.Derivatives
public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Basic
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# The Cauchy heat potential and its parabolic Hölder estimate

For a suitable initial datum `g`, for instance a bounded continuous one, the classical solution of
the heat equation `∂ₜu = Δu` on `E × [0, ∞)` with initial datum `g` is the *Cauchy potential*
`u(t, x) = (K_t ⋆ g)(x)`, where `K_t` is the heat kernel. This file does not prove that `u` solves
the heat equation; it proves the estimates below. Substituting `z = √t • y` in the convolution
integral writes it as

`u(t, x) = ∫ K_1(y) g(x - √t • y) dy`,

an average of translates of `g` against the fixed probability density `K_1`. This formula is the
definition `TauCeti.heatCauchyPotential` used here. It makes sense for every real `t`:
`TauCeti.heatCauchyPotential_eq_convolution` identifies it with `K_t ⋆ g` for `t > 0`, and when `F`
is complete `TauCeti.heatCauchyPotential_of_nonpos` gives `u(t, ·) = g` for `t ≤ 0`, because `K_1`
has mass one. If the translates of `g` are not integrable against `K_1`, the Bochner integral takes
the junk value `0`, so the potential is meaningful only under integrability assumptions, such as
the continuity and Hölder hypotheses of the estimates below
(`TauCeti.integrable_heatKernel_one_smul_sub_smul`).

In this form the Hölder estimates are immediate. If `g` is `α`-Hölder with constant `H`, then for
all `t, s` and `x, x'`

`‖g(x - √t • y) - g(x' - √s • y)‖ ≤ H (‖x - x'‖ + |√t - √s| ‖y‖)^α`,

and `|√t - √s| ≤ √|t - s|`. Integrating against `K_1` shows that `u` is `α`-Hölder with respect to
the parabolic distance `‖x - x'‖ + √|t - s|`, with constant `H (1 + M_α)`, where
`M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`. The constant depends only on `H`, `α` and
the dimension, and in particular not on the time. Separately, every time slice `u(t, ·)` is
`α`-Hölder with the constant `H` of the datum, and `u` is `α / 2`-Hölder in time with constant
`H M_α`; the latter bounds the rate `‖u(t, ·) - g‖ ≤ H M_α t^(α/2)` of attainment of the initial
datum.

These are the estimates behind the top-order seminorms of the Cauchy potential in the parabolic
space `C^{2+α,1+α/2}`, where they are applied to the second spatial derivatives and the Laplacian
of the datum.

## Main declarations

* `TauCeti.heatCauchyPotential`: the Cauchy potential `∫ K_1(y) g(x - √t • y) dy`.
* `TauCeti.heatCauchyPotential_of_nonpos`, `TauCeti.heatCauchyPotential_zero`: the initial datum.
* `TauCeti.heatCauchyPotential_eq_convolution`: agreement with `K_t ⋆ g` for `t > 0`.
* `TauCeti.norm_heatCauchyPotential_le`: the maximum principle `‖u‖ ≤ sup ‖g‖`.
* `TauCeti.holderWith_heatCauchyPotential`: the parabolic Hölder estimate.
* `HolderWith.heatCauchyPotential`: the spatial Hölder estimate of each time slice.
* `TauCeti.norm_heatCauchyPotential_sub_heatCauchyPotential_le`: the temporal Hölder estimate.
* `TauCeti.norm_heatCauchyPotential_sub_le`: the rate of attainment of the initial datum.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1 (the Cauchy problem
  for the heat equation).
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real ParabolicSpaceTime
open scoped Convolution NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Cauchy heat potential** of `g`, `u(t, x) = ∫ K_1(y) g(x - √t • y) dy`. For `t > 0` it is
the heat convolution `(K_t ⋆ g)(x)` (`TauCeti.heatCauchyPotential_eq_convolution`), which for
suitable data, such as bounded continuous ones, is the classical solution of the heat equation with
initial datum `g`; that is not proved here. When `F` is complete it is `g(x)` for `t ≤ 0`
(`TauCeti.heatCauchyPotential_of_nonpos`). If the translates of `g` are not integrable against
`K_1`, the integral takes the junk value `0`. -/
def heatCauchyPotential (g : E → F) (t : ℝ) (x : E) : F :=
  ∫ y, heatKernel 1 y • g (x - √t • y)

/-- The defining formula of the Cauchy heat potential. -/
theorem heatCauchyPotential_def (g : E → F) (t : ℝ) (x : E) :
    heatCauchyPotential g t x = ∫ y, heatKernel 1 y • g (x - √t • y) :=
  (rfl)

/-- **The initial datum.** For `t ≤ 0` the Cauchy heat potential of `g` is `g`. -/
theorem heatCauchyPotential_of_nonpos [CompleteSpace F] (g : E → F) {t : ℝ} (ht : t ≤ 0)
    (x : E) :
    heatCauchyPotential g t x = g x := by
  rw [heatCauchyPotential_def, sqrt_eq_zero'.2 ht]
  simp only [zero_smul, sub_zero]
  rw [integral_smul_const, integral_heatKernel one_pos, one_smul]

/-- **The initial datum.** At time zero the Cauchy heat potential of `g` is `g`. -/
@[simp]
theorem heatCauchyPotential_zero [CompleteSpace F] (g : E → F) : heatCauchyPotential g 0 = g :=
  funext <| heatCauchyPotential_of_nonpos g le_rfl

/-- For `t > 0` the Cauchy heat potential is the heat convolution `K_t ⋆ g`. -/
theorem heatCauchyPotential_eq_convolution (g : E → F) {t : ℝ} (ht : 0 < t) (x : E) :
    heatCauchyPotential g t x = (heatKernel t ⋆ g) x := by
  have hst : 0 < √t := sqrt_pos.2 ht
  -- Substitute `z = √t • y` in the convolution integral, using the parabolic scaling of `K_t`.
  have hsub := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E)
    (fun y => heatKernel 1 y • g (x - √t • y)) hst.le
  simp only [smul_inv_smul₀ hst.ne'] at hsub
  simp_rw [convolution_def, ContinuousLinearMap.lsmul_apply,
    heatKernel_eq_mul_heatKernel_one_smul ht, mul_smul]
  rw [integral_smul, hsub, smul_smul, ← mul_pow, inv_mul_cancel₀ hst.ne', one_pow, one_smul,
    heatCauchyPotential_def]

/-- **The maximum principle.** If `‖g‖ ≤ M` everywhere, then `‖u(t, x)‖ ≤ M` for the Cauchy heat
potential `u` of `g`, at every time `t` and point `x`. -/
theorem norm_heatCauchyPotential_le {g : E → F} {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) (t : ℝ) (x : E) :
    ‖heatCauchyPotential g t x‖ ≤ M := by
  -- `u(t, x)` is the heat convolution at time one and position zero of `z ↦ g (x + √t • z)`.
  have h := norm_heatKernel_convolution_le one_pos (g := fun z => g (x + √t • z))
    (ae_of_all _ fun z => hM _) 0
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, smul_neg,
    ← sub_eq_add_neg, ← heatCauchyPotential_def] using h

variable {g : E → F} {H α : ℝ≥0}

/-- A Hölder function grows at most like `‖y‖^α` along each line through `x`, so its translates
are integrable against `K_1`. -/
theorem integrable_heatKernel_one_smul_sub_smul (hg : HolderWith H α g) (hgc : Continuous g)
    (x : E) (c : ℝ) :
    Integrable fun y : E => heatKernel 1 y • g (x - c • y) := by
  have hK := integrable_heatKernel (E := E) one_pos
  have hw := integrable_norm_rpow_mul_heatKernel (E := E) one_pos α.coe_nonneg
  refine ((hK.mul_const ‖g x‖).add (hw.const_mul (H * |c| ^ (α : ℝ)))).mono'
    (((contDiff_heatKernel (k := 0) 1).continuous.smul
      (hgc.comp (by fun_prop))).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  have hgy : ‖g (x - c • y)‖ ≤ ‖g x‖ + H * |c| ^ (α : ℝ) * ‖y‖ ^ (α : ℝ) := by
    have h := hg.dist_le (x - c • y) x
    rw [dist_eq_norm (x - c • y) x, sub_sub_cancel_left, norm_neg, norm_smul, norm_eq_abs,
      mul_rpow (abs_nonneg c) (norm_nonneg y)] at h
    linarith [norm_sub_norm_le (g (x - c • y)) (g x), dist_eq_norm (g (x - c • y)) (g x)]
  rw [norm_smul, norm_of_nonneg (heatKernel_pos one_pos y).le]
  calc heatKernel 1 y * ‖g (x - c • y)‖
      ≤ heatKernel 1 y * (‖g x‖ + H * |c| ^ (α : ℝ) * ‖y‖ ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hgy (heatKernel_pos one_pos y).le
    _ = heatKernel 1 y * ‖g x‖ + H * |c| ^ (α : ℝ) * (‖y‖ ^ (α : ℝ) * heatKernel 1 y) := by ring

/-- The difference of two values of the Cauchy potential is bounded by integrating a pointwise
bound `A + B ‖y‖^α` on the difference of the integrands against `K_1`. -/
private theorem norm_heatCauchyPotential_sub_le_of_le (hg : HolderWith H α g)
    (hgc : Continuous g) {t s : ℝ} {x x' : E} {A B : ℝ}
    (hAB : ∀ y, ‖g (x - √t • y) - g (x' - √s • y)‖ ≤ A + B * ‖y‖ ^ (α : ℝ)) :
    ‖heatCauchyPotential g t x - heatCauchyPotential g s x'‖ ≤ A + B * heatKernelMoment E α := by
  have hK := integrable_heatKernel (E := E) one_pos
  have hw := integrable_norm_rpow_mul_heatKernel (E := E) one_pos α.coe_nonneg
  rw [heatCauchyPotential_def, heatCauchyPotential_def,
    ← integral_sub (integrable_heatKernel_one_smul_sub_smul hg hgc x _)
      (integrable_heatKernel_one_smul_sub_smul hg hgc x' _)]
  calc ‖∫ y, (heatKernel 1 y • g (x - √t • y) - heatKernel 1 y • g (x' - √s • y))‖
      ≤ ∫ y : E, (heatKernel 1 y * A + B * (‖y‖ ^ (α : ℝ) * heatKernel 1 y)) := by
        refine norm_integral_le_of_norm_le ((hK.mul_const A).add (hw.const_mul B))
          (ae_of_all _ fun y => ?_)
        rw [← smul_sub, norm_smul, norm_of_nonneg (heatKernel_pos one_pos y).le]
        calc heatKernel 1 y * ‖g (x - √t • y) - g (x' - √s • y)‖
            ≤ heatKernel 1 y * (A + B * ‖y‖ ^ (α : ℝ)) :=
              mul_le_mul_of_nonneg_left (hAB y) (heatKernel_pos one_pos y).le
          _ = heatKernel 1 y * A + B * (‖y‖ ^ (α : ℝ) * heatKernel 1 y) := by ring
    _ = A + B * heatKernelMoment E α := by
        rw [integral_add (hK.mul_const A) (hw.const_mul B), integral_mul_const,
          integral_heatKernel one_pos, one_mul, integral_const_mul,
          coe_heatKernelMoment]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] in
/-- The pointwise Hölder bound on the integrand of the Cauchy potential: the arguments of `g`
differ by `(x - x') - (√t - √s) • y`. -/
private theorem norm_sub_le_of_holderWith (hg : HolderWith H α g) (t s : ℝ) (x x' y : E) :
    ‖g (x - √t • y) - g (x' - √s • y)‖ ≤ H * ‖(x - x') - (√t - √s) • y‖ ^ (α : ℝ) := by
  have h := hg.dist_le (x - √t • y) (x' - √s • y)
  have hxy : (x - x') - (√t - √s) • y = (x - √t • y) - (x' - √s • y) := by
    rw [sub_smul]
    abel
  rwa [dist_eq_norm, dist_eq_norm, ← hxy] at h

/-- **The parabolic Hölder estimate of the Cauchy heat potential.** If `g` is continuous and
`α`-Hölder with constant `H`, its Cauchy potential is `α`-Hölder on parabolic space-time, whose
distance is `‖x - x'‖ + √|t - s|`, with constant `H (1 + M_α)`. Here
`M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`, which depends only on `α` and the
dimension. Continuity is automatic when `α > 0` (`HolderWith.continuous`). -/
theorem holderWith_heatCauchyPotential (hg : HolderWith H α g) (hgc : Continuous g) :
    HolderWith (H * (1 + heatKernelMoment E α)) α
      fun p : ParabolicSpaceTime E => heatCauchyPotential g p.time p.space := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun p _ q _ => ?_
  set d := dist p.space q.space + √|p.time - q.time| with hd_def
  have hd : 0 ≤ d := by positivity
  rw [dist_eq_norm, dist_eq p q, ← hd_def]
  -- The arguments of `g` differ by at most `d * max 1 ‖y‖`, and `max 1 ‖y‖ ^ α ≤ 1 + ‖y‖ ^ α`.
  have hAB : ∀ y, ‖g (p.space - √p.time • y) - g (q.space - √q.time • y)‖ ≤
      H * d ^ (α : ℝ) + H * d ^ (α : ℝ) * ‖y‖ ^ (α : ℝ) := fun y => by
    refine (norm_sub_le_of_holderWith hg _ _ _ _ y).trans ?_
    have hy : ‖(p.space - q.space) - (√p.time - √q.time) • y‖ ≤ d * max 1 ‖y‖ := by
      calc ‖(p.space - q.space) - (√p.time - √q.time) • y‖
          ≤ ‖p.space - q.space‖ + |√p.time - √q.time| * ‖y‖ := by
            rw [← norm_eq_abs, ← norm_smul]
            exact norm_sub_le _ _
        _ ≤ dist p.space q.space * max 1 ‖y‖ + √|p.time - q.time| * max 1 ‖y‖ := by
            rw [← dist_eq_norm]
            gcongr
            · exact le_mul_of_one_le_right dist_nonneg (le_max_left _ _)
            · exact abs_sqrt_sub_sqrt_le _ _
            · exact le_max_right _ _
        _ = d * max 1 ‖y‖ := by rw [hd_def, add_mul]
    have hmax : max 1 ‖y‖ ^ (α : ℝ) ≤ 1 + ‖y‖ ^ (α : ℝ) := by
      rcases le_total 1 ‖y‖ with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h, one_rpow]
        linarith [rpow_nonneg (norm_nonneg y) (α : ℝ)]
    calc (H : ℝ) * ‖(p.space - q.space) - (√p.time - √q.time) • y‖ ^ (α : ℝ)
        ≤ H * (d * max 1 ‖y‖) ^ (α : ℝ) := by gcongr
      _ = H * d ^ (α : ℝ) * max 1 ‖y‖ ^ (α : ℝ) := by
          rw [mul_rpow hd (by positivity), mul_assoc]
      _ ≤ H * d ^ (α : ℝ) * (1 + ‖y‖ ^ (α : ℝ)) := by gcongr
      _ = H * d ^ (α : ℝ) + H * d ^ (α : ℝ) * ‖y‖ ^ (α : ℝ) := by ring
  refine (norm_heatCauchyPotential_sub_le_of_le hg hgc hAB).trans_eq ?_
  push_cast
  ring

/-- **The spatial Hölder estimate of the Cauchy heat potential.** If `g` is continuous and
`α`-Hölder with constant `H`, then so is every time slice of its Cauchy potential, with the same
constant. -/
theorem _root_.HolderWith.heatCauchyPotential (hg : HolderWith H α g) (hgc : Continuous g)
    (t : ℝ) : HolderWith H α (heatCauchyPotential g t) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ x' _ => ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine (norm_heatCauchyPotential_sub_le_of_le (B := 0) hg hgc fun y => ?_).trans_eq
    (by rw [zero_mul, add_zero])
  simpa using norm_sub_le_of_holderWith hg t t x x' y

/-- **The temporal Hölder estimate of the Cauchy heat potential.** If `g` is continuous and
`α`-Hölder with constant `H`, its Cauchy potential `u` satisfies
`‖u(t, x) - u(s, x)‖ ≤ H M_α |t - s|^(α/2)`, where `M_α = ∫ ‖y‖^α K_1(y) dy` is
`TauCeti.heatKernelMoment`. -/
theorem norm_heatCauchyPotential_sub_heatCauchyPotential_le (hg : HolderWith H α g)
    (hgc : Continuous g) (t s : ℝ) (x : E) :
    ‖heatCauchyPotential g t x - heatCauchyPotential g s x‖ ≤
      H * heatKernelMoment E α * |t - s| ^ ((α : ℝ) / 2) := by
  rw [rpow_div_two_eq_sqrt _ (abs_nonneg _)]
  refine (norm_heatCauchyPotential_sub_le_of_le (A := 0)
    (B := H * √|t - s| ^ (α : ℝ)) hg hgc fun y => ?_).trans_eq (by ring)
  refine (norm_sub_le_of_holderWith hg t s x x y).trans ?_
  rw [sub_self, zero_sub, norm_neg, norm_smul, norm_eq_abs, mul_rpow (abs_nonneg _) (norm_nonneg y),
    zero_add, ← mul_assoc]
  gcongr
  exact abs_sqrt_sub_sqrt_le t s

/-- **Attainment of the initial datum at a rate.** If `g` is continuous and `α`-Hölder with
constant `H`, its Cauchy potential `u` satisfies `‖u(t, x) - g(x)‖ ≤ H M_α t^(α/2)` for `t ≥ 0`,
where `M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`. -/
theorem norm_heatCauchyPotential_sub_le [CompleteSpace F] (hg : HolderWith H α g)
    (hgc : Continuous g) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖heatCauchyPotential g t x - g x‖ ≤ H * heatKernelMoment E α * t ^ ((α : ℝ) / 2) := by
  simpa [abs_of_nonneg ht] using norm_heatCauchyPotential_sub_heatCauchyPotential_le hg hgc t 0 x

end TauCeti
