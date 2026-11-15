/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Hadamard
public import TauCeti.Analysis.Complex.FiniteOrder

/-!
# Finite-order growth on vertical strips

An exponential-of-power bound on a fixed vertical strip is dominated, at large height, by
`exp (exp (c * |im z|))` for every `c > 0`. Thus finite order supplies the growth hypothesis
of Mathlib's `PhragmenLindelof.vertical_strip`, regardless of the width of the strip.

The strip maximum principle below requires growth only along the open strip, holomorphy
there and continuity on its closure. It applies in particular after normalizing boundary
estimates for convexity arguments. A three-lines corollary interpolates two constant edge
bounds geometrically, without assuming boundedness inside the strip in advance.

The analytic principles are Mathlib's `PhragmenLindelof.vertical_strip` and
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`; the new input is the
comparison of their growth hypotheses with finite order.
-/

public section

open Complex Set Filter Asymptotics Bornology
open scoped Topology

namespace TauCeti.PhragmenLindelof

/-- On a fixed vertical strip, an exponential of any real power of the norm is dominated
by a double exponential in height, with any positive inner exponential rate. -/
theorem isBigO_exp_rpow_exp_exp_vertical_strip (a b A B : ℝ) {c : ℝ} (hc : 0 < c) :
    (fun z : ℂ ↦ Real.exp (B * ‖z‖ ^ A))
      =O[comap (fun z : ℂ ↦ |z.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      (fun z ↦ Real.exp (Real.exp (c * |z.im|))) := by
  let p := max A 0
  let K := |a| + |b| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have htail := ((isLittleO_rpow_exp_pos_mul_atTop p hc).const_mul_left
    (|B| * K ^ p)).eventuallyLE
  have ht : Tendsto (fun z : ℂ ↦ |z.im|)
      (comap (fun z : ℂ ↦ |z.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) atTop :=
    tendsto_comap.mono_left inf_le_left
  refine IsBigO.of_norm_eventuallyLE ?_
  filter_upwards [ht.eventually htail, ht.eventually (eventually_ge_atTop 1),
    (eventually_mem_principal (re ⁻¹' Ioo a b)).filter_mono inf_le_right] with z hz ht hzab
  have hn : 1 ≤ ‖z‖ := ht.trans (abs_im_le_norm z)
  have hre : |z.re| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor <;> linarith [hzab.1, hzab.2, neg_abs_le a, le_abs_self b,
      abs_nonneg a, abs_nonneg b]
  have hnorm : ‖z‖ ≤ K * |z.im| := by
    have := norm_le_abs_re_add_abs_im z
    have := mul_le_mul_of_nonneg_left ht (add_nonneg (abs_nonneg a) (abs_nonneg b))
    dsimp [K]
    nlinarith
  have hexp : B * ‖z‖ ^ A ≤ Real.exp (c * |z.im|) := by
    calc
      B * ‖z‖ ^ A ≤ |B| * ‖z‖ ^ p :=
        mul_le_mul (le_abs_self B) (Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _))
          (Real.rpow_nonneg (norm_nonneg z) _) (abs_nonneg B)
      _ ≤ |B| * (K * |z.im|) ^ p := by gcongr
      _ = |B| * K ^ p * |z.im| ^ p := by rw [Real.mul_rpow hK.le (abs_nonneg _)]; ring
      _ ≤ Real.exp (c * |z.im|) := (le_abs_self _).trans (by simpa using hz)
  simpa only [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp] using hexp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a b C : ℝ} {z : ℂ}

/-- The strip maximum principle under finite-order growth on the strip itself.
No global holomorphy, global growth bound or boundedness on the strip is assumed. -/
theorem vertical_strip_of_isBigO_exp_rpow (hab : a < b)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ A B : ℝ, f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      (fun w ↦ Real.exp (B * ‖w‖ ^ A)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C)
    (hz : z.re ∈ Icc a b) : ‖f z‖ ≤ C := by
  obtain ⟨A, B, hg⟩ := hg
  let l := comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)
  have ht : Tendsto (fun w : ℂ ↦ |w.im|) l atTop := tendsto_comap.mono_left inf_le_left
  have hn : Tendsto (fun w : ℂ ↦ ‖w‖) l atTop :=
    tendsto_atTop_mono (fun w ↦ abs_im_le_norm w) ht
  have hl : l ≤ cobounded ℂ := by
    exact tendsto_id'.mp (tendsto_norm_atTop_iff_cobounded.mp hn)
  have hπ : 0 < Real.pi / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  let c := Real.pi / (b - a) / 2
  have hc : 0 < c := half_pos hπ
  have hc' : c < Real.pi / (b - a) := half_lt_self hπ
  exact _root_.PhragmenLindelof.vertical_strip hd
    ⟨c, hc', 1, by
      simpa only [one_mul, Function.comp_def] using
        (hg.mono (le_inf hl inf_le_right)).trans
          (isBigO_exp_rpow_exp_exp_vertical_strip a b A B hc)⟩ ha hb hz.1 hz.2

/-- Constant edge bounds interpolate geometrically for a function of finite order on a
strip. Unlike the bounded three-lines theorem, no interior bound is required as input. -/
theorem norm_le_interp_of_isBigO_exp_rpow {C₁ C₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ A B : ℝ, f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      (fun w ↦ Real.exp (B * ‖w‖ ^ A)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) := by
  have hbound : ∀ w : ℂ, w.re ∈ Icc a b → ‖f w‖ ≤ max C₁ C₂ :=
    fun w hw ↦ vertical_strip_of_isBigO_exp_rpow hab hd hg
      (fun v hv ↦ (ha v hv).trans (le_max_left _ _))
      (fun v hv ↦ (hb v hv).trans (le_max_right _ _)) hw
  exact Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab hz hd
    ⟨max C₁ C₂, by rintro _ ⟨w, hw, rfl⟩; exact hbound w hw⟩ ha hb

/-- Global finite order supplies the strip growth input automatically. The function need
only be holomorphic in the strip and continuous on its closure. -/
theorem vertical_strip_of_isFiniteOrder {f : ℂ → ℂ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) (hg : IsFiniteOrder f)
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C)
    (hz : z.re ∈ Icc a b) : ‖f z‖ ≤ C := by
  obtain ⟨A, hA⟩ := isFiniteOrder_def.mp hg
  apply vertical_strip_of_isBigO_exp_rpow hab hd ?_ ha hb hz
  refine ⟨A + 1, 1, ?_⟩
  simpa only [one_mul] using (hA.isBigO (by linarith : A < A + 1)).mono inf_le_left

end TauCeti.PhragmenLindelof
