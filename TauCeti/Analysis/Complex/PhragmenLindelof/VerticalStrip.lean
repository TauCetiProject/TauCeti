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
# Growth and boundary bounds on vertical strips

An exponential-of-power bound on a fixed vertical strip is dominated, at large height, by
`exp (exp (c * |im z|))` for every `c > 0`. Thus finite order supplies the growth hypothesis
of Mathlib's `PhragmenLindelof.vertical_strip`, regardless of the width of the strip. Positive
real dilations `u ↦ d * u` likewise transfer Mathlib's sharp growth condition `c < π / (b - a)`
from `(a, b)` to `(a / d, b / d)`. On any vertical line `Re w = σ` along which `t ↦ f (σ + t * I)`
is continuous, an asymptotic `O(|t| ^ p)` bound along `cocompact ℝ` upgrades to a global bound in
`(d + |Im w|) ^ p` for every `d > 0`.

The strip maximum principle below requires growth only along the open strip, holomorphy
there and continuity on its closure. It applies in particular after normalizing boundary
estimates for convexity arguments. A three-lines corollary interpolates two constant edge
bounds geometrically, without assuming boundedness inside the strip in advance.

The analytic principles are Mathlib's `PhragmenLindelof.vertical_strip` and
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`; the new inputs are the
rescaling and finite-order comparisons for their growth hypotheses and the upgrade from asymptotic
to global vertical-line bounds.
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

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Positive real dilation `u ↦ d * u` transfers Mathlib's sharp Phragmén–Lindelöf vertical-strip
growth condition from `(a, b)` to `(a / d, b / d)`. -/
theorem exists_isBigO_comp_ofReal_mul_exp_exp {f : ℂ → E} {a b d : ℝ} (hd_pos : 0 < d)
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|))) :
    ∃ c' < Real.pi / (b / d - a / d), ∃ B',
      (fun u ↦ f ((d : ℂ) * u))
        =O[comap (fun u : ℂ ↦ |u.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (a / d) (b / d))]
        fun u ↦ Real.exp (B' * Real.exp (c' * |u.im|)) := by
  obtain ⟨c, hc, B, hO⟩ := hg
  have hmaps : MapsTo (fun u : ℂ ↦ (d : ℂ) * u)
      (re ⁻¹' Ioo (a / d) (b / d)) (re ⁻¹' Ioo a b) := fun u hu ↦ by
    simpa only [mem_preimage, mem_Ioo, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      lt_div_iff₀' hd_pos, div_lt_iff₀' hd_pos] using hu
  have htend : Tendsto (fun u : ℂ ↦ (d : ℂ) * u)
      (comap (fun u : ℂ ↦ |u.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (a / d) (b / d)))
      (comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) := by
    refine (tendsto_comap_iff.mpr ?_).inf hmaps.tendsto
    have him : (fun w : ℂ ↦ |w.im|) ∘ (fun u : ℂ ↦ (d : ℂ) * u) = fun u : ℂ ↦ d * |u.im| := by
      ext u; simp [abs_of_pos hd_pos]
    rw [him]
    exact tendsto_comap.const_mul_atTop' hd_pos
  have hc_d : c * d < Real.pi / (b / d - a / d) := by
    calc
      c * d < (Real.pi / (b - a)) * d := mul_lt_mul_of_pos_right hc hd_pos
      _ = Real.pi / (b / d - a / d) := by
        rw [← sub_div, div_div_eq_mul_div, mul_div_right_comm]
  refine ⟨c * d, hc_d, B, (hO.comp_tendsto htend).congr' EventuallyEq.rfl ?_⟩
  exact Eventually.of_forall fun u ↦ by simp [abs_of_pos hd_pos, mul_assoc]

/-- On a vertical line `Re w = σ` along which `t ↦ f (σ + t * I)` is continuous, an asymptotic
`O(|t| ^ p)` bound along `cocompact ℝ` upgrades to a global bound in `(d + |Im w|) ^ p` for every
`d > 0`. -/
theorem exists_norm_le_mul_rpow_of_isBigO_cocompact {f : ℂ → E} {σ d p : ℝ} (hd_pos : 0 < d)
    (hcont : Continuous fun t : ℝ ↦ f (σ + t * I))
    (hO : (fun t : ℝ ↦ f (σ + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p) :
    ∃ C : ℝ, ∀ w : ℂ, w.re = σ → ‖f w‖ ≤ C * (d + |w.im|) ^ p := by
  let q : ℝ → ℝ := fun t ↦ ‖f (σ + t * I)‖ / (d + |t|) ^ p
  have hcont_q : Continuous q := by
    refine hcont.norm.div ?_ fun t ↦
      (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg hd_pos (abs_nonneg t)) p).ne'
    exact (continuous_const.add continuous_abs).rpow_const fun t ↦
      Or.inl (add_pos_of_pos_of_nonneg hd_pos (abs_nonneg t)).ne'
  have hdom : (fun t : ℝ ↦ |t| ^ p) =O[cocompact ℝ] fun t : ℝ ↦ (d + |t|) ^ p :=
    ((IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      ((tendsto_norm_cocompact_atTop (E := ℝ)).congr fun _ ↦ by simp)).rpow
      fun t ↦ abs_nonneg t).isBigO_symm
  have hqO : q =O[cocompact ℝ] (1 : ℝ → ℝ) :=
    (div_isBoundedUnder_of_isBigO (hO.norm_left.trans hdom)).isBigO_const one_ne_zero
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (hcont_q.isBounded_range_iff_isBigO.mpr hqO)
  refine ⟨C, fun w hw ↦ ?_⟩
  have hw_eq : (σ : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [hw]
  have hle : q w.im ≤ C :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC _ (mem_range_self w.im))
  simpa only [q, hw_eq] using (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) p)).mp hle

end Seminormed

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
