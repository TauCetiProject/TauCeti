/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.VerticalStrip.Basic
import TauCeti.Analysis.Convex.Midpoint

/-!
# The Phragmén–Lindelöf principle with products of powers on the edges

Let `f` be holomorphic on the open vertical strip `a < re s < b`, continuous on its closure and of
growth at most `exp (B exp (c |im s|))` with `c < π / (b - a)`. Suppose that on the two boundary
lines `f` is bounded by products of real powers of functions `G i` that are holomorphic on the open
strip and continuous and nowhere zero on the closed strip,

`‖f (a + it)‖ ≤ ∏ i, ‖G i (a + it)‖ ^ α i`   and   `‖f (b + it)‖ ≤ ∏ i, ‖G i (b + it)‖ ^ β i`.

If `σ ↦ ‖G i (σ + it)‖` is increasing on `[a, b]` whenever `α i > β i` and decreasing whenever
`α i < β i`, then the exponents interpolate linearly across the strip:

`‖f (σ + it)‖ ≤ ∏ i, ‖G i (σ + it)‖ ^ ((α i (b - σ) + β i (σ - a)) / (b - a))`   for `a ≤ σ ≤ b`.

This is the explicit form of the convexity principle used for pointwise bounds of the Riemann zeta
function and of `L`-functions inside the critical strip: the factors `G i` are typically positive
constants (such as a power of the conductor), linear functions `Q + s`, or holomorphic versions of
`log t`, and the conclusion carries no implicit constant. Unlike the version with polynomial edge
bounds (`TauCeti.PhragmenLindelof.exists_norm_le_interp_mul_one_add_abs_im_rpow`), nothing is lost
in passing from the edges to the interior. The factors `G i` must grow at most like
`exp (B exp (c |im s|))` in the reciprocal sense when one of their exponents is positive, and in the
direct sense when one is negative.

The monotonicity hypothesis cannot be dropped when the exponents differ: on `[0, 1]` the constant
`f = 1` satisfies both edge bounds for the single factor `G s = exp (-s)` with `α = 1`, `β = 0`, but
at `σ = 1 / 2` the interpolated bound is `exp (-1 / 4) < 1`.

The proof first treats the midpoint `σ = (a + b) / 2`. There the function
`F (s) = f s * conj (f (a + b - conj s))` is holomorphic, has the same modulus
`‖f (a + it)‖ ‖f (b + it)‖` on both boundary lines and equals `‖f‖ ^ 2` on the middle line.
Choose holomorphic logarithms `L i` of the `G i` on the closed strip and divide `F` by the
exponential of the weighted sum `∑ i ((α i + β i) / 2) (L i s + conj (L i (a + b - conj s)))`,
whose modulus is `∏ i (‖G i s‖ ‖G i (a + b - conj s)‖) ^ ((α i + β i) / 2)`. The monotonicity
hypothesis makes the modulus of the quotient at most `1` on both boundary lines, and Mathlib's
`PhragmenLindelof.vertical_strip` bounds it by `1` inside. Applied to substrips, the midpoint case
shows that the set of `σ ∈ [a, b]` for which the bound holds contains the midpoint of any two of
its points; it is closed by continuity in `σ`, so it is all of `[a, b]`.

## Main results

* `TauCeti.PhragmenLindelof.norm_le_prod_rpow_interp`: the interpolation bound above.

## References

* A. Fiori, *A Note on the Phragmen-Lindelof Theorem*, 2025, arXiv:2502.13282, Theorem 1 with
  Remark 2 (negative exponents) and Lemma 5. Its proof (the midpoint case for the symmetrised
  function, then bisection) is followed here; the reflection symmetry `G i (conj s) = conj (G i s)`
  assumed there is not needed.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., §5.65.
-/

public section

open Complex Filter Set
open scoped Real ComplexConjugate
open TauCeti.Complex.HadamardThreeLines (closure_verticalStrip)

namespace TauCeti.PhragmenLindelof

variable {ι : Type*} {a b : ℝ}

/-! ### Growth along the strip -/

/-- `u` is at most `exp (B exp (c |im z|))` on the open strip `a < re z < b`, with `B ≥ 0` and an
exponent `0 ≤ c < π / (b - a)` below the Phragmén–Lindelöf threshold. -/
private def StripGrowth (a b : ℝ) (u : ℂ → ℝ) : Prop :=
  ∃ c B : ℝ, 0 ≤ c ∧ c < π / (b - a) ∧ 0 ≤ B ∧
    ∀ z ∈ re ⁻¹' Ioo a b, u z ≤ Real.exp (B * Real.exp (c * |z.im|))

/-- An admissible exponent `0 ≤ c < π / (b - a)` exists only for a nondegenerate strip. -/
private theorem StripGrowth.lt {u : ℂ → ℝ} (h : StripGrowth a b u) : a < b := by
  obtain ⟨c, -, hc, hcπ, -⟩ := h
  exact sub_pos.1 ((div_pos_iff_of_pos_left Real.pi_pos).1 (hc.trans_lt hcπ))

private theorem StripGrowth.of_le {u v : ℂ → ℝ} (h : StripGrowth a b u)
    (hvu : ∀ z ∈ re ⁻¹' Ioo a b, v z ≤ u z) : StripGrowth a b v := by
  obtain ⟨c, B, hc, hcπ, hB, hu⟩ := h
  exact ⟨c, B, hc, hcπ, hB, fun z hz ↦ (hvu z hz).trans (hu z hz)⟩

private theorem stripGrowth_of_le_mul_exp (hab : a < b) {u : ℂ → ℝ} {c B C : ℝ}
    (hc : c < π / (b - a))
    (hu : ∀ z ∈ re ⁻¹' Ioo a b, u z ≤ C * Real.exp (B * Real.exp (c * |z.im|))) :
    StripGrowth a b u := by
  refine ⟨max c 0, |C| + |B|, le_max_right _ _,
    max_lt hc (div_pos Real.pi_pos (sub_pos.2 hab)), by positivity, fun z hz ↦ ?_⟩
  have hE : Real.exp (c * |z.im|) ≤ Real.exp (max c 0 * |z.im|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hE₁ : 1 ≤ Real.exp (max c 0 * |z.im|) :=
    Real.one_le_exp (mul_nonneg (le_max_right _ _) (abs_nonneg _))
  have hX : B * Real.exp (c * |z.im|) ≤ |B| * Real.exp (max c 0 * |z.im|) :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left hE (abs_nonneg B))
  have hC : C ≤ Real.exp |C| := (le_abs_self C).trans ((le_add_of_nonneg_right zero_le_one).trans
    (Real.add_one_le_exp _))
  calc u z ≤ C * Real.exp (B * Real.exp (c * |z.im|)) := hu z hz
    _ ≤ Real.exp |C| * Real.exp (|B| * Real.exp (max c 0 * |z.im|)) := by gcongr
    _ ≤ Real.exp ((|C| + |B|) * Real.exp (max c 0 * |z.im|)) := by
      rw [← Real.exp_add, add_mul]
      gcongr
      exact le_mul_of_one_le_right (abs_nonneg C) hE₁

private theorem stripGrowth_one (hab : a < b) : StripGrowth a b fun _ ↦ 1 :=
  ⟨0, 0, le_rfl, div_pos Real.pi_pos (sub_pos.2 hab), le_rfl, fun _ _ ↦ by simp⟩

private theorem StripGrowth.mul {u v : ℂ → ℝ} (hu : StripGrowth a b u) (hv : StripGrowth a b v)
    (hv₀ : ∀ z, 0 ≤ v z) : StripGrowth a b fun z ↦ u z * v z := by
  obtain ⟨c₁, B₁, hc₁, hcπ₁, hB₁, hu⟩ := hu
  obtain ⟨c₂, B₂, -, hcπ₂, hB₂, hv⟩ := hv
  refine ⟨max c₁ c₂, B₁ + B₂, le_max_of_le_left hc₁, max_lt hcπ₁ hcπ₂, by positivity,
    fun z hz ↦ ?_⟩
  calc u z * v z
      ≤ Real.exp (B₁ * Real.exp (c₁ * |z.im|)) * Real.exp (B₂ * Real.exp (c₂ * |z.im|)) :=
        mul_le_mul (hu z hz) (hv z hz) (hv₀ z) (Real.exp_pos _).le
    _ ≤ Real.exp ((B₁ + B₂) * Real.exp (max c₁ c₂ * |z.im|)) := by
      rw [← Real.exp_add, add_mul]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

private theorem StripGrowth.prod (hab : a < b) {s : Finset ι} {u : ι → ℂ → ℝ}
    (hu : ∀ i ∈ s, StripGrowth a b (u i)) (hu₀ : ∀ i ∈ s, ∀ z, 0 ≤ u i z) :
    StripGrowth a b fun z ↦ ∏ i ∈ s, u i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stripGrowth_one hab
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    refine (hu j (s.mem_insert_self j)).mul
      (ih (fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hu₀ i (Finset.mem_insert_of_mem hi))) fun z ↦ ?_
    exact Finset.prod_nonneg fun i hi ↦ hu₀ i (Finset.mem_insert_of_mem hi) z

private theorem StripGrowth.rpow {u : ℂ → ℝ} (hu : StripGrowth a b u) (hu₀ : ∀ z, 0 ≤ u z)
    {γ : ℝ} (hγ : 0 ≤ γ) : StripGrowth a b fun z ↦ u z ^ γ := by
  obtain ⟨c, B, hc, hcπ, hB, hu⟩ := hu
  refine ⟨c, γ * B, hc, hcπ, by positivity, fun z hz ↦ ?_⟩
  calc u z ^ γ ≤ Real.exp (B * Real.exp (c * |z.im|)) ^ γ :=
        Real.rpow_le_rpow (hu₀ z) (hu z hz) hγ
    _ = Real.exp (γ * B * Real.exp (c * |z.im|)) := by rw [← Real.exp_mul]; ring_nf

/-- The reflection `z ↦ a + b - conj z` in the middle line `re z = (a + b) / 2` of the strip. -/
private def reflect (a b : ℝ) (z : ℂ) : ℂ := ((a + b : ℝ) : ℂ) - conj z

private theorem reflect_re (z : ℂ) : (reflect a b z).re = a + b - z.re := by simp [reflect]

private theorem reflect_im (z : ℂ) : (reflect a b z).im = z.im := by simp [reflect]

private theorem reflect_reflect (z : ℂ) : reflect a b (reflect a b z) = z := by simp [reflect]

private theorem reflect_ofReal_add_mul_I (σ t : ℝ) :
    reflect a b (σ + t * I) = ((a + b - σ : ℝ) : ℂ) + t * I := by
  apply Complex.ext <;> simp [reflect_re, reflect_im]

private theorem reflect_mem_Ioo {z : ℂ} (hz : z ∈ re ⁻¹' Ioo a b) :
    reflect a b z ∈ re ⁻¹' Ioo a b := by
  simp only [mem_preimage, reflect_re, mem_Ioo] at hz ⊢
  constructor <;> linarith [hz.1, hz.2]

private theorem reflect_mem_Icc {z : ℂ} (hz : z ∈ re ⁻¹' Icc a b) :
    reflect a b z ∈ re ⁻¹' Icc a b := by
  simp only [mem_preimage, reflect_re, mem_Icc] at hz ⊢
  constructor <;> linarith [hz.1, hz.2]

private theorem continuous_reflect : Continuous (reflect a b) :=
  continuous_const.sub continuous_conj

private theorem StripGrowth.comp_reflect {u : ℂ → ℝ} (hu : StripGrowth a b u) :
    StripGrowth a b fun z ↦ u (reflect a b z) := by
  obtain ⟨c, B, hc, hcπ, hB, hu⟩ := hu
  refine ⟨c, B, hc, hcπ, hB, fun z hz ↦ ?_⟩
  simpa [reflect_im] using hu _ (reflect_mem_Ioo hz)

private theorem StripGrowth.mono {u v : ℝ} {g : ℂ → ℝ} (hg : StripGrowth a b g) (hau : a ≤ u)
    (huv : u < v) (hvb : v ≤ b) : StripGrowth u v g := by
  obtain ⟨c, B, hc, hcπ, hB, hg⟩ := hg
  refine ⟨c, B, hc, hcπ.trans_le ?_, hB, fun z hz ↦ hg z ⟨hau.trans_lt hz.1, hz.2.trans_le hvb⟩⟩
  exact div_le_div_of_nonneg_left Real.pi_pos.le (sub_pos.2 huv) (by linarith)

private theorem StripGrowth.isBigO {g : ℂ → ℂ} (hg : StripGrowth a b fun z ↦ ‖g z‖) :
    ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨c, B, -, hcπ, -, hg⟩ := hg
  refine ⟨c, hcπ, B, Asymptotics.IsBigO.of_bound 1 ?_⟩
  refine eventually_inf_principal.2 (Eventually.of_forall fun z hz ↦ ?_)
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hg z hz

/-- The power `‖g z‖ ^ (-γ)` grows admissibly when `‖g z‖⁻¹` does, if `γ > 0`, and when `‖g z‖`
does, if `γ < 0`. -/
private theorem stripGrowth_norm_rpow_neg (hab : a < b) {g : ℂ → ℂ} {γ : ℝ}
    (hlow : 0 < γ → StripGrowth a b fun z ↦ ‖g z‖⁻¹)
    (hup : γ < 0 → StripGrowth a b fun z ↦ ‖g z‖) :
    StripGrowth a b fun z ↦ ‖g z‖ ^ (-γ) := by
  rcases lt_trichotomy γ 0 with hγ | rfl | hγ
  · exact (hup hγ).rpow (fun _ ↦ norm_nonneg _) (by linarith)
  · simpa using stripGrowth_one hab
  · refine ((hlow hγ).rpow (fun _ ↦ inv_nonneg.2 (norm_nonneg _)) hγ.le).of_le fun z _ ↦ ?_
    rw [Real.rpow_neg (norm_nonneg _), Real.inv_rpow (norm_nonneg _)]

/-! ### Holomorphic ingredients -/

/-- Mathlib's growth hypothesis of `PhragmenLindelof.vertical_strip`, asymptotic as `|im z| → ∞`,
gives a bound on the whole strip for a function continuous on the closed strip. -/
private theorem stripGrowth_of_isBigO (hab : a < b) {g : ℂ → ℂ}
    (hg : ContinuousOn g (re ⁻¹' Icc a b))
    (hB : ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|))) :
    StripGrowth a b fun z ↦ ‖g z‖ := by
  obtain ⟨c, hc, B, hO⟩ := hB
  obtain ⟨C, hC⟩ := hO.bound
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC
  obtain ⟨T, hT⟩ := hC
  -- Below the height `T` the function is bounded, by compactness.
  obtain ⟨K, hK⟩ := (isCompact_Icc.reProdIm (isCompact_Icc (a := -T) (b := T)))
    |>.exists_bound_of_continuousOn (hg.mono fun z hz ↦ (mem_reProdIm.1 hz).1)
  refine stripGrowth_of_le_mul_exp (B := |B|) (C := |K| + |C|) hab hc fun z hz ↦ ?_
  have hE : 1 ≤ Real.exp (|B| * Real.exp (c * |z.im|)) := Real.one_le_exp (by positivity)
  rcases le_or_gt T |z.im| with hzT | hzT
  · calc ‖g z‖ ≤ C * ‖Real.exp (B * Real.exp (c * |z.im|))‖ := hT _ hzT z rfl hz
      _ ≤ |C| * Real.exp (|B| * Real.exp (c * |z.im|)) := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        gcongr
        · exact le_abs_self C
        · exact le_abs_self B
      _ ≤ (|K| + |C|) * Real.exp (|B| * Real.exp (c * |z.im|)) := by gcongr; simp
  · have hzK : z ∈ Icc a b ×ℂ Icc (-T) T :=
      mem_reProdIm.2 ⟨Ioo_subset_Icc_self hz, abs_le.1 hzT.le⟩
    calc ‖g z‖ ≤ K := hK z hzK
      _ ≤ |K| + |C| := (le_abs_self K).trans (le_add_of_nonneg_right (abs_nonneg C))
      _ ≤ (|K| + |C|) * Real.exp (|B| * Real.exp (c * |z.im|)) :=
        le_mul_of_one_le_right (by positivity) hE

/-- A function holomorphic on the open strip, continuous and nowhere zero on the closed strip, has
a logarithm with the same regularity. -/
private theorem exists_log_strip {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b))
    (hg₀ : ∀ z ∈ re ⁻¹' Icc a b, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DiffContOnCl ℂ L (re ⁻¹' Ioo a b) ∧ ∀ z ∈ re ⁻¹' Icc a b, exp (L z) = g z := by
  rcases le_or_gt b a with hba | hab
  · -- The open strip is empty, so a pointwise logarithm will do.
    refine ⟨fun z ↦ log (g z), ?_, fun z hz ↦ exp_log (hg₀ z hz)⟩
    rw [Ioo_eq_empty hba.not_gt, preimage_empty]
    exact ⟨differentiableOn_empty, by rw [closure_empty]; exact continuousOn_empty _⟩
  have hint : interior (re ⁻¹' Icc a b) = re ⁻¹' Ioo a b := by
    rw [interior_preimage_re, interior_Icc]
  have hconv : Convex ℝ (re ⁻¹' Icc a b) := (convex_Icc a b).linear_preimage reLm
  obtain ⟨L, hLc, hLd, hL⟩ := hconv.exists_continuousOn_differentiableOn_eqOn_exp_comp
    (hg.continuousOn_verticalClosedStrip hab) (hint ▸ hg.differentiableOn)
    (by rintro ⟨z, hz, hz₀⟩; exact hg₀ z hz hz₀)
  exact ⟨L, ⟨hint ▸ hLd, (closure_verticalStrip hab).symm ▸ hLc⟩, fun z hz ↦ hL hz⟩

/-- `z ↦ conj (g (a + b - conj z))` is holomorphic on the strip when `g` is. -/
private theorem diffContOnCl_conj_comp_reflect {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b)) :
    DiffContOnCl ℂ (fun z ↦ conj (g (reflect a b z))) (re ⁻¹' Ioo a b) := by
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have h₁ : DifferentiableAt ℂ g (((a + b : ℝ) : ℂ) - conj z) :=
      hg.differentiableAt (isOpen_Ioo.preimage continuous_re) (reflect_mem_Ioo hz)
    have hd : DifferentiableAt ℂ (fun w ↦ g (((a + b : ℝ) : ℂ) - w)) (conj z) :=
      h₁.comp (conj z) ((differentiableAt_const _).sub differentiableAt_id)
    have hd' := hd.conj_conj
    rw [conj_conj] at hd'
    exact hd'.differentiableWithinAt
  · exact continuous_conj.comp_continuousOn (hg.continuousOn.comp continuous_reflect.continuousOn
      (MapsTo.closure (fun _ ↦ reflect_mem_Ioo) continuous_reflect))

/-! ### The midpoint case -/

/-- The scalar heart of the boundary estimate: with `‖x‖ ^ p ≤ ‖y‖ ^ p` for `p = (α - β) / 2`, the
edge bounds `‖x‖ ^ α` and `‖y‖ ^ β` divided by the interpolating weight `(‖x‖ ‖y‖) ^ ((α + β) / 2)`
give at most `1`. -/
private theorem rpow_mul_rpow_mul_rpow_neg_le_one {x y : ℂ} {α β : ℝ}
    (h : ‖x‖ ^ ((α - β) / 2) ≤ ‖y‖ ^ ((α - β) / 2)) :
    ‖x‖ ^ α * ‖y‖ ^ β * (‖x‖ ^ (-((α + β) / 2)) * ‖y‖ ^ (-((α + β) / 2))) ≤ 1 := by
  -- If `x = 0` or `y = 0`, a factor `0 ^ e` with `e ≠ 0` vanishes unless `α = β = 0`.
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne α 0 with rfl | hα
    · rcases eq_or_ne β 0 with rfl | hβ
      · simp
      · simp [Real.zero_rpow (neg_ne_zero.2 (div_ne_zero hβ two_ne_zero))]
    · simp [Real.zero_rpow hα]
  rcases eq_or_ne y 0 with rfl | hy
  · rcases eq_or_ne β 0 with rfl | hβ
    · rcases eq_or_ne α 0 with rfl | hα
      · simp
      · simp [Real.zero_rpow (neg_ne_zero.2 (div_ne_zero hα two_ne_zero))]
    · simp [Real.zero_rpow hβ]
  have hx' := norm_pos_iff.2 hx
  have hy' := norm_pos_iff.2 hy
  have e₁ : ‖x‖ ^ α * ‖x‖ ^ (-((α + β) / 2)) = ‖x‖ ^ ((α - β) / 2) := by
    rw [← Real.rpow_add hx']; ring_nf
  have e₂ : ‖y‖ ^ β * ‖y‖ ^ (-((α + β) / 2)) = (‖y‖ ^ ((α - β) / 2))⁻¹ := by
    rw [← Real.rpow_add hy', ← Real.rpow_neg hy'.le]; ring_nf
  calc ‖x‖ ^ α * ‖y‖ ^ β * (‖x‖ ^ (-((α + β) / 2)) * ‖y‖ ^ (-((α + β) / 2)))
      = ‖x‖ ^ ((α - β) / 2) * (‖y‖ ^ ((α - β) / 2))⁻¹ := by rw [← e₁, ← e₂]; ring
    _ ≤ ‖y‖ ^ ((α - β) / 2) * (‖y‖ ^ ((α - β) / 2))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hy' _).ne'

/-- The holomorphic weight `∑ i, γ i (L i z + conj (L i (a + b - conj z)))` whose exponential has
modulus `∏ i, (‖G i z‖ ‖G i (a + b - conj z)‖) ^ γ i` when `L i` is a logarithm of `G i`. -/
private def weight (s : Finset ι) (a b : ℝ) (γ : ι → ℝ) (L : ι → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, (γ i : ℂ) * (L i z + conj (L i (reflect a b z)))

private theorem norm_exp_neg_weight {s : Finset ι} {γ : ι → ℝ} {G L : ι → ℂ → ℂ}
    (hLG : ∀ i ∈ s, ∀ z ∈ re ⁻¹' Icc a b, exp (L i z) = G i z) {z : ℂ}
    (hz : z ∈ re ⁻¹' Icc a b) :
    ‖exp (-weight s a b γ L z)‖ =
      ∏ i ∈ s, ‖G i z‖ ^ (-γ i) * ‖G i (reflect a b z)‖ ^ (-γ i) := by
  rw [weight, ← Finset.sum_neg_distrib, exp_sum, norm_prod]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [← hLG i hi z hz, ← hLG i hi _ (reflect_mem_Icc hz)]
  simp only [norm_exp, ← Real.exp_mul, ← Real.exp_add]
  simp
  ring

private theorem diffContOnCl_weight {s : Finset ι} {γ : ι → ℝ} {L : ι → ℂ → ℂ}
    (hL : ∀ i ∈ s, DiffContOnCl ℂ (L i) (re ⁻¹' Ioo a b)) :
    DiffContOnCl ℂ (weight s a b γ L) (re ⁻¹' Ioo a b) := by
  have hi : ∀ i ∈ s, DiffContOnCl ℂ
      (fun z ↦ (γ i : ℂ) * (L i z + conj (L i (reflect a b z)))) (re ⁻¹' Ioo a b) :=
    fun i hi ↦ ((hL i hi).add (diffContOnCl_conj_comp_reflect (hL i hi))).const_smul (γ i : ℂ)
  exact ⟨DifferentiableOn.fun_sum fun i h ↦ (hi i h).differentiableOn,
    continuousOn_finsetSum _ fun i h ↦ (hi i h).continuousOn⟩

/-- The boundary estimate of the midpoint case: the product of the edge values of `f` divided by
the interpolating weight is at most `1`. -/
private theorem norm_mul_norm_mul_prod_rpow_neg_le_one {s : Finset ι} {f : ℂ → ℂ}
    {G : ι → ℂ → ℂ} {α β : ι → ℝ}
    (hcmp : ∀ i ∈ s, ∀ t : ℝ,
      ‖G i (a + t * I)‖ ^ ((α i - β i) / 2) ≤ ‖G i (b + t * I)‖ ^ ((α i - β i) / 2))
    (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ ∏ i ∈ s, ‖G i (a + t * I)‖ ^ α i)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ ∏ i ∈ s, ‖G i (b + t * I)‖ ^ β i) (t : ℝ) :
    ‖f (a + t * I)‖ * ‖f (b + t * I)‖ * ∏ i ∈ s, ‖G i (a + t * I)‖ ^ (-((α i + β i) / 2)) *
      ‖G i (b + t * I)‖ ^ (-((α i + β i) / 2)) ≤ 1 := by
  calc _ ≤ (∏ i ∈ s, ‖G i (a + t * I)‖ ^ α i) * (∏ i ∈ s, ‖G i (b + t * I)‖ ^ β i) *
        ∏ i ∈ s, ‖G i (a + t * I)‖ ^ (-((α i + β i) / 2)) *
          ‖G i (b + t * I)‖ ^ (-((α i + β i) / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ ↦ by positivity)
        exact mul_le_mul (ha t) (hb t) (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ by positivity)
    _ = ∏ i ∈ s, ‖G i (a + t * I)‖ ^ α i * ‖G i (b + t * I)‖ ^ β i *
        (‖G i (a + t * I)‖ ^ (-((α i + β i) / 2)) * ‖G i (b + t * I)‖ ^ (-((α i + β i) / 2))) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ ≤ 1 := Finset.prod_le_one₀ (fun i _ ↦ by positivity) fun i hi ↦
        rpow_mul_rpow_mul_rpow_neg_le_one (hcmp i hi t)

/-- From `x ^ 2 ∏ (y i ^ γ i) ^ (-2) ≤ 1` to `x ≤ ∏ y i ^ γ i`, for `y i > 0`. -/
private theorem le_prod_rpow_of_mul_self_mul_prod_le_one {s : Finset ι} {x : ℝ} {y γ : ι → ℝ}
    (hy : ∀ i ∈ s, 0 < y i)
    (h : x * x * ∏ i ∈ s, y i ^ (-γ i) * y i ^ (-γ i) ≤ 1) : x ≤ ∏ i ∈ s, y i ^ γ i := by
  have hM : 0 < ∏ i ∈ s, y i ^ γ i := Finset.prod_pos fun i hi ↦ Real.rpow_pos_of_pos (hy i hi) _
  have hprod : ∏ i ∈ s, y i ^ (-γ i) * y i ^ (-γ i) =
      (∏ i ∈ s, y i ^ γ i)⁻¹ * (∏ i ∈ s, y i ^ γ i)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i hi ↦ by rw [Real.rpow_neg (hy i hi).le]
  rw [hprod, ← mul_inv, mul_inv_le_iff₀ (by positivity), one_mul] at h
  nlinarith

/-- **The midpoint case.** Under the hypotheses of the main theorem, with the monotonicity replaced
by the comparison of the two edges that it implies, the bound holds on the middle line with the
average exponents `(α i + β i) / 2`. -/
private theorem norm_le_prod_rpow_midpoint {s : Finset ι} {f : ℂ → ℂ}
    {G L : ι → ℂ → ℂ} {α β : ι → ℝ}
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) (hfB : StripGrowth a b fun z ↦ ‖f z‖)
    (hL : ∀ i ∈ s, DiffContOnCl ℂ (L i) (re ⁻¹' Ioo a b))
    (hLG : ∀ i ∈ s, ∀ z ∈ re ⁻¹' Icc a b, exp (L i z) = G i z)
    (hGB : ∀ i ∈ s, StripGrowth a b fun z ↦ ‖G i z‖ ^ (-((α i + β i) / 2)))
    (hcmp : ∀ i ∈ s, ∀ t : ℝ,
      ‖G i (a + t * I)‖ ^ ((α i - β i) / 2) ≤ ‖G i (b + t * I)‖ ^ ((α i - β i) / 2))
    (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ ∏ i ∈ s, ‖G i (a + t * I)‖ ^ α i)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ ∏ i ∈ s, ‖G i (b + t * I)‖ ^ β i) (t : ℝ) :
    ‖f (((a + b) / 2 : ℝ) + t * I)‖ ≤
      ∏ i ∈ s, ‖G i (((a + b) / 2 : ℝ) + t * I)‖ ^ ((α i + β i) / 2) := by
  have hab := hfB.lt
  set γ : ι → ℝ := fun i ↦ (α i + β i) / 2
  -- `Q z = f z * conj (f (a + b - conj z)) * exp (-weight z)` is holomorphic on the strip.
  set Q : ℂ → ℂ := fun z ↦ f z * conj (f (reflect a b z)) * exp (-weight s a b γ L z)
  have hQd : DiffContOnCl ℂ Q (re ⁻¹' Ioo a b) := by
    have hw := diffContOnCl_weight (γ := γ) hL
    have hF := diffContOnCl_conj_comp_reflect hf
    exact ⟨(hf.differentiableOn.mul hF.differentiableOn).mul hw.differentiableOn.neg.cexp,
      (hf.continuousOn.mul hF.continuousOn).mul hw.continuousOn.neg.cexp⟩
  have hnorm : ∀ z ∈ re ⁻¹' Icc a b, ‖Q z‖ = ‖f z‖ * ‖f (reflect a b z)‖ *
      ∏ i ∈ s, ‖G i z‖ ^ (-γ i) * ‖G i (reflect a b z)‖ ^ (-γ i) := fun z hz ↦ by
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_exp_neg_weight hLG hz]
  -- Its growth is admissible.
  have hQB : StripGrowth a b fun z ↦ ‖Q z‖ := by
    refine (((hfB.mul hfB.comp_reflect fun _ ↦ norm_nonneg _).mul
      (StripGrowth.prod hab (fun i hi ↦ (hGB i hi).mul (hGB i hi).comp_reflect
        fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) fun i _ z ↦ by positivity)
      fun z ↦ by positivity)).of_le fun z hz ↦ (hnorm z (Ioo_subset_Icc_self hz)).le
  -- `‖Q‖` is symmetric under the reflection, and at most `1` on the line `re z = a` by the edge
  -- bounds and the comparison of the edges; so it is at most `1` on both boundary lines.
  have hmem : ∀ σ ∈ Icc a b, ∀ t : ℝ, (σ : ℂ) + t * I ∈ re ⁻¹' Icc a b := fun σ hσ t ↦ by
    simpa using hσ
  have hsymm : ∀ z ∈ re ⁻¹' Icc a b, ‖Q (reflect a b z)‖ = ‖Q z‖ := fun z hz ↦ by
    rw [hnorm _ (reflect_mem_Icc hz), hnorm z hz, reflect_reflect, mul_comm ‖f (reflect a b z)‖]
    exact congrArg _ (Finset.prod_congr rfl fun i _ ↦ mul_comm _ _)
  have hedge_a : ∀ t : ℝ, ‖Q (a + t * I)‖ ≤ 1 := fun t ↦ by
    rw [hnorm _ (hmem a (left_mem_Icc.2 hab.le) t), reflect_ofReal_add_mul_I, add_sub_cancel_left]
    exact norm_mul_norm_mul_prod_rpow_neg_le_one hcmp ha hb t
  have hedge : ∀ z : ℂ, z.re = a ∨ z.re = b → ‖Q z‖ ≤ 1 := by
    rintro z (h | h) <;> rw [← re_add_im z, h]
    · exact hedge_a z.im
    · rw [← hsymm _ (hmem b (right_mem_Icc.2 hab.le) _), reflect_ofReal_add_mul_I,
        add_sub_cancel_right]
      exact hedge_a z.im
  -- The Phragmén–Lindelöf principle bounds `Q` on the middle line, where it is `‖f‖ ^ 2` divided
  -- by the square of the interpolating product.
  have hz₀ := hmem ((a + b) / 2) ⟨by linarith, by linarith⟩ t
  have hRz₀ : reflect a b (((a + b) / 2 : ℝ) + t * I) = ((a + b) / 2 : ℝ) + t * I := by
    rw [reflect_ofReal_add_mul_I]
    congr 3
    ring
  have hQz₀ : ‖Q (((a + b) / 2 : ℝ) + t * I)‖ ≤ 1 := PhragmenLindelof.vertical_strip hQd
    hQB.isBigO (fun z hz ↦ hedge z (Or.inl hz)) (fun z hz ↦ hedge z (Or.inr hz)) hz₀.1 hz₀.2
  rw [hnorm _ hz₀, hRz₀] at hQz₀
  exact le_prod_rpow_of_mul_self_mul_prod_le_one
    (fun i hi ↦ by rw [← hLG i hi _ hz₀]; exact norm_pos_iff.2 (exp_ne_zero _)) hQz₀

/-! ### The interpolation bound -/

/-- The interpolated exponent `(α (b - σ) + β (σ - a)) / (b - a)`. -/
private theorem interp_mid (α β u v : ℝ) :
    (α * (b - (u + v) / 2) + β * ((u + v) / 2 - a)) / (b - a) =
      ((α * (b - u) + β * (u - a)) / (b - a) + (α * (b - v) + β * (v - a)) / (b - a)) / 2 := by
  ring

/-- One bisection step: the bound on two lines `re z = u` and `re z = v` of the strip gives it on
the line `re z = (u + v) / 2`, by the midpoint case on the strip `u ≤ re z ≤ v`. -/
private theorem norm_le_prod_rpow_interp_midpoint {s : Finset ι} {f : ℂ → ℂ} {G L : ι → ℂ → ℂ}
    {α β : ι → ℝ} (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b)) (hfB : StripGrowth a b fun z ↦ ‖f z‖)
    (hL : ∀ i ∈ s, DiffContOnCl ℂ (L i) (re ⁻¹' Ioo a b))
    (hLG : ∀ i ∈ s, ∀ z ∈ re ⁻¹' Icc a b, exp (L i z) = G i z)
    (hGlow : ∀ i ∈ s, 0 < α i ∨ 0 < β i → StripGrowth a b fun z ↦ ‖G i z‖⁻¹)
    (hGup : ∀ i ∈ s, α i < 0 ∨ β i < 0 → StripGrowth a b fun z ↦ ‖G i z‖)
    (hmono : ∀ i ∈ s, β i < α i → ∀ t : ℝ, MonotoneOn (fun σ : ℝ ↦ ‖G i (σ + t * I)‖) (Icc a b))
    (hanti : ∀ i ∈ s, α i < β i → ∀ t : ℝ, AntitoneOn (fun σ : ℝ ↦ ‖G i (σ + t * I)‖) (Icc a b))
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hu : ∀ t : ℝ, ‖f (u + t * I)‖ ≤
      ∏ i ∈ s, ‖G i (u + t * I)‖ ^ ((α i * (b - u) + β i * (u - a)) / (b - a)))
    (hv : ∀ t : ℝ, ‖f (v + t * I)‖ ≤
      ∏ i ∈ s, ‖G i (v + t * I)‖ ^ ((α i * (b - v) + β i * (v - a)) / (b - a))) (t : ℝ) :
    ‖f (((u + v) / 2 : ℝ) + t * I)‖ ≤ ∏ i ∈ s, ‖G i (((u + v) / 2 : ℝ) + t * I)‖ ^
      ((α i * (b - (u + v) / 2) + β i * ((u + v) / 2 - a)) / (b - a)) := by
  have hab := hfB.lt
  set e : ι → ℝ → ℝ := fun i σ ↦ (α i * (b - σ) + β i * (σ - a)) / (b - a)
  have hba : 0 < b - a := sub_pos.2 hab
  have hsub : re ⁻¹' Ioo u v ⊆ re ⁻¹' Ioo a b := preimage_mono (Ioo_subset_Ioo hau hvb)
  have hsubc : re ⁻¹' Icc u v ⊆ re ⁻¹' Icc a b := preimage_mono (Icc_subset_Icc hau hvb)
  have hmem : ∀ σ ∈ Icc u v, ∀ t : ℝ, (σ : ℂ) + t * I ∈ re ⁻¹' Icc a b := fun σ hσ t ↦ by
    simpa using Icc_subset_Icc hau hvb hσ
  simp only [interp_mid]
  refine norm_le_prod_rpow_midpoint (α := fun i ↦ e i u) (β := fun i ↦ e i v)
    (hf.mono hsub) (hfB.mono hau huv hvb) (fun i hi ↦ (hL i hi).mono hsub)
    (fun i hi z hz ↦ hLG i hi z (hsubc hz)) (fun i hi ↦ ?_) (fun i hi t ↦ ?_) hu hv t
  · -- The growth of the weight: its exponent is positive only if `α i` or `β i` is.
    refine (stripGrowth_norm_rpow_neg hab (fun h ↦ hGlow i hi ?_) (fun h ↦ hGup i hi ?_)).mono
      hau huv hvb
    · by_contra! h'
      have : e i u + e i v ≤ 0 := by
        simp only [e, ← add_div]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hba.le
      linarith
    · by_contra! h'
      have : 0 ≤ e i u + e i v := by
        simp only [e, ← add_div]
        exact div_nonneg (by nlinarith) hba.le
      linarith
  · -- The comparison of the two edges, from the monotonicity of `‖G i‖` in `σ`.
    have hd : (e i u - e i v) / 2 = (α i - β i) * ((v - u) / (2 * (b - a))) := by
      simp only [e]; field_simp; ring
    have hpos : 0 < (v - u) / (2 * (b - a)) := by positivity
    have hv₀ : 0 < ‖G i (v + t * I)‖ := by
      rw [← hLG i hi _ (hmem v ⟨huv.le, le_rfl⟩ t)]; exact norm_pos_iff.2 (exp_ne_zero _)
    rw [hd]
    rcases lt_trichotomy (β i) (α i) with h | h | h
    · exact Real.rpow_le_rpow (norm_nonneg _) (hmono i hi h t ⟨hau, huv.le.trans hvb⟩
        ⟨hau.trans huv.le, hvb⟩ huv.le) (mul_nonneg (by linarith) hpos.le)
    · simp [h]
    · exact Real.rpow_le_rpow_of_nonpos hv₀ (hanti i hi h t ⟨hau, huv.le.trans hvb⟩
        ⟨hau.trans huv.le, hvb⟩ huv.le) (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le)

/-- The lines `re z = σ`, `σ ∈ [a, b]`, on which the interpolation bound holds form a closed set,
by continuity in `σ`. -/
private theorem isClosed_setOf_norm_le_prod_rpow {s : Finset ι} {f : ℂ → ℂ}
    {G : ι → ℂ → ℂ} {α β : ι → ℝ} (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hG : ∀ i ∈ s, DiffContOnCl ℂ (G i) (re ⁻¹' Ioo a b))
    (hG₀ : ∀ i ∈ s, ∀ z ∈ re ⁻¹' Icc a b, G i z ≠ 0) :
    IsClosed {σ | σ ∈ Icc a b ∧ ∀ t : ℝ, ‖f (σ + t * I)‖ ≤
      ∏ i ∈ s, ‖G i (σ + t * I)‖ ^ ((α i * (b - σ) + β i * (σ - a)) / (b - a))} := by
  rcases le_or_gt b a with hba | hab
  · -- A subset of the degenerate interval `[a, b]` has at most one point.
    refine Subsingleton.isClosed ((subsingleton_Icc_of_ge hba).anti ?_)
    exact fun _ hσ ↦ hσ.1
  have hcont : ∀ t : ℝ, ContinuousOn (fun σ : ℝ ↦ (σ : ℂ) + t * I) (Icc a b) := fun t ↦ by
    fun_prop
  have hmaps : ∀ t : ℝ, MapsTo (fun σ : ℝ ↦ (σ : ℂ) + t * I) (Icc a b) (re ⁻¹' Icc a b) :=
    fun t σ hσ ↦ by simpa using hσ
  have : {σ | σ ∈ Icc a b ∧ ∀ t : ℝ, ‖f (σ + t * I)‖ ≤
      ∏ i ∈ s, ‖G i (σ + t * I)‖ ^ ((α i * (b - σ) + β i * (σ - a)) / (b - a))} =
      ⋂ t : ℝ, {σ ∈ Icc a b | ‖f (σ + t * I)‖ ≤
        ∏ i ∈ s, ‖G i (σ + t * I)‖ ^ ((α i * (b - σ) + β i * (σ - a)) / (b - a))} := by
    ext σ
    simp only [mem_ofPred_eq, mem_iInter, forall_and, forall_const]
  rw [this]
  refine isClosed_iInter fun t ↦ isClosed_Icc.isClosed_le
    (((hf.continuousOn_verticalClosedStrip hab).comp (hcont t) (hmaps t)).norm)
    (continuousOn_finsetProd _ fun i hi ↦ ContinuousOn.rpow
      (((hG i hi).continuousOn_verticalClosedStrip hab).comp (hcont t) (hmaps t)).norm
      (by fun_prop) fun σ hσ ↦ Or.inl (norm_ne_zero_iff.2 (hG₀ i hi _ (hmaps t hσ))))

/-- **The Phragmén–Lindelöf principle with products of powers on the edges** (Fiori). Let `f` be
holomorphic on the open strip `a < re s < b`, continuous on its closure, with
`f s = O(exp (B exp (c |im s|)))` as `|im s| → ∞` in the strip, for some `c < π / (b - a)`. Let
`G i`, `i ∈ s`, be holomorphic on the open strip, continuous and nowhere zero on its closure, with
`(G i s)⁻¹ = O(exp (B' exp (c' |im s|)))` (`c' < π / (b - a)`) if `α i > 0` or `β i > 0`, and
`G i s = O(exp (B' exp (c' |im s|)))` if `α i < 0` or `β i < 0`. Suppose that
`σ ↦ ‖G i (σ + it)‖` is monotone on `[a, b]` when `β i < α i` and antitone when `α i < β i`. If
`‖f (a + it)‖ ≤ ∏ i ∈ s, ‖G i (a + it)‖ ^ α i` and `‖f (b + it)‖ ≤ ∏ i ∈ s, ‖G i (b + it)‖ ^ β i`
for all real `t`, then for `a ≤ re z ≤ b`,
`‖f z‖ ≤ ∏ i ∈ s, ‖G i z‖ ^ ((α i (b - re z) + β i (re z - a)) / (b - a))`. -/
theorem norm_le_prod_rpow_interp {s : Finset ι} (hab : a < b) {f : ℂ → ℂ} {G : ι → ℂ → ℂ}
    {α β : ι → ℝ} (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hfB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hG : ∀ i ∈ s, DiffContOnCl ℂ (G i) (re ⁻¹' Ioo a b))
    (hG₀ : ∀ i ∈ s, ∀ z ∈ re ⁻¹' Icc a b, G i z ≠ 0)
    (hGlow : ∀ i ∈ s, 0 < α i ∨ 0 < β i → ∃ c < π / (b - a), ∃ B,
      (fun z ↦ (G i z)⁻¹) =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hGup : ∀ i ∈ s, α i < 0 ∨ β i < 0 → ∃ c < π / (b - a), ∃ B,
      G i =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)))
    (hmono : ∀ i ∈ s, β i < α i → ∀ t : ℝ, MonotoneOn (fun σ : ℝ ↦ ‖G i (σ + t * I)‖) (Icc a b))
    (hanti : ∀ i ∈ s, α i < β i → ∀ t : ℝ, AntitoneOn (fun σ : ℝ ↦ ‖G i (σ + t * I)‖) (Icc a b))
    (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ ∏ i ∈ s, ‖G i (a + t * I)‖ ^ α i)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ ∏ i ∈ s, ‖G i (b + t * I)‖ ^ β i)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖f z‖ ≤ ∏ i ∈ s, ‖G i z‖ ^ ((α i * (b - z.re) + β i * (z.re - a)) / (b - a)) := by
  classical
  -- Normalize the growth hypotheses and choose logarithms of the factors.
  have hfc := hf.continuousOn_verticalClosedStrip hab
  have hGc : ∀ i ∈ s, ContinuousOn (G i) (re ⁻¹' Icc a b) := fun i hi ↦
    (hG i hi).continuousOn_verticalClosedStrip hab
  have hfB' := stripGrowth_of_isBigO hab hfc hfB
  have hGlow' : ∀ i ∈ s, 0 < α i ∨ 0 < β i → StripGrowth a b fun z ↦ ‖G i z‖⁻¹ :=
    fun i hi h ↦ (stripGrowth_of_isBigO hab ((hGc i hi).inv₀ (hG₀ i hi)) (hGlow i hi h)).of_le
      fun z _ ↦ (norm_inv _).ge
  have hGup' : ∀ i ∈ s, α i < 0 ∨ β i < 0 → StripGrowth a b fun z ↦ ‖G i z‖ :=
    fun i hi h ↦ stripGrowth_of_isBigO hab (hGc i hi) (hGup i hi h)
  have hlog : ∀ i, ∃ L : ℂ → ℂ, i ∈ s → DiffContOnCl ℂ L (re ⁻¹' Ioo a b) ∧
      ∀ z ∈ re ⁻¹' Icc a b, exp (L z) = G i z := fun i ↦ by
    by_cases hi : i ∈ s
    · obtain ⟨L, hL⟩ := exists_log_strip (hG i hi) (hG₀ i hi)
      exact ⟨L, fun _ ↦ hL⟩
    · exact ⟨0, fun h ↦ (hi h).elim⟩
  choose L hL using hlog
  -- The set of lines `re z = σ` of the strip on which the bound holds is closed, contains both
  -- boundary lines and is closed under midpoints, so it is all of `[a, b]`.
  set P : ℝ → Prop := fun σ ↦ ∀ t : ℝ, ‖f (σ + t * I)‖ ≤
    ∏ i ∈ s, ‖G i (σ + t * I)‖ ^ ((α i * (b - σ) + β i * (σ - a)) / (b - a))
  have hclosed : IsClosed {σ | σ ∈ Icc a b ∧ P σ} := isClosed_setOf_norm_le_prod_rpow hf hG hG₀
  -- At the two ends the interpolated exponents are `α i` and `β i`.
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hea : ∀ i, (α i * (b - a) + β i * (a - a)) / (b - a) = α i := fun i ↦ by
    field_simp; ring
  have heb : ∀ i, (α i * (b - b) + β i * (b - a)) / (b - a) = β i := fun i ↦ by
    field_simp; ring
  have hend_a : a ∈ {σ | σ ∈ Icc a b ∧ P σ} :=
    ⟨left_mem_Icc.2 hab.le, fun t ↦ by simpa only [hea] using ha t⟩
  have hend_b : b ∈ {σ | σ ∈ Icc a b ∧ P σ} :=
    ⟨right_mem_Icc.2 hab.le, fun t ↦ by simpa only [heb] using hb t⟩
  have hall := hclosed.Icc_subset_of_midpoint_mem
    (fun u hu v hv huv ↦ ⟨⟨by linarith [hu.1.1], by linarith [hv.1.2]⟩,
      norm_le_prod_rpow_interp_midpoint hf hfB' (fun i hi ↦ (hL i hi).1) (fun i hi ↦ (hL i hi).2)
        hGlow' hGup' hmono hanti hu.1.1 huv hv.1.2 hu.2 hv.2⟩)
    hend_a hend_b
  simpa only [re_add_im] using (hall ⟨hza, hzb⟩).2 z.im

end TauCeti.PhragmenLindelof
