/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Operator
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.MeasureTheory.Function.Lp.Operator.Local

/-!
# What the kernel of a Calderón–Zygmund operator determines

A Calderón–Zygmund operator `T` on `L²(V, F)` with standard kernel `K`
(`TauCeti.HasStandardKernel`) is given by `T f x = ∫ K x y • f y dy` only for `x` off the support
of `f`. This file shows that the kernel and the operator determine each other exactly up to what
this description cannot see.

* **The operator determines the kernel off the diagonal.** If `T` has the standard kernels `K`
  and `K'`, then `K x y = K' x y` whenever `x ≠ y`, for nonzero complete `F`
  (`TauCeti.HasStandardKernel.unique`). Testing `T` on `1_{B(y, r)} e` for a vector `e ≠ 0` gives
  equal averages of `K x ·` and `K' x ·` over `B(y, r)` at almost every `x` near a point `x₀ ≠ y`,
  and both kernels are continuous off the diagonal
  (`TauCeti.HasStandardKernel.continuousOn_uncurry`).
* **The kernel determines the operator up to a bounded multiplication operator.** An operator
  that agrees with `T` off the support of its argument has the same standard kernel
  (`TauCeti.HasStandardKernel.of_forall_ae_eq`); in particular so does `T + M_a` for the
  multiplication operator `M_a` of any `a ∈ L^∞(V)`
  (`TauCeti.HasStandardKernel.add_multiplicationOperator`). Conversely, when `F` is
  finite-dimensional, two operators with the same kernel differ by multiplication by a strongly
  measurable field `m : V → (F →L[ℂ] F)` of essential supremum at most the norm of their
  difference (`TauCeti.HasStandardKernel.hasStandardKernel_iff_exists_ae_eq_add`), by the general
  statement for operators given by a common kernel
  (`ContinuousLinearMap.exists_forall_ae_eq_add_of_ae_eq_integral`). For
  scalar functions, `F = ℂ`, the operators with the standard kernel `K` are exactly the
  `T + M_a`, `a ∈ L^∞(V)`
  (`TauCeti.HasStandardKernel.hasStandardKernel_iff_exists_eq_add_multiplicationOperator`).

So the operator, not the kernel, is the primitive datum of a Calderón–Zygmund operator: for
instance, the identity has the kernel `0` (`TauCeti.hasStandardKernel_id`), and hence so has
`1 + M_a` for every `a ∈ L^∞(V)`. For infinite-dimensional `F` a local operator need not be
multiplication by a strongly measurable field (see
`TauCeti.MeasureTheory.Function.Lp.Operator.Local`), so there only the direction from
multiplication operators to kernels is stated.

## References

* E. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals*,
  Chapter VII, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace HasStandardKernel

variable {T T' : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)}
  {K K' : V → V → ℂ} {C C' : ℝ≥0} {δ δ' : ℝ}

/-- On a set of points `y` at which `x` is off the diagonal, `y ↦ K x y` is integrable when the set
lies in a compact set avoiding `x`. -/
private theorem integrableOn_of_isCompact (h : HasStandardKernel T K C δ) {x : V} {s t : Set V}
    (ht : IsCompact t) (hst : s ⊆ t) (hxt : x ∉ t) : IntegrableOn (K x) s :=
  -- Membership of `(x, y)` in the off-diagonal `{p | p.1 ≠ p.2}` is `x ≠ y` by definition.
  ((h.continuousOn_uncurry.comp (Continuous.prodMk_right x).continuousOn
    fun y hy ↦ show x ≠ y from fun hxy ↦ hxt (hxy ▸ hy)).integrableOn_compact ht).mono_set hst

/-- Away from a ball `B(y₀, r)` carrying the test function `1_{B(y₀, r)} e`, the operator acts by
integrating the kernel over the ball. -/
private theorem ae_apply_indicatorConstLp_eq [CompleteSpace F] (h : HasStandardKernel T K C δ)
    (y₀ : V) (r : ℝ) (e : F) :
    ∀ᵐ x, x ∉ closedBall y₀ r → T (indicatorConstLp 2 (measurableSet_ball (x := y₀) (ε := r))
      (measure_ball_lt_top (μ := volume)).ne e) x = (∫ y in ball y₀ r, K x y) • e := by
  have hf : ⇑(indicatorConstLp 2 (measurableSet_ball (x := y₀) (ε := r))
      (measure_ball_lt_top (μ := volume)).ne e) =ᵐ[volume] (ball y₀ r).indicator fun _ ↦ e :=
    indicatorConstLp_coeFn
  have hsupp : ∀ᵐ y, y ∉ closedBall y₀ r → (indicatorConstLp 2
      (measurableSet_ball (x := y₀) (ε := r)) (measure_ball_lt_top (μ := volume)).ne e :
        V → F) y = 0 := by
    filter_upwards [hf] with y hy hyr
    rw [hy, indicator_of_notMem fun hyb ↦ hyr (ball_subset_closedBall hyb)]
  filter_upwards [h.ae_apply_eq_integral _ _ (isCompact_closedBall y₀ r) hsupp] with x hx hxr
  rw [hx hxr, ← integral_smul_const, ← integral_indicator measurableSet_ball]
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  rw [hy]
  by_cases hyb : y ∈ ball y₀ r <;> simp [hyb]

/-- Testing an operator with two standard kernels `K` and `K'` on `1_{B(y₀, r)} e` for a vector
`e ≠ 0`: if `3 r ≤ dist x₀ y₀`, then at some `x ∈ B(x₀, r)` the difference `K x · - K' x ·` is
integrable on `B(y₀, r)` with integral `0`. -/
private theorem exists_integral_sub_eq_zero [Nontrivial F] [CompleteSpace F]
    (h : HasStandardKernel T K C δ) (h' : HasStandardKernel T K' C' δ') (x₀ y₀ : V) {r : ℝ}
    (hr : 0 < r) (hrd : 3 * r ≤ dist x₀ y₀) :
    ∃ x ∈ ball x₀ r, IntegrableOn (fun y ↦ K x y - K' x y) (ball y₀ r) ∧
      ∫ y in ball y₀ r, (K x y - K' x y) = 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : F)
  have hev : ∀ᵐ x ∂volume.restrict (ball x₀ r), x ∈ ball x₀ r ∧ (x ∉ closedBall y₀ r →
      (∫ y in ball y₀ r, K x y) • e = (∫ y in ball y₀ r, K' x y) • e) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (h.ae_apply_indicatorConstLp_eq y₀ r e),
      ae_restrict_of_ae (h'.ae_apply_indicatorConstLp_eq y₀ r e)] with x hx h₁ h₂
    exact ⟨hx, fun hxr ↦ (h₁ hxr).symm.trans (h₂ hxr)⟩
  have := ae_restrict_neBot.2 (measure_ball_pos volume x₀ hr).ne'
  obtain ⟨x, hx, hxe⟩ := hev.exists
  -- The point `x` lies at distance more than `r` from `y₀`.
  have hxr : x ∉ closedBall y₀ r := fun hxr ↦ by
    rw [mem_ball] at hx
    rw [mem_closedBall] at hxr
    linarith [dist_triangle x₀ x y₀, dist_comm x x₀]
  have hK := h.integrableOn_of_isCompact (isCompact_closedBall y₀ r) ball_subset_closedBall hxr
  have hK' := h'.integrableOn_of_isCompact (isCompact_closedBall y₀ r) ball_subset_closedBall hxr
  refine ⟨x, hx, hK.sub hK', ?_⟩
  rw [integral_sub hK hK', smul_left_injective ℂ he (hxe hxr), sub_self]

/-- **The operator determines its kernel off the diagonal.** If a Calderón–Zygmund operator `T` on
`L²(V, F)`, `F` nonzero and complete, has the standard kernels `K` and `K'`, then `K x y = K' x y`
for all `x ≠ y`. Nothing is claimed on the diagonal, where the definition asks nothing of the
kernel. -/
theorem unique [Nontrivial F] [CompleteSpace F] (h : HasStandardKernel T K C δ)
    (h' : HasStandardKernel T K' C' δ') {x₀ y₀ : V} (hxy : x₀ ≠ y₀) : K x₀ y₀ = K' x₀ y₀ := by
  set D : V → V → ℂ := fun x y ↦ K x y - K' x y
  have hd : 0 < dist x₀ y₀ := dist_pos.2 hxy
  have hD : ContinuousAt (Function.uncurry D) (x₀, y₀) :=
    (h.continuousOn_uncurry.sub h'.continuousOn_uncurry).continuousAt
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hxy)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- `D` is within `ε` of `D x₀ y₀` on `B(x₀, r) × B(y₀, r)`, and has zero average over `B(y₀, r)`
  -- in the second variable at some `x ∈ B(x₀, r)`.
  obtain ⟨ρ, hρ, hDρ⟩ := Metric.continuousAt_iff.1 hD ε hε
  set r := min ρ (dist x₀ y₀ / 3)
  have hr : 0 < r := lt_min hρ (by positivity)
  obtain ⟨x, hx, hint, hzero⟩ := exists_integral_sub_eq_zero h h' x₀ y₀ hr
    (by linarith [min_le_right ρ (dist x₀ y₀ / 3)])
  have hvol : 0 < volume.real (ball y₀ r) :=
    ENNReal.toReal_pos (measure_ball_pos volume y₀ hr).ne' measure_ball_lt_top.ne
  have key : volume.real (ball y₀ r) * ‖D x₀ y₀‖ ≤ ε * volume.real (ball y₀ r) := by
    calc volume.real (ball y₀ r) * ‖D x₀ y₀‖ = ‖∫ y in ball y₀ r, (D x₀ y₀ - D x y)‖ := by
          rw [integral_sub (integrableOn_const measure_ball_lt_top.ne) hint, hzero, sub_zero,
            setIntegral_const, norm_smul, Real.norm_of_nonneg hvol.le]
      _ ≤ ε * volume.real (ball y₀ r) := by
          refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun y hy ↦ ?_
          rw [norm_sub_rev, ← dist_eq_norm]
          refine (@hDρ (x, y) ?_).le
          rw [Prod.dist_eq]
          exact max_lt (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _))
  rw [zero_add]
  exact le_of_mul_le_mul_left (key.trans_eq (mul_comm _ _)) hvol

/-- **Agreement off supports preserves the kernel.** An operator `T'` that agrees with a
Calderón–Zygmund operator `T` off the compact support of its argument (whenever `f` vanishes almost
everywhere off a compact set `s`, `T' f x = T f x` for almost every `x ∉ s`) has the same standard
kernel, with the same constants. -/
theorem of_forall_ae_eq (h : HasStandardKernel T K C δ)
    (hT' : ∀ (f : Lp F 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T' f x = T f x) :
    HasStandardKernel T' K C δ where
  exponent_pos := h.exponent_pos
  norm_le := h.norm_le
  norm_sub_add_norm_sub_le := h.norm_sub_add_norm_sub_le
  ae_apply_eq_integral f s hs hf := by
    filter_upwards [hT' f s hs hf, h.ae_apply_eq_integral f s hs hf] with x h₁ h₂ hx
    rw [h₁ hx, h₂ hx]

/-- **Adding a multiplication operator preserves the kernel.** If `T` is a Calderón–Zygmund
operator with standard kernel `K`, then so is `T + M_a` for multiplication `M_a` by any
`a ∈ L^∞(V)`, with the same constants: `M_a f` vanishes wherever `f` does. -/
theorem add_multiplicationOperator (h : HasStandardKernel T K C δ)
    (a : Lp ℂ ∞ (volume : Measure V)) :
    HasStandardKernel (T + Lp.multiplicationOperator a) K C δ :=
  h.of_forall_ae_eq fun f s _ hf ↦ by
    filter_upwards [Lp.coeFn_add (T f) (Lp.multiplicationOperator a f),
      Lp.multiplicationOperator_ae a f, hf] with x h₁ h₂ h₃ hx
    rw [add_apply, h₁, Pi.add_apply, h₂, h₃ hx]
    simp

/-- **Operators with the same kernel differ by a multiplication operator.** Let `T` be a
Calderón–Zygmund operator with standard kernel `K` on `L²(V, F)` for finite-dimensional `F`.
Another operator `T'` on `L²(V, F)` has the standard kernel `K`, with the same constants, if and
only if `T' = T + m` for multiplication by a strongly measurable field `m : V → (F →L[ℂ] F)`,
which can be taken of essential supremum at most `‖T' - T‖`. -/
theorem hasStandardKernel_iff_exists_ae_eq_add [FiniteDimensional ℂ F]
    (h : HasStandardKernel T K C δ) :
    HasStandardKernel T' K C δ ↔ ∃ m : V → F →L[ℂ] F, StronglyMeasurable m ∧
      (∀ᵐ x, ‖m x‖ ≤ ‖T' - T‖) ∧ ∀ f, T' f =ᵐ[volume] fun x ↦ T f x + m x (f x) := by
  have : ProperSpace F := FiniteDimensional.proper_rclike ℂ F
  refine ⟨fun h' ↦ T'.exists_forall_ae_eq_add_of_ae_eq_integral ENNReal.ofNat_ne_top T
    (fun x y ↦ ContinuousLinearMap.lsmul ℂ ℂ (K x y)) h'.ae_apply_eq_integral
    h.ae_apply_eq_integral, fun ⟨m, _, _, hm⟩ ↦ h.of_forall_ae_eq fun f s _ hf ↦ ?_⟩
  filter_upwards [hm f, hf] with x h₁ h₂ hx
  rw [h₁, h₂ hx, map_zero, add_zero]

/-- **The scalar Calderón–Zygmund operators with a given kernel.** Let `T` be a Calderón–Zygmund
operator on `L²(V)` with standard kernel `K`. An operator `T'` on `L²(V)` has the standard kernel
`K`, with the same constants, if and only if `T' = T + M_a` for the multiplication operator `M_a`
of some `a ∈ L^∞(V)`. -/
theorem hasStandardKernel_iff_exists_eq_add_multiplicationOperator
    {T T' : Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V)}
    (h : HasStandardKernel T K C δ) :
    HasStandardKernel T' K C δ ↔
      ∃ a : Lp ℂ ∞ (volume : Measure V), T' = T + Lp.multiplicationOperator a := by
  refine ⟨fun h' ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ h.add_multiplicationOperator a⟩
  obtain ⟨m, hm, hmT, hTm⟩ := h.hasStandardKernel_iff_exists_ae_eq_add.1 h'
  -- The scalar symbol is `x ↦ m x 1`, essentially bounded by `‖T' - T‖`.
  have ha : MemLp (fun x ↦ m x 1) ∞ volume :=
    memLp_top_of_bound ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_stronglyMeasurable
      hm).aestronglyMeasurable ‖T' - T‖ <| by
      filter_upwards [hmT] with x hx
      exact (le_of_le_of_eq ((m x).le_opNorm 1) (by rw [norm_one, mul_one])).trans hx
  refine ⟨ha.toLp _, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [hTm f, Lp.coeFn_add (T f) (Lp.multiplicationOperator (ha.toLp _) f),
    Lp.multiplicationOperator_ae (ha.toLp _) f, ha.coeFn_toLp] with x h₁ h₂ h₃ h₄
  -- `m x` is `ℂ`-linear on `ℂ`, so `m x (f x) = f x • m x 1`.
  rw [h₁, add_apply, h₂, Pi.add_apply, h₃, h₄]
  simpa [mul_comm] using (m x).map_smul (f x) 1

end HasStandardKernel

end TauCeti
