/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Contour.Argument.PowerSum
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.RingTheory.Polynomial.PrescribedPowerSums

/-!
# Holomorphic divisors confined in the transverse direction

Let `E` be a complex normed space, the *base*, and let `f : E × ℂ → ℂ` be holomorphic. For each
base point `x`, the transverse slice `w ↦ f (x, w)` is an entire function of one variable, with
its divisor of zeros. Suppose the zeros are **confined**: `f (x, w) ≠ 0` whenever `‖w‖ ≥ K`, for
one constant `K` and every `x`. Then the transverse divisor does not depend on the base point:
there is a single multiset `s` of points of the open disc of radius `K` such that the order of
vanishing of every slice `w ↦ f (x, w)` at every `w` is the multiplicity of `w` in `s`
(`Differentiable.exists_forall_analyticOrderAt_eq_count`).

This is the classification step for the holomorphic zero divisors that arise as rescaled limits
of Seiberg–Witten solutions along a pseudoholomorphic curve. In Taubes's analysis such a limit
lives on `ℂ_base × ℂ_normal`, its zero divisor is holomorphic and confined to a bounded normal
disc, and the conclusion here says that the divisor is the product of `ℂ_base` with a fixed
divisor of `ℂ_normal`. A confined holomorphic divisor of `ℂ × ℂ` is therefore never a nontrivial
holomorphic family of plane divisors.

Restricting `f` to the complex line through `0` and `x` reduces the statement to a base `ℂ`, where
a holomorphic function is analytic (`DifferentiableOn.analyticOnNhd_of_finiteDimensional`). For an
analytic `f`, the proof is the classical one through symmetric functions. Choose `R > K`. For each
`x`, the `k`-th power sum of the zeros of the slice in the disc of radius `R` is the contour
integral `(2πi)⁻¹ ∮ ζᵏ ∂_w f (x, ζ) / f (x, ζ)`
(`TauCeti.Contour.sum_map_pow_zeroMultiset_eq_circleIntegral_fderiv`), which is holomorphic in `x`
(`TauCeti.Contour.differentiableAt_sum_map_pow_zeroMultiset`). For `k = 0` it is
the number of zeros, which is therefore constant, say `N`. The `k`-th power sum is then bounded by
`N Rᵏ`, so it is constant by Liouville's theorem. By Newton's identities the power sums determine
the multiset of zeros (`TauCeti.roots_newtonPolynomial_sum_map_pow`).

Over a finite-dimensional base the divisor can then be divided out: a holomorphic `f` whose
slices all vanish to the orders recorded by a multiset `s` is
`f (x, w) = q (x, w) ∏_{a ∈ s} (w - a)` with `q` holomorphic and nowhere zero
(`Differentiable.exists_eq_mul_prod_sub_of_forall_analyticOrderAt_eq_count`). The factors are
removed one at a time by the transverse divided slope `(x, w) ↦ dslope (f (x, ·)) a w`, which is
jointly holomorphic because near each point it is a Cauchy integral depending analytically on
`(x, w)` (`Differentiable.dslope_prodMk`, using `TauCeti.analyticAt_circleIntegral`). For a
confined `f` this writes the zeros as the base-independent divisor `E × s` times a holomorphic unit
(`Differentiable.exists_eq_mul_prod_sub_of_forall_le_norm_ne_zero`), which is how such a limit is
compared with the plane vortex that has the zeros `s`.

## Main results

* `Differentiable.exists_forall_analyticOrderAt_eq_count`: a holomorphic function on `E × ℂ` whose
  zeros are confined to `‖w‖ < K` has a base-independent transverse divisor, given by a multiset of
  points of norm less than `K`.
* `Differentiable.analyticOrderAt_eq_of_forall_le_norm_ne_zero`: the same conclusion, comparing the
  slices over two base points.
* `Differentiable.dslope_prodMk`: the transverse divided slope of a holomorphic function on a
  finite-dimensional base is holomorphic.
* `Differentiable.exists_eq_mul_prod_sub_of_forall_analyticOrderAt_eq_count`: a base-independent
  transverse divisor `s` divides out, `f = q ∏_{a ∈ s} (w - a)` with `q` a holomorphic unit.
* `Differentiable.exists_eq_mul_prod_sub_of_forall_le_norm_ne_zero`: the factorization of a confined
  holomorphic function.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1, for the
  symmetric functions of the zeros of a holomorphic family.
-/

public section

open Complex Metric Real Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The case of `Differentiable.exists_forall_analyticOrderAt_eq_count` where `f` is analytic. -/
private theorem exists_forall_analyticOrderAt_eq_count_of_analyticOnNhd {f : E × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ)
    {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w := by
  classical
  set R := max K 0 + 1
  have hR : 0 < R := by positivity
  have hKR : K < R := by grind
  have hf' (x : E) : ∀ ζ ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (x, ζ) :=
    fun ζ _ ↦ hf (x, ζ) trivial
  have hslice (x : E) : AnalyticOnNhd ℂ (fun w ↦ f (x, w)) (closedBall 0 R) :=
    fun w hw ↦ (hf' x w hw).curry_right
  have hsphere (x : E) : ∀ ζ ∈ sphere (0 : ℂ) R, f (x, ζ) ≠ 0 := fun ζ hζ ↦
    hK x ζ (by rw [mem_sphere_zero_iff_norm.1 hζ]; exact hKR.le)
  set Z : E → Multiset ℂ := fun x ↦ AnalyticOnNhd.zeroMultiset (fun w ↦ f (x, w)) (ball 0 R)
  have hdiff (k : ℕ) : Differentiable ℂ fun x ↦ ((Z x).map (· ^ k)).sum := fun x ↦
    Contour.differentiableAt_sum_map_pow_zeroMultiset hR (hf' x) (hsphere x) k
  -- The number of zeros is the zeroth power sum: it is continuous and integer valued, hence
  -- constant on the connected base.
  have hcard (x : E) : (Z x).card = (Z 0).card :=
    Contour.card_zeroMultiset_eq_of_isPreconnected isPreconnected_univ hR (fun x _ ↦ hf' x)
      (fun x _ ↦ hsphere x) trivial trivial
  -- Every zero lies in `ball 0 R`, so the `k`-th power sum is bounded by `card (Z 0) * R ^ k`,
  -- and Liouville's theorem makes it constant.
  have hpow (k : ℕ) (x : E) : ((Z x).map (· ^ k)).sum = ((Z 0).map (· ^ k)).sum := by
    refine (hdiff k).apply_eq_apply_of_bounded ?_ x 0
    refine isBounded_iff_forall_norm_le.2 ⟨(Z 0).card * R ^ k, ?_⟩
    rintro _ ⟨y, rfl⟩
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map, ← hcard y]
    refine (Multiset.sum_le_card_nsmul _ (R ^ k) fun t ht ↦ ?_).trans_eq (by simp)
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 ht
    rw [Function.comp_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg a)
      (mem_ball_zero_iff.1 (AnalyticOnNhd.mem_of_mem_zeroMultiset ha)).le k
  -- Newton's identities recover each multiset of zeros from its power sums.
  have hZ (x : E) : Z x = Z 0 := by
    rw [← roots_newtonPolynomial_sum_map_pow (Z x), ← roots_newtonPolynomial_sum_map_pow (Z 0),
      hcard x, funext fun k ↦ hpow k x]
  have horder (x : E) {w : ℂ} (hw : w ∈ closedBall 0 R) :
      analyticOrderAt (fun w ↦ f (x, w)) w = (Z 0).count w := by
    rw [← hZ x]
    exact (hslice x).analyticOrderAt_eq_count_zeroMultiset (hsphere x) hw
  have hmem (a : ℂ) (ha : a ∈ Z 0) : ‖a‖ < K := by
    by_contra hKa
    exact hK 0 a (not_lt.1 hKa) (((hslice 0).mem_zeroMultiset_iff (hsphere 0)).1 ha).2
  refine ⟨Z 0, hmem, fun x w ↦ ?_⟩
  by_cases hKw : K ≤ ‖w‖
  · rw [(hf (x, w) trivial).curry_right.analyticOrderAt_eq_zero.2 (hK x w hKw),
      Multiset.count_eq_zero.2 fun hw ↦ (hmem w hw).not_ge hKw, Nat.cast_zero]
  · exact horder x (mem_closedBall_zero_iff.2 (by grind))


end TauCeti

namespace Differentiable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Base-independence of a confined transverse divisor.** Let `f : E × ℂ → ℂ` be holomorphic,
and suppose that `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there is a multiset `s` of points of
norm less than `K` such that for every base point `x` and every `w`, the order of vanishing of
`w ↦ f (x, w)` at `w` is the multiplicity of `w` in `s`. -/
theorem exists_forall_analyticOrderAt_eq_count {f : E × ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w := by
  -- On the complex line through `0` and `x`, `f` is a holomorphic function on `ℂ × ℂ`, hence
  -- analytic.
  have hline (x : E) : ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∀ (t : ℂ) w, analyticOrderAt (fun w ↦ f (t • x, w)) w = s.count w :=
    TauCeti.exists_forall_analyticOrderAt_eq_count_of_analyticOnNhd
      (f := fun p : ℂ × ℂ ↦ f (p.1 • x, p.2))
      ((hf.comp ((differentiable_fst.smul_const x).prodMk differentiable_snd)).differentiableOn
        |>.analyticOnNhd_of_finiteDimensional isOpen_univ)
      fun t w hw ↦ hK _ w hw
  have hbase (x : E) (w : ℂ) :
      analyticOrderAt (fun w ↦ f (x, w)) w = analyticOrderAt (fun w ↦ f (0, w)) w := by
    obtain ⟨s, -, hs⟩ := hline x
    simpa using (hs 1 w).trans (hs 0 w).symm
  obtain ⟨s, hsK, hs⟩ := hline 0
  exact ⟨s, hsK, fun x w ↦ (hbase x w).trans (by simpa using hs 0 w)⟩

/-- **Base-independence of a confined transverse divisor, pairwise form.** If `f : E × ℂ → ℂ` is
holomorphic and `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`, then the slices `w ↦ f (x, w)` and
`w ↦ f (y, w)` over any two base points have the same order of vanishing at every point. -/
theorem analyticOrderAt_eq_of_forall_le_norm_ne_zero {f : E × ℂ → ℂ}
    (hf : Differentiable ℂ f) {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) (x y : E)
    (w : ℂ) :
    analyticOrderAt (fun w ↦ f (x, w)) w = analyticOrderAt (fun w ↦ f (y, w)) w := by
  obtain ⟨s, -, hs⟩ := hf.exists_forall_analyticOrderAt_eq_count hK
  rw [hs, hs]

/-! ### Dividing out a base-independent transverse divisor -/

section Division

variable [FiniteDimensional ℂ E]

/-- The Cauchy integrand `(ζ - w)⁻¹ (ζ - a)⁻¹ (f (x, ζ) - f (x, a))` of the transverse divided
slope is jointly analytic in `((x, w), ζ)` away from `ζ = w` and `ζ = a`. -/
private theorem analyticAt_cauchyDSlopeIntegrand {f : E × ℂ → ℂ} (hf : Differentiable ℂ f)
    (a : ℂ) {p₀ : E × ℂ} {ζ : ℂ} (h₁ : ζ ≠ p₀.2) (h₂ : ζ ≠ a) :
    AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦
      (q.2 - q.1.2)⁻¹ * ((q.2 - a)⁻¹ * (f (q.1.1, q.2) - f (q.1.1, a)))) (p₀, ζ) := by
  have hfa : AnalyticOnNhd ℂ f univ :=
    hf.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ
  have hx : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ q.1.1) (p₀, ζ) :=
    analyticAt_fst.comp analyticAt_fst
  have hw : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ q.1.2) (p₀, ζ) :=
    analyticAt_snd.comp analyticAt_fst
  have hf₁ : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ f (q.1.1, q.2)) (p₀, ζ) :=
    (hfa _ trivial).comp (hx.prod analyticAt_snd)
  have hf₂ : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ f (q.1.1, a)) (p₀, ζ) :=
    (hfa _ trivial).comp (hx.prod analyticAt_const)
  have hs₁ : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ q.2 - q.1.2) (p₀, ζ) := analyticAt_snd.sub hw
  have hs₂ : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ ↦ q.2 - a) (p₀, ζ) :=
    analyticAt_snd.sub analyticAt_const
  exact (hs₁.inv (sub_ne_zero.2 h₁)).mul ((hs₂.inv (sub_ne_zero.2 h₂)).mul (hf₁.sub hf₂))

/-- **The transverse divided slope of a holomorphic function is holomorphic.** For a holomorphic
`f : E × ℂ → ℂ` on a finite-dimensional base and a point `a ∈ ℂ`, the divided slope
`(x, w) ↦ dslope (f (x, ·)) a w` of the transverse slices is jointly holomorphic. Near a point
`(x₀, w₀)` it is the Cauchy integral
`(2πi)⁻¹ ∮_{|ζ - a| = R} (ζ - w)⁻¹ (ζ - a)⁻¹ (f (x, ζ) - f (x, a)) dζ` with `R > ‖w₀ - a‖`, which
depends analytically on `(x, w)`. -/
theorem dslope_prodMk {f : E × ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ fun p : E × ℂ ↦ dslope (fun w ↦ f (p.1, w)) a p.2 := by
  intro p₀
  set R := ‖p₀.2 - a‖ + 1 with hR
  have hR₀ : 0 < R := by positivity
  -- The Cauchy integrand, a function of the parameter `p = (x, w)` and of `ζ`.
  set G : (E × ℂ) × ℂ → ℂ := fun q ↦ (q.2 - q.1.2)⁻¹ * ((q.2 - a)⁻¹ * (f (q.1.1, q.2) -
    f (q.1.1, a))) with hG
  have hGa : ∀ ζ ∈ sphere a |R|, AnalyticAt ℂ G (p₀, ζ) := by
    intro ζ hζ
    rw [abs_of_pos hR₀, mem_sphere_iff_norm] at hζ
    refine hf.analyticAt_cauchyDSlopeIntegrand a (fun h ↦ ?_) fun h ↦ ?_
    · rw [h] at hζ
      linarith
    · rw [h, sub_self, norm_zero] at hζ
      linarith
  -- Near `p₀` the divided slope is `(2πi)⁻¹` times the Cauchy integral of `G`.
  have heq : (fun p : E × ℂ ↦ (2 * π * I : ℂ)⁻¹ * ∮ ζ in C(a, R), G (p, ζ)) =ᶠ[nhds p₀]
      fun p ↦ dslope (fun w ↦ f (p.1, w)) a p.2 := by
    have hmem : {p : E × ℂ | p.2 ∈ ball a R} ∈ nhds p₀ :=
      (isOpen_ball.preimage continuous_snd).mem_nhds
        (mem_ball_iff_norm.2 (by rw [hR]; linarith))
    filter_upwards [hmem] with p hp
    have hd : Differentiable ℂ (dslope (fun w ↦ f (p.1, w)) a) := fun w ↦
      ((differentiableOn_dslope (Filter.univ_mem)).2
        (hf.comp (differentiable_const p.1 |>.prodMk differentiable_id)).differentiableOn w
          trivial).differentiableAt Filter.univ_mem
    have hC := hd.differentiableOn.circleIntegral_sub_inv_smul (c := a) (R := R) hp
    have hcongr : ∮ ζ in C(a, R), G (p, ζ) =
        ∮ ζ in C(a, R), (ζ - p.2)⁻¹ • dslope (fun w ↦ f (p.1, w)) a ζ := by
      refine circleIntegral.integral_congr hR₀.le fun ζ hζ ↦ ?_
      have hζa : ζ ≠ a := by
        rintro rfl
        simp only [mem_sphere_iff_norm, sub_self, norm_zero] at hζ
        linarith
      simp [hG, dslope_of_ne _ hζa, slope_def_field, div_eq_inv_mul]
    rw [hcongr, hC, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]
  exact ((analyticAt_const.mul (TauCeti.analyticAt_circleIntegral hGa)).congr heq).differentiableAt

/-- **Dividing out a base-independent transverse divisor.** Let `f : E × ℂ → ℂ` be holomorphic on
a finite-dimensional base, and suppose that every transverse slice `w ↦ f (x, w)` vanishes at
every `w` to order exactly the multiplicity of `w` in a multiset `s`. Then
`f (x, w) = q (x, w) ∏_{a ∈ s} (w - a)` with `q` holomorphic and nowhere zero. -/
theorem exists_eq_mul_prod_sub_of_forall_analyticOrderAt_eq_count {f : E × ℂ → ℂ}
    (hf : Differentiable ℂ f) {s : Multiset ℂ}
    (hs : ∀ x w, analyticOrderAt (fun w ↦ f (x, w)) w = s.count w) :
    ∃ q : E × ℂ → ℂ, Differentiable ℂ q ∧ (∀ p, q p ≠ 0) ∧
      ∀ p, f p = q p * (s.map fun a ↦ p.2 - a).prod := by
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    refine ⟨f, hf, fun p ↦ ?_, fun p ↦ by simp⟩
    have h := hs p.1 p.2
    rw [Multiset.count_zero, Nat.cast_zero, analyticOrderAt_eq_zero] at h
    exact h.resolve_left (not_not.2 ((hf.comp (differentiable_const p.1 |>.prodMk
      differentiable_id)).analyticAt p.2))
  | cons a t ih =>
    have hslice (x : E) : Differentiable ℂ fun w ↦ f (x, w) :=
      hf.comp (differentiable_const x |>.prodMk differentiable_id)
    -- Every slice vanishes at `a`, so `f (x, w) = (w - a) g (x, w)` for the divided slope `g`.
    have hfa (x : E) : f (x, a) = 0 :=
      (analyticOrderAt_ne_zero (f := fun w ↦ f (x, w)) (z₀ := a)).1 (by simp [hs x a]) |>.2
    set g : E × ℂ → ℂ := fun p ↦ dslope (fun w ↦ f (p.1, w)) a p.2
    have hfg (p : E × ℂ) : f p = (p.2 - a) * g p := by
      have h := sub_smul_dslope (fun w ↦ f (p.1, w)) a p.2
      simp only [hfa, sub_zero, smul_eq_mul] at h
      exact h.symm
    -- The slices of `g` vanish to the orders recorded by `t`.
    have hgt (x : E) (w : ℂ) : analyticOrderAt (fun w ↦ g (x, w)) w = t.count w := by
      have hga : AnalyticAt ℂ (fun w ↦ g (x, w)) w := ((hslice x).analyticAt w).dslope a
      have hlin : AnalyticAt ℂ (fun w ↦ w - a) w := analyticAt_id.sub analyticAt_const
      have h := hs x w
      rw [show (fun w ↦ f (x, w)) = (fun w ↦ w - a) * fun w ↦ g (x, w) from
        funext fun w ↦ hfg (x, w), analyticOrderAt_mul hlin hga] at h
      by_cases hw : w = a
      · subst hw
        have h₁ : analyticOrderAt (fun w' ↦ w' - w) w = (1 : ℕ) :=
          hlin.analyticOrderAt_eq_natCast.2 ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
            Filter.Eventually.of_forall fun _ ↦ by simp⟩
        rw [h₁, Multiset.count_cons_self, Nat.cast_succ, add_comm] at h
        simpa using h
      · have h₀ : analyticOrderAt (fun w' ↦ w' - a) w = 0 :=
          analyticOrderAt_eq_zero.2 (Or.inr (sub_ne_zero.2 hw))
        rwa [h₀, zero_add, Multiset.count_cons_of_ne hw] at h
    obtain ⟨q, hq, hq₀, hgq⟩ := ih (f := g) (hf.dslope_prodMk a) hgt
    refine ⟨q, hq, hq₀, fun p ↦ ?_⟩
    rw [hfg p, hgq p, Multiset.map_cons, Multiset.prod_cons]
    ring

/-- **Factorization of a confined holomorphic function.** Let `f : E × ℂ → ℂ` be holomorphic on a
finite-dimensional base, with `f (x, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there are a multiset `s` of
points of norm less than `K` and a nowhere-zero holomorphic `q` with
`f (x, w) = q (x, w) ∏_{a ∈ s} (w - a)`. So the zeros of `f` are the base-independent divisor
`E × s`, and dividing them out leaves a holomorphic unit. -/
theorem exists_eq_mul_prod_sub_of_forall_le_norm_ne_zero {f : E × ℂ → ℂ}
    (hf : Differentiable ℂ f) {K : ℝ} (hK : ∀ x w, K ≤ ‖w‖ → f (x, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ q : E × ℂ → ℂ, Differentiable ℂ q ∧
      (∀ p, q p ≠ 0) ∧ ∀ p, f p = q p * (s.map fun a ↦ p.2 - a).prod := by
  obtain ⟨s, hsK, hs⟩ := hf.exists_forall_analyticOrderAt_eq_count hK
  exact ⟨s, hsK, hf.exists_eq_mul_prod_sub_of_forall_analyticOrderAt_eq_count hs⟩

end Division

end Differentiable
