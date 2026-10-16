/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SubgradientImage
public import TauCeti.Analysis.Convex.Differentiability
public import Mathlib.Analysis.InnerProductSpace.Positive
import TauCeti.Analysis.Calculus.SecondOrderExpansion
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Alexandrov's theorem: convex functions are twice differentiable almost everywhere

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with real representative
`F x = (f x).toReal`. **Alexandrov's theorem** says that at `μ`-almost every point `x` of the
effective domain, `F` has a second-order Taylor expansion

  `F x' = F x + ⟪∇F x, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)`

with a positive (symmetric, positive semidefinite) operator `A`, the Alexandrov Hessian of `F` at
`x`; it is the only symmetric operator giving such an expansion. The stronger statement proved
here is that the subdifferential `∂f` itself is differentiable at `x` with derivative `A`: every
subgradient `y'` of `f` at a point `x'` near `x` satisfies `y' = ∇F x + A (x' - x) + o(‖x' - x‖)`.

The proof goes through the resolvent of the subdifferential. If `y₁ ∈ ∂f(x₁)` and `y₂ ∈ ∂f(x₂)`,
then `‖x₁ - x₂‖ ≤ ‖(x₁ + y₁) - (x₂ + y₂)‖`, by monotonicity of `∂f`; so `x + y ↦ x` is a
well-defined `1`-Lipschitz map `J` on the set of points `x + y` with `y ∈ ∂f(x)`, the resolvent
`(I + ∂f)⁻¹`. Extend it to a Lipschitz map on `E`. By Rademacher's theorem it is differentiable
off a null set, and Lipschitz maps send null sets to null sets; by Sard's lemma it sends the points
where its derivative is singular to a null set. At almost every `x` the real representative is
differentiable and `x` avoids both of these null images; since `J (x + ∇F x) = x`, the map `J` is
then differentiable at `z = x + ∇F x` with invertible derivative `L`. Inverting the expansion of
`J` at `z` gives the expansion of `∂f` at `x`, with `A = L⁻¹ - I`.

The second-order expansion of `F` follows from that of `∂f` with no convexity: on the segment from
`x` to `x'`, split into `n` steps, the increments of `F` are squeezed between the subgradient
inequalities at the ends of each step, and summing them gives the expansion up to an error of
order `(‖A‖ / n + ε) * ‖x' - x‖ ^ 2`. Comparing that expansion with the subgradient inequality at
nearby points shows that `A` is symmetric and positive semidefinite. Both expansions determine
`A`: two derivatives of the subdifferential differ by a map that is `o(‖x' - x‖)`, and two symmetric
second-order terms differ by a quadratic form that is `o(‖x' - x‖ ^ 2)`, hence zero.

## Main statements

* `TauCeti.mul_norm_sub_le_norm_smul_add_smul_sub_of_mem_subdifferential` — the interpolation
  `x ↦ (1 - t) • x + t • y`, `y ∈ ∂f(x)`, expands distances by at least the factor `1 - t`;
* `TauCeti.norm_sub_le_norm_add_sub_add_of_mem_subdifferential` — the resolvent of the
  subdifferential is nonexpansive;
* `TauCeti.isLittleO_of_forall_mem_subdifferential_norm_sub_le` — a first-order expansion of the
  subdifferential at `x` gives a second-order Taylor expansion of `F` at `x`;
* `TauCeti.hasGradientAt_toReal_of_forall_mem_subdifferential_norm_sub_le` — the centre `y` of a
  first-order expansion of the subdifferential at `x` is the gradient of `F` at `x`;
* `TauCeti.subdifferential_eq_singleton_gradient_of_forall_mem_subdifferential_norm_sub_le` — the
  subdifferential at such a point `x` is the single gradient `∇F x`;
* `TauCeti.hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le` — the
  derivative of the subdifferential at `x` is the derivative of `∇F` at `x` within any set of
  points where `∇F` is a subgradient;
* `TauCeti.isPositive_of_forall_mem_subdifferential_norm_sub_le` — the derivative of the
  subdifferential is a positive operator;
* `TauCeti.eq_of_forall_mem_subdifferential_norm_sub_le` — the derivative of the subdifferential
  is unique;
* `TauCeti.apply_sub_eq_zero_of_forall_mem_subdifferential_norm_sub_le` — the derivative of the
  subdifferential vanishes along a segment on which a subgradient is shared;
* `TauCeti.ae_existsUnique_isPositive_forall_mem_subdifferential_norm_sub_le` — **Alexandrov's
  theorem** for the subdifferential: it is differentiable, with a unique and positive derivative,
  almost everywhere on the effective domain;
* `TauCeti.ae_existsUnique_isPositive_isLittleO` — **Alexandrov's theorem**: `F` has a
  second-order Taylor expansion with a unique positive Hessian almost everywhere on the effective
  domain;
* `ConvexOn.ae_existsUnique_isPositive_isLittleO` — the same for a real convex function on a set.

## References

* A. D. Alexandrov, *Almost everywhere existence of the second differential of a convex function
  and some properties of convex surfaces connected with it*, Leningrad State Univ. Annals
  [Uchenye Zapiski] Math. Ser. 6 (1939), 3–35.
* F. Mignot, *Contrôle dans les inéquations variationelles elliptiques*, J. Functional Analysis 22
  (1976), 130–185, for the route through the resolvent of a monotone operator.
* G. Alberti and L. Ambrosio, *A geometrical approach to monotone functions in `ℝⁿ`*, Math. Z. 230
  (1999), 259–316, Theorem 7.10.
* R. T. Rockafellar and R. J.-B. Wets, *Variational Analysis*, Grundlehren 317, Springer 1998,
  Theorem 13.51.
-/

public section

namespace TauCeti

open Filter Set Metric Asymptotics MeasureTheory MeasureTheory.Measure Function
open scoped Topology InnerProductSpace

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

/-- **The interpolation towards the subdifferential is expanding.** If `y₁ ∈ ∂f(x₁)`,
`y₂ ∈ ∂f(x₂)` and `0 ≤ t`, then
`(1 - t) * ‖x₁ - x₂‖ ≤ ‖((1 - t) • x₁ + t • y₁) - ((1 - t) • x₂ + t • y₂)‖`. In particular, for
`t < 1` the interpolating map `x ↦ (1 - t) • x + t • y`, `y ∈ ∂f(x)`, is injective. -/
theorem mul_norm_sub_le_norm_smul_add_smul_sub_of_mem_subdifferential {x₁ x₂ y₁ y₂ : E} {t : ℝ}
    (ht : 0 ≤ t) (h₁ : y₁ ∈ subdifferential (innerₗ E) f x₁)
    (h₂ : y₂ ∈ subdifferential (innerₗ E) f x₂) :
    (1 - t) * ‖x₁ - x₂‖ ≤ ‖(1 - t) • x₁ + t • y₁ - ((1 - t) • x₂ + t • y₂)‖ := by
  have hmono := apply_le_apply_of_mem_subdifferential (innerₗ E) h₁ h₂
  rw [innerₗ_apply_apply, innerₗ_apply_apply] at hmono
  have hpos : 0 ≤ ⟪x₁ - x₂, y₁ - y₂⟫_ℝ := by
    rw [← neg_sub x₂ x₁, inner_neg_left, inner_sub_right]
    linarith
  have hinner : ⟪(1 - t) • x₁ + t • y₁ - ((1 - t) • x₂ + t • y₂), x₁ - x₂⟫_ℝ =
      (1 - t) * ‖x₁ - x₂‖ ^ 2 + t * ⟪x₁ - x₂, y₁ - y₂⟫_ℝ := by
    rw [show (1 - t) • x₁ + t • y₁ - ((1 - t) • x₂ + t • y₂) =
        (1 - t) • (x₁ - x₂) + t • (y₁ - y₂) by simp only [smul_sub]; abel,
      inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm (y₁ - y₂)]
    simp
  rcases (norm_nonneg (x₁ - x₂)).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  refine le_of_mul_le_mul_right ?_ h0
  calc (1 - t) * ‖x₁ - x₂‖ * ‖x₁ - x₂‖ ≤ (1 - t) * ‖x₁ - x₂‖ ^ 2 + t * ⟪x₁ - x₂, y₁ - y₂⟫_ℝ := by
        nlinarith [mul_nonneg ht hpos]
    _ ≤ _ := by rw [← hinner]; exact real_inner_le_norm _ _

/-- **The resolvent of the subdifferential is nonexpansive.** If `y₁ ∈ ∂f(x₁)` and `y₂ ∈ ∂f(x₂)`,
then `‖x₁ - x₂‖ ≤ ‖(x₁ + y₁) - (x₂ + y₂)‖`. Thus `x + y ↦ x`, for `y ∈ ∂f(x)`, is a well-defined
`1`-Lipschitz map, the resolvent `(I + ∂f)⁻¹`. -/
theorem norm_sub_le_norm_add_sub_add_of_mem_subdifferential {x₁ x₂ y₁ y₂ : E}
    (h₁ : y₁ ∈ subdifferential (innerₗ E) f x₁) (h₂ : y₂ ∈ subdifferential (innerₗ E) f x₂) :
    ‖x₁ - x₂‖ ≤ ‖x₁ + y₁ - (x₂ + y₂)‖ := by
  have h := mul_norm_sub_le_norm_smul_add_smul_sub_of_mem_subdifferential (t := 1 / 2)
    (by norm_num) h₁ h₂
  rw [show (1 - 1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • y₁ - ((1 - 1 / 2 : ℝ) • x₂ + (1 / 2 : ℝ) • y₂) =
      (1 / 2 : ℝ) • (x₁ + y₁ - (x₂ + y₂)) by module, norm_smul] at h
  norm_num at h
  linarith

/-- **A first-order expansion of the subdifferential gives a second-order expansion of the
function.** Suppose `f : E → EReal` has subgradients at every point near `x`, and that these
follow the expansion `y' = y + A (x' - x) + o(‖x' - x‖)` uniformly over the subdifferential at
`x'`. Then the real representative of `f` has the second-order Taylor expansion
`F x' = F x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)`. No convexity is
needed. -/
theorem isLittleO_of_forall_mem_subdifferential_norm_sub_le {x y : E} {A : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    (fun x' => (f x').toReal - (f x).toReal - ⟪y, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
  -- Split the segment from `x` to `x' = x + h` into `n` steps of length `a = 1 / n`. Across
  -- each step the increment of `F = toReal ∘ f` lies between the subgradient inequalities at its
  -- two ends, and the subgradients there follow the linear expansion up to `(c / 2) * ‖h‖`.
  -- Summing, the increments of the expansion add up to `⟪y, h⟫ + ⟪A h, h⟫ / 2`, with an error
  -- of at most `(‖A‖ / (2 * n) + c / 2) * ‖h‖ ^ 2`.
  refine IsLittleO.of_bound fun c hc => ?_
  set F : E → ℝ := fun x' => (f x').toReal
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hne.and (hexp (c / 2) (by positivity)))
  choose Y hY using fun z => (show ∃ w, dist z x < r → w ∈ subdifferential (innerₗ E) f z from
    if h : dist z x < r then ⟨_, fun _ => (hball h).1.some_mem⟩ else ⟨0, fun h' => absurd h' h⟩)
  rw [Metric.eventually_nhds_iff]
  refine ⟨r, hr, fun x' hx' => ?_⟩
  set h := x' - x
  set X := ⟪h, A h⟫_ℝ
  set n : ℕ := ⌈‖A‖ / c⌉₊ + 1
  set a : ℝ := (n : ℝ)⁻¹
  have hn : (0 : ℝ) < n := by positivity
  have ha : 0 < a := inv_pos.2 hn
  have hna : (n : ℝ) * a = 1 := mul_inv_cancel₀ hn.ne'
  have hAa : ‖A‖ * a ≤ c := by
    have := Nat.le_ceil (‖A‖ / c)
    rw [div_le_iff₀ hc] at this
    rw [← le_div_iff₀ ha, div_eq_mul_inv, inv_inv]
    simp only [n, Nat.cast_add, Nat.cast_one]
    nlinarith
  set p : ℕ → E := fun k => x + ((k : ℝ) * a) • h
  have hpx : ∀ k ≤ n, ‖p k - x‖ ≤ ‖h‖ := fun k hk => by
    simp only [p, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [← hna]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ha.le
  have hp : ∀ k ≤ n, dist (p k) x < r := fun k hk =>
    (dist_eq_norm _ _).trans_lt ((hpx k hk).trans_lt (by rwa [← dist_eq_norm]))
  have hX : |X| ≤ ‖A‖ * ‖h‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [A.le_opNorm h, norm_nonneg h]
  -- Along the segment, `⟪h, Y (p k)⟫` follows the expansion up to `(c / 2) * ‖h‖ ^ 2`.
  have hY' : ∀ k ≤ n, |⟪h, Y (p k)⟫_ℝ - ⟪h, y⟫_ℝ - k * a * X| ≤ c / 2 * ‖h‖ ^ 2 :=
      fun k hk => by
    have hb := (hball (hp k hk)).2 _ (hY _ (hp k hk))
    have hpk : p k - x = ((k : ℝ) * a) • h := by simp only [p, add_sub_cancel_left]
    have : ⟪h, Y (p k)⟫_ℝ - ⟪h, y⟫_ℝ - k * a * X = ⟪h, Y (p k) - y - A (p k - x)⟫_ℝ := by
      rw [hpk, map_smul, inner_sub_right, inner_sub_right, real_inner_smul_right]
    rw [this]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖h‖ * ‖Y (p k) - y - A (p k - x)‖ ≤ ‖h‖ * (c / 2 * ‖h‖) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left (hpx k hk)
            (by positivity))) (norm_nonneg h)
      _ = c / 2 * ‖h‖ ^ 2 := by ring
  -- Each step's increment of `F` is within `‖A‖ ‖h‖² a² / 2 + (c / 2) ‖h‖² a` of that of the
  -- expansion.
  have hstep : ∀ k < n, |F (p (k + 1)) - F (p k) - (a * ⟪h, y⟫_ℝ + (k + 1 / 2) * a ^ 2 * X)| ≤
      ‖A‖ * ‖h‖ ^ 2 * a ^ 2 / 2 + c / 2 * ‖h‖ ^ 2 * a := fun k hk => by
    have hdiff : p (k + 1) - p k = a • h := by
      simp only [p, add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      ring
    have hk₀ := hY _ (hp k hk.le)
    have hk₁ := hY _ (hp (k + 1) hk)
    have hlow := toReal_add_le_toReal_of_mem_subdifferential (innerₗ E) hk₀
      (ne_top_of_mem_subdifferential _ hk₁)
    have hup := toReal_add_le_toReal_of_mem_subdifferential (innerₗ E) hk₁
      (ne_top_of_mem_subdifferential _ hk₀)
    rw [innerₗ_apply_apply, hdiff, real_inner_smul_left] at hlow
    rw [innerₗ_apply_apply, ← neg_sub, hdiff, inner_neg_left, real_inner_smul_left] at hup
    have e₀ := abs_le.1 (hY' k hk.le)
    have e₁ := abs_le.1 (hY' (k + 1) hk)
    have hX' := abs_le.1 hX
    push_cast at e₁
    have l₀ := mul_le_mul_of_nonneg_left e₀.1 ha.le
    have u₁ := mul_le_mul_of_nonneg_left e₁.2 ha.le
    have a₁ := mul_le_mul_of_nonneg_left hX'.1 (sq_nonneg a)
    have a₂ := mul_le_mul_of_nonneg_left hX'.2 (sq_nonneg a)
    rw [abs_le]
    constructor <;> nlinarith
  -- Sum the steps: the increments of `F` telescope, and those of the expansion add up to
  -- `⟪h, y⟫ + X / 2` because `n * a = 1`.
  have htel : ∑ k ∈ Finset.range n, (F (p (k + 1)) - F (p k)) = F x' - F x := by
    rw [Finset.sum_range_sub (fun k => F (p k))]
    simp only [p, Nat.cast_zero, zero_mul, zero_smul, add_zero, hna, one_smul, h,
      add_sub_cancel]
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (a * ⟪h, y⟫_ℝ + (k + 1 / 2) * a ^ 2 * X) =
      m * a * ⟪h, y⟫_ℝ + m ^ 2 * a ^ 2 * X / 2 := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hbound := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk =>
    hstep k (Finset.mem_range.1 hk))
  rw [Finset.sum_sub_distrib, htel, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    hna, show (n : ℝ) ^ 2 * a ^ 2 = 1 by rw [← mul_pow, hna, one_pow]] at hbound
  have : (n : ℝ) * (‖A‖ * ‖h‖ ^ 2 * a ^ 2 / 2 + c / 2 * ‖h‖ ^ 2 * a) =
      ‖A‖ * a * ‖h‖ ^ 2 / 2 + c / 2 * ‖h‖ ^ 2 := by
    linear_combination (‖A‖ * ‖h‖ ^ 2 * a / 2 + c / 2 * ‖h‖ ^ 2) * hna
  rw [this, one_mul, one_mul, ← sub_sub] at hbound
  have : ‖A‖ * a * ‖h‖ ^ 2 ≤ c * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right hAa (sq_nonneg _)
  rw [Real.norm_eq_abs, norm_pow, norm_norm, real_inner_comm h (A h), real_inner_comm h y]
  linarith

/-- **A first-order expansion of the subdifferential gives the gradient.** Suppose `f : E → EReal`
has subgradients at every point near `x`, and that these follow the expansion
`y' = y + A (x' - x) + o(‖x' - x‖)` uniformly over the subdifferential at `x'`. Then the real
representative of `f` has gradient `y` at `x`. No convexity is needed. -/
theorem hasGradientAt_toReal_of_forall_mem_subdifferential_norm_sub_le [CompleteSpace E]
    {x y : E} {A : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    HasGradientAt (fun x' => (f x').toReal) y x := by
  have hT := isLittleO_of_forall_mem_subdifferential_norm_sub_le hne hexp
  -- Both `‖x' - x‖ ^ 2` and the quadratic term of the second-order expansion are `o(x' - x)`.
  have hsq : (fun x' => ‖x' - x‖ ^ 2) =o[𝓝 x] fun x' => x' - x :=
    (isLittleO_norm_pow_id (E' := E) one_lt_two).comp_tendsto
      (tendsto_sub_nhds_zero_iff.2 tendsto_id)
  have hq : (fun x' => ⟪A (x' - x), x' - x⟫_ℝ / 2) =o[𝓝 x] fun x' => x' - x := by
    refine (IsBigO.of_bound (‖A‖ / 2) (Eventually.of_forall fun x' => ?_)).trans_isLittleO hsq
    calc ‖⟪A (x' - x), x' - x⟫_ℝ / 2‖ = ‖⟪A (x' - x), x' - x⟫_ℝ‖ / 2 := by simp
      _ ≤ ‖A (x' - x)‖ * ‖x' - x‖ / 2 := by gcongr; exact norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x' - x‖ * ‖x' - x‖ / 2 := by gcongr; exact A.le_opNorm _
      _ = ‖A‖ / 2 * ‖‖x' - x‖ ^ 2‖ := by simp only [norm_pow, norm_norm]; ring
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.of_isLittleO (((hT.trans hsq).add hq).congr_left fun x' => ?_)
  rw [InnerProductSpace.toDual_apply_apply]
  ring

/-- **A first-order expansion of the subdifferential makes it the single gradient.** Suppose
`f : E → EReal` has subgradients at every point near `x`, and that these follow the expansion
`y' = y + A (x' - x) + o(‖x' - x‖)` uniformly over the subdifferential at `x'`. Then the
subdifferential of `f` at `x` is the single gradient of the real representative of `f` at `x`. No
convexity is needed. -/
theorem subdifferential_eq_singleton_gradient_of_forall_mem_subdifferential_norm_sub_le
    [CompleteSpace E] {x y : E} {A : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    subdifferential (innerₗ E) f x = {gradient (fun x' => (f x').toReal) x} := by
  rw [(hasGradientAt_toReal_of_forall_mem_subdifferential_norm_sub_le hne hexp).gradient]
  refine eq_singleton_iff_nonempty_unique_mem.2 ⟨hne.self_of_nhds, fun y' hy' => ?_⟩
  simpa [sub_eq_zero] using (hexp 1 one_pos).self_of_nhds y' hy'

/-- **The derivative of the gradient within a set of subgradients.** Let `t` be a set at each point
of which the gradient of the real representative `F` of `f : E → EReal` is a subgradient of `f`.
If the subdifferential of `f` has the expansion `y' = ∇F x + A (x' - x) + o(‖x' - x‖)` at `x`,
then the gradient `∇F` has derivative `A` within `t` at `x`. No convexity is needed. -/
theorem hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
    [CompleteSpace E] {t : Set E} {x : E} {A : E →L[ℝ] E}
    (ht : ∀ x' ∈ t, gradient (fun x' => (f x').toReal) x' ∈ subdifferential (innerₗ E) f x')
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - gradient (fun x' => (f x').toReal) x - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    HasFDerivWithinAt (gradient fun x' => (f x').toReal) A t x := by
  refine HasFDerivWithinAt.of_isLittleO (IsLittleO.of_bound fun ε hε => ?_)
  filter_upwards [nhdsWithin_le_nhds (hexp ε hε), self_mem_nhdsWithin] with x' hx' hx't
  exact hx' _ (ht x' hx't)

/-- The comparison behind `isPositive_of_forall_mem_subdifferential_norm_sub_le`: under its
hypotheses, `⟪A b, a⟫ - ⟪A a, b⟫ + ⟪A b, b⟫ ≥ 0` for all `a` and `b`. The second-order expansion
of `F = toReal ∘ f` about `x`, compared with the subgradient inequality at `x + t • a` in the
direction `t • b`, gives this inequality up to an error of order `ε * t ^ 2`. -/
private theorem inner_sub_inner_add_inner_nonneg {x y : E} {A : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) (a b : E) :
    0 ≤ ⟪A b, a⟫_ℝ - ⟪A a, b⟫_ℝ + ⟪A b, b⟫_ℝ := by
  have hT := isLittleO_of_forall_mem_subdifferential_norm_sub_le hne hexp
  set M := ‖a + b‖ ^ 2 + ‖a‖ ^ 2 + ‖a‖ * ‖b‖
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε' := ε / (2 * M + 1)
  have hε' : 0 < ε' := by positivity
  have hlim : ∀ v : E, Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := fun v =>
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x
      (by simp)).mono_left nhdsWithin_le_nhds
  have hev := (hlim a).eventually (hne.and ((hexp ε' hε').and (hT.def hε')))
  have hev' := (hlim (a + b)).eventually (hne.and (hT.def hε'))
  obtain ⟨t, ⟨⟨⟨yh, hyh⟩, hexpa, hTa⟩, ⟨yab, hyab⟩, hTab⟩, ht⟩ :=
    ((hev.and hev').and self_mem_nhdsWithin).exists
  replace ht : 0 < t := mem_Ioi.1 ht
  simp only [add_sub_cancel_left, Real.norm_eq_abs, norm_pow, norm_smul,
    abs_of_pos ht, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at hTa hTab
  have he := hexpa yh hyh
  rw [add_sub_cancel_left, map_smul] at he
  have hsub := toReal_add_le_toReal_of_mem_subdifferential (innerₗ E) hyh
    (ne_top_of_mem_subdifferential _ hyab)
  rw [innerₗ_apply_apply, add_sub_add_left_eq_sub, ← smul_sub, add_sub_cancel_left,
    real_inner_smul_left] at hsub
  -- The subgradient `yh` at `x + t • a` is `y + t • A a` up to `ε' * t * ‖a‖`.
  have hyb : ⟪b, yh⟫_ℝ ≥ ⟪y, b⟫_ℝ + t * ⟪A a, b⟫_ℝ - t * (ε' * (‖a‖ * ‖b‖)) := by
    have hsplit : ⟪b, yh⟫_ℝ = ⟪y, b⟫_ℝ + t * ⟪A a, b⟫_ℝ + ⟪b, yh - y - t • A a⟫_ℝ := by
      simp only [inner_sub_right, real_inner_smul_right, real_inner_comm b]
      ring
    have hbe : |⟪b, yh - y - t • A a⟫_ℝ| ≤ t * (ε' * (‖a‖ * ‖b‖)) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at he
      calc ‖b‖ * ‖yh - y - t • A a‖ ≤ ‖b‖ * (ε' * (t * ‖a‖)) :=
            mul_le_mul_of_nonneg_left he (norm_nonneg b)
        _ = t * (ε' * (‖a‖ * ‖b‖)) := by ring
    linarith [(abs_le.1 hbe).1]
  have hTa' := (abs_le.1 hTa).1
  have hTab' := (abs_le.1 hTab).2
  rw [sq_abs, mul_pow] at hTa' hTab'
  simp only [inner_add_right, map_add, inner_add_left] at hTab'
  have hkey : t ^ 2 * 0 ≤ t ^ 2 * (⟪A b, a⟫_ℝ - ⟪A a, b⟫_ℝ + ⟪A b, b⟫_ℝ + 2 * ε' * M) := by
    have := mul_le_mul_of_nonneg_left hyb ht.le
    have hab : ‖a + b‖ ^ 2 = M - ‖a‖ ^ 2 - ‖a‖ * ‖b‖ := by simp only [M]; ring
    rw [hab] at hTab'
    nlinarith [real_inner_comm (A a) b]
  have hM : 2 * ε' * M ≤ ε := by
    have hM0 : 0 ≤ M := by positivity
    rw [show 2 * ε' * M = ε * (2 * M / (2 * M + 1)) by simp only [ε']; ring]
    exact mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 (by linarith))
  linarith [le_of_mul_le_mul_left hkey (by positivity)]

/-- **The derivative of the subdifferential is positive.** If the subgradients of `f : E → EReal`
near `x` follow the expansion `y' = y + A (x' - x) + o(‖x' - x‖)`, and exist at every point near
`x`, then `A` is a positive operator: symmetric with `⟪A v, v⟫ ≥ 0`. -/
theorem isPositive_of_forall_mem_subdifferential_norm_sub_le {x y : E} {A : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    A.IsPositive := by
  -- With `Q a b = ⟪A b, a⟫ - ⟪A a, b⟫ + ⟪A b, b⟫ ≥ 0`, `Q 0 b ≥ 0` is positivity, and
  -- `Q a (s • b) ≥ 0` for small `s > 0` forces `⟪A b, a⟫ ≥ ⟪A a, b⟫`, hence symmetry.
  have hQ := inner_sub_inner_add_inner_nonneg hne hexp
  have hD : ∀ a b : E, ⟪A a, b⟫_ℝ ≤ ⟪A b, a⟫_ℝ := by
    intro a b
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set s := ε / (|⟪A b, b⟫_ℝ| + 1)
    have hs : 0 < s := by positivity
    have h := hQ a (s • b)
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h
    have h' : 0 ≤ ⟪A b, a⟫_ℝ - ⟪A a, b⟫_ℝ + s * ⟪A b, b⟫_ℝ :=
      nonneg_of_mul_nonneg_right (by linarith) hs
    have hsb : s * ⟪A b, b⟫_ℝ ≤ ε := by
      calc s * ⟪A b, b⟫_ℝ ≤ s * |⟪A b, b⟫_ℝ| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.le
        _ ≤ s * (|⟪A b, b⟫_ℝ| + 1) := by linarith
        _ = ε := div_mul_cancel₀ _ (by positivity)
    linarith
  refine (A.isPositive_iff).2 ⟨fun u v => ?_, fun b => by simpa using hQ 0 b⟩
  rw [ContinuousLinearMap.coe_coe, real_inner_comm (A v) u]
  exact le_antisymm (hD u v) (hD v u)

/-- **The derivative of the subdifferential is unique.** If `f : E → EReal` has subgradients at
every point near `x`, and these follow both expansions `y' = y + A (x' - x) + o(‖x' - x‖)` and
`y' = y + B (x' - x) + o(‖x' - x‖)`, then `A = B`. -/
theorem eq_of_forall_mem_subdifferential_norm_sub_le {x y : E} {A B : E →L[ℝ] E}
    (hne : ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty)
    (hA : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖)
    (hB : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - B (x' - x)‖ ≤ ε * ‖x' - x‖) :
    A = B := by
  -- The map `x' ↦ (A - B) (x' - x)` has derivative `A - B` at `x`, and also derivative `0`, since
  -- comparing the two expansions at a subgradient near `x` makes it `o(‖x' - x‖)`.
  have h₀ : HasFDerivAt (fun x' => (A - B) (x' - x)) (0 : E →L[ℝ] E) x := by
    refine HasFDerivAt.of_isLittleO (IsLittleO.of_bound fun c hc => ?_)
    filter_upwards [hne, hA (c / 2) (half_pos hc), hB (c / 2) (half_pos hc)]
      with x' ⟨y', hy'⟩ hA' hB'
    have h : (A - B) (x' - x) = (y' - y - B (x' - x)) - (y' - y - A (x' - x)) := by
      rw [sub_apply]
      abel
    rw [sub_self, map_zero, sub_zero, zero_apply, sub_zero, h]
    linarith [norm_sub_le (y' - y - B (x' - x)) (y' - y - A (x' - x)), hA' y' hy', hB' y' hy']
  have h₁ : HasFDerivAt (fun x' => (A - B) (x' - x)) (A - B) x := by
    have h := (A - B).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    rwa [ContinuousLinearMap.comp_id] at h
  exact sub_eq_zero.1 (h₁.unique h₀)

/-- **The derivative of the subdifferential kills the direction of a flat segment.** Let
`f : E → EReal` be convex, and let `y` be a subgradient of `f` at both `x₁` and `x₂`. If the
subgradients of `f` near `x₁` follow the expansion `y' = y + A (x' - x₁) + o(‖x' - x₁‖)`, then
`A (x₂ - x₁) = 0`. So when `x₁ ≠ x₂` the operator `A` is singular: a point at which the
derivative of the subdifferential is invertible shares none of its subgradients with another
point. -/
theorem apply_sub_eq_zero_of_forall_mem_subdifferential_norm_sub_le
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {x₁ x₂ y : E} {A : E →L[ℝ] E}
    (h₁ : y ∈ subdifferential (innerₗ E) f x₁) (h₂ : y ∈ subdifferential (innerₗ E) f x₂)
    (hexp : ∀ ε > 0, ∀ᶠ x' in 𝓝 x₁, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x₁)‖ ≤ ε * ‖x' - x₁‖) :
    A (x₂ - x₁) = 0 := by
  set v := x₂ - x₁
  -- `y` is a subgradient at every point `x₁ + t • v` of the segment, so the expansion at a small
  -- `t > 0` gives `t * ‖A v‖ ≤ ε * (t * ‖v‖)`.
  have hε : ∀ ε > 0, ‖A v‖ ≤ ε * ‖v‖ := by
    intro ε hε
    have hp : Tendsto (fun t : ℝ => x₁ + t • v) (𝓝[>] 0) (𝓝 x₁) := by
      have : Continuous fun t : ℝ => x₁ + t • v := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0, ht1⟩ := ((hp.eventually (hexp ε hε)).and
      (Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))).exists
    have hy := (convex_setOf_mem_subdifferential (innerₗ E) hf y).add_smul_sub_mem h₁ h₂
      ⟨ht0.le, ht1⟩
    have h : t * ‖A v‖ ≤ ε * (t * ‖v‖) := by
      simpa [norm_smul, abs_of_nonneg ht0.le] using ht y hy
    exact le_of_mul_le_mul_left (by linarith) ht0
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  calc ‖A v‖ ≤ δ / (‖v‖ + 1) * ‖v‖ := hε _ (by positivity)
    _ ≤ 0 + δ := by
      rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]

/-- The expansion of the subdifferential at `x` obtained by inverting that of the resolvent. Let
`g` agree with the resolvent, `g (x' + y') = x'` whenever `y' ∈ ∂f(x')`, let `y ∈ ∂f(x)`, and let
`g` have the invertible derivative `L` at `x + y`. If the subgradients at points near `x` are close
to `y`, they follow the expansion `y' = y + (L⁻¹ - 1) (x' - x) + o(‖x' - x‖)`. -/
private theorem eventually_forall_mem_subdifferential_norm_sub_le_of_hasFDerivAt
    {g : E → E} {L : E ≃L[ℝ] E} {x y : E} (hy : y ∈ subdifferential (innerₗ E) f x)
    (hg : HasFDerivAt g (L : E →L[ℝ] E) (x + y))
    (hgx : ∀ x' y', y' ∈ subdifferential (innerₗ E) f x' → g (x' + y') = x')
    (hcont : ∀ δ > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y‖ ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - ((L.symm : E →L[ℝ] E) - 1) (x' - x)‖ ≤ ε * ‖x' - x‖ := by
  -- With `z' = x' + y'`, `w = z' - (x + y)` and `e = (x' - x) - L w`, the expansion of `g` at
  -- `x + y` gives `‖e‖ ≤ η ‖w‖`. Then `L⁻¹ (x' - x) = w + L⁻¹ e`, so `‖w‖ ≤ 2 M ‖x' - x‖` with
  -- `M = ‖L⁻¹‖`, and the error in the expansion of `y' = z' - x'` is `-L⁻¹ e`.
  set M := ‖(L.symm : E →L[ℝ] E)‖
  set η := min (1 / (2 * (M + 1))) (ε / (2 * (M + 1) ^ 2))
  have hη : 0 < η := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hg.isLittleO.def hη)
  filter_upwards [ball_mem_nhds x (half_pos hρ), hcont (ρ / 2) (half_pos hρ)] with x' hx' hy'
  intro y' hy'm
  set w := x' + y' - (x + y)
  have hw : w = (x' - x) + (y' - y) := by simp only [w]; abel
  have hz : dist (x' + y') (x + y) < ρ := by
    rw [dist_eq_norm, ← add_halves ρ]
    exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 hx')
      (hy' y' hy'm)) |>.trans_eq' (by rw [← hw])
  have hb := hball hz
  rw [hgx x' y' hy'm, hgx x y hy] at hb
  set e := x' - x - L w
  have he : ‖e‖ ≤ η * ‖w‖ := hb
  have hLe : L.symm (x' - x) = w + L.symm e := by
    simp only [e, map_sub, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hMe : ‖L.symm e‖ ≤ M * (η * ‖w‖) :=
    ((L.symm : E →L[ℝ] E).le_opNorm e).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
  have hMη : M * η ≤ 1 / 2 := by
    calc M * η ≤ M * (1 / (2 * (M + 1))) := mul_le_mul_of_nonneg_left (min_le_left _ _)
          (norm_nonneg _)
      _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [norm_nonneg (L.symm : E →L[ℝ] E)]
  have hwle : ‖w‖ ≤ 2 * M * ‖x' - x‖ := by
    have h₁ : ‖w‖ ≤ M * ‖x' - x‖ + M * (η * ‖w‖) := by
      calc ‖w‖ = ‖L.symm (x' - x) - L.symm e‖ := by rw [hLe, add_sub_cancel_right]
        _ ≤ ‖L.symm (x' - x)‖ + ‖L.symm e‖ := norm_sub_le _ _
        _ ≤ M * ‖x' - x‖ + M * (η * ‖w‖) :=
          add_le_add ((L.symm : E →L[ℝ] E).le_opNorm _) hMe
    nlinarith [norm_nonneg w]
  have hkey : y' - y - ((L.symm : E →L[ℝ] E) - 1) (x' - x) = -L.symm e := by
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearEquiv.coe_coe, hLe,
      ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id', id_eq, hw]
    abel
  rw [hkey, norm_neg]
  calc ‖L.symm e‖ ≤ M * (η * ‖w‖) := hMe
    _ ≤ M * (η * (2 * M * ‖x' - x‖)) := by gcongr
    _ = 2 * M ^ 2 * η * ‖x' - x‖ := by ring
    _ ≤ ε * ‖x' - x‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc 2 * M ^ 2 * η ≤ 2 * (M + 1) ^ 2 * (ε / (2 * (M + 1) ^ 2)) := by
            gcongr
            · nlinarith [norm_nonneg (L.symm : E →L[ℝ] E)]
            · exact min_le_right _ _
        _ = ε := by
          have : M + 1 ≠ 0 := by positivity
          field_simp

end InnerProduct

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ] {f : E → EReal}

/-- **Alexandrov's theorem for the subdifferential.** Let `f : E → EReal` be convex (convex real
epigraph, never `⊥`) on a finite-dimensional real inner product space with an additive Haar measure
`μ`. At `μ`-almost every point `x` of the effective domain, the subdifferential of `f` is
differentiable with a positive derivative `A`: every subgradient `y'` of `f` at a point `x'` near
`x` satisfies `y' = ∇F x + A (x' - x) + o(‖x' - x‖)`, where `F x = (f x).toReal`. The operator `A`
is the only positive operator with this expansion; uniqueness among all operators is
`eq_of_forall_mem_subdifferential_norm_sub_le`. -/
theorem ae_existsUnique_isPositive_forall_mem_subdifferential_norm_sub_le
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ → ∃! A : E →L[ℝ] E, A.IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - gradient (fun x' => (f x').toReal) x - A (x' - x)‖ ≤ ε * ‖x' - x‖ := by
  -- The resolvent `R : x + y ↦ x` (for `y ∈ ∂f(x)`) is `1`-Lipschitz on its domain; extend it to
  -- a Lipschitz map `g` on `E`.
  have hR : ∀ z, ∃ x, (∃ x', z - x' ∈ subdifferential (innerₗ E) f x') →
      z - x ∈ subdifferential (innerₗ E) f x := fun z => by
    by_cases h : ∃ x', z - x' ∈ subdifferential (innerₗ E) f x'
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose R hR using hR
  have hRx : ∀ x y, y ∈ subdifferential (innerₗ E) f x → R (x + y) = x := fun x y hy => by
    have h := norm_sub_le_norm_add_sub_add_of_mem_subdifferential
      (hR (x + y) ⟨x, by rwa [add_sub_cancel_left]⟩) hy
    rwa [add_sub_cancel, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at h
  have hRlip : LipschitzOnWith 1 R {z | ∃ x, z - x ∈ subdifferential (innerₗ E) f x} :=
    LipschitzOnWith.of_dist_le_mul fun z₁ h₁ z₂ h₂ => by
      have h := norm_sub_le_norm_add_sub_add_of_mem_subdifferential (hR z₁ h₁) (hR z₂ h₂)
      rw [add_sub_cancel, add_sub_cancel] at h
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h
  obtain ⟨g, hglip, hgR⟩ := hRlip.extend_finite_dimension
  have hgx : ∀ x y, y ∈ subdifferential (innerₗ E) f x → g (x + y) = x := fun x y hy => by
    rw [← hgR ⟨x, by rwa [add_sub_cancel_left]⟩, hRx x y hy]
  -- `g` maps the points where it is not differentiable, and those where its derivative is not
  -- surjective, to null sets.
  have hgN : μ (g '' {z | ¬DifferentiableAt ℝ g z}) = 0 :=
    hglip.lipschitzOnWith.addHaar_image_eq_zero μ μ le_rfl
      (measure_eq_zero_iff_ae_notMem.2 (hglip.ae_differentiableAt.mono fun _ h h' => h' h))
  have hgC : μ (g '' {z | DifferentiableAt ℝ g z ∧ ¬Surjective (fderiv ℝ g z)}) = 0 :=
    addHaar_image_eq_zero_of_not_surjective_fderivWithin μ rfl
      (fun z hz => hz.1.hasFDerivAt.hasFDerivWithinAt) fun z hz => hz.2
  filter_upwards [ae_eventually_ne_top_and_differentiableAt_toReal hf hbot,
    measure_eq_zero_iff_ae_notMem.1 hgN, measure_eq_zero_iff_ae_notMem.1 hgC]
    with x hx hxN hxC hfx
  obtain ⟨hdom, hdiff⟩ := hx hfx
  -- At such an `x`, with `y = ∇F x ∈ ∂f(x)`, `g` is differentiable at `x + y` with invertible
  -- derivative, since `g (x + y) = x`.
  set y := gradient (fun x' => (f x').toReal) x
  have hy : y ∈ subdifferential (innerₗ E) f x :=
    gradient_toReal_mem_subdifferential hf hbot hfx hdiff
  have hdz : DifferentiableAt ℝ g (x + y) := by
    by_contra h
    exact hxN ⟨x + y, h, hgx x y hy⟩
  have hsurj : Surjective (fderiv ℝ g (x + y)) := by
    by_contra h
    exact hxC ⟨x + y, ⟨hdz, h⟩, hgx x y hy⟩
  set L : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (fderiv ℝ g (x + y))
    (LinearMap.ker_eq_bot.2 (LinearMap.injective_iff_surjective.2 hsurj))
    (LinearMap.range_eq_top.2 hsurj)
  have hL : HasFDerivAt g (L : E →L[ℝ] E) (x + y) := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hdz.hasFDerivAt
  have hexp := fun ε (hε : 0 < ε) =>
    eventually_forall_mem_subdifferential_norm_sub_le_of_hasFDerivAt hy hL hgx
      (fun δ hδ => eventually_forall_mem_subdifferential_norm_sub_le hdom hdiff.hasGradientAt hδ)
      hε
  have hne := eventually_nonempty_subdifferential hf hbot hdom
  exact ⟨_, ⟨isPositive_of_forall_mem_subdifferential_norm_sub_le hne hexp, hexp⟩,
    fun B hB => eq_of_forall_mem_subdifferential_norm_sub_le hne hB.2 hexp⟩

/-- **Alexandrov's theorem.** Let `f : E → EReal` be convex (convex real epigraph, never `⊥`) on a
finite-dimensional real inner product space with an additive Haar measure `μ`, and let
`F x = (f x).toReal`. At `μ`-almost every point `x` of the effective domain, `F` has a
second-order Taylor expansion
`F x' = F x + ⟪∇F x, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)`
with a positive operator `A`, the only positive operator giving such an expansion. -/
theorem ae_existsUnique_isPositive_isLittleO
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ → ∃! A : E →L[ℝ] E, A.IsPositive ∧
      (fun x' => (f x').toReal - (f x).toReal -
          ⟪gradient (fun x' => (f x').toReal) x, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
        =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
  filter_upwards
    [ae_existsUnique_isPositive_forall_mem_subdifferential_norm_sub_le (μ := μ) hf hbot,
    ae_eventually_ne_top_and_differentiableAt_toReal (μ := μ) hf hbot] with x h₁ h₂ hfx
  obtain ⟨A, ⟨hA, hexp⟩, -⟩ := h₁ hfx
  have hT := isLittleO_of_forall_mem_subdifferential_norm_sub_le
    (eventually_nonempty_subdifferential hf hbot (h₂ hfx).1) hexp
  exact ⟨A, ⟨hA, hT⟩, fun B hB => eq_of_isSymmetric_of_isLittleO hB.1.isSymmetric
    hA.isSymmetric hB.2 hT⟩

/-- **Alexandrov's theorem** for a real convex function. Let `u` be convex on a set `Ω` of a
finite-dimensional real inner product space with an additive Haar measure `μ`. At `μ`-almost every
point `x` of `Ω`, `u` is differentiable and has a second-order Taylor expansion
`u x' = u x + ⟪∇u x, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)` with a positive
operator `A`, the only positive operator giving such an expansion. -/
theorem _root_.ConvexOn.ae_existsUnique_isPositive_isLittleO {Ω : Set E} {u : E → ℝ}
    (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂μ, x ∈ Ω → DifferentiableAt ℝ u x ∧ ∃! A : E →L[ℝ] E, A.IsPositive ∧
      (fun x' => u x' - u x - ⟪gradient u x, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
        =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
  classical
  -- Extend `u` by `⊤` off `Ω`. Almost every point of `Ω` is interior, and near an interior point
  -- the real representative of the extension is `u` itself.
  filter_upwards [TauCeti.ae_existsUnique_isPositive_isLittleO (μ := μ) (convex_epigraph_ite hu)
    ite_ne_bot, hu.ae_differentiableAt_of_mem, hu.1.ae_mem_interior] with x h₁ h₂ h₃ hx
  have heq : (fun x' => ((if x' ∈ Ω then (u x' : EReal) else ⊤)).toReal) =ᶠ[𝓝 x] u :=
    eventually_of_mem (isOpen_interior.mem_nhds (h₃ hx)) fun x' hx' => by
      simp [interior_subset hx']
  obtain ⟨A, ⟨hA, hT⟩, -⟩ := h₁ (by simp [hx])
  have hT' : (fun x' => u x' - u x - ⟪gradient u x, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
    refine hT.congr' ?_ EventuallyEq.rfl
    filter_upwards [heq] with x' hx'
    rw [hx', heq.gradient_eq, heq.eq_of_nhds]
  exact ⟨h₂ hx, A, ⟨hA, hT'⟩, fun B hB => eq_of_isSymmetric_of_isLittleO hB.1.isSymmetric
    hA.isSymmetric hB.2 hT'⟩

end FiniteDimensional

end TauCeti
