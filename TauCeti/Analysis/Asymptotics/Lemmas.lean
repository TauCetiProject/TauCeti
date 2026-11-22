/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Elementary asymptotic criteria

General criteria that supplement Mathlib's asymptotics API, elementary estimates, and an
elementary limit of ratios.

For functions into a normed division ring, `f` satisfies `f = a g + o(g)` exactly when `f / g`
tends to `a`, provided `g` is eventually nonzero. This criterion converts little-o error estimates
into limits of normalized functions, and conversely recovers error estimates from ratio limits.
The quotient is right division: multiplication need not be commutative. For ordered fields,
the ratio formulation also supports order arguments.

If `(σ - a) • f(σ)` has a limit along a filter on a normed division ring that eventually avoids
`a`, then `f(σ) = O((σ - a)⁻¹)` along it. On the real line, for `a = 1` and the right-sided limit
`σ → 1⁺`, this is the growth bound near `s = 1` of a Dedekind zeta function or an `L`-series with
a simple pole there, read off from the limit of `(s - 1) L(s)` along the real axis.

A map `u` between pseudometric spaces whose distances satisfy
`dist (u y) (u y') = O(dist y y')` near `(x, x)`, the difference estimate of a strictly
differentiable map, is continuous at `x`. Only this Lipschitz-type estimate is used, not
differentiability or any additive structure.

In a seminormed group the norm is at most one on a neighbourhood of the origin, so there a higher
power of the norm is dominated by any lower one. This is the comparison that lets a Taylor
remainder of one order be read as a remainder of a smaller order.

A bound `‖g x‖ ≤ A / ‖x - c‖ ^ n` outside a ball about any centre `c` of a normed division ring
gives `g = O(x⁻¹ ^ n)` at infinity: the decay rate of an inverse power does not depend on the
centre.

A bound `F = O(x ^ r)` at infinity survives the dilation `x ↦ c x` for `c > 0`. This is how
rapid decay at infinity, `O(x ^ r)` for every `r`, passes to rescaled functions such as the
theta kernels of a lattice at a level. A bound `u n = O(n ^ r)` on a sequence likewise passes to
the step function `t ↦ u ⌊t⌋₊` as `O(t ^ r)`, since `⌊t⌋₊ ∼ t`; this is how a bound on the
partial sums of a sequence enters an integral against the partial-sum step function.

An eventual big-O bound at `atTop` is uniform on a whole half-line `[a, ∞)` of a linear order as
soon as the dominated function is bounded on the intervals `[a, b]` and the dominating one is
bounded away from zero. This is how an asymptotic estimate becomes an explicit inequality valid at
every point, which a summation argument can apply at infinitely many points at once. Continuity of
both functions on the half-line, with a nonvanishing dominating function, is another sufficient
condition when closed intervals are compact: it covers exponentially decaying majorants such as
`exp (-p x)`. For the slowly decaying majorant `(log x)⁻¹` on `[a, ∞)` (`a > 1`), local
boundedness of `f` on compact intervals alone suffices, covering step functions such as summatory
functions.

A fixed power of a shifted natural number times a geometric sequence of ratio of absolute value
less than one tends to zero. This is the form needed to absorb polynomial growth after shifting an
index.

If the weighted terms `aₙ qⁿ` of a real sequence are bounded by `A` at a radius `q > 0`, then at
a radius `c` they are bounded by `A * (|c| / q)ⁿ`. For `|c| < q` this geometric bound is the
estimate behind every loss of radius for power series.

In an ordered field, the ratio `(t + x) / (t + y)` of two translates tends to `1` as `t → ∞`. This
is the limit at infinity of antiderivatives built from such ratios, for example in elementary
evaluations of elliptic integrals.

## Main results

* `Asymptotics.isLittleO_sub_mul_iff_tendsto_div`: `f - a g = o(g)` if and only if
  `f / g → a`, for an eventually nonzero `g`.
* `Asymptotics.isBigO_inv_sub_of_tendsto_sub_smul`: if `(σ - a) • f(σ)` converges along a filter
  on which eventually `σ ≠ a`, then `f(σ) = O((σ - a)⁻¹)` along it.
* `Asymptotics.isBigO_norm_pow_norm_pow_nhds_zero_of_le`: `‖x‖ ^ m = O(‖x‖ ^ n)` at the origin
  whenever `n ≤ m`.
* `Asymptotics.isBigO_inv_pow_cobounded_of_norm_le`: a bound `‖g x‖ ≤ A / ‖x - c‖ ^ n` for
  `‖x - c‖ > R` gives `g = O(x⁻¹ ^ n)` at infinity.
* `Asymptotics.IsBigO.comp_const_mul_rpow`: `F = O(x ^ r)` at infinity implies
  `F (c x) = O(x ^ r)` for `c > 0`.
* `Asymptotics.IsBigO.comp_natFloor_rpow`: `u n = O(n ^ r)` implies `u ⌊t⌋₊ = O(t ^ r)` as
  `t → ∞`.
* `Asymptotics.isLittleO_smul_const_self_iff`: if `ψ` is frequently nonzero, then `ψ • c = o(ψ)`
  if and only if `c = 0`.
* `Asymptotics.isBigO_smul_const_self`: `u • c = O(u)` for a scalar function `u` and a constant
  vector `c` with `‖r • c‖ ≤ ‖r‖ * ‖c‖` for every scalar `r`.
* `Asymptotics.IsBigO.isBigO_principal_Ici`: `f = O(g)` at `atTop` gives `f = O(g)` on `[a, ∞)`
  when `f` is bounded on each `[a, b]` and `‖g‖` is bounded below on `[a, ∞)` by a positive
  constant.
* `Asymptotics.IsBigO.isBigO_principal_Ici_of_continuousOn`: the same conclusion when closed
  intervals are compact, `f` and `g` are continuous on `[a, ∞)` and `g` does not vanish there.
* `Asymptotics.IsBigO.exists_norm_le_div_log`: `f = O((log x)⁻¹)` at `atTop` gives a uniform bound
  `‖f x‖ ≤ C / log x` on `[a, ∞)` (`a > 1`) when `f` is bounded on each `[a, b]`.
* `TauCeti.tendsto_add_pow_mul_pow_of_abs_lt_one`: `(n + m) ^ k * ρ ^ n` tends to zero when
  `|ρ| < 1`.
* `TauCeti.mul_abs_pow_le_of_forall_mul_pow_le`: weighted terms bounded by `A` at a radius `q > 0`
  are bounded by `A * (|c| / q)ⁿ` at the radius `c`.
* `TauCeti.continuousAt_of_isBigO_dist`: `dist (u y) (u y') = O(dist y y')` near `(x, x)` implies
  continuity of `u` at `x`.
* `TauCeti.tendsto_add_div_add_atTop`: `(t + x) / (t + y) → 1` as `t → ∞`.

## Related results

Mathlib's `Asymptotics.isLittleO_iff_tendsto'` is the underlying zero-limit ratio criterion, and
`Asymptotics.isBigO_pow_pow_cobounded_of_le` is the comparison of powers at infinity. Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler, derives the
bound `f(σ) = O((σ - 1)⁻¹)` for the Dirichlet `L`-function of the trivial character in
`DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal`.
-/

public section

open Filter Topology

namespace Asymptotics

/-- **A linear asymptotic is a limit of ratios.** For an eventually nonzero `g`, `f = a g + o(g)`
if and only if `f / g` tends to `a`. -/
theorem isLittleO_sub_mul_iff_tendsto_div {α 𝕜 : Type*} [NormedDivisionRing 𝕜]
    {l : Filter α} {f g : α → 𝕜} {a : 𝕜} (hg : ∀ᶠ x in l, g x ≠ 0) :
    (fun x ↦ f x - a * g x) =o[l] g ↔ Tendsto (fun x ↦ f x / g x) l (𝓝 a) := by
  rw [isLittleO_iff_tendsto' (hg.mono fun x hx ↦ by simp [hx])]
  refine (tendsto_congr' (hg.mono fun x hx ↦ ?_)).trans tendsto_sub_nhds_zero_iff
  rw [sub_div, mul_div_cancel_right₀ _ hx]

/-- **A limit of `(σ - a) • f(σ)` bounds `f` by `(σ - a)⁻¹`.** If `(σ - a) • f(σ)` has a limit
along a filter `l` on a normed division ring `𝕜` on which eventually `σ ≠ a`, then
`f(σ) = O((σ - a)⁻¹)` along `l`. The action of `𝕜` need only be a multiplicative action with
`‖c • x‖ ≤ ‖c‖ * ‖x‖`, as `norm_smul_le` gives for any bounded action. Typical choices of `l` are
the one-sided and punctured neighbourhoods of `a`. For `𝕜 = ℝ`, `a = 1` and `l = 𝓝[>] 1` this is
how such a bound is usually obtained for a Dedekind zeta function or an `L`-series near `s = 1`,
from the limit of `(s - 1) L(s)` along the real axis. -/
theorem isBigO_inv_sub_of_tendsto_sub_smul {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [SeminormedAddGroup E] [MulAction 𝕜 E] (hb : ∀ (c : 𝕜) (x : E), ‖c • x‖ ≤ ‖c‖ * ‖x‖)
    {l : Filter 𝕜} {f : 𝕜 → E} {a : 𝕜} {r : E} (hne : ∀ᶠ σ in l, σ ≠ a)
    (h : Tendsto (fun σ ↦ (σ - a) • f σ) l (𝓝 r)) :
    f =O[l] fun σ ↦ (σ - a)⁻¹ := by
  obtain ⟨C, hC⟩ := (h.norm.isBigO_one ℝ).bound
  refine .of_bound C ?_
  filter_upwards [hne, hC] with σ hσ hCσ
  rw [Real.norm_eq_abs, abs_norm, norm_one, mul_one] at hCσ
  rw [← inv_smul_smul₀ (sub_ne_zero.2 hσ) (f σ), mul_comm]
  exact (hb _ _).trans (mul_le_mul_of_nonneg_left hCσ (norm_nonneg _))

/-- **At the origin a higher power of the norm is dominated by a lower one.** The norm is at most
one near `0`, so `‖x‖ ^ m = O(‖x‖ ^ n)` whenever `n ≤ m`. -/
theorem isBigO_norm_pow_norm_pow_nhds_zero_of_le {E : Type*} [SeminormedAddGroup E]
    {m n : ℕ} (h : n ≤ m) :
    (fun x : E ↦ ‖x‖ ^ m) =O[𝓝 (0 : E)] fun x ↦ ‖x‖ ^ n := by
  refine isBigO_iff.2 ⟨1, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with x hx
  simp only [one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg x)]
  exact pow_le_pow_of_le_one (norm_nonneg x) (by simpa [Metric.mem_closedBall] using hx) h

/-- **An inverse-power bound about any centre is a decay bound at infinity.** If
`‖g x‖ ≤ A / ‖x - c‖ ^ n` whenever `R < ‖x - c‖`, then `g = O(x⁻¹ ^ n)` along `cobounded 𝕜`. -/
theorem isBigO_inv_pow_cobounded_of_norm_le {𝕜 E : Type*} [NormedDivisionRing 𝕜] [Norm E]
    {g : 𝕜 → E} {c : 𝕜} {R A : ℝ} (n : ℕ)
    (hg : ∀ x, R < ‖x - c‖ → ‖g x‖ ≤ A / ‖x - c‖ ^ n) :
    g =O[Bornology.cobounded 𝕜] fun x ↦ x⁻¹ ^ n := by
  -- `g = O((x - c)⁻¹ ^ n)`, as `R < ‖x - c‖` eventually
  have hgc : g =O[Bornology.cobounded 𝕜] fun x ↦ (x - c)⁻¹ ^ n :=
    .of_bound A <| (tendsto_norm_cobounded_atTop.eventually_gt_atTop (R + ‖c‖)).mono fun x hx ↦
      by simpa [div_eq_mul_inv] using hg x (by linarith [norm_sub_norm_le x c])
  -- `x - c ∼ x`, as the constant `c` is `o(x)`; hence `x = O(x - c)`
  have hx : (fun x : 𝕜 ↦ x) =O[Bornology.cobounded 𝕜] fun x ↦ x - c :=
    IsEquivalent.isBigO_symm <| (isLittleO_const_id_cobounded (-c)).congr_left fun x ↦ by simp
  exact hgc.trans ((hx.inv_rev ((Bornology.eventually_ne_cobounded 0).mono
    fun _ h h0 ↦ absurd h0 h)).pow n)

/-- **A power bound at infinity survives a dilation.** If `F = O(x ^ r)` as `x → ∞`, then
`F (c x) = O(x ^ r)` for every `c > 0`. -/
theorem IsBigO.comp_const_mul_rpow {E : Type*} [Norm E] {F : ℝ → E} {r c : ℝ}
    (hF : F =O[atTop] (· ^ r)) (hc : 0 < c) :
    (fun x ↦ F (c * x)) =O[atTop] (· ^ r) := by
  refine (hF.comp_tendsto (tendsto_id.const_mul_atTop hc)).trans ?_
  refine ((isBigO_refl (fun x : ℝ ↦ x ^ r) atTop).const_mul_left (c ^ r)).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 0] with x hx
  simp [Real.mul_rpow hc.le hx]

/-- **A power bound on a sequence passes to its step function.** If `u n = O(n ^ r)` as
`n → ∞`, then `u ⌊t⌋₊ = O(t ^ r)` as `t → ∞`, for every real exponent `r`. -/
theorem IsBigO.comp_natFloor_rpow {E : Type*} [Norm E] {u : ℕ → E} {r : ℝ}
    (hu : u =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ u ⌊t⌋₊) =O[atTop] (· ^ r) := by
  have hmax : (fun t : ℝ ↦ max t 0) =ᶠ[atTop] fun t ↦ t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact max_eq_left ht
  have hequiv : (fun t : ℝ ↦ (⌊t⌋₊ : ℝ)) ~[atTop] fun t ↦ max t 0 :=
    isEquivalent_nat_floor.congr_right hmax.symm
  exact (hu.comp_tendsto tendsto_nat_floor_atTop).trans <|
    (hequiv.rpow fun _ ↦ le_max_right _ _).isBigO.congr' EventuallyEq.rfl
      (hmax.fun_comp fun t ↦ t ^ r)

/-- **An eventual big-O bound holds on a whole half-line.** If `f = O(g)` at `atTop`, `f` is
bounded on every interval `[a, b]`, and `‖g‖` is bounded below by a positive constant on
`[a, ∞)`, then `f = O(g)` uniformly on `[a, ∞)`. -/
theorem IsBigO.isBigO_principal_Ici {ι E F : Type*} [LinearOrder ι] [Norm E] [Norm F]
    {f : ι → E} {g : ι → F} {a : ι} {c : ℝ} (h : f =O[atTop] g) (hc : 0 < c)
    (hg : ∀ x, a ≤ x → c ≤ ‖g x‖) (hf : ∀ b, ∃ B, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) :
    f =O[𝓟 (Set.Ici a)] g := by
  -- `eventually_atTop` needs a nonempty order
  have : Nonempty ι := ⟨a⟩
  obtain ⟨c₀, hc₀⟩ := h.bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hc₀
  obtain ⟨B, hB⟩ := hf b
  refine isBigO_principal.mpr ⟨max c₀ (max B 0 / c), fun x hx ↦ ?_⟩
  have hgx := hg x hx
  have hg0 : 0 ≤ ‖g x‖ := hc.le.trans hgx
  rcases le_or_gt b x with hbx | hbx
  · exact (hb x hbx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0)
  · calc ‖f x‖ ≤ max B 0 := (hB x ⟨hx, hbx.le⟩).trans (le_max_left _ _)
      _ ≤ max B 0 / c * ‖g x‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        exact mul_le_mul_of_nonneg_left hgx (le_max_right _ _)
      _ ≤ max c₀ (max B 0 / c) * ‖g x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) hg0

/-- **An eventual big-O bound holds on a whole half-line, continuous version.** In a linear
order whose closed intervals are compact, if `f = O(g)` at `atTop`, both functions are continuous
on `[a, ∞)` and `g` does not vanish there, then `f = O(g)` uniformly on `[a, ∞)`. Unlike
`IsBigO.isBigO_principal_Ici`, `‖g‖` may tend to zero, as for an exponentially decaying
majorant. -/
theorem IsBigO.isBigO_principal_Ici_of_continuousOn {ι E F : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [CompactIccSpace ι] [SeminormedAddGroup E] [NormedAddGroup F]
    {f : ι → E} {g : ι → F} {a : ι} (h : f =O[atTop] g) (hf : ContinuousOn f (Set.Ici a))
    (hg : ContinuousOn g (Set.Ici a)) (hg0 : ∀ x ∈ Set.Ici a, g x ≠ 0) :
    f =O[𝓟 (Set.Ici a)] g := by
  -- `eventually_atTop` needs a nonempty order
  have : Nonempty ι := ⟨a⟩
  obtain ⟨c₀, hc₀⟩ := h.bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hc₀
  have hcont : ContinuousOn (fun x ↦ ‖f x‖ / ‖g x‖) (Set.Icc a b) :=
    (hf.norm.div hg.norm fun x hx ↦ norm_ne_zero_iff.mpr (hg0 x hx)).mono
      Set.Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine isBigO_principal.mpr ⟨max c₀ B, fun x hx ↦ ?_⟩
  have hgx : 0 < ‖g x‖ := norm_pos_iff.mpr (hg0 x hx)
  rcases le_or_gt b x with hbx | hbx
  · exact (hb x hbx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgx.le)
  · have hBx := hB x ⟨hx, hbx.le⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hgx] at hBx
    exact hBx.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hgx.le)

/-- **A constant multiple of `ψ` is `o(ψ)` only if it vanishes.** If `ψ` is frequently nonzero
along `l`, then `ψ • c = o(ψ)` along `l` if and only if `c = 0`. -/
theorem isLittleO_smul_const_self_iff {α 𝕜 E : Type*} [NormedAddGroup 𝕜] [NormedAddGroup E]
    [SMul 𝕜 E] [NormSMulClass 𝕜 E] {l : Filter α} {ψ : α → 𝕜} {c : E}
    (hψ : ∃ᶠ x in l, ψ x ≠ 0) : (fun x => ψ x • c) =o[l] ψ ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun hc ↦ isLittleO_iff.mpr fun ε hε ↦ .of_forall fun x ↦ ?_⟩
  · by_contra hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    obtain ⟨x, hx, hψx⟩ := (hψ.and_eventually (h.def (half_pos hcpos))).exists
    rw [norm_smul] at hψx
    have hψpos : 0 < ‖ψ x‖ := norm_pos_iff.mpr hx
    nlinarith
  · rw [norm_smul, hc, norm_zero, mul_zero]
    positivity

/-- **A scalar function times a constant vector is big-O of the scalar function:**
`(fun x => u x • c) =O[l] u`, with constant `‖c‖`, whenever scalar multiplication satisfies
`‖r • c‖ ≤ ‖r‖ * ‖c‖` at `c`. This holds for every bounded action, by `norm_smul_le`. -/
theorem isBigO_smul_const_self {α 𝕜 E : Type*} [Norm 𝕜] [Norm E] [SMul 𝕜 E]
    {l : Filter α} (u : α → 𝕜) (c : E) (hc : ∀ r : 𝕜, ‖r • c‖ ≤ ‖r‖ * ‖c‖) :
    (fun x => u x • c) =O[l] u :=
  IsBigO.of_bound ‖c‖ (Eventually.of_forall fun x => (hc (u x)).trans_eq (mul_comm _ _))

/-- **An eventual `O((log x)⁻¹)` bound holds on a whole half-line `[a, ∞)` (`a > 1`).** If
`f = O((log x)⁻¹)` at `atTop` and `f` is bounded on every compact interval `[a, b]`, then there is
a constant `C ≥ 0` with `‖f x‖ ≤ C / log x` for all `x ≥ a`. Unlike `IsBigO.isBigO_principal_Ici`,
`(log x)⁻¹` tends to zero; unlike `IsBigO.isBigO_principal_Ici_of_continuousOn`, `f` need not be
continuous. -/
theorem IsBigO.exists_norm_le_div_log {E : Type*} [Norm E] {f : ℝ → E} {a : ℝ}
    (hO : f =O[atTop] fun x ↦ (Real.log x)⁻¹) (ha : 1 < a)
    (hbdd : ∀ b : ℝ, ∃ B : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, a ≤ x → ‖f x‖ ≤ C / Real.log x := by
  obtain ⟨c₀, hc₀⟩ := hO.bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hc₀
  obtain ⟨B, hB⟩ := hbdd b
  have hM0 : 0 ≤ max B 0 * max (Real.log b) 0 := by positivity
  refine ⟨max c₀ (max B 0 * max (Real.log b) 0), hM0.trans (le_max_right _ _), fun x hx ↦ ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (ha.trans_le hx)
  rcases le_or_gt b x with hbx | hbx
  · have hx' := hb x hbx
    rw [norm_inv, Real.norm_of_nonneg hlog.le, ← div_eq_mul_inv] at hx'
    exact hx'.trans (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le)
  · have hlog_le : Real.log x ≤ max (Real.log b) 0 :=
      (Real.log_le_log (zero_lt_one.trans (ha.trans_le hx)) hbx.le).trans (le_max_left _ _)
    rw [le_div_iff₀ hlog]
    exact (mul_le_mul ((hB x ⟨hx, hbx.le⟩).trans (le_max_left _ _)) hlog_le hlog.le
      (le_max_right _ _)).trans (le_max_right _ _)

end Asymptotics

namespace TauCeti

/-- For `|ρ| < 1`, the shifted polynomial-times-geometric sequence `(n + m)ᵏ ρⁿ` tends to `0`.
This is useful for absorbing polynomial growth after shifting an index. -/
theorem tendsto_add_pow_mul_pow_of_abs_lt_one (m k : ℕ) {ρ : ℝ} (hρ : |ρ| < 1) :
    Tendsto (fun n : ℕ ↦ (n + m : ℝ) ^ k * ρ ^ n) atTop (𝓝 0) := by
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · exact tendsto_const_nhds.congr' <| (eventually_ge_atTop 1).mono fun n hn ↦ by
      simp [zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  -- `(n + m)ᵏ ρⁿ = ρ⁻ᵐ (n + m)ᵏ ρⁿ⁺ᵐ`, a shift of Mathlib's unshifted limit
  have h := ((tendsto_pow_const_mul_const_pow_of_abs_lt_one k hρ).comp
    (tendsto_add_atTop_nat m)).const_mul (ρ⁻¹ ^ m)
  convert h using 1
  · ext n
    simp only [Function.comp_apply, Nat.cast_add, pow_add, inv_pow]
    field_simp
  · simp

/-- If the weighted terms `aₙ qⁿ` of a real sequence at a radius `q > 0` are bounded by `A`, then
at the radius `c` its weighted terms are bounded by `A * (|c| / q)ⁿ`. Applied to the coefficient
norms of a power series, this is the estimate behind every loss of radius. -/
theorem mul_abs_pow_le_of_forall_mul_pow_le {a : ℕ → ℝ} {q A c : ℝ} (hq : 0 < q)
    (hA : ∀ n, a n * q ^ n ≤ A) (n : ℕ) : a n * |c| ^ n ≤ A * (|c| / q) ^ n :=
  calc a n * |c| ^ n = a n * q ^ n * (|c| / q) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ A * (|c| / q) ^ n := by gcongr; exact hA n

/-- A map between pseudometric spaces satisfying the difference estimate of a strictly
differentiable map near `x`, `dist (u y) (u y') = O(dist y y')` near `(x, x)`, is continuous at
`x`. -/
theorem continuousAt_of_isBigO_dist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {u : X → Y} {x : X}
    (hu : (fun p : X × X ↦ dist (u p.1) (u p.2)) =O[𝓝 (x, x)] fun p ↦ dist p.1 p.2) :
    ContinuousAt u x := by
  have hpair : Tendsto (fun y : X ↦ (y, x)) (𝓝 x) (𝓝 (x, x)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact (hu.comp_tendsto hpair).trans_tendsto (tendsto_iff_dist_tendsto_zero.mp tendsto_id)

/-- In an ordered field, the ratio `(t + x) / (t + y)` of two translates of `t` tends to `1` as
`t → ∞`. -/
theorem tendsto_add_div_add_atTop {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] (x y : 𝕜) :
    Tendsto (fun t : 𝕜 ↦ (t + x) / (t + y)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := x - y)).div_atTop
    (tendsto_atTop_add_const_right atTop y tendsto_id)
  rw [show (1 : 𝕜) = 1 + 0 by simp]
  refine (h.const_add 1).congr' ?_
  filter_upwards [eventually_gt_atTop (-y)] with t ht
  have : t + y ≠ 0 := by linarith
  simp only [id]
  field_simp
  ring

end TauCeti
