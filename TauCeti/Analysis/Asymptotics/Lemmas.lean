/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Elementary asymptotic criteria

General criteria that supplement Mathlib's asymptotics API, elementary estimates, and an
elementary limit of ratios.

For functions into a normed division ring, `f` satisfies `f = a g + o(g)` exactly when `f / g`
tends to `a`, provided `g` is eventually nonzero. This criterion converts little-o error estimates
into limits of normalized functions, and conversely recovers error estimates from ratio limits.
The quotient is right division: multiplication need not be commutative. For ordered fields,
the ratio formulation also supports order arguments.

If `(σ - a) • f(σ)` is bounded along a filter on a normed division ring `𝕜` that eventually
avoids `a`, then `f(σ) = O((σ - a)⁻¹)` along it. When the values of `f` lie in a seminormed group,
whose norm is continuous, a limit of `(σ - a) • f(σ)` gives this boundedness. Here `𝕜` acts on
the values of `f` by a multiplicative action with `‖c • x‖ ≤ ‖c‖ * ‖x‖`, as every bounded scalar
action preserving zero on a seminormed additive group does. On the real line, for `a = 1` and the
right-sided limit `σ → 1⁺`, this is the growth bound near `s = 1` of a Dedekind zeta function or
an `L`-series with a simple pole there, read off from the limit of `(s - 1) L(s)` along the real
axis.

A map `u` between pseudometric spaces with `dist (u y) (u x) = O(dist y x)` as `y → x` is
continuous at `x`. This estimate follows from the difference estimate
`dist (u y) (u y') = O(dist y y')` near `(x, x)` of a strictly differentiable map. Only distances
are used, not differentiability or any additive structure.

In a seminormed group the norm is at most one on a neighbourhood of the origin, so there a higher
power of the norm is dominated by any lower one. This is the comparison that lets a Taylor
remainder of one order be read as a remainder of a smaller order. In particular a map within
`O(‖x‖ ^ k)`, `k ≥ 1`, of the identity is itself `O(‖x‖)` at the origin.

A bound `‖g x‖ ≤ A / ‖x - c‖ ^ n` outside a ball about any centre `c` of a normed division ring
gives `g = O(x⁻¹ ^ n)` at infinity: the decay rate of an inverse power does not depend on the
centre.

A power bound `g = O(u ^ p)` survives the dilation `t ↦ x t` for `x > 0`, at infinity as well
as at `0+`. This is how rapid decay at infinity, `O(x ^ r)` for every `r`, passes to rescaled
functions such as the theta kernels of a lattice at a level. A bound `u n = O(n ^ r)` on a
sequence likewise passes to the step function `t ↦ u ⌊t⌋₊` as `O(t ^ r)`, since `⌊t⌋₊ ∼ t`;
this is how a bound on the partial sums of a sequence enters an integral against the partial-sum
step function.

On a set where a real function `g` is nonnegative, `f = O(g)` uniformly on the set means
`‖f x‖ ≤ c * g x` there for a constant `c`, with no norm on `g`. This is the form in which a big-O
hypothesis on a weight enters a pointwise estimate, such as the bound of a solution of a Volterra
integral equation by a multiple of its weight.

An eventual big-O bound at `atTop` is uniform on a whole half-line `[a, ∞)` of a linear order as
soon as it holds uniformly on every interval `[a, b]`. This is how an asymptotic estimate becomes
an explicit inequality valid at every point, which a summation argument can apply at infinitely
many points at once. The interval bounds hold when, on each interval `[a, b]`, the dominated
function is bounded and the norm of the dominating one is bounded below by a positive constant,
which may shrink as `b` grows. This holds when closed intervals are compact and both functions
take values in seminormed groups and are continuous on the half-line, where the norm of the
dominating function does not vanish: this covers exponentially decaying majorants such as
`exp (-p x)`. For the slowly decaying majorant `(log x)⁻¹` on `[a, ∞)` (`a > 1`), local
boundedness of `f` on compact intervals alone suffices, covering step functions such as summatory
functions.

If the weighted terms `aₙ qⁿ` of a real sequence are bounded by `A` at a radius `q > 0`, then at
a radius `c` they are bounded by `A * (|c| / q)ⁿ`. For `|c| < q` this geometric bound is the
estimate behind every loss of radius for power series.

In an ordered field, the ratio `(t + x) / (t + y)` of two translates tends to `1` as `t → ∞`. This
is the limit at infinity of antiderivatives built from such ratios, for example in elementary
evaluations of elliptic integrals.

A function `g` with `f x ‖g x‖` eventually bounded along a filter on which `f → ∞` tends to `0`.
For `f y = y` on the real line, a bound on `y ‖g y‖` for large `y` also bounds `y |Im g y|` when
`g` is complex-valued. These are the decay estimates read off along the imaginary axis from
resolvent-type functions, which are `O(1 / y)` there.

## Main results

* `Asymptotics.isLittleO_sub_mul_iff_tendsto_div`: `f - a g = o(g)` if and only if
  `f / g → a`, for an eventually nonzero `g`.
* `Asymptotics.isBigO_inv_sub_of_sub_smul_isBigO_one`: if `(σ - a) • f(σ) = O(1)` along a filter
  on which eventually `σ ≠ a`, for an action with `‖c • x‖ ≤ ‖c‖ * ‖x‖`, then
  `f(σ) = O((σ - a)⁻¹)` along it.
* `Asymptotics.isBigO_norm_pow_norm_pow_nhds_zero_of_le`: `‖x‖ ^ m = O(‖x‖ ^ n)` at the origin
  whenever `n ≤ m`.
* `Asymptotics.isBigO_norm_of_isBigO_sub_norm_pow`: `w x - x = O(‖x‖ ^ k)` at the origin with
  `k ≥ 1` implies `w x = O(‖x‖)` there.
* `Asymptotics.isBigO_inv_pow_cobounded_of_norm_le`: a bound `‖g x‖ ≤ A / ‖x - c‖ ^ n` for
  `‖x - c‖ > R` gives `g = O(x⁻¹ ^ n)` at infinity.
* `Asymptotics.IsBigO.comp_mul_left_rpow`: `g = O(u ^ p)` along `l` implies
  `g (x t) = O(t ^ p)` along any `l'` that `t ↦ x t` maps to `l` and that lies eventually in
  `(0, ∞)`, for `x > 0`.
* `Asymptotics.IsBigO.comp_natFloor_rpow`: `u n = O(n ^ r)` implies `u ⌊t⌋₊ = O(t ^ r)` as
  `t → ∞`.
* `Asymptotics.isLittleO_smul_const_self_iff`: if `‖ψ‖` is eventually nonnegative and frequently
  nonzero, `c` lies in a normed (not merely seminormed) additive group and scalar multiplication
  satisfies `‖r • c‖ = ‖r‖ * ‖c‖` at `c`, then `ψ • c = o(ψ)` if and only if `c = 0`.
* `Asymptotics.isBigO_smul_const_self`: `u • c = O(u)` for a scalar function `u` and a constant
  vector `c` with `‖r • c‖ ≤ ‖r‖ * ‖c‖` for every scalar `r`.
* `Asymptotics.isBigO_principal_iff_of_nonneg`: for `g ≥ 0` on `s`, `f = O(g)` on `s` if and
  only if `‖f x‖ ≤ c * g x` on `s` for some `c`.
* `Asymptotics.IsBigO.isBigO_principal_Ici_of_isBigO_principal_Icc`: `f = O(g)` at `atTop` and
  on every `[a, b]` gives `f = O(g)` on `[a, ∞)`.
* `Asymptotics.isBigO_inv_norm_smul_apply`: evaluating continuous linear maps `L a` at `x a` and
  dividing by `‖x a‖` gives `O(L)`.
* `Asymptotics.IsBigO.isBigO_principal_Ici`: `f = O(g)` at `atTop` gives `f = O(g)` on `[a, ∞)`
  when, on each `[a, b]`, `f` is bounded and `‖g‖` is bounded below by a positive constant.
* `Asymptotics.IsBigO.isBigO_principal_Ici_of_continuousOn`: the same conclusion when closed
  intervals are compact, `f` and `g` take values in seminormed groups and are continuous on
  `[a, ∞)`, and `‖g‖` does not vanish there.
* `Asymptotics.IsBigO.isBigO_principal_Ioc_of_continuousOn`: the counterpart at a left endpoint:
  `f = O(g)` as `x → a⁺` gives `f = O(g)` on `(a, b]` under the same continuity and nonvanishing
  hypotheses on `(a, b]`.
* `Asymptotics.IsBigO.exists_norm_le_div_log`: `f = O((log x)⁻¹)` at `atTop` gives a uniform bound
  `‖f x‖ ≤ C / log x` on `[a, ∞)` (`a > 1`) when `f` is bounded on each `[a, b]`.
* `TauCeti.mul_abs_pow_le_of_forall_mul_pow_le`: weighted terms bounded by `A` at a radius `q > 0`
  are bounded by `A * (|c| / q)ⁿ` at the radius `c`.
* `TauCeti.continuousAt_of_isBigO_dist`: `dist (u y) (u x) = O(dist y x)` as `y → x` implies
  continuity of `u` at `x`.
* `TauCeti.tendsto_add_div_add_atTop`: `(t + x) / (t + y) → 1` as `t → ∞`.
* `TauCeti.tendsto_zero_of_eventually_mul_norm_le`: `f x ‖g x‖ ≤ K` eventually along a filter on
  which `f → ∞` implies `g → 0`.
* `TauCeti.eventually_mul_abs_im_le_of_mul_norm_le`: an eventual bound on `y ‖f y‖` bounds
  `y |Im f y|`.

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

/-- **A bounded `(σ - a) • f(σ)` bounds `f` by `(σ - a)⁻¹`.** If `(σ - a) • f(σ) = O(1)` along a
filter `l` on a normed division ring `𝕜` on which eventually `σ ≠ a`, then `f(σ) = O((σ - a)⁻¹)`
along `l`. The boundedness holds in particular when the values of `f` lie in a seminormed group,
whose norm is continuous, and `(σ - a) • f(σ)` has a limit along `l` (`Filter.Tendsto.isBigO_one`).
The action of `𝕜` need only be a multiplicative action with `‖c • x‖ ≤ ‖c‖ * ‖x‖`, as
`norm_smul_le` gives for any bounded scalar action preserving zero (`SMulZeroClass`) on a
seminormed additive group. Typical choices of `l` are the one-sided and punctured
neighbourhoods of `a`. For `𝕜 = ℝ`, `a = 1` and `l = 𝓝[>] 1` this is how such a bound is
usually obtained for a Dedekind zeta function or an `L`-series near `s = 1`, from the limit of
`(s - 1) L(s)` along the real axis. -/
theorem isBigO_inv_sub_of_sub_smul_isBigO_one {𝕜 E : Type*} [NormedDivisionRing 𝕜] [Norm E]
    [MulAction 𝕜 E] (hb : ∀ (c : 𝕜) (x : E), ‖c • x‖ ≤ ‖c‖ * ‖x‖)
    {l : Filter 𝕜} {f : 𝕜 → E} {a : 𝕜} (hne : ∀ᶠ σ in l, σ ≠ a)
    (h : (fun σ ↦ (σ - a) • f σ) =O[l] fun _ ↦ (1 : ℝ)) :
    f =O[l] fun σ ↦ (σ - a)⁻¹ := by
  obtain ⟨C, hC⟩ := h.bound
  refine .of_bound C ?_
  filter_upwards [hne, hC] with σ hσ hCσ
  rw [norm_one, mul_one] at hCσ
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

/-- **A map within `O(‖x‖ ^ k)` of the identity is `O(‖x‖)` at the origin.** If
`w x - x = O(‖x‖ ^ k)` near `0` for some `k ≥ 1`, then `w x = O(‖x‖)` near `0`. -/
theorem isBigO_norm_of_isBigO_sub_norm_pow {E : Type*} [SeminormedAddCommGroup E] {w : E → E}
    {k : ℕ} (hk : 1 ≤ k) (hw : (fun x ↦ w x - x) =O[𝓝 0] fun x ↦ ‖x‖ ^ k) :
    w =O[𝓝 0] fun x ↦ ‖x‖ := by
  have hk1 : (fun x : E ↦ ‖x‖ ^ k) =O[𝓝 0] fun x ↦ ‖x‖ := by
    simpa using isBigO_norm_pow_norm_pow_nhds_zero_of_le (E := E) hk
  simpa using (hw.trans hk1).add (isBigO_norm_right.2 (isBigO_refl (fun x : E ↦ x) (𝓝 0)))

/-- **An inverse-power bound about any centre is a decay bound at infinity.** If
`‖g x‖ ≤ A / ‖x - c‖ ^ n` whenever `R < ‖x - c‖`, then `g = O(x⁻¹ ^ n)` along `cobounded 𝕜`. -/
theorem isBigO_inv_pow_cobounded_of_norm_le {𝕜 E : Type*} [NormedDivisionRing 𝕜] [Norm E]
    {g : 𝕜 → E} {c : 𝕜} {R A : ℝ} (n : ℕ)
    (hg : ∀ x, R < ‖x - c‖ → ‖g x‖ ≤ A / ‖x - c‖ ^ n) :
    g =O[Bornology.cobounded 𝕜] fun x ↦ x⁻¹ ^ n := by
  -- `g = O((x - c)⁻¹ ^ n)`, as `‖x - c‖ → ∞` and so `R < ‖x - c‖` eventually
  have hR : ∀ᶠ x in Bornology.cobounded 𝕜, R < ‖x - c‖ :=
    (tendsto_norm_cobounded_atTop.comp (tendsto_sub_const_cobounded c)).eventually_gt_atTop R
  have hgc : g =O[Bornology.cobounded 𝕜] fun x ↦ (x - c)⁻¹ ^ n :=
    .of_bound A <| hR.mono fun x hx ↦ by simpa [div_eq_mul_inv] using hg x hx
  -- `x - c ∼ x`, as the constant `c` is `o(x)` by Mathlib's
  -- `Asymptotics.isLittleO_const_id_cobounded`; hence `x = O(x - c)`
  have hx : (fun x : 𝕜 ↦ x) =O[Bornology.cobounded 𝕜] fun x ↦ x - c :=
    IsEquivalent.isBigO_symm <| (isLittleO_const_id_cobounded (-c)).congr_left fun x ↦ by simp
  exact hgc.trans ((hx.inv_rev ((Bornology.eventually_ne_cobounded 0).mono
    fun _ h h0 ↦ absurd h0 h)).pow n)

/-- **A power bound survives a dilation of the variable.** If `g = O(u ^ p)` along `l`, `x > 0`,
and `t ↦ x t` tends to `l` along a filter `l'` eventually in `(0, ∞)`, then `t ↦ g (x t)` is
`O(t ^ p)` along `l'`. For instance `l = l' = atTop`, or `l = l' = 𝓝[>] 0`. -/
theorem IsBigO.comp_mul_left_rpow {R : Type*} [Norm R] {l l' : Filter ℝ} {g : ℝ → R} {p x : ℝ}
    (hg : g =O[l] fun u ↦ u ^ p) (hx : 0 < x) (hl : Tendsto (x * ·) l' l)
    (hpos : ∀ᶠ t in l', 0 < t) : (fun t ↦ g (x * t)) =O[l'] fun t ↦ t ^ p := by
  refine (hg.comp_tendsto hl).trans (IsBigO.of_bound (x ^ p) (hpos.mono fun t ht ↦ ?_))
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.mul_rpow hx.le ht.le]
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx p)]

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

/-- **A big-O bound on a set by a nonnegative real function.** If `g ≥ 0` on `s`, then
`f = O(g)` on `s` exactly when `‖f x‖ ≤ c * g x` on `s` for some constant `c`. -/
theorem isBigO_principal_iff_of_nonneg {α E : Type*} [Norm E] {f : α → E} {g : α → ℝ}
    {s : Set α} (hg : ∀ x ∈ s, 0 ≤ g x) :
    f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * g x :=
  isBigO_principal.trans <| exists_congr fun _ ↦ forall₂_congr fun x hx ↦ by
    rw [Real.norm_of_nonneg (hg x hx)]

/-- **An eventual big-O bound holds on a whole half-line once it holds on its intervals.** If
`f = O(g)` at `atTop` and `f = O(g)` uniformly on every interval `[a, b]`, then `f = O(g)`
uniformly on `[a, ∞)`. The norms need not be nonnegative. -/
theorem IsBigO.isBigO_principal_Ici_of_isBigO_principal_Icc {ι E F : Type*} [LinearOrder ι]
    [Norm E] [Norm F] {f : ι → E} {g : ι → F} {a : ι} (h : f =O[atTop] g)
    (hI : ∀ b, f =O[𝓟 (Set.Icc a b)] g) :
    f =O[𝓟 (Set.Ici a)] g := by
  -- `eventually_atTop` needs a nonempty order
  have : Nonempty ι := ⟨a⟩
  -- the bound at `atTop` holds with a constant `c` on some tail `[b, ∞)`, and the bound on
  -- `[a, b]` with a constant `c'`
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hc
  obtain ⟨c', hc'⟩ := isBigO_principal.mp (hI b)
  have h₀ (x : ι) (hx : a ≤ x) : ‖f x‖ ≤ c * ‖g x‖ ∨ ‖f x‖ ≤ c' * ‖g x‖ :=
    (le_total b x).imp (hb x) fun hxb ↦ hc' x ⟨hx, hxb⟩
  -- the norms may be negative, so the constraint `‖f x‖ ≤ C * ‖g x‖` is a lower bound on `C`
  -- where `‖g x‖ > 0` and an upper bound where `‖g x‖ < 0`. Take for `C` the supremum of the
  -- set `L` of the lower bounds `‖f x‖ / ‖g x‖` and of `min c c'`, which `max c c'` bounds.
  set L := insert (min c c') ((fun x ↦ ‖f x‖ / ‖g x‖) '' {x | a ≤ x ∧ 0 < ‖g x‖})
  have hL : BddAbove L := by
    refine ⟨max c c', ?_⟩
    rintro _ (rfl | ⟨y, ⟨hy, hgy⟩, rfl⟩)
    · exact min_le_max
    · dsimp only
      rw [div_le_iff₀ hgy]
      rcases h₀ y hy with h | h
      · exact h.trans (by gcongr; exact le_max_left _ _)
      · exact h.trans (by gcongr; exact le_max_right _ _)
  refine isBigO_principal.mpr ⟨sSup L, fun x (hx : a ≤ x) ↦ ?_⟩
  rcases lt_or_ge 0 ‖g x‖ with hgx | hgx
  · rw [← div_le_iff₀ hgx]
    exact le_csSup hL (.inr ⟨x, ⟨hx, hgx⟩, rfl⟩)
  -- where `‖g x‖ ≤ 0`, every `s ∈ L` satisfies the constraint at `x`: `min c c'` by the choice
  -- of `c` and `c'`, and a lower bound from `y` as `x` and `y` share the constant on `[a, max x y]`
  have hs : ∀ s ∈ L, ‖f x‖ ≤ s * ‖g x‖ := by
    rintro _ (rfl | ⟨y, ⟨hy, hgy⟩, rfl⟩)
    · rcases h₀ x hx with h | h
      · exact h.trans (mul_le_mul_of_nonpos_right (min_le_left _ _) hgx)
      · exact h.trans (mul_le_mul_of_nonpos_right (min_le_right _ _) hgx)
    · obtain ⟨d, hd⟩ := isBigO_principal.mp (hI (max x y))
      exact (hd x ⟨hx, le_max_left _ _⟩).trans <| mul_le_mul_of_nonpos_right
        ((div_le_iff₀ hgy).mpr (hd y ⟨hy, le_max_right _ _⟩)) hgx
  rcases hgx.lt_or_eq with hgx | hgx
  · rw [← le_div_iff_of_neg hgx]
    exact csSup_le (Set.insert_nonempty _ _) fun s hs' ↦ (le_div_iff_of_neg hgx).mpr (hs s hs')
  · simpa [hgx] using hs _ (Set.mem_insert _ _)

/-- **An eventual big-O bound holds on a whole half-line.** If `f = O(g)` at `atTop` and, on
every interval `[a, b]`, `‖g‖` is bounded below by a positive constant and `f` is bounded, then
`f = O(g)` uniformly on `[a, ∞)`. The lower bound on `‖g‖` may depend on `b`, so `‖g‖` may tend
to zero. -/
theorem IsBigO.isBigO_principal_Ici {ι E F : Type*} [LinearOrder ι] [Norm E] [Norm F]
    {f : ι → E} {g : ι → F} {a : ι} (h : f =O[atTop] g)
    (hg : ∀ b, ∃ c > 0, ∀ x ∈ Set.Icc a b, c ≤ ‖g x‖)
    (hf : ∀ b, ∃ B, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) :
    f =O[𝓟 (Set.Ici a)] g := by
  -- on `[a, b]`, `‖f‖ ≤ B` and `‖g‖ ≥ c`
  refine h.isBigO_principal_Ici_of_isBigO_principal_Icc fun b ↦ ?_
  obtain ⟨c, hc, hgc⟩ := hg b
  obtain ⟨B, hB⟩ := hf b
  refine isBigO_principal.mpr ⟨max B 0 / c, fun x hx ↦ ?_⟩
  calc ‖f x‖ ≤ max B 0 := (hB x hx).trans (le_max_left _ _)
    _ ≤ max B 0 / c * ‖g x‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left (hgc x hx) (le_max_right _ _)

/-- **An eventual big-O bound holds on a whole half-line, continuous version.** In a linear
order whose closed intervals are compact, if `f = O(g)` at `atTop`, both functions take values in
seminormed groups and are continuous on `[a, ∞)`, and `‖g‖` does not vanish there, then
`f = O(g)` uniformly on `[a, ∞)`. The majorant `‖g‖` may tend to zero, as for an exponentially
decaying majorant. -/
theorem IsBigO.isBigO_principal_Ici_of_continuousOn {ι E F : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [CompactIccSpace ι] [SeminormedAddGroup E] [SeminormedAddGroup F]
    {f : ι → E} {g : ι → F} {a : ι} (h : f =O[atTop] g) (hf : ContinuousOn f (Set.Ici a))
    (hg : ContinuousOn g (Set.Ici a)) (hg0 : ∀ x ∈ Set.Ici a, ‖g x‖ ≠ 0) :
    f =O[𝓟 (Set.Ici a)] g := by
  -- on the compact `[a, b]`, the continuous positive `‖g‖` has a positive lower bound, and the
  -- continuous `f` is bounded
  exact h.isBigO_principal_Ici
    (fun b ↦ isCompact_Icc.exists_forall_le' (hg.norm.mono Set.Icc_subset_Ici_self)
      fun x hx ↦ (norm_nonneg _).lt_of_ne' (hg0 x hx.1))
    fun b ↦ isCompact_Icc.exists_bound_of_continuousOn (hf.mono Set.Icc_subset_Ici_self)

/-- **A big-O bound at `a⁺` holds on a whole interval `(a, b]`, continuous version.** In a
linear order with the order topology whose closed intervals are compact, if `f = O(g)` as
`x → a⁺`, both functions take values in seminormed groups and are continuous on `(a, b]`, and `‖g‖`
does not vanish there, then `f = O(g)` uniformly on `(a, b]`. This is the counterpart at a left
endpoint of `IsBigO.isBigO_principal_Ici_of_continuousOn`. -/
theorem IsBigO.isBigO_principal_Ioc_of_continuousOn {ι E F : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι] [SeminormedAddGroup E]
    [SeminormedAddGroup F] {f : ι → E} {g : ι → F} {a b : ι} (h : f =O[𝓝[>] a] g)
    (hf : ContinuousOn f (Set.Ioc a b)) (hg : ContinuousOn g (Set.Ioc a b))
    (hg0 : ∀ x ∈ Set.Ioc a b, ‖g x‖ ≠ 0) : f =O[𝓟 (Set.Ioc a b)] g := by
  rcases le_or_gt b a with hba | hab
  · simp only [Set.Ioc_eq_empty hba.not_gt, principal_empty, isBigO_bot]
  -- near `a` the bound holds on some `(a, u)`; on the compact `[u, b] ⊆ (a, b]` the continuous `f`
  -- is bounded and the continuous nonvanishing `‖g‖` is bounded below
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hab).mp hC
  have hK : Set.Icc u b ⊆ Set.Ioc a b := fun x hx ↦ ⟨lt_of_lt_of_le hu hx.1, hx.2⟩
  have hfar : f =O[𝓟 (Set.Icc u b)] g :=
    ((hf.mono hK).isBigO_principal isCompact_Icc (c := (1 : ℝ)) (by norm_num)).trans
      (((hg.norm.mono hK).isBigO_rev_principal isCompact_Icc (fun x hx ↦ hg0 x (hK hx))
        (1 : ℝ)).trans (IsBigO.of_bound' (Eventually.of_forall fun x ↦
          (Real.norm_of_nonneg (norm_nonneg (g x))).le)))
  obtain ⟨C', hC'⟩ := isBigO_principal.mp hfar
  refine isBigO_principal.mpr ⟨max C C', fun x hx ↦ ?_⟩
  rcases lt_or_ge x u with hxu | hux
  · exact (hsub ⟨hx.1, hxu⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (hC' x ⟨hux, hx.2⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- **A constant multiple of `ψ` is `o(ψ)` only if it vanishes.** If `‖ψ‖` is eventually
nonnegative and frequently nonzero along `l`, the vector `c` lies in a normed additive group, whose
norm vanishes only at `0` (a seminorm does not suffice), and scalar multiplication satisfies
`‖r • c‖ = ‖r‖ * ‖c‖` at `c` for every scalar `r`, then `ψ • c = o(ψ)` along `l` if and only if
`c = 0`. Eventual nonnegativity holds whenever `𝕜` is a seminormed additive group (by
`norm_nonneg`), and the norm identity holds for every action with `NormSMulClass` (by
`norm_smul`). -/
@[simp]
theorem isLittleO_smul_const_self_iff {α 𝕜 E : Type*} [Norm 𝕜] [NormedAddGroup E] [SMul 𝕜 E]
    {l : Filter α} {ψ : α → 𝕜} {c : E} (hψ₀ : ∀ᶠ x in l, 0 ≤ ‖ψ x‖)
    (hψ : ∃ᶠ x in l, ‖ψ x‖ ≠ 0) (hc : ∀ r : 𝕜, ‖r • c‖ = ‖r‖ * ‖c‖) :
    (fun x => ψ x • c) =o[l] ψ ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun hc₀ ↦ isLittleO_iff.mpr fun ε hε ↦ hψ₀.mono fun x hx ↦ ?_⟩
  · by_contra hc₀
    -- `‖ψ x • c‖ = ‖c‖ * ‖ψ x‖`, so `‖c‖ * ‖ψ‖ = o(ψ)`; cancelling the nonzero constant `‖c‖`
    -- gives `‖ψ‖ = o(‖ψ‖)`, impossible as `‖ψ‖` is frequently nonzero
    have h₁ : (fun x ↦ ‖c‖ * ‖ψ x‖) =o[l] ψ :=
      (IsBigOWith.of_bound (c := 1) (g := fun x ↦ ψ x • c) <| hψ₀.mono fun x hx ↦ by
        rw [one_mul, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hx), hc,
          mul_comm]).trans_isLittleO h one_pos
    exact isLittleO_irrefl' (hψ.mono fun x hx ↦ by simpa using hx)
      (((isLittleO_const_mul_left_iff (norm_ne_zero_iff.mpr hc₀)).mp h₁).trans_isBigO
        (isBigO_of_le l fun x ↦ Real.le_norm_self _))
  · rw [hc, hc₀, norm_zero, mul_zero]
    exact mul_nonneg hε.le hx

/-- **A scalar function times a constant vector is big-O of the scalar function:**
`(fun x => u x • c) =O[l] u`, with constant `‖c‖`, whenever scalar multiplication satisfies
`‖r • c‖ ≤ ‖r‖ * ‖c‖` at `c`. This holds for every bounded scalar action preserving zero
(`SMulZeroClass`) on seminormed additive groups, by `norm_smul_le`. -/
theorem isBigO_smul_const_self {α 𝕜 E : Type*} [Norm 𝕜] [Norm E] [SMul 𝕜 E]
    {l : Filter α} (u : α → 𝕜) (c : E) (hc : ∀ r : 𝕜, ‖r • c‖ ≤ ‖r‖ * ‖c‖) :
    (fun x => u x • c) =O[l] u :=
  IsBigO.of_bound ‖c‖ (Eventually.of_forall fun x => (hc (u x)).trans_eq (mul_comm _ _))

/-- **Evaluation at a unit vector is bounded by the operator norm.** For continuous linear maps
`L a` and vectors `x a`, `‖x a‖⁻¹ • L a (x a) = O(L)`, along any filter. -/
theorem isBigO_inv_norm_smul_apply {α E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (l : Filter α) (L : α → E →L[ℝ] F)
    (x : α → E) : (fun a ↦ ‖x a‖⁻¹ • L a (x a)) =O[l] L := by
  refine IsBigO.of_bound' (Eventually.of_forall fun a ↦ ?_)
  rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) ((L a).le_opNorm (x a))

/-- **An eventual `O((log x)⁻¹)` bound holds on a whole half-line `[a, ∞)` (`a > 1`).** If
`f = O((log x)⁻¹)` at `atTop` and `f` is bounded on every compact interval `[a, b]`, then there is
a constant `C ≥ 0` with `‖f x‖ ≤ C / log x` for all `x ≥ a`. Unlike
`IsBigO.isBigO_principal_Ici_of_continuousOn`, `f` need not be continuous. -/
theorem IsBigO.exists_norm_le_div_log {E : Type*} [Norm E] {f : ℝ → E} {a : ℝ}
    (hO : f =O[atTop] fun x ↦ (Real.log x)⁻¹) (ha : 1 < a)
    (hbdd : ∀ b : ℝ, ∃ B : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, a ≤ x → ‖f x‖ ≤ C / Real.log x := by
  have hlog {x : ℝ} (hx : a ≤ x) : 0 < Real.log x := Real.log_pos (ha.trans_le hx)
  -- on `[a, b]`, `(log x)⁻¹ ≥ (log (max a b))⁻¹ > 0`, as `log` is increasing
  have hO' : f =O[𝓟 (Set.Ici a)] fun x ↦ (Real.log x)⁻¹ := by
    refine hO.isBigO_principal_Ici (fun b ↦ ⟨(Real.log (max a b))⁻¹,
      inv_pos.mpr (hlog (le_max_left a b)), fun x hx ↦ ?_⟩) hbdd
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (hlog hx.1).le)]
    exact inv_anti₀ (hlog hx.1) (Real.log_le_log (zero_lt_one.trans (ha.trans_le hx.1))
      (hx.2.trans (le_max_right a b)))
  obtain ⟨C, hC0, hC⟩ := hO'.exists_pos
  refine ⟨C, hC0.le, fun x hx ↦ ?_⟩
  simpa [norm_inv, Real.norm_of_nonneg (hlog hx).le, div_eq_mul_inv] using
    isBigOWith_principal.mp hC x hx

end Asymptotics

namespace TauCeti

/-- If the weighted terms `aₙ qⁿ` of a real sequence at a radius `q > 0` are bounded by `A`, then
at the radius `c` its weighted terms are bounded by `A * (|c| / q)ⁿ`. Applied to the coefficient
norms of a power series, this is the estimate behind every loss of radius. -/
theorem mul_abs_pow_le_of_forall_mul_pow_le {a : ℕ → ℝ} {q A c : ℝ} (hq : 0 < q)
    (hA : ∀ n, a n * q ^ n ≤ A) (n : ℕ) : a n * |c| ^ n ≤ A * (|c| / q) ^ n :=
  calc a n * |c| ^ n = a n * q ^ n * (|c| / q) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ A * (|c| / q) ^ n := by gcongr; exact hA n

/-- A map between pseudometric spaces with `dist (u y) (u x) = O(dist y x)` as `y → x` is
continuous at `x`. The difference estimate `dist (u y) (u y') = O(dist y y')` near `(x, x)` of a
strictly differentiable map gives this estimate by fixing `y' = x`. -/
theorem continuousAt_of_isBigO_dist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {u : X → Y} {x : X} (hu : (fun y ↦ dist (u y) (u x)) =O[𝓝 x] fun y ↦ dist y x) :
    ContinuousAt u x := by
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact hu.trans_tendsto (tendsto_iff_dist_tendsto_zero.mp tendsto_id)

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

/-- If `f x ‖g x‖` is eventually bounded along a filter on which `f` tends to infinity, then `g`
tends to `0`. -/
theorem tendsto_zero_of_eventually_mul_norm_le {α E : Type*} [SeminormedAddCommGroup E]
    {l : Filter α} {f : α → ℝ} {g : α → E} {K : ℝ} (hf : Tendsto f l atTop)
    (h : ∀ᶠ x in l, f x * ‖g x‖ ≤ K) : Tendsto g l (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x ↦ K / f x) ?_ (tendsto_const_nhds.div_atTop hf)
  filter_upwards [h, hf.eventually_gt_atTop 0] with x hx hx0
  rw [le_div_iff₀ hx0, mul_comm]
  exact hx

/-- A bound on `y ‖f y‖` for large `y` bounds `y |Im f y|`. -/
theorem eventually_mul_abs_im_le_of_mul_norm_le {f : ℝ → ℂ} {C : ℝ}
    (h : ∀ᶠ y : ℝ in atTop, y * ‖f y‖ ≤ C) : ∀ᶠ y : ℝ in atTop, y * |(f y).im| ≤ C := by
  filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
  exact (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hy0.le).trans hy

end TauCeti
