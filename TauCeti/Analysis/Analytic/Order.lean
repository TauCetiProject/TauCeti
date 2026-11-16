/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The analytic order of products, power maps and derivatives

Extensions of Mathlib's analytic-order calculus: `analyticOrderNatAt` respects eventual equality,
the order is additive over finite products, composing with `q ↦ q ^ N` at `0` multiplies the order
by `N`, the power map `w ↦ w ^ m` recentred at `0` has order `m` there for `m ≠ 0`, the
recentred function `f · - f x` has order `1` at `x` exactly when `deriv f x ≠ 0`, and the order is
monotone under domination (`=O`), hence invariant under equivalence up to constant factors (`=Θ`)
and characterized by comparison with the powers `(z - z₀) ^ n`, and at a zero the divided
difference `dslope f a` has order one less than `f`. The order is finite at a point with a
punctured neighbourhood free of zeros, in particular wherever the zeros nearby are confined to a
finite set. The exponent `m` of a local factorization `(w - z) ^ m v w`, with `v` continuous and
nonzero at `z`, is unique, and multiplying an analytic function by a factor continuous and nonzero
at `z` keeps its order as that exponent. The finiteness of the zero set itself on a compact is
`AnalyticOnNhd.finite_setOf_mem_and_eq_zero_of_isCompact`, provided by
`TauCeti.Analysis.Analytic.IsolatedZeros`, which mentions no order.

## Main declarations

* `TauCeti.exists_analyticOrderAt_monomial_sub_eq_min`: outside at most two scalar
  coefficients, subtraction of a scalar monomial has the minimum of the two orders.
* `TauCeti.analyticOrderNatAt_congr`: eventual equality preserves the natural analytic order.
* `TauCeti.analyticOrderAt_prod`: the order of `∏ i ∈ s, F i` is `∑ i ∈ s`, of the orders.
* `TauCeti.analyticOrderAt_comp_pow_zero`: the order of `q ↦ f (q ^ N)` at `0` is `N` times
  the order of `f` at `0`.
* `TauCeti.analyticOrderAt_pow_sub_zero_pow`: the order of `w ↦ w ^ m - 0 ^ m` at `0` is `m`
  for `m ≠ 0`.
* `AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero`: `f · - f x` has order `1` at `x`
  exactly when `deriv f x ≠ 0`, the `iff` form of Mathlib's
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`.
* `AnalyticAt.analyticOrderAt_le_of_isBigO` and `AnalyticAt.analyticOrderAt_eq_of_isTheta`: an
  analytic function dominated by `f` vanishes to at least the order of `f`, so analytic functions
  equivalent up to constant factors have the same order.
* `AnalyticAt.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul`: a factorization
  `(z - z₀) ^ n • u z` with `u` continuous at `z₀` forces order at least `n`.
* `AnalyticAt.analyticOrderAt_eq_natCast_iff_isTheta` and
  `AnalyticAt.analyticOrderAt_eq_top_iff_forall_isBigO`: an analytic function has order `n`
  exactly when it is comparable to `(z - z₀) ^ n`, and infinite order exactly when it is
  `O((z - z₀) ^ n)` for every `n`.
* `TauCeti.isTheta_pow_sub_pow_sub_iff`: powers of `z - z₀` of different exponents are not
  comparable near `z₀`.
* `AnalyticAt.analyticOrderAt_dslope_add_one`: at a zero `a` of `f`, the divided difference
  `dslope f a` has order one less than `f` at `a`.
* `TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero`: a function with no zero in a punctured
  ball has finite order at its centre.
* `TauCeti.analyticOrderAt_ne_top_of_zeros_subset`: if the zeros in an open set `U` lie in a
  finite set, the order is finite at every point of `U`.
* `TauCeti.eq_of_eventually_sub_pow_mul_eq`: the exponent of a local factorization
  `(w - z) ^ m v w`, with `v` continuous and nonzero at `z`, is unique.
* `TauCeti.exists_eventually_mul_eq_sub_pow_mul`, `TauCeti.eq_of_eventually_mul_eq_sub_pow_mul`:
  for `Φ` continuous and nonzero at `z` and `σ` analytic of order `n` at `z`, `Φ σ` factors with
  exponent `n`, and every such factorization has exponent `n`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft from which this file ports the eventual-equality,
  product, power-map and derivative lemmas onto the current Mathlib pin.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {z₀ : 𝕜}

/-- Functions that agree near a point have the same natural analytic order there. -/
theorem analyticOrderNatAt_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderNatAt f z₀ = analyticOrderNatAt g z₀ := by
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hfg]

/-- The order is additive when taking a finite product of analytic functions. -/
theorem analyticOrderAt_prod {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜}
    (hF : ∀ i ∈ s, AnalyticAt 𝕜 (F i) z₀) :
    analyticOrderAt (∏ i ∈ s, F i) z₀ = ∑ i ∈ s, analyticOrderAt (F i) z₀ := by
  induction s using Finset.cons_induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      analyticOrderAt_mul (hF a (Finset.mem_cons_self a s))
        (Finset.analyticAt_prod _ fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)),
      ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)]

/-- The analytic order of `q ↦ f (q ^ N)` at `0` is `N` times the analytic order of `f`
at `0`. -/
lemma analyticOrderAt_comp_pow_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) {N : ℕ} (hN : 0 < N) :
    analyticOrderAt (fun q : 𝕜 ↦ f (q ^ N)) 0 = analyticOrderAt f 0 * N := by
  set g : 𝕜 → 𝕜 := fun q ↦ q ^ N with hg_def
  have hzero : g 0 = 0 := zero_pow hN.ne'
  have h_sub_eq : (fun x : 𝕜 ↦ g x - 0) = (id : 𝕜 → 𝕜) ^ N := funext fun x ↦ by simp [hg_def]
  -- The composite is definitionally the power lambda; `show … from rfl` records the
  -- identification once so the composition rule applies.
  rw [show (fun q : 𝕜 ↦ f (q ^ N)) = f ∘ g from rfl,
    AnalyticAt.analyticOrderAt_comp (hzero.symm ▸ hf) (analyticAt_id.pow N), hzero, h_sub_eq,
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- The power map `w ↦ w ^ m`, recentred at `0`, has analytic order `m` at `0` when `m ≠ 0`. -/
theorem analyticOrderAt_pow_sub_zero_pow {m : ℕ} (hm : m ≠ 0) :
    analyticOrderAt (fun w : 𝕜 ↦ w ^ m - 0 ^ m) 0 = m := by
  have hpow : (fun w : 𝕜 ↦ w ^ m - 0 ^ m) = (· - 0) ^ m := funext fun w ↦ by simp [zero_pow hm]
  rw [hpow, analyticOrderAt_centeredMonomial]

/-- A function analytic at `x` has a simple zero of `f · - f x` at `x` exactly when its
derivative at `x` does not vanish: the `iff` form of Mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`. -/
theorem _root_.AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    analyticOrderAt (f · - f x) x = 1 ↔ deriv f x ≠ 0 := by
  refine ⟨fun h => ?_, hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero⟩
  obtain ⟨g, hg, hgx, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast (hf.sub analyticAt_const)).1
    (h.trans Nat.cast_one.symm)
  have hd : HasDerivAt f (g x) x := by
    have h1 := (HasDerivAt.fun_smul ((hasDerivAt_id x).sub_const x)
      hg.differentiableAt.hasDerivAt).add_const (f x)
    simp only [id_eq, sub_self, zero_smul, zero_add, one_smul] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hfg] with z hz
    simp only [pow_one, Pi.sub_apply] at hz
    simp [← hz]
  rwa [hd.deriv]

/-- A function analytic at `z₀` and dominated there by `f` vanishes to at least the order of `f`
at `z₀`. No analyticity of `f` is needed: a non-analytic `f` has order `0`. -/
theorem _root_.AnalyticAt.analyticOrderAt_le_of_isBigO {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → E} {g : 𝕜 → F}
    (hg : AnalyticAt 𝕜 g z₀) (hgf : g =O[𝓝 z₀] f) :
    analyticOrderAt f z₀ ≤ analyticOrderAt g z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  swap
  · simp [analyticOrderAt_of_not_analyticAt hf]
  by_cases hftop : analyticOrderAt f z₀ = ⊤
  · -- a function dominated by one vanishing near `z₀` vanishes near `z₀`
    rw [hftop, top_le_iff, analyticOrderAt_eq_top]
    exact Asymptotics.isBigO_zero_right_iff.1
      (hgf.trans_eventuallyEq (analyticOrderAt_eq_top.1 hftop))
  by_cases hgtop : analyticOrderAt g z₀ = ⊤
  · simp [hgtop]
  rw [← Nat.cast_analyticOrderNatAt hftop, ← Nat.cast_analyticOrderNatAt hgtop, Nat.cast_le]
  by_contra! hlt
  -- otherwise `(z - z₀) ^ b`, for `b` the order of `g`, would be negligible compared to itself
  have hpow : (fun z => (z - z₀) ^ analyticOrderNatAt f z₀) =o[𝓝 z₀]
      fun z => (z - z₀) ^ analyticOrderNatAt g z₀ :=
    Asymptotics.isLittleO_norm_norm.1 <| by
      simpa only [norm_pow] using Asymptotics.isLittleO_pow_sub_pow_sub z₀ hlt
  refine Asymptotics.isLittleO_irrefl' ?_ <|
    ((hg.isTheta_pow_sub hgtop).symm.isBigO.trans hgf).trans_isLittleO
      ((hf.isTheta_pow_sub hftop).isBigO.trans_isLittleO hpow)
  exact ((eventually_nhdsWithin_of_forall (s := {z₀}ᶜ) fun z hz =>
    norm_ne_zero_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hz))).frequently).filter_mono
      nhdsWithin_le_nhds

/-- A function analytic at `z₀` that factors near `z₀` as `(z - z₀) ^ n • u z`, with `u` only
continuous at `z₀`, vanishes to order at least `n` there. Mathlib's `natCast_le_analyticOrderAt`
characterizes the order by such factorizations with an analytic factor `u`. -/
theorem _root_.AnalyticAt.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g u : 𝕜 → E} {n : ℕ} (hg : AnalyticAt 𝕜 g z₀)
    (hu : ContinuousAt u z₀) (h : ∀ᶠ z in 𝓝 z₀, g z = (z - z₀) ^ n • u z) :
    (n : ℕ∞) ≤ analyticOrderAt g z₀ := by
  have hO : g =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n :=
    Asymptotics.IsBigO.congr' (by
      simpa only [smul_eq_mul, mul_one] using
        (Asymptotics.isBigO_refl (fun z ↦ (z - z₀) ^ n) (𝓝 z₀)).smul
          (hu.norm.isBoundedUnder_le.isBigO_one 𝕜 (f := u)))
      (h.mono fun z hz ↦ hz.symm) EventuallyEq.rfl
  have hle := hg.analyticOrderAt_le_of_isBigO hO
  rwa [← Pi.pow_def, analyticOrderAt_centeredMonomial] at hle

/-- Two functions analytic at `z₀` that are equivalent up to constant factors near `z₀` vanish to
the same order there. -/
theorem _root_.AnalyticAt.analyticOrderAt_eq_of_isTheta {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → E} {g : 𝕜 → F}
    (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) (hfg : f =Θ[𝓝 z₀] g) :
    analyticOrderAt f z₀ = analyticOrderAt g z₀ :=
  le_antisymm (hg.analyticOrderAt_le_of_isBigO hfg.2) (hf.analyticOrderAt_le_of_isBigO hfg.isBigO)

/-- A function analytic at `z₀` has order `n` there exactly when its size is comparable to
`‖z - z₀‖ ^ n` near `z₀`. -/
theorem _root_.AnalyticAt.analyticOrderAt_eq_natCast_iff_isTheta {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    analyticOrderAt f z₀ = n ↔ f =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have htop : analyticOrderAt f z₀ ≠ ⊤ := by simp [h]
    have hn : analyticOrderNatAt f z₀ = n := by
      exact_mod_cast (Nat.cast_analyticOrderNatAt htop).trans h
    simpa [hn] using hf.isTheta_pow_sub htop
  · rw [hf.analyticOrderAt_eq_of_isTheta (by fun_prop) h]
    exact analyticOrderAt_centeredMonomial

/-- A function analytic at `z₀` vanishes identically near `z₀` exactly when it is `O(‖z - z₀‖ⁿ)`
near `z₀` for every `n`. -/
theorem _root_.AnalyticAt.analyticOrderAt_eq_top_iff_forall_isBigO {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = ⊤ ↔ ∀ n : ℕ, f =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · have h0 : ∀ᶠ z in 𝓝 z₀, f z = 0 := analyticOrderAt_eq_top.1 h
    exact (Asymptotics.isBigO_zero _ _).congr' (h0.mono fun z hz ↦ hz.symm) EventuallyEq.rfl
  · refine ENat.eq_top_iff_forall_ge.2 fun n ↦ ?_
    have hn : analyticOrderAt (fun z ↦ (z - z₀) ^ n) z₀ = n := analyticOrderAt_centeredMonomial
    exact hn ▸ hf.analyticOrderAt_le_of_isBigO (h n)

/-- Powers of `z - z₀` of different exponents are not comparable near `z₀`. -/
theorem isTheta_pow_sub_pow_sub_iff {m n : ℕ} :
    ((fun z ↦ (z - z₀) ^ m) =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ n) ↔ m = n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Asymptotics.isTheta_refl _ _⟩
  exact_mod_cast ((analyticAt_id.sub analyticAt_const).pow m).analyticOrderAt_eq_natCast_iff_isTheta
    |>.2 h |>.symm.trans analyticOrderAt_centeredMonomial |>.symm

/-- At a zero `a` of an analytic function `f`, the divided difference `dslope f a` vanishes to
order one less than `f` at `a`. -/
theorem _root_.AnalyticAt.analyticOrderAt_dslope_add_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : 𝕜 → E} {a : 𝕜} (hf : AnalyticAt 𝕜 f a) (ha : f a = 0) :
    analyticOrderAt (dslope f a) a + 1 = analyticOrderAt f a := by
  have hfa : ((· - a) • dslope f a) = f := funext fun z ↦ sub_smul_dslope_of_zero ha z
  calc analyticOrderAt (dslope f a) a + 1
      = analyticOrderAt ((· - a) • dslope f a) a := by
        rw [analyticOrderAt_smul (by fun_prop) (hf.dslope a), analyticOrderAt_id_sub_const_self,
          add_comm]
    _ = analyticOrderAt f a := by rw [hfa]

/-- **A function with no zero off the centre does not vanish identically there.** If `f` is
nonzero at every point of an open ball of positive radius other than its centre `z₀`, then `f`
has finite analytic order at `z₀`.

Nothing is assumed about `f z₀`, which may or may not be zero, nor about analyticity of `f`. -/
theorem analyticOrderAt_ne_top_of_forall_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : 𝕜 → E} {ρ : ℝ} (hρ : 0 < ρ)
    (hzf : ∀ z ∈ Metric.ball z₀ ρ, z ≠ z₀ → f z ≠ 0) : analyticOrderAt f z₀ ≠ ⊤ := fun h ↦
  have hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
    eventually_nhdsWithin_iff.mpr <| mem_of_superset (Metric.ball_mem_nhds z₀ hρ) fun z hz ↦
      hzf z hz
  (hne.and (nhdsWithin_le_nhds (analyticOrderAt_eq_top.mp h))).exists.elim fun _ h ↦ h.1 h.2

/-- **A function whose zeros are confined to a finite set has finite order.** If every zero of `f`
in an open set `U` lies in a finite set `S`, then `f` does not vanish identically near any point
of `U`, so `analyticOrderAt f z₀ ≠ ⊤` there.

The point `z₀` itself is allowed to be a zero, indeed to lie in `S`. This is the finite-set form
of `TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero`. -/
theorem analyticOrderAt_ne_top_of_zeros_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {S : Finset 𝕜} (hU : IsOpen U) (hz : z₀ ∈ U)
    (hzeros : ∀ w ∈ U, f w = 0 → w ∈ S) : analyticOrderAt f z₀ ≠ ⊤ := by
  -- Deleting `z₀`, the finite set `S` is closed and misses `z₀`, so `U` minus it is an open
  -- neighbourhood of `z₀`; any ball inside it has no zero of `f` off its centre.
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (hU.inter (S.finite_toSet.sdiff (t := {z₀})).isClosed.isOpen_compl) z₀ ⟨hz, by simp⟩
  exact analyticOrderAt_ne_top_of_forall_ne_zero hρ fun w hw hwz hw0 ↦
    (hball hw).2 ⟨hzeros w (hball hw).1 hw0, hwz⟩

/-- The exponent of a local factorization `(w - z) ^ m * v w`, with `v` continuous and nonzero at
`z`, is unique. -/
theorem eq_of_eventually_sub_pow_mul_eq {z : 𝕜} {m n : ℕ} {u v : 𝕜 → 𝕜}
    (hu : ContinuousAt u z) (hu₀ : u z ≠ 0) (hv : ContinuousAt v z) (hv₀ : v z ≠ 0)
    (h : ∀ᶠ w in 𝓝 z, (w - z) ^ m * u w = (w - z) ^ n * v w) : m = n := by
  wlog hmn : m < n generalizing m n u v
  · rcases (not_lt.mp hmn).eq_or_lt with h' | h'
    · exact h'.symm
    · exact (this hv hv₀ hu hu₀ (h.mono fun w hw ↦ hw.symm) h').symm
  exfalso
  -- Off `z`, cancelling `(w - z) ^ m` gives `u w = (w - z) ^ (n - m) * v w`, which tends to `0`.
  have hlim : Tendsto (fun w ↦ (w - z) ^ (n - m) * v w) (𝓝[≠] z) (𝓝 (u z)) := by
    refine (hu.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw hwz
    apply mul_left_cancel₀ (pow_ne_zero m (sub_ne_zero.mpr hwz))
    rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn.le]
  have h0 : Tendsto (fun w ↦ (w - z) ^ (n - m) * v w) (𝓝[≠] z) (𝓝 0) := by
    have hc : ContinuousAt (fun w ↦ (w - z) ^ (n - m) * v w) z :=
      ((continuousAt_id.sub continuousAt_const).pow _).mul hv
    simpa [zero_pow (Nat.sub_ne_zero_of_lt hmn)] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hu₀ (tendsto_nhds_unique hlim h0)

/-- If `Φ` is continuous and nonzero at `z` and `σ` is analytic with a zero of order `n` at `z`,
then `Φ σ` factors near `z` as `(w - z) ^ n` times a function continuous and nonzero at `z`. -/
theorem exists_eventually_mul_eq_sub_pow_mul {Φ σ : 𝕜 → 𝕜} {z : 𝕜} {n : ℕ}
    (hΦ : ContinuousAt Φ z) (hΦ₀ : Φ z ≠ 0) (hσ : AnalyticAt 𝕜 σ z)
    (hn : analyticOrderAt σ z = n) :
    ∃ v : 𝕜 → 𝕜, ContinuousAt v z ∧ v z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, Φ w * σ w = (w - z) ^ n * v w := by
  obtain ⟨g, hg, hg₀, hgσ⟩ := hσ.analyticOrderAt_eq_natCast.mp hn
  refine ⟨fun w ↦ Φ w * g w, hΦ.mul hg.continuousAt, mul_ne_zero hΦ₀ hg₀, ?_⟩
  filter_upwards [hgσ] with w hw
  rw [hw, smul_eq_mul]
  ring

/-- The zero orders of `Φ σ` are those of `σ`: for `Φ` continuous and nonzero at `z` and `σ`
analytic with a zero of order `n` at `z`, every local factorization `Φ σ = (w - z) ^ m v`, with `v`
continuous and nonzero at `z`, has `m = n`. -/
theorem eq_of_eventually_mul_eq_sub_pow_mul {Φ σ v : 𝕜 → 𝕜} {z : 𝕜} {m n : ℕ}
    (hΦ : ContinuousAt Φ z) (hΦ₀ : Φ z ≠ 0) (hσ : AnalyticAt 𝕜 σ z)
    (hn : analyticOrderAt σ z = n) (hv : ContinuousAt v z) (hv₀ : v z ≠ 0)
    (h : ∀ᶠ w in 𝓝 z, Φ w * σ w = (w - z) ^ m * v w) : m = n := by
  obtain ⟨u, hu, hu₀, hσu⟩ := exists_eventually_mul_eq_sub_pow_mul hΦ hΦ₀ hσ hn
  exact eq_of_eventually_sub_pow_mul_eq hv hv₀ hu hu₀ <| by
    filter_upwards [h, hσu] with w hw hw'
    rw [← hw, hw']

end TauCeti

/-- Outside zero and at most one additional scalar, subtracting a function from
a scalar multiple of a monomial has order equal to the minimum of their orders. The
exceptional scalar accounts for cancellation when the two orders coincide. If `f` is not analytic
at `0` the difference is not either, and both orders are `0` by convention. -/
theorem TauCeti.exists_analyticOrderAt_monomial_sub_eq_min {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (N : ℕ) :
    ∃ b : 𝕜, ∀ c : 𝕜, c ≠ 0 → c ≠ b →
      analyticOrderAt (fun t ↦ c * t ^ N - f t) 0 = min (N : ℕ∞) (analyticOrderAt f 0) := by
  by_cases hf : AnalyticAt 𝕜 f 0
  swap
  · refine ⟨0, fun c _ _ ↦ ?_⟩
    have hd : ¬ AnalyticAt 𝕜 (fun t ↦ c * t ^ N - f t) 0 := fun h ↦ hf <|
      (((analyticAt_const (v := c)).mul (analyticAt_id.pow N)).sub h).congr
        (.of_forall fun t ↦ by simp)
    rw [analyticOrderAt_of_not_analyticAt hd, analyticOrderAt_of_not_analyticAt hf]
    simp
  have hmono (c : 𝕜) (hc : c ≠ 0) :
      analyticOrderAt (fun t : 𝕜 ↦ c * t ^ N) 0 = N := by
    apply (analyticAt_const.mul (analyticAt_id.pow N)).analyticOrderAt_eq_natCast.2
    exact ⟨fun _ ↦ c, analyticAt_const, hc, .of_forall fun t ↦ by
      simp [smul_eq_mul, mul_comm]⟩
  by_cases heq : analyticOrderAt f 0 = N
  · obtain ⟨g, hg, -, hfg⟩ := hf.analyticOrderAt_eq_natCast.1 heq
    refine ⟨g 0, fun c _ hcb ↦ ?_⟩
    rw [heq, min_self]
    apply ((analyticAt_const.mul (analyticAt_id.pow N)).sub hf).analyticOrderAt_eq_natCast.2
    refine ⟨fun t ↦ c - g t, analyticAt_const.sub hg, sub_ne_zero.2 hcb, ?_⟩
    filter_upwards [hfg] with t ht
    simp only [sub_zero, smul_eq_mul, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] at ht ⊢
    rw [ht]
    ring
  · refine ⟨0, fun c hc _ ↦ ?_⟩
    have hne : analyticOrderAt (fun t : 𝕜 ↦ c * t ^ N) 0 ≠ analyticOrderAt (-f) 0 := by
      simpa [hmono c hc] using Ne.symm heq
    have hsum := analyticOrderAt_add_of_ne hne
    rw [analyticOrderAt_neg, hmono c hc] at hsum
    simpa only [Pi.add_def, Pi.neg_def, sub_eq_add_neg] using hsum

end
