/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Meromorphic order from limits, bounds and connected sets

A nonzero limit of `(z - c) • f z` at `c` detects an exact simple pole of `f`.
A function bounded on a punctured neighbourhood has nonnegative meromorphic order.
An analytic function on a connected set that is nonzero somewhere has finite meromorphic
order throughout the set.

On a nonempty closed disc `closedBall c R` over `ℝ` or `ℂ` (`RCLike 𝕜`), the boundary point
`c + R` lies on `sphere c R` and `closedBall c R` is convex, hence preconnected. Consequently,
if a meromorphic function on `closedBall c R` has finite meromorphic order at every point of
`sphere c R` — in particular, if an analytic function on `closedBall c R` does not vanish on
`sphere c R` — then `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates finite
meromorphic order to every point of `closedBall c R`.

## Main results

* `MeromorphicAt.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul`: a nonzero residue limit
  forces meromorphic order exactly `-1`.
* `Filter.BoundedAtFilter.meromorphicOrderAt_nonneg`: boundedness on a punctured neighbourhood
  forces nonnegative meromorphic order.
* `exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero`: a negative meromorphic order is `-(m + 1)`
  for some `m : ℕ`.
* `AnalyticOnNhd.meromorphicOrderAt_ne_top_of_exists_ne_zero`: a nonzero value on a connected
  set rules out infinite order throughout the set.
* `AnalyticAt.meromorphicOrderAt_pos_iff_eq_zero`: an analytic function at `x` has positive
  meromorphic order at `x` if and only if `f x = 0`.
* `MeromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere`: finite meromorphic order on the
  bounding sphere propagates throughout the closed disc.
* `AnalyticOnNhd.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero`: an analytic function on
  a closed disc that does not vanish on the bounding sphere has finite meromorphic order throughout
  the closed disc.
* `DifferentiableOn.neg_one_le_meromorphicOrderAt`: a function differentiable off a closed set of
  at-worst-simple poles has meromorphic order at least `-1` throughout an open set.
* `AnalyticAt.meromorphicOrderAt_nonpos_iff`: at a point of analyticity the order is at most `0`
  exactly when the value is nonzero.
* `AnalyticAt.meromorphicOrderAt_fun_sub_nonneg_iff`: subtracting `F` from a function analytic at
  `x` leaves `x` a pole exactly when it is a pole of `F`.
* `MeromorphicAt.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top`: a meromorphic scalar factor
  that does not vanish identically does not change whether a function is meromorphic.
* `MeromorphicAt.meromorphicOrderAt_smul_nonpos`,
  `MeromorphicAt.meromorphicOrderAt_smul_nonpos_iff`: when `g • f` has order at most `0`, in terms
  of `g` and `f`.
* `MeromorphicAt.meromorphicOrderAt_smul_of_meromorphicOrderAt_eq_zero`: a meromorphic scalar
  factor of order `0` does not change the order.
* `MeromorphicAt.meromorphicAt_mul_iff_of_meromorphicOrderAt_ne_top`,
  `MeromorphicAt.meromorphicOrderAt_mul_nonpos`, `MeromorphicAt.meromorphicOrderAt_mul_nonpos_iff`,
  `MeromorphicAt.meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero`: the same for a product of
  scalar functions.
* `le_meromorphicOrderAt_sum`: a common lower bound on the orders of finitely many meromorphic
  summands bounds the order of their sum.
-/

public section

/-- An analytic function on a connected set has finite meromorphic order everywhere
on that set if it is nonzero at some point of the set. -/
theorem AnalyticOnNhd.meromorphicOrderAt_ne_top_of_exists_ne_zero
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set 𝕜} {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U)
    (h0 : ∃ z ∈ U, f z ≠ 0) {z : 𝕜} (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
  have hfin := (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hU).mp
  have hex : ∃ z : U, meromorphicOrderAt f z ≠ ⊤ := by
    obtain ⟨z, hz, hzero⟩ := h0
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [(hf z hz).meromorphicOrderAt_eq, (hf z hz).analyticOrderAt_eq_zero.mpr hzero]
    simp
  exact hfin hex ⟨z, hz⟩

/-- An analytic function at `x` has positive meromorphic order at `x` if and only if it vanishes
at `x` (including when it vanishes identically near `x`, where the order is `⊤`). -/
@[simp]
theorem AnalyticAt.meromorphicOrderAt_pos_iff_eq_zero
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    0 < meromorphicOrderAt f x ↔ f x = 0 := by
  rw [lt_iff_le_and_ne, and_iff_right hf.meromorphicOrderAt_nonneg, ne_comm,
    hf.meromorphicOrderAt_eq, ← hf.analyticOrderAt_ne_zero]
  cases analyticOrderAt f x <;> simp

open Filter Metric Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- A meromorphic function has an exact simple pole if multiplying by the displacement from
that point gives a nonzero punctured limit. -/
theorem MeromorphicAt.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (hf : MeromorphicAt f c) {a : E} (ha : a ≠ 0)
    (hlim : Tendsto (fun z ↦ (z - c) • f z) (𝓝[≠] c) (𝓝 a)) :
    meromorphicOrderAt f c = (-1 : ℤ) := by
  have hm : MeromorphicAt (fun z : 𝕜 ↦ z - c) c := by fun_prop
  have h := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hm.smul hf)).mp
    ⟨a, ha, hlim⟩
  rw [meromorphicOrderAt_smul hm hf, meromorphicOrderAt_id_sub_const] at h
  exact (WithTop.add_left_inj (by simp : (1 : WithTop ℤ) ≠ ⊤)).mp
    (h.trans (by norm_num : (0 : WithTop ℤ) = 1 + (-1 : ℤ)))

/-- If `f` is meromorphic on `closedBall c R` and has finite meromorphic order at every point of
the bounding sphere `sphere c R`, then `f` has finite meromorphic order throughout
`closedBall c R`. -/
theorem MeromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere
    (hf : MeromorphicOn f (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, meromorphicOrderAt f ζ ≠ ⊤)
    {z : 𝕜} (hz : z ∈ closedBall c R) : meromorphicOrderAt f z ≠ ⊤ := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.1 hz)
  have hmem : c + (R : 𝕜) ∈ sphere c R := by simp [abs_of_nonneg hR]
  exact hf.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (sphere_subset_closedBall hmem) hz (hsphere _ hmem)

/-- If `f` is analytic on `closedBall c R` and nonvanishing on the bounding sphere `sphere c R`,
then `f` has finite meromorphic order throughout `closedBall c R`. -/
theorem AnalyticOnNhd.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero
    (hf : AnalyticOnNhd 𝕜 f (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, f ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) : meromorphicOrderAt f z ≠ ⊤ :=
  hf.meromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere
    (fun ζ hζ ↦ by
      rw [(hf ζ (sphere_subset_closedBall hζ)).meromorphicOrderAt_eq,
        (hf ζ (sphere_subset_closedBall hζ)).analyticOrderAt_eq_zero.2 (hsphere ζ hζ)]
      exact WithTop.zero_ne_top) hz

/-- **Simple poles on an open set.** If `f` is complex differentiable on `U \ S` for a closed set
`S`, and has meromorphic order at least `-1` at each point of `S` in `U`, then it has order at
least `-1` at every point of the open set `U`: at points off `S` by analyticity. -/
theorem DifferentiableOn.neg_one_le_meromorphicOrderAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {U S : Set ℂ} (hU : IsOpen U)
    (hS : IsClosed S) (hf : DifferentiableOn ℂ f (U \ S))
    (h_simple : ∀ s ∈ S, s ∈ U → ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ∀ w ∈ U, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f w := by
  intro w hw
  by_cases hwS : w ∈ S
  · exact h_simple w hwS hw
  · have h_an : AnalyticAt ℂ f w := hf.analyticOnNhd (hU.sdiff hS) w ⟨hw, hwS⟩
    exact le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
      h_an.meromorphicOrderAt_nonneg

section Bounded

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {g : 𝕜 → E} {x : 𝕜}

/-- A function which is bounded on a punctured neighbourhood of `x` has nonnegative meromorphic
order at `x`. -/
theorem _root_.Filter.BoundedAtFilter.meromorphicOrderAt_nonneg
    (hbdd : BoundedAtFilter (𝓝[≠] x) g) :
    0 ≤ meromorphicOrderAt g x := by
  by_contra hlt
  exact Filter.not_isBoundedUnder_of_tendsto_atTop
    (tendsto_norm_atTop_iff_cobounded.mpr
      (tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.mp hlt)))
    ((Asymptotics.isBigO_one_iff (F := ℝ)).mp hbdd)

/-- A negative meromorphic order is `-(m + 1)` for some `m : ℕ`: this is the form of the pole
order taken by `Contour.exists_laurent_data_of_meromorphicOrderAt_eq_neg_succ`. -/
theorem exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero (h : meromorphicOrderAt g x < 0) :
    ∃ m : ℕ, meromorphicOrderAt g x = (-(↑(m + 1) : ℤ) : WithTop ℤ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h.ne_top
  have hn' : n < 0 := WithTop.coe_lt_coe.mp (hn ▸ h)
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hn'
  exact ⟨m, by simpa [Int.negSucc_eq] using hn.symm⟩

end Bounded

section Mul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {g : 𝕜 → 𝕜} {x : 𝕜}

/-- At a point where `f` is analytic, the order of `f` is at most `0` exactly when `f` does not
vanish there. -/
theorem AnalyticAt.meromorphicOrderAt_nonpos_iff (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x ≤ 0 ↔ f x ≠ 0 := by
  rw [← hf.analyticOrderAt_eq_zero, hf.meromorphicOrderAt_eq]
  induction analyticOrderAt f x using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- Subtracting `F` from a function analytic at `x` leaves `x` a pole exactly when it is a pole
of `F`. If `F` is not meromorphic at `x`, both orders are the junk value `0`. -/
theorem AnalyticAt.meromorphicOrderAt_fun_sub_nonneg_iff {P F : 𝕜 → E} {x : 𝕜}
    (hP : AnalyticAt 𝕜 P x) :
    0 ≤ meromorphicOrderAt (fun z ↦ P z - F z) x ↔ 0 ≤ meromorphicOrderAt F x := by
  have hsub : (fun z ↦ P z - F z) = P + fun z ↦ -F z := funext fun z ↦ sub_eq_add_neg _ _
  rw [hsub]
  constructor
  · intro h
    by_contra! hp
    have hlt : meromorphicOrderAt (fun z ↦ -F z) x < meromorphicOrderAt P x := by
      rw [← meromorphicOrderAt_fun_neg]
      exact hp.trans_le hP.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_add_eq_right_of_lt hP.meromorphicAt hlt,
      ← meromorphicOrderAt_fun_neg] at h
    exact h.not_gt hp
  · intro h
    by_cases hF : MeromorphicAt F x
    · refine (le_min hP.meromorphicOrderAt_nonneg ?_).trans
        (meromorphicOrderAt_add hP.meromorphicAt hF.fun_neg)
      rwa [← meromorphicOrderAt_fun_neg]
    · rw [meromorphicOrderAt_of_not_meromorphicAt fun hm ↦ hF ?_]
      convert hP.meromorphicAt.sub hm using 1
      funext z
      simp

/-- Multiplying by a scalar function `g` that is meromorphic at `x` and does not vanish identically
near `x` does not change whether a function is meromorphic at `x`. For `g` analytic and nonzero at
`x` this is Mathlib's `meromorphicAt_smul_iff_of_ne_zero`. -/
theorem MeromorphicAt.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top
    (hg : MeromorphicAt g x) (hg' : meromorphicOrderAt g x ≠ ⊤) :
    MeromorphicAt (g • f) x ↔ MeromorphicAt f x := by
  refine ⟨fun hgf => (hg.inv.smul hgf).congr ?_, hg.smul⟩
  filter_upwards [(meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq hg).1 hg'] with y hy
  rw [Pi.smul_apply', Pi.smul_apply', smul_smul, mul_comm]
  exact (congrArg (· • f y) hy).trans (one_smul 𝕜 (f y))

/-- The case of `MeromorphicAt.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top` for a product
of scalar functions. For `g` analytic and nonzero at `x` this is Mathlib's
`meromorphicAt_mul_iff_of_ne_zero`. -/
theorem MeromorphicAt.meromorphicAt_mul_iff_of_meromorphicOrderAt_ne_top {f : 𝕜 → 𝕜}
    (hg : MeromorphicAt g x) (hg' : meromorphicOrderAt g x ≠ ⊤) :
    MeromorphicAt (g * f) x ↔ MeromorphicAt f x :=
  hg.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top hg'

/-- Multiplying by a scalar function that is meromorphic of order `0` at `x` does not change the
order at `x`, whether or not the other factor is meromorphic there. For `g` analytic and nonzero
at `x` this is Mathlib's `meromorphicOrderAt_smul_of_ne_zero`; here the value of `g` at `x` is not
read. -/
theorem MeromorphicAt.meromorphicOrderAt_smul_of_meromorphicOrderAt_eq_zero
    (hg : MeromorphicAt g x) (hg0 : meromorphicOrderAt g x = 0) :
    meromorphicOrderAt (g • f) x = meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x
  · rw [meromorphicOrderAt_smul hg hf, hg0, zero_add]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt
      fun h => hf ((hg.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top
        (by rw [hg0]; exact WithTop.zero_ne_top)).1 h)]

/-- The case of `MeromorphicAt.meromorphicOrderAt_smul_of_meromorphicOrderAt_eq_zero` for a product
of scalar functions. For `g` analytic and nonzero at `x` this is Mathlib's
`meromorphicOrderAt_mul_of_ne_zero`. -/
theorem MeromorphicAt.meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero {f : 𝕜 → 𝕜}
    (hg : MeromorphicAt g x) (hg0 : meromorphicOrderAt g x = 0) :
    meromorphicOrderAt (g * f) x = meromorphicOrderAt f x :=
  hg.meromorphicOrderAt_smul_of_meromorphicOrderAt_eq_zero hg0

/-- If the scalar function `g` is meromorphic of order at most `0` at `x` and `f` has order at
most `0` at `x`, then `g • f` has order at most `0` at `x`. If `f` is not meromorphic at `x`,
neither is `g • f`, and its order is the junk value `0`. -/
theorem MeromorphicAt.meromorphicOrderAt_smul_nonpos (hg : MeromorphicAt g x)
    (hg0 : meromorphicOrderAt g x ≤ 0) (hf0 : meromorphicOrderAt f x ≤ 0) :
    meromorphicOrderAt (g • f) x ≤ 0 := by
  by_cases hf : MeromorphicAt f x
  · rw [meromorphicOrderAt_smul hg hf]
    exact add_nonpos hg0 hf0
  · rw [meromorphicOrderAt_of_not_meromorphicAt fun h =>
      hf ((hg.meromorphicAt_smul_iff_of_meromorphicOrderAt_ne_top
        (ne_top_of_le_ne_top WithTop.zero_ne_top hg0)).1 h)]

/-- The product of two scalar functions of order at most `0` at `x`, one of which is meromorphic
at `x`, has order at most `0` at `x`: the case of `MeromorphicAt.meromorphicOrderAt_smul_nonpos`
for scalar functions. -/
theorem MeromorphicAt.meromorphicOrderAt_mul_nonpos {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x)
    (hf0 : meromorphicOrderAt f x ≤ 0) (hg0 : meromorphicOrderAt g x ≤ 0) :
    meromorphicOrderAt (f * g) x ≤ 0 :=
  hf.meromorphicOrderAt_smul_nonpos hf0 hg0

/-- For a scalar function `g` and a function `f` meromorphic at `x`, such that a pole of either at
`x` is not a zero of the other, `g • f` has order at most `0` at `x` exactly when `g` and `f` both
do. The two conditions exclude the cancellation of a zero against a pole, as in
`(z - x)⁻¹ • (z - x)`. -/
theorem MeromorphicAt.meromorphicOrderAt_smul_nonpos_iff (hg : MeromorphicAt g x)
    (hf : MeromorphicAt f x)
    (hgf : meromorphicOrderAt g x < 0 → meromorphicOrderAt f x ≤ 0)
    (hfg : meromorphicOrderAt f x < 0 → meromorphicOrderAt g x ≤ 0) :
    meromorphicOrderAt (g • f) x ≤ 0 ↔
      meromorphicOrderAt g x ≤ 0 ∧ meromorphicOrderAt f x ≤ 0 := by
  refine ⟨fun h => ?_, fun h => hg.meromorphicOrderAt_smul_nonpos h.1 h.2⟩
  rw [meromorphicOrderAt_smul hg hf] at h
  rcases lt_or_ge (meromorphicOrderAt g x) 0 with hg0 | hg0
  · exact ⟨hg0.le, hgf hg0⟩
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with hf0 | hf0
  · exact ⟨hfg hf0, hf0.le⟩
  · exact ⟨(le_add_of_nonneg_right hf0).trans h, (le_add_of_nonneg_left hg0).trans h⟩

/-- The case of `MeromorphicAt.meromorphicOrderAt_smul_nonpos_iff` for a product of scalar
functions: for `f` and `g` meromorphic at `x`, such that a pole of either at `x` is not a zero of
the other, `f * g` has order at most `0` at `x` exactly when `f` and `g` both do. -/
theorem MeromorphicAt.meromorphicOrderAt_mul_nonpos_iff {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x)
    (hfg : meromorphicOrderAt f x < 0 → meromorphicOrderAt g x ≤ 0)
    (hgf : meromorphicOrderAt g x < 0 → meromorphicOrderAt f x ≤ 0) :
    meromorphicOrderAt (f * g) x ≤ 0 ↔
      meromorphicOrderAt f x ≤ 0 ∧ meromorphicOrderAt g x ≤ 0 :=
  hf.meromorphicOrderAt_smul_nonpos_iff hg hfg hgf

end Mul

section Sum

/-- A common lower bound on the meromorphic orders of the summands also bounds the order of
the sum from below. In particular, a finite sum cannot acquire a pole of higher order than
those of its summands. -/
theorem le_meromorphicOrderAt_sum {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Finset ι} {f : ι → 𝕜 → E} {z : 𝕜}
    {m : WithTop ℤ} (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) z) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) z := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Pi.zero_def, meromorphicOrderAt_const]
    simp
  | cons i s hi ih =>
    have hf' j (hj : j ∈ s) := hf j (Finset.mem_cons_of_mem hj)
    rw [Finset.sum_cons]
    exact (le_min (hm i (Finset.mem_cons_self i s))
      (ih hf' fun j hj ↦ hm j (Finset.mem_cons_of_mem hj))).trans
        (meromorphicOrderAt_add (hf i (Finset.mem_cons_self i s)) (MeromorphicAt.sum hf'))

end Sum

end
