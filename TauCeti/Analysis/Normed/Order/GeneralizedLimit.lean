/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Pointwise

/-!
# Dilation-invariant generalized limits

A *generalized limit* on bounded real sequences is a positive linear functional `ω` on `ℕ →ᵇ ℝ`
which agrees with the ordinary limit on every convergent sequence. It is *dilation invariant*
when `ω (n ↦ f (n / k)) = ω f` for every `k ≥ 1`, with natural-number division. For `k = 2`
this is invariance under duplicating every entry, `(f₀, f₁, f₂, …) ↦ (f₀, f₀, f₁, f₁, …)`.
Dixmier traces `Tr_ω` are generalized limits of logarithmic means of singular values, and
dilation invariance of `ω` is the hypothesis making them additive.

Every generalized limit lies between `liminf` and `limsup`, ignores finitely many entries, and
is bounded by the supremum norm. Dilation-invariant generalized limits exist: the Hahn–Banach
theorem extends `0` from the zero subspace to a linear functional dominated by the sublinear
functional

`p f = inf_s limsup_n 𝔼 i, f (n / s i)`,

where `s` ranges over nonempty finite families of positive integers. Dilations commute,
`n / k / l = n / (k * l)`, so averaging over a product of two families shows that `p` is
subadditive, and the telescoping average over `1, k, …, k ^ (N - 1)` shows
`p (f - f.dilate k) ≤ 2 ‖f‖ / N` for every `N ≥ 1`. This is the Agnew–Morse argument for
extensions invariant under a commuting family of operators.

## Main definitions

* `TauCeti.GeneralizedLimit`: positive linear functionals on `ℕ →ᵇ ℝ` extending the limit.
* `TauCeti.GeneralizedLimit.IsDilationInvariant`: invariance under every dilation by `k ≥ 1`.

## Main results

* `TauCeti.GeneralizedLimit.map_of_tendsto`: a generalized limit of a convergent sequence is its
  limit.
* `TauCeti.GeneralizedLimit.liminf_le_apply`, `TauCeti.GeneralizedLimit.apply_le_limsup`:
  `liminf f ≤ ω f ≤ limsup f`.
* `TauCeti.GeneralizedLimit.map_eq_of_eventuallyEq`: eventually equal sequences have the same
  generalized limit.
* `TauCeti.GeneralizedLimit.abs_apply_le_norm`: `|ω f| ≤ ‖f‖`.
* `TauCeti.GeneralizedLimit.exists_isDilationInvariant`: a dilation-invariant generalized limit
  exists.

## References

* R. P. Agnew, A. P. Morse, *Extensions of linear functionals, with applications to limits,
  integrals, measures, and densities*, Ann. of Math. 39 (1938), 20–30.
* J. Dixmier, *Existence de traces non normales*, C. R. Acad. Sci. Paris Sér. A-B 262 (1966),
  A1107–A1108.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.β.
-/

public section

noncomputable section

open Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace TauCeti

/-- A generalized limit on bounded real sequences: a positive linear functional on `ℕ →ᵇ ℝ`
which agrees with the ordinary limit on every convergent sequence. -/
structure GeneralizedLimit extends (ℕ →ᵇ ℝ) →ₚ[ℝ] ℝ where
  /-- A generalized limit of a convergent sequence is its limit. -/
  map_of_tendsto' (f : ℕ →ᵇ ℝ) {c : ℝ} : Tendsto f atTop (𝓝 c) → toFun f = c

namespace GeneralizedLimit

instance : FunLike GeneralizedLimit (ℕ →ᵇ ℝ) ℝ where
  coe ω := ω.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass GeneralizedLimit ℝ (ℕ →ᵇ ℝ) ℝ where
  map_add ω := map_add ω.toPositiveLinearMap
  map_smulₛₗ ω := map_smul ω.toPositiveLinearMap

instance : OrderHomClass GeneralizedLimit (ℕ →ᵇ ℝ) ℝ where
  map_rel ω _ _ h := OrderHomClass.mono ω.toPositiveLinearMap h

/-- Two generalized limits are equal when they agree on every bounded sequence. -/
@[ext]
theorem ext {ω ω' : GeneralizedLimit} (h : ∀ f, ω f = ω' f) : ω = ω' :=
  DFunLike.ext ω ω' h

@[simp]
theorem coe_toPositiveLinearMap (ω : GeneralizedLimit) : ⇑ω.toPositiveLinearMap = ⇑ω :=
  (rfl)

/-- A generalized limit built from a linear functional which is nonnegative on nonnegative
sequences and agrees with the limit of every convergent sequence. -/
def mk₀ (φ : (ℕ →ᵇ ℝ) →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f)
    (hlim : ∀ (f : ℕ →ᵇ ℝ) {c : ℝ}, Tendsto f atTop (𝓝 c) → φ f = c) : GeneralizedLimit :=
  { PositiveLinearMap.mk₀ φ hφ with map_of_tendsto' := hlim }

@[simp]
theorem mk₀_apply (φ : (ℕ →ᵇ ℝ) →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f)
    (hlim : ∀ (f : ℕ →ᵇ ℝ) {c : ℝ}, Tendsto f atTop (𝓝 c) → φ f = c) (f : ℕ →ᵇ ℝ) :
    mk₀ φ hφ hlim f = φ f :=
  (rfl)

variable (ω : GeneralizedLimit)

/-- A generalized limit of a convergent sequence is its limit. -/
theorem map_of_tendsto {f : ℕ →ᵇ ℝ} {c : ℝ} (h : Tendsto f atTop (𝓝 c)) : ω f = c :=
  ω.map_of_tendsto' f h

/-- A generalized limit of a constant sequence is its value. -/
@[simp]
theorem map_const (c : ℝ) : ω (BoundedContinuousFunction.const ℕ c) = c :=
  ω.map_of_tendsto tendsto_const_nhds

/-- A generalized limit takes the value `1` at the constant sequence `1`. -/
@[simp]
theorem map_one : ω 1 = 1 :=
  ω.map_of_tendsto tendsto_const_nhds

/-- A generalized limit of a sequence which is eventually at most `c` is at most `c`. -/
theorem apply_le_of_eventually_le {f : ℕ →ᵇ ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, f n ≤ c) :
    ω f ≤ c := by
  -- Truncating `f` at `c` changes it only at finitely many places.
  set g := f ⊓ BoundedContinuousFunction.const ℕ c
  have hfg : ω f - ω g = 0 := by
    rw [← map_sub]
    exact ω.map_of_tendsto <| tendsto_const_nhds.congr' <| h.mono fun n hn ↦ by simp [g, hn]
  have hg : ω g ≤ c := by
    simpa using OrderHomClass.mono ω (inf_le_right : g ≤ BoundedContinuousFunction.const ℕ c)
  linarith

/-- A generalized limit of a sequence which is eventually at least `c` is at least `c`. -/
theorem le_apply_of_eventually_le {f : ℕ →ᵇ ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, c ≤ f n) :
    c ≤ ω f := by
  have := ω.apply_le_of_eventually_le (f := -f) (c := -c) (h.mono fun n hn ↦ by simpa using hn)
  simpa using this

/-- Eventually equal bounded sequences have the same generalized limit. -/
theorem map_eq_of_eventuallyEq {f g : ℕ →ᵇ ℝ} (h : ⇑f =ᶠ[atTop] ⇑g) : ω f = ω g := by
  rw [← sub_eq_zero, ← map_sub]
  exact ω.map_of_tendsto <| tendsto_const_nhds.congr' <| h.mono fun n hn ↦ by simp [hn]

/-- A generalized limit is at most the `limsup`. -/
theorem apply_le_limsup (f : ℕ →ᵇ ℝ) : ω f ≤ limsup f atTop := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ω.apply_le_of_eventually_le ?_
  exact (eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε)
    (isBoundedUnder_of ⟨‖f‖, f.apply_le_norm⟩)).mono fun _ ↦ le_of_lt

/-- A generalized limit is at least the `liminf`. -/
theorem liminf_le_apply (f : ℕ →ᵇ ℝ) : liminf f atTop ≤ ω f := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [← sub_le_iff_le_add]
  refine ω.le_apply_of_eventually_le ?_
  exact (eventually_lt_of_lt_liminf (sub_lt_self _ hε)
    (isBoundedUnder_of ⟨-‖f‖, f.neg_norm_le_apply⟩)).mono fun _ ↦ le_of_lt

/-- A generalized limit is bounded in absolute value by the supremum norm. -/
theorem abs_apply_le_norm (f : ℕ →ᵇ ℝ) : |ω f| ≤ ‖f‖ := by
  simpa using PositiveLinearMap.abs_apply_le_mul_norm ω (u := 1)
    (fun g n ↦ by simpa using g.apply_le_norm n) f

/-- A generalized limit is *dilation invariant* when `ω (f.dilate k) = ω f` for every bounded
sequence `f` and every `k ≥ 1`. -/
def IsDilationInvariant : Prop :=
  ∀ (f : ℕ →ᵇ ℝ) (k : ℕ), 0 < k → ω (f.dilate k) = ω f

variable {ω} in
/-- Unfolding lemma for `IsDilationInvariant`, used to prove that a generalized limit is dilation
invariant. -/
theorem isDilationInvariant_iff :
    ω.IsDilationInvariant ↔ ∀ (f : ℕ →ᵇ ℝ) (k : ℕ), 0 < k → ω (f.dilate k) = ω f :=
  Iff.rfl

variable {ω} in
/-- A dilation-invariant generalized limit is unchanged by the dilation by any `k ≥ 1`. -/
theorem IsDilationInvariant.map_dilate (hω : ω.IsDilationInvariant) (f : ℕ →ᵇ ℝ) {k : ℕ}
    (hk : 0 < k) : ω (f.dilate k) = ω f :=
  hω f k hk

section Existence

/-! ### Existence of dilation-invariant generalized limits -/

/-- The constants `c` bounding, eventually from above, the average of `f` over the dilations
by some nonempty finite family of positive integers. -/
private def dilationUpperBounds (f : ℕ → ℝ) : Set ℝ :=
  {c | ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (s : ι → ℕ), (∀ i, 0 < s i) ∧
    ∀ᶠ n in atTop, 𝔼 i, f (n / s i) ≤ c}

private theorem mem_dilationUpperBounds_of_eventually_le {f : ℕ → ℝ} {c : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ c) : c ∈ dilationUpperBounds f :=
  ⟨Unit, inferInstance, inferInstance, fun _ ↦ 1, fun _ ↦ one_pos, by simpa using h⟩

private theorem neg_norm_le_of_mem_dilationUpperBounds {f : ℕ →ᵇ ℝ} {c : ℝ}
    (hc : c ∈ dilationUpperBounds f) : -‖f‖ ≤ c := by
  obtain ⟨ι, _, _, s, -, h⟩ := hc
  obtain ⟨n, hn⟩ := h.exists
  exact (Finset.le_expect Finset.univ_nonempty fun i _ ↦ f.neg_norm_le_apply _).trans hn

private theorem add_mem_dilationUpperBounds {f g : ℕ → ℝ} {c d : ℝ}
    (hc : c ∈ dilationUpperBounds f) (hd : d ∈ dilationUpperBounds g) :
    c + d ∈ dilationUpperBounds (f + g) := by
  obtain ⟨ι, _, _, s, hs, hc⟩ := hc
  obtain ⟨κ, _, _, t, ht, hd⟩ := hd
  refine ⟨ι × κ, inferInstance, inferInstance, fun p ↦ s p.1 * t p.2,
    fun p ↦ mul_pos (hs p.1) (ht p.2), ?_⟩
  -- Each dilation by a positive integer tends to infinity, so the bounds hold for all dilations.
  filter_upwards [eventually_all.2 fun j ↦ (Nat.tendsto_div_const_atTop (ht j).ne').eventually hc,
    eventually_all.2 fun i ↦ (Nat.tendsto_div_const_atTop (hs i).ne').eventually hd] with n hc hd
  -- Average over `ι × κ` as an iterated average, over `κ` first for `f` and over `ι` for `g`.
  simp only [Pi.add_apply, Finset.expect_add_distrib, ← Finset.univ_product_univ,
    Finset.expect_product]
  rw [Finset.expect_comm]
  refine add_le_add (Finset.expect_le Finset.univ_nonempty fun j _ ↦ ?_)
    (Finset.expect_le Finset.univ_nonempty fun i _ ↦ ?_)
  · simpa [Nat.div_div_eq_div_mul, mul_comm] using hc j
  · simpa [Nat.div_div_eq_div_mul] using hd i

private theorem smul_mem_dilationUpperBounds {f : ℕ → ℝ} {c r : ℝ} (hr : 0 ≤ r)
    (hc : c ∈ dilationUpperBounds f) : r * c ∈ dilationUpperBounds (r • f) := by
  obtain ⟨ι, _, _, s, hs, hc⟩ := hc
  refine ⟨ι, inferInstance, inferInstance, s, hs, hc.mono fun n hn ↦ ?_⟩
  simpa [← Finset.mul_expect] using mul_le_mul_of_nonneg_left hn hr

/-- The average of `f - f.dilate k` over the dilations by `1, k, …, k ^ (N - 1)` telescopes to
`(f n - f (n / k ^ N)) / N`, so it is at most `2 ‖f‖ / N`. -/
private theorem two_mul_norm_div_mem_dilationUpperBounds (f : ℕ →ᵇ ℝ) (k N : ℕ) (hk : 0 < k)
    (hN : 0 < N) : 2 * ‖f‖ / N ∈ dilationUpperBounds ⇑(f - f.dilate k) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨Fin N, inferInstance, inferInstance, fun j ↦ k ^ (j : ℕ), fun j ↦ pow_pos hk _,
    Eventually.of_forall fun n ↦ ?_⟩
  have hsum : ∑ j : Fin N, (f - f.dilate k) (n / k ^ (j : ℕ)) = f n - f (n / k ^ N) := by
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
      BoundedContinuousFunction.dilate_apply, Nat.div_div_eq_div_mul, ← pow_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ f (n / k ^ j) - f (n / k ^ (j + 1))),
      Finset.sum_range_sub']
    simp
  rw [Fintype.expect_eq_sum_div_card, hsum, Fintype.card_fin]
  gcongr
  linarith [f.apply_le_norm n, f.neg_norm_le_apply (n / k ^ N)]

/-- The sublinear functional dominating the extension: the infimum of the eventual upper bounds
of the averages of `f` over finitely many dilations. -/
private def dilationUpperBound (f : ℕ →ᵇ ℝ) : ℝ :=
  sInf (dilationUpperBounds f)

private theorem bddBelow_dilationUpperBounds (f : ℕ →ᵇ ℝ) :
    BddBelow (dilationUpperBounds f) :=
  ⟨-‖f‖, fun _ ↦ neg_norm_le_of_mem_dilationUpperBounds⟩

private theorem nonempty_dilationUpperBounds (f : ℕ →ᵇ ℝ) :
    (dilationUpperBounds f).Nonempty :=
  ⟨‖f‖, mem_dilationUpperBounds_of_eventually_le (Eventually.of_forall f.apply_le_norm)⟩

private theorem dilationUpperBound_le_of_eventually_le {f : ℕ →ᵇ ℝ} {c : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ c) : dilationUpperBound f ≤ c :=
  csInf_le (bddBelow_dilationUpperBounds f) (mem_dilationUpperBounds_of_eventually_le h)

private theorem dilationUpperBound_add_le (f g : ℕ →ᵇ ℝ) :
    dilationUpperBound (f + g) ≤ dilationUpperBound f + dilationUpperBound g := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (nonempty_dilationUpperBounds f) fun c hc ↦ ?_
  rw [sub_le_comm]
  refine le_csInf (nonempty_dilationUpperBounds g) fun d hd ↦ ?_
  rw [sub_le_iff_le_add']
  exact csInf_le (bddBelow_dilationUpperBounds _) (add_mem_dilationUpperBounds hc hd)

private theorem dilationUpperBound_smul_le {r : ℝ} (hr : 0 ≤ r) (f : ℕ →ᵇ ℝ) :
    dilationUpperBound (r • f) ≤ r * dilationUpperBound f := by
  simp only [dilationUpperBound]
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hr]
  refine csInf_le_csInf (bddBelow_dilationUpperBounds _)
    ((nonempty_dilationUpperBounds f).smul_set) ?_
  rintro _ ⟨c, hc, rfl⟩
  exact smul_mem_dilationUpperBounds hr hc

private theorem dilationUpperBound_smul {r : ℝ} (hr : 0 < r) (f : ℕ →ᵇ ℝ) :
    dilationUpperBound (r • f) = r * dilationUpperBound f := by
  refine le_antisymm (dilationUpperBound_smul_le hr.le f) ?_
  have := dilationUpperBound_smul_le (inv_nonneg.2 hr.le) (r • f)
  rw [inv_smul_smul₀ hr.ne'] at this
  rwa [← le_inv_mul_iff₀ hr]

private theorem dilationUpperBound_sub_dilate_nonpos (f : ℕ →ᵇ ℝ) {k : ℕ} (hk : 0 < k) :
    dilationUpperBound (f - f.dilate k) ≤ 0 := by
  refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖)) ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact csInf_le (bddBelow_dilationUpperBounds _)
    (two_mul_norm_div_mem_dilationUpperBounds f k N hk hN)

private theorem dilationUpperBound_zero_nonneg : 0 ≤ dilationUpperBound 0 :=
  le_csInf (nonempty_dilationUpperBounds 0) fun _ hc ↦ by
    simpa using neg_norm_le_of_mem_dilationUpperBounds hc

/-- **Existence of dilation-invariant generalized limits.** -/
theorem exists_isDilationInvariant : ∃ ω : GeneralizedLimit, ω.IsDilationInvariant := by
  let f₀ : (ℕ →ᵇ ℝ) →ₗ.[ℝ] ℝ := { domain := ⊥, toFun := 0 }
  have h₀ (x : f₀.domain) : f₀ x ≤ dilationUpperBound x := by
    obtain ⟨x, hx⟩ := x
    obtain rfl : x = 0 := (Submodule.mem_bot ℝ).1 hx
    exact dilationUpperBound_zero_nonneg
  obtain ⟨φ, -, hφ⟩ := exists_extension_of_le_sublinear f₀ dilationUpperBound
    (fun r hr f ↦ dilationUpperBound_smul hr f) dilationUpperBound_add_le h₀
  have hle {f : ℕ →ᵇ ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, f n ≤ c) : φ f ≤ c :=
    (hφ f).trans (dilationUpperBound_le_of_eventually_le h)
  have hge {f : ℕ →ᵇ ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, c ≤ f n) : c ≤ φ f := by
    have := hle (f := -f) (c := -c) (h.mono fun n hn ↦ by simpa using hn)
    rw [map_neg] at this
    linarith
  refine ⟨mk₀ φ (fun f hf ↦ hge (Eventually.of_forall hf)) fun f c hf ↦ ?_,
    isDilationInvariant_iff.2 fun f k hk ↦ ?_⟩
  · refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ hle ?_)
      (le_of_forall_pos_le_add fun ε hε ↦ ?_)
    · exact hf.eventually (Iic_mem_nhds (lt_add_of_pos_right c hε))
    · rw [← sub_le_iff_le_add]
      exact hge (hf.eventually (Ici_mem_nhds (sub_lt_self c hε)))
  · have h₁ := (hφ _).trans (dilationUpperBound_sub_dilate_nonpos f hk)
    have h₂ := (hφ _).trans (dilationUpperBound_sub_dilate_nonpos (-f) hk)
    simp only [map_sub, map_neg, BoundedContinuousFunction.neg_dilate] at h₁ h₂
    simp only [mk₀_apply]
    linarith

end Existence

end GeneralizedLimit

end TauCeti
