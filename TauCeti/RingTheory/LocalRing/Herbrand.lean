/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Herbrand function of a group acting on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with real-indexed ramification
groups `G_t = ramificationGroupReal G S t = G_{⌈t⌉}`. The **Herbrand function** of the action is

`φ(u) = ∫_0^u #G_t / #G_0 dt`,

its **inverse** is `ψ(v)`, the least `u` with `v ≤ φ(u)`, and the **upper numbering** is
`G^v = G_{ψ(v)}`. These are the objects of Serre's Herbrand theory, written for the pair `(G, S)`
rather than for an extension of local fields: nothing here uses a valuation, a complete base or a
finite residue field, so they apply to the integral closure of a complete discrete valuation ring
in a finite Galois extension of its fraction field with an arbitrary residue field. The Herbrand
function of a finite Galois extension of nonarchimedean local fields is the instance
`G = L ≃ₐ[K] L`, `S = 𝒪[L]`.

The integrand is a step function of `⌈t⌉`, so for every group `G` the function `φ` is
continuous and affine on each interval `[m, m + 1]` with `m : ℕ`, with
`φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. For finite `G` the integrand is moreover antitone, equal to
`#G / #G_0` on `(-2, -1]`, to `1` on `(-1, 0]` and bounded below by `1 / #G_0`. So `φ` is a
continuous, strictly increasing, concave bijection of `ℝ`, the identity on `[-1, 0]`, and `ψ` is
its inverse, so that `G^{φ(u)} = G_u`. Below `-1` the functions leave the identity, so only
their values on `[-1, ∞)`, which `φ` and `ψ` preserve, carry meaning.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun G S`: the Herbrand function `φ`, as a function `ℝ → ℝ`.
* `TauCeti.IsLocalRing.inverseHerbrandFun G S`: the inverse Herbrand function `ψ`.
* `TauCeti.IsLocalRing.herbrandOrderIso G S`: for finite `G`, `φ` as an order automorphism of
  `ℝ` with inverse `ψ`.
* `TauCeti.IsLocalRing.upperRamificationGroup G S v`: the upper ramification group
  `G^v = G_{ψ(v)}`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_strictMono`, `TauCeti.IsLocalRing.continuous_herbrandFun`,
  `TauCeti.IsLocalRing.concaveOn_herbrandFun` and `TauCeti.IsLocalRing.herbrandFun_surjective`:
  `φ` is a continuous, strictly increasing, concave bijection of `ℝ`.
* `TauCeti.IsLocalRing.herbrandFun_sub_herbrandFun_of_forall_eq`: `φ` is affine of slope
  `#H / #G_0` on an interval over which the filtration is constantly `H`.
* `TauCeti.IsLocalRing.herbrandFun_of_neg_one_le_of_nonpos`: `φ` is the identity on `[-1, 0]`.
* `TauCeti.IsLocalRing.herbrandFun_of_mem_Icc` and `TauCeti.IsLocalRing.herbrandFun_natCast`:
  the finite-sum formula `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0` on `[m, m + 1]`.
* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun` and
  `TauCeti.IsLocalRing.inverseHerbrandFun_herbrandFun`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
* `TauCeti.IsLocalRing.neg_one_le_herbrandFun_iff` and
  `TauCeti.IsLocalRing.neg_one_le_inverseHerbrandFun_iff`: `φ` and `ψ` preserve `[-1, ∞)`.
* `TauCeti.IsLocalRing.upperRamificationGroup_herbrandFun`: `G^{φ(u)} = G_u`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti

namespace IsLocalRing

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-! ### Definitions -/

/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` of a group `G` acting on a local ring
`S`, where `G_t = G_{⌈t⌉}` is the real-indexed ramification filtration. For `t > -1` the group
`G_t` lies in `G_0`, so the integrand is `1 / [G_0 : G_t]` there. Only the values on `[-1, ∞)`
carry meaning. -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The **inverse Herbrand function** `ψ(v)`, the least `u` with `v ≤ φ(u)`. For finite `G` it
is the inverse of the Herbrand function (`herbrandFun_inverseHerbrandFun` and
`inverseHerbrandFun_herbrandFun`). -/
def inverseHerbrandFun (v : ℝ) : ℝ :=
  sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}`, the numbering under which
`G^{φ(u)} = G_u` (`upperRamificationGroup_herbrandFun`). -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

theorem herbrandFun_def (u : ℝ) :
    herbrandFun G S u = ∫ t in (0 : ℝ)..u,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  (rfl)

theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} :=
  (rfl)

theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  (rfl)

variable {G S} in
/-- Membership in the upper ramification groups: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} :
    σ ∈ upperRamificationGroup G S v ↔
      σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) := by
  rw [upperRamificationGroup_def]

/-- Every upper ramification group is normal in `G`. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 :=
  integral_same

/-! ### The integrand -/

/-- The integrand `#G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The integrand is a step function of `⌈t⌉`, so it is bounded on every bounded interval and
integrable there, whether or not `G` is finite. -/
private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity G S) volume a b := by
  set g : ℤ → ℝ := fun i ↦
    (Nat.card (ramificationGroup G S i) : ℝ) / Nat.card (ramificationGroup G S 0)
  have hg₀ (i : ℤ) : 0 ≤ g i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg : herbrandDensity G S = g ∘ Int.ceil :=
    funext fun t ↦ by rw [herbrandDensity, ramificationGroupReal_def, Function.comp_apply]
  rw [intervalIntegrable_iff, uIoc, hg]
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((Measurable.of_discrete.comp Int.measurable_ceil).aestronglyMeasurable)
    (∑ i ∈ Finset.Icc ⌈min a b⌉ ⌈max a b⌉, g i)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_)
  rw [Function.comp_apply, Real.norm_of_nonneg (hg₀ _)]
  exact Finset.single_le_sum (fun i _ ↦ hg₀ i)
    (Finset.mem_Icc.2 ⟨Int.ceil_mono ht.1.le, Int.ceil_mono ht.2⟩)

private theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a = ∫ t in a..b, herbrandDensity G S t :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-! ### Affine pieces and the finite-sum formula -/

/-- On an interval `[a, b]` over which the ramification filtration is constantly `H`, that is
`G_t = H` for every `a < t ≤ b`, the Herbrand function is affine of slope `#H / #G_0`. -/
theorem herbrandFun_sub_herbrandFun_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [herbrandDensity, h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]` the Herbrand function is affine of slope
`#G_i / #G_0`. -/
private theorem herbrandFun_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_herbrandFun_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

/-- The Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) :
    herbrandFun G S u =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
        (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  have hstep := herbrandFun_sub_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith) h₁
    (by push_cast; linarith)
  induction m generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandFun_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ m ih =>
    have hm := ih (u := (m + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hm] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) :
    herbrandFun G S m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
        Nat.card (ramificationGroup G S 0) := by
  rw [herbrandFun_of_mem_Icc G S m le_rfl (by linarith), sub_self, zero_mul, add_zero]

/-- The Herbrand function is the identity on `[-1, 0]`, where the integrand is `#G_0 / #G_0`. -/
theorem herbrandFun_of_neg_one_le_of_nonpos [Finite (ramificationGroup G S 0)] {u : ℝ}
    (h₁ : -1 ≤ u) (h₀ : u ≤ 0) : herbrandFun G S u = u := by
  have h := herbrandFun_sub_of_le G S (i := 0) (by simpa using h₁) h₀ (by simp)
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [div_self h0, herbrandFun_zero] at h
  linarith

@[simp]
theorem herbrandFun_neg_one [Finite (ramificationGroup G S 0)] : herbrandFun G S (-1) = -1 :=
  herbrandFun_of_neg_one_le_of_nonpos G S le_rfl (by norm_num)

/-! ### Monotonicity, concavity and surjectivity for a finite group -/

variable [Finite G]

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun s t hst ↦ by
  unfold herbrandDensity
  gcongr
  exact Subgroup.card_le_of_le (ramificationGroupReal_antitone G S hst)

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (ramificationGroup G S 0) : ℝ)⁻¹ ≤ herbrandDensity G S t := by
  rw [herbrandDensity, div_eq_mul_inv]
  refine le_mul_of_one_le_left (by positivity) ?_
  exact_mod_cast Nat.card_pos

private theorem div_sub_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t _ ↦ inv_le_herbrandDensity G S t

private theorem herbrandFun_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandFun G S b - herbrandFun G S a ≤ (b - a) * herbrandDensity G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity G S a b) intervalIntegrable_const
    fun t ht ↦ herbrandDensity_antitone G S ht.1

private theorem mul_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G S b ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t ht ↦ herbrandDensity_antitone G S ht.2

/-- The Herbrand function is strictly increasing. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun a b hab ↦ by
  have h := div_sub_le_herbrandFun_sub G S hab.le
  have : 0 < (b - a) / Nat.card (ramificationGroup G S 0) := by
    have : 0 < Nat.card (ramificationGroup G S 0) := Nat.card_pos
    have : 0 < b - a := sub_pos.2 hab
    positivity
  linarith

/-- The Herbrand function is concave, its integrand `#G_t / #G_0` being antitone. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ univ (herbrandFun G S) :=
  concaveOn_of_slope_anti_adjacent convex_univ fun {x y z} _ _ hxy hyz ↦
    calc (herbrandFun G S z - herbrandFun G S y) / (z - y)
        ≤ herbrandDensity G S y :=
          (div_le_iff₀' (sub_pos.2 hyz)).2 (herbrandFun_sub_le_mul G S hyz.le)
      _ ≤ (herbrandFun G S y - herbrandFun G S x) / (y - x) :=
          (le_div_iff₀' (sub_pos.2 hxy)).2 (mul_le_herbrandFun_sub G S hxy.le)

/-- The Herbrand function is onto: its slope is at least `1 / #G_0` everywhere. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  have hab : -(|y| * g) ≤ |y| * g := by
    have := abs_nonneg y
    nlinarith
  -- On `[-|y| g, |y| g]` the Herbrand function rises by at least `2 |y|` around `φ(0) = 0`.
  have hb := div_sub_le_herbrandFun_sub G S (a := 0) (b := |y| * g) (by positivity)
  have ha := div_sub_le_herbrandFun_sub G S (a := -(|y| * g)) (b := 0)
    (by have := abs_nonneg y; nlinarith)
  rw [herbrandFun_zero, sub_zero, mul_div_cancel_right₀ _ hg.ne'] at hb
  rw [herbrandFun_zero, zero_sub, neg_neg, mul_div_cancel_right₀ _ hg.ne'] at ha
  have hy : y ∈ Icc (herbrandFun G S (-(|y| * g))) (herbrandFun G S (|y| * g)) :=
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc hab (continuous_herbrandFun G S).continuousOn hy
  exact ⟨u, hu⟩

/-! ### The inverse Herbrand function -/

/-- The inverse Herbrand function undoes the Herbrand function: `ψ(φ(u)) = u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u := by
  have : {w : ℝ | herbrandFun G S u ≤ herbrandFun G S w} = Ici u :=
    Set.ext fun _ ↦ (herbrandFun_strictMono G S).le_iff_le
  rw [inverseHerbrandFun_def, this, csInf_Ici]

/-- The Herbrand function undoes its inverse: `φ(ψ(v)) = v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  obtain ⟨u, rfl⟩ := herbrandFun_surjective G S v
  rw [inverseHerbrandFun_herbrandFun]

/-- The Herbrand function as an order automorphism of `ℝ`, with inverse the inverse Herbrand
function. -/
def herbrandOrderIso : ℝ ≃o ℝ where
  toFun := herbrandFun G S
  invFun := inverseHerbrandFun G S
  left_inv := inverseHerbrandFun_herbrandFun G S
  right_inv := herbrandFun_inverseHerbrandFun G S
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

@[simp]
theorem herbrandOrderIso_apply (u : ℝ) : herbrandOrderIso G S u = herbrandFun G S u :=
  (rfl)

@[simp]
theorem herbrandOrderIso_symm_apply (v : ℝ) :
    (herbrandOrderIso G S).symm v = inverseHerbrandFun G S v :=
  (rfl)

/-- The inverse Herbrand function is strictly increasing. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.strictMono

/-- The inverse Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.continuous

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
theorem inverseHerbrandFun_of_neg_one_le_of_nonpos {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_of_neg_one_le_of_nonpos G S h₁ h₀]
  exact inverseHerbrandFun_herbrandFun G S v

@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_of_neg_one_le_of_nonpos G S le_rfl (by norm_num)

/-- The Herbrand function preserves `[-1, ∞)`, the range on which it carries meaning. -/
@[simp]
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  have h := (herbrandFun_strictMono G S).le_iff_le (a := -1) (b := u)
  rwa [herbrandFun_neg_one] at h

/-- The inverse Herbrand function preserves `[-1, ∞)`. -/
@[simp]
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  have h := (inverseHerbrandFun_strictMono G S).le_iff_le (a := -1) (b := v)
  rwa [inverseHerbrandFun_neg_one] at h

/-! ### The upper numbering -/

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- The upper ramification groups decrease. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)

/-- On `[-1, 0]` the upper and lower numberings agree: `G^v = G_v`. -/
theorem upperRamificationGroup_of_neg_one_le_of_nonpos {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_of_neg_one_le_of_nonpos G S h₁ h₀]

end IsLocalRing

end TauCeti
