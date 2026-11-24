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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.MeasureTheory.Function.IntervalStep
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Herbrand function of a group acting on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with real-indexed ramification
groups `G_t = ramificationGroupReal G S t = G_{⌈t⌉}`. The **Herbrand function** of the action is

`φ(u) = ∫_0^u #G_t / #G_0 dt`,

its **inverse** is `ψ(v) = sInf {u | v ≤ φ(u)}`, and the **upper numbering** is
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
continuous, strictly increasing, concave bijection of `ℝ`, the identity on `[-1, 0]`, and `ψ(v)` is
the least `u` with `v ≤ φ(u)`. So `ψ` is the inverse of `φ` and `G^{φ(u)} = G_u`. For finite `G`
both functions preserve `[-1, ∞)`. Below `-1` they are an affine extension outside the classical
domain (of slope `#G / #G_0` for `φ`), so only their values on `[-1, ∞)` carry meaning. For an
infinite `G` the three definitions are totalized formulas: `Nat.card` makes `φ` identically zero
when `G_0` is infinite, and `ψ` need not invert `φ`.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun G S`: the Herbrand function `φ`, as a function `ℝ → ℝ`.
* `TauCeti.IsLocalRing.inverseHerbrandFun G S`: the inverse Herbrand function `ψ`.
* `TauCeti.IsLocalRing.herbrandOrderIso G S`: for finite `G`, `φ` as an order automorphism of
  `ℝ` with inverse `ψ`.
* `TauCeti.IsLocalRing.herbrandIciOrderIso G S`: for finite `G`, its restriction to an order
  automorphism of `[-1, ∞)`.
* `TauCeti.IsLocalRing.upperRamificationGroup G S v`: the upper ramification group
  `G^v = G_{ψ(v)}`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_strictMono`, `TauCeti.IsLocalRing.continuous_herbrandFun`,
  `TauCeti.IsLocalRing.concaveOn_herbrandFun` and `TauCeti.IsLocalRing.herbrandFun_surjective`:
  `φ` is a continuous, strictly increasing, concave bijection of `ℝ`.
* `TauCeti.IsLocalRing.herbrandFun_sub_herbrandFun_of_forall_eq`: `φ` is affine of slope
  `#H / #G_0` on an interval over which the filtration is constantly `H`, and
  `TauCeti.IsLocalRing.herbrandFun_sub_herbrandFun_of_sub_one_le_of_le`: of slope `#G_i / #G_0`
  on `[i - 1, i]`.
* `TauCeti.IsLocalRing.herbrandFun_of_neg_one_le_of_nonpos`: for finite `G_0`, `φ` is the
  identity on `[-1, 0]`, and `TauCeti.IsLocalRing.herbrandFun_eq_self_of_forall_eq`: on
  `[-1, u]` as long as the filtration is constant from `0` through `u`.
* `TauCeti.IsLocalRing.herbrandFun_of_mem_Icc` and `TauCeti.IsLocalRing.herbrandFun_natCast`:
  the finite-sum formula `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0` on `[m, m + 1]`.

The remaining results assume that `G` is finite.

* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun` and
  `TauCeti.IsLocalRing.inverseHerbrandFun_herbrandFun`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
* `TauCeti.IsLocalRing.inverseHerbrandFun_le_iff`: `ψ(v) ≤ u ↔ v ≤ φ(u)`, so `ψ(v)` is the least
  `u` with `v ≤ φ(u)`.
* `TauCeti.IsLocalRing.neg_one_le_herbrandFun_iff` and
  `TauCeti.IsLocalRing.neg_one_le_inverseHerbrandFun_iff`: `φ` and `ψ` preserve `[-1, ∞)`.
* `TauCeti.IsLocalRing.upperRamificationGroup_herbrandFun`: `G^{φ(u)} = G_u`, and
  `TauCeti.IsLocalRing.upperRamificationGroup_eq_of_herbrandFun_lt_of_le`: `G^v = G_i` for
  `φ(i - 1) < v ≤ φ(i)`.
* `TauCeti.IsLocalRing.upperRamificationGroup_antitone`: the upper filtration decreases.

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
`G_t` lies in `G_0`, so when `G_0` is finite the integrand is `1 / [G_0 : G_t]` there. When `G_0`
is infinite, `Nat.card` makes the integrand, and so `φ`, identically zero. Only the values on
`[-1, ∞)` carry meaning. -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The **inverse Herbrand function** `ψ(v) = sInf {u | v ≤ φ(u)}`. For finite `G` it is the
least `u` with `v ≤ φ(u)` (`inverseHerbrandFun_le_iff`) and the inverse of the Herbrand function
(`herbrandFun_inverseHerbrandFun` and `inverseHerbrandFun_herbrandFun`). For infinite `G` it is
only a totalized formula: it need not invert `φ` or be monotone, even on `[-1, ∞)`. -/
def inverseHerbrandFun (v : ℝ) : ℝ :=
  sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}`. For finite `G` this is the
numbering under which `G^{φ(u)} = G_u` (`upperRamificationGroup_herbrandFun`), and it decreases
(`upperRamificationGroup_antitone`). For infinite `G` it is only a totalized formula: it need not
satisfy `G^{φ(u)} = G_u`, even on `[-1, ∞)`. -/
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
  have hg : herbrandDensity G S = fun t ↦
      (Nat.card (ramificationGroup G S ⌈t⌉) : ℝ) / Nat.card (ramificationGroup G S 0) :=
    funext fun t ↦ by rw [herbrandDensity, ramificationGroupReal_def]
  rw [hg]
  exact intervalIntegrable_comp_ceil (fun i ↦
    (Nat.card (ramificationGroup G S i) : ℝ) / Nat.card (ramificationGroup G S 0)) a b

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

/-- On an interval `[a, b] ⊆ [i - 1, i]` with `i : ℤ`, the Herbrand function is affine of slope
`#G_i / #G_0`. -/
theorem herbrandFun_sub_herbrandFun_of_sub_one_le_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_herbrandFun_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

/-- The Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) :
    herbrandFun G S m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
        Nat.card (ramificationGroup G S 0) := by
  -- Sum the integrals over the unit intervals `[k, k + 1]`, on each of which `G_t = G_{k+1}`.
  have hk (k : ℕ) : ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), herbrandDensity G S t =
      Nat.card (ramificationGroup G S (k + 1 : ℕ)) / Nat.card (ramificationGroup G S 0) := by
    rw [← herbrandFun_sub, herbrandFun_sub_herbrandFun_of_sub_one_le_of_le G S (i := (k + 1 : ℕ))
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; rfl)]
    push_cast
    ring
  have h := sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ)) (n := m)
    fun k _ ↦ intervalIntegrable_herbrandDensity G S _ _
  simp only [hk, Nat.cast_zero] at h
  change ∫ t in (0 : ℝ)..m, herbrandDensity G S t = _
  rw [← h, Finset.sum_div, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [add_comm 1 k]

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) :
    herbrandFun G S u =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
        (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  have h := herbrandFun_sub_herbrandFun_of_sub_one_le_of_le G S (i := (m + 1 : ℕ))
    (by push_cast; linarith) h₁ (by push_cast; linarith)
  rw [herbrandFun_natCast] at h
  linear_combination h

/-- When `G_0` is finite, the Herbrand function is the identity on `[-1, 0]`, since the integrand
is `#G_0 / #G_0 = 1` on `(-1, 0]`. -/
@[simp]
theorem herbrandFun_of_neg_one_le_of_nonpos [Finite (ramificationGroup G S 0)] {u : ℝ}
    (h₁ : -1 ≤ u) (h₀ : u ≤ 0) : herbrandFun G S u = u := by
  have h := herbrandFun_sub_herbrandFun_of_sub_one_le_of_le G S (i := 0) (by simpa using h₁) h₀
    (by simp)
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [div_self h0, herbrandFun_zero] at h
  linarith

theorem herbrandFun_neg_one [Finite (ramificationGroup G S 0)] : herbrandFun G S (-1) = -1 :=
  herbrandFun_of_neg_one_le_of_nonpos G S le_rfl (by norm_num)

/-- When `G_0` is finite, the Herbrand function is the identity on `[-1, u]` as long as the
ramification filtration is constant from `0` through `u`, that is `G_t = G_0` for every
`0 < t ≤ u`. -/
theorem herbrandFun_eq_self_of_forall_eq [Finite (ramificationGroup G S 0)] {u : ℝ}
    (h₁ : -1 ≤ u)
    (h : ∀ t : ℝ, 0 < t → t ≤ u → ramificationGroupReal G S t = ramificationGroup G S 0) :
    herbrandFun G S u = u := by
  rcases le_total u 0 with hu | hu
  · exact herbrandFun_of_neg_one_le_of_nonpos G S h₁ hu
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have := herbrandFun_sub_herbrandFun_of_forall_eq G S hu h
  rwa [herbrandFun_zero, div_self h0, sub_zero, sub_zero, mul_one] at this

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
  rw [← sub_pos, herbrandFun_sub]
  exact intervalIntegral_pos_of_pos_on (intervalIntegrable_herbrandDensity G S a b)
    (fun t _ ↦ (inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)).trans_le (inv_le_herbrandDensity G S t))
    hab

/-- The Herbrand function is concave, its integrand `#G_t / #G_0` being antitone. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ univ (herbrandFun G S) :=
  concaveOn_of_slope_anti_adjacent convex_univ fun {x y z} _ _ hxy hyz ↦
    calc (herbrandFun G S z - herbrandFun G S y) / (z - y)
        ≤ herbrandDensity G S y :=
          (div_le_iff₀' (sub_pos.2 hyz)).2 (herbrandFun_sub_le_mul G S hyz.le)
      _ ≤ (herbrandFun G S y - herbrandFun G S x) / (y - x) :=
          (le_div_iff₀' (sub_pos.2 hxy)).2 (mul_le_herbrandFun_sub G S hxy.le)

/-- The Herbrand function is onto: its integrand is bounded below by `1 / #G_0`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) :=
  have h := tendsto_intervalIntegral_atTop_atBot (intervalIntegrable_herbrandDensity G S 0)
    (inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)) (Filter.Eventually.of_forall
      (inv_le_herbrandDensity G S))
  (continuous_herbrandFun G S).surjective h.1 h.2

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
def herbrandOrderIso : ℝ ≃o ℝ :=
  (herbrandFun_strictMono G S).orderIsoOfRightInverse _ (inverseHerbrandFun G S)
    (herbrandFun_inverseHerbrandFun G S)

@[simp]
theorem herbrandOrderIso_apply (u : ℝ) : herbrandOrderIso G S u = herbrandFun G S u :=
  (rfl)

@[simp]
theorem herbrandOrderIso_symm_apply (v : ℝ) :
    (herbrandOrderIso G S).symm v = inverseHerbrandFun G S v :=
  (rfl)

/-- `ψ(v) ≤ u ↔ v ≤ φ(u)`: the inverse Herbrand function `ψ(v)` is the least `u` with
`v ≤ φ(u)`. -/
theorem inverseHerbrandFun_le_iff {u v : ℝ} :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u :=
  (herbrandOrderIso G S).symm_apply_le

/-- `u ≤ ψ(v) ↔ φ(u) ≤ v`. -/
theorem le_inverseHerbrandFun_iff {u v : ℝ} :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v :=
  (herbrandOrderIso G S).le_symm_apply

/-- The inverse Herbrand function is strictly increasing. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.strictMono

/-- The inverse Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.continuous

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem inverseHerbrandFun_of_neg_one_le_of_nonpos {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_of_neg_one_le_of_nonpos G S h₁ h₀]
  exact inverseHerbrandFun_herbrandFun G S v

theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_of_neg_one_le_of_nonpos G S le_rfl (by norm_num)

theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 :=
  inverseHerbrandFun_of_neg_one_le_of_nonpos G S (by norm_num) le_rfl

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

/-- The Herbrand function as an order automorphism of `[-1, ∞)`, the range on which it carries
meaning, with inverse the inverse Herbrand function: the restriction of `herbrandOrderIso G S`,
which fixes `-1`. -/
def herbrandIciOrderIso : Ici (-1 : ℝ) ≃o Ici (-1 : ℝ) :=
  ((herbrandOrderIso G S).Ici (-1)).trans
    (Set.orderIsoOfEq _ _ (congrArg Ici (herbrandFun_neg_one G S)))

@[simp]
theorem coe_herbrandIciOrderIso_apply (u : Ici (-1 : ℝ)) :
    (herbrandIciOrderIso G S u : ℝ) = herbrandFun G S u :=
  (rfl)

@[simp]
theorem coe_herbrandIciOrderIso_symm_apply (v : Ici (-1 : ℝ)) :
    ((herbrandIciOrderIso G S).symm v : ℝ) = inverseHerbrandFun G S v :=
  (rfl)

/-! ### The upper numbering -/

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- The upper ramification group is constant on each upper-numbering step: for `i : ℤ` and
`φ(i - 1) < v ≤ φ(i)`, `G^v = G_i`. -/
theorem upperRamificationGroup_eq_of_herbrandFun_lt_of_le {i : ℤ} {v : ℝ}
    (hv₁ : herbrandFun G S (i - 1) < v) (hv₂ : v ≤ herbrandFun G S i) :
    upperRamificationGroup G S v = ramificationGroup G S i := by
  rw [upperRamificationGroup_def]
  exact ramificationGroupReal_eq_of_sub_one_lt_of_le G S
    ((herbrandOrderIso G S).lt_symm_apply.2 hv₁) ((inverseHerbrandFun_le_iff G S).2 hv₂)

/-- The upper ramification groups decrease. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)

/-- On `[-1, 0]` the upper and lower numberings agree: `G^v = G_v`. -/
@[simp]
theorem upperRamificationGroup_of_neg_one_le_of_nonpos {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_of_neg_one_le_of_nonpos G S h₁ h₀]

end IsLocalRing

end TauCeti
