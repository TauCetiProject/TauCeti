/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Herbrand function and upper ramification groups of a local ring

For a group `G` acting by ring automorphisms on a local ring `S`, with real-indexed lower
ramification filtration `G_t = ramificationGroupReal G S t = G_{⌈t⌉}`, this file defines the
**Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt`, its **inverse** `ψ(v) = sInf {u | v ≤ φ(u)}`,
the **upper ramification groups** `G^v = G_{ψ(v)}`, the integral inverse `ψℕ(n) = ⌊ψ(n)⌋₊`, and
lower/upper jumps.

When `G` is finite, `φ` is a continuous, strictly increasing, concave bijection of `ℝ` (and of
`[-1, ∞)`) with two-sided inverse `ψ`, equal to the identity on `[-1, 0]`, affine of slope
`#G_{m+1} / #G_0` on `[m, m + 1]` (`m : ℕ`), and with `ψ(n) ∈ ℕ` for `n : ℕ`. Neither a discrete
valuation, completeness, nor residue-field finiteness is required.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun`, `TauCeti.IsLocalRing.inverseHerbrandFun`,
  `TauCeti.IsLocalRing.herbrandOrderIso`, `TauCeti.IsLocalRing.herbrandOrderIsoIci`,
  `TauCeti.IsLocalRing.psiNat`
* `TauCeti.IsLocalRing.upperRamificationGroup`
* `TauCeti.IsLocalRing.LowerJump`, `TauCeti.IsLocalRing.UpperJump`

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), n° 3.1.
* Adapts `TauCeti/NumberTheory/LocalField/Herbrand/{Basic,Jump}.lean` to arbitrary local rings.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti.IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` of `G` acting on a local ring `S`. -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The integral formula defining `herbrandFun`. -/
theorem herbrandFun_def (u : ℝ) :
    herbrandFun G S u = ∫ t in (0 : ℝ)..u,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) := (rfl)

/-- The **inverse Herbrand function** `ψ(v) = sInf {u : ℝ | v ≤ φ(u)}`. -/
def inverseHerbrandFun (v : ℝ) : ℝ := sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- Unfolding lemma for `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} := (rfl)

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of `G` acting on `S`. -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

/-- Unfolding lemma for `upperRamificationGroup`. -/
theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) := (rfl)

/-- The **integral inverse Herbrand function** `ψℕ(n) = ⌊ψ(n)⌋₊`. -/
def psiNat (n : ℕ) : ℕ := ⌊inverseHerbrandFun G S n⌋₊

/-- A **lower jump** (break) of the lower ramification filtration. -/
def LowerJump (u : ℝ) : Prop :=
  ∀ v : ℝ, u < v → ramificationGroupReal G S v < ramificationGroupReal G S u

/-- An **upper jump** (break) of the upper ramification filtration. -/
def UpperJump (v : ℝ) : Prop :=
  ∀ w : ℝ, v < w → upperRamificationGroup G S w < upperRamificationGroup G S v

theorem lowerJump_iff (u : ℝ) :
    LowerJump G S u ↔ ∀ v : ℝ, u < v → ramificationGroupReal G S v < ramificationGroupReal G S u :=
  Iff.rfl

theorem upperJump_iff (v : ℝ) :
    UpperJump G S v ↔
      ∀ w : ℝ, v < w → upperRamificationGroup G S w < upperRamificationGroup G S v := Iff.rfl

/-- `φ(0) = 0`. -/
@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 := by rw [herbrandFun_def, integral_same]

variable {G S} in
/-- Membership in an upper ramification group: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} :
    σ ∈ upperRamificationGroup G S v ↔ σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  by rw [upperRamificationGroup_def]

/-- Every upper ramification group is normal in `G`. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]; infer_instance

end Defs

section LowerJump

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- Every lower jump is at least `-1`. -/
theorem neg_one_le_of_lowerJump {u : ℝ} (h : LowerJump G S u) : -1 ≤ u := by
  by_contra hlt
  replace hlt : u < -1 := not_le.1 hlt
  have hstrict := h ((u + -1) / 2) (by linarith)
  rw [ramificationGroupReal_def, ramificationGroupReal_def,
    ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by push_cast; linarith)),
    ramificationGroup_eq_top_of_le_neg_one G S
      (Int.ceil_le.2 (by exact_mod_cast hlt.le))] at hstrict
  exact lt_irrefl _ hstrict

/-- Every lower jump is an integer `≥ -1`. -/
theorem lowerJump_eq_intCast {u : ℝ} (h : LowerJump G S u) :
    ∃ i : ℤ, -1 ≤ i ∧ u = (i : ℝ) := by
  refine ⟨⌈u⌉, by exact_mod_cast (neg_one_le_of_lowerJump G S h).trans (Int.le_ceil u), ?_⟩
  rcases eq_or_lt_of_le (Int.le_ceil u) with heq | hlt
  · exact heq
  · have hstrict := h ⌈u⌉ hlt
    rw [ramificationGroupReal_intCast, ramificationGroupReal_def] at hstrict
    exact absurd hstrict (lt_irrefl _)

/-- At an integer `i`, a lower jump is a strict drop from `G_i` to `G_{i+1}`. -/
@[simp]
theorem lowerJump_intCast_iff {i : ℤ} :
    LowerJump G S (i : ℝ) ↔ ramificationGroup G S (i + 1) < ramificationGroup G S i := by
  refine ⟨fun h ↦ by
      simpa only [ramificationGroupReal_intCast] using h ((i + 1 : ℤ) : ℝ) (by push_cast; linarith),
    fun h v hv ↦ ?_⟩
  rw [ramificationGroupReal_intCast, ramificationGroupReal_def]
  exact (ramificationGroup_antitone G S (by have := Int.lt_ceil.2 hv; omega)).trans_lt h

end LowerJump

section Finite

variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]

/-- The integrand `#G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun _ _ hst ↦ by
  unfold herbrandDensity
  gcongr
  exact Subgroup.card_le_of_le (ramificationGroupReal_antitone G S hst)

private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity G S) volume a b :=
  (herbrandDensity_antitone G S).intervalIntegrable

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (ramificationGroup G S 0) : ℝ)⁻¹ ≤ herbrandDensity G S t := by
  rw [herbrandDensity, div_eq_mul_inv]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.card_pos)

/-- Increment formula: `φ(b) - φ(a) = ∫_a^b #G_t / #G_0 dt`. -/
theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a = ∫ t in a..b,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-- On an interval `[a, b]` where `G_t = H` on `(a, b]`, `φ` is affine of slope `#H / #G_0`. -/
theorem herbrandFun_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * ((Nat.card H : ℝ) / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]`, `φ` is affine of slope `#G_i / #G_0`. -/
theorem herbrandFun_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * ((Nat.card (ramificationGroup G S i) : ℝ) /
        Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

/-- Lower linear growth bound: `(b - a) / #G_0 ≤ φ(b) - φ(a)` for `a ≤ b`. -/
theorem div_sub_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t _ ↦ inv_le_herbrandDensity G S t

private theorem herbrandFun_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandFun G S b - herbrandFun G S a ≤ (b - a) * herbrandDensity G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity G S a b) intervalIntegrable_const
    fun _ ht ↦ herbrandDensity_antitone G S ht.1

private theorem mul_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G S b ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun _ ht ↦ herbrandDensity_antitone G S ht.2

/-- The Herbrand function is strictly increasing on `ℝ`. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun a b hab ↦ by
  have h := div_sub_le_herbrandFun_sub G S hab.le
  have hpos : 0 < (b - a) / Nat.card (ramificationGroup G S 0) :=
    div_pos (sub_pos.2 hab) (Nat.cast_pos.2 Nat.card_pos)
  linarith

/-- The Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- The slopes of `herbrandFun` decrease over adjacent intervals. -/
theorem herbrandFun_slope_anti_adjacent {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (herbrandFun G S w - herbrandFun G S v) / (w - v) ≤
      (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
  calc (herbrandFun G S w - herbrandFun G S v) / (w - v)
      ≤ herbrandDensity G S v :=
        (div_le_iff₀' (sub_pos.2 hvw)).2 (herbrandFun_sub_le_mul G S hvw.le)
    _ ≤ (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
        (le_div_iff₀' (sub_pos.2 huv)).2 (mul_le_herbrandFun_sub G S huv.le)

/-- The Herbrand function is concave on `ℝ`. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ Set.univ (herbrandFun G S) :=
  concaveOn_of_slope_anti_adjacent convex_univ fun _ _ huv hvw ↦
    herbrandFun_slope_anti_adjacent G S huv hvw

/-- The Herbrand function is the identity on `[-1, 0]`. -/
theorem herbrandFun_of_neg_one_le_of_le_zero {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandFun G S u = u := by
  have h := herbrandFun_sub_of_le G S (i := 0) (by simpa using h₁) h₀ (by simp)
  rw [div_self (by exact_mod_cast (Nat.card_pos (α := ramificationGroup G S 0)).ne'),
    herbrandFun_zero] at h
  linarith

/-- `φ(-1) = -1`. -/
@[simp]
theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_of_neg_one_le_of_le_zero G S le_rfl (by norm_num)

/-- On `(-∞, -1]`, `φ(u) = -1 + (u + 1) · #G / #G_0`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u =
      -1 + (u + 1) * ((Nat.card G : ℝ) / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_of_forall_eq G S (H := ⊤) hu fun _ _ ht₂ ↦ by
    rw [ramificationGroupReal_def]
    exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast ht₂))
  rw [herbrandFun_neg_one, Subgroup.card_top] at h
  linarith

/-- For `m : ℕ` and `m ≤ u ≤ m + 1`, `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
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
  | succ k ih =>
    have hk := ih (u := (k + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_of_le G S (i := (k + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hk] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- At `m : ℕ`, `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) :
    herbrandFun G S m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
        Nat.card (ramificationGroup G S 0) := by
  rw [herbrandFun_of_mem_Icc G S m le_rfl (by linarith), sub_self, zero_mul, add_zero]

/-- The Herbrand function is surjective onto `ℝ`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  have ha : herbrandFun G S (min 0 (y * g)) ≤ y := by
    have h := div_sub_le_herbrandFun_sub G S (min_le_left 0 (y * g))
    have h2 : min 0 (y * g) / g ≤ y := (div_le_iff₀ hg).2 (min_le_right _ _)
    rw [herbrandFun_zero, zero_sub, neg_div] at h
    linarith
  have hb : y ≤ herbrandFun G S (max 0 (y * g)) := by
    have h := div_sub_le_herbrandFun_sub G S (le_max_left 0 (y * g))
    have h2 : y ≤ max 0 (y * g) / g := (le_div_iff₀ hg).2 (le_max_right _ _)
    rw [herbrandFun_zero, sub_zero, sub_zero] at h
    linarith
  obtain ⟨u, _, hu⟩ := intermediate_value_Icc ((min_le_left 0 _).trans (le_max_left 0 _))
    (continuous_herbrandFun G S).continuousOn ⟨ha, hb⟩
  exact ⟨u, hu⟩

/-- `φ(ψ(v)) = v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  obtain ⟨u₀, rfl⟩ := herbrandFun_surjective G S v
  have hset : {u : ℝ | herbrandFun G S u₀ ≤ herbrandFun G S u} = Set.Ici u₀ :=
    Set.ext fun _ ↦ (herbrandFun_strictMono G S).le_iff_le
  rw [inverseHerbrandFun_def, hset, csInf_Ici]

/-- `ψ(φ(u)) = u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u :=
  (herbrandFun_strictMono G S).injective (herbrandFun_inverseHerbrandFun G S _)

/-- The Herbrand function as an order automorphism of `ℝ`, with inverse `inverseHerbrandFun`. -/
def herbrandOrderIso : ℝ ≃o ℝ where
  toFun := herbrandFun G S
  invFun := inverseHerbrandFun G S
  left_inv := inverseHerbrandFun_herbrandFun G S
  right_inv := herbrandFun_inverseHerbrandFun G S
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

@[simp]
theorem herbrandOrderIso_apply (u : ℝ) : herbrandOrderIso G S u = herbrandFun G S u := (rfl)

@[simp]
theorem herbrandOrderIso_symm_apply (v : ℝ) :
    (herbrandOrderIso G S).symm v = inverseHerbrandFun G S v := (rfl)

/-- The inverse Herbrand function is strictly increasing on `ℝ`. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.strictMono

/-- The inverse Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) :=
  (herbrandOrderIso G S).symm.continuous

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
theorem inverseHerbrandFun_of_neg_one_le_of_le_zero {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_of_neg_one_le_of_le_zero G S h₁ h₀]
  exact inverseHerbrandFun_herbrandFun G S v

/-- `ψ(-1) = -1`. -/
@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_of_neg_one_le_of_le_zero G S le_rfl (by norm_num)

/-- `ψ(0) = 0`. -/
@[simp]
theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 :=
  inverseHerbrandFun_of_neg_one_le_of_le_zero G S (by norm_num) le_rfl

/-- `φ` preserves `[-1, ∞)`. -/
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  conv_lhs => rw [← herbrandFun_neg_one G S]
  exact (herbrandFun_strictMono G S).le_iff_le

/-- `ψ` preserves `[-1, ∞)`. -/
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  conv_lhs => rw [← inverseHerbrandFun_neg_one G S]
  exact (inverseHerbrandFun_strictMono G S).le_iff_le

/-- The Herbrand function as an order automorphism of `[-1, ∞)`. -/
def herbrandOrderIsoIci : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) where
  toFun u := ⟨herbrandFun G S u, (neg_one_le_herbrandFun_iff G S).2 u.2⟩
  invFun v := ⟨inverseHerbrandFun G S v, (neg_one_le_inverseHerbrandFun_iff G S).2 v.2⟩
  left_inv u := Subtype.ext (inverseHerbrandFun_herbrandFun G S u)
  right_inv v := Subtype.ext (herbrandFun_inverseHerbrandFun G S v)
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

@[simp]
theorem coe_herbrandOrderIsoIci (u : Set.Ici (-1 : ℝ)) :
    (herbrandOrderIsoIci G S u : ℝ) = herbrandFun G S u := (rfl)

@[simp]
theorem coe_herbrandOrderIsoIci_symm (v : Set.Ici (-1 : ℝ)) :
    ((herbrandOrderIsoIci G S).symm v : ℝ) = inverseHerbrandFun G S v := (rfl)

/-! ### Upper ramification groups and jumps -/

/-- `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- On `[-1, 0]` the upper and lower numberings agree. -/
theorem upperRamificationGroup_of_neg_one_le_of_le_zero {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_of_neg_one_le_of_le_zero G S h₁ h₀]

/-- `G^0 = G_0`. -/
@[simp]
theorem upperRamificationGroup_zero :
    upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  rw [upperRamificationGroup_of_neg_one_le_of_le_zero G S (by norm_num) le_rfl,
    ← Int.cast_zero, ramificationGroupReal_intCast]

/-- For `v ≤ -1`, `G^v = ⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ := by
  have hψ : inverseHerbrandFun G S v ≤ -1 := by
    rw [← inverseHerbrandFun_neg_one G S]
    exact (inverseHerbrandFun_strictMono G S).monotone hv
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast hψ))

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)

/-- **Finite-level subgroup identity:** `H ∩ G^u = H^{φ_H(ψ_G(u))}` for any `H ≤ G`. -/
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal, upperRamificationGroup_def,
    inverseHerbrandFun_herbrandFun]

/-- `φ` carries lower jumps precisely to upper jumps. -/
@[simp]
theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  refine ⟨fun h v huv ↦ by
      simpa only [upperRamificationGroup_herbrandFun] using
        h (herbrandFun G S v) (herbrandFun_strictMono G S huv),
    fun h w hvw ↦ ?_⟩
  have hlt : u < inverseHerbrandFun G S w := by
    simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono G S hvw
  simpa only [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun] using h _ hlt

/-- `ψ` carries upper jumps precisely to lower jumps. -/
@[simp]
theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa only [herbrandFun_inverseHerbrandFun] using
    (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

/-- Every upper jump is at least `-1`. -/
theorem neg_one_le_of_upperJump {v : ℝ} (h : UpperJump G S v) : -1 ≤ v :=
  (neg_one_le_inverseHerbrandFun_iff G S).1 <|
    neg_one_le_of_lowerJump G S ((lowerJump_inverseHerbrandFun_iff G S v).2 h)

/-! ### Integrality of the inverse Herbrand function at natural numbers -/

/-- For every `n : ℕ`, `ψ(n)` is a natural number equal to `psiNat G S n`. -/
@[simp]
theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n := by
  set u : ℝ := inverseHerbrandFun G S n
  set m := ⌊u⌋₊
  have hu0 : 0 ≤ u := by
    rw [← inverseHerbrandFun_zero G S]
    exact (inverseHerbrandFun_strictMono G S).monotone (Nat.cast_nonneg n)
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le hu0
  have hm₂ : u < m + 1 := Nat.lt_floor_add_one u
  have hφ := herbrandFun_of_mem_Icc G S m hm₁ hm₂.le
  rw [herbrandFun_inverseHerbrandFun,
    eq_div_iff (by exact_mod_cast (Nat.card_pos (α := ramificationGroup G S 0)).ne')] at hφ
  set g : ℤ → ℕ := fun i ↦ Nat.card (ramificationGroup G S i)
  have hdvd : ∀ i : ℤ, i ≤ (m + 1 : ℕ) → g (m + 1 : ℕ) ∣ g i := fun i hi ↦
    Subgroup.card_dvd_of_le (ramificationGroup_antitone G S hi)
  have h₁ : g (m + 1 : ℕ) ∣ n * g 0 := dvd_mul_of_dvd_right (hdvd 0 (by omega)) _
  have h₂ : g (m + 1 : ℕ) ∣ ∑ i ∈ Finset.Icc 1 m, g i := Finset.dvd_sum fun i hi ↦
    hdvd i (by have := (Finset.mem_Icc.1 hi).2; omega)
  obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.2 h₁).sub (Int.natCast_dvd_natCast.2 h₂)
  have hcR : (n : ℝ) * g 0 - ∑ i ∈ Finset.Icc 1 m, (g i : ℝ) = g (m + 1 : ℕ) * c := by
    exact_mod_cast hc
  have hcu : u - m = c := mul_right_cancel₀ (by exact_mod_cast Nat.card_pos.ne') <|
    (by rw [← hcR]; linarith : (u - m) * g (m + 1 : ℕ) = g (m + 1 : ℕ) * c).trans (mul_comm _ _)
  have hc0 : 0 ≤ c := by exact_mod_cast (hcu ▸ sub_nonneg.2 hm₁ : (0 : ℝ) ≤ c)
  have hc1 : c < 1 := by exact_mod_cast (hcu ▸ by linarith : (c : ℝ) < 1)
  have hcz : c = 0 := by omega
  rw [hcz, Int.cast_zero, sub_eq_zero] at hcu
  exact hcu.symm

/-- `psiNat G S n = m` iff `#G_1 + ⋯ + #G_m = n · #G_0`. -/
theorem psiNat_eq_iff {n m : ℕ} :
    psiNat G S n = m ↔
      ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
        n * Nat.card (ramificationGroup G S 0) := by
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup G S 0)).ne'
  rw [← Nat.cast_inj (R := ℝ), coe_psiNat, ← (herbrandFun_strictMono G S).injective.eq_iff,
    herbrandFun_inverseHerbrandFun, herbrandFun_natCast, eq_comm, div_eq_iff h0]
  norm_cast

/-- `ψℕ(0) = 0`. -/
@[simp]
theorem psiNat_zero : psiNat G S 0 = 0 :=
  (psiNat_eq_iff G S).2 (by simp)

/-- `psiNat G S` is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat G S) := fun _ _ h ↦ by
  have hlt := inverseHerbrandFun_strictMono G S (Nat.cast_lt.2 h)
  exact_mod_cast (coe_psiNat G S _).trans_lt (hlt.trans_eq (coe_psiNat G S _).symm)

/-- `n ≤ ψℕ(n)`. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat G S n :=
  (psiNat_strictMono G S).id_le n

/-- `ψℕ(n) ≤ i ↔ n ≤ ⌊φ(i)⌋₊`. -/
@[simp]
theorem psiNat_le_iff_le_floor_herbrandFun {n i : ℕ} :
    psiNat G S n ≤ i ↔ n ≤ ⌊herbrandFun G S i⌋₊ := by
  have h0 : 0 ≤ herbrandFun G S i := by
    rw [← herbrandFun_zero G S]
    exact (herbrandFun_strictMono G S).monotone (Nat.cast_nonneg i)
  rw [Nat.le_floor_iff h0, ← Nat.cast_le (α := ℝ), coe_psiNat,
    ← (herbrandFun_strictMono G S).le_iff_le, herbrandFun_inverseHerbrandFun]

/-- At `n : ℕ`, `G^n = G_{ψℕ(n)}`. -/
@[simp]
theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S (n : ℝ) = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast, ramificationGroupReal_intCast]

/-- For a faithful action of a finite group on a Noetherian local ring, the upper ramification
groups vanish for all sufficiently large real indices. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ N : ℝ, ∀ v : ℝ, N ≤ v → upperRamificationGroup G S v = ⊥ := by
  obtain ⟨M, hM⟩ := exists_forall_ramificationGroup_eq_bot G S
  refine ⟨herbrandFun G S M, fun v hv ↦ ?_⟩
  have hψ : (M : ℝ) ≤ inverseHerbrandFun G S v := by
    simpa only [inverseHerbrandFun_herbrandFun] using
      (inverseHerbrandFun_strictMono G S).monotone hv
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact hM ⌈inverseHerbrandFun G S v⌉ (Int.le_ceil_iff.2 (by linarith))

end Finite

section Transport

variable {G S G' S' : Type*} [Group G] [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  [Group G'] [CommRing S'] [IsLocalRing S'] [MulSemiringAction G' S']

/-- A ring isomorphism equivariant along a group homomorphism pulls back `ramificationGroup`. -/
theorem ramificationGroup_eq_comap_of_ringEquiv (φ : G →* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = φ g • eS x) (i : ℤ) :
    ramificationGroup G S i = (ramificationGroup G' S' i).comap φ := by
  have hmax : (_root_.IsLocalRing.maximalIdeal S).map eS.toRingHom =
      _root_.IsLocalRing.maximalIdeal S' :=
    _root_.IsLocalRing.map_ringEquiv_maximalIdeal eS
  have hpow (n : ℕ) : (_root_.IsLocalRing.maximalIdeal S' ^ n).comap eS.toRingHom =
      _root_.IsLocalRing.maximalIdeal S ^ n := by
    rw [← hmax, ← Ideal.map_pow, Ideal.comap_map_of_bijective eS.toRingHom eS.bijective]
  exact ramificationGroup_eq_comap_of_comap_maximalIdeal_pow φ eS.toRingHom he hpow
    (fun _ y ↦ ⟨eS.symm y, by simp⟩) i

/-- A ring isomorphism equivariant along a group homomorphism pulls back `ramificationGroupReal`. -/
theorem ramificationGroupReal_eq_comap_of_ringEquiv (φ : G →* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = φ g • eS x) (u : ℝ) :
    ramificationGroupReal G S u = (ramificationGroupReal G' S' u).comap φ := by
  rw [ramificationGroupReal_def, ramificationGroupReal_def]
  exact ramificationGroup_eq_comap_of_ringEquiv φ eS he ⌈u⌉

/-- A ring isomorphism equivariant along a surjective homomorphism of finite groups preserves
`herbrandFun`. -/
theorem herbrandFun_eq_of_surjective_ringEquiv [Finite G] (φ : G →* G')
    (hφ : Function.Surjective φ) (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = φ g • eS x) (u : ℝ) :
    herbrandFun G S u = herbrandFun G' S' u := by
  have hcard (i : ℤ) : Nat.card (ramificationGroup G S i) =
      Nat.card φ.ker * Nat.card (ramificationGroup G' S' i) := by
    rw [ramificationGroup_eq_comap_of_ringEquiv φ eS he i]
    have hle : φ.ker ≤ (ramificationGroup G' S' i).comap φ := fun g hg ↦ by
      simp [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
    have hker : (φ.domRestrict ((ramificationGroup G' S' i).comap φ)).ker =
        φ.ker.subgroupOf ((ramificationGroup G' S' i).comap φ) := by ext ⟨g, _⟩; rfl
    rw [← Subgroup.card_ker_mul_card_range (φ.domRestrict ((ramificationGroup G' S' i).comap φ)),
      hker, MonoidHom.domRestrict_range, Subgroup.map_comap_eq_self_of_surjective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  rw [herbrandFun_def, herbrandFun_def]
  congr 1 with t
  rw [ramificationGroupReal_def, ramificationGroupReal_def, hcard, hcard, Nat.cast_mul,
    Nat.cast_mul, mul_div_mul_left _ _ (by exact_mod_cast Nat.card_pos.ne')]

/-- A ring isomorphism equivariant along a surjective homomorphism of finite groups preserves
`inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_surjective_ringEquiv [Finite G] (φ : G →* G')
    (hφ : Function.Surjective φ) (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = φ g • eS x) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun G' S' v := by
  simp only [inverseHerbrandFun_def, herbrandFun_eq_of_surjective_ringEquiv φ hφ eS he]

/-- A ring isomorphism equivariant along a surjective homomorphism of finite groups pulls back
`upperRamificationGroup`. -/
theorem upperRamificationGroup_eq_comap_of_surjective_ringEquiv [Finite G] (φ : G →* G')
    (hφ : Function.Surjective φ) (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = φ g • eS x) (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup G' S' v).comap φ := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_eq_of_surjective_ringEquiv φ hφ eS he v,
    ramificationGroupReal_eq_comap_of_ringEquiv φ eS he]

/-- An equivariant isomorphism of local rings transports `ramificationGroup`. -/
theorem ramificationGroup_map_of_ringEquiv (eG : G ≃* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = eG g • eS x) (i : ℤ) :
    (ramificationGroup G S i).map eG.toMonoidHom = ramificationGroup G' S' i := by
  rw [ramificationGroup_eq_comap_of_ringEquiv eG.toMonoidHom eS he i,
    Subgroup.map_comap_eq_self_of_surjective eG.surjective]

/-- An equivariant isomorphism of local rings transports `ramificationGroupReal`. -/
theorem ramificationGroupReal_map_of_ringEquiv (eG : G ≃* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = eG g • eS x) (u : ℝ) :
    (ramificationGroupReal G S u).map eG.toMonoidHom = ramificationGroupReal G' S' u := by
  rw [ramificationGroupReal_def, ramificationGroupReal_def]
  exact ramificationGroup_map_of_ringEquiv eG eS he ⌈u⌉

/-- An equivariant isomorphism of local rings preserves `herbrandFun`. -/
theorem herbrandFun_eq_of_ringEquiv (eG : G ≃* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = eG g • eS x) (u : ℝ) :
    herbrandFun G S u = herbrandFun G' S' u := by
  have hcard (i : ℤ) : Nat.card (ramificationGroup G S i) = Nat.card (ramificationGroup G' S' i) :=
    (ramificationGroup_map_of_ringEquiv eG eS he i) ▸
      Nat.card_congr (eG.subgroupMap (ramificationGroup G S i)).toEquiv
  rw [herbrandFun_def, herbrandFun_def]
  congr 1 with t
  rw [ramificationGroupReal_def, ramificationGroupReal_def, hcard, hcard]

/-- An equivariant isomorphism of local rings preserves `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_ringEquiv (eG : G ≃* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = eG g • eS x) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun G' S' v := by
  simp only [inverseHerbrandFun_def, herbrandFun_eq_of_ringEquiv eG eS he]

/-- An equivariant isomorphism of local rings transports `upperRamificationGroup`. -/
theorem upperRamificationGroup_map_of_ringEquiv (eG : G ≃* G') (eS : S ≃+* S')
    (he : ∀ (g : G) (x : S), eS (g • x) = eG g • eS x) (v : ℝ) :
    (upperRamificationGroup G S v).map eG.toMonoidHom = upperRamificationGroup G' S' v := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    ← inverseHerbrandFun_eq_of_ringEquiv eG eS he v,
    ramificationGroupReal_map_of_ringEquiv eG eS he]

end Transport

end TauCeti.IsLocalRing
