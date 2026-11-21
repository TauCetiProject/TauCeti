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

/-!
# The Herbrand function and upper ramification numbering on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with real-indexed lower
ramification filtration `G_t = ramificationGroupReal G S t = G_{⌈t⌉}`. The **Herbrand function**
is

`φ(u) = ∫_0^u (#G_t / #G_0) dt`

for real `u`. Its **inverse Herbrand function** is `ψ(v) = sInf {u : ℝ | v ≤ φ(u)}`, and the
**upper ramification groups** are `G^v = G_{ψ(v)}`. Only values at indices `≥ -1` carry
ramification-theoretic meaning, though the definitions are total on `ℝ`.

When `G` is finite, the integrand `#G_t / #G_0` is an antitone step function, equal to `1` on
`(-1, 0]` and bounded below by `1 / #G_0 > 0` everywhere. Consequently `φ` is a continuous,
strictly increasing, piecewise linear, concave bijection of `ℝ` onto `ℝ` that is the identity on
`[-1, 0]` and restricts to an order automorphism `herbrandOrderIso G S` of `[-1, ∞)` with inverse
`ψ`. At a natural number `m` it is given by the finite-sum formula
`φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`, and by Lagrange's theorem `ψ(n)` is a natural number for every
natural number `n`, packaged as `psiNat G S : ℕ → ℕ`.

The upper numbering satisfies `G^{φ(u)} = G_u`, is antitone and normal, and for every subgroup
`H ≤ G` acting by restriction satisfies the trace identity
`H ∩ G^u = H^{φ_H(ψ_G(u))}`. The Herbrand function carries lower jumps bijectively to upper jumps,
and both functions and the upper filtration transport along equivariant ring isomorphisms.

These analytic and structural proofs adapt `TauCeti/NumberTheory/LocalField/Herbrand/Basic.lean` and
`Jump.lean` from nonarchimedean local fields to arbitrary local rings with a finite group action.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun G S u`: the Herbrand function `φ(u)`.
* `TauCeti.IsLocalRing.inverseHerbrandFun G S v`: the inverse Herbrand function `ψ(v)`.
* `TauCeti.IsLocalRing.herbrandOrderIso G S`: `φ` as an order automorphism of `[-1, ∞)`.
* `TauCeti.IsLocalRing.psiNat G S`: the integral inverse Herbrand function `ψℕ : ℕ → ℕ`.
* `TauCeti.IsLocalRing.upperRamificationGroup G S v`: the upper ramification group `G^v = G_{ψ(v)}`.
* `TauCeti.IsLocalRing.UpperJump G S v`: strict drops of the upper filtration.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_strictMono`, `TauCeti.IsLocalRing.continuous_herbrandFun`,
  `TauCeti.IsLocalRing.concaveOn_herbrandFun`,
  `TauCeti.IsLocalRing.herbrandFun_of_neg_one_le_of_le_zero`,
  `TauCeti.IsLocalRing.herbrandFun_of_mem_Icc`,
  `TauCeti.IsLocalRing.herbrandFun_natCast`: analytic properties and finite-sum formula for `φ`.
* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_herbrandFun`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_strictMono`,
  `TauCeti.IsLocalRing.continuous_inverseHerbrandFun`,
  `TauCeti.IsLocalRing.convexOn_inverseHerbrandFun`: inversion, monotonicity, and convexity of `ψ`.
* `TauCeti.IsLocalRing.coe_psiNat`, `TauCeti.IsLocalRing.psiNat_eq_iff`,
  `TauCeti.IsLocalRing.psiNat_strictMono`, `TauCeti.IsLocalRing.self_le_psiNat`: integrality of
  `ψ(n)` and its arithmetic characterization.
* `TauCeti.IsLocalRing.upperRamificationGroup_herbrandFun`,
  `TauCeti.IsLocalRing.upperRamificationGroup_antitone`,
  `TauCeti.IsLocalRing.instNormalUpperRamificationGroup`,
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup`: basic properties and subgroup trace of
  the upper numbering.
* `TauCeti.IsLocalRing.upperJump_herbrandFun_iff`,
  `TauCeti.IsLocalRing.lowerJump_inverseHerbrandFun_iff`: bijection between lower and upper jumps.
* `MulEquiv.herbrandFun_eq_of_equiv`, `MulEquiv.inverseHerbrandFun_eq_of_equiv`,
  `MulEquiv.map_upperRamificationGroup_of_equiv`: transport along equivariant ring isomorphisms.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti.IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [_root_.IsLocalRing S]
  [MulSemiringAction G S]

/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` of a group `G` acting on a local ring
`S`, where `G_t = ramificationGroupReal G S t`. For finite `G`, `φ` is a continuous strictly
increasing bijection of `ℝ`, the identity on `[-1, 0]`, with `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0` at
every natural number `m`; only its values on `[-1, ∞)` carry ramification-theoretic meaning. -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) /
      Nat.card (ramificationGroup G S 0)

/-- The defining integral formula for `herbrandFun`. -/
theorem herbrandFun_def (u : ℝ) :
    herbrandFun G S u = ∫ t in (0 : ℝ)..u,
      (Nat.card (ramificationGroupReal G S t) : ℝ) /
        Nat.card (ramificationGroup G S 0) :=
  (rfl)

/-- The **inverse Herbrand function** `ψ(v)`, defined as the least `u : ℝ` with `v ≤ φ(u)`. For
finite `G`, `φ` is a continuous strictly increasing bijection of `ℝ`, so `ψ` is the two-sided
inverse of `φ`, with `ψ(-1) = -1`. -/
def inverseHerbrandFun (v : ℝ) : ℝ :=
  sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- The defining infimum formula for `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} :=
  (rfl)

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of a group `G` acting on a local
ring `S`, indexed so that `G^{φ(u)} = G_u` when `G` is finite. -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

/-- The defining formula for `upperRamificationGroup`. -/
theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  (rfl)

/-- The **integral inverse Herbrand function** `ψℕ : ℕ → ℕ`, recording `⌊ψ(n)⌋₊`. When `G` is
finite, `ψ(n)` is itself a natural number (`coe_psiNat`), so `ψℕ(n) = ψ(n)`. -/
def psiNat (n : ℕ) : ℕ :=
  ⌊inverseHerbrandFun G S n⌋₊

/-- The defining floor formula for `psiNat`. -/
theorem psiNat_def (n : ℕ) : psiNat G S n = ⌊inverseHerbrandFun G S n⌋₊ :=
  (rfl)

/-- An **upper jump** (or upper break): a real index `v` at which `G^v` strictly contains `G^w`
for every `w > v`. -/
def UpperJump (v : ℝ) : Prop :=
  ∀ w : ℝ, v < w → upperRamificationGroup G S w < upperRamificationGroup G S v

/-- An upper jump is a strict drop of the upper ramification filtration at every later index. -/
theorem upperJump_iff (v : ℝ) :
    UpperJump G S v ↔ ∀ w : ℝ, v < w →
      upperRamificationGroup G S w < upperRamificationGroup G S v :=
  Iff.rfl

/-- `φ(0) = 0`. -/
@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 := by
  rw [herbrandFun_def, integral_same]

variable {G S} in
/-- Membership in the upper ramification group: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} :
    σ ∈ upperRamificationGroup G S v ↔
      σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) := by
  rw [upperRamificationGroup_def]

/-- Every upper ramification group is normal in `G`. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

end Defs

section Finite

variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [_root_.IsLocalRing S]
  [MulSemiringAction G S]

/-! ### Analytic properties of `herbrandFun` -/

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
  refine le_mul_of_one_le_left (by positivity) ?_
  exact_mod_cast (Nat.card_pos (α := ramificationGroupReal G S t))

/-- Increment formula: `φ(b) - φ(a) = ∫_a^b (#G_t / #G_0) dt`. -/
theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a =
      ∫ t in a..b, (Nat.card (ramificationGroupReal G S t) : ℝ) /
        Nat.card (ramificationGroup G S 0) :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-- On an interval `[a, b]` over which the lower ramification filtration is constantly `H`, that
is `G_t = H` for every `a < t ≤ b`, the Herbrand function is affine of slope `#H / #G_0`. -/
theorem herbrandFun_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]` the Herbrand function is affine of slope
`#G_i / #G_0`. -/
theorem herbrandFun_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) /
        Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

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

/-- The Herbrand function is surjective onto `ℝ`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  rcases le_total 0 y with hy | hy
  · have hφ : y ≤ herbrandFun G S (y * g) := by
      have h := div_sub_le_herbrandFun_sub G S (mul_nonneg hy hg.le)
      rw [herbrandFun_zero, sub_zero, sub_zero, mul_div_cancel_right₀ _ hg.ne'] at h
      exact h
    obtain ⟨u, -, hu⟩ := intermediate_value_Icc (mul_nonneg hy hg.le)
      (continuous_herbrandFun G S).continuousOn ⟨by rwa [herbrandFun_zero], hφ⟩
    exact ⟨u, hu⟩
  · have hle : y * g ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy hg.le
    have hφ : herbrandFun G S (y * g) ≤ y := by
      have h := div_sub_le_herbrandFun_sub G S hle
      rw [herbrandFun_zero, zero_sub, zero_sub, neg_div, mul_div_cancel_right₀ _ hg.ne'] at h
      linarith
    obtain ⟨u, -, hu⟩ := intermediate_value_Icc hle
      (continuous_herbrandFun G S).continuousOn ⟨hφ, by rwa [herbrandFun_zero]⟩
    exact ⟨u, hu⟩

/-- The Herbrand function has decreasing slopes over adjacent intervals. -/
theorem herbrandFun_slope_anti_adjacent {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (herbrandFun G S w - herbrandFun G S v) / (w - v) ≤
      (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
  calc
    (herbrandFun G S w - herbrandFun G S v) / (w - v)
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
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup G S 0)).ne'
  rw [div_self h0, herbrandFun_zero] at h
  linarith

/-- `φ(-1) = -1`. -/
@[simp]
theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_of_neg_one_le_of_le_zero G S le_rfl (by norm_num)

/-- Below `-1`, the Herbrand function is linear of slope `#G / #G_0`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u =
      -1 + (u + 1) * ((Nat.card G : ℝ) / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_of_forall_eq G S (H := ⊤) hu fun t _ ht₂ ↦ by
    rw [ramificationGroupReal_def]
    exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast ht₂))
  rw [herbrandFun_neg_one, Subgroup.card_top] at h
  linarith

/-- `φ(u) ≥ -1` if and only if `u ≥ -1`. -/
@[simp]
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  nth_rw 1 [← herbrandFun_neg_one G S]
  exact (herbrandFun_strictMono G S).le_iff_le

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
  | succ k ih =>
    have hk := ih (u := (k + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_of_le G S (i := (k + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hk] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) :
    herbrandFun G S m =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
        Nat.card (ramificationGroup G S 0) := by
  rw [herbrandFun_of_mem_Icc G S m le_rfl (by linarith), sub_self, zero_mul, add_zero]

/-! ### The inverse Herbrand function and order automorphism -/

/-- `ψ(φ(u)) = u` for every real `u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u := by
  rw [inverseHerbrandFun_def]
  have hset : {t : ℝ | herbrandFun G S u ≤ herbrandFun G S t} = Set.Ici u := by
    ext t
    exact (herbrandFun_strictMono G S).le_iff_le
  rw [hset, csInf_Ici]

/-- `φ(ψ(v)) = v` for every real `v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  obtain ⟨u, rfl⟩ := herbrandFun_surjective G S v
  rw [inverseHerbrandFun_herbrandFun]

/-- The Herbrand function as an order automorphism of `ℝ`. -/
private def herbrandRealOrderIso : ℝ ≃o ℝ where
  toFun := herbrandFun G S
  invFun := inverseHerbrandFun G S
  left_inv := inverseHerbrandFun_herbrandFun G S
  right_inv := herbrandFun_inverseHerbrandFun G S
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

/-- The inverse Herbrand function is strictly increasing on `ℝ`. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) :=
  (herbrandRealOrderIso G S).symm.strictMono

/-- The inverse Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) :=
  (herbrandRealOrderIso G S).symm.continuous

/-- The inverse Herbrand function is convex on `ℝ`. -/
theorem convexOn_inverseHerbrandFun : ConvexOn ℝ Set.univ (inverseHerbrandFun G S) := by
  refine convexOn_of_slope_mono_adjacent convex_univ fun {x y z} _ _ hxy hyz ↦ ?_
  have hψxy : inverseHerbrandFun G S x < inverseHerbrandFun G S y :=
    inverseHerbrandFun_strictMono G S hxy
  have hψyz : inverseHerbrandFun G S y < inverseHerbrandFun G S z :=
    inverseHerbrandFun_strictMono G S hyz
  have hslope := herbrandFun_slope_anti_adjacent G S hψxy hψyz
  rw [herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun,
    herbrandFun_inverseHerbrandFun] at hslope
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  rw [div_le_div_iff₀ (sub_pos.2 hψyz) (sub_pos.2 hψxy)] at hslope
  linarith

/-- `ψ(v) ≤ u ↔ v ≤ φ(u)`. -/
theorem inverseHerbrandFun_le_iff_le_herbrandFun {v u : ℝ} :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u :=
  (herbrandRealOrderIso G S).symm_apply_le

/-- `u ≤ ψ(v) ↔ φ(u) ≤ v`. -/
theorem le_inverseHerbrandFun_iff_herbrandFun_le {u v : ℝ} :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v :=
  (herbrandRealOrderIso G S).le_symm_apply

/-- `ψ(v) < u ↔ v < φ(u)`. -/
theorem inverseHerbrandFun_lt_iff_lt_herbrandFun {v u : ℝ} :
    inverseHerbrandFun G S v < u ↔ v < herbrandFun G S u :=
  (herbrandRealOrderIso G S).symm_apply_lt

/-- `u < ψ(v) ↔ φ(u) < v`. -/
theorem lt_inverseHerbrandFun_iff_herbrandFun_lt {u v : ℝ} :
    u < inverseHerbrandFun G S v ↔ herbrandFun G S u < v :=
  (herbrandRealOrderIso G S).lt_symm_apply

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
theorem inverseHerbrandFun_of_neg_one_le_of_le_zero {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  have h := inverseHerbrandFun_herbrandFun G S v
  rwa [herbrandFun_of_neg_one_le_of_le_zero G S h₁ h₀] at h

/-- `ψ(0) = 0`. -/
@[simp]
theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 :=
  inverseHerbrandFun_of_neg_one_le_of_le_zero G S (by norm_num) le_rfl

/-- `ψ(-1) = -1`. -/
@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_of_neg_one_le_of_le_zero G S le_rfl (by norm_num)

/-- `ψ(v) ≥ -1` if and only if `v ≥ -1`. -/
@[simp]
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  nth_rw 1 [← inverseHerbrandFun_neg_one G S]
  exact (inverseHerbrandFun_strictMono G S).le_iff_le

/-- The **Herbrand function** restricted to `[-1, ∞)`, packaged as an order automorphism with
inverse `ψ`. -/
def herbrandOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) where
  toFun u := ⟨herbrandFun G S u, (neg_one_le_herbrandFun_iff G S).2 u.property⟩
  invFun v := ⟨inverseHerbrandFun G S v, (neg_one_le_inverseHerbrandFun_iff G S).2 v.property⟩
  left_inv u := Subtype.ext (inverseHerbrandFun_herbrandFun G S u)
  right_inv v := Subtype.ext (herbrandFun_inverseHerbrandFun G S v)
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

/-- The underlying real value of `herbrandOrderIso G S u` is `herbrandFun G S u`. -/
@[simp]
theorem coe_herbrandOrderIso_apply (u : Set.Ici (-1 : ℝ)) :
    (herbrandOrderIso G S u : ℝ) = herbrandFun G S u :=
  (rfl)

/-- The underlying real value of `(herbrandOrderIso G S).symm v` is `inverseHerbrandFun G S v`. -/
@[simp]
theorem coe_herbrandOrderIso_symm_apply (v : Set.Ici (-1 : ℝ)) :
    ((herbrandOrderIso G S).symm v : ℝ) = inverseHerbrandFun G S v :=
  (rfl)

/-! ### Integrality of `ψ(n)` -/

private theorem inverseHerbrandFun_natCast_nonneg (n : ℕ) :
    0 ≤ inverseHerbrandFun G S n := by
  rw [← inverseHerbrandFun_zero G S]
  exact (inverseHerbrandFun_strictMono G S).monotone (Nat.cast_nonneg n)

/-- For every natural number `n`, `ψ(n)` is a natural number, computed by `psiNat G S n`. -/
@[simp]
theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n := by
  symm
  rw [psiNat]
  set u : ℝ := inverseHerbrandFun G S n
  set m := ⌊u⌋₊
  have hu : 0 ≤ u := inverseHerbrandFun_natCast_nonneg G S n
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le hu
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
  have hg_ne : (g (m + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup G S (m + 1 : ℕ))).ne'
  have hcu : u - m = c := mul_right_cancel₀ hg_ne <|
    (by rw [← hcR]; linarith : (u - m) * g (m + 1 : ℕ) = g (m + 1 : ℕ) * c).trans (mul_comm _ _)
  have hc0 : 0 ≤ c := by exact_mod_cast (hcu ▸ sub_nonneg.2 hm₁ : (0 : ℝ) ≤ c)
  have hc1 : c < 1 := by exact_mod_cast (hcu ▸ by linarith : (c : ℝ) < 1)
  have hc_zero : c = 0 := by omega
  rw [hc_zero, Int.cast_zero, sub_eq_zero] at hcu
  exact hcu

/-- Arithmetic characterization of `psiNat`: `ψℕ(n) = m` if and only if
`#G_1 + ⋯ + #G_m = n · #G_0`. -/
theorem psiNat_eq_iff {n m : ℕ} :
    psiNat G S n = m ↔
      ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
        n * Nat.card (ramificationGroup G S 0) := by
  have h0 : (Nat.card (ramificationGroup G S 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup G S 0)).ne'
  calc
    psiNat G S n = m ↔ (psiNat G S n : ℝ) = m := Nat.cast_inj.symm
    _ ↔ inverseHerbrandFun G S n = m := by rw [coe_psiNat]
    _ ↔ herbrandFun G S m = n :=
      (herbrandRealOrderIso G S).symm_apply_eq.trans eq_comm
    _ ↔ ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
          n * Nat.card (ramificationGroup G S 0) := by
      rw [herbrandFun_natCast, div_eq_iff h0]
      norm_cast

/-- `ψℕ(0) = 0`. -/
@[simp]
theorem psiNat_zero : psiNat G S 0 = 0 :=
  (psiNat_eq_iff G S).2 (by simp)

/-- The integral inverse Herbrand function is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat G S) := fun a b hab ↦ by
  have hlt : inverseHerbrandFun G S a < inverseHerbrandFun G S b :=
    inverseHerbrandFun_strictMono G S (Nat.cast_lt.2 hab)
  exact_mod_cast (coe_psiNat G S a).trans_lt (hlt.trans_eq (coe_psiNat G S b).symm)

/-- `n ≤ ψℕ(n)`. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat G S n :=
  (psiNat_strictMono G S).id_le n

/-- `ψℕ(n) ≤ i` if and only if `n ≤ ⌊φ(i)⌋₊`. -/
@[simp]
theorem psiNat_le_iff_le_floor_herbrandFun {n i : ℕ} :
    psiNat G S n ≤ i ↔ n ≤ ⌊herbrandFun G S i⌋₊ := by
  have h0 : 0 ≤ herbrandFun G S i := by
    rw [← herbrandFun_zero G S]
    exact (herbrandFun_strictMono G S).monotone (Nat.cast_nonneg i)
  rw [Nat.le_floor_iff h0, ← Nat.cast_le (α := ℝ), coe_psiNat,
    inverseHerbrandFun_le_iff_le_herbrandFun]

/-! ### Basic properties of the upper numbering -/

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- For `v ≤ -1`, `G^v = ⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ := by
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  have hψ : inverseHerbrandFun G S v ≤ -1 := by
    rw [← inverseHerbrandFun_neg_one G S]
    exact (inverseHerbrandFun_strictMono G S).monotone hv
  exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast hψ))

/-- For `v ≤ 0`, the upper and lower numberings agree. -/
theorem upperRamificationGroup_of_le_zero {v : ℝ} (h₀ : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  by_cases h₁ : -1 ≤ v
  · rw [upperRamificationGroup_def, inverseHerbrandFun_of_neg_one_le_of_le_zero G S h₁ h₀]
  · have hv : v ≤ -1 := by linarith
    rw [upperRamificationGroup_eq_top_of_le_neg_one G S hv, ramificationGroupReal_def,
      ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by exact_mod_cast hv))]

/-- `G^0 = G_0`. -/
@[simp]
theorem upperRamificationGroup_zero :
    upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_zero, ← Int.cast_zero,
    ramificationGroupReal_intCast]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S
    ((inverseHerbrandFun_strictMono G S).monotone h)

/-- At a natural number `n`, `G^n = G_{ψℕ(n)}`. -/
@[simp]
theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S n = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast,
    ramificationGroupReal_intCast]

/-- For a faithful action of a finite group on a Noetherian local ring, the upper ramification
groups vanish from some index on. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ N : ℝ, ∀ v : ℝ, N ≤ v → upperRamificationGroup G S v = ⊥ := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  refine ⟨herbrandFun G S N, fun v hv ↦ ?_⟩
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  refine hN _ (Int.le_ceil_iff.2 ?_)
  have hle : (N : ℝ) ≤ inverseHerbrandFun G S v :=
    (le_inverseHerbrandFun_iff_herbrandFun_le G S).2 hv
  linarith

/-- **Subgroup trace in the upper numbering.** For any subgroup `H ≤ G` acting on `S` by
restriction and any real `u`, `H ∩ G^u = H^{φ_H(ψ_G(u))}`. Neither normality of `H` nor a discrete
valuation ring structure on `S` is needed. -/
@[simp]
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal,
    upperRamificationGroup_herbrandFun]

/-! ### Jumps of the lower and upper filtrations -/

/-- The Herbrand function carries lower jumps bijectively to upper jumps. -/
@[simp]
theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [lowerJump_iff]
  constructor
  · intro h v huv
    have h' := h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
    simpa only [upperRamificationGroup_herbrandFun] using h'
  · intro h w hvw
    have h' : u < inverseHerbrandFun G S w := by
      have hw := inverseHerbrandFun_strictMono G S hvw
      rwa [inverseHerbrandFun_herbrandFun] at hw
    simpa only [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun] using h _ h'

/-- The inverse Herbrand function carries upper jumps bijectively to lower jumps. -/
@[simp]
theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa only [herbrandFun_inverseHerbrandFun] using
    (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

end Finite

end TauCeti.IsLocalRing

/-! ### Transport along equivariant ring isomorphisms -/

namespace MulEquiv

open TauCeti.IsLocalRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {G' : Type*} [Group G'] {S' : Type*} [CommRing S'] [IsLocalRing S'] [MulSemiringAction G' S']

/-- An equivariant ring isomorphism preserves the Herbrand function. -/
theorem herbrandFun_eq_of_equiv (φ : G ≃* G') (f : S ≃+* S')
    (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x) (u : ℝ) :
    herbrandFun G S u = herbrandFun G' S' u := by
  have hcard (i : ℤ) :
      Nat.card (ramificationGroup G S i) = Nat.card (ramificationGroup G' S' i) := by
    rw [← φ.map_ramificationGroup_of_equiv f hf i]
    exact Nat.card_congr (φ.subgroupMap (ramificationGroup G S i)).toEquiv
  rw [herbrandFun_def, herbrandFun_def]
  congr 1 with t
  rw [ramificationGroupReal_def, ramificationGroupReal_def, hcard, hcard]

/-- An equivariant ring isomorphism preserves the inverse Herbrand function. -/
theorem inverseHerbrandFun_eq_of_equiv (φ : G ≃* G') (f : S ≃+* S')
    (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun G' S' v := by
  simp only [inverseHerbrandFun_def, φ.herbrandFun_eq_of_equiv f hf]

/-- An equivariant ring isomorphism maps each upper ramification group onto the target one. -/
theorem map_upperRamificationGroup_of_equiv (φ : G ≃* G') (f : S ≃+* S')
    (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x) (v : ℝ) :
    (upperRamificationGroup G S v).map φ.toMonoidHom = upperRamificationGroup G' S' v := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    φ.inverseHerbrandFun_eq_of_equiv f hf, ramificationGroupReal_def, ramificationGroupReal_def,
    φ.map_ramificationGroup_of_equiv f hf]

end MulEquiv
