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

/-!
# The Herbrand function of a group acting on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with lower ramification groups
`G_t = TauCeti.IsLocalRing.ramificationGroupReal G S t`, the groups `G_{⌈t⌉}` of the elements
acting trivially on `S ⧸ 𝔪 ^ (⌈t⌉ + 1)`. The **Herbrand function** of the action is

`φ(u) = ∫_0^u #G_t / #G_0 dt`,

its **inverse Herbrand function** `ψ(v)` is the least `u` with `v ≤ φ(u)`, and the **upper
numbering** of the ramification groups is `G^v = G_{ψ(v)}`. For a finite Galois extension `L/K`
of fields complete for a discrete valuation, with `G = Gal(L/K)` acting on the integer ring of
`L`, these are the classical `φ_{L/K}`, `ψ_{L/K}` and `Gal(L/K)^v`; nothing here uses
completeness, a discrete valuation, or finiteness of the residue field.

For finite `G` the integrand is an antitone step function, constant on each interval `(i - 1, i]`
with `i : ℤ`, equal to `#G / #G_0` on `(-∞, -1]` and to `1` on `(-1, 0]`, and bounded below by
`1 / #G_0`. Hence `φ` is a continuous, strictly increasing, concave, piecewise linear bijection of
`ℝ`, the identity on `[-1, 0]`, with the finite-sum formula `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0` at
every natural number `m`. It is packaged as the order automorphism `herbrandOrderIso G S` of `ℝ`,
whose inverse is `ψ`. Only values on `[-1, ∞)` carry arithmetic meaning, and `φ` and `ψ` preserve
that half-line. Although `φ(m)` need not be an integer, `ψ(n)` is a natural number for every
natural number `n`, since `#G_{m+1}` divides `#G_i` for `i ≤ m + 1`.

The upper numbering is related to the lower one by `G^{φ(u)} = G_u`; its point, the compatibility
`(G / H)^v = G^v H / H` with quotients, is not proved here.

## Main definitions

* `TauCeti.IsLocalRing.herbrandFun G S`: the Herbrand function `φ`.
* `TauCeti.IsLocalRing.inverseHerbrandFun G S`: the inverse Herbrand function `ψ`.
* `TauCeti.IsLocalRing.upperRamificationGroup G S v`: the upper ramification group `G^v`.
* `TauCeti.IsLocalRing.herbrandOrderIso G S`: `φ` as an order automorphism of `ℝ`, for finite `G`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_strictMono`, `TauCeti.IsLocalRing.continuous_herbrandFun`,
  `TauCeti.IsLocalRing.concaveOn_herbrandFun`: `φ` is strictly increasing, continuous and
  concave.
* `TauCeti.IsLocalRing.herbrandFun_sub_herbrandFun_of_forall_eq`: `φ` is affine of slope
  `#H / #G_0` on an interval where the filtration is constantly `H`.
* `TauCeti.IsLocalRing.herbrandFun_eq_self_of_mem_Icc`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_eq_self_of_mem_Icc`: `φ` and `ψ` are the identity on
  `[-1, 0]`.
* `TauCeti.IsLocalRing.herbrandFun_of_mem_Icc`, `TauCeti.IsLocalRing.herbrandFun_natCast`: the
  finite-sum formula.
* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_herbrandFun`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
* `TauCeti.IsLocalRing.inverseHerbrandFun_natCast_eq_natCast_iff`,
  `TauCeti.IsLocalRing.exists_inverseHerbrandFun_natCast_eq_natCast`: `ψ(n) = m` exactly when
  `#G_1 + ⋯ + #G_m = n · #G_0`, and `ψ(n)` is a natural number.
* `TauCeti.IsLocalRing.upperRamificationGroup_herbrandFun`: `G^{φ(u)} = G_u`.
* `TauCeti.IsLocalRing.upperRamificationGroup_eq_of_herbrandFun_lt_of_le`: `G^v = G_i` for
  `φ(i - 1) < v ≤ φ(i)`.
* `TauCeti.IsLocalRing.exists_forall_upperRamificationGroup_eq_bot`: for a faithful action on a
  Noetherian local ring, `G^v = 1` for all large `v`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, formula (5) and the properties of `φ` and `ψ`, for totally ramified
  extensions with algebraically closed residue field.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral Filter

namespace TauCeti.IsLocalRing

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-! ### Definitions -/

/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` of a group `G` acting on a local ring
`S`, where `G_t = ramificationGroupReal G S t` is the lower ramification group `G_{⌈t⌉}`. For
`t > -1` the group `G_t` lies in `G_0`, so the integrand is `1 / [G_0 : G_t]` there. Only the
values on `[-1, ∞)` carry arithmetic meaning; for finite `G` the function is an order
automorphism of `ℝ` (`herbrandOrderIso`). -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- The integral formula defining the Herbrand function. -/
theorem herbrandFun_def (u : ℝ) :
    herbrandFun G S u = ∫ t in (0 : ℝ)..u,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  (rfl)

/-- The **inverse Herbrand function** `ψ(v)`, the least `u` with `v ≤ φ(u)`. For finite `G` it
is the inverse of the Herbrand function (`herbrandOrderIso_symm_apply`). -/
def inverseHerbrandFun (v : ℝ) : ℝ :=
  sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- The defining formula of the inverse Herbrand function. -/
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} :=
  (rfl)

/-- The **upper ramification group** `G^v = G_{ψ(v)}` of a group `G` acting on a local ring `S`,
the numbering under which `G^{φ(u)} = G_u` (`upperRamificationGroup_herbrandFun`). -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

/-- The upper ramification group at `v` is the lower one at `ψ(v)`. -/
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

/-- Every upper ramification group is normal. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

/-- The Herbrand function vanishes at `0`. -/
@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 :=
  integral_same

/-! ### The integrand -/

section Finite

variable [Finite G]

/-- The integrand `#G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  Nat.card (ramificationGroupReal G S t) / Nat.card (ramificationGroup G S 0)

private theorem natCard_ramificationGroup_zero_pos :
    (0 : ℝ) < Nat.card (ramificationGroup G S 0) := by
  exact_mod_cast Nat.card_pos

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun s t hst ↦ by
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
  exact_mod_cast Nat.card_pos

/-! ### The Herbrand function -/

/-- The increment of the Herbrand function over `[a, b]` is the integral of `#G_t / #G_0`. -/
theorem herbrandFun_sub_herbrandFun (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a = ∫ t in a..b,
      (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-- On an interval `[a, b]` over which the lower ramification filtration is constantly `H`, that
is `G_t = H` for every `a < t ≤ b`, the Herbrand function is affine of slope `#H / #G_0`. -/
theorem herbrandFun_sub_herbrandFun_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub_herbrandFun, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [h t ht.1 ht.2]

/-- On an interval `[a, b] ⊆ [i - 1, i]` with `i : ℤ` the Herbrand function is affine of slope
`#G_i / #G_0`. -/
theorem herbrandFun_sub_herbrandFun_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_herbrandFun_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)

private theorem div_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub_herbrandFun, div_eq_mul_inv, ← smul_eq_mul,
    ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t _ ↦ inv_le_herbrandDensity G S t

private theorem herbrandFun_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandFun G S b - herbrandFun G S a ≤ (b - a) * herbrandDensity G S a := by
  rw [herbrandFun_sub_herbrandFun, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity G S a b) intervalIntegrable_const
    fun t ht ↦ herbrandDensity_antitone G S ht.1

private theorem mul_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G S b ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub_herbrandFun, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun t ht ↦ herbrandDensity_antitone G S ht.2

/-- The Herbrand function of a finite group is strictly increasing. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun a b hab ↦ by
  have h := div_le_herbrandFun_sub G S hab.le
  have : 0 < (b - a) / Nat.card (ramificationGroup G S 0) :=
    div_pos (sub_pos.2 hab) (natCard_ramificationGroup_zero_pos G S)
  linarith

/-- The Herbrand function of a finite group is continuous. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- The Herbrand function of a finite group is **concave**: the integrand `#G_t / #G_0` is
antitone. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ univ (herbrandFun G S) :=
  concaveOn_of_slope_anti_adjacent convex_univ fun {u v w} _ _ huv hvw ↦
    calc (herbrandFun G S w - herbrandFun G S v) / (w - v)
        ≤ herbrandDensity G S v :=
          (div_le_iff₀' (sub_pos.2 hvw)).2 (herbrandFun_sub_le_mul G S hvw.le)
      _ ≤ (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
          (le_div_iff₀' (sub_pos.2 huv)).2 (mul_le_herbrandFun_sub G S huv.le)

/-- The Herbrand function is the identity on `[-1, 0]`. -/
theorem herbrandFun_eq_self_of_mem_Icc {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 0) :
    herbrandFun G S u = u := by
  have h := herbrandFun_sub_herbrandFun_of_le G S (i := 0) (by simpa using hu.1) hu.2 (by simp)
  rw [div_self (natCard_ramificationGroup_zero_pos G S).ne', herbrandFun_zero] at h
  linarith

/-- The Herbrand function fixes `-1`. -/
@[simp]
theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_eq_self_of_mem_Icc G S ⟨le_rfl, by norm_num⟩

/-- The Herbrand function is the identity on `[-1, u]` as long as the lower ramification
filtration is constant from `0` through `u`. For `u ≤ 0` the hypothesis `h` is vacuous and the
conclusion is `herbrandFun_eq_self_of_mem_Icc`. -/
theorem herbrandFun_eq_self_of_forall_eq {u : ℝ} (hu : -1 ≤ u)
    (h : ∀ t : ℝ, 0 < t → t ≤ u → ramificationGroupReal G S t = ramificationGroup G S 0) :
    herbrandFun G S u = u := by
  rcases le_total u 0 with hu₀ | hu₀
  · exact herbrandFun_eq_self_of_mem_Icc G S ⟨hu, hu₀⟩
  have h' := herbrandFun_sub_herbrandFun_of_forall_eq G S hu₀ h
  rw [div_self (natCard_ramificationGroup_zero_pos G S).ne', herbrandFun_zero] at h'
  linarith

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) :
    herbrandFun G S u =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
        (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  have hstep := herbrandFun_sub_herbrandFun_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith)
    h₁ (by push_cast; linarith)
  induction m generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandFun_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ m ih =>
    have hm := ih (u := (m + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_herbrandFun_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith)
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

/-- The Herbrand function of a finite group is a bijection of `ℝ`: its slope is at least
`1 / #G_0` everywhere. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := by
  have hg := natCard_ramificationGroup_zero_pos G S
  -- The linear bounds `φ(u) ≥ u / #G_0` for `u ≥ 0` and `φ(u) ≤ u / #G_0` for `u ≤ 0`.
  have htop : Tendsto (herbrandFun G S) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const hg)
    filter_upwards [eventually_ge_atTop 0] with u hu
    simpa only [id, herbrandFun_zero, sub_zero] using div_le_herbrandFun_sub G S hu
  have hbot : Tendsto (herbrandFun G S) atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.atBot_div_const hg)
    filter_upwards [eventually_le_atBot 0] with u hu
    have h := div_le_herbrandFun_sub G S hu
    rw [herbrandFun_zero, zero_sub, zero_sub, neg_div, neg_le_neg_iff] at h
    exact h
  exact (continuous_herbrandFun G S).surjective htop hbot

/-- The Herbrand function of a finite group as an order automorphism of `ℝ`. Its forward map is
`herbrandFun G S` and its inverse is `inverseHerbrandFun G S`. -/
def herbrandOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (herbrandFun G S) (herbrandFun_strictMono G S)
    (herbrandFun_surjective G S)

@[simp]
theorem herbrandOrderIso_apply (u : ℝ) : herbrandOrderIso G S u = herbrandFun G S u :=
  (rfl)
@[simp]
theorem herbrandOrderIso_symm_apply (v : ℝ) :
    (herbrandOrderIso G S).symm v = inverseHerbrandFun G S v := by
  have hset : {u : ℝ | v ≤ herbrandFun G S u} = Ici ((herbrandOrderIso G S).symm v) := by
    ext u
    rw [mem_ofPred_eq, mem_Ici, ← herbrandOrderIso_apply, OrderIso.symm_apply_le]
  rw [inverseHerbrandFun_def, hset, csInf_Ici]

/-- The inverse of `herbrandOrderIso G S` is the inverse Herbrand function. -/
theorem coe_herbrandOrderIso_symm : ⇑(herbrandOrderIso G S).symm = inverseHerbrandFun G S :=
  funext (herbrandOrderIso_symm_apply G S)

/-! ### The inverse Herbrand function -/

/-- The Herbrand function undoes its inverse: `φ(ψ(v)) = v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  rw [← herbrandOrderIso_symm_apply, ← herbrandOrderIso_apply, OrderIso.apply_symm_apply]

/-- The inverse Herbrand function undoes the Herbrand function: `ψ(φ(u)) = u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u := by
  rw [← herbrandOrderIso_symm_apply, ← herbrandOrderIso_apply, OrderIso.symm_apply_apply]

variable {G S} in
/-- `ψ(v) ≤ u` exactly when `v ≤ φ(u)`. -/
theorem inverseHerbrandFun_le_iff {u v : ℝ} :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u := by
  rw [← herbrandOrderIso_symm_apply, OrderIso.symm_apply_le, herbrandOrderIso_apply]

variable {G S} in
/-- `u ≤ ψ(v)` exactly when `φ(u) ≤ v`. -/
theorem le_inverseHerbrandFun_iff {u v : ℝ} :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v := by
  rw [← herbrandOrderIso_symm_apply, OrderIso.le_symm_apply, herbrandOrderIso_apply]

variable {G S} in
/-- `u < ψ(v)` exactly when `φ(u) < v`. -/
theorem lt_inverseHerbrandFun_iff {u v : ℝ} :
    u < inverseHerbrandFun G S v ↔ herbrandFun G S u < v := by
  rw [← herbrandOrderIso_symm_apply, OrderIso.lt_symm_apply, herbrandOrderIso_apply]

/-- The inverse Herbrand function of a finite group is strictly increasing. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) :=
  coe_herbrandOrderIso_symm G S ▸ (herbrandOrderIso G S).symm.strictMono

/-- The inverse Herbrand function of a finite group is continuous. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) :=
  coe_herbrandOrderIso_symm G S ▸ (herbrandOrderIso G S).symm.continuous

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
theorem inverseHerbrandFun_eq_self_of_mem_Icc {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_eq_self_of_mem_Icc G S hv]
  exact inverseHerbrandFun_herbrandFun G S v

/-- The inverse Herbrand function fixes `-1`. -/
@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 :=
  inverseHerbrandFun_eq_self_of_mem_Icc G S ⟨le_rfl, by norm_num⟩

variable {G S} in
/-- The Herbrand function preserves the half-line `[-1, ∞)`: `-1 ≤ φ(u) ↔ -1 ≤ u`. -/
@[simp]
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  conv_lhs => rw [← herbrandFun_neg_one G S]
  exact (herbrandFun_strictMono G S).le_iff_le

variable {G S} in
/-- The inverse Herbrand function preserves the half-line `[-1, ∞)`: `-1 ≤ ψ(v) ↔ -1 ≤ v`. -/
@[simp]
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  conv_lhs => rw [← inverseHerbrandFun_neg_one G S]
  exact (inverseHerbrandFun_strictMono G S).le_iff_le

variable {G S} in
/-- At natural numbers, `ψ(n) = m` exactly when `#G_1 + ⋯ + #G_m = n · #G_0`, that is when
`φ(m) = n`. -/
theorem inverseHerbrandFun_natCast_eq_natCast_iff {n m : ℕ} :
    inverseHerbrandFun G S n = m ↔
      ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
        n * Nat.card (ramificationGroup G S 0) := by
  rw [← herbrandOrderIso_symm_apply, OrderIso.symm_apply_eq, herbrandOrderIso_apply,
    herbrandFun_natCast, eq_comm, div_eq_iff (natCard_ramificationGroup_zero_pos G S).ne']
  norm_cast

/-- The inverse Herbrand function takes natural numbers to natural numbers, although the Herbrand
function need not: `#G_{m+1}` divides `#G_i` for `i ≤ m + 1`. -/
theorem exists_inverseHerbrandFun_natCast_eq_natCast (n : ℕ) :
    ∃ m : ℕ, inverseHerbrandFun G S n = m := by
  set u : ℝ := inverseHerbrandFun G S n
  have hu : 0 ≤ u := by
    rw [← inverseHerbrandFun_eq_self_of_mem_Icc G S (v := 0) ⟨by norm_num, le_rfl⟩]
    exact (inverseHerbrandFun_strictMono G S).monotone (Nat.cast_nonneg n)
  set m := ⌊u⌋₊
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le hu
  have hm₂ : u < m + 1 := Nat.lt_floor_add_one u
  refine ⟨m, ?_⟩
  -- The finite-sum formula at `u = ψ(n)`, with `φ(u) = n` and denominators cleared.
  have hφ := herbrandFun_of_mem_Icc G S m hm₁ hm₂.le
  rw [herbrandFun_inverseHerbrandFun,
    eq_div_iff (natCard_ramificationGroup_zero_pos G S).ne'] at hφ
  set g : ℤ → ℕ := fun i ↦ Nat.card (ramificationGroup G S i)
  -- `#G_{m+1}` divides `n #G_0 - (#G_1 + ⋯ + #G_m)`.
  have hdvd : ∀ i : ℤ, i ≤ (m + 1 : ℕ) → g (m + 1 : ℕ) ∣ g i := fun i hi ↦
    Subgroup.card_dvd_of_le (ramificationGroup_antitone G S hi)
  have h₁ : g (m + 1 : ℕ) ∣ n * g 0 := dvd_mul_of_dvd_right (hdvd 0 (by omega)) _
  have h₂ : g (m + 1 : ℕ) ∣ ∑ i ∈ Finset.Icc 1 m, g i := Finset.dvd_sum fun i hi ↦
    hdvd i (by have := (Finset.mem_Icc.1 hi).2; omega)
  obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.2 h₁).sub (Int.natCast_dvd_natCast.2 h₂)
  have hcR : (n : ℝ) * g 0 - ∑ i ∈ Finset.Icc 1 m, (g i : ℝ) = g (m + 1 : ℕ) * c := by
    exact_mod_cast hc
  -- Hence `u - m` is an integer `c` with `0 ≤ c < 1`.
  have hg : (g (m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcu : u - m = c := mul_right_cancel₀ hg <|
    (by rw [← hcR]; linarith : (u - m) * g (m + 1 : ℕ) = g (m + 1 : ℕ) * c).trans (mul_comm _ _)
  have hc0 : 0 ≤ c := by exact_mod_cast (hcu ▸ sub_nonneg.2 hm₁ : (0 : ℝ) ≤ c)
  have hc1 : c < 1 := by exact_mod_cast (hcu ▸ by linarith : (c : ℝ) < 1)
  have hc_zero : c = 0 := by omega
  rw [hc_zero, Int.cast_zero, sub_eq_zero] at hcu
  exact hcu

/-! ### The upper numbering -/

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦
    ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)

/-- Up to `0` the upper and lower numberings agree. Below `-1` both are all of `G`. -/
theorem upperRamificationGroup_of_le_zero {v : ℝ} (hv : v ≤ 0) :
    upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rcases le_total (-1) v with hv₁ | hv₁
  · rw [upperRamificationGroup_def, inverseHerbrandFun_eq_self_of_mem_Icc G S ⟨hv₁, hv⟩]
  have htop {w : ℝ} (hw : w ≤ -1) : ramificationGroupReal G S w = ⊤ := by
    rw [ramificationGroupReal_def]
    exact ramificationGroup_eq_top_of_le_neg_one G S (Int.ceil_le.2 (by simpa using hw))
  rw [upperRamificationGroup_def, htop hv₁, htop ?_]
  rw [← inverseHerbrandFun_neg_one G S]
  exact (inverseHerbrandFun_strictMono G S).monotone hv₁

/-- For `φ(i - 1) < v ≤ φ(i)` with `i : ℤ`, the upper ramification group `G^v` is the lower
ramification group `G_i`. -/
theorem upperRamificationGroup_eq_of_herbrandFun_lt_of_le {i : ℤ} {v : ℝ}
    (hv₁ : herbrandFun G S (i - 1) < v) (hv₂ : v ≤ herbrandFun G S i) :
    upperRamificationGroup G S v = ramificationGroup G S i := by
  rw [upperRamificationGroup_def]
  exact ramificationGroupReal_eq_of_sub_one_lt_of_le G S (lt_inverseHerbrandFun_iff.2 hv₁)
    (inverseHerbrandFun_le_iff.2 hv₂)

/-- For a faithful action of a finite group on a Noetherian local ring, the upper ramification
groups are trivial from some index on. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ v : ℝ, ∀ w : ℝ, v ≤ w → upperRamificationGroup G S w = ⊥ := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  refine ⟨herbrandFun G S N, fun w hw ↦ ?_⟩
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact hN _ (Int.cast_le.1 ((le_inverseHerbrandFun_iff.2 hw).trans (Int.le_ceil _)))

end Finite

end TauCeti.IsLocalRing
