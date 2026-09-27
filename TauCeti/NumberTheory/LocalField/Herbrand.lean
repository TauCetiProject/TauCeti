/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationGroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Herbrand function and the upper numbering

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with lower ramification
groups `G_u = G_{⌈u⌉}` of `G = Gal(L/K)` indexed by real `u ≥ -1`. The **Herbrand function** is

`φ_{L/K}(u) = ∫_0^u dt / [G_0 : G_t]`,

for `u ≥ -1`. Since `G_t` is a subgroup of `G_0` for `t > -1`, the integrand is
`#G_t / #G_0`; it equals `1` on `(-1, 0]`, so `φ(u) = u` for `-1 ≤ u ≤ 0`. On each interval
`[m, m + 1]` with `m : ℕ` the function `φ` is affine of slope `#G_{m+1} / #G_0`, which gives the
finite-sum formula

`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`.

The integrand is positive and bounded below by `1 / #G_0`, so `φ` is a strictly increasing
continuous bijection of `[-1, ∞)` onto itself. This file packages it as an order isomorphism
`herbrandOrderIso K L` of the domain `RamificationIndexDomain = [-1, ∞)`, whose forward map is
`herbrand K L` and whose inverse is the inverse Herbrand function `inverseHerbrand K L`, usually
written `ψ_{L/K}`. Keeping the domain in the type means that no statement concerns a value
below `-1`.

The **upper numbering** of the ramification groups is `G^v = G_{ψ(v)}`, so that
`G^{φ(u)} = G_u`. Its point is the compatibility with quotients, `(G/H)^v = G^v H / H` for `H`
normal, which the lower numbering lacks; that theorem is not proved here.

The Herbrand function and the upper numbering are defined only for Galois `L/K`: for a
non-Galois extension the automorphism group does not carry the ramification of `L/K`, and the
classical `φ_{L/K}` is instead defined through a Galois closure.

## Main definitions

* `TauCeti.LocalFieldsRamification.RamificationIndexDomain`: the interval `[-1, ∞)`.
* `TauCeti.LocalFieldsRamification.herbrandOrderIso`: the Herbrand function as an order
  automorphism of `[-1, ∞)`.
* `TauCeti.LocalFieldsRamification.herbrand`, `TauCeti.LocalFieldsRamification.inverseHerbrand`:
  its forward map `φ_{L/K}` and its inverse `ψ_{L/K}`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup`: the upper-numbering ramification
  group `G^v = G_{ψ(v)}`.

## Main results

* `TauCeti.LocalFieldsRamification.coe_herbrand`: the integral formula defining `φ`.
* `TauCeti.LocalFieldsRamification.coe_herbrand_of_mem_Icc` and
  `TauCeti.LocalFieldsRamification.coe_herbrand_of_coe_eq_natCast`: the finite-sum formula.
* `TauCeti.LocalFieldsRamification.herbrand_of_coe_le_zero` and
  `TauCeti.LocalFieldsRamification.inverseHerbrand_of_coe_le_zero`: `φ` and `ψ` are the identity
  on `[-1, 0]`.
* `TauCeti.LocalFieldsRamification.herbrand_inverseHerbrand` and
  `TauCeti.LocalFieldsRamification.inverseHerbrand_herbrand`: `φ ∘ ψ = id` and `ψ ∘ φ = id`.
* `TauCeti.LocalFieldsRamification.herbrand_slope_anti_adjacent`: `φ` is concave.
* `TauCeti.LocalFieldsRamification.continuous_herbrand`,
  `TauCeti.LocalFieldsRamification.herbrand_strictMono` and their counterparts for `ψ`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_herbrand`: `G^{φ(u)} = G_u`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_antitone`: the upper filtration
  decreases, and each `G^v` is normal.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace TauCeti.LocalFieldsRamification

/-- The interval `[-1, ∞)`, the domain of the Herbrand function and of its inverse. The lower
ramification groups are indexed by real numbers `u ≥ -1`, and `G_u` is the whole automorphism
group for `u ≤ -1`. -/
abbrev RamificationIndexDomain : Set ℝ := Ici (-1 : ℝ)

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-! ### The integrand and its primitive on the real line -/

/-- The integrand `1 / [G_0 : G_t] = #G_t / #G_0` of the Herbrand function. -/
private def herbrandDensity (t : ℝ) : ℝ :=
  Nat.card (lowerRamificationGroupReal K L t) / Nat.card (lowerRamificationGroup K L 0)

private theorem natCard_lowerRamificationGroup_pos (i : ℤ) :
    0 < Nat.card (lowerRamificationGroup K L i) :=
  Nat.card_pos

private theorem herbrandDensity_antitone : Antitone (herbrandDensity K L) := fun s t hst ↦ by
  unfold herbrandDensity
  gcongr
  exact Subgroup.card_le_of_le (lowerRamificationGroupReal_antitone K L hst)

private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity K L) volume a b :=
  (herbrandDensity_antitone K L).intervalIntegrable

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ ≤ herbrandDensity K L t := by
  rw [herbrandDensity, div_eq_mul_inv]
  refine le_mul_of_one_le_left (by positivity) ?_
  rw [lowerRamificationGroupReal_def]
  exact_mod_cast natCard_lowerRamificationGroup_pos K L _

/-- The Herbrand function on the whole real line, as the primitive of `herbrandDensity`; only its
values on `[-1, ∞)` are meaningful, and only those are exported through `herbrandOrderIso`. -/
private def herbrandReal (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, herbrandDensity K L t

private theorem herbrandReal_def (u : ℝ) :
    herbrandReal K L u = ∫ t in (0 : ℝ)..u,
      (Nat.card (lowerRamificationGroupReal K L t) : ℝ) / Nat.card (lowerRamificationGroup K L 0) :=
  rfl

private theorem herbrandReal_zero : herbrandReal K L 0 = 0 :=
  integral_same

private theorem herbrandReal_sub (a b : ℝ) :
    herbrandReal K L b - herbrandReal K L a = ∫ t in a..b, herbrandDensity K L t :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity K L 0 b)
    (intervalIntegrable_herbrandDensity K L 0 a)

/-- On an interval `[a, b] ⊆ [i - 1, i]` the Herbrand function is affine of slope
`#G_i / #G_0`. -/
private theorem herbrandReal_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) :
    herbrandReal K L b - herbrandReal K L a =
      (b - a) * (Nat.card (lowerRamificationGroup K L i) /
        Nat.card (lowerRamificationGroup K L 0)) := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht
  rw [herbrandDensity,
    lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K L (ha.trans_lt ht.1) (ht.2.trans hb)]

private theorem div_sub_le_herbrandReal_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (lowerRamificationGroup K L 0) ≤
      herbrandReal K L b - herbrandReal K L a := by
  rw [herbrandReal_sub, div_eq_mul_inv, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity K L a b)
    fun t _ ↦ inv_le_herbrandDensity K L t

private theorem herbrandReal_sub_le_mul {a b : ℝ} (hab : a ≤ b) :
    herbrandReal K L b - herbrandReal K L a ≤ (b - a) * herbrandDensity K L a := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab (intervalIntegrable_herbrandDensity K L a b) intervalIntegrable_const
    fun t ht ↦ herbrandDensity_antitone K L ht.1

private theorem mul_le_herbrandReal_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity K L b ≤ herbrandReal K L b - herbrandReal K L a := by
  rw [herbrandReal_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity K L a b)
    fun t ht ↦ herbrandDensity_antitone K L ht.2

private theorem herbrandReal_strictMono : StrictMono (herbrandReal K L) := fun a b hab ↦ by
  have h := div_sub_le_herbrandReal_sub K L hab.le
  have : 0 < (b - a) / Nat.card (lowerRamificationGroup K L 0) := by
    have := natCard_lowerRamificationGroup_pos K L 0
    have : 0 < b - a := sub_pos.2 hab
    positivity
  linarith

private theorem herbrandReal_continuous : Continuous (herbrandReal K L) :=
  continuous_primitive (intervalIntegrable_herbrandDensity K L) 0

private theorem herbrandReal_of_le_zero {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandReal K L u = u := by
  have h := herbrandReal_sub_of_le K L (i := 0) (by simpa using h₁) h₀ (by simp)
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast (natCard_lowerRamificationGroup_pos K L 0).ne'
  rw [div_self h0, herbrandReal_zero] at h
  linarith

private theorem neg_one_le_herbrandReal {u : ℝ} (hu : -1 ≤ u) : -1 ≤ herbrandReal K L u := by
  rw [← herbrandReal_of_le_zero K L le_rfl (by norm_num)]
  exact (herbrandReal_strictMono K L).monotone hu

private theorem exists_herbrandReal_eq {y : ℝ} (hy : -1 ≤ y) :
    ∃ u, -1 ≤ u ∧ herbrandReal K L u = y := by
  set g : ℝ := (Nat.card (lowerRamificationGroup K L 0) : ℝ)
  have hg : 1 ≤ g := Nat.one_le_cast.2 (natCard_lowerRamificationGroup_pos K L 0)
  set b := -1 + (y + 1) * g
  have hb : -1 ≤ b := by nlinarith
  have hφb : y ≤ herbrandReal K L b := by
    have h := div_sub_le_herbrandReal_sub K L hb
    have hb_sub : b - -1 = (y + 1) * g := by
      dsimp [b]
      ring
    rw [herbrandReal_of_le_zero K L le_rfl (by norm_num),
      hb_sub, mul_div_cancel_right₀ _ (by positivity)] at h
    linarith
  obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hb (herbrandReal_continuous K L).continuousOn
    ⟨(herbrandReal_of_le_zero K L le_rfl (by norm_num)).trans_le hy, hφb⟩
  exact ⟨u, hu.1, rfl⟩

/-- The Herbrand function as a self-map of `[-1, ∞)`. -/
private def herbrandFun (u : RamificationIndexDomain) : RamificationIndexDomain :=
  ⟨herbrandReal K L u, mem_Ici.2 (neg_one_le_herbrandReal K L u.2)⟩

private theorem herbrandFun_strictMono : StrictMono (herbrandFun K L) :=
  fun _ _ h ↦ Subtype.mk_lt_mk.2 (herbrandReal_strictMono K L h)

private theorem herbrandFun_surjective : Function.Surjective (herbrandFun K L) := fun y ↦ by
  obtain ⟨u, hu, h⟩ := exists_herbrandReal_eq K L y.2
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

/-! ### The Herbrand function and its inverse -/

/-- The **Herbrand function** `φ_{L/K}(u) = ∫_0^u dt / [G_0 : G_t]` of a finite Galois extension
of local fields, as an order automorphism of `[-1, ∞)`. Its inverse is the inverse Herbrand function
`ψ_{L/K}`. The integral formula is `coe_herbrand`. The construction does not use `IsGalois`;
the hypothesis restricts the Herbrand function to the Galois case, where it is meaningful. -/
def herbrandOrderIso [_hGal : IsGalois K L] : RamificationIndexDomain ≃o RamificationIndexDomain :=
  StrictMono.orderIsoOfSurjective (herbrandFun K L) (herbrandFun_strictMono K L)
    (herbrandFun_surjective K L)

variable [IsGalois K L]

/-- The **Herbrand function** `φ_{L/K}`, the forward map of `herbrandOrderIso K L`. -/
def herbrand (u : RamificationIndexDomain) : RamificationIndexDomain :=
  herbrandOrderIso K L u

/-- The **inverse Herbrand function** `ψ_{L/K}`, the inverse of `herbrandOrderIso K L`. -/
def inverseHerbrand (v : RamificationIndexDomain) : RamificationIndexDomain :=
  (herbrandOrderIso K L).symm v

@[simp]
theorem herbrandOrderIso_apply (u : RamificationIndexDomain) :
    herbrandOrderIso K L u = herbrand K L u :=
  (rfl)

@[simp]
theorem herbrandOrderIso_symm_apply (v : RamificationIndexDomain) :
    (herbrandOrderIso K L).symm v = inverseHerbrand K L v :=
  (rfl)

/-- The integral formula for the Herbrand function:
`φ_{L/K}(u) = ∫_0^u #G_t / #G_0 dt`. For `t > -1` the group `G_t` is a subgroup of `G_0` and
`#G_t / #G_0 = 1 / [G_0 : G_t]`, so this holds almost everywhere on the interval of integration. -/
theorem coe_herbrand (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = ∫ t in (0 : ℝ)..u,
      (Nat.card (lowerRamificationGroupReal K L t) : ℝ) /
        Nat.card (lowerRamificationGroup K L 0) := by
  rw [← herbrandOrderIso_apply, herbrandOrderIso, StrictMono.coe_orderIsoOfSurjective]
  exact herbrandReal_def K L u

private theorem coe_herbrand_eq_herbrandReal (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = herbrandReal K L u :=
  (coe_herbrand K L u).trans (herbrandReal_def K L u).symm

/-- The Herbrand function undoes its inverse: `φ(ψ(v)) = v`. -/
@[simp]
theorem herbrand_inverseHerbrand (v : RamificationIndexDomain) :
    herbrand K L (inverseHerbrand K L v) = v :=
  (herbrandOrderIso K L).apply_symm_apply v

/-- The inverse Herbrand function undoes the Herbrand function: `ψ(φ(u)) = u`. -/
@[simp]
theorem inverseHerbrand_herbrand (u : RamificationIndexDomain) :
    inverseHerbrand K L (herbrand K L u) = u :=
  (herbrandOrderIso K L).symm_apply_apply u

/-- The Herbrand function is strictly increasing. -/
theorem herbrand_strictMono : StrictMono (herbrand K L) :=
  (herbrandOrderIso K L).strictMono

/-- The inverse Herbrand function is strictly increasing. -/
theorem inverseHerbrand_strictMono : StrictMono (inverseHerbrand K L) :=
  (herbrandOrderIso K L).symm.strictMono

/-- The Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_herbrand : Continuous (herbrand K L) :=
  (herbrandOrderIso K L).continuous

/-- The inverse Herbrand function is continuous. -/
@[fun_prop]
theorem continuous_inverseHerbrand : Continuous (inverseHerbrand K L) :=
  (herbrandOrderIso K L).symm.continuous

/-- The Herbrand function is **concave**: its slopes over two adjacent intervals decrease. -/
theorem herbrand_slope_anti_adjacent {u v w : RamificationIndexDomain} (huv : u < v)
    (hvw : v < w) :
    ((herbrand K L w : ℝ) - herbrand K L v) / ((w : ℝ) - v) ≤
      ((herbrand K L v : ℝ) - herbrand K L u) / ((v : ℝ) - u) := by
  have huv' : (u : ℝ) < v := huv
  have hvw' : (v : ℝ) < w := hvw
  simp only [coe_herbrand_eq_herbrandReal]
  calc (herbrandReal K L w - herbrandReal K L v) / ((w : ℝ) - v)
      ≤ herbrandDensity K L v :=
        (div_le_iff₀' (sub_pos.2 hvw')).2 (herbrandReal_sub_le_mul K L hvw'.le)
    _ ≤ (herbrandReal K L v - herbrandReal K L u) / ((v : ℝ) - u) :=
        (le_div_iff₀' (sub_pos.2 huv')).2 (mul_le_herbrandReal_sub K L huv'.le)

/-- The Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem herbrand_of_coe_le_zero {u : RamificationIndexDomain} (hu : (u : ℝ) ≤ 0) :
    herbrand K L u = u :=
  Subtype.ext ((coe_herbrand_eq_herbrandReal K L u).trans (herbrandReal_of_le_zero K L u.2 hu))

/-- The inverse Herbrand function is the identity on `[-1, 0]`. -/
@[simp]
theorem inverseHerbrand_of_coe_le_zero {v : RamificationIndexDomain} (hv : (v : ℝ) ≤ 0) :
    inverseHerbrand K L v = v :=
  (herbrandOrderIso K L).symm_apply_eq.2 (herbrand_of_coe_le_zero K L hv).symm

omit [IsGalois K L] in
private theorem herbrandReal_of_mem_Icc (n : ℕ) {u : ℝ} (h₁ : (n : ℝ) ≤ u) (h₂ : u ≤ n + 1) :
    herbrandReal K L u =
      (∑ i ∈ Finset.Icc 1 n, (Nat.card (lowerRamificationGroup K L i) : ℝ) +
        (u - n) * Nat.card (lowerRamificationGroup K L (n + 1 : ℕ))) /
        Nat.card (lowerRamificationGroup K L 0) := by
  have hstep := herbrandReal_sub_of_le K L (i := (n + 1 : ℕ)) (by push_cast; linarith) h₁
    (by push_cast; linarith)
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandReal_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linear_combination hstep
  | succ m ih =>
    have hm := ih (u := (m + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandReal_sub_of_le K L (i := (m + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hm] at hstep
    push_cast at hstep ⊢
    linear_combination hstep

/-- The **finite-sum formula** for the Herbrand function: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem coe_herbrand_of_mem_Icc (m : ℕ) {u : RamificationIndexDomain} (h₁ : (m : ℝ) ≤ u)
    (h₂ : (u : ℝ) ≤ m + 1) :
    (herbrand K L u : ℝ) =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (lowerRamificationGroup K L i) : ℝ) +
        (u - m) * Nat.card (lowerRamificationGroup K L (m + 1 : ℕ))) /
        Nat.card (lowerRamificationGroup K L 0) :=
  (coe_herbrand_eq_herbrandReal K L u).trans (herbrandReal_of_mem_Icc K L m h₁ h₂)

/-- The Herbrand function at a natural number `m`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem coe_herbrand_of_coe_eq_natCast (m : ℕ) {u : RamificationIndexDomain} (hu : (u : ℝ) = m) :
    (herbrand K L u : ℝ) =
      (∑ i ∈ Finset.Icc 1 m, (Nat.card (lowerRamificationGroup K L i) : ℝ)) /
        Nat.card (lowerRamificationGroup K L 0) := by
  rw [coe_herbrand_of_mem_Icc K L m hu.ge (by linarith), hu, sub_self, zero_mul, add_zero]

/-! ### The upper numbering -/

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of a finite Galois extension of
local fields, for `v ≥ -1`, where `ψ = inverseHerbrand K L`. -/
def upperRamificationGroup (v : RamificationIndexDomain) : Subgroup (L ≃ₐ[K] L) :=
  lowerRamificationGroupReal K L (inverseHerbrand K L v)

theorem upperRamificationGroup_def (v : RamificationIndexDomain) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L (inverseHerbrand K L v) :=
  (rfl)

variable {K L} in
/-- Membership in the upper ramification groups: `σ ∈ G^v ↔ σ ∈ G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : RamificationIndexDomain} {σ : L ≃ₐ[K] L} :
    σ ∈ upperRamificationGroup K L v ↔
      σ ∈ lowerRamificationGroupReal K L (inverseHerbrand K L v) := by
  rw [upperRamificationGroup_def]

/-- The upper and lower numberings are related by `G^{φ(u)} = G_u`. -/
@[simp]
theorem upperRamificationGroup_herbrand (u : RamificationIndexDomain) :
    upperRamificationGroup K L (herbrand K L u) = lowerRamificationGroupReal K L u := by
  rw [upperRamificationGroup_def, inverseHerbrand_herbrand]

/-- On `[-1, 0]` the upper and lower numberings agree. -/
@[simp]
theorem upperRamificationGroup_of_coe_le_zero {v : RamificationIndexDomain} (hv : (v : ℝ) ≤ 0) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L v := by
  rw [upperRamificationGroup_def, inverseHerbrand_of_coe_le_zero K L hv]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) :=
  fun _ _ h ↦ lowerRamificationGroupReal_antitone K L ((inverseHerbrand_strictMono K L).monotone h)

/-- Every upper ramification group is normal in the automorphism group. -/
instance instNormalUpperRamificationGroup (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).Normal := by
  rw [upperRamificationGroup_def]
  infer_instance

end TauCeti.LocalFieldsRamification
