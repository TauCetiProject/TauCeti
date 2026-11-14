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
# Herbrand functions and the upper numbering on a local ring

Let a group `G` act by ring automorphisms on a local ring `S`, with real-indexed lower ramification
groups `G_t = ramificationGroupReal G S t = G_{⌈t⌉}`. We define the **Herbrand function**
`herbrandFun G S u = ∫ t in 0..u, #G_t / #G_0`, its inverse
`inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u}`, the **upper ramification groups**
`upperRamificationGroup G S v = G_{inverseHerbrandFun G S v}`, and `UpperJump G S v`. Only values on
`[-1, ∞)` carry ramification meaning.

When `G` is finite, `herbrandFun G S` is a continuous, strictly increasing, piecewise-linear
concave bijection of `ℝ` onto `ℝ` with inverse `inverseHerbrandFun G S`, restricting to an order
automorphism `herbrandOrderIso G S` of `Set.Ici (-1 : ℝ)`. By Lagrange's theorem, `ψ` maps `ℕ` to
`ℕ` (`psiNat G S`), and for every subgroup `H ≤ G`, `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}`
(`subgroupOf_upperRamificationGroup`) with no normality, DVR, or residue-separability assumption.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1, 3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, pp. 127–128.
-/

public section
noncomputable section

open IsLocalRing MeasureTheory Set intervalIntegral

namespace TauCeti.IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` of `G` acting on a local ring `S`
(only values on `[-1, ∞)` carry ramification meaning). -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

/-- Defining integral formula for `herbrandFun`. -/
theorem herbrandFun_def (u : ℝ) : herbrandFun G S u = ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) := (rfl)

/-- The **inverse Herbrand function** `ψ(v) = sInf {u : ℝ | v ≤ φ(u)}`, which is the two-sided
inverse of `herbrandFun` when `G` is finite. -/
def inverseHerbrandFun (v : ℝ) : ℝ := sInf {u : ℝ | v ≤ herbrandFun G S u}

/-- Defining infimum formula for `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} := (rfl)

/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of `G` acting on `S`. -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)

/-- Defining formula `G^v = G_{ψ(v)}` for the upper ramification filtration. -/
theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) := (rfl)

variable {G S} in
/-- Membership in `upperRamificationGroup G S v` is membership in `G_{ψ(v)}`. -/
@[simp]
theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} :
    σ ∈ upperRamificationGroup G S v ↔ σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) :=
  Iff.rfl

/-- Every upper ramification group is normal in `G`. -/
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]; infer_instance

/-- `herbrandFun` vanishes at `0`. -/
@[simp]
theorem herbrandFun_zero : herbrandFun G S 0 = 0 := by rw [herbrandFun_def, integral_same]

/-- An **upper break** of the ramification filtration: `G^v < G^u` for every `v > u`. -/
def UpperJump (u : ℝ) : Prop :=
  ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u

/-- Defining criterion for `UpperJump`. -/
theorem upperJump_iff (u : ℝ) : UpperJump G S u ↔
    ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u := Iff.rfl

end Defs

section Transport

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {H : Type*} [Group H] {T : Type*} [CommRing T] [IsLocalRing T] [MulSemiringAction H T]

/-- If a bijective group homomorphism `φ : G →* H` identifies every lower ramification group on `S`
with the preimage of that on `T`, then `herbrandFun G S` and `herbrandFun H T` agree. -/
theorem herbrandFun_eq_of_ramificationGroup_eq_comap {φ : G →* H} (hφ : Function.Bijective φ)
    (he : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (u : ℝ) :
    herbrandFun G S u = herbrandFun H T u := by
  have hcard : ∀ i : ℤ,
      Nat.card (ramificationGroup G S i) = Nat.card (ramificationGroup H T i) := fun i ↦
    Nat.card_congr ((Equiv.ofBijective φ hφ).subtypeEquiv fun g ↦ by rw [he i]; rfl)
  simp only [herbrandFun_def, ramificationGroupReal_def, hcard]

/-- Under `herbrandFun_eq_of_ramificationGroup_eq_comap`, the inverse Herbrand functions agree. -/
theorem inverseHerbrandFun_eq_of_ramificationGroup_eq_comap {φ : G →* H} (hφ : Function.Bijective φ)
    (he : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H T v := by
  simp only [inverseHerbrandFun_def, herbrandFun_eq_of_ramificationGroup_eq_comap hφ he]

/-- Under `herbrandFun_eq_of_ramificationGroup_eq_comap`, `φ` identifies every upper ramification
group on `S` with the preimage of the corresponding upper ramification group on `T`. -/
theorem upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap {φ : G →* H}
    (hφ : Function.Bijective φ)
    (he : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ) (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H T v).comap φ := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_eq_of_ramificationGroup_eq_comap hφ he, ramificationGroupReal_def,
    ramificationGroupReal_def, he]

/-- Two groups linked by a bijective action-compatible homomorphism have equal `herbrandFun`. -/
theorem herbrandFun_eq_of_smul_eq {φ : G →* H} (hφ : Function.Bijective φ) [MulSemiringAction H S]
    (he : ∀ (g : G) (x : S), g • x = φ g • x) (u : ℝ) : herbrandFun G S u = herbrandFun H S u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap hφ (ramificationGroup_eq_comap_of_smul_eq he) u

/-- Two groups linked by a bijective action-compatible homomorphism have equal
`inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_smul_eq {φ : G →* H} (hφ : Function.Bijective φ)
    [MulSemiringAction H S] (he : ∀ (g : G) (x : S), g • x = φ g • x) (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H S v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap hφ
    (ramificationGroup_eq_comap_of_smul_eq he) v

/-- Two groups linked by a bijective action-compatible homomorphism have preimage-compatible upper
ramification groups. -/
theorem upperRamificationGroup_eq_comap_of_smul_eq {φ : G →* H} (hφ : Function.Bijective φ)
    [MulSemiringAction H S] (he : ∀ (g : G) (x : S), g • x = φ g • x) (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H S v).comap φ :=
  upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap hφ
    (ramificationGroup_eq_comap_of_smul_eq he) v

end Transport

section Finite

variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]

private def herbrandDensity (t : ℝ) : ℝ :=
  (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)

private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun _ _ hst ↦ by
  unfold herbrandDensity; gcongr
  exact Subgroup.card_le_of_le (ramificationGroupReal_antitone G S hst)

private theorem intervalIntegrable_herbrandDensity (a b : ℝ) :
    IntervalIntegrable (herbrandDensity G S) volume a b :=
  (herbrandDensity_antitone G S).intervalIntegrable

private theorem inv_le_herbrandDensity (t : ℝ) :
    (Nat.card (ramificationGroup G S 0) : ℝ)⁻¹ ≤ herbrandDensity G S t := by
  rw [herbrandDensity, div_eq_mul_inv]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.card_pos)

private theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a = ∫ t in a..b, herbrandDensity G S t :=
  integral_interval_sub_left (intervalIntegrable_herbrandDensity G S 0 b)
    (intervalIntegrable_herbrandDensity G S 0 a)

/-- On `[a, b]` where `(a, b]` has constant lower ramification group `H`, `herbrandFun` is affine of
slope `#H / #G_0`. -/
theorem herbrandFun_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hab] at ht; rw [herbrandDensity, h t ht.1 ht.2]

/-- On any subinterval `[a, b] ⊆ [i - 1, i]`, `herbrandFun` is affine of slope `#G_i / #G_0`. -/
theorem herbrandFun_sub_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b) (hb : b ≤ i) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
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
    fun _ ht ↦ herbrandDensity_antitone G S ht.1

private theorem mul_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) * herbrandDensity G S b ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, ← smul_eq_mul, ← intervalIntegral.integral_const]
  exact integral_mono_on hab intervalIntegrable_const (intervalIntegrable_herbrandDensity G S a b)
    fun _ ht ↦ herbrandDensity_antitone G S ht.2

/-- The Herbrand function is strictly increasing on `ℝ`. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun a b hab ↦ by
  have hpos : 0 < (b - a) / Nat.card (ramificationGroup G S 0) :=
    div_pos (sub_pos.2 hab) (Nat.cast_pos.2 Nat.card_pos)
  linarith [div_sub_le_herbrandFun_sub G S hab.le]

/-- The Herbrand function is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (intervalIntegrable_herbrandDensity G S) 0

/-- Slopes of `herbrandFun` over adjacent intervals decrease. -/
theorem herbrandFun_slope_anti_adjacent {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (herbrandFun G S w - herbrandFun G S v) / (w - v) ≤
      (herbrandFun G S v - herbrandFun G S u) / (v - u) :=
  ((div_le_iff₀' (sub_pos.2 hvw)).2 (herbrandFun_sub_le_mul G S hvw.le)).trans
    ((le_div_iff₀' (sub_pos.2 huv)).2 (mul_le_herbrandFun_sub G S huv.le))

/-- The Herbrand function is concave on `ℝ`. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ univ (herbrandFun G S) :=
  concaveOn_iff_slope_anti_adjacent.2
    ⟨convex_univ, fun _ _ _ _ _ huv hvw ↦ herbrandFun_slope_anti_adjacent G S huv hvw⟩

/-- On `[-1, 0]`, `herbrandFun` is the identity. -/
theorem herbrandFun_eq_self_of_mem_Icc {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandFun G S u = u := by
  have h := herbrandFun_sub_of_le G S (i := 0) (by simpa using h₁) h₀ (by simp)
  rw [div_self (by exact_mod_cast Nat.card_pos.ne'), herbrandFun_zero] at h; linarith

/-- `herbrandFun` fixes `-1`. -/
@[simp]
theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_eq_self_of_mem_Icc G S le_rfl (by norm_num)

/-- Below `-1`, `herbrandFun` is affine of slope `#G / #G_0` passing through `(-1, -1)`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u = -1 + (u + 1) * (Nat.card G / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_of_forall_eq G S hu (H := ⊤) fun t _ ht ↦
    ramificationGroupReal_eq_top_of_le_neg_one G S ht
  rw [herbrandFun_neg_one, Nat.card_congr Subgroup.topEquiv.toEquiv] at h; linarith

/-- The **finite-sum formula** for `herbrandFun`: for `m : ℕ` and `m ≤ u ≤ m + 1`,
`φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_mem_Icc (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) :
    herbrandFun G S u = (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
      (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  have hstep := herbrandFun_sub_of_le G S (i := (m + 1 : ℕ)) (by push_cast; linarith) h₁
    (by push_cast; linarith)
  induction m generalizing u with
  | zero =>
    rw [Nat.cast_zero, herbrandFun_zero] at hstep
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]; linear_combination hstep
  | succ k ih =>
    have hk := ih (u := (k + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)
      (herbrandFun_sub_of_le G S (i := (k + 1 : ℕ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith))
    rw [Finset.sum_Icc_succ_top (by omega)]; rw [hk] at hstep; push_cast at hstep ⊢
    linear_combination hstep

/-- Value of `herbrandFun` at `m : ℕ`: `φ(m) = (#G_1 + ⋯ + #G_m) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) : herbrandFun G S m =
    (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
      Nat.card (ramificationGroup G S 0) := by
  rw [herbrandFun_of_mem_Icc G S m le_rfl (by linarith), sub_self, zero_mul, add_zero]

/-- Value of `herbrandFun` at a nonnegative integer `m`. -/
theorem herbrandFun_intCast_of_nonneg {m : ℤ} (hm : 0 ≤ m) : herbrandFun G S m =
    (∑ i ∈ Finset.Icc 1 m.toNat, (Nat.card (ramificationGroup G S i) : ℝ)) /
      Nat.card (ramificationGroup G S 0) := by
  have hm' : (m : ℝ) = (m.toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hm).symm
  rw [hm', herbrandFun_natCast]

/-- The Herbrand function is surjective onto `ℝ`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  set g : ℝ := (Nat.card (ramificationGroup G S 0) : ℝ)
  have hg : 0 < g := Nat.cast_pos.2 Nat.card_pos
  have ha0 : -(|y| * g) ≤ 0 := neg_nonpos.2 (mul_nonneg (abs_nonneg y) hg.le)
  have hb0 : 0 ≤ |y| * g := mul_nonneg (abs_nonneg y) hg.le
  have hφa : herbrandFun G S (-(|y| * g)) ≤ y := by
    have h := div_sub_le_herbrandFun_sub G S ha0
    rw [herbrandFun_zero, sub_neg_eq_add, zero_add, mul_div_cancel_right₀ _ hg.ne'] at h
    linarith [neg_abs_le y]
  have hφb : y ≤ herbrandFun G S (|y| * g) := by
    have h := div_sub_le_herbrandFun_sub G S hb0
    rw [herbrandFun_zero, sub_zero, mul_div_cancel_right₀ _ hg.ne'] at h
    linarith [le_abs_self y]
  exact (intermediate_value_Icc (ha0.trans hb0) (continuous_herbrandFun G S).continuousOn
    ⟨hφa, hφb⟩).imp fun _ hx ↦ hx.2

private def herbrandRealOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (herbrandFun G S) (herbrandFun_strictMono G S)
    (herbrandFun_surjective G S)

private theorem inverseHerbrandFun_eq_symm (v : ℝ) :
    inverseHerbrandFun G S v = (herbrandRealOrderIso G S).symm v := by
  have hset : {u : ℝ | v ≤ herbrandFun G S u} = Ici ((herbrandRealOrderIso G S).symm v) :=
    Set.ext fun _ ↦ (herbrandRealOrderIso G S).symm_apply_le.symm
  rw [inverseHerbrandFun_def, hset, csInf_Ici]

/-- `φ(ψ(v)) = v` for every real `v`. -/
@[simp]
theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v := by
  rw [inverseHerbrandFun_eq_symm]; exact (herbrandRealOrderIso G S).apply_symm_apply v

/-- `ψ(φ(u)) = u` for every real `u`. -/
@[simp]
theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u := by
  rw [inverseHerbrandFun_eq_symm]; exact (herbrandRealOrderIso G S).symm_apply_apply u

/-- `inverseHerbrandFun` is strictly increasing on `ℝ`. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) := by
  simpa only [funext (inverseHerbrandFun_eq_symm G S)] using
    (herbrandRealOrderIso G S).symm.strictMono

/-- `inverseHerbrandFun` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) := by
  simpa only [funext (inverseHerbrandFun_eq_symm G S)] using
    (herbrandRealOrderIso G S).symm.continuous

/-- `inverseHerbrandFun` vanishes at `0`. -/
@[simp]
theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 := by
  simpa using inverseHerbrandFun_herbrandFun G S 0

/-- `inverseHerbrandFun` fixes `-1`. -/
@[simp]
theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 := by
  simpa using inverseHerbrandFun_herbrandFun G S (-1)

/-- On `[-1, 0]`, `inverseHerbrandFun` is the identity. -/
theorem inverseHerbrandFun_eq_self_of_mem_Icc {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_eq_self_of_mem_Icc G S h₁ h₀]
  exact inverseHerbrandFun_herbrandFun G S v

/-- `-1 ≤ φ(u)` if and only if `-1 ≤ u`. -/
@[simp]
theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  conv_lhs => rw [← herbrandFun_neg_one G S]
  exact (herbrandFun_strictMono G S).le_iff_le

/-- `0 ≤ φ(u)` if and only if `0 ≤ u`. -/
@[simp]
theorem herbrandFun_nonneg_iff {u : ℝ} : 0 ≤ herbrandFun G S u ↔ 0 ≤ u := by
  conv_lhs => rw [← herbrandFun_zero G S]
  exact (herbrandFun_strictMono G S).le_iff_le

/-- `-1 ≤ ψ(v)` if and only if `-1 ≤ v`. -/
@[simp]
theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} : -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := by
  conv_lhs => rw [← inverseHerbrandFun_neg_one G S]
  exact (inverseHerbrandFun_strictMono G S).le_iff_le

/-- `0 ≤ ψ(v)` if and only if `0 ≤ v`. -/
@[simp]
theorem inverseHerbrandFun_nonneg_iff {v : ℝ} : 0 ≤ inverseHerbrandFun G S v ↔ 0 ≤ v := by
  conv_lhs => rw [← inverseHerbrandFun_zero G S]
  exact (inverseHerbrandFun_strictMono G S).le_iff_le

/-- `herbrandFun` restricted to an order automorphism of `[-1, ∞)`, with inverse
`inverseHerbrandFun`. -/
def herbrandOrderIso : Ici (-1 : ℝ) ≃o Ici (-1 : ℝ) where
  toFun u := ⟨herbrandFun G S u, (neg_one_le_herbrandFun_iff G S).2 u.2⟩
  invFun v := ⟨inverseHerbrandFun G S v, (neg_one_le_inverseHerbrandFun_iff G S).2 v.2⟩
  left_inv u := Subtype.ext (inverseHerbrandFun_herbrandFun G S u)
  right_inv v := Subtype.ext (herbrandFun_inverseHerbrandFun G S v)
  map_rel_iff' := (herbrandFun_strictMono G S).le_iff_le

/-- Forward coercion of `herbrandOrderIso` is `herbrandFun`. -/
@[simp]
theorem coe_herbrandOrderIso_apply (u : Ici (-1 : ℝ)) :
    (herbrandOrderIso G S u : ℝ) = herbrandFun G S u := (rfl)

/-- Inverse coercion of `herbrandOrderIso` is `inverseHerbrandFun`. -/
@[simp]
theorem coe_herbrandOrderIso_symm_apply (v : Ici (-1 : ℝ)) :
    ((herbrandOrderIso G S).symm v : ℝ) = inverseHerbrandFun G S v := (rfl)

/-- When inertia is trivial (`G_0 = ⊥`), `herbrandFun` is the identity on `[-1, ∞)`. -/
theorem herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot
    (h0 : ramificationGroup G S 0 = ⊥) {u : ℝ} (hu : -1 ≤ u) : herbrandFun G S u = u := by
  rcases le_or_gt u 0 with hu0 | hu0
  · exact herbrandFun_eq_self_of_mem_Icc G S hu hu0
  · have h := herbrandFun_sub_of_forall_eq G S hu0.le (H := ⊥) fun t ht _ ↦ eq_bot_iff.2
      ((ramificationGroupReal_antitone G S ht.le).trans
        (by rw [← Int.cast_zero, ramificationGroupReal_intCast, h0]))
    rw [h0, div_self (by exact_mod_cast Nat.card_pos.ne'), herbrandFun_zero] at h; linarith

/-- When inertia is trivial (`G_0 = ⊥`), `inverseHerbrandFun` is the identity on `[-1, ∞)`. -/
theorem inverseHerbrandFun_eq_self_of_ramificationGroup_zero_eq_bot
    (h0 : ramificationGroup G S 0 = ⊥) {v : ℝ} (hv : -1 ≤ v) : inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S h0 hv]
  exact inverseHerbrandFun_herbrandFun G S v

/-- When inertia is trivial (`G_0 = ⊥`), `G^v = ⊥` for every `v > -1`. -/
theorem upperRamificationGroup_eq_bot_of_ramificationGroup_zero_eq_bot
    (h0 : ramificationGroup G S 0 = ⊥) {v : ℝ} (hv : -1 < v) :
    upperRamificationGroup G S v = ⊥ := by
  rw [upperRamificationGroup_def,
    inverseHerbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S h0 hv.le,
    ramificationGroupReal_def]
  exact eq_bot_iff.2 ((ramificationGroup_antitone G S
    (Int.le_ceil_iff.2 (by simpa using hv))).trans h0.le)

/-- For a subsingleton group `G`, `herbrandFun G S` is the identity on all of `ℝ`. -/
@[simp]
theorem herbrandFun_of_subsingleton [Subsingleton G] (u : ℝ) : herbrandFun G S u = u := by
  rcases le_total (-1) u with hu | hu
  · exact herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S (Subsingleton.elim _ _) hu
  · have : Unique G := uniqueOfSubsingleton 1
    have : Unique (ramificationGroup G S 0) := uniqueOfSubsingleton 1
    rw [herbrandFun_of_le_neg_one G S hu, Nat.card_unique, Nat.card_unique]; push_cast; ring

/-- For a subsingleton group `G`, `inverseHerbrandFun G S` is the identity on all of `ℝ`. -/
@[simp]
theorem inverseHerbrandFun_of_subsingleton [Subsingleton G] (v : ℝ) :
    inverseHerbrandFun G S v = v := by
  conv_lhs => rw [← herbrandFun_of_subsingleton G S v]
  exact inverseHerbrandFun_herbrandFun G S v

private theorem inverseHerbrandFun_natCast_eq_floor (n : ℕ) :
    inverseHerbrandFun G S n = ⌊inverseHerbrandFun G S n⌋₊ := by
  set u := inverseHerbrandFun G S n
  set m := ⌊u⌋₊
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le ((inverseHerbrandFun_nonneg_iff G S).2 (Nat.cast_nonneg n))
  have hm₂ : u < m + 1 := Nat.lt_floor_add_one u
  have hφ := herbrandFun_of_mem_Icc G S m hm₁ hm₂.le
  rw [herbrandFun_inverseHerbrandFun, eq_div_iff (by exact_mod_cast Nat.card_pos.ne')] at hφ
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
  have hc_zero : c = 0 := by omega
  rw [hc_zero, Int.cast_zero, sub_eq_zero] at hcu; exact hcu

/-- The **integral inverse Herbrand function** `ψℕ : ℕ → ℕ`, whose real value equals
`inverseHerbrandFun G S n` (`coe_psiNat`). -/
def psiNat (n : ℕ) : ℕ := ⌊inverseHerbrandFun G S n⌋₊

omit [Finite G] in
/-- Defining floor formula for `psiNat`. -/
theorem psiNat_def (n : ℕ) : psiNat G S n = ⌊inverseHerbrandFun G S n⌋₊ := by rfl

/-- For every `n : ℕ`, `inverseHerbrandFun G S n` is the natural number `psiNat G S n`. -/
@[simp]
theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n :=
  (inverseHerbrandFun_natCast_eq_floor G S n).symm

/-- Arithmetic characterization: `ψℕ(n) = m ↔ #G_1 + ⋯ + #G_m = n · #G_0`. -/
theorem psiNat_eq_iff {n m : ℕ} : psiNat G S n = m ↔
    ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
      n * Nat.card (ramificationGroup G S 0) := by
  rw [← Nat.cast_inj (R := ℝ), coe_psiNat, ← (herbrandFun_strictMono G S).injective.eq_iff,
    herbrandFun_inverseHerbrandFun, eq_comm, herbrandFun_natCast,
    div_eq_iff (by exact_mod_cast Nat.card_pos.ne')]
  norm_cast

/-- Order characterization: `psiNat G S n ≤ m ↔ (n : ℝ) ≤ herbrandFun G S m`. -/
theorem psiNat_le_iff {n m : ℕ} : psiNat G S n ≤ m ↔ (n : ℝ) ≤ herbrandFun G S m := by
  rw [← Nat.cast_le (α := ℝ), coe_psiNat, ← (herbrandFun_strictMono G S).le_iff_le,
    herbrandFun_inverseHerbrandFun]

/-- `psiNat` vanishes at `0`. -/
@[simp]
theorem psiNat_zero : psiNat G S 0 = 0 := (psiNat_eq_iff G S).2 (by simp)

/-- `psiNat` is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat G S) := fun a b hab ↦ by
  have hlt : inverseHerbrandFun G S a < inverseHerbrandFun G S b :=
    inverseHerbrandFun_strictMono G S (by exact_mod_cast hab)
  exact_mod_cast (coe_psiNat G S a).trans_lt (hlt.trans_eq (coe_psiNat G S b).symm)

/-- `n ≤ psiNat G S n` for every `n : ℕ`. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat G S n := (psiNat_strictMono G S).id_le n

/-- `psiNat G S n = n` if and only if the lower filtration is constant through `n` (`G_n = G_0`). -/
@[simp]
theorem psiNat_eq_self_iff {n : ℕ} :
    psiNat G S n = n ↔ ramificationGroup G S n = ramificationGroup G S 0 := by
  have hle : ∀ i : ℕ, ramificationGroup G S i ≤ ramificationGroup G S 0 := fun i ↦
    ramificationGroup_antitone G S (Int.natCast_nonneg i)
  rw [psiNat_eq_iff]; refine ⟨fun h ↦ ?_, fun hn ↦ ?_⟩
  · rcases n with _ | k
    · simp
    have hk := Finset.sum_le_card_nsmul (Finset.Icc 1 k)
      (fun i : ℕ ↦ Nat.card (ramificationGroup G S i)) _ fun i _ ↦ Subgroup.card_le_of_le (hle i)
    rw [Finset.sum_Icc_succ_top (by omega)] at h
    simp only [Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul] at hk
    exact Subgroup.eq_of_le_of_card_ge (hle _) (by rw [add_mul, one_mul] at h; omega)
  · calc ∑ i ∈ Finset.Icc 1 n, Nat.card (ramificationGroup G S i)
        = ∑ _i ∈ Finset.Icc 1 n, Nat.card (ramificationGroup G S 0) :=
          Finset.sum_congr rfl fun i hi ↦ by
            have hi' : (i : ℤ) ≤ n := by have := (Finset.mem_Icc.1 hi).2; omega
            rw [le_antisymm (hle i) (hn.symm.le.trans (ramificationGroup_antitone G S hi'))]
      _ = n * Nat.card (ramificationGroup G S 0) := by simp

/-- `G^{φ(u)} = G_u` for every real `u`. -/
@[simp]
theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]

/-- At a natural number `n`, `G^n = G_{psiNat G S n}`. -/
theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S n = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast, ramificationGroupReal_intCast]

/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)

/-- On `[-1, 0]`, the upper and lower numberings coincide. -/
theorem upperRamificationGroup_eq_ramificationGroupReal_of_mem_Icc {v : ℝ} (h₁ : -1 ≤ v)
    (h₀ : v ≤ 0) : upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_eq_self_of_mem_Icc G S h₁ h₀]

/-- At `0`, the upper ramification group is the zeroth lower ramification group (inertia). -/
@[simp]
theorem upperRamificationGroup_zero : upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_zero, ← Int.cast_zero,
    ramificationGroupReal_intCast]

/-- For `v ≤ -1`, the upper ramification group is `⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ := by
  have hψ : inverseHerbrandFun G S v ≤ -1 := by
    simpa only [inverseHerbrandFun_neg_one] using (inverseHerbrandFun_strictMono G S).monotone hv
  rw [upperRamificationGroup_def, ramificationGroupReal_eq_top_of_le_neg_one G S hψ]

/-- At `-1`, the upper ramification group is `⊤`. -/
@[simp]
theorem upperRamificationGroup_neg_one : upperRamificationGroup G S (-1) = ⊤ :=
  upperRamificationGroup_eq_top_of_le_neg_one G S le_rfl

/-- Over a Noetherian local ring, the upper ramification filtration cuts out the kernel of the
action. -/
theorem iInf_upperRamificationGroup_eq_ker [IsNoetherianRing S] :
    ⨅ v : ℝ, upperRamificationGroup G S v = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  rw [← iInf_ramificationGroup_eq_ker G S]
  refine le_antisymm (le_iInf fun i ↦ (iInf_le _ (herbrandFun G S i)).trans_eq
    (by rw [upperRamificationGroup_herbrandFun, ramificationGroupReal_intCast]))
    (le_iInf fun v ↦ ?_)
  rw [upperRamificationGroup_def, ramificationGroupReal_def]; exact iInf_le _ _

/-- A faithful finite action on a Noetherian local ring is separated by its upper ramification
filtration. -/
theorem iInf_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ⨅ v : ℝ, upperRamificationGroup G S v = ⊥ := by
  rw [iInf_upperRamificationGroup_eq_ker, TauCeti.MulSemiringAction.ker_toRingAut_eq_bot]

/-- Over a Noetherian local ring, the upper ramification filtration reaches the kernel of the
action at a finite index. -/
theorem exists_forall_upperRamificationGroup_eq_ker [IsNoetherianRing S] :
    ∃ V : ℝ, ∀ v : ℝ, V ≤ v →
      upperRamificationGroup G S v = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_ker G S
  refine ⟨herbrandFun G S N, fun v hv ↦ ?_⟩
  have hle : (N : ℝ) ≤ inverseHerbrandFun G S v := by
    simpa only [inverseHerbrandFun_herbrandFun] using
      (inverseHerbrandFun_strictMono G S).monotone hv
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact hN _ (Int.le_ceil_iff.2 (by linarith))

/-- For a faithful finite action on a Noetherian local ring, the upper ramification groups vanish
from some index on. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ V : ℝ, ∀ v : ℝ, V ≤ v → upperRamificationGroup G S v = ⊥ := by
  simpa only [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot] using
    exists_forall_upperRamificationGroup_eq_ker G S

/-- **Subgroup trace identity for the upper numbering.** For any subgroup `H ≤ G` of a finite group
`G` acting on `S`, `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}`. -/
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal,
    upperRamificationGroup_herbrandFun]

/-- `herbrandFun` carries lower breaks to upper breaks. -/
@[simp]
theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [upperJump_iff, lowerJump_iff]; refine ⟨fun h v huv ↦ ?_, fun h v huv ↦ ?_⟩
  · simpa only [upperRamificationGroup_herbrandFun] using
      h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
  · have hlt : u < inverseHerbrandFun G S v := by
      simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono G S huv
    rw [upperRamificationGroup_herbrandFun, upperRamificationGroup_def]; exact h _ hlt

/-- `inverseHerbrandFun` carries upper breaks to lower breaks. -/
@[simp]
theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa only [herbrandFun_inverseHerbrandFun] using
    (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

variable {G S} in
/-- Every upper break is at least `-1`. -/
theorem UpperJump.neg_one_le {v : ℝ} (hv : UpperJump G S v) : -1 ≤ v :=
  (neg_one_le_inverseHerbrandFun_iff G S).1
    ((lowerJump_inverseHerbrandFun_iff G S v).2 hv).neg_one_le

end Finite

end TauCeti.IsLocalRing
