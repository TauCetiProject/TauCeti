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

For a group `G` acting by ring automorphisms on a local ring `S`, we define the **Herbrand
function** `herbrandFun G S u = ∫ t in 0..u, #G_t / #G_0`, its inverse `inverseHerbrandFun G S`,
`upperRamificationGroup G S v = G_{ψ(v)}`, and `UpperJump G S`. For finite `G`, `herbrandFun G S`
is a continuous, strictly increasing, concave bijection of `ℝ` restricting to `herbrandOrderIso G S`
on `[-1, ∞)`, `ψ` maps `ℕ` to `ℕ` (`psiNat G S`), and `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}`
(`subgroupOf_upperRamificationGroup`). Adapts
`NumberTheory/LocalField/Herbrand/{Basic,Jump,Quotient}.lean`.

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
/-- The **Herbrand function** `φ(u) = ∫_0^u #G_t / #G_0 dt` (meaningful on `[-1, ∞)`). -/
def herbrandFun (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)
theorem herbrandFun_def (u : ℝ) : herbrandFun G S u = ∫ t in (0 : ℝ)..u,
    (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0) := (rfl)
/-- The **inverse Herbrand function** `ψ(v) = sInf {u : ℝ | v ≤ φ(u)}`. -/
def inverseHerbrandFun (v : ℝ) : ℝ := sInf {u : ℝ | v ≤ herbrandFun G S u}
theorem inverseHerbrandFun_def (v : ℝ) :
    inverseHerbrandFun G S v = sInf {u : ℝ | v ≤ herbrandFun G S u} := (rfl)
/-- The **upper-numbering ramification group** `G^v = G_{ψ(v)}` of `G` acting on `S`. -/
def upperRamificationGroup (v : ℝ) : Subgroup G :=
  ramificationGroupReal G S (inverseHerbrandFun G S v)
theorem upperRamificationGroup_def (v : ℝ) :
    upperRamificationGroup G S v = ramificationGroupReal G S (inverseHerbrandFun G S v) := (rfl)
variable {G S} in
@[simp] theorem mem_upperRamificationGroup_iff {v : ℝ} {σ : G} : σ ∈ upperRamificationGroup G S v ↔
    σ ∈ ramificationGroupReal G S (inverseHerbrandFun G S v) := Iff.rfl
instance instNormalUpperRamificationGroup (v : ℝ) : (upperRamificationGroup G S v).Normal := by
  rw [upperRamificationGroup_def]; infer_instance
@[simp] theorem herbrandFun_zero : herbrandFun G S 0 = 0 := by rw [herbrandFun_def, integral_same]
/-- An **upper break** of the ramification filtration: `G^v < G^u` for every `v > u`. -/
def UpperJump (u : ℝ) : Prop :=
  ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u
theorem upperJump_iff (u : ℝ) : UpperJump G S u ↔
    ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u := Iff.rfl
/-- The **integral inverse Herbrand function** `ψℕ : ℕ → ℕ` (`coe_psiNat`). -/
def psiNat (n : ℕ) : ℕ := ⌊inverseHerbrandFun G S n⌋₊
theorem psiNat_def (n : ℕ) : psiNat G S n = ⌊inverseHerbrandFun G S n⌋₊ := (rfl)
end Defs

section Transport
section Actions
variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {H : Type*} [Group H]
section Comap
variable {T : Type*} [CommRing T] [IsLocalRing T] [MulSemiringAction H T] {φ : G →* H}
  (hφ : Function.Bijective φ)
  (he : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ)
include hφ he
/-- A bijective `φ : G →* H` pulling back all lower ramification groups preserves `herbrandFun`. -/
theorem herbrandFun_eq_of_ramificationGroup_eq_comap (u : ℝ) :
    herbrandFun G S u = herbrandFun H T u := by
  have hcard (i : ℤ) : Nat.card (ramificationGroup G S i) = Nat.card (ramificationGroup H T i) :=
    Nat.card_congr ((Equiv.ofBijective φ hφ).subtypeEquiv fun _ ↦ by rw [he i]; rfl)
  simp only [herbrandFun_def, ramificationGroupReal_def, hcard]
/-- A bijective `φ : G →* H` pulling back lower groups preserves `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H T v := by
  simp only [inverseHerbrandFun_def, herbrandFun_eq_of_ramificationGroup_eq_comap hφ he]
/-- A bijective `φ : G →* H` pulling back lower groups pulls back `upperRamificationGroup`. -/
theorem upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H T v).comap φ := by
  simp only [upperRamificationGroup_def, inverseHerbrandFun_eq_of_ramificationGroup_eq_comap hφ he,
    ramificationGroupReal_def, he]
/-- A bijective `φ : G →* H` pulling back lower groups preserves `UpperJump`. -/
theorem upperJump_iff_of_ramificationGroup_eq_comap (u : ℝ) :
    UpperJump G S u ↔ UpperJump H T u := by
  simp_rw [upperJump_iff, upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap hφ he,
    Subgroup.comap_lt_comap_of_surjective hφ.2]
end Comap
section SMul
variable {φ : G →* H} (hφ : Function.Bijective φ) [MulSemiringAction H S]
  (he : ∀ (g : G) (x : S), g • x = φ g • x)
include hφ he
/-- Two groups linked by a bijective action-compatible homomorphism share `herbrandFun`. -/
theorem herbrandFun_eq_of_smul_eq (u : ℝ) : herbrandFun G S u = herbrandFun H S u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap hφ (ramificationGroup_eq_comap_of_smul_eq he) u
/-- Two groups linked by a bijective action-compatible homomorphism share `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_smul_eq (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H S v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap hφ
    (ramificationGroup_eq_comap_of_smul_eq he) v
/-- A bijective action-compatible map pulls back `upperRamificationGroup`. -/
theorem upperRamificationGroup_eq_comap_of_smul_eq (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H S v).comap φ :=
  upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap hφ
    (ramificationGroup_eq_comap_of_smul_eq he) v
/-- Two groups linked by a bijective action-compatible homomorphism share `UpperJump`. -/
theorem upperJump_iff_of_smul_eq (u : ℝ) : UpperJump G S u ↔ UpperJump H S u :=
  upperJump_iff_of_ramificationGroup_eq_comap hφ (ramificationGroup_eq_comap_of_smul_eq he) u
end SMul
end Actions
end Transport

section Finite
variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]
private def herbrandDensity (t : ℝ) : ℝ :=
  (Nat.card (ramificationGroupReal G S t) : ℝ) / Nat.card (ramificationGroup G S 0)
private theorem herbrandDensity_antitone : Antitone (herbrandDensity G S) := fun _ _ h ↦
  div_le_div_of_nonneg_right
    (Nat.cast_le.2 (Subgroup.card_le_of_le (ramificationGroupReal_antitone G S h)))
    (Nat.cast_nonneg _)
private theorem herbrandFun_sub (a b : ℝ) :
    herbrandFun G S b - herbrandFun G S a = ∫ t in a..b, herbrandDensity G S t :=
  integral_interval_sub_left (herbrandDensity_antitone G S).intervalIntegrable
    (herbrandDensity_antitone G S).intervalIntegrable
private theorem integral_const_real (a b c : ℝ) : ∫ _ in a..b, c = (b - a) * c := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
/-- On `[a, b]` where `(a, b]` has constant `G_t = H`, `herbrandFun` has slope `#H / #G_0`. -/
theorem herbrandFun_sub_of_forall_eq {a b : ℝ} (hab : a ≤ b) {H : Subgroup G}
    (h : ∀ t : ℝ, a < t → t ≤ b → ramificationGroupReal G S t = H) :
    herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card H / Nat.card (ramificationGroup G S 0)) := by
  rw [herbrandFun_sub, ← integral_const_real]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun t ht ↦ by
    rw [uIoc_of_le hab] at ht; rw [herbrandDensity, h t ht.1 ht.2]
/-- On any subinterval `[a, b] ⊆ [i - 1, i]`, `herbrandFun` is affine of slope `#G_i / #G_0`. -/
theorem herbrandFun_sub_of_sub_one_le_of_le {i : ℤ} {a b : ℝ} (ha : (i : ℝ) - 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ i) : herbrandFun G S b - herbrandFun G S a =
      (b - a) * (Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0)) :=
  herbrandFun_sub_of_forall_eq G S hab fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_sub_one_lt_of_le G S (ha.trans_lt ht₁) (ht₂.trans hb)
private theorem div_sub_le_herbrandFun_sub {a b : ℝ} (hab : a ≤ b) :
    (b - a) / Nat.card (ramificationGroup G S 0) ≤ herbrandFun G S b - herbrandFun G S a := by
  rw [herbrandFun_sub, div_eq_mul_inv, ← integral_const_real]
  exact integral_mono_on hab intervalIntegrable_const
    (herbrandDensity_antitone G S).intervalIntegrable fun _ _ ↦ by
      rw [herbrandDensity, div_eq_mul_inv]
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.card_pos)
/-- The Herbrand function is strictly increasing on `ℝ`. -/
theorem herbrandFun_strictMono : StrictMono (herbrandFun G S) := fun _ _ hab ↦ by
  linarith [div_sub_le_herbrandFun_sub G S hab.le,
    div_pos (sub_pos.2 hab) (Nat.cast_pos.2 (Nat.card_pos (α := ramificationGroup G S 0)))]
/-- The Herbrand function is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_herbrandFun : Continuous (herbrandFun G S) :=
  continuous_primitive (fun _ _ ↦ (herbrandDensity_antitone G S).intervalIntegrable) 0
/-- Slopes of `herbrandFun` over adjacent intervals decrease. -/
theorem herbrandFun_slope_anti_adjacent {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    (herbrandFun G S w - herbrandFun G S v) / (w - v) ≤
      (herbrandFun G S v - herbrandFun G S u) / (v - u) := by
  have hd := herbrandDensity_antitone G S
  refine le_trans (b := herbrandDensity G S v)
    ((div_le_iff₀' (sub_pos.2 hvw)).2 ?_) ((le_div_iff₀' (sub_pos.2 huv)).2 ?_) <;>
    rw [herbrandFun_sub, ← integral_const_real]
  · exact integral_mono_on hvw.le hd.intervalIntegrable intervalIntegrable_const fun _ ht ↦ hd ht.1
  · exact integral_mono_on huv.le intervalIntegrable_const hd.intervalIntegrable fun _ ht ↦ hd ht.2
/-- The Herbrand function is concave on `ℝ`. -/
theorem concaveOn_herbrandFun : ConcaveOn ℝ univ (herbrandFun G S) :=
  concaveOn_iff_slope_anti_adjacent.2
    ⟨convex_univ, fun _ _ _ _ _ huv hvw ↦ herbrandFun_slope_anti_adjacent G S huv hvw⟩
/-- On `[-1, 0]`, `herbrandFun` is the identity. -/
theorem herbrandFun_eq_self_of_neg_one_le_of_nonpos {u : ℝ} (h₁ : -1 ≤ u) (h₀ : u ≤ 0) :
    herbrandFun G S u = u := by
  have h := herbrandFun_sub_of_sub_one_le_of_le G S (i := 0) (by simpa using h₁) h₀ (by simp)
  rw [div_self (by exact_mod_cast Nat.card_pos.ne'), herbrandFun_zero] at h; linarith
@[simp] theorem herbrandFun_neg_one : herbrandFun G S (-1) = -1 :=
  herbrandFun_eq_self_of_neg_one_le_of_nonpos G S le_rfl (by norm_num)
/-- Below `-1`, `herbrandFun` is affine of slope `#G / #G_0` passing through `(-1, -1)`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u = -1 + (u + 1) * (Nat.card G / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_of_forall_eq G S hu (H := ⊤) fun _ _ ht ↦
    ramificationGroupReal_eq_top_of_le_neg_one G S ht
  rw [herbrandFun_neg_one, Nat.card_congr Subgroup.topEquiv.toEquiv] at h; linarith
/-- On `[m, m + 1]` (`m : ℕ`), `φ(u) = (#G_1 + ⋯ + #G_m + (u - m) #G_{m+1}) / #G_0`. -/
theorem herbrandFun_of_natCast_le_of_le_add_one (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u)
    (h₂ : u ≤ m + 1) :
    herbrandFun G S u = (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ) +
      (u - m) * Nat.card (ramificationGroup G S (m + 1 : ℕ))) /
        Nat.card (ramificationGroup G S 0) := by
  induction m generalizing u with
  | zero =>
    have hs := herbrandFun_sub_of_sub_one_le_of_le G S (i := 1) (by simp) h₁ (by simpa using h₂)
    rw [Nat.cast_zero, herbrandFun_zero] at hs
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]; linear_combination hs
  | succ k ih =>
    have hs := herbrandFun_sub_of_sub_one_le_of_le G S (i := (k + 1 + 1 : ℕ))
      (by push_cast; linarith) h₁ (by push_cast at h₂ ⊢; linarith)
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih (u := (k + 1 : ℕ)) (by push_cast; linarith) (by push_cast; linarith)] at hs
    push_cast at hs ⊢; linear_combination hs
/-- At a natural number `m`, `φ(m) = (∑ i ∈ Icc 1 m, #G_i) / #G_0`. -/
theorem herbrandFun_natCast (m : ℕ) : herbrandFun G S m =
    (∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ)) /
      Nat.card (ramificationGroup G S 0) := by
  simp [herbrandFun_of_natCast_le_of_le_add_one G S m le_rfl (by linarith)]
/-- At a nonnegative integer `m`, `φ(m) = (∑ i ∈ Icc 1 m.toNat, #G_i) / #G_0`. -/
theorem herbrandFun_intCast_of_nonneg {m : ℤ} (hm : 0 ≤ m) : herbrandFun G S m =
    (∑ i ∈ Finset.Icc 1 m.toNat, (Nat.card (ramificationGroup G S i) : ℝ)) /
      Nat.card (ramificationGroup G S 0) := by
  rw [← herbrandFun_natCast]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hm).symm
/-- Arithmetic core of Serre's lemma: if `#G_0 · n = ∑ k ∈ range j, #G_k`, then
`φ_G(j - 1) = n - 1`. Adapts `TauCeti.LocalFieldsRamification.coe_herbrand_lowerIndex_sub_one`
from `NumberTheory/LocalField/Herbrand/Quotient.lean`. -/
theorem herbrandFun_sub_one_of_card_mul_eq_sum {j n : ℕ}
    (hsum : Nat.card (ramificationGroup G S 0) * n =
      ∑ k ∈ Finset.range j, Nat.card (ramificationGroup G S k)) :
    herbrandFun G S ((j : ℝ) - 1) = (n : ℝ) - 1 := by
  rcases j with _ | m
  · rw [herbrandFun_eq_self_of_neg_one_le_of_nonpos G S (by norm_num) (by norm_num)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast,
      div_eq_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    linear_combination -(by exact_mod_cast hsum : (Nat.card (ramificationGroup G S 0) : ℝ) * n =
      Nat.card (ramificationGroup G S 0) +
        ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ))
/-- The Herbrand function is surjective onto `ℝ`. -/
theorem herbrandFun_surjective : Function.Surjective (herbrandFun G S) := fun y ↦ by
  have hg : (0 : ℝ) < Nat.card (ramificationGroup G S 0) := Nat.cast_pos.2 Nat.card_pos
  have hb0 : 0 ≤ |y| * Nat.card (ramificationGroup G S 0) := by positivity
  have h₁ := div_sub_le_herbrandFun_sub G S (neg_nonpos.2 hb0)
  have h₂ := div_sub_le_herbrandFun_sub G S hb0
  simp only [herbrandFun_zero, sub_neg_eq_add, zero_add, sub_zero,
    mul_div_cancel_right₀ _ hg.ne'] at h₁ h₂
  exact (intermediate_value_Icc ((neg_nonpos.2 hb0).trans hb0)
    (continuous_herbrandFun G S).continuousOn
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩).imp fun _ ↦ And.right
private def herbrandRealOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (herbrandFun_strictMono G S) (herbrandFun_surjective G S)
private theorem inverseHerbrandFun_eq_symm (v : ℝ) :
    inverseHerbrandFun G S v = (herbrandRealOrderIso G S).symm v := by
  rw [inverseHerbrandFun_def, (Set.ext fun _ ↦ (herbrandRealOrderIso G S).symm_apply_le.symm :
    {u : ℝ | v ≤ herbrandFun G S u} = Ici ((herbrandRealOrderIso G S).symm v)), csInf_Ici]
/-- `herbrandFun` is a left inverse to `inverseHerbrandFun` (`φ (ψ v) = v`). -/
@[simp] theorem herbrandFun_inverseHerbrandFun (v : ℝ) :
    herbrandFun G S (inverseHerbrandFun G S v) = v :=
  inverseHerbrandFun_eq_symm G S v ▸ (herbrandRealOrderIso G S).apply_symm_apply v
/-- `inverseHerbrandFun` is a left inverse to `herbrandFun`. -/
@[simp] theorem inverseHerbrandFun_herbrandFun (u : ℝ) :
    inverseHerbrandFun G S (herbrandFun G S u) = u :=
  (inverseHerbrandFun_eq_symm G S _).trans ((herbrandRealOrderIso G S).symm_apply_apply u)
/-- `inverseHerbrandFun` is strictly increasing on `ℝ`. -/
theorem inverseHerbrandFun_strictMono : StrictMono (inverseHerbrandFun G S) := by
  simpa [funext (inverseHerbrandFun_eq_symm G S)] using (herbrandRealOrderIso G S).symm.strictMono
/-- `inverseHerbrandFun` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_inverseHerbrandFun : Continuous (inverseHerbrandFun G S) := by
  simpa [funext (inverseHerbrandFun_eq_symm G S)] using (herbrandRealOrderIso G S).symm.continuous
@[simp] theorem inverseHerbrandFun_zero : inverseHerbrandFun G S 0 = 0 := by
  simpa using inverseHerbrandFun_herbrandFun G S 0
@[simp] theorem inverseHerbrandFun_neg_one : inverseHerbrandFun G S (-1) = -1 := by
  simpa using inverseHerbrandFun_herbrandFun G S (-1)
/-- On `[-1, 0]`, `inverseHerbrandFun` is the identity. -/
theorem inverseHerbrandFun_eq_self_of_neg_one_le_of_nonpos {v : ℝ} (h₁ : -1 ≤ v) (h₀ : v ≤ 0) :
    inverseHerbrandFun G S v = v :=
  (herbrandFun_strictMono G S).injective <| by
    simp [herbrandFun_eq_self_of_neg_one_le_of_nonpos G S h₁ h₀]
@[simp] theorem herbrandFun_le_herbrandFun_iff {u v : ℝ} :
    herbrandFun G S u ≤ herbrandFun G S v ↔ u ≤ v := (herbrandFun_strictMono G S).le_iff_le
@[simp] theorem herbrandFun_lt_herbrandFun_iff {u v : ℝ} :
    herbrandFun G S u < herbrandFun G S v ↔ u < v := (herbrandFun_strictMono G S).lt_iff_lt
@[simp] theorem herbrandFun_inj {u v : ℝ} :
    herbrandFun G S u = herbrandFun G S v ↔ u = v := (herbrandFun_strictMono G S).injective.eq_iff
@[simp] theorem inverseHerbrandFun_le_inverseHerbrandFun_iff {u v : ℝ} :
    inverseHerbrandFun G S u ≤ inverseHerbrandFun G S v ↔ u ≤ v :=
  (inverseHerbrandFun_strictMono G S).le_iff_le
@[simp] theorem inverseHerbrandFun_lt_inverseHerbrandFun_iff {u v : ℝ} :
    inverseHerbrandFun G S u < inverseHerbrandFun G S v ↔ u < v :=
  (inverseHerbrandFun_strictMono G S).lt_iff_lt
@[simp] theorem inverseHerbrandFun_inj {u v : ℝ} :
    inverseHerbrandFun G S u = inverseHerbrandFun G S v ↔ u = v :=
  (inverseHerbrandFun_strictMono G S).injective.eq_iff
/-- Lower-bound adjunction `u ≤ ψ(v) ↔ φ(u) ≤ v`. -/
theorem le_inverseHerbrandFun_iff {u v : ℝ} :
    u ≤ inverseHerbrandFun G S v ↔ herbrandFun G S u ≤ v :=
  inverseHerbrandFun_eq_symm G S v ▸ (herbrandRealOrderIso G S).le_symm_apply
/-- Upper-bound adjunction `ψ(v) ≤ u ↔ v ≤ φ(u)`. -/
theorem inverseHerbrandFun_le_iff {u v : ℝ} :
    inverseHerbrandFun G S v ≤ u ↔ v ≤ herbrandFun G S u :=
  inverseHerbrandFun_eq_symm G S v ▸ (herbrandRealOrderIso G S).symm_apply_le
/-- For finite `G`, `ψ(v)` is the least `u : ℝ` satisfying `v ≤ φ(u)`. -/
theorem isLeast_inverseHerbrandFun (v : ℝ) :
    IsLeast {u : ℝ | v ≤ herbrandFun G S u} (inverseHerbrandFun G S v) :=
  ⟨(herbrandFun_inverseHerbrandFun G S v).ge, fun _ hu ↦ (inverseHerbrandFun_le_iff G S).2 hu⟩
/-- Strict lower-bound adjunction `u < ψ(v) ↔ φ(u) < v`. -/
theorem lt_inverseHerbrandFun_iff {u v : ℝ} :
    u < inverseHerbrandFun G S v ↔ herbrandFun G S u < v :=
  inverseHerbrandFun_eq_symm G S v ▸ (herbrandRealOrderIso G S).lt_symm_apply
/-- Strict upper-bound adjunction `ψ(v) < u ↔ v < φ(u)`. -/
theorem inverseHerbrandFun_lt_iff {u v : ℝ} :
    inverseHerbrandFun G S v < u ↔ v < herbrandFun G S u :=
  inverseHerbrandFun_eq_symm G S v ▸ (herbrandRealOrderIso G S).symm_apply_lt
@[simp] theorem neg_one_le_herbrandFun_iff {u : ℝ} : -1 ≤ herbrandFun G S u ↔ -1 ≤ u := by
  rw [← inverseHerbrandFun_le_iff, inverseHerbrandFun_neg_one]
@[simp] theorem herbrandFun_le_neg_one_iff {u : ℝ} : herbrandFun G S u ≤ -1 ↔ u ≤ -1 := by
  rw [← le_inverseHerbrandFun_iff, inverseHerbrandFun_neg_one]
@[simp] theorem neg_one_lt_herbrandFun_iff {u : ℝ} : -1 < herbrandFun G S u ↔ -1 < u :=
  lt_iff_lt_of_le_iff_le (herbrandFun_le_neg_one_iff G S)
@[simp] theorem herbrandFun_lt_neg_one_iff {u : ℝ} : herbrandFun G S u < -1 ↔ u < -1 :=
  lt_iff_lt_of_le_iff_le (neg_one_le_herbrandFun_iff G S)
@[simp] theorem herbrandFun_eq_neg_one_iff {u : ℝ} : herbrandFun G S u = -1 ↔ u = -1 :=
  (herbrandFun_strictMono G S).injective.eq_iff' (herbrandFun_neg_one G S)
@[simp] theorem herbrandFun_nonneg_iff {u : ℝ} : 0 ≤ herbrandFun G S u ↔ 0 ≤ u := by
  rw [← inverseHerbrandFun_le_iff, inverseHerbrandFun_zero]
@[simp] theorem herbrandFun_nonpos_iff {u : ℝ} : herbrandFun G S u ≤ 0 ↔ u ≤ 0 := by
  rw [← le_inverseHerbrandFun_iff, inverseHerbrandFun_zero]
@[simp] theorem herbrandFun_pos_iff {u : ℝ} : 0 < herbrandFun G S u ↔ 0 < u :=
  lt_iff_lt_of_le_iff_le (herbrandFun_nonpos_iff G S)
@[simp] theorem herbrandFun_neg_iff {u : ℝ} : herbrandFun G S u < 0 ↔ u < 0 :=
  lt_iff_lt_of_le_iff_le (herbrandFun_nonneg_iff G S)
@[simp] theorem herbrandFun_eq_zero_iff {u : ℝ} : herbrandFun G S u = 0 ↔ u = 0 :=
  (herbrandFun_strictMono G S).injective.eq_iff' (herbrandFun_zero G S)
@[simp] theorem neg_one_le_inverseHerbrandFun_iff {v : ℝ} :
    -1 ≤ inverseHerbrandFun G S v ↔ -1 ≤ v := (le_inverseHerbrandFun_iff G S).trans (by simp)
@[simp] theorem inverseHerbrandFun_le_neg_one_iff {v : ℝ} :
    inverseHerbrandFun G S v ≤ -1 ↔ v ≤ -1 := (inverseHerbrandFun_le_iff G S).trans (by simp)
@[simp] theorem neg_one_lt_inverseHerbrandFun_iff {v : ℝ} :
    -1 < inverseHerbrandFun G S v ↔ -1 < v := (lt_inverseHerbrandFun_iff G S).trans (by simp)
@[simp] theorem inverseHerbrandFun_lt_neg_one_iff {v : ℝ} :
    inverseHerbrandFun G S v < -1 ↔ v < -1 := (inverseHerbrandFun_lt_iff G S).trans (by simp)
@[simp] theorem inverseHerbrandFun_eq_neg_one_iff {v : ℝ} :
    inverseHerbrandFun G S v = -1 ↔ v = -1 := by rw [← herbrandFun_inj G S]; simp
@[simp] theorem inverseHerbrandFun_nonneg_iff {v : ℝ} : 0 ≤ inverseHerbrandFun G S v ↔ 0 ≤ v := by
  rw [le_inverseHerbrandFun_iff, herbrandFun_zero]
@[simp] theorem inverseHerbrandFun_nonpos_iff {v : ℝ} : inverseHerbrandFun G S v ≤ 0 ↔ v ≤ 0 := by
  rw [inverseHerbrandFun_le_iff, herbrandFun_zero]
@[simp] theorem inverseHerbrandFun_pos_iff {v : ℝ} : 0 < inverseHerbrandFun G S v ↔ 0 < v :=
  lt_iff_lt_of_le_iff_le (inverseHerbrandFun_nonpos_iff G S)
@[simp] theorem inverseHerbrandFun_neg_iff {v : ℝ} : inverseHerbrandFun G S v < 0 ↔ v < 0 :=
  lt_iff_lt_of_le_iff_le (inverseHerbrandFun_nonneg_iff G S)
@[simp] theorem inverseHerbrandFun_eq_zero_iff {v : ℝ} : inverseHerbrandFun G S v = 0 ↔ v = 0 :=
  (inverseHerbrandFun_strictMono G S).injective.eq_iff' (inverseHerbrandFun_zero G S)
/-- `herbrandFun` restricted to an order automorphism of `[-1, ∞)`. -/
def herbrandOrderIso : Ici (-1 : ℝ) ≃o Ici (-1 : ℝ) :=
  ((herbrandRealOrderIso G S).Ici (-1)).trans
    (Set.orderIsoOfEq _ _ (congrArg Ici (herbrandFun_neg_one G S)))
@[simp] theorem coe_herbrandOrderIso_apply (u : Ici (-1 : ℝ)) :
    (herbrandOrderIso G S u : ℝ) = herbrandFun G S u := (rfl)
@[simp] theorem coe_herbrandOrderIso_symm_apply (v : Ici (-1 : ℝ)) :
    ((herbrandOrderIso G S).symm v : ℝ) = inverseHerbrandFun G S v :=
  (inverseHerbrandFun_eq_symm G S v).symm
/-- When inertia is trivial (`G_0 = ⊥`), `herbrandFun` is the identity on `[-1, ∞)`. -/
theorem herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot (h0 : ramificationGroup G S 0 = ⊥)
    {u : ℝ} (hu : -1 ≤ u) : herbrandFun G S u = u := by
  rcases le_or_gt u 0 with hu0 | hu0; · exact herbrandFun_eq_self_of_neg_one_le_of_nonpos G S hu hu0
  have h := herbrandFun_sub_of_forall_eq G S hu0.le (H := ⊥) fun _ ht _ ↦ eq_bot_iff.2
    ((ramificationGroupReal_antitone G S ht.le).trans
      (by rw [← Int.cast_zero, ramificationGroupReal_intCast, h0]))
  rw [h0, div_self (by exact_mod_cast Nat.card_pos.ne'), herbrandFun_zero] at h; linarith
/-- When inertia is trivial (`G_0 = ⊥`), `inverseHerbrandFun` is the identity on `[-1, ∞)`. -/
theorem inverseHerbrandFun_eq_self_of_ramificationGroup_zero_eq_bot
    (h0 : ramificationGroup G S 0 = ⊥) {v : ℝ} (hv : -1 ≤ v) : inverseHerbrandFun G S v = v := by
  rw [← herbrandFun_inj G S, herbrandFun_inverseHerbrandFun,
    herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S h0 hv]
/-- When inertia is trivial (`G_0 = ⊥`), `G^v = ⊥` for every `v > -1`. -/
theorem upperRamificationGroup_eq_bot_of_ramificationGroup_zero_eq_bot
    (h0 : ramificationGroup G S 0 = ⊥) {v : ℝ} (hv : -1 < v) :
    upperRamificationGroup G S v = ⊥ := by
  rw [upperRamificationGroup_def, ramificationGroupReal_def,
    inverseHerbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S h0 hv.le]
  exact eq_bot_iff.2 ((ramificationGroup_antitone G S (Int.le_ceil_iff.2 (by simpa))).trans h0.le)
omit [Finite G] in
@[simp] theorem herbrandFun_of_subsingleton [Subsingleton G] (u : ℝ) : herbrandFun G S u = u := by
  rcases le_total (-1) u with hu | hu
  · exact herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S (Subsingleton.elim _ _) hu
  · rw [herbrandFun_of_le_neg_one G S hu, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩,
      Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩]; norm_num
omit [Finite G] in
@[simp] theorem inverseHerbrandFun_of_subsingleton [Subsingleton G] (v : ℝ) :
    inverseHerbrandFun G S v = v := by simpa using inverseHerbrandFun_herbrandFun G S v
/-- For every `n : ℕ`, `inverseHerbrandFun G S n` is the natural number `psiNat G S n`. -/
@[simp] theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n := by
  set u := inverseHerbrandFun G S n; set m := ⌊u⌋₊
  set g : ℤ → ℕ := fun i ↦ Nat.card (ramificationGroup G S i)
  have hm₁ : (m : ℝ) ≤ u := Nat.floor_le ((inverseHerbrandFun_nonneg_iff G S).2 (Nat.cast_nonneg n))
  have hφ := herbrandFun_of_natCast_le_of_le_add_one G S m hm₁ (Nat.lt_floor_add_one u).le
  rw [herbrandFun_inverseHerbrandFun, eq_div_iff (by exact_mod_cast Nat.card_pos.ne')] at hφ
  have hdvd (i : ℤ) (hi : i ≤ (m + 1 : ℕ)) : g (m + 1 : ℕ) ∣ g i :=
    Subgroup.card_dvd_of_le (ramificationGroup_antitone G S hi)
  obtain ⟨c, hc⟩ := (Int.natCast_dvd_natCast.2 (dvd_mul_of_dvd_right (hdvd 0 (by omega)) n)).sub
    (Int.natCast_dvd_natCast.2 (Finset.dvd_sum (s := Finset.Icc 1 m) fun i hi ↦
      hdvd i (by have := (Finset.mem_Icc.1 hi).2; omega)))
  have hcu : u - m = c := mul_right_cancel₀ (b := (g (m + 1 : ℕ) : ℝ))
    (by exact_mod_cast Nat.card_pos.ne') <| by
      linear_combination -hφ + (by exact_mod_cast hc :
        (n : ℝ) * g 0 - ∑ i ∈ Finset.Icc 1 m, (g i : ℝ) = g (m + 1 : ℕ) * c)
  have hc_bounds : 0 ≤ c ∧ c < 1 := ⟨by exact_mod_cast (hcu ▸ sub_nonneg.2 hm₁ : (0 : ℝ) ≤ c),
    by exact_mod_cast (hcu ▸ by linarith [Nat.lt_floor_add_one u] : (c : ℝ) < 1)⟩
  have hc_zero : c = 0 := by omega
  simp only [hc_zero, Int.cast_zero, sub_eq_zero] at hcu
  rw [psiNat_def, ← hcu]
/-- Arithmetic characterization: `ψℕ(n) = m ↔ #G_1 + ⋯ + #G_m = n · #G_0`. -/
theorem psiNat_eq_iff {n m : ℕ} : psiNat G S n = m ↔
    ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
      n * Nat.card (ramificationGroup G S 0) := by
  rw [← Nat.cast_inj (R := ℝ), coe_psiNat, ← herbrandFun_inj G S, herbrandFun_inverseHerbrandFun,
    eq_comm, herbrandFun_natCast, div_eq_iff (by exact_mod_cast Nat.card_pos.ne')]; norm_cast
/-- Upper-bound characterization `ψℕ(n) ≤ m ↔ (n : ℝ) ≤ φ(m)`. -/
theorem psiNat_le_iff {n m : ℕ} : psiNat G S n ≤ m ↔ (n : ℝ) ≤ herbrandFun G S m := by
  rw [← Nat.cast_le (α := ℝ), coe_psiNat, inverseHerbrandFun_le_iff]
@[simp] theorem psiNat_zero : psiNat G S 0 = 0 := (psiNat_eq_iff G S).2 (by simp)
/-- The integral inverse Herbrand function `ψℕ` is strictly increasing. -/
theorem psiNat_strictMono : StrictMono (psiNat G S) := fun _ _ h ↦ by
  rw [← Nat.cast_lt (α := ℝ)]; simp [h]
/-- For every `n : ℕ`, `n ≤ ψℕ(n)`. -/
theorem self_le_psiNat (n : ℕ) : n ≤ psiNat G S n := (psiNat_strictMono G S).id_le n
/-- `psiNat G S n = n` if and only if the lower filtration is constant through `n` (`G_n = G_0`). -/
@[simp] theorem psiNat_eq_self_iff {n : ℕ} :
    psiNat G S n = n ↔ ramificationGroup G S n = ramificationGroup G S 0 := by
  have hle (i : ℕ) := ramificationGroup_antitone G S (Int.natCast_nonneg i)
  rw [psiNat_eq_iff]; refine ⟨fun h ↦ ?_, fun hn ↦ ?_⟩
  · rcases n with _ | k; · simp
    have hk := Finset.sum_le_card_nsmul (Finset.Icc 1 k)
      (fun i : ℕ ↦ Nat.card (ramificationGroup G S i)) _ fun i _ ↦ Subgroup.card_le_of_le (hle i)
    rw [Finset.sum_Icc_succ_top (by omega), add_mul] at h
    simp only [Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul] at hk
    exact Subgroup.eq_of_le_of_card_ge (hle _) (by omega)
  · rw [Finset.sum_congr rfl fun i hi ↦ by rw [le_antisymm (hle i) (hn.symm.le.trans
      (ramificationGroup_antitone G S (by have := (Finset.mem_Icc.1 hi).2; omega)))]]; simp
/-- Evaluating the upper filtration at `φ(u)` recovers the lower filtration `G_u`. -/
@[simp] theorem upperRamificationGroup_herbrandFun (u : ℝ) :
    upperRamificationGroup G S (herbrandFun G S u) = ramificationGroupReal G S u := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_herbrandFun]
/-- At `n : ℕ`, the upper ramification group `G^n` equals the lower group `G_{ψℕ(n)}`. -/
@[simp] theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S n = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast, ramificationGroupReal_intCast]
/-- The upper ramification filtration is decreasing. -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup G S) :=
  fun _ _ h ↦ ramificationGroupReal_antitone G S ((inverseHerbrandFun_strictMono G S).monotone h)
/-- On `[-1, 0]`, the upper and lower ramification filtrations agree. -/
theorem upperRamificationGroup_eq_ramificationGroupReal_of_neg_one_le_of_nonpos {v : ℝ}
    (h₁ : -1 ≤ v) (h₀ : v ≤ 0) : upperRamificationGroup G S v = ramificationGroupReal G S v := by
  rw [upperRamificationGroup_def, inverseHerbrandFun_eq_self_of_neg_one_le_of_nonpos G S h₁ h₀]
@[simp] theorem upperRamificationGroup_zero :
    upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  simpa using upperRamificationGroup_natCast G S 0
/-- Below `-1`, the upper ramification group is the full group `⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ :=
  ramificationGroupReal_eq_top_of_le_neg_one G S ((inverseHerbrandFun_le_neg_one_iff G S).2 hv)
@[simp] theorem upperRamificationGroup_neg_one : upperRamificationGroup G S (-1) = ⊤ :=
  upperRamificationGroup_eq_top_of_le_neg_one G S le_rfl
/-- For a finite group `G` and Noetherian `S`, `⨅ v, G^v` is the kernel of the action. -/
theorem iInf_upperRamificationGroup_eq_ker [IsNoetherianRing S] :
    ⨅ v : ℝ, upperRamificationGroup G S v = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  rw [← iInf_ramificationGroup_eq_ker G S]
  exact le_antisymm (le_iInf fun i ↦ (iInf_le _ (herbrandFun G S i)).trans_eq (by simp))
    (le_iInf fun _ ↦ by
      rw [upperRamificationGroup_def, ramificationGroupReal_def]; exact iInf_le _ _)
/-- For a finite group `G` acting faithfully on Noetherian `S`, `⨅ v, G^v = ⊥`. -/
theorem iInf_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ⨅ v : ℝ, upperRamificationGroup G S v = ⊥ := by
  rw [iInf_upperRamificationGroup_eq_ker, TauCeti.MulSemiringAction.ker_toRingAut_eq_bot]
/-- For a finite group `G` and Noetherian `S`, `G^v` stabilizes at the kernel for large `v`. -/
theorem exists_forall_upperRamificationGroup_eq_ker [IsNoetherianRing S] :
    ∃ V : ℝ, ∀ v : ℝ, V ≤ v →
      upperRamificationGroup G S v = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_ker G S
  refine ⟨herbrandFun G S N, fun _ hv ↦ ?_⟩
  rw [upperRamificationGroup_def, ramificationGroupReal_def]
  exact hN _ (Int.le_ceil_iff.2 (by linarith [(le_inverseHerbrandFun_iff G S).2 hv]))
/-- For a finite group `G` acting faithfully on Noetherian `S`, `G^v = ⊥` for large `v`. -/
theorem exists_forall_upperRamificationGroup_eq_bot [IsNoetherianRing S] [FaithfulSMul G S] :
    ∃ V : ℝ, ∀ v : ℝ, V ≤ v → upperRamificationGroup G S v = ⊥ := by
  simpa [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot] using
    exists_forall_upperRamificationGroup_eq_ker G S
/-- **Subgroup trace identity**: for finite `G` and `H ≤ G`, `(G^u) ∩ H = H^{φ_H(ψ_G(u))}`. -/
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal,
    upperRamificationGroup_herbrandFun]
/-- `herbrandFun G S u` is an upper break if and only if `u` is a lower break. -/
@[simp] theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [upperJump_iff, lowerJump_iff]; refine ⟨fun h v huv ↦ ?_, fun h _ huv ↦ ?_⟩
  · simpa using h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
  · rw [upperRamificationGroup_herbrandFun, upperRamificationGroup_def]
    exact h _ ((lt_inverseHerbrandFun_iff G S).2 huv)
/-- `inverseHerbrandFun G S v` is a lower break if and only if `v` is an upper break. -/
@[simp] theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa using (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm
variable {G S} in
/-- Every upper break of a finite group action is at least `-1`. -/
theorem UpperJump.neg_one_le {v : ℝ} (hv : UpperJump G S v) : -1 ≤ v :=
  (neg_one_le_inverseHerbrandFun_iff G S).1
    ((lowerJump_inverseHerbrandFun_iff G S v).2 hv).neg_one_le
end Finite
end TauCeti.IsLocalRing
