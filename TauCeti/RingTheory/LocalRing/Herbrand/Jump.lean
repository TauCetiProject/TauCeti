/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Herbrand.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic

/-!
# Upper ramification jumps, `psiNat`, and transport of Herbrand functions on a local ring

This module extends `TauCeti.RingTheory.LocalRing.Herbrand.Basic` with:
* `TauCeti.IsLocalRing.UpperJump`: upper breaks of the ramification filtration of a finite group
  acting on a local ring, and their correspondence with `LowerJump`.
* `TauCeti.IsLocalRing.psiNat`: the integral inverse Herbrand function `ψℕ : ℕ → ℕ`.
* `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup`: the subgroup trace identity
  `(G^u).subgroupOf H = H^{φ_H(ψ_G(u))}`.
* Order/sign `simp` lemmas, behavior below `-1`, trivial-inertia simplifications, kernel
  stabilization, and transport along bijective action-compatible homomorphisms.

Adapts `NumberTheory/LocalField/Herbrand/{Basic,Jump,Quotient}.lean`.

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

/-- An **upper break** of the ramification filtration of a finite group `G`: `G^v < G^u` for every
`v > u`. -/
def UpperJump (u : ℝ) : Prop :=
  ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u

theorem upperJump_iff (u : ℝ) : UpperJump G S u ↔
    ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u := Iff.rfl

/-- The **integral inverse Herbrand function** `ψℕ : ℕ → ℕ` (`coe_psiNat`) for a finite group
`G`. -/
def psiNat (n : ℕ) : ℕ := ⌊inverseHerbrandFun G S n⌋₊

theorem psiNat_def (n : ℕ) : psiNat G S n = ⌊inverseHerbrandFun G S n⌋₊ := (rfl)

end Defs

section Finite
variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]

/-- Below `-1`, `herbrandFun` is affine of slope `#G / #G_0` passing through `(-1, -1)`. -/
theorem herbrandFun_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    herbrandFun G S u = -1 + (u + 1) * (Nat.card G / Nat.card (ramificationGroup G S 0)) := by
  have h := herbrandFun_sub_herbrandFun_of_forall_eq G S hu (H := ⊤) fun _ _ ht ↦
    ramificationGroupReal_eq_top_of_le_neg_one G S ht
  rw [herbrandFun_neg_one, Nat.card_congr Subgroup.topEquiv.toEquiv] at h
  linarith

/-- Arithmetic core of Serre's lemma: if `#G_0 · n = ∑ k ∈ range j, #G_k` in `ℕ∞` with `n ≠ ⊤`,
then `φ_G(j - 1) = n.toNat - 1`. Adapts
`TauCeti.LocalFieldsRamification.coe_herbrand_lowerIndex_sub_one` from
`NumberTheory/LocalField/Herbrand/Quotient.lean`. -/
theorem herbrandFun_sub_one_of_card_mul_eq_sum {j : ℕ} {n : ℕ∞} (hn : n ≠ ⊤)
    (hsum : (Nat.card (ramificationGroup G S 0) : ℕ∞) * n =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup G S k) : ℕ∞)) :
    herbrandFun G S ((j : ℝ) - 1) = (n.toNat : ℝ) - 1 := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hn
  rw [← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [ENat.toNat_natCast]
  rcases j with _ | m
  · rw [herbrandFun_eq_self_of_mem_Icc G S ⟨by norm_num, by norm_num⟩]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast,
      div_eq_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    linear_combination -(by exact_mod_cast hsum : (Nat.card (ramificationGroup G S 0) : ℝ) * n =
      Nat.card (ramificationGroup G S 0) +
        ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup G S i) : ℝ))

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

/-- For finite `G`, `ψ(v)` is the least `u : ℝ` satisfying `v ≤ φ(u)`. -/
theorem isLeast_inverseHerbrandFun (v : ℝ) :
    IsLeast {u : ℝ | v ≤ herbrandFun G S u} (inverseHerbrandFun G S v) :=
  ⟨(herbrandFun_inverseHerbrandFun G S v).ge, fun _ hu ↦ inverseHerbrandFun_le_iff.2 hu⟩

@[simp] theorem herbrandFun_le_neg_one_iff {u : ℝ} : herbrandFun G S u ≤ -1 ↔ u ≤ -1 := by
  rw [← le_inverseHerbrandFun_iff, inverseHerbrandFun_neg_one]

@[simp] theorem neg_one_lt_herbrandFun_iff {u : ℝ} : -1 < herbrandFun G S u ↔ -1 < u :=
  lt_iff_lt_of_le_iff_le (herbrandFun_le_neg_one_iff G S)

@[simp] theorem herbrandFun_lt_neg_one_iff {u : ℝ} : herbrandFun G S u < -1 ↔ u < -1 :=
  lt_iff_lt_of_le_iff_le neg_one_le_herbrandFun_iff

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

@[simp] theorem inverseHerbrandFun_le_neg_one_iff {v : ℝ} :
    inverseHerbrandFun G S v ≤ -1 ↔ v ≤ -1 := inverseHerbrandFun_le_iff.trans (by simp)

@[simp] theorem neg_one_lt_inverseHerbrandFun_iff {v : ℝ} :
    -1 < inverseHerbrandFun G S v ↔ -1 < v := lt_inverseHerbrandFun_iff.trans (by simp)

@[simp] theorem inverseHerbrandFun_lt_neg_one_iff {v : ℝ} :
    inverseHerbrandFun G S v < -1 ↔ v < -1 := inverseHerbrandFun_lt_iff.trans (by simp)

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

/-- When inertia is trivial (`G_0 = ⊥`), `herbrandFun` is the identity on `[-1, ∞)`. -/
theorem herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot (h0 : ramificationGroup G S 0 = ⊥)
    {u : ℝ} (hu : -1 ≤ u) : herbrandFun G S u = u := by
  rcases le_or_gt u 0 with hu0 | hu0
  · exact herbrandFun_eq_self_of_mem_Icc G S ⟨hu, hu0⟩
  have h := herbrandFun_sub_herbrandFun_of_forall_eq G S hu0.le (H := ⊥) fun _ ht _ ↦ eq_bot_iff.2
    ((ramificationGroupReal_antitone G S ht.le).trans
      (by rw [← Int.cast_zero, ramificationGroupReal_intCast, h0]))
  rw [h0, div_self (by exact_mod_cast Nat.card_pos.ne'), herbrandFun_zero] at h
  linarith

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

/-- For every `n : ℕ`, `inverseHerbrandFun G S n` is the natural number `psiNat G S n`. -/
@[simp] theorem coe_psiNat (n : ℕ) : (psiNat G S n : ℝ) = inverseHerbrandFun G S n := by
  obtain ⟨m, hm⟩ := exists_inverseHerbrandFun_natCast_eq_natCast G S n
  rw [psiNat_def, hm, Nat.floor_natCast]

/-- Arithmetic characterization: `ψℕ(n) = m ↔ #G_1 + ⋯ + #G_m = n · #G_0`. -/
theorem psiNat_eq_iff {n m : ℕ} : psiNat G S n = m ↔
    ∑ i ∈ Finset.Icc 1 m, Nat.card (ramificationGroup G S i) =
      n * Nat.card (ramificationGroup G S 0) := by
  rw [← Nat.cast_inj (R := ℝ), coe_psiNat, inverseHerbrandFun_natCast_eq_natCast_iff]

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
  rw [psiNat_eq_iff]
  refine ⟨fun h ↦ ?_, fun hn ↦ ?_⟩
  · rcases n with _ | k
    · simp
    have hk := Finset.sum_le_card_nsmul (Finset.Icc 1 k)
      (fun i : ℕ ↦ Nat.card (ramificationGroup G S i)) _ fun i _ ↦ Subgroup.card_le_of_le (hle i)
    rw [Finset.sum_Icc_succ_top (by omega), add_mul] at h
    simp only [Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul] at hk
    exact Subgroup.eq_of_le_of_card_ge (hle _) (by omega)
  · rw [Finset.sum_congr rfl fun i hi ↦ by rw [le_antisymm (hle i) (hn.symm.le.trans
      (ramificationGroup_antitone G S (by have := (Finset.mem_Icc.1 hi).2; omega)))]]
    simp

/-- At `n : ℕ`, the upper ramification group `G^n` equals the lower group `G_{ψℕ(n)}`. -/
@[simp] theorem upperRamificationGroup_natCast (n : ℕ) :
    upperRamificationGroup G S n = ramificationGroup G S (psiNat G S n) := by
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast, ramificationGroupReal_intCast]

@[simp] theorem upperRamificationGroup_zero :
    upperRamificationGroup G S 0 = ramificationGroup G S 0 := by
  simpa using upperRamificationGroup_natCast G S 0

/-- Below `-1`, the upper ramification group is the full group `⊤`. -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    upperRamificationGroup G S v = ⊤ := by
  rw [upperRamificationGroup_def]
  exact ramificationGroupReal_eq_top_of_le_neg_one G S
    ((inverseHerbrandFun_le_neg_one_iff G S).2 hv)

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
  exact hN _ (Int.le_ceil_iff.2 (by linarith [le_inverseHerbrandFun_iff.2 hv]))

/-- **Subgroup trace identity**: for finite `G` and `H ≤ G`, `(G^u) ∩ H = H^{φ_H(ψ_G(u))}`. -/
theorem subgroupOf_upperRamificationGroup (H : Subgroup G) (u : ℝ) :
    (upperRamificationGroup G S u).subgroupOf H =
      upperRamificationGroup H S (herbrandFun H S (inverseHerbrandFun G S u)) := by
  rw [upperRamificationGroup_def, subgroupOf_ramificationGroupReal,
    upperRamificationGroup_herbrandFun]

/-- `herbrandFun G S u` is an upper break if and only if `u` is a lower break. -/
@[simp] theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [upperJump_iff, lowerJump_iff]
  refine ⟨fun h v huv ↦ ?_, fun h _ huv ↦ ?_⟩
  · simpa using h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
  · rw [upperRamificationGroup_herbrandFun, upperRamificationGroup_def]
    exact h _ (lt_inverseHerbrandFun_iff.2 huv)

/-- `inverseHerbrandFun G S v` is a lower break if and only if `v` is an upper break. -/
@[simp] theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa using (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

variable {G S} in
/-- Every upper break of a finite group action is at least `-1`. -/
theorem UpperJump.neg_one_le {v : ℝ} (hv : UpperJump G S v) : -1 ≤ v :=
  neg_one_le_inverseHerbrandFun_iff.1
    ((lowerJump_inverseHerbrandFun_iff G S v).2 hv).neg_one_le

end Finite

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
    Nat.card_congr ((Equiv.ofBijective φ hφ).subtypeEquiv fun _ ↦ by
      simp only [he i, Subgroup.mem_comap, Equiv.ofBijective_apply])
  simp only [herbrandFun_def, ramificationGroupReal_def, hcard]

/-- A bijective `φ : G →* H` pulling back lower groups preserves `inverseHerbrandFun`. -/
theorem inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (v : ℝ) :
    inverseHerbrandFun G S v = inverseHerbrandFun H T v := by
  simp only [inverseHerbrandFun_def, herbrandFun_eq_of_ramificationGroup_eq_comap hφ he]

/-- A bijective `φ : G →* H` pulling back lower groups pulls back `upperRamificationGroup`. -/
theorem upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap (v : ℝ) :
    upperRamificationGroup G S v = (upperRamificationGroup H T v).comap φ := by
  simp only [upperRamificationGroup_def,
    inverseHerbrandFun_eq_of_ramificationGroup_eq_comap hφ he, ramificationGroupReal_def, he]

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
theorem upperJump_iff_of_smul_eq (u : ℝ) :
    UpperJump G S u ↔ UpperJump H S u :=
  upperJump_iff_of_ramificationGroup_eq_comap hφ (ramificationGroup_eq_comap_of_smul_eq he) u

end SMul
end Actions
end Transport

section Subsingleton
variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  [Subsingleton G]

@[simp] theorem herbrandFun_of_subsingleton (u : ℝ) : herbrandFun G S u = u := by
  rcases le_total (-1) u with hu | hu
  · exact herbrandFun_eq_self_of_ramificationGroup_zero_eq_bot G S (Subsingleton.elim _ _) hu
  · rw [herbrandFun_of_le_neg_one G S hu, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩,
      Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩]
    norm_num

@[simp] theorem inverseHerbrandFun_of_subsingleton (v : ℝ) :
    inverseHerbrandFun G S v = v := by simpa using inverseHerbrandFun_herbrandFun G S v

end Subsingleton

end TauCeti.IsLocalRing
