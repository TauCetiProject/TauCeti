/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Wohlfahrt

/-!
# The congruence closure of a subgroup of `SL(2, ℤ)`

The **congruence closure** `Γ.congruenceClosure` of a subgroup `Γ ≤ SL(2, ℤ)` is the intersection
of all congruence subgroups containing `Γ`. Unconditionally, it is a monotone, idempotent closure
operation fixing every congruence subgroup, commuting with conjugation and with adjoining the
center `±I`, preserving normality, and preserving the image of `Γ` under reduction modulo every
positive integer `N`.

When `Γ` has positive strict level (in particular, whenever `Γ` has finite index), strict
Wohlfahrt's theorem identifies the congruence closure concretely as
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`: every congruence subgroup containing `Γ` has strict
level dividing `Γ.strictLevel` and hence contains `Γ(Γ.strictLevel)`. Consequently,
`Γ.congruenceClosure` is itself a congruence subgroup, and `Γ` is a congruence subgroup if and only
if `Γ.congruenceClosure = Γ`. Moreover, if `±Γ` is a congruence subgroup while `Γ` itself is not
(a noncongruence lift of a projective congruence subgroup), then `Γ.congruenceClosure = ±Γ`.

## Main declarations

* `Subgroup.congruenceClosure`: the intersection of all congruence subgroups containing `Γ`.
* `Subgroup.congruenceClosure_def`, `Subgroup.mem_congruenceClosure_iff`,
  `Subgroup.le_congruenceClosure`, `Subgroup.congruenceClosure_le_iff`: definition, membership,
  and universal property.
* `Subgroup.congruenceClosure_mono`, `Subgroup.congruenceClosure_idem`,
  `Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup`: closure-operator laws.
* `Subgroup.congruenceClosure_conjAct_smul`, `Subgroup.instNormalCongruenceClosure`,
  `Subgroup.congruenceClosure_withCenter`: interaction with conjugation, normality, and `±I`.
* `Subgroup.map_congruenceClosure_intCast_zmod`: `Γ` and `Γ.congruenceClosure` have the same
  image in `SL(2, ZMod N)` for every `N ≠ 0`.
* `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel`: for `Γ` with `Γ.strictLevel ≠ 0`,
  `Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`.
* `Subgroup.isCongruenceSubgroup_congruenceClosure`, `Subgroup.congruenceClosure_eq_self_iff`:
  for `Γ` with `Γ.strictLevel ≠ 0`, `Γ.congruenceClosure` is a congruence subgroup and equals `Γ`
  if and only if `Γ` is a congruence subgroup.
* `Subgroup.congruenceClosure_eq_self_or_withCenter`, `Subgroup.congruenceClosure_eq_withCenter`:
  when `±Γ` is a congruence subgroup, `Γ.congruenceClosure` is either `Γ` or `±Γ`, and equals `±Γ`
  when `Γ` itself is not a congruence subgroup.
* `CongruenceSubgroup.congruenceClosure_Gamma`, `CongruenceSubgroup.congruenceClosure_Gamma0`,
  `CongruenceSubgroup.congruenceClosure_Gamma1`: `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)` are fixed by the
  congruence closure at every level `N : ℕ` (including `N = 0`).

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt, and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups Pointwise

namespace Subgroup

variable {Γ Γ₁ Γ₂ Δ : Subgroup SL(2, ℤ)}

/-- The **congruence closure** of `Γ ≤ SL(2, ℤ)`: the intersection of all congruence subgroups
containing `Γ`. When `Γ.strictLevel ≠ 0` (in particular, when `Γ` has finite index),
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)` is the smallest congruence subgroup containing `Γ`. -/
def congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  sInf {Δ : Subgroup SL(2, ℤ) | IsCongruenceSubgroup Δ ∧ Γ ≤ Δ}

/-- Unfolding: `Γ.congruenceClosure` is the infimum of all congruence subgroups containing `Γ`. -/
theorem congruenceClosure_def (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure = sInf {Δ : Subgroup SL(2, ℤ) | IsCongruenceSubgroup Δ ∧ Γ ≤ Δ} := (rfl)

/-- Characteristic membership for `congruenceClosure`: an element lies in `Γ.congruenceClosure`
if and only if it lies in every congruence subgroup containing `Γ`. -/
theorem mem_congruenceClosure_iff {g : SL(2, ℤ)} :
    g ∈ Γ.congruenceClosure ↔ ∀ Δ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Δ → Γ ≤ Δ → g ∈ Δ := by
  simp [congruenceClosure_def, Subgroup.mem_sInf]

/-- Every subgroup is contained in its congruence closure. -/
theorem le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Γ ≤ Γ.congruenceClosure :=
  le_sInf fun _ h ↦ h.2

/-- **Universal property of `congruenceClosure`**: a congruence subgroup contains
`Γ.congruenceClosure` if and only if it contains `Γ`. -/
theorem congruenceClosure_le_iff (hΔ : IsCongruenceSubgroup Δ) :
    Γ.congruenceClosure ≤ Δ ↔ Γ ≤ Δ :=
  ⟨(le_congruenceClosure Γ).trans, fun h ↦ sInf_le ⟨hΔ, h⟩⟩

/-- The congruence closure is monotone with respect to subgroup inclusion. -/
theorem congruenceClosure_mono : Monotone Subgroup.congruenceClosure :=
  fun _ _ h ↦ le_sInf fun _ hΔ ↦ sInf_le ⟨hΔ.1, h.trans hΔ.2⟩

/-- The congruence closure is idempotent, with no finiteness assumption on `Γ`. -/
@[simp]
theorem congruenceClosure_idem (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.congruenceClosure = Γ.congruenceClosure :=
  le_antisymm (le_sInf fun _ hΔ ↦ sInf_le ⟨hΔ.1, sInf_le hΔ⟩) (le_congruenceClosure _)

/-- Every congruence subgroup equals its own congruence closure. -/
theorem congruenceClosure_eq_self_of_isCongruenceSubgroup (h : IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ :=
  le_antisymm ((congruenceClosure_le_iff h).mpr le_rfl) (le_congruenceClosure Γ)

/-- The congruence closure of `SL(2, ℤ)` is `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_top : (⊤ : Subgroup SL(2, ℤ)).congruenceClosure = ⊤ :=
  top_unique (le_congruenceClosure ⊤)

/-- The congruence closure of the trivial subgroup is trivial. -/
@[simp]
theorem congruenceClosure_bot : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦ mem_bot.mpr ?_
  have hmem : ∀ M : ℕ, M ≠ 0 → g ∈ Gamma M := fun M hM ↦
    have : NeZero M := ⟨hM⟩
    (congruenceClosure_le_iff (Gamma_is_cong_sub M)).mpr bot_le hg
  ext i j
  have hdvd : ∀ M : ℕ, M ≠ 0 →
      (M : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro M hM
    simpa [Matrix.one_apply] using
      Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp (hmem M hM) i j
  set x := (g : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
  have hx : x = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd (x.natAbs + 1) (Nat.succ_ne_zero _)) (by omega)
  exact sub_eq_zero.mp hx

/-- Conjugation in `SL(2, ℤ)` commutes with the congruence closure. -/
@[simp]
theorem congruenceClosure_conjAct_smul (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ)) :
    (g • Γ).congruenceClosure = g • Γ.congruenceClosure := by
  have hle : ∀ (a : ConjAct SL(2, ℤ)) (H : Subgroup SL(2, ℤ)),
      a⁻¹ • (a • H).congruenceClosure ≤ H.congruenceClosure := fun a H ↦
    le_sInf fun Δ ⟨hΔ, hHΔ⟩ ↦ by
      rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a), smul_inv_smul]
      exact (congruenceClosure_le_iff ((isCongruenceSubgroup_conjAct_smul_iff a).mpr hΔ)).mpr
        (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHΔ)
  refine le_antisymm ?_ ?_
  · simpa [smul_inv_smul] using
      (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := g)).mpr (hle g Γ)
  · simpa [inv_inv, inv_smul_smul] using hle g⁻¹ (g • Γ)

/-- The congruence closure of a normal subgroup of `SL(2, ℤ)` is normal. -/
instance instNormalCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.Normal] :
    Γ.congruenceClosure.Normal where
  conj_mem x hx g := by
    have hEq : ConjAct.toConjAct g • Γ.congruenceClosure = Γ.congruenceClosure := by
      rw [← congruenceClosure_conjAct_smul, Subgroup.Normal.conjAct ‹Γ.Normal›]
    rw [← hEq]
    exact ⟨x, hx, rfl⟩

/-- Adjoining the center `{±I}` commutes with the congruence closure, for every subgroup
`Γ ≤ SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_withCenter (Γ : Subgroup SL(2, ℤ)) :
    Γ.withCenter.congruenceClosure = Γ.congruenceClosure.withCenter := by
  refine le_antisymm ?_ (withCenter_le_iff.mpr
    ⟨congruenceClosure_mono Γ.le_withCenter, Γ.center_le_withCenter.trans (le_congruenceClosure _)⟩)
  intro g hg
  by_contra hnot
  have hg_not : g ∉ Γ.congruenceClosure := fun h ↦ hnot (le_withCenter _ h)
  have hng_not : -g ∉ Γ.congruenceClosure := fun h ↦ hnot <|
    mem_withCenter_iff.mpr ⟨-g, h, -1,
      Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (.inr rfl), by simp⟩
  rw [mem_congruenceClosure_iff] at hg_not hng_not
  push Not at hg_not hng_not
  obtain ⟨Δ₁, hΔ₁, hΓΔ₁, hg₁⟩ := hg_not
  obtain ⟨Δ₂, hΔ₂, hΓΔ₂, hg₂⟩ := hng_not
  have hΔ : IsCongruenceSubgroup (Δ₁ ⊓ Δ₂).withCenter :=
    isCongruenceSubgroup_trans _ _ (le_withCenter _) (isCongruenceSubgroup_inf_iff.mpr ⟨hΔ₁, hΔ₂⟩)
  have hle : Γ.withCenter ≤ (Δ₁ ⊓ Δ₂).withCenter :=
    withCenter_le_iff.mpr ⟨(le_inf hΓΔ₁ hΓΔ₂).trans (le_withCenter _), center_le_withCenter _⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := mem_withCenter_iff.mp (mem_congruenceClosure_iff.mp hg _ hΔ hle)
  rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with rfl | rfl
  · exact hg₁ (by simpa using hγ.1)
  · exact hg₂ (by simpa using hγ.2)

/-- `Γ` and its congruence closure have the same image under reduction modulo every positive `N`. -/
@[simp]
theorem map_congruenceClosure_intCast_zmod (Γ : Subgroup SL(2, ℤ)) (N : ℕ) [NeZero N] :
    Γ.congruenceClosure.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) := by
  set φ : SL(2, ℤ) →* SL(2, ZMod N) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))
  have hsup : IsCongruenceSubgroup (Γ ⊔ Gamma N) :=
    isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub N)
  refine le_antisymm ?_ (Subgroup.map_mono (le_congruenceClosure Γ))
  calc Γ.congruenceClosure.map φ
      ≤ (Γ ⊔ Gamma N).map φ := Subgroup.map_mono ((congruenceClosure_le_iff hsup).mpr le_sup_left)
    _ = Γ.map φ ⊔ (Gamma N).map φ := Subgroup.map_sup _ _ _
    _ = Γ.map φ := by rw [Gamma, Subgroup.map_ker_self, sup_bot_eq]

/-- **Wohlfahrt characterization of the congruence closure**: when `Γ.strictLevel ≠ 0` (in
particular, when `Γ` has finite index), `Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel (Γ : Subgroup SL(2, ℤ))
    [NeZero Γ.strictLevel] :
    Γ.congruenceClosure = Γ ⊔ Gamma Γ.strictLevel := by
  refine le_antisymm ?_ ?_
  · exact (congruenceClosure_le_iff
      (isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub _))).mpr le_sup_left
  · refine le_sInf fun Δ ⟨hΔ, hΓΔ⟩ ↦ sup_le hΓΔ ?_
    exact (Gamma_le_Gamma_of_dvd (strictLevel_dvd_of_le hΓΔ)).trans hΔ.Gamma_strictLevel_le

/-- When `Γ.strictLevel ≠ 0` (in particular, when `Γ` has finite index), `Γ.congruenceClosure` is
a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    IsCongruenceSubgroup Γ.congruenceClosure := by
  rw [congruenceClosure_eq_sup_Gamma_strictLevel]
  exact isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub _)

/-- A subgroup `Γ ≤ SL(2, ℤ)` with `Γ.strictLevel ≠ 0` (in particular, any finite-index subgroup)
equals its congruence closure if and only if it is a congruence subgroup. -/
theorem congruenceClosure_eq_self_iff (Γ : Subgroup SL(2, ℤ)) [NeZero Γ.strictLevel] :
    Γ.congruenceClosure = Γ ↔ IsCongruenceSubgroup Γ :=
  ⟨fun h ↦ h ▸ isCongruenceSubgroup_congruenceClosure Γ,
    congruenceClosure_eq_self_of_isCongruenceSubgroup⟩

/-- If `±Γ` is a congruence subgroup, then the congruence closure of `Γ` is either `Γ` itself or
`±Γ`. -/
theorem congruenceClosure_eq_self_or_withCenter (hcong : IsCongruenceSubgroup Γ.withCenter) :
    Γ.congruenceClosure = Γ ∨ Γ.congruenceClosure = Γ.withCenter := by
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
  · have hwith : Γ.withCenter = Γ := by simp [hneg]
    exact .inl (congruenceClosure_eq_self_of_isCongruenceSubgroup (hwith ▸ hcong))
  · have hle₁ : Γ ≤ Γ.congruenceClosure := le_congruenceClosure Γ
    have hle₂ : Γ.congruenceClosure ≤ Γ.withCenter :=
      (congruenceClosure_le_iff hcong).mpr Γ.le_withCenter
    have hmul : Γ.relIndex Γ.congruenceClosure * Γ.congruenceClosure.relIndex Γ.withCenter = 2 := by
      rw [Subgroup.relIndex_mul_relIndex (H := Γ) (K := Γ.congruenceClosure) (L := Γ.withCenter)
        hle₁ hle₂,
        Matrix.SpecialLinearGroup.relIndex_withCenter_eq_two_of_neg_one_notMem hneg]
    have hdvd : Γ.congruenceClosure.relIndex Γ.withCenter ∣ 2 := ⟨_, by rw [mul_comm, hmul]⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact .inr (le_antisymm hle₂ (Subgroup.relIndex_eq_one.mp h1))
    · rw [h2, mul_eq_right₀ two_ne_zero] at hmul
      exact .inl (le_antisymm (Subgroup.relIndex_eq_one.mp hmul) hle₁)

/-- **Congruence closure of a noncongruence lift**: if `±Γ` is a congruence subgroup while `Γ` is
not, then the congruence closure of `Γ` is `±Γ`. -/
theorem congruenceClosure_eq_withCenter
    (hcong : IsCongruenceSubgroup Γ.withCenter) (hnot : ¬ IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ.withCenter := by
  have : Γ.withCenter.FiniteIndex := hcong.finiteIndex
  have : NeZero Γ.strictLevel :=
    ⟨ne_zero_of_dvd_ne_zero (mul_ne_zero two_ne_zero (NeZero.ne _))
      Γ.strictLevel_dvd_two_mul_strictLevel_withCenter⟩
  exact (congruenceClosure_eq_self_or_withCenter hcong).resolve_left fun h ↦
    hnot ((congruenceClosure_eq_self_iff Γ).mp h)

end Subgroup

namespace CongruenceSubgroup

/-- `Γ(N)` equals its congruence closure at every level `N : ℕ`, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma (N : ℕ) : (Gamma N).congruenceClosure = Gamma N := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [Gamma_zero_bot, Subgroup.congruenceClosure_bot]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma_is_cong_sub N)

/-- `Γ₀(N)` equals its congruence closure at every level `N : ℕ`, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma0 (N : ℕ) : (Gamma0 N).congruenceClosure = Gamma0 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun g hg ↦ mem_Gamma0_iff_dvd.mpr ?_) (Subgroup.le_congruenceClosure _)
    have hdvd : ∀ M : ℕ, M ≠ 0 → (M : ℤ) ∣ g 1 0 := fun M hM ↦
      have : NeZero M := ⟨hM⟩
      mem_Gamma0_iff_dvd.mp
        ((Subgroup.congruenceClosure_le_iff (Gamma0_is_congruence M)).mpr
          (Gamma0_le_Gamma0_of_dvd (dvd_zero M)) hg)
    have h0 : g 1 0 = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd ((g 1 0).natAbs + 1) (Nat.succ_ne_zero _))
        (by omega)
    simp [h0]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma0_is_congruence N)

/-- `Γ₁(N)` equals its congruence closure at every level `N : ℕ`, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma1 (N : ℕ) : (Gamma1 N).congruenceClosure = Gamma1 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun g hg ↦ mem_Gamma1_iff_dvd_lowerRow.mpr ?_)
      (Subgroup.le_congruenceClosure _)
    have hdvd : ∀ M : ℕ, M ≠ 0 → (M : ℤ) ∣ g 1 0 ∧ (M : ℤ) ∣ g 1 1 - 1 := fun M hM ↦
      have : NeZero M := ⟨hM⟩
      mem_Gamma1_iff_dvd_lowerRow.mp
        ((Subgroup.congruenceClosure_le_iff (Gamma1_is_congruence M)).mpr
          (Gamma1_le_Gamma1_of_dvd (dvd_zero M)) hg)
    have h10 : g 1 0 = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd ((g 1 0).natAbs + 1) (Nat.succ_ne_zero _)).1
        (by omega)
    have h11 : g 1 1 - 1 = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
        (hdvd ((g 1 1 - 1).natAbs + 1) (Nat.succ_ne_zero _)).2 (by omega)
    simp [h10, h11]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma1_is_congruence N)

end CongruenceSubgroup
