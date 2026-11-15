/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Wohlfahrt
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The congruence closure of a subgroup of `SL(2, ℤ)`

For an arbitrary subgroup `Γ ≤ SL(2, ℤ)`, its **congruence closure** `Γ.congruenceClosure` is the
infimum of all congruence subgroups of `SL(2, ℤ)` containing `Γ`. This defines a conjugation-
equivariant closure operator on `Subgroup SL(2, ℤ)`.

Because infinite intersections of congruence subgroups need not be congruence subgroups—indeed
`⨅ (N ≠ 0), Γ(N) = ⊥`, so `(⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥`—`Γ.congruenceClosure` is
not always a congruence subgroup when `Γ` has infinite index. Whenever `Γ.strictLevel ≠ 0` (and in
particular for every finite-index subgroup `Γ`), Wohlfahrt's theorem in strict form collapses the
intersection to a single subgroup:
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`.
Equivalently, `Γ.congruenceClosure` is the preimage under `SL(2, ℤ) →* SL(2, ZMod Γ.strictLevel)`
of the reduction image of `Γ`, so it is always a congruence subgroup when `Γ` has finite index, and
`Γ.congruenceClosure = Γ` holds if and only if `Γ` is itself a congruence subgroup.

Notice that passing from `Γ` to `Γ.congruenceClosure` can strictly divide the strict level: a
noncongruence subgroup of strict level `8` can surject onto `SL(2, ZMod 8)` and thus have
congruence closure `⊤` of strict level `1`.

## Main definitions and results

* `CongruenceSubgroup.iInf_Gamma_ne_zero`: `⨅ (N ≠ 0), Γ(N) = ⊥` (residual finiteness of
  `SL(2, ℤ)` along principal congruence subgroups).
* `Subgroup.congruenceClosure`: the intersection of all congruence subgroups containing `Γ`.
* `Subgroup.le_congruenceClosure`, `Subgroup.congruenceClosure_le`,
  `Subgroup.congruenceClosure_mono`, `Subgroup.congruenceClosure_idem`: closure-operator laws.
* `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel`: for finite-index `Γ`,
  `Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)` (and more generally whenever `Γ.strictLevel ≠ 0`).
* `Subgroup.isCongruenceSubgroup_congruenceClosure`, `Subgroup.congruenceClosure_eq_self_iff`:
  for finite-index `Γ`, `Γ.congruenceClosure` is a congruence subgroup and equals `Γ` iff `Γ` is
  congruence.
* `Subgroup.congruenceClosure_eq_comap_map_zmod`, `Subgroup.map_zmod_congruenceClosure`,
  `Subgroup.index_congruenceClosure`, `Subgroup.congruenceClosure_eq_top_iff_map_zmod_eq_top`:
  description of `Γ.congruenceClosure` via the image of `Γ` in `SL(2, ZMod Γ.strictLevel)`.
* `Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`: if `Γ` is noncongruence
  while `Γ.withCenter` is congruence, then `Γ.congruenceClosure = Γ.withCenter`.
* `CongruenceSubgroup.congruenceClosure_Gamma`, `CongruenceSubgroup.congruenceClosure_Gamma0`,
  `CongruenceSubgroup.congruenceClosure_Gamma1`: `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)` are congruence-closed
  at every modulus `N` (including `N = 0`).

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt, and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. (2) 83 (2011), 96–120, §3.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

namespace CongruenceSubgroup

/-- If an integer `d` vanishes in `ZMod N` for every nonzero `N`, then `d = 0`. -/
private lemma int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero {d : ℤ}
    (h : ∀ N : ℕ, N ≠ 0 → (d : ZMod N) = 0) : d = 0 := by
  have hdvd : ((d.natAbs + 1 : ℕ) : ℤ) ∣ d :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd d (d.natAbs + 1)).mp (h (d.natAbs + 1) (Nat.succ_ne_zero _))
  have hnat : d.natAbs + 1 ∣ d.natAbs := Int.ofNat_dvd_left.mp hdvd
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hnat (Nat.lt_succ_self _))

/-- The intersection of all nonzero principal congruence subgroups `Γ(N)` in `SL(2, ℤ)` is
trivial. -/
@[simp]
theorem iInf_Gamma_ne_zero : (⨅ (N : ℕ) (_ : N ≠ 0), Gamma N) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  have hmem (N : ℕ) (hN : N ≠ 0) : γ ∈ Gamma N :=
    (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hγ) N)) hN
  have h00 : γ 0 0 - 1 = 0 :=
    int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun N hN ↦ by
      rw [Int.cast_sub, Int.cast_one, (Gamma_mem.mp (hmem N hN)).1, sub_self]
  have h01 : γ 0 1 = 0 :=
    int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun N hN ↦ (Gamma_mem.mp (hmem N hN)).2.1
  have h10 : γ 1 0 = 0 :=
    int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun N hN ↦ (Gamma_mem.mp (hmem N hN)).2.2.1
  have h11 : γ 1 1 - 1 = 0 :=
    int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun N hN ↦ by
      rw [Int.cast_sub, Int.cast_one, (Gamma_mem.mp (hmem N hN)).2.2.2, sub_self]
  ext i j
  fin_cases i <;> fin_cases j
  · exact sub_eq_zero.mp h00
  · exact h01
  · exact h10
  · exact sub_eq_zero.mp h11

end CongruenceSubgroup

namespace Subgroup

/-- The **congruence closure** of `Γ ≤ SL(2, ℤ)`: the intersection of all congruence subgroups of
`SL(2, ℤ)` containing `Γ`. When `Γ` has finite index (or more generally `Γ.strictLevel ≠ 0`), this
equals `Γ ⊔ Γ(Γ.strictLevel)` (`congruenceClosure_eq_sup_Gamma_strictLevel`). -/
def congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  sInf {Δ : Subgroup SL(2, ℤ) | CongruenceSubgroup.IsCongruenceSubgroup Δ ∧ Γ ≤ Δ}

/-- Unfolding lemma for `Subgroup.congruenceClosure`. -/
theorem congruenceClosure_def (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure =
      sInf {Δ : Subgroup SL(2, ℤ) | CongruenceSubgroup.IsCongruenceSubgroup Δ ∧ Γ ≤ Δ} := (rfl)

/-- Every subgroup of `SL(2, ℤ)` is contained in its congruence closure. -/
theorem le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Γ ≤ Γ.congruenceClosure :=
  le_sInf fun _ ⟨_, hle⟩ ↦ hle

/-- The congruence closure of `Γ` is contained in every congruence subgroup containing `Γ`. -/
theorem congruenceClosure_le {Γ Δ : Subgroup SL(2, ℤ)}
    (hΔ : CongruenceSubgroup.IsCongruenceSubgroup Δ) (hΓΔ : Γ ≤ Δ) :
    Γ.congruenceClosure ≤ Δ :=
  sInf_le ⟨hΔ, hΓΔ⟩

/-- Taking the congruence closure is monotone with respect to subgroup inclusion. -/
theorem congruenceClosure_mono {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} (h : Γ₁ ≤ Γ₂) :
    Γ₁.congruenceClosure ≤ Γ₂.congruenceClosure :=
  sInf_le_sInf fun _ ⟨hΔ, h₂⟩ ↦ ⟨hΔ, h.trans h₂⟩

/-- A congruence subgroup equals its own congruence closure. -/
theorem _root_.CongruenceSubgroup.IsCongruenceSubgroup.congruenceClosure_eq
    {Γ : Subgroup SL(2, ℤ)} (h : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ :=
  le_antisymm (Γ.congruenceClosure_le h le_rfl) Γ.le_congruenceClosure

/-- Taking the congruence closure is idempotent on all subgroups of `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_idem (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.congruenceClosure = Γ.congruenceClosure :=
  le_antisymm
    (le_sInf fun _ ⟨hΔ, hΓΔ⟩ ↦ congruenceClosure_le hΔ (congruenceClosure_le hΔ hΓΔ))
    Γ.congruenceClosure.le_congruenceClosure

/-- The strict level of `Γ.congruenceClosure` divides the strict level of `Γ`. -/
theorem strictLevel_congruenceClosure_dvd (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.strictLevel ∣ Γ.strictLevel :=
  strictLevel_dvd_of_le Γ.le_congruenceClosure

/-- Whenever `Γ.strictLevel ≠ 0`, the congruence closure of `Γ` is `Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero
    {Γ : Subgroup SL(2, ℤ)} (hN : Γ.strictLevel ≠ 0) :
    Γ.congruenceClosure = Γ ⊔ CongruenceSubgroup.Gamma Γ.strictLevel := by
  have : NeZero Γ.strictLevel := ⟨hN⟩
  refine le_antisymm ?_ (le_sInf fun Δ ⟨hΔ, hΓΔ⟩ ↦ ?_)
  · exact Γ.congruenceClosure_le
      (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ le_sup_right
        (CongruenceSubgroup.Gamma_is_cong_sub Γ.strictLevel))
      le_sup_left
  · exact sup_le hΓΔ
      ((CongruenceSubgroup.Gamma_le_Gamma_of_dvd (strictLevel_dvd_of_le hΓΔ)).trans
        hΔ.Gamma_strictLevel_le)

/-- **Wohlfahrt formula for the congruence closure.** For a finite-index subgroup `Γ ≤ SL(2, ℤ)`,
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ⊔ CongruenceSubgroup.Gamma Γ.strictLevel :=
  congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- Whenever `Γ.strictLevel ≠ 0`, `Γ.congruenceClosure` is a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero
    {Γ : Subgroup SL(2, ℤ)} (hN : Γ.strictLevel ≠ 0) :
    CongruenceSubgroup.IsCongruenceSubgroup Γ.congruenceClosure := by
  have : NeZero Γ.strictLevel := ⟨hN⟩
  rw [congruenceClosure_eq_sup_Gamma_strictLevel_of_strictLevel_ne_zero hN]
  exact CongruenceSubgroup.isCongruenceSubgroup_trans _ _ le_sup_right
    (CongruenceSubgroup.Gamma_is_cong_sub Γ.strictLevel)

/-- For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure` is a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CongruenceSubgroup.IsCongruenceSubgroup Γ.congruenceClosure :=
  isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

instance finiteIndex_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.FiniteIndex :=
  Γ.isCongruenceSubgroup_congruenceClosure.finiteIndex

/-- A finite-index subgroup `Γ ≤ SL(2, ℤ)` equals its congruence closure if and only if it is a
congruence subgroup. -/
theorem congruenceClosure_eq_self_iff {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ↔ CongruenceSubgroup.IsCongruenceSubgroup Γ :=
  ⟨fun h ↦ h ▸ Γ.isCongruenceSubgroup_congruenceClosure,
    CongruenceSubgroup.IsCongruenceSubgroup.congruenceClosure_eq⟩

/-- When `Γ₁` has finite index, `Γ₁.congruenceClosure` is already a congruence subgroup, so any
larger subgroup is congruence-closed and congruence closure distributes over `Γ₁ ⊔ Γ₂`. -/
theorem congruenceClosure_sup (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) [Γ₁.FiniteIndex] :
    (Γ₁ ⊔ Γ₂).congruenceClosure = Γ₁.congruenceClosure ⊔ Γ₂.congruenceClosure := by
  refine le_antisymm ?_
    (sup_le (congruenceClosure_mono le_sup_left) (congruenceClosure_mono le_sup_right))
  exact congruenceClosure_le
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ le_sup_left
      Γ₁.isCongruenceSubgroup_congruenceClosure)
    (sup_le_sup Γ₁.le_congruenceClosure Γ₂.le_congruenceClosure)

/-- For finite-index `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure` is the preimage under reduction modulo
`Γ.strictLevel` of the reduction image of `Γ`. -/
theorem congruenceClosure_eq_comap_map_zmod (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure =
      (Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel)))).comap
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) := by
  rw [congruenceClosure_eq_sup_Gamma_strictLevel]
  exact (comap_map_eq (f := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel)))
    Γ).symm

/-- `Γ` and `Γ.congruenceClosure` have the same image in `SL(2, ZMod Γ.strictLevel)`. -/
@[simp]
theorem map_zmod_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.map
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) := by
  have : NeZero Γ.strictLevel := ⟨Γ.strictLevel_pos.ne'⟩
  rw [congruenceClosure_eq_comap_map_zmod,
    map_comap_eq_self_of_surjective Matrix.SpecialLinearGroup.map_intCast_zmod_surjective]

/-- The index of `Γ.congruenceClosure` in `SL(2, ℤ)` equals the index of the image of `Γ` in
`SL(2, ZMod Γ.strictLevel)`. -/
theorem index_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.index =
      (Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel)))).index := by
  have : NeZero Γ.strictLevel := ⟨Γ.strictLevel_pos.ne'⟩
  rw [congruenceClosure_eq_comap_map_zmod,
    index_comap_of_surjective _ Matrix.SpecialLinearGroup.map_intCast_zmod_surjective]

/-- For finite-index `Γ ≤ SL(2, ℤ)`, `Γ.congruenceClosure = ⊤` if and only if `Γ` surjects onto
`SL(2, ZMod Γ.strictLevel)`. -/
theorem congruenceClosure_eq_top_iff_map_zmod_eq_top {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    Γ.congruenceClosure = ⊤ ↔
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod Γ.strictLevel))) = ⊤ := by
  have : NeZero Γ.strictLevel := ⟨Γ.strictLevel_pos.ne'⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← map_zmod_congruenceClosure, h]
    exact map_top_of_surjective _ Matrix.SpecialLinearGroup.map_intCast_zmod_surjective
  · rw [congruenceClosure_eq_comap_map_zmod, h, comap_top]

/-- If `Γ ≤ SL(2, ℤ)` is not a congruence subgroup while `Γ.withCenter` is a congruence subgroup,
then `Γ.congruenceClosure = Γ.withCenter`. -/
theorem congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup {Γ : Subgroup SL(2, ℤ)}
    (hΓ : ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (hwc : CongruenceSubgroup.IsCongruenceSubgroup Γ.withCenter) :
    Γ.congruenceClosure = Γ.withCenter := by
  have hneg_Γ : (-1 : SL(2, ℤ)) ∉ Γ := fun hneg ↦
    hΓ (by rwa [withCenter_eq_self_iff.mpr
      (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr hneg)] at hwc)
  have : Γ.FiniteIndex :=
    ⟨by rw [Matrix.SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem hneg_Γ]
        exact mul_ne_zero two_ne_zero hwc.finiteIndex.index_ne_zero⟩
  have hle : Γ.congruenceClosure ≤ Γ.withCenter := congruenceClosure_le hwc Γ.le_withCenter
  refine le_antisymm hle ?_
  have hneg_cl : (-1 : SL(2, ℤ)) ∈ Γ.congruenceClosure := by
    by_contra hnot
    have heq : Γ.congruenceClosure ⊓ Γ.withCenter = Γ :=
      inf_withCenter_eq_of_le Γ.le_congruenceClosure fun h ↦ False.elim (hnot h)
    rw [inf_eq_left.mpr hle] at heq
    exact hΓ (heq ▸ Γ.isCongruenceSubgroup_congruenceClosure)
  rw [withCenter_def]
  exact sup_le Γ.le_congruenceClosure
    (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr hneg_cl)

/-- Conjugating a subgroup of `SL(2, ℤ)` commutes with taking its congruence closure. -/
@[simp]
theorem congruenceClosure_conjAct_smul (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ)) :
    (g • Γ).congruenceClosure = g • Γ.congruenceClosure := by
  have haux (h : ConjAct SL(2, ℤ)) (H : Subgroup SL(2, ℤ)) :
      h • H.congruenceClosure ≤ (h • H).congruenceClosure := by
    refine le_sInf fun Δ ⟨hΔ, hHΔ⟩ ↦ ?_
    have hHΔ' : H ≤ h⁻¹ • Δ := by
      simpa [inv_smul_smul] using
        (pointwise_smul_le_pointwise_smul_iff (a := h⁻¹)).mpr hHΔ
    simpa [smul_inv_smul] using
      (pointwise_smul_le_pointwise_smul_iff (a := h)).mpr
        (congruenceClosure_le (CongruenceSubgroup.conj_cong_is_cong h⁻¹ Δ hΔ) hHΔ')
  refine le_antisymm ?_ (haux g Γ)
  simpa [smul_inv_smul] using
    (pointwise_smul_le_pointwise_smul_iff (a := g)).mpr (haux g⁻¹ (g • Γ))

instance normal_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.Normal] :
    Γ.congruenceClosure.Normal := by
  refine ⟨fun x hx g ↦ ?_⟩
  have hfixed : ConjAct.toConjAct g • Γ.congruenceClosure = Γ.congruenceClosure := by
    rw [← congruenceClosure_conjAct_smul, Subgroup.Normal.conjAct ‹Γ.Normal›]
  rw [← hfixed]
  exact ⟨x, hx, rfl⟩

/-- `SL(2, ℤ)` is its own congruence closure. -/
@[simp]
theorem congruenceClosure_top : (⊤ : Subgroup SL(2, ℤ)).congruenceClosure = ⊤ :=
  CongruenceSubgroup.isCongruenceSubgroup_top.congruenceClosure_eq

/-- The congruence closure of the trivial subgroup is trivial, since `⨅ (N ≠ 0), Γ(N) = ⊥`. -/
@[simp]
theorem congruenceClosure_bot : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥ :=
  eq_bot_iff.mpr <| le_trans (le_iInf₂ fun N hN ↦ by
    have : NeZero N := ⟨hN⟩
    exact congruenceClosure_le (CongruenceSubgroup.Gamma_is_cong_sub N) bot_le)
    CongruenceSubgroup.iInf_Gamma_ne_zero.le

end Subgroup

namespace CongruenceSubgroup

/-- Every principal congruence subgroup `Γ(N)` (including `N = 0`) equals its congruence
closure. -/
@[simp]
theorem congruenceClosure_Gamma (N : ℕ) : (Gamma N).congruenceClosure = Gamma N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Gamma_zero_bot]
  · have : NeZero N := ⟨hN⟩
    exact (Gamma_is_cong_sub N).congruenceClosure_eq

/-- Every congruence subgroup `Γ₀(N)` (including `N = 0`) equals its congruence closure. -/
@[simp]
theorem congruenceClosure_Gamma0 (N : ℕ) : (Gamma0 N).congruenceClosure = Gamma0 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ ?_) (Gamma0 0).le_congruenceClosure
    rw [Gamma0_mem]
    have h0 : (γ 1 0 : ℤ) = 0 := by
      refine int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun M hM ↦ ?_
      have : NeZero M := ⟨hM⟩
      have hle : Gamma0 0 ≤ Gamma0 M := Gamma0_le_Gamma0_of_dvd (dvd_zero M)
      exact Gamma0_mem.mp ((Subgroup.congruenceClosure_le (Gamma0_is_congruence M) hle) hγ)
    simp [h0]
  · have : NeZero N := ⟨hN⟩
    exact (Gamma0_is_congruence N).congruenceClosure_eq

/-- Every congruence subgroup `Γ₁(N)` (including `N = 0`) equals its congruence closure. -/
@[simp]
theorem congruenceClosure_Gamma1 (N : ℕ) : (Gamma1 N).congruenceClosure = Gamma1 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ ?_) (Gamma1 0).le_congruenceClosure
    have hmem (M : ℕ) (hM : M ≠ 0) : γ ∈ Gamma1 M := by
      have : NeZero M := ⟨hM⟩
      exact (Subgroup.congruenceClosure_le (Gamma1_is_congruence M)
        (Gamma1_le_Gamma1_of_dvd (dvd_zero M))) hγ
    have h00 : γ 0 0 - 1 = 0 :=
      int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun M hM ↦ by
        rw [Int.cast_sub, Int.cast_one, ((Gamma1_mem M γ).mp (hmem M hM)).1, sub_self]
    have h11 : γ 1 1 - 1 = 0 :=
      int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun M hM ↦ by
        rw [Int.cast_sub, Int.cast_one, ((Gamma1_mem M γ).mp (hmem M hM)).2.1, sub_self]
    have h10 : γ 1 0 = 0 :=
      int_eq_zero_of_forall_nat_ne_zero_cast_eq_zero fun M hM ↦
        ((Gamma1_mem M γ).mp (hmem M hM)).2.2
    rw [Gamma1_mem]
    exact ⟨by simp [sub_eq_zero.mp h00], by simp [sub_eq_zero.mp h11], by simp [h10]⟩
  · have : NeZero N := ⟨hN⟩
    exact (Gamma1_is_congruence N).congruenceClosure_eq

end CongruenceSubgroup
