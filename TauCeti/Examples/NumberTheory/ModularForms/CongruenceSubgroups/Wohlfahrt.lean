/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Closure
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Examples for strict Wohlfahrt's theorem and congruence closures

Concrete congruence and noncongruence subgroups of `SL(2, ℤ)` exercising every branch of
`CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le` and
`Subgroup.congruenceClosure`:

1. **Odd congruence subgroups (`Γ(3)` and `Γ₁(5)`):** `-I ∉ Γ`, positive strict level equal to the
   modulus, `IsCongruenceSubgroup`, and `Γ.congruenceClosure = Γ`.
2. **Strict level twice the signed level (`{γ ∈ Γ(2) | a ≡ 1 (mod 4)}`):** an odd congruence
   subgroup `Γ` with `Γ.withCenter = Γ(2)` of strict level `2`, while `Γ.strictLevel = 4`,
   `Γ(4) ≤ Γ`, and `¬ Γ(2) ≤ Γ`.
3. **An index-`8` even noncongruence subgroup (`indexEightSubgroup`):** `-I ∈ Γ`, index `8`, strict
   level `8`, `¬ IsCongruenceSubgroup Γ` witnessed by `!![25, -64; -16, 41] ∈ Γ(8) \ Γ`, and full
   congruence closure `Γ.congruenceClosure = ⊤` (showing that `Γ.congruenceClosure.strictLevel` can
   strictly divide `Γ.strictLevel`).
4. **Kiming–Schütt–Verrill's index-`24` odd noncongruence lift of `Γ₀(6)` (`ksvSubgroup`):** an
   index-`2` subgroup `Γ ≤ Γ₀(6)` with `-I ∉ Γ`, `Γ.withCenter = Γ₀(6)` (hence `Γ.withCenter` is a
   congruence subgroup of strict level `6`), `Γ.strictLevel = 12`, `¬ IsCongruenceSubgroup Γ`
   witnessed by `!![97, 312; 60, 193] ∈ Γ(12) \ Γ`, and `Γ.congruenceClosure = Γ₀(6)`.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt, and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. (2) 83 (2011), 96–120, §3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti.WohlfahrtExample

/-! ### 1. Standard odd congruence subgroups `Γ(3)` and `Γ₁(5)` -/

/-- `Γ(3)` has strict level `3`, misses `-I`, is a congruence subgroup, and equals its congruence
closure. -/
theorem gamma_three_properties :
    (Gamma 3).strictLevel = 3 ∧ (-1 : SL(2, ℤ)) ∉ Gamma 3 ∧
      IsCongruenceSubgroup (Gamma 3) ∧ (Gamma 3).congruenceClosure = Gamma 3 :=
  ⟨strictLevel_Gamma 3, by rw [neg_one_mem_Gamma_iff]; decide,
    Gamma_is_cong_sub 3, congruenceClosure_Gamma 3⟩

/-- `Γ₁(5)` has strict level `5`, misses `-I`, is a congruence subgroup, and equals its congruence
closure. -/
theorem gamma1_five_properties :
    (Gamma1 5).strictLevel = 5 ∧ (-1 : SL(2, ℤ)) ∉ Gamma1 5 ∧
      IsCongruenceSubgroup (Gamma1 5) ∧ (Gamma1 5).congruenceClosure = Gamma1 5 :=
  ⟨strictLevel_Gamma1 5, by rw [neg_one_mem_Gamma1_iff]; decide,
    Gamma1_is_congruence 5, congruenceClosure_Gamma1 5⟩

/-! ### 2. Strict level `4` versus signed level `2`: `{γ ∈ Γ(2) | a ≡ 1 (mod 4)}` -/

/-- For `A, B ∈ Γ(2)`, the off-diagonal product `A 0 1 * B 1 0` vanishes in `ZMod 4`. -/
private lemma offDiag_mul_eq_zero_mod_four {A B : SL(2, ℤ)}
    (hA : A ∈ Gamma 2) (hB : B ∈ Gamma 2) :
    ((A 0 1 * B 1 0 : ℤ) : ZMod 4) = 0 := by
  obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (Gamma_mem.mp hA).2.1
  obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (Gamma_mem.mp hB).2.2.1
  have hmul : A 0 1 * B 1 0 = 4 * (x * y) := by rw [hx, hy]; ring
  rw [hmul, Int.cast_mul, show ((4 : ℤ) : ZMod 4) = 0 by decide, zero_mul]

/-- The odd congruence subgroup `{γ ∈ Γ(2) | (γ 0 0 : ZMod 4) = 1}`. -/
def gammaTwoModFourSubgroup : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Gamma 2 ∧ (γ 0 0 : ZMod 4) = 1}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {A B} hA hB := by
    refine ⟨mul_mem hA.1 hB.1, ?_⟩
    have h00 : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
      simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h00, Int.cast_add, offDiag_mul_eq_zero_mod_four hA.1 hB.1, add_zero, Int.cast_mul,
      hA.2, hB.2, mul_one]
  inv_mem' {A} hA := by
    refine ⟨inv_mem hA.1, ?_⟩
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [← Matrix.det_fin_two, det_coe]
    have hcast := congrArg (Int.cast : ℤ → ZMod 4) hdet
    rw [Int.cast_sub, offDiag_mul_eq_zero_mod_four hA.1 hA.1, sub_zero, Int.cast_mul, hA.2,
      one_mul, Int.cast_one] at hcast
    have hinv00 : (A⁻¹ : SL(2, ℤ)) 0 0 = A 1 1 := by
      simp [SL2_inv_expl]
    rwa [hinv00]

/-- `-I` does not lie in `gammaTwoModFourSubgroup`. -/
theorem neg_one_notMem_gammaTwoModFourSubgroup : (-1 : SL(2, ℤ)) ∉ gammaTwoModFourSubgroup := by
  intro h
  have h00 : (((-1 : SL(2, ℤ)) 0 0 : ℤ) : ZMod 4) = 1 := h.2
  revert h00
  decide

/-- Adjoining `{±I}` to `gammaTwoModFourSubgroup` recovers `Γ(2)`. -/
theorem withCenter_gammaTwoModFourSubgroup : gammaTwoModFourSubgroup.withCenter = Gamma 2 := by
  refine le_antisymm ?_ fun γ hγ ↦ ?_
  · rw [Subgroup.withCenter_def]
    exact sup_le (fun _ h ↦ h.1)
      (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr
        (by rw [neg_one_mem_Gamma_iff]))
  · rw [Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg]
    have hmod2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (γ 0 0 : ZMod 4) = 1 := by
      rw [ZMod.castHom_apply, ZMod.cast_intCast (by decide : 2 ∣ 4)]
      exact (Gamma_mem.mp hγ).1
    have hcases : (γ 0 0 : ZMod 4) = 1 ∨ -(γ 0 0 : ZMod 4) = 1 :=
      (by decide : ∀ z : ZMod 4, ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) z = 1 →
        z = 1 ∨ -z = 1) (γ 0 0 : ZMod 4) hmod2
    rcases hcases with h1 | hm1
    · exact ⟨γ, ⟨hγ, h1⟩, Or.inl rfl⟩
    · refine ⟨-γ, ⟨?_, ?_⟩, Or.inr (neg_neg γ).symm⟩
      · rw [neg_eq_neg_one_mul]
        exact mul_mem (neg_one_mem_Gamma_iff.mpr dvd_rfl) hγ
      · change ((-(γ 0 0) : ℤ) : ZMod 4) = 1
        rwa [Int.cast_neg]

/-- `Γ(4)` is contained in `gammaTwoModFourSubgroup`. -/
theorem Gamma_four_le_gammaTwoModFourSubgroup : Gamma 4 ≤ gammaTwoModFourSubgroup := by
  intro γ hγ
  refine ⟨Gamma_le_Gamma_of_dvd (by decide : 2 ∣ 4) hγ, (Gamma_mem.mp hγ).1⟩

/-- `gammaTwoModFourSubgroup` is a congruence subgroup. -/
theorem isCongruenceSubgroup_gammaTwoModFourSubgroup :
    IsCongruenceSubgroup gammaTwoModFourSubgroup :=
  ⟨4, by decide, Gamma_four_le_gammaTwoModFourSubgroup⟩

/-- `Γ(2)` is not contained in `gammaTwoModFourSubgroup` since `-I ∈ Γ(2) \ Γ`. -/
theorem not_Gamma_two_le_gammaTwoModFourSubgroup : ¬ Gamma 2 ≤ gammaTwoModFourSubgroup :=
  fun h ↦ neg_one_notMem_gammaTwoModFourSubgroup (h (neg_one_mem_Gamma_iff.mpr dvd_rfl))

/-- `gammaTwoModFourSubgroup` has strict level `4`, twice the strict level `2` of its
projectivization `Γ(2)`. -/
theorem strictLevel_gammaTwoModFourSubgroup :
    gammaTwoModFourSubgroup.strictLevel = 4 ∧
      gammaTwoModFourSubgroup.withCenter.strictLevel = 2 := by
  have hwc : gammaTwoModFourSubgroup.withCenter.strictLevel = 2 := by
    rw [withCenter_gammaTwoModFourSubgroup, strictLevel_Gamma]
  refine ⟨?_, hwc⟩
  rcases gammaTwoModFourSubgroup.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter with h2 | h4
  · rw [hwc] at h2
    exfalso
    apply not_Gamma_two_le_gammaTwoModFourSubgroup
    simpa [h2] using isCongruenceSubgroup_gammaTwoModFourSubgroup.Gamma_strictLevel_le
  · omega

/-! ### Helper for homomorphisms `SL(2, ℤ) →* G` factoring through `PSL(2, ℤ)` -/

/-- Lift a `(3, 2, ∞)` triple in a group `G` to a homomorphism `SL(2, ℤ) →* G` via
`TauCeti.ModularGroup.modularEquiv`. -/
private noncomputable def liftSL2Z {G : Type*} [Group G] (u s t : G)
    (hu : u ^ 3 = 1) (hs : s ^ 2 = 1) (htsu : t * s * u = 1) : SL(2, ℤ) →* G :=
  (TauCeti.TriangleGroup.lift u s t hu hs (pow_zero t) htsu).comp
    (TauCeti.ModularGroup.modularEquiv.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))

private lemma liftSL2Z_S {G : Type*} [Group G] (u s t : G)
    (hu : u ^ 3 = 1) (hs : s ^ 2 = 1) (htsu : t * s * u = 1) :
    liftSL2Z u s t hu hs htsu ModularGroup.S = s := by
  simp [liftSL2Z, ← TauCeti.ModularGroup.modularEquiv_y]

private lemma liftSL2Z_T {G : Type*} [Group G] (u s t : G)
    (hu : u ^ 3 = 1) (hs : s ^ 2 = 1) (htsu : t * s * u = 1) :
    liftSL2Z u s t hu hs htsu ModularGroup.T = t := by
  simp [liftSL2Z, ← TauCeti.ModularGroup.modularEquiv_z]

private lemma liftSL2Z_neg_one {G : Type*} [Group G] (u s t : G)
    (hu : u ^ 3 = 1) (hs : s ^ 2 = 1) (htsu : t * s * u = 1) :
    liftSL2Z u s t hu hs htsu (-1 : SL(2, ℤ)) = 1 := by
  have hmem : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
    Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)
  simp [liftSL2Z, (QuotientGroup.eq_one_iff (-1 : SL(2, ℤ))).mpr hmem]

/-! ### 3. An index-`8` noncongruence subgroup with `congruenceClosure = ⊤` -/

private def permS8 : Equiv.Perm (Fin 8) :=
  ⟨![0, 1, 3, 2, 5, 4, 7, 6], ![0, 1, 3, 2, 5, 4, 7, 6], by decide, by decide⟩

private def permT8 : Equiv.Perm (Fin 8) :=
  ⟨![1, 3, 0, 5, 7, 4, 2, 6], ![2, 0, 6, 1, 5, 3, 7, 4], by decide, by decide⟩

private def permU8 : Equiv.Perm (Fin 8) :=
  ⟨![3, 0, 7, 1, 4, 2, 6, 5], ![1, 3, 5, 0, 4, 7, 6, 2], by decide, by decide⟩

private noncomputable def hom8 : SL(2, ℤ) →* Equiv.Perm (Fin 8) :=
  liftSL2Z permU8 permS8 permT8 (by decide) (by decide) (by decide)

/-- The index-`8` subgroup of `SL(2, ℤ)` stabilizing `0 : Fin 8` under `hom8`. -/
noncomputable def indexEightSubgroup : Subgroup SL(2, ℤ) :=
  (MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8)).comap hom8

private lemma mem_indexEightSubgroup_iff {γ : SL(2, ℤ)} :
    γ ∈ indexEightSubgroup ↔ hom8 γ 0 = 0 :=
  Iff.rfl

/-- `-I` belongs to `indexEightSubgroup`. -/
theorem neg_one_mem_indexEightSubgroup : (-1 : SL(2, ℤ)) ∈ indexEightSubgroup := by
  rw [mem_indexEightSubgroup_iff, hom8, liftSL2Z_neg_one]
  rfl

/-- `indexEightSubgroup` has index `8` in `SL(2, ℤ)`. -/
theorem index_indexEightSubgroup : indexEightSubgroup.index = 8 := by
  let f : SL(2, ℤ) ⧸ indexEightSubgroup → Fin 8 :=
    Quotient.lift (fun g ↦ hom8 g 0) fun a b hab ↦ by
      have hmem : a⁻¹ * b ∈ indexEightSubgroup := QuotientGroup.leftRel_apply.mp hab
      rw [mem_indexEightSubgroup_iff, map_mul, map_inv] at hmem
      simpa using congrArg (hom8 a) hmem.symm
  have hbij : Function.Bijective f := by
    refine ⟨?_, fun k ↦ ?_⟩
    · intro q₁ q₂ hq
      induction q₁ using Quotient.inductionOn with | h a =>
      induction q₂ using Quotient.inductionOn with | h b =>
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
      rw [mem_indexEightSubgroup_iff, map_mul, map_inv]
      change hom8 a 0 = hom8 b 0 at hq
      change (hom8 a)⁻¹ (hom8 b 0) = 0
      rw [← hq]
      exact Equiv.symm_apply_apply (hom8 a) 0
    · obtain ⟨m, hm⟩ : ∃ m : Fin 8, (permT8 ^ m.1) 0 = k :=
        (by decide : ∀ k : Fin 8, ∃ m : Fin 8, (permT8 ^ m.1) 0 = k) k
      refine ⟨⟦ModularGroup.T ^ m.1⟧, ?_⟩
      change hom8 (ModularGroup.T ^ m.1) 0 = k
      rw [map_pow, hom8, liftSL2Z_T]
      exact hm
  rw [Subgroup.index, Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_fin]

instance : indexEightSubgroup.FiniteIndex :=
  ⟨by rw [index_indexEightSubgroup]; decide⟩

/-- `indexEightSubgroup` has strict level `8`. -/
theorem strictLevel_indexEightSubgroup : indexEightSubgroup.strictLevel = 8 := by
  have hdvd8 : indexEightSubgroup.strictLevel ∣ 8 := by
    rw [Subgroup.strictLevel_dvd_iff]
    intro σ
    rw [mem_indexEightSubgroup_iff, map_mul, map_mul, map_pow, map_inv, hom8, liftSL2Z_T]
    have hT8 : permT8 ^ 8 = 1 := by decide
    simp [hT8]
  have hnot4 : ¬ indexEightSubgroup.strictLevel ∣ 4 := by
    rw [Subgroup.strictLevel_dvd_iff]
    intro h
    have h1 := h 1
    rw [one_mul, inv_one, mul_one, mem_indexEightSubgroup_iff, map_pow, hom8, liftSL2Z_T] at h1
    revert h1
    decide
  exact (by decide : ∀ d : ℕ, d ≤ 8 → d ∣ 8 → ¬ d ∣ 4 → d = 8) _
    (Nat.le_of_dvd (by decide) hdvd8) hdvd8 hnot4

private def wordV8 : SL(2, ℤ) :=
  ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ *
    ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S *
    ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.T⁻¹

private def witnessW8 : SL(2, ℤ) := -wordV8

private lemma witnessW8_mem_Gamma_eight : witnessW8 ∈ Gamma 8 := by
  have hmat : (witnessW8 : Matrix (Fin 2) (Fin 2) ℤ) = !![25, -64; -16, 41] := by decide
  rw [Gamma_mem, hmat]
  decide

private lemma witnessW8_notMem_indexEightSubgroup : witnessW8 ∉ indexEightSubgroup := by
  rw [mem_indexEightSubgroup_iff]
  have hval : hom8 witnessW8 = hom8 wordV8 := by
    rw [witnessW8, neg_eq_neg_one_mul, map_mul, hom8, liftSL2Z_neg_one, one_mul]
  rw [hval]
  simp only [wordV8, hom8, map_mul, map_pow, map_inv, liftSL2Z_S, liftSL2Z_T]
  decide

/-- `indexEightSubgroup` is not a congruence subgroup, by strict Wohlfahrt's theorem. -/
theorem not_isCongruenceSubgroup_indexEightSubgroup :
    ¬ IsCongruenceSubgroup indexEightSubgroup := by
  rw [isCongruenceSubgroup_iff_Gamma_strictLevel_le, strictLevel_indexEightSubgroup]
  exact fun h ↦ witnessW8_notMem_indexEightSubgroup (h witnessW8_mem_Gamma_eight)

/-- The congruence closure of `indexEightSubgroup` is all of `SL(2, ℤ)`, so its strict level drops
from `8` to `1`. -/
theorem congruenceClosure_indexEightSubgroup :
    indexEightSubgroup.congruenceClosure = ⊤ ∧
      indexEightSubgroup.congruenceClosure.strictLevel = 1 := by
  suffices htop : indexEightSubgroup.congruenceClosure = ⊤ by
    exact ⟨htop, by rw [htop, Subgroup.strictLevel_top]⟩
  have hcl : indexEightSubgroup.congruenceClosure = indexEightSubgroup ⊔ Gamma 8 := by
    rw [indexEightSubgroup.congruenceClosure_eq_sup_Gamma_strictLevel,
      strictLevel_indexEightSubgroup]
  have hS : ModularGroup.S ∈ indexEightSubgroup.congruenceClosure := by
    refine indexEightSubgroup.le_congruenceClosure ?_
    rw [mem_indexEightSubgroup_iff, hom8, liftSL2Z_S]
    decide
  let u8 : SL(2, ℤ) :=
    ModularGroup.T * (ModularGroup.S * witnessW8 * ModularGroup.S⁻¹)
  have hu8 : u8 ∈ indexEightSubgroup := by
    rw [mem_indexEightSubgroup_iff]
    have hval : hom8 witnessW8 = hom8 wordV8 := by
      rw [witnessW8, neg_eq_neg_one_mul, map_mul, hom8, liftSL2Z_neg_one, one_mul]
    simp only [u8, map_mul, map_inv, hval]
    simp only [wordV8, hom8, map_mul, map_pow, map_inv, liftSL2Z_S, liftSL2Z_T]
    decide
  have hconj8 : ModularGroup.S * witnessW8 * ModularGroup.S⁻¹ ∈ Gamma 8 :=
    (Gamma_normal 8).conj_mem _ witnessW8_mem_Gamma_eight ModularGroup.S
  have hT : ModularGroup.T ∈ indexEightSubgroup.congruenceClosure := by
    have hmul : ModularGroup.T =
        u8 * (ModularGroup.S * witnessW8 * ModularGroup.S⁻¹)⁻¹ := by
      dsimp [u8]
      group
    rw [hmul, hcl]
    exact mul_mem (Subgroup.mem_sup_left hu8) (Subgroup.mem_sup_right (inv_mem hconj8))
  rw [eq_top_iff, ← _root_.SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  rintro γ (rfl | rfl)
  · exact hS
  · exact hT

/-! ### 4. Kiming–Schütt–Verrill's index-`24` odd noncongruence lift of `Γ₀(6)` -/

private def permS12 : Equiv.Perm (Fin 12) :=
  ⟨![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8], ![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8],
    by decide, by decide⟩

private def permT12 : Equiv.Perm (Fin 12) :=
  ⟨![0, 2, 7, 11, 8, 3, 1, 10, 4, 6, 9, 5], ![0, 6, 1, 5, 8, 11, 9, 2, 4, 10, 7, 3],
    by decide, by decide⟩

private def permU12 : Equiv.Perm (Fin 12) :=
  ⟨![1, 2, 0, 7, 11, 8, 3, 6, 10, 4, 5, 9], ![2, 0, 1, 6, 9, 10, 7, 3, 5, 11, 8, 4],
    by decide, by decide⟩

private noncomputable def hom12 : SL(2, ℤ) →* Equiv.Perm (Fin 12) :=
  liftSL2Z permU12 permS12 permT12 (by decide) (by decide) (by decide)

private def reps12 : Fin 12 → ZMod 6 × ZMod 6 :=
  ![(1, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 3), (2, 5), (3, 1), (3, 2)]

private def mulVec6 (M : SL(2, ZMod 6)) (v : ZMod 6 × ZMod 6) : ZMod 6 × ZMod 6 :=
  (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2)

private def projEq6 (u v : ZMod 6 × ZMod 6) : Prop := u = v ∨ u = -v

private instance : DecidableRel projEq6 := fun u v ↦ inferInstanceAs (Decidable (u = v ∨ u = -v))

private lemma projEq6_symm {u v : ZMod 6 × ZMod 6} : projEq6 u v → projEq6 v u := by
  rintro (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (neg_neg _).symm

private lemma projEq6_trans {u v w : ZMod 6 × ZMod 6} :
    projEq6 u v → projEq6 v w → projEq6 u w := by
  rintro (rfl | rfl) (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

private lemma mulVec6_one (v : ZMod 6 × ZMod 6) : mulVec6 1 v = v := by
  ext <;> simp [mulVec6]

private lemma mulVec6_mul (M N : SL(2, ZMod 6)) (v : ZMod 6 × ZMod 6) :
    mulVec6 (M * N) v = mulVec6 M (mulVec6 N v) := by
  ext <;> simp [mulVec6, coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma mulVec6_neg (M : SL(2, ZMod 6)) (v : ZMod 6 × ZMod 6) :
    mulVec6 M (-v) = -mulVec6 M v := by
  ext <;> simp [mulVec6] <;> ring

private lemma mulVec6_projEq6 (M : SL(2, ZMod 6)) {u v : ZMod 6 × ZMod 6} :
    projEq6 u v → projEq6 (mulVec6 M u) (mulVec6 M v) := by
  rintro (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (mulVec6_neg M _)

private lemma reps12_hom12_projEq6 (g : SL(2, ℤ)) :
    ∀ j : Fin 12,
      projEq6 (reps12 (hom12 g j))
        (mulVec6 (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 6)) g) (reps12 j)) := by
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [_root_.SpecialLinearGroup.SL2Z_generators]
    trivial
  refine Subgroup.closure_induction (fun x hx ↦ ?_) (fun j ↦ ?_) (fun x y _ _ hx hy j ↦ ?_)
    (fun x _ hx j ↦ ?_) hg
  · rcases hx with rfl | rfl
    · intro j
      rw [hom12, liftSL2Z_S]
      revert j
      decide
    · intro j
      rw [hom12, liftSL2Z_T]
      revert j
      decide
  · simp [mulVec6_one, projEq6]
  · rw [map_mul, map_mul, mulVec6_mul, Equiv.Perm.mul_apply]
    exact projEq6_trans (hx _) (mulVec6_projEq6 _ (hy j))
  · let M := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 6)) x
    have h := hx ((hom12 x).symm j)
    rw [Equiv.apply_symm_apply] at h
    have hinv := projEq6_symm (mulVec6_projEq6 M⁻¹ h)
    rwa [← mulVec6_mul, inv_mul_cancel, mulVec6_one, ← Equiv.Perm.inv_def, ← map_inv,
      ← map_inv] at hinv

private lemma hom12_zero_of_mem_Gamma0_six {g : SL(2, ℤ)} (hg : g ∈ Gamma0 6) :
    hom12 g 0 = 0 := by
  have h := reps12_hom12_projEq6 g 0
  have hmul : mulVec6 (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 6)) g) (reps12 0) =
      ((g 0 0 : ZMod 6), 0) := by
    simp [reps12, mulVec6, Gamma0_mem.mp hg]
  rw [hmul] at h
  have h2 : (reps12 (hom12 g 0)).2 = 0 := by
    rcases h with h | h
    · exact congrArg Prod.snd h
    · simpa using congrArg Prod.snd h
  exact (by decide : ∀ k : Fin 12, (reps12 k).2 = 0 → k = 0) (hom12 g 0) h2

private def permS24 : Equiv.Perm (Fin 24) :=
  ⟨![3, 2, 1, 0, 12, 13, 18, 19, 20, 21, 14, 15, 4, 5, 10, 11, 22, 23, 6, 7, 8, 9, 16, 17],
    ![3, 2, 1, 0, 12, 13, 18, 19, 20, 21, 14, 15, 4, 5, 10, 11, 22, 23, 6, 7, 8, 9, 16, 17],
    by decide, by decide⟩

private def permT24 : Equiv.Perm (Fin 24) :=
  ⟨![1, 0, 5, 4, 14, 15, 22, 23, 16, 17, 6, 7, 2, 3, 20, 21, 8, 9, 12, 13, 18, 19, 10, 11],
    ![1, 0, 12, 13, 3, 2, 10, 11, 16, 17, 22, 23, 18, 19, 4, 5, 8, 9, 20, 21, 14, 15, 6, 7],
    by decide, by decide⟩

private def permU24 : Equiv.Perm (Fin 24) :=
  ⟨![2, 3, 4, 5, 0, 1, 14, 15, 22, 23, 16, 17, 6, 7, 12, 13, 20, 21, 8, 9, 10, 11, 18, 19],
    ![4, 5, 0, 1, 2, 3, 12, 13, 18, 19, 20, 21, 14, 15, 6, 7, 10, 11, 22, 23, 16, 17, 8, 9],
    by decide, by decide⟩

private noncomputable def hom24 : SL(2, ℤ) →* Equiv.Perm (Fin 24) :=
  liftSL2Z permU24 permS24 permT24 (by decide) (by decide) (by decide)

private def div2Fin24 (x : Fin 24) : Fin 12 := ⟨x.1 / 2, by omega⟩

private lemma div2Fin24_hom24 (g : SL(2, ℤ)) :
    ∀ x : Fin 24, div2Fin24 (hom24 g x) = hom12 g (div2Fin24 x) := by
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [_root_.SpecialLinearGroup.SL2Z_generators]
    trivial
  refine Subgroup.closure_induction (fun x hx ↦ ?_) (fun x ↦ by simp)
    (fun x y _ _ hx hy z ↦ by simp [hx, hy]) (fun x _ hx z ↦ ?_) hg
  · rcases hx with rfl | rfl
    · intro z
      rw [hom24, hom12, liftSL2Z_S, liftSL2Z_S]
      revert z
      decide
    · intro z
      rw [hom24, hom12, liftSL2Z_T, liftSL2Z_T]
      revert z
      decide
  · have h := hx ((hom24 x).symm z)
    rw [Equiv.apply_symm_apply] at h
    rw [map_inv, map_inv, Equiv.Perm.inv_def, Equiv.Perm.inv_def, h, Equiv.symm_apply_apply]

private lemma hom24_zero_eq_zero_or_one {g : SL(2, ℤ)} (hg : g ∈ Gamma0 6) :
    hom24 g 0 = 0 ∨ hom24 g 0 = 1 := by
  have hdiv : div2Fin24 (hom24 g 0) = 0 := by
    rw [div2Fin24_hom24, show div2Fin24 0 = 0 from rfl, hom12_zero_of_mem_Gamma0_six hg]
  exact (by decide : ∀ y : Fin 24, div2Fin24 y = 0 → y = 0 ∨ y = 1) (hom24 g 0) hdiv

private lemma hom24_one_of_mem_Gamma0_six {g : SL(2, ℤ)} (hg : g ∈ Gamma0 6) :
    (hom24 g 0 = 0 → hom24 g 1 = 1) ∧ (hom24 g 0 = 1 → hom24 g 1 = 0) := by
  have hdiv : div2Fin24 (hom24 g 1) = 0 := by
    rw [div2Fin24_hom24, show div2Fin24 1 = 0 from rfl, hom12_zero_of_mem_Gamma0_six hg]
  have h01 : hom24 g 1 = 0 ∨ hom24 g 1 = 1 :=
    (by decide : ∀ y : Fin 24, div2Fin24 y = 0 → y = 0 ∨ y = 1) (hom24 g 1) hdiv
  have hne : hom24 g 1 ≠ hom24 g 0 := fun h ↦
    (by decide : (1 : Fin 24) ≠ 0) ((hom24 g).injective h)
  exact ⟨fun h0 ↦ h01.resolve_left (h0 ▸ hne), fun h1 ↦ h01.resolve_right (h1 ▸ hne)⟩

/-- The permutation sign character on `Γ₀(6)` recording whether `hom24` swaps `{0, 1}`. -/
private noncomputable def fiberSignHom : Gamma0 6 →* (ZMod 6)ˣ where
  toFun g := if hom24 g.1 0 = 0 then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply]
    rcases hom24_zero_eq_zero_or_one b.2 with hb0 | hb1 <;>
      rcases hom24_zero_eq_zero_or_one a.2 with ha0 | ha1
    · simp [hb0, ha0]
    · simp [hb0, ha1, show (1 : Fin 24) ≠ 0 by decide]
    · have ha_one := (hom24_one_of_mem_Gamma0_six a.2).1 ha0
      simp [hb1, ha0, ha_one, show (1 : Fin 24) ≠ 0 by decide]
    · have ha_one := (hom24_one_of_mem_Gamma0_six a.2).2 ha1
      have hsq : (-1 : (ZMod 6)ˣ) * -1 = 1 := by decide
      simp [hb1, ha1, ha_one, show (1 : Fin 24) ≠ 0 by decide, hsq]

/-- Kiming–Schütt–Verrill's odd index-`2` noncongruence subgroup of `Γ₀(6)`. -/
noncomputable def ksvSubgroup : Subgroup SL(2, ℤ) :=
  ((fiberSignHom * (Gamma0Map 6).toHomUnits).ker).map (Gamma0 6).subtype

/-- `ksvSubgroup` is contained in `Γ₀(6)`. -/
theorem ksvSubgroup_le_Gamma0_six : ksvSubgroup ≤ Gamma0 6 := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

private lemma mem_ksvSubgroup_iff {g : SL(2, ℤ)} (hg : g ∈ Gamma0 6) :
    g ∈ ksvSubgroup ↔
      fiberSignHom ⟨g, hg⟩ * (Gamma0Map 6).toHomUnits ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨⟨_, _⟩, hker, rfl⟩
    exact hker
  · intro hker
    exact ⟨⟨g, hg⟩, hker, rfl⟩

private lemma toHomUnits_neg_one_six :
    (Gamma0Map 6).toHomUnits ⟨-1, neg_one_mem_Gamma0⟩ = -1 := by
  ext
  decide

/-- `-I` does not belong to `ksvSubgroup`. -/
theorem neg_one_notMem_ksvSubgroup : (-1 : SL(2, ℤ)) ∉ ksvSubgroup := by
  rw [mem_ksvSubgroup_iff neg_one_mem_Gamma0]
  have hf : fiberSignHom ⟨-1, neg_one_mem_Gamma0⟩ = 1 := by
    simp [fiberSignHom, hom24, liftSL2Z_neg_one]
  rw [hf, toHomUnits_neg_one_six, one_mul]
  decide

/-- Adjoining `{±I}` to `ksvSubgroup` yields the congruence subgroup `Γ₀(6)`. -/
theorem withCenter_ksvSubgroup : ksvSubgroup.withCenter = Gamma0 6 := by
  refine le_antisymm (withCenter_le_Gamma0 ksvSubgroup_le_Gamma0_six) fun g hg ↦ ?_
  rw [Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg]
  let val := fiberSignHom ⟨g, hg⟩ * (Gamma0Map 6).toHomUnits ⟨g, hg⟩
  have hval : val = 1 ∨ val = -1 := (by decide : ∀ u : (ZMod 6)ˣ, u = 1 ∨ u = -1) val
  rcases hval with h1 | hm1
  · exact ⟨g, (mem_ksvSubgroup_iff hg).mpr h1, Or.inl rfl⟩
  · have hneg_mem : -g ∈ Gamma0 6 := by
      rw [neg_eq_neg_one_mul]
      exact mul_mem neg_one_mem_Gamma0 hg
    refine ⟨-g, (mem_ksvSubgroup_iff hneg_mem).mpr ?_, Or.inr (neg_neg g).symm⟩
    have hneg_elem : (⟨-g, hneg_mem⟩ : Gamma0 6) = ⟨-1, neg_one_mem_Gamma0⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      exact neg_eq_neg_one_mul g
    change (fiberSignHom * (Gamma0Map 6).toHomUnits) ⟨-g, hneg_mem⟩ = 1
    rw [hneg_elem, map_mul]
    have hneg1 : (fiberSignHom * (Gamma0Map 6).toHomUnits) ⟨-1, neg_one_mem_Gamma0⟩ = -1 := by
      change fiberSignHom _ * (Gamma0Map 6).toHomUnits _ = -1
      have hf : fiberSignHom ⟨-1, neg_one_mem_Gamma0⟩ = 1 := by
        simp [fiberSignHom, hom24, liftSL2Z_neg_one]
      rw [hf, toHomUnits_neg_one_six, one_mul]
    rw [hneg1]
    change (-1 : (ZMod 6)ˣ) * val = 1
    rw [hm1]
    decide

/-- `ksvSubgroup` has index `24` in `SL(2, ℤ)`. -/
theorem index_ksvSubgroup : ksvSubgroup.index = 24 := by
  have h6 : (Gamma0 6).index = 12 := by
    have hmul : (Gamma0 (2 * 3)).index = (Gamma0 2).index * (Gamma0 3).index :=
      Gamma0_index_mul_of_coprime (by decide)
    rw [show 2 * 3 = 6 by rfl, Gamma0_prime_index 2 Nat.prime_two,
      Gamma0_prime_index 3 Nat.prime_three] at hmul
    exact hmul
  rw [Matrix.SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem
    neg_one_notMem_ksvSubgroup, withCenter_ksvSubgroup, h6]

instance : ksvSubgroup.FiniteIndex :=
  ⟨by rw [index_ksvSubgroup]; decide⟩

/-- `ksvSubgroup` has strict level `12`, twice the strict level `6` of `Γ₀(6)`. -/
theorem strictLevel_ksvSubgroup : ksvSubgroup.strictLevel = 12 := by
  have hwc : ksvSubgroup.withCenter.strictLevel = 6 := by
    rw [withCenter_ksvSubgroup, strictLevel_Gamma0]
  rcases ksvSubgroup.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter with h6 | h12
  · exfalso
    have hmem : ModularGroup.S * ModularGroup.T ^ 6 * ModularGroup.S⁻¹ ∈ ksvSubgroup := by
      have hdvd : ksvSubgroup.strictLevel ∣ 6 := by rw [h6, hwc]
      exact Subgroup.strictLevel_dvd_iff.mp hdvd ModularGroup.S
    let c : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ 6 * ModularGroup.S⁻¹
    have hc_mat : (c : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -6, 1] := by decide
    have hc0 : c ∈ Gamma0 6 := by
      rw [Gamma0_mem, hc_mat]
      decide
    rw [mem_ksvSubgroup_iff hc0] at hmem
    have hf : fiberSignHom ⟨c, hc0⟩ = -1 := by
      change (if hom24 c 0 = 0 then (1 : (ZMod 6)ˣ) else -1) = -1
      have hc24 : hom24 c 0 = 1 := by
        simp only [c, hom24, map_mul, map_pow, map_inv, liftSL2Z_S, liftSL2Z_T]
        decide
      simp [hc24, show (1 : Fin 24) ≠ 0 by decide]
    have hu : (Gamma0Map 6).toHomUnits ⟨c, hc0⟩ = 1 := by
      apply Units.ext
      change ((c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 6) = 1
      rw [hc_mat]
      decide
    rw [hf, hu, mul_one] at hmem
    revert hmem
    decide
  · omega

private def witnessW24 : SL(2, ℤ) :=
  ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T *
    ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T * ModularGroup.S *
    ModularGroup.T⁻¹ ^ 2 * ModularGroup.S * ModularGroup.T⁻¹ ^ 5 * ModularGroup.S *
    ModularGroup.T ^ 3

private lemma witnessW24_mem_Gamma_twelve : witnessW24 ∈ Gamma 12 := by
  have hmat : (witnessW24 : Matrix (Fin 2) (Fin 2) ℤ) = !![97, 312; 60, 193] := by decide
  rw [Gamma_mem, hmat]
  decide

private lemma witnessW24_notMem_ksvSubgroup : witnessW24 ∉ ksvSubgroup := by
  have hw0 : witnessW24 ∈ Gamma0 6 :=
    (Gamma_le_Gamma0 6) (Gamma_le_Gamma_of_dvd (by decide : 6 ∣ 12) witnessW24_mem_Gamma_twelve)
  rw [mem_ksvSubgroup_iff hw0]
  have hf : fiberSignHom ⟨witnessW24, hw0⟩ = -1 := by
    change (if hom24 witnessW24 0 = 0 then (1 : (ZMod 6)ˣ) else -1) = -1
    have hw24 : hom24 witnessW24 0 = 1 := by
      simp only [witnessW24, hom24, map_mul, map_pow, map_inv, liftSL2Z_S, liftSL2Z_T]
      decide
    simp [hw24, show (1 : Fin 24) ≠ 0 by decide]
  have hu : (Gamma0Map 6).toHomUnits ⟨witnessW24, hw0⟩ = 1 := by
    have hmat : (witnessW24 : Matrix (Fin 2) (Fin 2) ℤ) = !![97, 312; 60, 193] := by decide
    apply Units.ext
    change ((witnessW24 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 6) = 1
    rw [hmat]
    decide
  rw [hf, hu, mul_one]
  decide

/-- `ksvSubgroup` is not a congruence subgroup even though `ksvSubgroup.withCenter = Γ₀(6)` is. -/
theorem not_isCongruenceSubgroup_ksvSubgroup : ¬ IsCongruenceSubgroup ksvSubgroup := by
  rw [isCongruenceSubgroup_iff_Gamma_strictLevel_le, strictLevel_ksvSubgroup]
  exact fun h ↦ witnessW24_notMem_ksvSubgroup (h witnessW24_mem_Gamma_twelve)

/-- The congruence closure of `ksvSubgroup` is `Γ₀(6)`. -/
theorem congruenceClosure_ksvSubgroup : ksvSubgroup.congruenceClosure = Gamma0 6 := by
  rw [← withCenter_ksvSubgroup]
  exact ksvSubgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup
    not_isCongruenceSubgroup_ksvSubgroup
    (withCenter_ksvSubgroup ▸ Gamma0_is_congruence 6)

end TauCeti.WohlfahrtExample
