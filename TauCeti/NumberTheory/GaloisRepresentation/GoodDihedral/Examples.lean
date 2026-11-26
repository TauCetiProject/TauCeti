/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.GoodDihedral.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Character
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Data.ZMod.Pow
import TauCeti.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Examples of good-dihedral primes

Concrete checks of `MonoidHom.IsGoodDihedralAt` and `MonoidHom.IsLocallyGoodDihedral`.

* For a unit `u` of order `7` in a commutative semiring `K`, the dihedral group `D₇` acts on
  `K²` by sending the rotation `r i` to `diag(uⁱ, u⁻ⁱ)` and the reflection `sr i` to the swap
  composed with it. With inertia the rotation subgroup `TauCeti.dihedralRotations 7`,
  characteristic `p = 2` and conductor `N = 41²`, the prime `41` is good-dihedral, with `t = 7`:
  the character `TauCeti.dihedralRotationChar` sending `r i` to `uⁱ` has exact order `7`,
  `u⁴¹ = u⁻¹`, `7 ∣ 42`, `7 > max(Q(1), 5, 2)`, and `41 ≡ 1` modulo `8` and `2`. Over
  `𝔽₈ = GaloisField 2 3` such a unit exists, so this representation is locally good-dihedral.
  This is an algebraic example; it does not assert a Galois realization.
* `13` is never good-dihedral, since `13 ≢ 1 (mod 8)`.
* For `p = 7`, `q = 241` and `N = 9 · 241²`, the congruences modulo `8`, `2`, `3` and `5` hold
  but `241 ≢ 1 (mod 7)`, so `241` is not good-dihedral: the range of the congruence conditions
  includes `s = p`.
* The trivial representation is good-dihedral at no prime, so it is not locally good-dihedral.
-/

public section

namespace TauCeti.GoodDihedralExamples

open Matrix DihedralGroup AddChar

variable {K : Type*} [CommSemiring K]

section Dihedral

/-- The matrices of `dihedralRep`: `r i ↦ diag(uⁱ, u⁻ⁱ)` and `sr i ↦ (0, u⁻ⁱ; uⁱ, 0)`. -/
private def dihedralMatrix (u : Kˣ) (hu : u ^ 7 = 1) :
    DihedralGroup 7 → Matrix (Fin 2) (Fin 2) K
  | r i => !![(zmodChar 7 hu i : K), 0; 0, (zmodChar 7 hu (-i) : K)]
  | sr i => !![0, (zmodChar 7 hu (-i) : K); (zmodChar 7 hu i : K), 0]

/-- The two-dimensional representation of the dihedral group `D₇` induced from the character
`i ↦ uⁱ` of its rotation subgroup (`AddChar.zmodChar`). Its values are `coe_dihedralRep_r` and
`coe_dihedralRep_sr`. -/
def dihedralRep (u : Kˣ) (hu : u ^ 7 = 1) : DihedralGroup 7 →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := dihedralMatrix u hu
      map_one' := by rw [one_def]; simp [dihedralMatrix, one_fin_two]
      map_mul' := by
        rintro (i | i) (j | j) <;> ext a b <;> fin_cases a <;> fin_cases b <;>
          simp [dihedralMatrix, map_add_eq_mul, sub_eq_add_neg, mul_comm] }

/-- `dihedralRep u hu` sends the rotation `r i` to `diag(uⁱ, u⁻ⁱ)`. -/
theorem coe_dihedralRep_r (u : Kˣ) (hu : u ^ 7 = 1) (i : ZMod 7) :
    (dihedralRep u hu (r i) : Matrix (Fin 2) (Fin 2) K) =
      !![(zmodChar 7 hu i : K), 0; 0, (zmodChar 7 hu (-i) : K)] :=
  (rfl)

/-- `dihedralRep u hu` sends the reflection `sr i` to `(0, u⁻ⁱ; uⁱ, 0)`. -/
theorem coe_dihedralRep_sr (u : Kˣ) (hu : u ^ 7 = 1) (i : ZMod 7) :
    (dihedralRep u hu (sr i) : Matrix (Fin 2) (Fin 2) K) =
      !![0, (zmodChar 7 hu (-i) : K); (zmodChar 7 hu i : K), 0] :=
  (rfl)

/-- For a unit `u` of order `7`, the prime `41` is good-dihedral for the dihedral
representation `dihedralRep`, with inertia the rotation subgroup, characteristic `2` and
conductor `41²`; the witnesses are `t = 7`, `a = 1`, the character
`TauCeti.dihedralRotationChar : r i ↦ uⁱ` and `B = 1`. -/
theorem isGoodDihedralAt_dihedralRep (u : Kˣ) (hu : orderOf u = 7) :
    (dihedralRep u (hu ▸ pow_orderOf_eq_one u)).IsGoodDihedralAt
      (fun _ ↦ (dihedralRotations 7).subtype) 2 (41 ^ 2) 41 := by
  have hu7 : u ^ 7 = 1 := hu ▸ pow_orderOf_eq_one u
  -- `ψ⁴¹ = ψ⁻¹` pointwise, since `41 ≡ -1 (mod 7)`.
  have hpow := pow_val_neg_eq_pow_val_pow (k := 41) hu7 (by decide)
  refine ⟨by norm_num, by norm_num, ⟨7, 1, dihedralRotationChar hu7, by norm_num, by norm_num,
    ?_, one_pos, ?_, 1, fun ⟨x, hx⟩ ↦ ?_⟩, by norm_num, fun s hs hs2 ↦ ?_⟩
  · norm_num
  · -- `dihedralRotationChar` is `zmodChar` composed with the rotation coordinate.
    have hψ : dihedralRotationChar hu7 = MulEquiv.monoidHomCongrLeft
        (dihedralRotationsMulEquiv 7).symm (zmodChar 7 hu7).toMonoidHom :=
      MonoidHom.ext fun x ↦ by simp [zmodChar_apply]
    rw [pow_one, hψ, MulEquiv.orderOf_eq, orderOf_toMonoidHom_zmodChar, hu]
  · obtain ⟨i, rfl⟩ := mem_dihedralRotations_iff.mp hx
    rw [inv_one, one_mul, mul_one, diagonal_fin_two]
    simp only [Subgroup.coe_subtype, coe_dihedralRep_r, dihedralRotationChar_r, zmodChar_apply,
      hpow]
    simp
  · norm_num at hs2
    obtain rfl : s = 2 := le_antisymm hs2 hs.two_le
    norm_num

/-- Over `𝔽₈ = GaloisField 2 3`, some representation of the dihedral group `D₇` is locally
good-dihedral, with inertia the rotation subgroup, characteristic `2` and conductor `41²`. -/
theorem exists_isLocallyGoodDihedral_galoisField :
    ∃ ρ : DihedralGroup 7 →* GL (Fin 2) (GaloisField 2 3),
      ρ.IsLocallyGoodDihedral (fun _ ↦ (dihedralRotations 7).subtype) 2 (41 ^ 2) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 3)ˣ)
  have hu : orderOf u = 7 := by
    rw [hu, Nat.card_units, GaloisField.card 2 3 (by norm_num)]
    norm_num
  exact ⟨_, (isGoodDihedralAt_dihedralRep u hu).isLocallyGoodDihedral⟩

end Dihedral

variable {G : Type*} [Group G] {I : ℕ → Type*} [∀ q, Group (I q)] {ρ : G →* GL (Fin 2) K}
  {ι : ∀ q, I q →* G} {p N : ℕ}

/-- `13` is never a good-dihedral prime, since `13 ≢ 1 (mod 8)`. -/
theorem not_isGoodDihedralAt_thirteen : ¬ ρ.IsGoodDihedralAt ι p N 13 :=
  fun h ↦ absurd h.mod_eight_eq_one (by norm_num)

/-- For `p = 7` and `N = 9 · 241²`, the prime `241` satisfies the congruences modulo `8`, `2`,
`3` and `5` but is not good-dihedral, because `241 ≢ 1 (mod 7)`. -/
theorem not_isGoodDihedralAt_two_hundred_forty_one :
    ¬ ρ.IsGoodDihedralAt ι 7 (9 * 241 ^ 2) 241 :=
  fun h ↦ absurd (h.mod_eq_one (by norm_num)) (by norm_num)

/-- The trivial representation is not locally good-dihedral. -/
theorem not_isLocallyGoodDihedral_one :
    ¬ (1 : G →* GL (Fin 2) K).IsLocallyGoodDihedral ι p N :=
  MonoidHom.not_isLocallyGoodDihedral_of_forall_eq_one fun _ _ ↦ rfl

end TauCeti.GoodDihedralExamples
