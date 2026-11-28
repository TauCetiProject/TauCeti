/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Tower
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Quotient
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Range

/-!
# Logarithmic character and torsion of the full cyclotomic tower

The splitting `TauCeti.padicIntUnitsEquivZModUnitsProd` supplies the logarithmic coordinate of
`TauCeti.cyclotomicTowerCharacter`. The kernel of `TauCeti.cyclotomicTowerLogCharacter`
is the finite subgroup of finite-order tower
automorphisms. The sign of the full character at `p = 2` can also be nontrivial on automorphisms
of infinite order.
-/

public section

open Multiplicative

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]
  [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

local notation "C" => cyclotomicTower p K L

/-- The normalized logarithmic coordinate of the full cyclotomic character. -/
noncomputable def cyclotomicTowerLogCharacter : Gal(C/K) →ₜ* Multiplicative ℤ_[p] :=
  (ContinuousMonoidHom.snd _ _).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (padicIntUnitsEquivZModUnitsProd p)).comp
      ⟨cyclotomicTowerCharacter p K L, continuous_cyclotomicTowerCharacter p K L⟩)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
@[simp]
theorem cyclotomicTowerLogCharacter_apply (σ : Gal(C/K)) :
    cyclotomicTowerLogCharacter p K L σ =
      (padicIntUnitsEquivZModUnitsProd p (cyclotomicTowerCharacter p K L σ)).2 :=
  (rfl)

/-- The subgroup of finite-order automorphisms of the full cyclotomic tower. -/
noncomputable def torsionCharSubgroup : Subgroup Gal(C/K) :=
  (CommGroup.torsion ℤ_[p]ˣ).comap (cyclotomicTowerCharacter p K L)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The torsion subgroup is the preimage of torsion in the p-adic units. -/
theorem mem_torsionCharSubgroup_iff (σ : Gal(C/K)) :
    σ ∈ torsionCharSubgroup p K L ↔
      cyclotomicTowerCharacter p K L σ ∈ CommGroup.torsion ℤ_[p]ˣ :=
  Iff.rfl

/-- A torsion automorphism is exactly an automorphism of finite order. -/
theorem mem_torsionCharSubgroup_iff_isOfFinOrder (σ : Gal(C/K)) :
    σ ∈ torsionCharSubgroup p K L ↔ IsOfFinOrder σ :=
  (mem_torsionCharSubgroup_iff p K L σ).trans <|
    (CommGroup.mem_torsion _).trans (cyclotomicTowerCharacter_injective p K L).isOfFinOrder_iff

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The logarithmic coordinate kills exactly the torsion in the full cyclotomic group. -/
@[simp]
theorem ker_cyclotomicTowerLogCharacter :
    (↑(cyclotomicTowerLogCharacter p K L) : Gal(C/K) →* Multiplicative ℤ_[p]).ker =
      torsionCharSubgroup p K L := by
  ext σ
  rw [mem_torsionCharSubgroup_iff, mem_torsion_padicIntUnits_iff]
  rw [MonoidHom.mem_ker]
  exact Iff.of_eq (congrArg (· = 1) (cyclotomicTowerLogCharacter_apply p K L σ))

/-- The torsion in the full cyclotomic group embeds in the finite torsion in `ℤ_pˣ`. -/
instance finite_torsionCharSubgroup : Finite (torsionCharSubgroup p K L) := by
  have hfin : (↑(CommGroup.torsion ℤ_[p]ˣ) : Set ℤ_[p]ˣ).Finite := by
    rw [torsion_padicIntUnits_eq_range_section, MonoidHom.coe_range]
    exact Set.finite_range _
  have hset : (↑(torsionCharSubgroup p K L) : Set Gal(C/K)) =
      cyclotomicTowerCharacter p K L ⁻¹' (↑(CommGroup.torsion ℤ_[p]ˣ) : Set ℤ_[p]ˣ) :=
    Set.ext (mem_torsionCharSubgroup_iff p K L)
  apply Set.finite_coe_iff.mpr
  rw [hset]
  exact hfin.preimage (cyclotomicTowerCharacter_injective p K L).injOn

/-- If the base contains a primitive root of unity of order `p` for odd `p`, or of order
four for `p = 2`, the full cyclotomic group is torsion-free. -/
theorem torsionCharSubgroup_eq_bot_of_isPrimitiveRoot {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ padicUnitsDepth p)) :
    torsionCharSubgroup p K L = ⊥ := by
  have hrange : (cyclotomicTowerCharacter p K L).range ≤ unitsPrincipal p (padicUnitsDepth p) := by
    rw [range_cyclotomicTowerCharacter]
    exact range_localCyclotomicCharacter_le_unitsPrincipal ⟨ζ, hζ⟩
  apply eq_bot_iff.mpr
  intro σ hσ
  let u := cyclotomicTowerCharacter p K L σ
  have hu : u = 1 := by
    by_contra hne
    exact not_isOfFinOrder_of_mem_unitsPrincipal (padicUnitsDepth_pos p)
      two_le_padicUnitsDepth (hrange ⟨σ, rfl⟩) hne
      ((CommGroup.mem_torsion _).mp ((mem_torsionCharSubgroup_iff p K L σ).mp hσ))
  exact Subgroup.mem_bot.mpr ((injective_iff_map_eq_one _).mp
    (cyclotomicTowerCharacter_injective p K L) σ hu)

section Dyadic

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [∀ i, HasEnoughRootsOfUnity L (2 ^ i)]

/-- If the base contains a square root of `-2`, its full dyadic cyclotomic group is
torsion-free. The sign unit `-1` is excluded by the character image modulo eight. -/
theorem torsionCharSubgroup_two_eq_bot_of_sq_eq_neg_two {s : K} (hs : s ^ 2 = -2) :
    torsionCharSubgroup 2 K L = ⊥ := by
  apply eq_bot_iff.mpr
  intro σ hσ
  have hχ := (mem_torsionCharSubgroup_iff 2 K L σ).mp hσ
  rw [torsion_padicIntUnits_two] at hχ
  have hu : cyclotomicTowerCharacter 2 K L σ = 1 := by
    rcases Subgroup.mem_zpowers_neg_one_iff.mp hχ with hu | hu
    · exact hu
    exact (neg_one_notMem_range_localCyclotomicCharacter_of_sq_eq_neg_two hs <| by
      rw [← range_cyclotomicTowerCharacter 2 K L, ← hu]
      exact ⟨σ, rfl⟩).elim
  exact Subgroup.mem_bot.mpr ((injective_iff_map_eq_one _).mp
    (cyclotomicTowerCharacter_injective 2 K L) σ hu)

end Dyadic

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The logarithmic character has open image in `ℤ_p` if the full character has open image. -/
theorem isOpen_range_cyclotomicTowerLogCharacter
    (hopen : IsOpen ((cyclotomicTowerCharacter p K L).range : Set ℤ_[p]ˣ)) :
    IsOpen ((cyclotomicTowerLogCharacter p K L).toMonoidHom.range :
      Set (Multiplicative ℤ_[p])) := by
  rw [MonoidHom.coe_range]
  have hmap : IsOpenMap (Prod.snd ∘ padicIntUnitsEquivZModUnitsProd p) :=
    isOpenMap_snd.comp (padicIntUnitsEquivZModUnitsProd p).toHomeomorph.isOpenMap
  have heq : ⇑(cyclotomicTowerLogCharacter p K L).toMonoidHom =
      (Prod.snd ∘ padicIntUnitsEquivZModUnitsProd p) ∘ cyclotomicTowerCharacter p K L :=
    funext (cyclotomicTowerLogCharacter_apply p K L)
  rw [heq, Set.range_comp, ← MonoidHom.coe_range]
  exact hmap _ hopen

end TauCeti
