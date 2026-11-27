/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Profinite
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The mod-`p` cyclotomic character of an absolute Galois group

For a characteristic-zero field `K` and a prime `p`, reducing the profinite cyclotomic character
`profiniteCyclotomicCharacter K : G_K →ₜ* (Additive zHat)ˣ` modulo `p` yields the continuous
mod-`p` cyclotomic character `modPLocalCyclotomicCharacter p K : G_K →ₜ* (ZMod p)ˣ`. Its values
agree with reducing `localCyclotomicCharacter p K` modulo `p`
(`coe_modPLocalCyclotomicCharacter_apply`), and pushing `continuousLocalCyclotomicCharacter p K`
along any ring homomorphism `f : ℤ_[p] →+* k` into a topological ring of characteristic `p`
agrees with pushing `modPLocalCyclotomicCharacter p K` along `ZMod.castHom`
(`map_continuousLocalCyclotomicCharacter_eq_cast_modP`).

## Main definitions

* `TauCeti.modPLocalCyclotomicCharacter`: the mod-`p` cyclotomic character `G_K →ₜ* (ZMod p)ˣ`.

## Main results

* `TauCeti.coe_modPLocalCyclotomicCharacter_apply`: `modPLocalCyclotomicCharacter p K σ` is the
  mod-`p` reduction of `localCyclotomicCharacter p K σ`.
* `TauCeti.map_continuousLocalCyclotomicCharacter_eq_cast_modP`: pushing
  `continuousLocalCyclotomicCharacter p K` along `f : ℤ_[p] →+* k` agrees with pushing
  `modPLocalCyclotomicCharacter p K` along `ZMod.castHom`.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharZero K]

/-- **The mod-`p` cyclotomic character** `G_K →ₜ* (ZMod p)ˣ`, defined as the level-`p` reduction
of `profiniteCyclotomicCharacter K`. -/
def modPLocalCyclotomicCharacter : Field.absoluteGaloisGroup K →ₜ* (ZMod p)ˣ :=
  (ContinuousMonoidHom.unitsMap
      ⟨(zHat.toZMod.{0} (⟨p, hp.out.pos⟩ : ℕ+)).toMonoidHom,
        zHat.continuous_toZMod.{0} (⟨p, hp.out.pos⟩ : ℕ+)⟩).comp
    (profiniteCyclotomicCharacter.{_, 0} K)

/-- The value of `modPLocalCyclotomicCharacter p K` in `ZMod p` is the mod-`p` reduction of
`localCyclotomicCharacter p K`. -/
@[simp]
theorem coe_modPLocalCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    (modPLocalCyclotomicCharacter p K σ : ZMod p) =
      PadicInt.toZMod (localCyclotomicCharacter p K σ : ℤ_[p]) := by
  have hlhs : (modPLocalCyclotomicCharacter p K σ : ZMod p) =
      zHat.toZMod.{0} (⟨p, hp.out.pos⟩ : ℕ+)
        (profiniteCyclotomicCharacter.{_, 0} K σ : Additive zHat) := by
    let f : Additive zHat.{0} →ₜ* ZMod p :=
      ⟨(zHat.toZMod.{0} (⟨p, hp.out.pos⟩ : ℕ+)).toMonoidHom,
        zHat.continuous_toZMod.{0} (⟨p, hp.out.pos⟩ : ℕ+)⟩
    change (ContinuousMonoidHom.unitsMap f (profiniteCyclotomicCharacter.{_, 0} K σ) : ZMod p) =
      f (profiniteCyclotomicCharacter.{_, 0} K σ : Additive zHat)
    exact ContinuousMonoidHom.coe_unitsMap_apply f (profiniteCyclotomicCharacter.{_, 0} K σ)
  rw [hlhs, ← PadicInt.cast_toZModPow_eq_toZMod one_ne_zero,
    ← map_component_profiniteCyclotomicCharacter.{_, 0} K p σ, Units.coe_map, MonoidHom.coe_ofClass,
    zHat.toZModPow_component p 1]
  exact (zHat.cast_toZMod (m := ⟨p, hp.out.pos⟩) (n := ⟨p ^ 1, pow_pos hp.out.pos 1⟩)
    (dvd_of_eq (pow_one p).symm) _).symm

/-- Pushing `continuousLocalCyclotomicCharacter p K` along any ring homomorphism `f : ℤ_[p] →+* k`
into a topological ring of characteristic `p` (such as the residue field `𝓀[L]` of a finite
extension `L / ℚ_[p]`) agrees with pushing `modPLocalCyclotomicCharacter p K` along
`ZMod.castHom`. -/
theorem map_continuousLocalCyclotomicCharacter_eq_cast_modP {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] (f : ℤ_[p] →+* k) :
    (ContinuousMonoidHom.unitsMap ⟨f.toMonoidHom, f.continuous_of_padicInt_charP⟩).comp
        (continuousLocalCyclotomicCharacter p K) =
      (ContinuousMonoidHom.unitsMap
          ⟨(ZMod.castHom (dvd_refl p) k).toMonoidHom, continuous_of_discreteTopology⟩).comp
        (modPLocalCyclotomicCharacter p K) := by
  rw [ContinuousMonoidHom.unitsMap_ringHom_comp_eq_castHom f
    (continuousLocalCyclotomicCharacter p K)]
  congr 1
  ext1 σ
  apply Units.ext
  simp [coe_modPLocalCyclotomicCharacter_apply]

end TauCeti
