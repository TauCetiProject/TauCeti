/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# Units of the profinite integers

An element of the profinite integers `Additive zHat` is a unit exactly when all of its finite
reductions are units, equivalently when all of its `ℓ`-adic components are units. The product
decomposition of the profinite integers therefore restricts to a topological group isomorphism
between their unit group and the product of the groups `ℤ_[ℓ]ˣ`.

A compatible family of characters `G →* (ZMod n)ˣ` consequently assembles uniquely into a
character `G →* (Additive zHat)ˣ`. The assembled character is continuous whenever all of its
finite-level characters are continuous.

## Main definitions

* `TauCeti.zHat.unitsEquivPiPadicInt`: the topological group isomorphism
  `(Additive zHat)ˣ ≃ₜ* ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ`.
* `TauCeti.zHat.unitsLift`: the character into the profinite units assembled from compatible
  characters at every finite level.

## Main results

* `TauCeti.zHat.isUnit_iff`, `TauCeti.zHat.isUnit_iff_component`: the finite-level and
  `ℓ`-adic unit criteria.
* `TauCeti.zHat.map_toZMod_unitsLift`, `TauCeti.zHat.unitsLift_unique`: the characterizing
  property of the assembled character.
* `TauCeti.zHat.continuous_unitsLift`: continuity is detected at the finite levels.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti

namespace zHat

universe u v

/-- A profinite integer is a unit exactly when each of its `ℓ`-adic components is a unit. -/
theorem isUnit_iff_component (a : Additive zHat.{u}) :
    IsUnit a ↔ ∀ (ℓ : ℕ) (_ : Fact ℓ.Prime), IsUnit (component ℓ a) := by
  constructor
  · exact fun ha ℓ _ ↦ ha.map (component ℓ)
  · intro h
    have ha : IsUnit (ringEquivPiPadicInt.{u} a) :=
      Pi.isUnit_iff.mpr fun ℓ ↦ by
        simpa only [ringEquivPiPadicInt_apply] using h ℓ ⟨ℓ.2⟩
    simpa using ha.map ringEquivPiPadicInt.{u}.symm.toRingHom

/-- A profinite integer is a unit exactly when its reduction modulo every positive integer is a
unit. -/
theorem isUnit_iff (a : Additive zHat.{u}) :
    IsUnit a ↔ ∀ n : ℕ+, IsUnit (toZMod n a) := by
  refine ⟨fun ha n ↦ ha.map (toZMod n), fun h ↦ (isUnit_iff_component a).2 fun ℓ hℓ ↦ ?_⟩
  by_contra hunit
  have hdvd : (ℓ : ℤ_[ℓ]) ∣ component ℓ a :=
    PadicInt.norm_lt_one_iff_dvd _ |>.mp (PadicInt.not_isUnit_iff.mp hunit)
  have hz : PadicInt.toZModPow 1 (component ℓ a) = 0 :=
    (PadicInt.toZModPow_eq_zero_iff_dvd 1 _).2 (by simpa using hdvd)
  have hlevel : IsUnit (PadicInt.toZModPow 1 (component ℓ a)) := by
    rw [toZModPow_component]
    exact h _
  exact @not_isUnit_zero (ZMod (ℓ ^ 1)) _
    (ZMod.nontrivial_iff.mpr (by simpa using hℓ.out.ne_one)) (hz ▸ hlevel)

/-- **The unit-group decomposition of the profinite integers.** The product decomposition
`Additive zHat ≃+* ∀ ℓ, ℤ_[ℓ]` restricts to an isomorphism of topological groups on units. -/
noncomputable def unitsEquivPiPadicInt :
    (Additive zHat.{u})ˣ ≃ₜ* ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ :=
  let e : Additive zHat.{u} ≃ₜ* (∀ ℓ : Nat.Primes, ℤ_[ℓ]) :=
    { toMulEquiv := ringEquivPiPadicInt.toMulEquiv
      continuous_toFun := continuous_ringEquivPiPadicInt
      continuous_invFun := continuous_ringEquivPiPadicInt_symm }
  (Units.mapContinuousMulEquiv e).trans ContinuousMulEquiv.piUnits

/-- The `ℓ`-adic coordinate of the unit-group decomposition is induced by `zHat.component ℓ`. -/
@[simp]
theorem unitsEquivPiPadicInt_apply (a : (Additive zHat.{u})ˣ) (ℓ : Nat.Primes) :
    unitsEquivPiPadicInt a ℓ = Units.map (component ℓ).toMonoidHom a := by
  apply Units.ext
  -- Unfold the two standard unit equivalences to expose their common underlying ring map.
  change ringEquivPiPadicInt (a : Additive zHat.{u}) ℓ = component ℓ a
  exact ringEquivPiPadicInt_apply (a : Additive zHat.{u}) ℓ

section UnitsLift

variable {G : Type v} [Group G]
variable (χ : ∀ n : ℕ+, G →* (ZMod n)ˣ)
variable (hχ : ∀ (m n : ℕ+) (h : (n : ℕ) ∣ m) (g : G),
  Units.map (ZMod.castHom h (ZMod n)).toMonoidHom (χ m g) = χ n g)

include hχ

private theorem unitsCoe_compatible (g : G) (m n : ℕ+) (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (χ n g : ZMod n) = (χ m g : ZMod m) := by
  exact congrArg Units.val (hχ n m h g)

private noncomputable def unitsLiftValue (g : G) : Additive zHat.{u} :=
  (existsUnique_forall_toZMod_eq (fun n ↦ (χ n g : ZMod n))
    (unitsCoe_compatible χ hχ g)).exists.choose

private theorem toZMod_unitsLiftValue (g : G) (n : ℕ+) :
    toZMod n (unitsLiftValue χ hχ g) = (χ n g : ZMod n) :=
  (existsUnique_forall_toZMod_eq (fun n ↦ (χ n g : ZMod n))
    (unitsCoe_compatible χ hχ g)).exists.choose_spec n

private theorem isUnit_unitsLiftValue (g : G) : IsUnit (unitsLiftValue χ hχ g) :=
  (isUnit_iff _).2 fun n ↦ (toZMod_unitsLiftValue χ hχ g n).symm ▸ (χ n g).isUnit

private noncomputable def unitsLiftUnit (g : G) : (Additive zHat.{u})ˣ :=
  (isUnit_unitsLiftValue χ hχ g).unit

private theorem coe_unitsLiftUnit (g : G) :
    (unitsLiftUnit χ hχ g : Additive zHat.{u}) = unitsLiftValue χ hχ g :=
  (isUnit_unitsLiftValue χ hχ g).unit_spec

/-- **Assembly of compatible finite-level characters.** A family of characters
`χ n : G →* (ZMod n)ˣ` compatible with reduction along divisibility assembles into a character
`G →* (Additive zHat)ˣ`, characterized by `zHat.map_toZMod_unitsLift`. -/
noncomputable def unitsLift : G →* (Additive zHat.{u})ˣ where
  toFun := unitsLiftUnit χ hχ
  map_one' := by
    apply Units.ext
    apply ext_of_toZMod
    intro n
    calc
      toZMod n (unitsLiftUnit χ hχ 1 : Additive zHat.{u}) = (χ n 1 : ZMod n) := by
        rw [coe_unitsLiftUnit, toZMod_unitsLiftValue]
      _ = 1 := congrArg Units.val (map_one (χ n))
      _ = toZMod n 1 := (map_one (toZMod n)).symm
  map_mul' g g' := by
    apply Units.ext
    apply ext_of_toZMod
    intro n
    calc
      toZMod n (unitsLiftUnit χ hχ (g * g') : Additive zHat.{u}) =
          (χ n (g * g') : ZMod n) := by
        rw [coe_unitsLiftUnit, toZMod_unitsLiftValue]
      _ = (χ n g : ZMod n) * (χ n g' : ZMod n) :=
        congrArg Units.val (map_mul (χ n) g g')
      _ = toZMod n ((unitsLiftUnit χ hχ g : Additive zHat.{u}) *
          (unitsLiftUnit χ hχ g' : Additive zHat.{u})) := by
        rw [map_mul, coe_unitsLiftUnit, coe_unitsLiftUnit, toZMod_unitsLiftValue,
          toZMod_unitsLiftValue]

private theorem coe_unitsLift (g : G) :
    (unitsLift χ hχ g : Additive zHat.{u}) = unitsLiftValue χ hχ g :=
  coe_unitsLiftUnit χ hχ g

/-- The reduction modulo `n` of the assembled character is its prescribed level-`n` character. -/
@[simp]
theorem map_toZMod_unitsLift (n : ℕ+) (g : G) :
    Units.map (toZMod.{u} n) (unitsLift.{u, v} χ hχ g) = χ n g := by
  apply Units.ext
  -- `Units.map` exposes the monoid-hom coercion of `toZMod`; its value is the ring-hom value.
  rw [Units.coe_map]
  change toZMod n (unitsLift.{u, v} χ hχ g : Additive zHat.{u}) = (χ n g : ZMod n)
  rw [coe_unitsLift, toZMod_unitsLiftValue]

/-- The compatible finite-level reductions uniquely determine the assembled character. -/
theorem unitsLift_unique (ψ : G →* (Additive zHat.{u})ˣ)
    (hψ : ∀ (n : ℕ+) (g : G), Units.map (toZMod.{u} n) (ψ g) = χ n g) :
    ψ = unitsLift.{u, v} χ hχ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply ext_of_toZMod
  intro n
  have hn := congrArg Units.val
    ((hψ n g).trans (map_toZMod_unitsLift χ hχ n g).symm)
  -- The unit maps in `hn` use the monoid-hom coercion of `toZMod`.
  simp only [Units.coe_map] at hn
  exact hn

/-- The assembled character is continuous whenever all of its finite-level characters are
continuous. -/
theorem continuous_unitsLift [TopologicalSpace G] [IsTopologicalGroup G]
    (hcont : ∀ n : ℕ+, Continuous (χ n)) : Continuous (unitsLift.{u, v} χ hχ) := by
  apply Continuous.of_coeHom_comp
  apply continuous_iff_forall_continuous_toZMod.mpr
  intro n
  exact (Units.continuous_val.comp (hcont n)).congr fun g ↦
    congrArg Units.val (map_toZMod_unitsLift χ hχ n g).symm

end UnitsLift

end zHat

end TauCeti
