/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType
public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic

/-!
# Splitting characters of a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x` and a CM type `Φ`, which identifies the
completion `E_w` at each infinite place `w` with `ℂ` through the embedding `Φ_w` of `Φ` above `w`
(`TauCeti.CMType.completionEmbedding`). A **splitting character** of `E` for `Φ` is a unitary
character `υ` of the idele class group `𝔸^× / E^×` such that

* conjugation inverts it: `υ(conj x) = υ(x)⁻¹`;
* `υ(x) = ∏_w Φ_w(x_w) / |x_w|` whenever the finite part of the idele `x` is a unit of `Ô`.

Splitting characters split the metaplectic cover over unitary groups: with them the Weil
representation of a unitary group over `E` is a genuine representation. Conjugation acts on the
idele classes as the nontrivial element `complexConj E` of `Gal(E / E⁺)`
(`TauCeti.GlobalNumberFields.ideleClassMulDistribMulAction`).

The two clauses of the second condition are separated here: `υ` is trivial on the ideles with
infinite part `1` and finite part in `Ô^×`
(`TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.apply_ofFiniteIdele`), and its component
at an infinite place `w` is `z ↦ Φ_w(z) / |z|`
(`TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.infiniteComponent_apply`). As `υ` is
trivial on `E^×`, the product `∏_w Φ_w(u) / |Φ_w(u)|` is `1` for every unit `u` of `𝓞_E`
(`TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.prod_embedding_div_norm_eq_one`); for
`E = ℚ(i)` the unit `i` violates this, so `ℚ(i)` has no splitting character.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting υ Φ`: `υ` is a splitting character of
  `E` for the CM type `Φ`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.apply_mul_conj`: `υ(x conj x) = 1`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.apply_ofFiniteIdele`: `υ` is trivial on
  the finite ideles in `Ô^×`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.infiniteComponent_apply`: the component
  of `υ` at an infinite place `w` is `z ↦ Φ_w(z) / |z|`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.prod_embedding_div_norm_eq_one`: the
  product of the phases `Φ_w(u) / |Φ_w(u)|` of a global unit `u` is `1`.

## References

* S. S. Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994).
* M. Harris, S. S. Kudla and W. J. Sweet, *Theta dichotomy for unitary groups*, J. Amer. Math. Soc.
  9 (1996), §1.

## Attribution

The definition follows `New.SplittingChar` in `src/Lib/Weil/Construction/WeilData.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.IsCMField
open scoped NumberField AdeleGaloisAction

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- A **splitting character** of the CM field `E` for the CM type `Φ`: a Hecke character `υ` of
`E` with values of absolute value one, inverted by complex conjugation, and equal to
`∏_w Φ_w(x_w) / |x_w|` at every idele `x` whose finite part is a unit of `Ô`, where `Φ_w` is the
embedding of `E_w` in `ℂ` extending the embedding of `Φ` above the infinite place `w`. -/
structure IsSplitting (υ : HeckeCharacter E) (Φ : CMType E) : Prop where
  /-- `υ` is unitary. -/
  norm_apply (c : IdeleClassGroup (𝓞 E) E) : ‖(υ c : ℂ)‖ = 1
  /-- Complex conjugation inverts `υ`: `υ(conj c) = υ(c)⁻¹`. -/
  apply_conj (c : IdeleClassGroup (𝓞 E) E) : υ (complexConj E • c) = (υ c)⁻¹
  /-- At an idele `x` whose finite part is a unit of `Ô`, `υ(x) = ∏_w Φ_w(x_w) / |x_w|`. -/
  apply_of_mem_integralUnits (x : IdeleGroup (𝓞 E) E)
    (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x ∈ FiniteAdeleRing.integralUnits (𝓞 E) E) :
    (υ x : ℂ) = ∏ w : InfinitePlace E,
      Φ.completionEmbedding w (w.ideleInfiniteCoord x) / ‖(w.ideleInfiniteCoord x : w.Completion)‖

namespace IsSplitting

variable {Φ : CMType E} {υ : HeckeCharacter E}

/-- A splitting character is trivial on the norms `c conj c` of idele classes. -/
theorem apply_mul_conj (hυ : υ.IsSplitting Φ) (c : IdeleClassGroup (𝓞 E) E) :
    υ (c * complexConj E • c) = 1 := by
  rw [map_mul, hυ.apply_conj, mul_inv_cancel]

/-- A splitting character is trivial on the ideles with infinite part `1` and finite part a unit of
`Ô`. -/
theorem apply_ofFiniteIdele (hυ : υ.IsSplitting Φ) {u : (FiniteAdeleRing (𝓞 E) E)ˣ}
    (hu : u ∈ FiniteAdeleRing.integralUnits (𝓞 E) E) :
    υ (IdeleGroup.ofFiniteIdele (𝓞 E) E u) = 1 := by
  refine Units.ext ?_
  rw [hυ.apply_of_mem_integralUnits _ (by rwa [IdeleGroup.toFiniteIdele_ofFiniteIdele])]
  simp

/-- **The component of a splitting character at an infinite place** `w` is `z ↦ Φ_w(z) / |z|`. -/
theorem infiniteComponent_apply (hυ : υ.IsSplitting Φ) (w : InfinitePlace E)
    (z : w.Completionˣ) :
    (υ.infiniteComponent w z : ℂ) = Φ.completionEmbedding w z / ‖(z : w.Completion)‖ := by
  rw [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion,
    MonoidHom.comp_apply, QuotientGroup.coe_mk', hυ.apply_of_mem_integralUnits _
      (by rw [IdeleGroup.toFiniteIdele_ofCompletion]; exact one_mem _)]
  -- the idele concentrated at `w` has components `1` away from `w`
  rw [Finset.prod_eq_single w (fun w' _ hw' ↦ by simp [hw']) (by simp)]
  simp

/-- **The phases of a global unit multiply to one.** For a unit `u` of `𝓞_E`, the principal idele
of `u` has finite part in `Ô^×` and trivial class, so `∏_w Φ_w(u) / |Φ_w(u)| = 1`. -/
theorem prod_embedding_div_norm_eq_one (hυ : υ.IsSplitting Φ) (u : (𝓞 E)ˣ) :
    ∏ w : InfinitePlace E, Φ.embedding w (u : E) / ‖Φ.embedding w (u : E)‖ = 1 := by
  set x := IdeleGroup.unitEmbedding (𝓞 E) E (Units.map (algebraMap (𝓞 E) E : 𝓞 E →* E) u)
  have hx : IdeleGroup.toFiniteIdele (𝓞 E) E x ∈ FiniteAdeleRing.integralUnits (𝓞 E) E := by
    simp [x]
  have h := hυ.apply_of_mem_integralUnits x hx
  rw [show (x : IdeleClassGroup (𝓞 E) E) = 1 from
    (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩] at h
  simpa [x, ← CMType.norm_completionEmbedding Φ] using h.symm

end IsSplitting

end TauCeti.GlobalNumberFields.HeckeCharacter
