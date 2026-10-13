/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction
import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisDescent

/-!
# The levels of the idele-class formation

Let `K` be a number field with separable closure `Kˢ` and absolute Galois group `G_K`, and let
`U` be an open subgroup of `G_K` with fixed field `E`, a finite subextension of `Kˢ/K` that need not
be Galois over `K`.
This file identifies the level `(C_{Kˢ})^U` of the idele-class formation `globalFormation K` with
the idele class group `C_E = I_E / Eˣ` of `E` (`ideleClassLevelEquiv`):

```text
C_E  ≃  (C_{Kˢ})^U.
```

The map sends the class of an idele `a` of `E` to the class of `a` regarded as an idele of `Kˢ`.

* It is **surjective** by Hilbert 90 for `U`: an idele class fixed by `U` is the class of an idele
  fixed by `U` (`exists_ideleClassMk_eq_of_isClosed`), which is an idele of `E` by Galois descent
  for ideles (`mem_range_ideleCoeffOfIntermediateField_iff`).
* It is **injective** because a principal idele of `Kˢ` that is an idele of `E` comes from a unit
  of `Kˢ` fixed by `U`, that is, from a unit of `E` (`mem_level_unitsFormation_iff`).

The identification is Galois equivariant: an element of `G_K` restricting to an automorphism `e`
of `E` acts on the level as `e` acts on `C_E` (`ideleClassLevelEquiv_units_map_adeleEquiv`), which
for `E` Galois over `K` is the action of `Gal(E/K)` (`ideleClassLevelEquiv_smul`). It is the map
induced on idele classes by the identification `ideleLevelEquiv` of the corresponding level of the
idele formation with `I_E` (`ideleClassHom_ideleLevelEquiv`). For an arbitrary layer `V ◁ U` of
`globalFormation K`, with fixed fields `L ⊇ F`, it identifies the coefficient module of the layer
with `C_L`, on which `U` acts through its restrictions to `L`, and its ground level with `C_F`.

At the ground, `U = G_K` and `E` is the bottom subextension, the image of `K` in `Kˢ`; reading
`C_E` as `C_K` through extension of ideles gives `globalGroundEquiv K : C_K ≃ (C_{Kˢ})^{G_K}`, the
ground level of every layer `V ◁ G_K`, that is, of every finite Galois extension of `K`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv hU`: the level of the idele-class formation at
  an open subgroup with fixed field `E` is the idele class group of `E`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv K`: the ground level of the idele-class formation is
  the idele class group of `K`.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv_mk`: the class of an idele of `E` goes to the
  class of the same idele of `Kˢ`.
* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv_units_map_adeleEquiv`,
  `TauCeti.ClassFieldTheory.ideleClassLevelEquiv_smul`: `ideleClassLevelEquiv` is Galois
  equivariant.
* `TauCeti.ClassFieldTheory.ideleClassHom_ideleLevelEquiv`: it is compatible with
  `ideleLevelEquiv` and the quotient map from ideles to idele classes.
* `TauCeti.ClassFieldTheory.globalGroundEquiv_mk`: the class of an idele of `K` goes to the class
  of its extension to `Kˢ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

section Level

variable {E : IntermediateField K (SeparableClosure K)} [NumberField E]
  {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = E)

/-- The additive map `I_E → (C_{Kˢ})^U`, sending an idele of `E` to its idele class in `Kˢ`. It
lands in the level because `ideleClassHom` preserves levels. -/
private def ideleToClassLevel : Additive (IdeleGroup (𝓞 E) E) →+ (globalFormation K).level U :=
  AddMonoidHom.codRestrict ((ideleClassCoeffEquivGlobalFormation K).toAddMonoidHom.comp
      ((ideleClassMk K).toAddMonoidHom.comp (ideleCoeffOfIntermediateField K E)))
    _ fun a ↦ by
      have := Formation.map_mem_level (ideleClassHom K) (ideleLevelEquiv hU a).2
      rwa [ideleLevelEquiv_apply_coe, ideleClassHom_hom_apply] at this

private theorem coe_ideleToClassLevel (a : Additive (IdeleGroup (𝓞 E) E)) :
    (ideleToClassLevel hU a : (globalFormation K).toRep.V) =
      ideleClassCoeffEquivGlobalFormation K
        (ideleClassMk K (ideleCoeffOfIntermediateField K E a)) :=
  (rfl)

include hU in
/-- An idele of `E` whose class in `Kˢ` vanishes is principal in `E`: it is the principal idele
of a unit of `Kˢ` fixed by the subgroup fixing `E`, hence of a unit of `E`. -/
private theorem mem_principalSubgroup_of_ideleClassMk_eq_zero {a : IdeleGroup (𝓞 E) E}
    (ha : ideleClassMk K (ideleCoeffOfIntermediateField K E (.ofMul a)) = 0) :
    a ∈ IdeleGroup.principalSubgroup (𝓞 E) E := by
  obtain ⟨y, hy⟩ := ideleClassMk_eq_zero_iff.1 ha
  -- The unit `y` is fixed by `U`, so it lies in the fixed field `E` of `U`.
  have hyU : unitsCoeffEquivUnitsFormation K y ∈ (unitsFormation K).level U := by
    refine (unitsFormation K).mem_level.2 fun u hu ↦ ?_
    rw [← unitsCoeffEquivUnitsFormation_smul]
    refine congrArg _ (principalIdele_injective ?_)
    rw [map_smul, hy, smul_ideleCoeffOfIntermediateField_of_mem_fixingSubgroup
      (toSubgroup_eq_fixingSubgroup_of_fixedField_eq hU ▸ hu)]
  rw [mem_level_unitsFormation_iff, hU] at hyU
  set e : E := ⟨_, hyU⟩
  have he : e ≠ 0 := fun h ↦ y.toMul.ne_zero (congrArg Subtype.val h)
  refine ⟨Units.mk0 e he, Additive.ofMul.injective (ideleCoeffOfIntermediateField_injective ?_)⟩
  rw [← principalIdele_ofMul_map_algebraMap, ← hy]
  exact congrArg _ (Additive.toMul.injective (Units.ext rfl))

include hU in
private theorem ideleToClassLevel_eq_zero_iff {a : IdeleGroup (𝓞 E) E} :
    ideleToClassLevel hU (.ofMul a) = 0 ↔ a ∈ IdeleGroup.principalSubgroup (𝓞 E) E := by
  rw [← ZeroMemClass.coe_eq_zero, coe_ideleToClassLevel, AddEquiv.map_eq_zero_iff]
  refine ⟨mem_principalSubgroup_of_ideleClassMk_eq_zero hU, ?_⟩
  rintro ⟨u, rfl⟩
  rw [ideleClassMk_eq_zero_iff, ← principalIdele_ofMul_map_algebraMap]
  exact ⟨_, rfl⟩

private theorem ker_ideleToClassLevel :
    (AddMonoidHom.toMultiplicativeRight (ideleToClassLevel hU)).ker =
      IdeleGroup.principalSubgroup (𝓞 E) E := by
  ext a
  exact MonoidHom.mem_ker.trans (ofAdd_eq_one.trans (ideleToClassLevel_eq_zero_iff hU))

private theorem surjective_ideleToClassLevel : Function.Surjective (ideleToClassLevel hU) := by
  rintro ⟨z, hz⟩
  obtain ⟨c, rfl⟩ := (ideleClassCoeffEquivGlobalFormation K).surjective z
  obtain ⟨x, hx, rfl⟩ := exists_ideleClassMk_eq_of_isClosed U.toSubgroup U.isClosed (c := c)
    fun u hu ↦ (ideleClassCoeffEquivGlobalFormation K).injective <| by
      rw [ideleClassCoeffEquivGlobalFormation_smul]
      exact (globalFormation K).mem_level.1 hz u hu
  obtain ⟨a, rfl⟩ := (mem_level_ideleFormation_iff hU).1 <|
    (ideleFormation K).mem_level.2 fun u hu ↦ by rw [← ideleCoeffEquivIdeleFormation_smul, hx u hu]
  exact ⟨a, rfl⟩

/-- **The level of the idele-class formation is the idele class group of the fixed field**: if
the fixed field of the open subgroup `U` is the finite subextension `E`, then sending the class of
an idele of `E` to its class as an idele of `Kˢ` identifies the idele class group
`C_E = I_E / Eˣ` with the level `(C_{Kˢ})^U` of `globalFormation K`. Applied to the open normal
subgroup fixing a finite Galois extension `L/K`, it identifies the top level of the layer of `L`
with `C_L`; applied to the two subgroups of an arbitrary layer `V ◁ U`, it identifies its
coefficient module and its ground level with the idele class groups of their fixed fields. -/
def ideleClassLevelEquiv : Additive (IdeleClassGroup (𝓞 E) E) ≃+ (globalFormation K).level U :=
  MulEquiv.toAdditiveLeft <|
    (QuotientGroup.quotientMulEquivOfEq (ker_ideleToClassLevel hU).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_ideleToClassLevel hU))

/-- `ideleClassLevelEquiv hU` sends the class of an idele of `E` to the class of the same idele
of `Kˢ`. -/
@[simp]
theorem ideleClassLevelEquiv_mk (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleClassLevelEquiv hU (.ofMul (a : IdeleClassGroup (𝓞 E) E)) :
        (globalFormation K).level U) : (globalFormation K).toRep.V)) =
      ideleClassCoeffEquivGlobalFormation K
        (ideleClassMk K (ideleCoeffOfIntermediateField K E (.ofMul a))) :=
  (rfl)

/-- **`ideleClassLevelEquiv` is Galois equivariant**: if `g ∈ G_K` restricts on `E` to the
automorphism `e` of `E`, then `g` acts on the level as `e` acts on the idele classes of `E`. -/
theorem ideleClassLevelEquiv_units_map_adeleEquiv (g : AbsoluteGaloisGroup K) (e : E ≃+* E)
    (he : ∀ x : E, ((e x : E) : SeparableClosure K) = g x) (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleClassLevelEquiv hU (.ofMul
        ((Units.map (GlobalNumberFields.adeleEquiv E E e).toMonoidHom a :
          IdeleGroup (𝓞 E) E) : IdeleClassGroup (𝓞 E) E)) :
          (globalFormation K).level U) : (globalFormation K).toRep.V)) =
      (globalFormation K).toRep.ρ g
        (ideleClassLevelEquiv hU (.ofMul (a : IdeleClassGroup (𝓞 E) E))) := by
  rw [ideleClassLevelEquiv_mk, ideleClassLevelEquiv_mk,
    ← smul_ideleCoeffOfIntermediateField g e he, map_smul,
    ideleClassCoeffEquivGlobalFormation_smul]

/-- **`ideleClassLevelEquiv` is Galois equivariant**: if `E` is normal over `K`, then `g ∈ G_K`
acts on the level as its restriction to `Gal(E/K)` acts on the idele classes of `E`. -/
theorem ideleClassLevelEquiv_smul [Normal K E] (g : AbsoluteGaloisGroup K)
    (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleClassLevelEquiv hU (.ofMul
        ((Units.map (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E)) a :
          IdeleGroup (𝓞 E) E) : IdeleClassGroup (𝓞 E) E)) :
          (globalFormation K).level U) : (globalFormation K).toRep.V)) =
      (globalFormation K).toRep.ρ g
        (ideleClassLevelEquiv hU (.ofMul (a : IdeleClassGroup (𝓞 E) E))) := by
  rw [ideleClassLevelEquiv_mk, ideleClassLevelEquiv_mk,
    ← smul_ideleCoeffOfIntermediateField_of_normal, map_smul,
    ideleClassCoeffEquivGlobalFormation_smul]

/-- **`ideleClassLevelEquiv` is induced by `ideleLevelEquiv`**: the quotient map from ideles to
idele classes sends the idele of `Kˢ` attached to an idele `a` of `E` to the class of `a`. -/
theorem ideleClassHom_ideleLevelEquiv (a : IdeleGroup (𝓞 E) E) :
    (ideleClassHom K).hom (ideleLevelEquiv hU (.ofMul a)) =
      ideleClassLevelEquiv hU (.ofMul (a : IdeleClassGroup (𝓞 E) E)) := by
  rw [ideleLevelEquiv_apply_coe, ideleClassHom_hom_apply, ideleClassLevelEquiv_mk]

end Level

/-! ### The ground level -/

section Ground

variable (K)

/-- **The ground level of the idele-class formation is the idele class group of `K`**: extension
of ideles from `K` to `Kˢ` identifies `C_K` with the level `(C_{Kˢ})^{G_K}` of `globalFormation K`.
It is `ideleClassLevelEquiv` at the bottom subextension, read on `C_K` through the identification
of `K` with its image in `Kˢ`. -/
def globalGroundEquiv :
    Additive (IdeleClassGroup (𝓞 K) K) ≃+ (globalFormation K).level ⊤ :=
  (MulEquiv.ofBijective _ (GlobalNumberFields.ideleClassExtension_bijective K
      ((⊥ : Ω) : IntermediateField K (SeparableClosure K))
      fun x ↦ (mem_bot.1 x.2).imp fun _ hc ↦ Subtype.ext hc)).toAdditive.trans
    (ideleClassLevelEquiv (E := ((⊥ : Ω) : IntermediateField K (SeparableClosure K)))
      (TauCeti.fixedField_toSubgroup_top K))

/-- `globalGroundEquiv K` sends the class of an idele of `K` to the class of its extension to
`Kˢ`. -/
@[simp]
theorem globalGroundEquiv_mk (a : IdeleGroup (𝓞 K) K) :
    (dsimp% only ((globalGroundEquiv K (.ofMul (a : IdeleClassGroup (𝓞 K) K)) :
        (globalFormation K).level ⊤) : (globalFormation K).toRep.V)) =
      ideleClassCoeffEquivGlobalFormation K (ideleClassMk K (ideleCoeffOf K ⊥
        (.ofMul (GlobalNumberFields.ideleExtension K
          ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) a)))) := by
  simp only [globalGroundEquiv, AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, MulEquiv.ofBijective_apply, GlobalNumberFields.ideleClassExtension_mk,
    ideleClassLevelEquiv_mk, ideleCoeffOfIntermediateField_coe]

end Ground

end TauCeti.ClassFieldTheory
