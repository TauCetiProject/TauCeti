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
`U` be an open subgroup of `G_K` whose fixed field is a finite Galois subextension `E` of `Kˢ/K`.
This file identifies the level `(C_{Kˢ})^U` of the idele-class formation `globalFormation K` with
the idele class group `C_E = I_E / Eˣ` of `E` (`ideleClassLevelEquiv`):

```text
C_E  ≃  (C_{Kˢ})^U.
```

The map sends the class of an idele `a` of `E` to the class of `a` regarded as an idele of `Kˢ`.

* It is **surjective** by Hilbert 90 for `U`: an idele class fixed by `U` is the class of an idele
  fixed by `U` (`exists_ideleClassMk_eq_of_isClosed`), which is an idele of `E` by Galois descent
  for ideles (`mem_range_ideleCoeffOf_iff`).
* It is **injective** because a principal idele of `Kˢ` that is an idele of `E` comes from a unit
  of `Kˢ` fixed by `U`, that is, from a unit of `E` (`mem_level_unitsFormation_iff`).

The identification is Galois equivariant (`ideleClassLevelEquiv_smul`) and is the map induced on
idele classes by the identification `ideleLevelEquiv` of the corresponding level of the idele
formation with `I_E` (`ideleClassHom_ideleLevelEquiv`). For a layer `V ◁ U` of `globalFormation K`
whose fixed fields `L` and `F` are Galois over `K`, it identifies the coefficient module of the
layer with `C_L` and its ground level with `C_F`.

At the ground, `U = G_K` and `E` is the bottom subextension, the image of `K` in `Kˢ`; reading
`C_E` as `C_K` through extension of ideles gives `globalGroundEquiv K : C_K ≃ (C_{Kˢ})^{G_K}`, the
ground level of every layer `V ◁ G_K`, that is, of every finite Galois extension of `K`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv E hU`: the level of the idele-class formation at
  an open subgroup with fixed field `E` is the idele class group of `E`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv K`: the ground level of the idele-class formation is
  the idele class group of `K`.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv_mk`: the class of an idele of `E` goes to the
  class of the same idele of `Kˢ`.
* `TauCeti.ClassFieldTheory.ideleClassLevelEquiv_smul`: `ideleClassLevelEquiv` is Galois
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

/-- The open subgroup with fixed field `E` is the subgroup of `G_K` fixing `E`. -/
private theorem toSubgroup_eq_fixingSubgroup (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    U.toSubgroup = (E : IntermediateField K (SeparableClosure K)).fixingSubgroup := by
  rw [← hU]
  exact (InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩).symm

/-- The class of an idele of `E`, regarded as an idele of `Kˢ`, lies in the level of the
idele-class formation at an open subgroup with fixed field `E`. -/
private theorem ideleClassMk_ideleCoeffOf_mem_level (E : Ω)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = E)
    (a : IdeleGroup (𝓞 E) E) :
    ideleClassCoeffEquivGlobalFormation K (ideleClassMk K (ideleCoeffOf K E (.ofMul a))) ∈
      (globalFormation K).level U := by
  refine (globalFormation K).mem_level.2 fun u hu ↦ ?_
  rw [← ideleClassCoeffEquivGlobalFormation_smul, ← map_smul,
    smul_ideleCoeffOf_of_mem_fixingSubgroup (toSubgroup_eq_fixingSubgroup E hU ▸ hu)]

/-- The additive map `I_E → (C_{Kˢ})^U`, sending an idele of `E` to its idele class in `Kˢ`. -/
private def ideleToClassLevel (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    Additive (IdeleGroup (𝓞 E) E) →+ (globalFormation K).level U :=
  AddMonoidHom.codRestrict ((ideleClassCoeffEquivGlobalFormation K).toAddMonoidHom.comp
      ((ideleClassMk K).toAddMonoidHom.comp (ideleCoeffOf K E)))
    _ fun a ↦ ideleClassMk_ideleCoeffOf_mem_level E hU a.toMul

private theorem coe_ideleToClassLevel (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (a : Additive (IdeleGroup (𝓞 E) E)) :
    (ideleToClassLevel E hU a : (globalFormation K).toRep.V) =
      ideleClassCoeffEquivGlobalFormation K (ideleClassMk K (ideleCoeffOf K E a)) :=
  (rfl)

/-- An idele of `E` whose class in `Kˢ` vanishes is principal in `E`: it is the principal idele
of a unit of `Kˢ` fixed by the subgroup fixing `E`, hence of a unit of `E`. -/
private theorem mem_principalSubgroup_of_ideleClassMk_eq_zero (E : Ω)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = E)
    {a : IdeleGroup (𝓞 E) E} (ha : ideleClassMk K (ideleCoeffOf K E (.ofMul a)) = 0) :
    a ∈ IdeleGroup.principalSubgroup (𝓞 E) E := by
  obtain ⟨y, hy⟩ := ideleClassMk_eq_zero_iff.1 ha
  -- The unit `y` is fixed by `U`, so it lies in the fixed field `E` of `U`.
  have hyU : unitsCoeffEquivUnitsFormation K y ∈ (unitsFormation K).level U := by
    refine (unitsFormation K).mem_level.2 fun u hu ↦ ?_
    rw [← unitsCoeffEquivUnitsFormation_smul]
    refine congrArg _ (principalIdele_injective ?_)
    rw [map_smul, hy,
      smul_ideleCoeffOf_of_mem_fixingSubgroup (toSubgroup_eq_fixingSubgroup E hU ▸ hu)]
  rw [mem_level_unitsFormation_iff, hU] at hyU
  set e : E := ⟨_, hyU⟩
  have he : e ≠ 0 := fun h ↦ y.toMul.ne_zero (congrArg Subtype.val h)
  refine ⟨Units.mk0 e he, Additive.ofMul.injective (ideleCoeffOf_injective E ?_)⟩
  rw [← principalIdele_ofMul_map_algebraMap, ← hy]
  exact congrArg _ (Additive.toMul.injective (Units.ext rfl))

private theorem ker_ideleToClassLevel (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    (AddMonoidHom.toMultiplicativeRight (ideleToClassLevel E hU)).ker =
      IdeleGroup.principalSubgroup (𝓞 E) E := by
  ext a
  rw [MonoidHom.mem_ker, AddMonoidHom.coe_toMultiplicativeRight, Function.comp_apply,
    Function.comp_apply, ofAdd_eq_one, ← Subtype.coe_inj, coe_ideleToClassLevel,
    ZeroMemClass.coe_zero, AddEquiv.map_eq_zero_iff]
  refine ⟨mem_principalSubgroup_of_ideleClassMk_eq_zero E hU, ?_⟩
  rintro ⟨u, rfl⟩
  rw [ideleClassMk_eq_zero_iff, ← principalIdele_ofMul_map_algebraMap]
  exact ⟨_, rfl⟩

private theorem surjective_ideleToClassLevel (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) : Function.Surjective (ideleToClassLevel E hU) := by
  rintro ⟨z, hz⟩
  obtain ⟨c, rfl⟩ := (ideleClassCoeffEquivGlobalFormation K).surjective z
  obtain ⟨x, hx, rfl⟩ := exists_ideleClassMk_eq_of_isClosed U.toSubgroup U.isClosed (c := c)
    fun u hu ↦ (ideleClassCoeffEquivGlobalFormation K).injective <| by
      rw [ideleClassCoeffEquivGlobalFormation_smul]
      exact (globalFormation K).mem_level.1 hz u hu
  obtain ⟨a, rfl⟩ := mem_range_ideleCoeffOf_iff.2 fun g hg ↦
    hx g (toSubgroup_eq_fixingSubgroup E hU ▸ hg)
  exact ⟨a, rfl⟩

/-- **The level of the idele-class formation is the idele class group of the fixed field**: if
the fixed field of the open subgroup `U` is the finite Galois subextension `E`, then sending the
class of an idele of `E` to its class as an idele of `Kˢ` identifies the idele class group
`C_E = I_E / Eˣ` with the level `(C_{Kˢ})^U` of `globalFormation K`. Applied to the open normal
subgroup fixing a finite Galois extension `L/K`, it identifies the top level of the layer of `L`
with `C_L`. -/
def ideleClassLevelEquiv (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) :
    Additive (IdeleClassGroup (𝓞 E) E) ≃+ (globalFormation K).level U :=
  MulEquiv.toAdditiveLeft <|
    (QuotientGroup.quotientMulEquivOfEq (ker_ideleToClassLevel E hU).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_ideleToClassLevel E hU))

/-- `ideleClassLevelEquiv E hU` sends the class of an idele of `E` to the class of the same idele
of `Kˢ`. -/
@[simp]
theorem ideleClassLevelEquiv_mk (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleClassLevelEquiv E hU (.ofMul (a : IdeleClassGroup (𝓞 E) E)) :
        (globalFormation K).level U) : (globalFormation K).toRep.V)) =
      ideleClassCoeffEquivGlobalFormation K (ideleClassMk K (ideleCoeffOf K E (.ofMul a))) :=
  (rfl)

/-- **`ideleClassLevelEquiv` is Galois equivariant**: `g ∈ G_K` acts on the level as its
restriction to `Gal(E/K)` acts on the idele classes of `E`. -/
theorem ideleClassLevelEquiv_smul (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (g : AbsoluteGaloisGroup K) (a : IdeleGroup (𝓞 E) E) :
    (dsimp% only ((ideleClassLevelEquiv E hU (.ofMul
        ((Units.map (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E)) a :
          IdeleGroup (𝓞 E) E) : IdeleClassGroup (𝓞 E) E)) :
          (globalFormation K).level U) : (globalFormation K).toRep.V)) =
      (globalFormation K).toRep.ρ g
        (ideleClassLevelEquiv E hU (.ofMul (a : IdeleClassGroup (𝓞 E) E))) := by
  rw [ideleClassLevelEquiv_mk, ideleClassLevelEquiv_mk, ← smul_ideleCoeffOf, map_smul,
    ideleClassCoeffEquivGlobalFormation_smul]

/-- **`ideleClassLevelEquiv` is induced by `ideleLevelEquiv`**: the quotient map from ideles to
idele classes sends the idele of `Kˢ` attached to an idele `a` of `E` to the class of `a`. -/
theorem ideleClassHom_ideleLevelEquiv (E : Ω) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = E) (a : IdeleGroup (𝓞 E) E) :
    (ideleClassHom K).hom (ideleLevelEquiv E hU (.ofMul a)) =
      ideleClassLevelEquiv E hU (.ofMul (a : IdeleClassGroup (𝓞 E) E)) := by
  rw [ideleLevelEquiv_apply_coe, ideleClassHom_hom_apply, ideleClassLevelEquiv_mk]

/-! ### The ground level -/

section Ground

variable (K)

/-- The whole of `G_K` has fixed field the bottom subextension `K` of `Kˢ/K`. -/
private theorem fixedField_top :
    fixedField (⊤ : OpenSubgroup (AbsoluteGaloisGroup K)).toSubgroup =
      ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) := by
  rw [OpenSubgroup.toSubgroup_top]
  exact InfiniteGalois.fixedField_bot

/-- Extension of idele classes from `K` to its image `⊥` in `Kˢ` is bijective. -/
private theorem bijective_ideleClassExtension_bot :
    Function.Bijective (GlobalNumberFields.ideleClassExtension K
      ((⊥ : Ω) : IntermediateField K (SeparableClosure K))) := by
  set B := ((⊥ : Ω) : IntermediateField K (SeparableClosure K))
  have hB (x : B) : ∃ c : K, algebraMap K B c = x := by
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 x.2
    exact ⟨c, Subtype.ext hc⟩
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · -- A principal idele of `B` extended from `K` is the extension of a principal idele of `K`.
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [GlobalNumberFields.ideleClassExtension_mk, QuotientGroup.eq_one_iff] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨c, hc⟩ := hB y
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact y.ne_zero (by rw [← hc, map_zero])
    rw [QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 c hc0, GlobalNumberFields.ideleExtension_injective K B ?_⟩
    rw [GlobalNumberFields.ideleExtension_unitEmbedding, ← hy]
    exact congrArg _ (Units.ext hc)
  · -- Every idele of `B` is fixed by the trivial group `Gal(B/K)`, so it descends to `K`.
    induction x using QuotientGroup.induction_on with | H a => ?_
    have hσ (σ : B ≃ₐ[K] B) : σ = 1 := AlgEquiv.ext fun x ↦ by
      obtain ⟨c, rfl⟩ := hB x
      exact σ.commutes c
    obtain ⟨b, hb⟩ := (GlobalNumberFields.mem_range_ideleExtension_iff K B (a := a)).2 fun σ ↦ by
      rw [hσ σ, map_one, RingAut.one_apply]
    exact ⟨b, by rw [GlobalNumberFields.ideleClassExtension_mk, hb]⟩

/-- **The ground level of the idele-class formation is the idele class group of `K`**: extension
of ideles from `K` to `Kˢ` identifies `C_K` with the level `(C_{Kˢ})^{G_K}` of `globalFormation K`.
It is `ideleClassLevelEquiv` at the bottom subextension, read on `C_K` through the identification
of `K` with its image in `Kˢ`. -/
def globalGroundEquiv :
    Additive (IdeleClassGroup (𝓞 K) K) ≃+ (globalFormation K).level ⊤ :=
  (MulEquiv.ofBijective _ (bijective_ideleClassExtension_bot K)).toAdditive.trans
    (ideleClassLevelEquiv ⊥ (fixedField_top K))

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
    ideleClassLevelEquiv_mk]

end Ground

end TauCeti.ClassFieldTheory
