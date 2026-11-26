/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import TauCeti.NumberTheory.NumberField.Ideal.DegreeOne

/-!
# Primitive Dirichlet and ray class characters of ℚ

The rational ray class dictionary `TauCeti.GlobalNumberFields.ratDirichletEquiv` at `(n)·∞`
identifies a Dirichlet character with a ray class character. Induction on either side preserves
its primitive source, so the dictionary descends to an equivalence of primitive bundles. The
absolute norm of the finite conductor recovers the Dirichlet level, and the infinite part records
parity. The ideal weight at a nonzero ideal is the Dirichlet character at its norm, so the two
Dirichlet series have the same coefficients at positive indices. The continued ray class
L-function is the meromorphic normal form of the Dirichlet L-function.
-/

public section

open scoped NumberField Topology
open Filter NumberField TauCeti.GlobalNumberFields TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- Changing the Dirichlet level before passing to the rational ray class dictionary does not
change the primitive ray class character. -/
private theorem rayClass_of_changeLevel {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (h : d ∣ n) (χ : DirichletCharacter ℂ d) :
    PrimitiveRayClassCharacter.of ((ratDirichletEquiv n hn).symm (χ.changeLevel h)) =
      PrimitiveRayClassCharacter.of ((ratDirichletEquiv d hd).symm χ) := by
  have hmod : ratModulus d hd ∣ ratModulus n hn := ratModulus_dvd_ratModulus_iff.mpr h
  have hind : ((ratDirichletEquiv d hd).symm χ).induced hmod =
      (ratDirichletEquiv n hn).symm (χ.changeLevel h) := by
    apply (ratDirichletEquiv n hn).injective
    simp only [ratDirichletEquiv_induced, MulEquiv.apply_symm_apply]
  rw [← hind, PrimitiveRayClassCharacter.of_induced]

/-- The rational ray class dictionary on primitive bundles. Its inverse presents a ray class
character of conductor `𝔣` at `(n)·∞`, where `n` is the norm of the finite part of `𝔣`. -/
noncomputable def toPrimitiveRayClassCharacter :
    PrimitiveDirichletCharacter ≃ PrimitiveRayClassCharacter ℚ := by
  let forward (ψ : PrimitiveDirichletCharacter) := PrimitiveRayClassCharacter.of
    ((ratDirichletEquiv ψ.level (NeZero.ne (ψ.level : ℕ))).symm ψ.character)
  let backward (η : PrimitiveRayClassCharacter ℚ) :=
    of (ratDirichletEquiv _ _ (η.character.induced (dvd_ratModulus_absNorm η.conductor)))
  have hlevel (ψ : PrimitiveDirichletCharacter) :
      Ideal.absNorm (forward ψ).conductor.finitePart = ψ.level := by
    simp only [forward, PrimitiveRayClassCharacter.conductor_of,
      RayClassCharacter.absNorm_conductor_finitePart, MulEquiv.apply_symm_apply,
      conductor_character]
  have hinj : Function.Injective forward := by
    intro ψ ξ h
    -- The conductor fixes the level, so both ray class presentations are at the same modulus.
    have hn : ψ.level = ξ.level := PNat.eq (by rw [← hlevel ψ, h, hlevel])
    obtain ⟨n, χ, hχ⟩ := ψ
    obtain ⟨m, η, hη⟩ := ξ
    dsimp only at hn
    subst m
    obtain ⟨_, hind⟩ := PrimitiveRayClassCharacter.of_eq_iff.mp h
    rw [PrimitiveRayClassCharacter.induced_character_of] at hind
    obtain rfl := (ratDirichletEquiv n (NeZero.ne (n : ℕ))).symm.injective hind
    rfl
  have hright : Function.RightInverse backward forward := by
    intro η
    let χ := ratDirichletEquiv _ _ (η.character.induced (dvd_ratModulus_absNorm η.conductor))
    have h := rayClass_of_changeLevel (NeZero.ne ((of χ).level : ℕ))
      (NeZero.ne (Ideal.absNorm η.conductor.finitePart)) (level_of_dvd χ) (of χ).character
    rw [changeLevel_character_of] at h
    calc
      forward (backward η) = _ := h.symm
      _ = η := by
        simp only [χ, MulEquiv.symm_apply_apply, PrimitiveRayClassCharacter.of_induced,
          PrimitiveRayClassCharacter.of_character]
  exact ⟨forward, backward, fun ψ ↦ hinj (hright (forward ψ)), hright⟩

/-- The ray class bundle is the primitive source of the character presented at `(n)·∞`. -/
theorem toPrimitiveRayClassCharacter_apply (ψ : PrimitiveDirichletCharacter) :
    toPrimitiveRayClassCharacter ψ = PrimitiveRayClassCharacter.of
      ((ratDirichletEquiv ψ.level (NeZero.ne (ψ.level : ℕ))).symm ψ.character) :=
  (rfl)

/-- Taking primitive sources commutes with the rational dictionary at any nonzero level. -/
@[simp]
theorem toPrimitiveRayClassCharacter_of {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    toPrimitiveRayClassCharacter (of χ) =
      PrimitiveRayClassCharacter.of ((ratDirichletEquiv n (NeZero.ne n)).symm χ) := by
  rw [toPrimitiveRayClassCharacter_apply]
  simpa only [changeLevel_character_of] using
    (rayClass_of_changeLevel (NeZero.ne ((of χ).level : ℕ)) (NeZero.ne n)
      (level_of_dvd χ) (of χ).character).symm

/-- The inverse dictionary takes a primitive ray class character to the primitive bundle of its
Dirichlet presentation at the norm of the finite conductor. -/
theorem toPrimitiveRayClassCharacter_symm_apply (η : PrimitiveRayClassCharacter ℚ) :
    toPrimitiveRayClassCharacter.symm η =
      of (ratDirichletEquiv _ _ (η.character.induced (dvd_ratModulus_absNorm η.conductor))) :=
  (rfl)

/-- The finite conductor is the ideal generated by the Dirichlet level. -/
@[simp]
theorem finitePart_conductor_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter) :
    (toPrimitiveRayClassCharacter ψ).conductor.finitePart = Ideal.span {((ψ.level : ℕ) : 𝓞 ℚ)} := by
  rw [toPrimitiveRayClassCharacter_apply, PrimitiveRayClassCharacter.conductor_of,
    RayClassCharacter.conductor_finitePart_eq_span, MulEquiv.apply_symm_apply, conductor_character]

/-- The Dirichlet level of a primitive ray class character is the norm of its finite conductor. -/
@[simp]
theorem level_toPrimitiveRayClassCharacter_symm (η : PrimitiveRayClassCharacter ℚ) :
    ((toPrimitiveRayClassCharacter.symm η).level : ℕ) = Ideal.absNorm η.conductor.finitePart := by
  have h := finitePart_conductor_toPrimitiveRayClassCharacter (toPrimitiveRayClassCharacter.symm η)
  rw [Equiv.apply_symm_apply] at h
  rw [h, RingOfIntegers.absNorm_span_natCast_of_finrank_eq_one (Module.finrank_self ℚ)]

/-- The real place is omitted from the conductor exactly when the Dirichlet character is even. -/
@[simp]
theorem infinitePart_conductor_toPrimitiveRayClassCharacter_eq_empty_iff
    (ψ : PrimitiveDirichletCharacter) :
    (toPrimitiveRayClassCharacter ψ).conductor.infinitePart = ∅ ↔ ψ.character.Even := by
  rw [toPrimitiveRayClassCharacter_apply, PrimitiveRayClassCharacter.conductor_of,
    RayClassCharacter.conductor_infinitePart_eq_empty_iff_even, MulEquiv.apply_symm_apply]

/-- The trivial Dirichlet bundle gives the trivial ray class bundle. -/
@[simp]
theorem toPrimitiveRayClassCharacter_one : toPrimitiveRayClassCharacter 1 = 1 := by
  rw [← of_one (N := 1), toPrimitiveRayClassCharacter_of, map_one,
    PrimitiveRayClassCharacter.of_one]

/-- The rational dictionary commutes with inversion of primitive bundles. -/
@[simp]
theorem toPrimitiveRayClassCharacter_inv (ψ : PrimitiveDirichletCharacter) :
    toPrimitiveRayClassCharacter ψ⁻¹ = (toPrimitiveRayClassCharacter ψ)⁻¹ := by
  have h := toPrimitiveRayClassCharacter_of ψ.character⁻¹
  rw [of_inv, of_character, map_inv, PrimitiveRayClassCharacter.of_inv] at h
  rw [h, toPrimitiveRayClassCharacter_apply]

/-- At a nonzero ideal, the primitive ray class character associated to `ψ` has weight given by
`ψ` at the ideal norm, with both sides zero at ideals meeting the conductor. -/
@[simp]
theorem toMultiplicativeIdealWeight_toPrimitiveRayClassCharacter_apply
    (ψ : PrimitiveDirichletCharacter) {J : Ideal (𝓞 ℚ)} (hJ : J ≠ ⊥) :
    (toPrimitiveRayClassCharacter ψ).character.toMultiplicativeIdealWeight J =
      ψ.character (Ideal.absNorm J) := by
  obtain ⟨h, hη⟩ := PrimitiveRayClassCharacter.of_eq_iff.mp
    (toPrimitiveRayClassCharacter_apply ψ).symm
  let 𝔫 := ratModulus ψ.level (NeZero.ne (ψ.level : ℕ))
  have hfin : (toPrimitiveRayClassCharacter ψ).conductor.finitePart = 𝔫.finitePart := by
    rw [finitePart_conductor_toPrimitiveRayClassCharacter, ratModulus_finitePart]
  have hcop : 𝔫.IsCoprimeTo J ↔ (Ideal.absNorm J).Coprime ψ.level :=
    isCoprimeTo_ratModulus_iff hJ
  have hprime : J.IsPrimeTo (toPrimitiveRayClassCharacter ψ).conductor.support ↔
      𝔫.IsCoprimeTo J := by
    rw [← Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm,
      Modulus.isCoprimeTo_iff_sup_eq_top, Modulus.isCoprimeTo_iff_sup_eq_top, hfin]
  by_cases hgood : 𝔫.IsCoprimeTo J
  · let I : integralIdealsPrimeTo 𝔫 := ⟨J, Modulus.mem_integralIdealsPrimeTo.mpr hgood⟩
    have hval := onIdeals_ratDirichletEquiv_symm ψ.character I
    rw [← hη, RayClassCharacter.onIdeals_induced] at hval
    rw [RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo _ (hprime.mpr hgood)]
    convert hval using 3
    exact (Subtype.ext (coe_integralIdealsPrimeToInclusion h I)).symm
  · rw [RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ (mt hprime.mp hgood)]
    have hnonunit : ¬ IsUnit (Ideal.absNorm J : ZMod ψ.level) := by
      simpa only [ZMod.isUnit_iff_coprime, ← hcop] using hgood
    exact (ψ.character.map_nonunit hnonunit).symm

/-- The coefficients of the corresponding ray class and Dirichlet series agree at every
positive index. -/
@[simp]
theorem normCoeff_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter)
    {n : ℕ} (hn : n ≠ 0) :
    normCoeff ℚ
      (toPrimitiveRayClassCharacter ψ).character.toUnitaryIdealWeight.toIdealArithmeticFunction n =
        ψ.character n := by
  have hJ : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hn
  rw [UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one
    (Module.finrank_self ℚ), RayClassCharacter.val_toUnitaryIdealWeight,
    toMultiplicativeIdealWeight_toPrimitiveRayClassCharacter_apply ψ hJ,
    RingOfIntegers.absNorm_span_natCast_of_finrank_eq_one (Module.finrank_self ℚ)]

/-- The continued ray class L-function is the meromorphic normal form of the corresponding
Dirichlet L-function. In particular the comparison does not identify their values at a pole. -/
theorem heckeLFunctionC_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter) :
    heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character =
      toMeromorphicNFOn ψ.character.LFunction Set.univ := by
  rw [heckeLFunctionC_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn ψ.character.meromorphic_LFunction
    (fun s hs ↦ ψ.character.analyticAt_LFunction (.inl ?_)) (fun s hs ↦ ?_)
  · rintro rfl
    simp at hs
  · rw [ψ.character.LFunction_eq_LSeries hs]
    exact LSeries_congr (fun {_} hn ↦ (normCoeff_toPrimitiveRayClassCharacter ψ hn).symm) s

/-- The corresponding continued L-functions have the same punctured germ at every point. -/
theorem heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq (ψ : PrimitiveDirichletCharacter)
    (s : ℂ) : heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character =ᶠ[𝓝[≠] s]
      ψ.character.LFunction := by
  rw [heckeLFunctionC_toPrimitiveRayClassCharacter]
  exact ψ.character.meromorphic_LFunction.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (Set.mem_univ s)

/-- The corresponding continued L-functions agree wherever the Dirichlet L-function is analytic. -/
theorem heckeLFunctionC_toPrimitiveRayClassCharacter_apply (ψ : PrimitiveDirichletCharacter)
    {s : ℂ} (hs : s ≠ 1 ∨ ψ.character ≠ 1) :
    heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character s = ψ.character.LFunction s := by
  rw [heckeLFunctionC_toPrimitiveRayClassCharacter]
  exact toMeromorphicNFOn_apply_of_analyticAt ψ.character.meromorphic_LFunction
    (ψ.character.analyticAt_LFunction hs)

end TauCeti.PrimitiveDirichletCharacter
