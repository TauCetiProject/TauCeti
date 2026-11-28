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
import TauCeti.NumberTheory.LFunctions.Hecke.Rat.Basic
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

/-- Transport an invariant `F` across `changeLevel hMN ψ = χ` when `N = M`. -/
private theorem eq_of_level_eq_of_changeLevel_eq {α : Sort*}
    (F : ∀ {N : ℕ}, [NeZero N] → DirichletCharacter ℂ N → α)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (hNM : N = M)
    {ψ : DirichletCharacter ℂ M} {χ : DirichletCharacter ℂ N}
    (h : DirichletCharacter.changeLevel hMN ψ = χ) :
    F χ = F ψ := by
  subst hNM
  rw [DirichletCharacter.changeLevel_self] at h
  subst h
  rfl

/-- The rational ray class dictionary on primitive bundles. Its inverse presents a ray class
character of conductor `𝔣` at `(n)·∞`, where `n` is the norm of the finite part of `𝔣`. -/
noncomputable def toPrimitiveRayClassCharacter :
    PrimitiveDirichletCharacter ≃ PrimitiveRayClassCharacter ℚ := by
  let forward (ψ : PrimitiveDirichletCharacter) := PrimitiveRayClassCharacter.of
    ((ratDirichletEquiv ψ.level (NeZero.ne (ψ.level : ℕ))).symm ψ.character)
  let backward (η : PrimitiveRayClassCharacter ℚ) :=
    of η.character.toDirichletCharacter
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
    let χ := η.character.toDirichletCharacter
    have h := rayClass_of_changeLevel (NeZero.ne ((of χ).level : ℕ))
      (NeZero.ne (Ideal.absNorm η.conductor.finitePart)) (level_of_dvd χ) (of χ).character
    rw [changeLevel_character_of] at h
    calc
      forward (backward η) = _ := h.symm
      _ = η := by
        simp only [χ, RayClassCharacter.toDirichletCharacter_apply, MulEquiv.symm_apply_apply,
          PrimitiveRayClassCharacter.of_induced, PrimitiveRayClassCharacter.of_character]
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
associated Dirichlet character. -/
theorem toPrimitiveRayClassCharacter_symm_apply (η : PrimitiveRayClassCharacter ℚ) :
    toPrimitiveRayClassCharacter.symm η = of η.character.toDirichletCharacter :=
  (rfl)

/-- The finite conductor is the ideal generated by the Dirichlet level. -/
@[simp]
theorem finitePart_conductor_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter) :
    (toPrimitiveRayClassCharacter ψ).conductor.finitePart = Ideal.span {((ψ.level : ℕ) : 𝓞 ℚ)} := by
  rw [toPrimitiveRayClassCharacter_apply, PrimitiveRayClassCharacter.conductor_of,
    RayClassCharacter.conductor_finitePart_eq_span, MulEquiv.apply_symm_apply, conductor_character]

private theorem absNorm_finitePart_conductor_toPrimitiveRayClassCharacter
    (ψ : PrimitiveDirichletCharacter) :
    Ideal.absNorm (toPrimitiveRayClassCharacter ψ).conductor.finitePart = ψ.level := by
  rw [finitePart_conductor_toPrimitiveRayClassCharacter,
    RingOfIntegers.absNorm_span_natCast_of_finrank_eq_one (Module.finrank_self ℚ)]

/-- The Dirichlet level of a primitive ray class character is the norm of its finite conductor. -/
@[simp]
theorem level_toPrimitiveRayClassCharacter_symm (η : PrimitiveRayClassCharacter ℚ) :
    ((toPrimitiveRayClassCharacter.symm η).level : ℕ) = Ideal.absNorm η.conductor.finitePart := by
  have h := absNorm_finitePart_conductor_toPrimitiveRayClassCharacter
    (toPrimitiveRayClassCharacter.symm η)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

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
  rw [← (toPrimitiveRayClassCharacter ψ).character.toDirichletCharacter_apply_absNorm hJ]
  obtain ⟨hdiv, hchg⟩ := of_eq_iff.mp (toPrimitiveRayClassCharacter.symm_apply_apply ψ)
  exact eq_of_level_eq_of_changeLevel_eq (fun {_ _} η ↦ η (Ideal.absNorm J)) hdiv
    (absNorm_finitePart_conductor_toPrimitiveRayClassCharacter ψ) hchg

/-- The coefficients of the corresponding ray class and Dirichlet series agree at every
positive index. -/
@[simp]
theorem normCoeff_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter)
    {n : ℕ} (hn : n ≠ 0) :
    normCoeff ℚ
      (toPrimitiveRayClassCharacter ψ).character.toUnitaryIdealWeight.toIdealArithmeticFunction n =
        ψ.character n := by
  rw [normCoeff_rayClassCharacter_rat_eq _ hn]
  obtain ⟨hdiv, hchg⟩ := of_eq_iff.mp (toPrimitiveRayClassCharacter.symm_apply_apply ψ)
  exact eq_of_level_eq_of_changeLevel_eq (fun {_ _} η ↦ η n) hdiv
    (absNorm_finitePart_conductor_toPrimitiveRayClassCharacter ψ) hchg

/-- The continued ray class L-function is the meromorphic normal form of the corresponding
Dirichlet L-function. In particular the comparison does not identify their values at a pole. -/
theorem heckeLFunctionC_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter) :
    heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character =
      toMeromorphicNFOn ψ.character.LFunction Set.univ := by
  obtain ⟨hdiv, hchg⟩ := of_eq_iff.mp (toPrimitiveRayClassCharacter.symm_apply_apply ψ)
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat,
    eq_of_level_eq_of_changeLevel_eq (fun {_ _} η ↦ η.LFunction) hdiv
      (absNorm_finitePart_conductor_toPrimitiveRayClassCharacter ψ) hchg]

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
