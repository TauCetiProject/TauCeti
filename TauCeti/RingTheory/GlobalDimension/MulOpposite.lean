/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule.MulOpposite
public import TauCeti.RingTheory.Morita.GlobalDimension

/-!
# Left and right global dimension of a Noetherian ring

`TauCeti.globalDimension A` is the left global dimension of a ring `A`, so `globalDimension Aᵐᵒᵖ`
is its right global dimension. These can differ in general, but Auslander proved that they agree
for a ring that is both left and right Noetherian. The result is what transfers a bound on the
right global dimension of an Artin algebra to the left: for instance the endomorphism algebra of
an additive generator of the finitely generated modules, whose finitely presented right modules
have projective dimension at most two.

## Main results

* `TauCeti.hasInjectiveDimensionLE_characterModule_iff`: over a left Noetherian ring, a finite
  left module has projective dimension at most `n` exactly when its character module, a right
  module, has injective dimension at most `n`.
* `TauCeti.globalDimension_le_globalDimension_mulOpposite`: over a left Noetherian ring, the left
  global dimension is at most the right global dimension.
* `TauCeti.globalDimension_mulOpposite`: over a left and right Noetherian ring, the left and right
  global dimensions agree.
* `TauCeti.globalDimension_mulOpposite_of_moduleFinite`: the same for an algebra that is a finite
  module over a commutative Noetherian ring, for instance an Artin algebra.

## Implementation notes

Auslander compares both dimensions with the weak dimension, defined through `Tor`. Mathlib's tensor
product of modules needs a commutative base ring, so we use instead Lambek's character modules
(`CharacterModule.injective_iff_projective`), which send a projective resolution of a finite left
module to an injective coresolution of a right module, and detect the projectivity of its syzygies.

## References

* M. Auslander, *On the dimension of modules and algebras III: global dimension*, Nagoya Math. J.
  9 (1955), 67–77.
* J. Lambek, *A module is flat if and only if its character module is injective*, Canad. Math. Bull.
  7 (1964), 237–243.
-/

public section

universe v u

open CategoryTheory

open scoped CharacterModule

namespace TauCeti

/-- Over a left Noetherian ring, the character module of a finite module `M` has injective
dimension at most `n` exactly when `M` has projective dimension at most `n`. -/
theorem hasInjectiveDimensionLE_characterModule_iff {A : Type u} [Ring A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    HasInjectiveDimensionLE (ModuleCat.of Aᵐᵒᵖ (CharacterModule M)) n ↔
      HasProjectiveDimensionLE (ModuleCat.of A M) n := by
  induction n generalizing M with
  | zero =>
    have := Module.finitePresentation_of_finite A M
    rw [← injective_iff_hasInjectiveDimensionLE_zero,
      ← projective_iff_hasProjectiveDimensionLE_zero, ← Module.injective_iff_injective_object,
      ← IsProjective.iff_projective]
    exact CharacterModule.injective_iff_projective
  | succ n ih =>
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' A M
    have hex := LinearMap.exact_subtype_ker_map f
    let S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
      .mk (ModuleCat.ofHom (CharacterModule.opDual f))
        (ModuleCat.ofHom (CharacterModule.opDual (LinearMap.ker f).subtype))
        (by
          ext χ x
          exact DFunLike.congr_fun ((CharacterModule.exact_opDual hex).apply_apply_eq_zero χ) x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
          (CharacterModule.exact_opDual hex)
        mono_f := (ModuleCat.mono_iff_injective _).mpr
          (CharacterModule.opDual_injective_of_surjective f hf)
        epi_g := (ModuleCat.epi_iff_surjective _).mpr
          (CharacterModule.opDual_surjective_of_injective _ (Submodule.injective_subtype _)) }
    have hinj : Injective S.X₂ :=
      have : Module.Injective Aᵐᵒᵖ (CharacterModule (Fin k → A)) :=
        CharacterModule.injective_of_projective
      Module.injective_object_of_injective_module _ _
    exact (hS.hasInjectiveDimensionLT_X₃_iff n hinj).symm.trans
      ((ih (LinearMap.ker f)).trans (f.hasProjectiveDimensionLE_succ_iff_ker hf n).symm)

/-- Over a left Noetherian ring, the left global dimension is at most the right global dimension. -/
theorem globalDimension_le_globalDimension_mulOpposite (A : Type u) [Ring A] [IsNoetherianRing A]
    [Small.{v} A] : globalDimension.{v} A ≤ globalDimension.{v} Aᵐᵒᵖ := by
  have : Small.{v} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  rw [globalDimension_eq_globalDimension.{v, u} A, globalDimension_eq_globalDimension.{v, u} Aᵐᵒᵖ]
  induction h : globalDimension.{u} Aᵐᵒᵖ using WithBot.recBotCoe with
  | bot =>
    have : Subsingleton Aᵐᵒᵖ := (globalDimension_eq_bot_iff.{u} Aᵐᵒᵖ).mp h
    have : Subsingleton A := MulOpposite.op_injective.subsingleton
    exact ((globalDimension_eq_bot_iff.{u} A).mpr this).le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      refine ((globalDimension_le_tfae.{u} A n).out 2 1).mp fun M hM ↦ ?_
      have := hM
      exact (hasInjectiveDimensionLE_characterModule_iff M n).mp
        ((globalDimension_le_iff_hasInjectiveDimensionLE.{u} Aᵐᵒᵖ n).mp h.le _)

/-- **Auslander**: over a ring that is left and right Noetherian, the left and right global
dimensions agree. Auslander, *On the dimension of modules and algebras III*, Cor. 5. -/
theorem globalDimension_mulOpposite (A : Type u) [Ring A] [IsNoetherianRing A]
    [IsNoetherianRing Aᵐᵒᵖ] [Small.{v} A] : globalDimension.{v} Aᵐᵒᵖ = globalDimension.{v} A :=
  have : Small.{v} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  le_antisymm
    ((globalDimension_le_globalDimension_mulOpposite Aᵐᵒᵖ).trans_eq
      (RingEquiv.opOp A).globalDimension_eq.symm)
    (globalDimension_le_globalDimension_mulOpposite A)

/-- An algebra that is a finite module over a commutative Noetherian ring, for instance an Artin
algebra, has equal left and right global dimension. -/
theorem globalDimension_mulOpposite_of_moduleFinite (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type u) [Ring A] [Algebra R A] [Module.Finite R A] [Small.{v} A] :
    globalDimension.{v} Aᵐᵒᵖ = globalDimension.{v} A :=
  have : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  have : Module.Finite R Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv R)
  have : IsNoetherianRing Aᵐᵒᵖ := isNoetherian_of_tower R inferInstance
  globalDimension_mulOpposite A

end TauCeti
