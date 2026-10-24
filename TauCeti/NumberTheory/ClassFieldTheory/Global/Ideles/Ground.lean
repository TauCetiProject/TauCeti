/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization

/-!
# Completion coordinates of ground-field ideles

An idele of a number field defines an invariant idele in its separable closure, by extension
through the bottom finite Galois subextension. Its finite completion coordinates are exactly the
original local components, independently of the embedding of separable closures. These equations
allow the character formula on invariant ideles to be applied to individual local factors.

## References

* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension

variable {K : Type} [Field K] [NumberField K]

local notation "E₀" =>
  ((⊥ : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    IntermediateField K (SeparableClosure K))

-- Keep the local fields abstract while checking the bottom-field scalar towers; substituting
-- completion types in these equations makes elaboration exceed the default heartbeat limit.
omit [NumberField K] in
private theorem agree_on_bot {F B : Type} [Field F] [Algebra K F] [Field B] [Algebra F B]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (f : E₀ →+* B)
    (τ' : B →ₐ[F] SeparableClosure F)
    (hf : ∀ k : K, algebraMap F B (algebraMap K F k) = f (algebraMap K E₀ k)) (x : E₀) :
    τ x = τ' (f x) := by
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 x.2
  have hx : x = algebraMap K E₀ k := Subtype.ext hk.symm
  calc
    τ x = τ (algebraMap K (SeparableClosure K) k) := congrArg τ hk.symm
    _ = algebraMap K (SeparableClosure F) k := τ.commutes k
    _ = algebraMap F (SeparableClosure F) (algebraMap K F k) :=
      IsScalarTower.algebraMap_apply K F (SeparableClosure F) k
    _ = τ' (algebraMap F B (algebraMap K F k)) := (τ'.commutes _).symm
    _ = τ' (f (algebraMap K E₀ k)) := congrArg τ' (hf k)
    _ = τ' (f x) := congrArg (fun y ↦ τ' (f y)) hx.symm

/-- Extending a ground-field idele to the separable closure does not change its coordinate at
a finite place, for any embedding of separable closures. -/
@[simp]
theorem ideleCoeffComponent_ideleExtension_bot (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (a : IdeleGroup (𝓞 K) K) :
    ideleCoeffComponent τ
        (ideleCoeffOf K ⊥ (.ofMul (GlobalNumberFields.ideleExtension K E₀ a))) =
      (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul (v.ideleFiniteCoord a)) :
        UnitsCoeff (v.adicCompletion K)) := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E₀) v
  let τ' : w.adicCompletion E₀ →ₐ[(w.under (𝓞 K)).adicCompletion K]
      SeparableClosure ((w.under (𝓞 K)).adicCompletion K) := IsSepClosed.lift
  have hτ := agree_on_bot τ (algebraMap E₀ (w.adicCompletion E₀)) τ' (fun k ↦ by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply] using
      HeightOneSpectrum.adicCompletionExtension_coe K E₀ (w.under (𝓞 K)) w k)
  apply Additive.toMul.injective
  simp only [← ideleCoeffOfIntermediateField_coe,
    toMul_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq_map_ideleFiniteCoord w τ' τ hτ,
    GlobalNumberFields.ideleFiniteCoord_ideleExtension, toMul_coe_baseUnitsEquivInvariants]
  apply Units.ext
  simpa [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra] using
    τ'.commutes ((w.under (𝓞 K)).ideleFiniteCoord a : (w.under (𝓞 K)).adicCompletion K)

end TauCeti.ClassFieldTheory
