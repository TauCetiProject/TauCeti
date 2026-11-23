/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.StableTranslate
public import TauCeti.Algebra.Module.AuslanderReiten.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Equivalence

/-!
# The Auslander–Reiten translate as a stable equivalence

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that each `Hom_R(R ⧸ 𝔪, E)` has length one. The Auslander–Reiten translate `τ = D Tr` is an
equivalence

`τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`

from finitely presented (equivalently, finitely generated) modules modulo maps through projectives
to finitely generated modules modulo maps through injectives. It is the composite of the
Auslander–Bridger duality `Tr` (`TauCeti.stableTransposeEquivalence`, over any ring) and the stable
Matlis duality `D` (`TauCeti.finiteStableMatlisDualEquivalence`). Its inverse is the inverse
translate `τ⁻ = Tr D`.

## Main definitions

* `TauCeti.finiteStableTranslate`: the translate `τ = D Tr` with values in finitely generated
  modules modulo injectives; it is `TauCeti.stableTranslate` up to the inclusion
  (`TauCeti.finiteStableTranslateCompιIso`).
* `TauCeti.stableTranslateEquivalence`: **the translate is an equivalence**
  `(mod A) / 𝒫 ≌ (mod A) / ℐ`; its inverse is the inverse translate `τ⁻`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition IV.1.9.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u v

variable (R : Type*) [CommRing R] (A : Type u) [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]
  [IsNoetherianRing R] [Module.Finite R A] [Module.Finite R E]

/-- **The Auslander–Reiten translate on finitely generated modules**: `τ = D Tr`, from finitely
presented modules modulo projectives to finitely generated modules modulo injectives. -/
def finiteStableTranslate :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  stableTranspose.{u, v} A ⋙ finiteStableMatlisDualOp R A E

instance : (finiteStableTranslate R A E).Additive := by
  unfold finiteStableTranslate
  infer_instance

/-- The translate on finitely generated modules is the translate `TauCeti.stableTranslate`, up to
the inclusion of finitely generated modules modulo injectives. -/
def finiteStableTranslateCompιIso :
    finiteStableTranslate R A E ⋙ ObjectProperty.ι _ ≅ stableTranslate R A E :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (finiteStableMatlisDualOpCompιIso R E) ≪≫
    eqToIso (by rw [stableTranslate_def, stableTranslateFunctor_def, ← stableTranspose_def])

variable {R E} [IsArtinianRing R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

omit [IsNoetherianRing R] [Module.Finite R E] in
variable (R E) in
/-- **The Auslander–Reiten translate is a stable equivalence.** Over an Artin algebra, `τ = D Tr`
is an equivalence from finitely presented modules modulo projectives to finitely generated modules
modulo injectives. Its inverse is the inverse translate `τ⁻ = Tr D`. -/
def stableTranslateEquivalence :
    FinitelyPresentedStableModule.{u, max u v} A ≌
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  (stableTranspose.{u, v} A).asEquivalence.trans (finiteStableMatlisDualEquivalence R A E hE)

/-- The functor of the stable equivalence is the translate. -/
@[simp]
theorem stableTranslateEquivalence_functor :
    (stableTranslateEquivalence R A E hE).functor = finiteStableTranslate R A E := by
  rw [stableTranslateEquivalence, Equivalence.trans_functor, Functor.asEquivalence_functor,
    finiteStableMatlisDualEquivalence_functor, finiteStableTranslate]

end TauCeti
