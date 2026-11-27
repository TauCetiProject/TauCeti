/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Abelian
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.CompletionSections
import Mathlib.RingTheory.AdicCompletion.Exactness
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Exactness of the completion functor on an affine noetherian scheme

The completion functor `M ↦ (M ⧸ I ^ (n + 1) M)ₙ` sends finitely presented `𝒪_X`-modules to
coherent formal modules on the formal completion `X/V(I)`. It is not exact level by level:
multiplication by `t` on `k[t]` is injective, but its reduction modulo `t` is zero. It is
nevertheless exact into the abelian category of coherent formal modules when `X` is noetherian
(Stacks, Lemma 30.23.4). This file proves this for `X = Spec R` with `R` noetherian.

Right exactness holds on every scheme, since pullback along the closed immersions
`V(I ^ (n + 1)) ⟶ X` preserves cokernels and cokernels of coherent formal modules are computed
level by level (`formalCompletion.isColimitCokernelCoforkCompletionFunctorMap`). Injectivity is the
Artin–Rees lemma. On `spf J` a morphism of coherent formal modules is a monomorphism as soon as
the inverse limit of its towers of global sections is injective
(`CoherentFormalModule.mono_of_injective_limMap`), and for the completion of `φ : M ⟶ N` on
`Spec R` this limit is the `J`-adic completion of the map of global sections of `φ`
(`formalCompletion.completionFunctorSectionsLimEquiv_limMap`), which is injective for an injective
map of finite modules over a noetherian ring (`AdicCompletion.map_injective`).

## Main results

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.mono_of_injective_limMap`:
  a morphism of coherent formal modules on `spf J` whose limit of global sections is injective is
  a monomorphism.
* `AlgebraicGeometry.Scheme.formalCompletion.isColimitCokernelCoforkCompletionFunctorMap`: the
  completion functor preserves cokernels.
* `AlgebraicGeometry.Scheme.formalCompletion.epi_completionFunctor_map`: the completion functor
  preserves epimorphisms.
* `AlgebraicGeometry.Scheme.formalCompletion.mono_completionFunctor_map`: on `Spec R` with `R`
  noetherian, the completion functor preserves monomorphisms.
* `AlgebraicGeometry.Scheme.formalCompletion.shortExact_completionFunctor`: on `Spec R` with `R`
  noetherian, the completion functor sends short exact sequences to short exact sequences.

## References

* [Stacks Project, Lemma 30.23.4](https://stacks.math.columbia.edu/tag/0881).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A morphism `f` of coherent formal modules on `spf I` is a monomorphism if the inverse limit
of the morphism of towers of global sections of `f` is injective. A morphism `g` with `g ≫ f = 0`
then has zero limit of global sections, so `g = 0`, because morphisms of `I`-adic systems are
determined by their limits. -/
theorem mono_of_injective_limMap {M N : CoherentFormalModule (spf I)} (f : M ⟶ N)
    (hf : Function.Injective (ModuleTower.limMap ((sectionsTower I).map f))) : Mono f := by
  refine Preadditive.mono_of_cancel_zero _ fun {P} g hg ↦ (sectionsTower I).map_injective ?_
  rw [Functor.map_zero]
  refine (ModuleTower.limMap_inj ((ModuleTower.isFiniteAdicSystem_iff I _).1
    (isFiniteAdicSystem_sectionsTower_obj I P)).1.transition_surjective).1 ?_
  refine LinearMap.ext fun y ↦ hf ?_
  rw [← LinearMap.comp_apply, ← ModuleTower.limMap_comp, ← Functor.map_comp, hg,
    Functor.map_zero, ModuleTower.limMap_zero, ModuleTower.limMap_zero, LinearMap.zero_apply,
    LinearMap.zero_apply, map_zero]

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

namespace AlgebraicGeometry.Scheme.formalCompletion

open IdealSheafData

/-! ### Right exactness -/

section RightExact

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The completion functor preserves cokernels.** If `g : N ⟶ P` is a cokernel of
`f : M ⟶ N` in `𝒪_X`-modules, then the completion of `g` is a cokernel of the completion of `f`,
since cokernels of coherent formal modules are computed level by level and pullback along the
closed immersions `V(I ^ (n + 1)) ⟶ X` preserves them. -/
noncomputable def isColimitCokernelCoforkCompletionFunctorMap {M N P : FinitelyPresentedSheaf X}
    {f : M ⟶ N} {g : N ⟶ P} (w : f.hom ≫ g.hom = 0)
    (hg : IsColimit (CokernelCofork.ofπ g.hom w)) :
    IsColimit (CokernelCofork.ofπ (f := (completionFunctor X I).map f)
      ((completionFunctor X I).map g) (by
        rw [← Functor.map_comp, ← (completionFunctor X I).map_zero M P]
        exact congrArg _ (InducedCategory.hom_ext w))) :=
  CoherentFormalModule.isColimitOfEvaluation _ fun n ↦
    (isColimitMapCoconeCoforkEquiv' (CoherentFormalModule.evaluation n) _).symm
      (isColimitMapCoconeCoforkEquiv' (Modules.pullback (toScheme X I n)) w
        (isColimitOfPreserves (Modules.pullback (toScheme X I n)) hg))

/-- **The completion functor preserves epimorphisms**: the completion of an epimorphism of
finitely presented `𝒪_X`-modules is an epimorphism at every level, being the pullback of an
epimorphism along a closed immersion. -/
theorem epi_completionFunctor_map {M N : FinitelyPresentedSheaf X} (φ : M ⟶ N) [Epi φ.hom] :
    Epi ((completionFunctor X I).map φ) :=
  (CoherentFormalModule.epi_iff_forall_epi_app _).2 fun n ↦ by
    have := (Modules.pullbackPushforwardAdjunction (toScheme X I n)).isLeftAdjoint
    have : Epi (C := X.Modules) φ.hom := ‹_›
    rw [completionFunctor_map_app]
    exact (Modules.pullback _).map_epi _

end RightExact

/-! ### Exactness on an affine noetherian scheme -/

section Affine

variable {R : Type u} [CommRing R]

/-- On `Spec R`, every ideal sheaf is cut out by an ideal of `R`, in the form used by
`specIso`. -/
private lemma exists_ofIdealTop_eq (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    ∃ J : Ideal R, ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom) = I := by
  let e := (ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  exact ⟨(equivOfIsAffine I).map e,
    (congrArg ofIdealTop (Ideal.map_of_equiv e)).trans (equivOfIsAffine.symm_apply_apply I)⟩

variable [IsNoetherianRing R]

/-- **The completion functor preserves monomorphisms on an affine noetherian scheme** (the
Artin–Rees lemma, Stacks, Lemma 30.23.4): for a noetherian ring `R`, an ideal sheaf `I` on
`Spec R` and a monomorphism `φ` of finitely presented modules on `Spec R`, the completion of `φ`
is a monomorphism of coherent formal modules on `Spec R/V(I)`, although its levels
`M ⧸ I ^ (n + 1) M ⟶ N ⧸ I ^ (n + 1) N` need not be injective. -/
@[stacks 0881]
theorem mono_completionFunctor_map (I : (Spec (CommRingCat.of R)).IdealSheafData)
    {M N : FinitelyPresentedSheaf (Spec (CommRingCat.of R))} (φ : M ⟶ N) [Mono φ.hom] :
    Mono ((completionFunctor _ I).map φ) := by
  obtain ⟨J, rfl⟩ := exists_ofIdealTop_eq I
  -- Transport to `spf J`, where monomorphisms are detected on the limits of global sections.
  refine (CoherentFormalModule.pullback (specIso J).inv).mono_of_mono_map
    (CoherentFormalModule.mono_of_injective_limMap J _ ?_)
  have := Scheme.Modules.finitePresentation_moduleSpecΓ N.obj
  have : Mono (C := (Spec (CommRingCat.of R)).Modules) φ.hom := ‹_›
  have hφ : Function.Injective (moduleSpecΓFunctor.map φ.hom).hom :=
    (ModuleCat.mono_iff_injective _).1 (moduleSpecΓFunctor.map_mono _)
  intro y y' h
  apply (completionFunctorSectionsLimEquiv J M).injective
  apply AdicCompletion.map_injective J hφ
  rw [← completionFunctorSectionsLimEquiv_limMap, ← completionFunctorSectionsLimEquiv_limMap, h]

/-- **The completion functor is exact on an affine noetherian scheme** (Stacks, Lemma 30.23.4):
for a noetherian ring `R` and an ideal sheaf `I` on `Spec R`, the completion of a short exact
sequence of finitely presented modules on `Spec R` is a short exact sequence in the abelian
category of coherent formal modules on `Spec R/V(I)`. -/
@[stacks 0881]
theorem shortExact_completionFunctor (I : (Spec (CommRingCat.of R)).IdealSheafData)
    {S : ShortComplex (FinitelyPresentedSheaf (Spec (CommRingCat.of R)))}
    (hS : (S.map (ObjectProperty.ι _)).ShortExact) :
    (S.map (completionFunctor _ I)).ShortExact := by
  have : Mono S.f.hom := hS.mono_f
  have : Epi S.g.hom := hS.epi_g
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkCompletionFunctorMap I _ hS.gIsCokernel))
    (mono_completionFunctor_map I S.f) (epi_completionFunctor_map I S.g)

end Affine

end AlgebraicGeometry.Scheme.formalCompletion
