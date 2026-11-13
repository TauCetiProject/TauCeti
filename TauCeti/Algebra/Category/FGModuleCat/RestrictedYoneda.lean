/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# Hom functors restricted to finitely generated modules

For a module `K` over a ring `R`, the functor `Hom(-, K)` restricted to the finitely generated
modules, `(-, K)|_fg`, is a functor `FGModuleCatᵒᵖ ⥤ AddCommGrpCat`. When `K` is itself finitely
generated it is representable, by `K` as an object of `FGModuleCat R`. Conversely, if
`(-, K)|_fg` is finitely generated, that is, a quotient of a representable functor `(-, Y)` with `Y`
finitely generated, then every morphism from a finitely generated module to `K` factors through a
single morphism `u : Y ⟶ K`. Applied to the inclusions of the cyclic submodules `R ∙ x`, this puts
every `x : K` in the range of `u`, so `K` is finitely generated.

So over a field `k`, the restriction of `Hom(-, K)` to finite-dimensional spaces is not a finitely
generated functor on finite-dimensional spaces for an infinite-dimensional space `K`. Every
morphism from a representable functor lands in the maps whose image lies in some
finite-dimensional subspace `K' ⊆ K`. So Hom functors of objects outside an additive category need
not be finitely generated on it, let alone finitely presented.

## Main results

* `ModuleCat.isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj_iff_finite`: the functor
  `(-, K)|_fg` is finitely generated exactly when `K` is a finitely generated module.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u

open CategoryTheory TauCeti

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- **Restricted Hom functors of modules.** For a module `K`, the restriction `(-, K)|_fg` of
`Hom(-, K)` to the finitely generated modules is a finitely generated functor on `FGModuleCat R`
exactly when `K` is a finitely generated module. -/
theorem isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj_iff_finite
    (K : ModuleCat.{v} R) :
    IsFinitelyGeneratedFunctor ((isFG R).restrictedPreadditiveYoneda.obj K) ↔
      Module.Finite R K := by
  refine ⟨fun hK ↦ ?_,
    fun hK ↦ (isFG R).isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj hK⟩
  obtain ⟨Y, hY, u, hu⟩ :=
    ((isFG R).isFinitelyGeneratedFunctor_restrictedPreadditiveYoneda_obj_iff K).1 hK
  have : Module.Finite R Y := hY
  refine Module.Finite.of_surjective u.hom fun x ↦ ?_
  obtain ⟨h, hh⟩ := hu (of R (R ∙ x)) (inferInstanceAs (Module.Finite R (R ∙ x)))
    (ofHom (R ∙ x).subtype)
  exact ⟨h.hom ⟨x, Submodule.mem_span_singleton_self x⟩, congr(($hh).hom ⟨x, _⟩)⟩

end ModuleCat
