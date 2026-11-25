/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Finitely generated comodules form an essentially small category

For a coalgebra `C : Type v` over a commutative ring `R : Type u`, the category
`FGComoduleCat.{u, v, u} R C` of finitely generated right comodules with carriers in `Type u` is
essentially small in the universe `max u v`. In particular, finite-dimensional comodules over a
Hopf algebra and a field in the same universe form an essentially small category, which is one of
the hypotheses on a neutral Tannakian category.

A finitely generated `R`-module is isomorphic to a quotient of some `Rⁿ`, recorded by Mathlib's
small type `FGModuleRepr R`. Transporting the coaction of a finite comodule along such a linear
equivalence shows that every finite comodule is isomorphic to one whose carrier is drawn from
`FGModuleRepr R`. The isomorphism classes are therefore indexed by a small type of pairs of a
representative and a comodule structure on it.

## Main declarations

* `TauCeti.FGComoduleCat.essentiallySmall`: finitely generated comodules form an essentially
  small category.

## References

The small model of finite modules is Mathlib's `FGModuleRepr`, from
`Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall`.
-/

public section

open CategoryTheory

namespace TauCeti.FGComoduleCat

universe u v

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- **Finitely generated comodules form an essentially small category**: for a coalgebra
`C : Type v` over a commutative ring `R : Type u`, the category of finitely generated right
comodules with carriers in `Type u` is essentially small in the universe `max u v`. -/
instance essentiallySmall : EssentiallySmall.{max u v} (FGComoduleCat.{u, v, u} R C) := by
  -- Each finite comodule is isomorphic to a comodule structure on a small model of its module.
  let g : (Σ x : FGModuleRepr.{u} R, Comodule R C x) → Skeleton (FGComoduleCat.{u, v, u} R C) :=
    fun s => letI := s.2; toSkeleton (of (R := R) (C := C) s.1)
  have hg : Function.Surjective g := by
    intro X
    obtain ⟨M, rfl⟩ : ∃ M, toSkeleton M = X := ⟨_, toSkeleton_fromSkeleton_obj X⟩
    let e : M ≃ₗ[R] FGModuleRepr.ofFinite R M := (FGModuleRepr.ofFiniteEquiv R M).symm
    refine ⟨⟨FGModuleRepr.ofFinite R M, Comodule.Transport (R := R) (C := C) e⟩,
      congr_toSkeleton_of_iso ?_⟩
    exact ((ComoduleCat.isFG (R := R) (C := C)).isoMk
      (ComoduleCat.transportIso (R := R) (C := C) (M := M) e)).symm
  exact (essentiallySmall_iff _).2 ⟨small_of_surjective hg, locallySmall_max⟩

end TauCeti.FGComoduleCat
