/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Functoriality
public import TauCeti.AlgebraicGeometry.FiniteEtale.Map
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
public import TauCeti.CategoryTheory.Adjunction.MapAut

/-!
# Étale fundamental groups of clopen subschemes

Let `g : T ⟶ S` be a finite étale monomorphism of schemes, such as the inclusion of a clopen
subscheme, and let `x` be a geometric point of `T`. Composition with `g` is a fully faithful left
adjoint of base change along `g` (`TauCeti.FiniteEtaleScheme.mapPullbackAdj`), so precomposition
with base change is an isomorphism of automorphism groups of fibre functors
(`CategoryTheory.Adjunction.mapAutWhiskeringLeftEquiv`). Hence the homomorphism of étale
fundamental groups `π₁(T, x) → π₁(S, x ≫ g)` induced by `g` is an isomorphism of topological
groups. No connectedness hypothesis is needed: the étale fundamental group `Aut (fiber x)` and the
homomorphism `mapAutFiber` are defined for every scheme.

For a clopen `U ⊆ S` this is the check in EtaleCohomologyFoundations §F.0.2 that the map of
fundamental groups along the inclusion of `S₁` into `S = S₁ ⊔ S₂` is an isomorphism: covers of
`S` restrict to covers of `S₁`, and every cover of `S₁` extends by the empty cover of `S₂`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.mapAutFiberEquivOfMono g h`: for a finite étale monomorphism `g`
  and `h : x ≫ g = y`, the isomorphism of topological groups `π₁(T, x) ≃ₜ* π₁(S, y)` underlying
  `mapAutFiber g h`.

## Main results

* `TauCeti.FiniteEtaleScheme.mapAutFiber_bijective_of_mono`: `mapAutFiber g h` is bijective for
  a finite étale monomorphism `g`.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_ι_bijective_of_isClosed`: `mapAutFiber U.ι rfl` is
  bijective for a clopen `U ⊆ S`.
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **Étale fundamental groups along a finite étale monomorphism.** For a finite étale
monomorphism `g : T ⟶ S`, such as the inclusion of a clopen subscheme, and `h : x ≫ g = y`, the
homomorphism `mapAutFiber g h : π₁(T, x) → π₁(S, y)` is an isomorphism of topological groups. Its
inverse precomposes with the extension functor `map g`. -/
noncomputable def mapAutFiberEquivOfMono (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S} (h : x ≫ g = y) :
    Aut (fiber x) ≃ₜ* Aut (fiber y) where
  __ := ((mapPullbackAdj g).mapAutWhiskeringLeftEquiv (fiber x)).trans
    (pullbackCompFiberIso g x ≪≫ eqToIso (congrArg fiber h)).conjAut
  continuous_toFun := (mapAutFiber g h).continuous.congr fun σ ↦ by
    change mapAutFiber g h σ = (pullbackCompFiberIso g x ≪≫ eqToIso (congrArg fiber h)).conjAut
      ((mapPullbackAdj g).mapAutWhiskeringLeftEquiv (fiber x) σ)
    rw [Adjunction.mapAutWhiskeringLeftEquiv_apply, mapAutFiber_eq_conjAut]
  continuous_invFun :=
    ((((mapPullbackAdj g).unitWhiskerIso (fiber x)).symm.continuous_conjAut.comp
      (continuous_mapAut_whiskeringLeft (map g) (pullback g ⋙ fiber x))).comp
        (pullbackCompFiberIso g x ≪≫ eqToIso (congrArg fiber h)).symm.continuous_conjAut).congr
      fun τ ↦ by
        change _ = ((mapPullbackAdj g).mapAutWhiskeringLeftEquiv (fiber x)).symm
          ((pullbackCompFiberIso g x ≪≫ eqToIso (congrArg fiber h)).conjAut.symm τ)
        rw [Adjunction.mapAutWhiskeringLeftEquiv_symm_apply, Iso.conjAut_symm_apply]
        rfl

/-- The isomorphism `mapAutFiberEquivOfMono g h` is `mapAutFiber g h`. -/
@[simp]
theorem coe_mapAutFiberEquivOfMono (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S} (h : x ≫ g = y) :
    ⇑(mapAutFiberEquivOfMono g h) = mapAutFiber g h :=
  funext fun σ ↦ by
    change (pullbackCompFiberIso g x ≪≫ eqToIso (congrArg fiber h)).conjAut
      ((mapPullbackAdj g).mapAutWhiskeringLeftEquiv (fiber x) σ) = _
    rw [Adjunction.mapAutWhiskeringLeftEquiv_apply, mapAutFiber_eq_conjAut]

/-- For a finite étale monomorphism `g`, the induced homomorphism of étale fundamental groups is
bijective. -/
theorem mapAutFiber_bijective_of_mono (g : T ⟶ S) [IsFinite g] [Etale g] [Mono g]
    {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S} (h : x ≫ g = y) :
    Function.Bijective (mapAutFiber g h) :=
  coe_mapAutFiberEquivOfMono g h ▸ (mapAutFiberEquivOfMono g h).bijective

/-- **Fundamental groups of clopen pieces.** For a clopen `U ⊆ S` and a geometric point `x` of
`U`, the inclusion induces a bijection `π₁(U, x) → π₁(S, x ≫ U.ι)`. No connectedness of `S` or
`U` is assumed. -/
theorem mapAutFiber_ι_bijective_of_isClosed (U : S.Opens) (hU : IsClosed (U : Set S))
    (x : Spec (.of Ω) ⟶ U) :
    Function.Bijective (mapAutFiber U.ι (rfl : x ≫ U.ι = x ≫ U.ι)) := by
  have : Fact (IsClosed (U : Set S)) := ⟨hU⟩
  exact mapAutFiber_bijective_of_mono U.ι rfl

end TauCeti.FiniteEtaleScheme
