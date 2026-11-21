/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Functoriality
public import TauCeti.CategoryTheory.Galois.Homomorphism

/-!
# Surjectivity and injectivity of homomorphisms of étale fundamental groups

Let `f : T ⟶ S` be a morphism of connected schemes, `x : Spec Ω ⟶ T` a geometric point and
`y = x ≫ f`. The continuous homomorphism of étale fundamental groups

`mapAutFiber f h : π₁(T, x) →ₜ* π₁(S, y)`

is the homomorphism induced by base change of finite étale covers along `f`, transported along the
identification `pullbackCompFiberIso` of base change followed by the geometric fibre at `x` with
the geometric fibre at `y` (`TauCeti.FiniteEtaleScheme.mapAutFiber_eq_conjAut`). The criteria for
Galois categories in `TauCeti.CategoryTheory.Galois.Homomorphism` therefore describe when it is
surjective or injective in terms of finite étale covers:

* `mapAutFiber f h` is surjective if and only if base change along `f` carries connected finite
  étale `S`-schemes to connected finite étale `T`-schemes;
* `mapAutFiber f h` is injective if and only if every connected finite étale `T`-scheme is a
  quotient of a subobject of the base change of some finite étale `S`-scheme.

These are the inputs, on the two sides, to the exactness of sequences of étale fundamental groups
such as `1 → π₁(X_K) → π₁(X) → Γ_k → 1` for a geometrically connected scheme `X` over a field `k`,
where `K` is an algebraic closure of `k` and `Γ_k` the absolute Galois group: surjectivity on the
right says that base change to `X` of a finite separable field extension of `k` stays connected.

## Main results

* `TauCeti.FiniteEtaleScheme.mapAutFiber_surjective_iff`: `mapAutFiber f h` is surjective if and
  only if base change along `f` preserves connectedness.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_injective_iff`: `mapAutFiber f h` is injective if and
  only if every connected finite étale `T`-scheme is a quotient of a subobject of a base change.

## References

* A. Grothendieck, *SGA 1*, Exposé V, Propositions 6.9 and 6.11.
* The Stacks Project, Lemma 0BN6 (Section 58.4, *Functors and homomorphisms*).
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Over a connected base, base change along `f : T ⟶ S` followed by a geometric fibre functor of
`T` is a fibre functor, being isomorphic to a geometric fibre functor of `S`. -/
instance [PreconnectedSpace S] (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T) :
    FiberFunctor (pullback f ⋙ fiber x) :=
  FiberFunctor.of_iso (pullbackCompFiberIso f x).symm

variable [ConnectedSpace S] [ConnectedSpace T]

/-- **Surjectivity criterion for étale fundamental groups.** For a morphism `f : T ⟶ S` of
connected schemes, the induced homomorphism `π₁(T, x) → π₁(S, y)` is surjective if and only if
the base change along `f` of every connected finite étale `S`-scheme is connected. -/
theorem mapAutFiber_surjective_iff (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S}
    (h : x ≫ f = y) :
    Function.Surjective (mapAutFiber f h) ↔ PreservesIsConnected (pullback f) := by
  rw [← mapAut_whiskeringLeft_surjective_iff (pullback f) (fiber x),
    show ⇑(mapAutFiber f h) = _ ∘ _ from funext (mapAutFiber_eq_conjAut f h),
    Function.Surjective.of_comp_iff' (Iso.conjAut _).bijective]

/-- **Injectivity criterion for étale fundamental groups.** For a morphism `f : T ⟶ S` of
connected schemes, the induced homomorphism `π₁(T, x) → π₁(S, y)` is injective if and only if
every connected finite étale `T`-scheme `A` is a quotient of a subobject of the base change of a
finite étale `S`-scheme `Y`: there are a monomorphism `Z ⟶ Y ×_S T` and an epimorphism
`Z ⟶ A`. -/
theorem mapAutFiber_injective_iff (f : T ⟶ S) {x : Spec (.of Ω) ⟶ T} {y : Spec (.of Ω) ⟶ S}
    (h : x ≫ f = y) :
    Function.Injective (mapAutFiber f h) ↔
      ∀ (A : FiniteEtaleScheme T) [IsConnected A], ∃ (Y : FiniteEtaleScheme S)
        (Z : FiniteEtaleScheme T) (i : Z ⟶ (pullback f).obj Y) (p : Z ⟶ A), Mono i ∧ Epi p := by
  rw [← mapAut_whiskeringLeft_injective_iff (pullback f) (fiber x),
    show ⇑(mapAutFiber f h) = _ ∘ _ from funext (mapAutFiber_eq_conjAut f h),
    Function.Injective.of_comp_iff (Iso.conjAut _).injective]

end TauCeti.FiniteEtaleScheme
