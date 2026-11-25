/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative

/-!
# The Kronecker map of singular cohomology with local coefficients

Let `L` be a local coefficient system of `R`-modules on a space `X` and `M` an `R`-module. The
twisted singular cochains of `X` with values in `M` are the morphisms `C(X; L) ⟶ M` out of the
twisted singular chains (`TauCeti.LocalCoefficientSystem.twistedCochainComplex`), so a twisted
cocycle can be evaluated on a twisted cycle. This evaluation descends to the **Kronecker map**

`Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)`,

the Kronecker map `TauCeti.ChainComplex.kronecker` of the twisted singular chain complex. It is
natural in the space, for the pulled-back system, in the local coefficient system, and in the
module of values `M`. The same construction for the relative twisted chains of a pair `(X, A)`
gives the relative Kronecker map `Hⁿ(X, A; L, M) →ₗ[k] (Hₙ(X, A; L) ⟶ M)`, natural in maps of pairs
and compatible with the absolute one.

When `M` is an injective `R`-module the Kronecker map is bijective, in every degree and for every
local system; in degree zero it is bijective for every `M`. These are the cases of the universal
coefficient theorem with local coefficients in which no `Ext` term appears. The general case, over
a hereditary ring or with projective homology, is in
`TauCeti.AlgebraicTopology.Cohomology.Twisted.UniversalCoefficient`.

This is the twisted counterpart of `TopCat.singularKronecker` and `TopPair.singularKronecker`; for
a constant system the twisted cochains are the ordinary singular cochains
(`TauCeti.LocalCoefficientSystem.twistedCohomologyConstantIso`).

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.twistedKronecker`: the Kronecker map of twisted cohomology, with
  `TauCeti.LocalCoefficientSystem.twistedKronecker_homologyπ` computing it on classes of cocycles
  and cycles, and its naturality in the space
  (`TauCeti.LocalCoefficientSystem.twistedKronecker_twistedCohomologyMap`), in the local system
  (`TauCeti.LocalCoefficientSystem.twistedKronecker_twistedCohomologyCoefficientMap`) and in the
  module of values (`TauCeti.LocalCoefficientSystem.twistedKronecker_value_naturality`).
* `TauCeti.LocalCoefficientSystem.twistedKronecker_bijective`,
  `TauCeti.LocalCoefficientSystem.twistedKroneckerEquiv`: for an injective module of values, the
  Kronecker map is bijective, a `k`-linear equivalence;
  `TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_zero`: in degree zero it is bijective
  for every module of values.
* `TopPair.twistedKronecker`: the relative Kronecker map, with the same API, and
  `TopPair.twistedKronecker_twistedCohomologyπ` comparing it with the absolute one.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  {M : ModuleCat.{max v w} R} {X : TopCat.{v}}

section Definition

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **The Kronecker map of twisted singular cohomology** `Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)`: it
sends the class of a twisted cocycle `φ : Cₙ(X; L) ⟶ M` to the morphism which on the class of a
twisted cycle is `φ` evaluated on that cycle
(`TauCeti.LocalCoefficientSystem.twistedKronecker_homologyπ`). -/
def twistedKronecker (n : ℕ) : L.twistedCohomology k M n →ₗ[k] (L.twistedHomology n ⟶ M) :=
  TauCeti.ChainComplex.kronecker k L.twistedChainComplex M n

/-- The Kronecker map of twisted cohomology is the Kronecker map of the twisted chain complex. -/
lemma twistedKronecker_def (n : ℕ) :
    L.twistedKronecker k (M := M) n = TauCeti.ChainComplex.kronecker k L.twistedChainComplex M n :=
  (rfl)

/-- The Kronecker map on the classes of a twisted cocycle and a twisted cycle is the cocycle
evaluated on the cycle. -/
@[simp, reassoc]
lemma twistedKronecker_homologyπ (n : ℕ) (φ : (L.twistedCochainComplex k M).cycles n) :
    L.twistedChainComplex.homologyπ n ≫
        L.twistedKronecker k n ((L.twistedCochainComplex k M).homologyπ n φ) =
      L.twistedChainComplex.iCycles n ≫ (L.twistedCochainComplex k M).iCycles n φ :=
  TauCeti.ChainComplex.kronecker_homologyπ n φ

/-- **Naturality of the twisted Kronecker map in the module of values**: postcomposing twisted
cochains with `g : M ⟶ N` postcomposes their evaluations with `g`. -/
lemma twistedKronecker_value_naturality {N : ModuleCat.{max v w} R} (g : M ⟶ N) (n : ℕ)
    (α : L.twistedCohomology k M n) :
    L.twistedKronecker k n
        (HomologicalComplex.homologyMap (L.twistedChainComplex.linearYonedaObjMap k g) n α) =
      L.twistedKronecker k n α ≫ g :=
  TauCeti.ChainComplex.kronecker_coefficient_naturality g n α

/-- **The universal coefficient theorem with local coefficients for injective values**: for an
injective module `M`, the Kronecker map `Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)` is bijective. -/
theorem twistedKronecker_bijective [Injective M] (n : ℕ) :
    Function.Bijective (L.twistedKronecker k (M := M) n) :=
  TauCeti.ChainComplex.kronecker_bijective n

/-- **The universal coefficient isomorphism with local coefficients for injective values**: for an
injective module `M`, the Kronecker map is a `k`-linear equivalence
`Hⁿ(X; L, M) ≃ₗ[k] (Hₙ(X; L) ⟶ M)`. -/
def twistedKroneckerEquiv [Injective M] (n : ℕ) :
    L.twistedCohomology k M n ≃ₗ[k] (L.twistedHomology n ⟶ M) :=
  LinearEquiv.ofBijective _ (L.twistedKronecker_bijective k n)

/-- The equivalence `TauCeti.LocalCoefficientSystem.twistedKroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma twistedKroneckerEquiv_apply [Injective M] (n : ℕ) (α : L.twistedCohomology k M n) :
    L.twistedKroneckerEquiv k n α = L.twistedKronecker k n α :=
  (rfl)

/-- **The universal coefficient theorem with local coefficients in degree zero**: for every module
of values `M`, the Kronecker map `H⁰(X; L, M) →ₗ[k] (H₀(X; L) ⟶ M)` is bijective, as no
differential leaves the degree-zero twisted chains. -/
theorem twistedKronecker_bijective_zero :
    Function.Bijective (L.twistedKronecker k (M := M) 0) :=
  TauCeti.ChainComplex.kronecker_bijective_of_isIso 0

end Definition

/-- **Naturality of the twisted Kronecker map in the local system**, `⟨η^*α, x⟩ = ⟨α, η_*x⟩`: for
a morphism `η : L ⟶ K` of local coefficient systems, evaluating the class `η^*α` of
`Hⁿ(X; L, M)` is evaluating `α ∈ Hⁿ(X; K, M)` after the map `Hₙ(X; L) ⟶ Hₙ(X; K)`. -/
lemma twistedKronecker_twistedCohomologyCoefficientMap
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (n : ℕ)
    (α : K.twistedCohomology k M n) :
    L.twistedKronecker k n (twistedCohomologyCoefficientMap k M η n α) =
      twistedHomologyCoefficientMap η n ≫ K.twistedKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (twistedChainComplexCoefficientMap η) n α

/-- **Naturality of the twisted Kronecker map in the space**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for a
continuous map `f : X ⟶ Y` and a local system `L` on `Y`, evaluating the pull-back of a class of
`Hⁿ(Y; L, M)` on `Hₙ(X; f^*L)` is evaluating the class after pushing forward along `f`. -/
lemma twistedKronecker_twistedCohomologyMap {Y : TopCat.{v}} (f : X ⟶ Y)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (n : ℕ) (α : L.twistedCohomology k M n) :
    ((pullback f.hom).obj L).twistedKronecker k n (twistedCohomologyMap k M f L n α) =
      twistedHomologyMap f L n ≫ L.twistedKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (twistedChainComplexMap f L) n α

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti

variable {R : Type u} [Ring R]

section Definition

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : Type*)
  [Ring k] [Linear k (ModuleCat.{max v w} R)] {M : ModuleCat.{max v w} R}

/-- **The Kronecker map of relative twisted singular cohomology**
`Hⁿ(X, A; L, M) →ₗ[k] (Hₙ(X, A; L) ⟶ M)` of a topological pair: it sends the class of a relative
twisted cocycle to the morphism which on the class of a relative twisted cycle is the cocycle
evaluated on that cycle (`TopPair.twistedKronecker_homologyπ`). -/
def twistedKronecker (n : ℕ) : P.twistedCohomology L k M n →ₗ[k] (P.twistedHomology L n ⟶ M) :=
  TauCeti.ChainComplex.kronecker k (P.twistedChainComplex L) M n

/-- The Kronecker map of relative twisted cohomology is the Kronecker map of the relative twisted
chain complex. -/
lemma twistedKronecker_def (n : ℕ) :
    P.twistedKronecker L k (M := M) n =
      TauCeti.ChainComplex.kronecker k (P.twistedChainComplex L) M n :=
  (rfl)

/-- The relative Kronecker map on the classes of a relative twisted cocycle and a relative twisted
cycle is the cocycle evaluated on the cycle. -/
@[simp, reassoc]
lemma twistedKronecker_homologyπ (n : ℕ) (φ : (P.twistedCochainComplex L k M).cycles n) :
    (P.twistedChainComplex L).homologyπ n ≫
        P.twistedKronecker L k n ((P.twistedCochainComplex L k M).homologyπ n φ) =
      (P.twistedChainComplex L).iCycles n ≫ (P.twistedCochainComplex L k M).iCycles n φ :=
  TauCeti.ChainComplex.kronecker_homologyπ n φ

/-- **Naturality of the relative twisted Kronecker map in the module of values**: postcomposing
relative twisted cochains with `g : M ⟶ N` postcomposes their evaluations with `g`. -/
lemma twistedKronecker_value_naturality {N : ModuleCat.{max v w} R} (g : M ⟶ N) (n : ℕ)
    (α : P.twistedCohomology L k M n) :
    P.twistedKronecker L k n
        (HomologicalComplex.homologyMap ((P.twistedChainComplex L).linearYonedaObjMap k g) n α) =
      P.twistedKronecker L k n α ≫ g :=
  TauCeti.ChainComplex.kronecker_coefficient_naturality g n α

/-- **Compatibility of the relative and absolute twisted Kronecker maps**: evaluating the image in
`Hⁿ(X; L, M)` of a relative class `α ∈ Hⁿ(X, A; L, M)` is evaluating `α` after the map
`Hₙ(X; L) ⟶ Hₙ(X, A; L)`. -/
lemma twistedKronecker_twistedCohomologyπ (n : ℕ) (α : P.twistedCohomology L k M n) :
    L.twistedKronecker k n (P.twistedCohomologyπ L k M n α) =
      P.twistedHomologyπ L n ≫ P.twistedKronecker L k n α :=
  TauCeti.ChainComplex.kronecker_naturality (P.twistedChainComplexπ L) n α

/-- **The relative universal coefficient theorem with local coefficients for injective values**:
for an injective module `M`, the Kronecker map `Hⁿ(X, A; L, M) →ₗ[k] (Hₙ(X, A; L) ⟶ M)` is
bijective. -/
theorem twistedKronecker_bijective [Injective M] (n : ℕ) :
    Function.Bijective (P.twistedKronecker L k (M := M) n) :=
  TauCeti.ChainComplex.kronecker_bijective n

/-- **The relative universal coefficient isomorphism with local coefficients for injective
values**: for an injective module `M`, the relative Kronecker map is a `k`-linear equivalence
`Hⁿ(X, A; L, M) ≃ₗ[k] (Hₙ(X, A; L) ⟶ M)`. -/
def twistedKroneckerEquiv [Injective M] (n : ℕ) :
    P.twistedCohomology L k M n ≃ₗ[k] (P.twistedHomology L n ⟶ M) :=
  LinearEquiv.ofBijective _ (P.twistedKronecker_bijective L k n)

/-- The equivalence `TopPair.twistedKroneckerEquiv` is the relative Kronecker map. -/
@[simp]
lemma twistedKroneckerEquiv_apply [Injective M] (n : ℕ) (α : P.twistedCohomology L k M n) :
    P.twistedKroneckerEquiv L k n α = P.twistedKronecker L k n α :=
  (rfl)

/-- **The relative universal coefficient theorem with local coefficients in degree zero**: for
every module of values `M`, the relative Kronecker map `H⁰(X, A; L, M) →ₗ[k] (H₀(X, A; L) ⟶ M)` is
bijective, as no differential leaves the degree-zero relative twisted chains. -/
theorem twistedKronecker_bijective_zero :
    Function.Bijective (P.twistedKronecker L k (M := M) 0) :=
  TauCeti.ChainComplex.kronecker_bijective_of_isIso 0

end Definition

variable (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] {M : ModuleCat.{max v w} R}

/-- **Naturality of the relative twisted Kronecker map in the local system**: for a morphism
`η : L ⟶ K` of local coefficient systems on the ambient space of a pair, evaluating the class
`η^*α` of `Hⁿ(X, A; L, M)` is evaluating `α ∈ Hⁿ(X, A; K, M)` after the map
`Hₙ(X, A; L) ⟶ Hₙ(X, A; K)`. -/
lemma twistedKronecker_twistedCohomologyCoefficientMap (P : TopPair.{v})
    {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ K) (n : ℕ)
    (α : P.twistedCohomology K k M n) :
    P.twistedKronecker L k n (P.twistedCohomologyCoefficientMap k M η n α) =
      P.twistedHomologyCoefficientMap η n ≫ P.twistedKronecker K k n α :=
  TauCeti.ChainComplex.kronecker_naturality (P.twistedChainComplexCoefficientMap η) n α

/-- **Naturality of the relative twisted Kronecker map in the pair**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for
a map of pairs `f : P ⟶ Q` and a local system `L` on the ambient space of `Q`, evaluating the
pull-back of a class of `Hⁿ(Q; L, M)` on `Hₙ(P; f^*L)` is evaluating the class after pushing
forward along `f`. -/
lemma twistedKronecker_twistedCohomologyMap {P Q : TopPair.{v}} (f : P ⟶ Q)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) (n : ℕ)
    (α : Q.twistedCohomology L k M n) :
    P.twistedKronecker ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k n
        (twistedCohomologyMap k M f L n α) =
      twistedHomologyMap f L n ≫ Q.twistedKronecker L k n α :=
  TauCeti.ChainComplex.kronecker_naturality (twistedChainComplexMap f L) n α

end TopPair
