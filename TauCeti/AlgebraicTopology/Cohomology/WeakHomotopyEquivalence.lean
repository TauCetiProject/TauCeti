/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Weak homotopy equivalences induce isomorphisms on singular cohomology

A weak homotopy equivalence `f : X → Y` induces isomorphisms `Hⁿ(Y; R, M) ≅ Hⁿ(X; R, M)` on
singular cohomology, for any chain coefficients `R` and values in any module `M`, and likewise on
cohomology with local coefficients in any system `L`. It also induces isomorphisms on the relative
cohomology of a map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces, for projective chain coefficients and for local coefficients with projective fibres.
More generally, for projective chain coefficients, a map of pairs inducing isomorphisms on
relative singular homology in every degree induces isomorphisms on relative singular cohomology.
No CW structure is needed.

The proof is at the chain level. The map of singular chains with local coefficients induced by
`f` is a chain homotopy equivalence, for every coefficient system
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_twistedChainComplexMap`), and so is
the map of singular chains with coefficients in any module
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_chainComplexMap`). The functor
`Hom(-, M)` turns a chain homotopy equivalence into a cochain homotopy equivalence
(`TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map`). For pairs, the map of
relative singular chains is a quasi-isomorphism by the five lemma; when its modules are projective
it is a chain homotopy equivalence
(`ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`).

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_singularCochainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularCohomologyMap`: a weak homotopy
  equivalence induces a cochain homotopy equivalence of singular cochains, and isomorphisms on
  singular cohomology.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_twistedCochainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedCohomologyMap`: the same with local
  coefficients in any system.
* `TopPair.homotopyEquivalences_singularCochainComplexMap_of_isIso_singularHomologyMap`,
  `TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap`: for projective chain
  coefficients, a map of pairs inducing isomorphisms on relative homology in every degree induces a
  cochain homotopy equivalence of relative cochains, and isomorphisms on relative cohomology.
* `TopPair.homotopyEquivalences_singularCochainComplexMap_of_isWeakHomotopyEquivalence`,
  `TopPair.isIso_singularCohomologyMap_of_isWeakHomotopyEquivalence`: the special case of a map
  of pairs which is a weak homotopy equivalence on the ambient spaces and on the subspaces.
* `TopPair.homotopyEquivalences_twistedCochainComplexMap_of_isWeakHomotopyEquivalence`,
  `TopPair.isIso_twistedCohomologyMap_of_isWeakHomotopyEquivalence`: the same for relative
  cohomology of pairs with local coefficients.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition 4.21 and Section 3.1.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 9.5.
-/

public section

open CategoryTheory

universe u v

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
  {A : Type u} [Ring A] (R : ModuleCat.{v} A)
  (k : Type*) [Ring k] [Linear k (ModuleCat.{v} A)] (M : ModuleCat.{v} A)

/-- **A weak homotopy equivalence induces a cochain homotopy equivalence of singular cochains**
`Hom(C(Y; R), M) ⟶ Hom(C(X; R), M)`, for any chain coefficients `R` and values in any module
`M`. -/
theorem homotopyEquivalences_singularCochainComplexMap (hf : f.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (TopCat.singularCochainComplexMap (R := R) (k := k) (M := M) (TopCat.ofHom f)) :=
  TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k M
    (hf.homotopyEquivalences_chainComplexMap R)

/-- **A weak homotopy equivalence induces isomorphisms on singular cohomology**
`Hⁿ(Y; R, M) ≅ Hⁿ(X; R, M)`, for any chain coefficients `R`, for instance the ring `A` itself, and
values in any module `M` (Hatcher, Proposition 4.21, dualized). -/
theorem isIso_singularCohomologyMap (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (TopCat.ofHom f) n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (hf.homotopyEquivalences_singularCochainComplexMap R k M)
  inferInstance

open TauCeti LocalCoefficientSystem

variable (L : LocalCoefficientSystem.{u, v, v} A (TopCat.of Y))

/-- **A weak homotopy equivalence induces a cochain homotopy equivalence of singular cochains with
local coefficients**, from the cochains of `Y` twisted by any local coefficient system `L` to
those of `X` twisted by its pullback, with values in any module `M`. -/
theorem homotopyEquivalences_twistedCochainComplexMap (hf : f.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (twistedCochainComplexMap.{u, v, v} k M (TopCat.ofHom f) L) :=
  TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k M
    (hf.homotopyEquivalences_twistedChainComplexMap L)

/-- **A weak homotopy equivalence induces isomorphisms on singular cohomology with local
coefficients** `Hⁿ(Y; L, M) ≅ Hⁿ(X; f⁎L, M)`, for any local coefficient system `L` on `Y` and
values in any module `M`. -/
theorem isIso_twistedCohomologyMap (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (twistedCohomologyMap.{u, v, v} k M (TopCat.ofHom f) L n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (hf.homotopyEquivalences_twistedCochainComplexMap k M L)
  inferInstance

end ContinuousMap.IsWeakHomotopyEquivalence

namespace TopPair

variable {P P' : TopPair.{v}} (f : P ⟶ P') {A : Type u} [Ring A] (R : ModuleCat.{v} A)
  [Projective R] (k : Type*) [Ring k] [Linear k (ModuleCat.{v} A)] (M : ModuleCat.{v} A)

/-- **A map of pairs inducing isomorphisms on relative singular homology induces a cochain
homotopy equivalence of relative singular cochains**: if `f` induces isomorphisms
`Hₙ(X, A; R) ≅ Hₙ(Y, B; R)` in every degree, for chain coefficients in a projective module `R`, then
it induces a cochain homotopy equivalence `Hom(C(Y, B; R), M) ⟶ Hom(C(X, A; R), M)` for values in
any module `M`. -/
theorem homotopyEquivalences_singularCochainComplexMap_of_isIso_singularHomologyMap
    (hf : ∀ n, IsIso (TopPair.singularHomologyMap f R n)) :
    HomologicalComplex.homotopyEquivalences _ _
      (singularCochainComplexMap (R := R) (k := k) (M := M) f) :=
  have : QuasiIso (singularChainComplexMap f R) :=
    (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 (hf n)
  ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective _ k M

/-- **A map of pairs inducing isomorphisms on relative singular homology induces isomorphisms on
relative singular cohomology**: if `f` induces isomorphisms `Hₙ(X, A; R) ≅ Hₙ(Y, B; R)` in every
degree, for chain coefficients in a projective module `R`, then it induces isomorphisms
`Hⁿ(Y, B; R, M) ≅ Hⁿ(X, A; R, M)` for values in any module `M`. -/
theorem isIso_singularCohomologyMap_of_isIso_singularHomologyMap
    (hf : ∀ n, IsIso (TopPair.singularHomologyMap f R n)) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_singularCochainComplexMap_of_isIso_singularHomologyMap f R k M hf)
  inferInstance

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a cochain homotopy equivalence of relative singular cochains**, for chain
coefficients in a projective module `R` and values in any module `M`. -/
theorem homotopyEquivalences_singularCochainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (singularCochainComplexMap (R := R) (k := k) (M := M) f) :=
  homotopyEquivalences_singularCochainComplexMap_of_isIso_singularHomologyMap f R k M
    (isIso_singularHomologyMap_of_isWeakHomotopyEquivalence f hfst hsnd R)

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces isomorphisms on relative singular cohomology** `Hⁿ(Y, B; R, M) ≅ Hⁿ(X, A; R, M)`,
for chain coefficients in a projective module `R` and values in any module `M`. -/
theorem isIso_singularCohomologyMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) :=
  isIso_singularCohomologyMap_of_isIso_singularHomologyMap f R k M
    (isIso_singularHomologyMap_of_isWeakHomotopyEquivalence f hfst hsnd R) n

section Twisted

variable (L : TauCeti.LocalCoefficientSystem.{u, v, v} A P'.fst) [∀ y, Projective (L.obj y)]

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a cochain homotopy equivalence of relative singular cochains with local
coefficients**, from the relative cochains of `P'` twisted by a local coefficient system `L` with
projective fibres to those of `P` twisted by its pullback, with values in any module `M`. -/
theorem homotopyEquivalences_twistedCochainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _ (TopPair.twistedCochainComplexMap k M f L) :=
  TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k M
    (homotopyEquivalences_twistedChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd L)

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces isomorphisms on relative singular cohomology with local coefficients**
`Hⁿ(Y, B; L, M) ≅ Hⁿ(X, A; f⁎L, M)`, for a local coefficient system `L` on `Y` with projective
fibres and values in any module `M`. -/
theorem isIso_twistedCohomologyMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (TopPair.twistedCohomologyMap k M f L n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_twistedCochainComplexMap_of_isWeakHomotopyEquivalence f k M L hfst hsnd)
  inferInstance

end Twisted

end TopPair
