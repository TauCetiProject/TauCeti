/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Weak homotopy equivalences induce isomorphisms on singular cohomology

A weak homotopy equivalence `f : X → Y` induces isomorphisms `Hⁿ(Y; R, M) ≅ Hⁿ(X; R, M)` on
singular cohomology, for chain coefficients in a projective module `R` (for instance the ring
itself) and values in any module `M`, and likewise on cohomology with local coefficients in a
system with projective fibres, and on the relative cohomology of a map of pairs which is a weak
homotopy equivalence on the ambient spaces and on the subspaces. No CW structure is needed.

The proof is at the chain level. The map of singular chains induced by `f` is a quasi-isomorphism
(`ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_chainComplexMap`). With projective chain
coefficients the singular chain modules are projective, so it is a chain homotopy equivalence
(`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_chainComplexMap`), and the functor
`Hom(-, M)` turns it into a cochain homotopy equivalence of singular cochains
(`ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`). The same applies to
singular chains with local coefficients and to relative singular chains, whose modules are
projective under the same hypotheses.

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_singularCochainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularCohomologyMap`: a weak homotopy
  equivalence induces a cochain homotopy equivalence of singular cochains, and isomorphisms on
  singular cohomology.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_twistedCochainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedCohomologyMap`: the same with local
  coefficients.
* `TopPair.homotopyEquivalences_singularCochainComplexMap_of_isWeakHomotopyEquivalence`,
  `TopPair.isIso_singularCohomologyMap_of_isWeakHomotopyEquivalence`: the same for relative
  cohomology of pairs.

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
  {A : Type u} [Ring A] (R : ModuleCat.{v} A) [Projective R]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{v} A)] (M : ModuleCat.{v} A)

/-- **A weak homotopy equivalence induces a cochain homotopy equivalence of singular cochains**
`Hom(C(Y; R), M) ⟶ Hom(C(X; R), M)`, for chain coefficients in a projective module `R` and values
in any module `M`. -/
theorem homotopyEquivalences_singularCochainComplexMap (hf : f.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (TopCat.singularCochainComplexMap (R := R) (k := k) (M := M) (TopCat.ofHom f)) :=
  have := hf.quasiIso_chainComplexMap R
  ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective _ k M

/-- **A weak homotopy equivalence induces isomorphisms on singular cohomology**
`Hⁿ(Y; R, M) ≅ Hⁿ(X; R, M)`, for chain coefficients in a projective module `R`, for instance the
ring `A` itself, and values in any module `M` (Hatcher, Proposition 4.21, dualized). -/
theorem isIso_singularCohomologyMap (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (TopCat.ofHom f) n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (hf.homotopyEquivalences_singularCochainComplexMap R k M)
  inferInstance

open TauCeti LocalCoefficientSystem

variable (L : LocalCoefficientSystem.{u, v, v} A (TopCat.of Y)) [∀ y, Projective (L.obj y)]

/-- **A weak homotopy equivalence induces a cochain homotopy equivalence of singular cochains with
local coefficients**, from the cochains of `Y` twisted by a local coefficient system `L` with
projective fibres to those of `X` twisted by its pullback, with values in any module `M`. -/
theorem homotopyEquivalences_twistedCochainComplexMap (hf : f.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (twistedCochainComplexMap.{u, v, v} k M (TopCat.ofHom f) L) := by
  obtain ⟨e, he⟩ := hf.homotopyEquivalences_twistedChainComplexMap L
  exact ⟨e.linearYonedaFunctorMap k M, by rw [HomotopyEquiv.linearYonedaFunctorMap_hom, he]⟩

/-- **A weak homotopy equivalence induces isomorphisms on singular cohomology with local
coefficients** `Hⁿ(Y; L, M) ≅ Hⁿ(X; f⁎L, M)`, for a local coefficient system `L` on `Y` with
projective fibres and values in any module `M`. -/
theorem isIso_twistedCohomologyMap (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (twistedCohomologyMap.{u, v, v} k M (TopCat.ofHom f) L n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (hf.homotopyEquivalences_twistedCochainComplexMap k M L)
  inferInstance

end ContinuousMap.IsWeakHomotopyEquivalence

namespace TopPair

variable {P P' : TopPair.{v}} (f : P ⟶ P') {A : Type u} [Ring A] (R : ModuleCat.{v} A)
  [Projective R] (k : Type*) [Ring k] [Linear k (ModuleCat.{v} A)] (M : ModuleCat.{v} A)

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a cochain homotopy equivalence of relative singular cochains**, for chain
coefficients in a projective module `R` and values in any module `M`. -/
theorem homotopyEquivalences_singularCochainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _
      (singularCochainComplexMap (R := R) (k := k) (M := M) f) :=
  have := quasiIso_singularChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd R
  ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective _ k M

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces isomorphisms on relative singular cohomology** `Hⁿ(Y, B; R, M) ≅ Hⁿ(X, A; R, M)`,
for chain coefficients in a projective module `R` and values in any module `M`. -/
theorem isIso_singularCohomologyMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) :=
  have := (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_singularCochainComplexMap_of_isWeakHomotopyEquivalence f R k M hfst hsnd)
  inferInstance

end TopPair
