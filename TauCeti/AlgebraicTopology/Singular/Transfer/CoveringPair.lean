/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Relative homology of a pair whose subspace covers a weak model of the ambient space

Let `(D, S)` be a pair of spaces and `p : S → B` a covering map which extends to a weak homotopy
equivalence `π : D → B`. For instance `D` may be the unit disc bundle of a real line bundle over
`B` and `S` its unit sphere bundle, a double cover of `B`; or `D` the mapping cylinder of `p`. Then
the relative homology of `(D, S)` is the homology of `B` with local coefficients, shifted by one:

`Hₙ₊₁(D, S; R) ≅ Hₙ(B; L)`

(`TopPair.singularHomologySuccIsoTwistedHomology`), where `L` is any local system on `B` making

`0 ⟶ L ⟶ R[p] ⟶ R ⟶ 0`

short exact, `R[p]` being the permutation local system of `p` and `R[p] ⟶ R` its augmentation,
which adds up the coefficients of the sheets. So `L` is the kernel of the augmentation; for a double
cover it is the sign local system of the involution exchanging the sheets.

The singular chains of `S` are the chains of `B` twisted by `R[p]`, with `p_*` induced by the
augmentation (`IsCoveringMap.singularChainComplexPermutationIso_hom_comp_augmentation`). So the
chains of `B` twisted by `L` are the kernel of `p_* = π_* ∘ i_*`, where `i : S ⟶ D` is the
inclusion, and the isomorphism is the lift of the connecting map of the pair along this kernel
(`CategoryTheory.ShortComplex.ShortExact.liftδIso`): `π_*` is a quasi-isomorphism, and the cokernel
of `i_*` is the relative chain complex of the pair. Followed by the map `Hₙ(B; L) ⟶ Hₙ(S)`, it is
the connecting map `Hₙ₊₁(D, S) ⟶ Hₙ(S)` of the pair
(`TopPair.singularHomologySuccIsoTwistedHomology_hom_comp`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (homology with local coefficients and the local
  system of a covering space).
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace TopPair

variable (P : TopPair.{u}) {B : TopCat.{u}} {p : P.snd ⟶ B} (hp : IsCoveringMap p)
  (π : P.fst ⟶ B) (hπ : P.map ≫ π = p) (R : Type u) [Ring R]

/-- The comparison of the chains of `B` with constant coefficients with singular chains, the latter
written as the chains of the singular simplicial set of `B`, as in the chain complexes of a pair. -/
private def constantIso :
    LocalCoefficientSystem.twistedChainComplex.{u, u, u}
        ((constantFunctor B).obj (ModuleCat.of R R)) ≅
      (TopCat.toSSet.obj B).chainComplex (ModuleCat.of R R) :=
  LocalCoefficientSystem.twistedChainComplexConstantIso.{u, u, u} B (ModuleCat.of R R)

include hπ in
/-- On chains, the augmentation of the permutation local system of `p` is `p_* = π_* ∘ i_*`, read
through the comparison of the chains of the covering space with twisted chains of the base. -/
private lemma permutationIso_inv_comp_chainComplexMap :
    (hp.singularChainComplexPermutationIso R).symm.hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of R R) ≫
          SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R) ≫ (constantIso R).inv =
      LocalCoefficientSystem.twistedChainComplexCoefficientMap
        (hp.permutationLocalSystemAugmentation R) := by
  have h : SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of R R) ≫
      SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R) =
        SSet.chainComplexMap (TopCat.toSSet.map p) (ModuleCat.of R R) := by
    rw [← hπ, Functor.map_comp]
    exact (Functor.map_comp _ _ _).symm
  have hk : (hp.singularChainComplexPermutationIso R).hom ≫
      LocalCoefficientSystem.twistedChainComplexCoefficientMap
        (hp.permutationLocalSystemAugmentation R) ≫ (constantIso R).hom =
      SSet.chainComplexMap (TopCat.toSSet.map p) (ModuleCat.of R R) :=
    hp.singularChainComplexPermutationIso_hom_comp_augmentation R
  rw [reassoc_of% h, ← hk]
  simp

variable {R} (hπw : π.hom.IsWeakHomotopyEquivalence) {L : LocalCoefficientSystem.{u, u, u} R B}
  {ι : L ⟶ hp.permutationLocalSystem R} {hι₀ : ι ≫ hp.permutationLocalSystemAugmentation R = 0}
  (hι : (ShortComplex.mk ι _ hι₀).ShortExact)

include hπw in
private lemma quasiIso_chainComplexMap_comp_constantIso_inv :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R) ≫
      (constantIso (B := B) R).inv) := by
  have : QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R)) :=
    hπw.quasiIso_chainComplexMap (ModuleCat.of R R)
  infer_instance

/-- **The relative homology of a pair over a covering.** Let `p : S ⟶ B` be a covering map, the
restriction of a weak homotopy equivalence `π : D ⟶ B` to the subspace `S` of the pair `(D, S)`,
and let `L ⟶ R[p] ⟶ R` be a short exact sequence of local systems on `B` ending with the
augmentation of the permutation local system of `p`. Then `Hₙ₊₁(D, S; R) ≅ Hₙ(B; L)`. -/
def singularHomologySuccIsoTwistedHomology (n : ℕ) :
    P.singularHomology (ModuleCat.of R R) (n + 1) ≅ L.twistedHomology n :=
  (P.shortExact_singularChainComplexShortComplex (ModuleCat.of R R)).liftδIso
    (hι.map_of_exact (twistedChainComplexFunctor R B))
    (hp.singularChainComplexPermutationIso R).symm
    (SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R) ≫ (constantIso R).inv)
    (permutationIso_inv_comp_chainComplexMap P hp π hπ R)
    (quasiIso_chainComplexMap_comp_constantIso_inv P π hπw) (n + 1) n rfl

/-- The isomorphism `Hₙ₊₁(D, S) ≅ Hₙ(B; L)`, followed by the map `Hₙ(B; L) ⟶ Hₙ(B; R[p]) ≅ Hₙ(S)`
induced by `L ⟶ R[p]`, is the connecting map `Hₙ₊₁(D, S) ⟶ Hₙ(S)` of the pair. -/
@[reassoc]
theorem singularHomologySuccIsoTwistedHomology_hom_comp (n : ℕ) :
    (P.singularHomologySuccIsoTwistedHomology hp π hπ hπw hι n).hom ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap ι n ≫
          (hp.singularHomologyPermutationIso R n).inv =
      P.singularHomologyδ (ModuleCat.of R R) (n + 1) n := by
  have h := (P.shortExact_singularChainComplexShortComplex
    (ModuleCat.of R R)).liftδIso_hom_comp_homologyMap
    (hι.map_of_exact (twistedChainComplexFunctor R B))
    (hp.singularChainComplexPermutationIso R).symm
    (SSet.chainComplexMap (TopCat.toSSet.map π) (ModuleCat.of R R) ≫ (constantIso R).inv)
    (permutationIso_inv_comp_chainComplexMap P hp π hπ R)
    (quasiIso_chainComplexMap_comp_constantIso_inv P π hπw) (n + 1) n rfl
  rw [HomologicalComplex.homologyMap_comp] at h
  rw [IsCoveringMap.singularHomologyPermutationIso_inv, TopPair.singularHomologyδ,
    SSetPair.homologyδ]
  exact h

end TopPair
