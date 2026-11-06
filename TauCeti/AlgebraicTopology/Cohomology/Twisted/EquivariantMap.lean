/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.GroupCohomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.EquivariantMap

/-!
# Change of groups in dual-local-system cohomology

An equivariant map between contractible quotient covers along `φ : G →* H`, together with a
coefficient map `ξ : A ⟶ Rep.res φ D`, induces a pullback on twisted cohomology with values in
any module `N`. Under the comparison with group cohomology, this is Mathlib's change-of-group
map with coefficient map given by precomposition with `ξ` on `Homₖ(D, N)`.

Here twisted cochains are maps from twisted chains into `N`: the coefficient systems being
compared are the dual systems `Homₖ(L_A, N)` and `Homₖ(L_D, N)`, not `L_A` and `L_D` themselves.
Neither the coefficient modules nor their duals need be finite, projective or reflexive.

The proof dualizes the geometric comparison of tensor-coinvariant chains and then uses
`MonoidHom.groupCohomologyIhomIso_inv_naturality` for the singular-chain resolutions.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.8.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B F C : TopCat.{u}} {p : E ⟶ B} {q : F ⟶ C}
  {G H : Type u} [Group G] [Group H] [MulAction G E] [MulAction H F]
  (hG : IsQuotientCoveringMap p G) (hH : IsQuotientCoveringMap q H)
  (k : Type u) [CommRing k] {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
  {A : Rep.{u} k G} {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D)
  (N : Type u) [AddCommGroup N] [Module k N]

/-- Pullback on dual-local-system cohomology along an equivariant map of contractible covers
corresponds to change of group on group cohomology, with precomposition on the internal-hom
coefficients. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_hom_naturality_over
    [ContractibleSpace E] [ContractibleSpace F] (n : ℕ) :
    HomologicalComplex.homologyMap
        ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
          (hG.associatedTwistedChainMap hH k f hf b hb ξ).op) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N n).hom =
      (hH.twistedCohomologyIsoGroupCohomology k D N n).hom ≫
        groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  let := Classical.decEq G
  let := Classical.decEq H
  have hchains := congrArg (fun t ↦
      (ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map t.op)
    (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over hH k f hf b hb ξ)
  simp only [op_comp, Functor.map_comp] at hchains
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n) hchains.symm).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [twistedCohomologyIsoGroupCohomology_hom_eq,
    twistedCohomologyIsoGroupCohomology_hom_eq]
  -- The resolution complexes are singular chains by definition; term-mode pasting keeps
  -- those wrappers fixed while composing the geometric and algebraic naturality squares.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (φ.groupCohomologyIhomIso_inv_naturality ξ N
      (singularChainsResolution k E G) (singularChainsResolution k F H)
      (singularChainsRepResMap k f hf)
      (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
        (Category.assoc _ _ _).symm

/-- The inverse comparison is natural for equivariant maps of contractible covers and
compatible coefficient maps as well. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_inv_naturality_over
    [ContractibleSpace E] [ContractibleSpace F] (n : ℕ) :
    groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N n).inv =
      (hH.twistedCohomologyIsoGroupCohomology k D N n).inv ≫
        HomologicalComplex.homologyMap
          ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
            (hG.associatedTwistedChainMap hH k f hf b hb ξ).op) n :=
  -- The functorial dual complex and `twistedCohomology` agree by unfolding, so invert the
  -- comparison square in term mode rather than asking the rewriter to identify the wrappers.
  (CommSq.horiz_inv (f := hH.twistedCohomologyIsoGroupCohomology k D N n)
    (i := hG.twistedCohomologyIsoGroupCohomology k A N n)
    ⟨(hG.twistedCohomologyIsoGroupCohomology_hom_naturality_over hH k f hf b hb ξ N n).symm⟩).w.symm

end IsQuotientCoveringMap
