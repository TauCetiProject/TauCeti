/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates

/-!
# Associated local systems of tensor products

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G`, and let `k` be a
commutative ring. A representation `A` of `G` has an associated local system `L_A` on `B`
(`IsQuotientCoveringMap.associatedLocalSystem`), and a sheet `e` over `x` identifies its fibre
over `x` with `A` (`IsQuotientCoveringMap.associatedLocalSystemFiberIso`). This file shows that
taking associated local systems turns the tensor product of representations into the pointwise
tensor product of local systems:

`L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}`

(`IsQuotientCoveringMap.associatedLocalSystemTensorIso`), naturally in both representations
(`IsQuotientCoveringMap.associatedLocalSystemTensorIso_hom_naturality`). In the coordinates of any
sheet `e` it is the identity of `A ⊗ A'`, read on the right through the coordinates of `e` on both
factors. It is built by recognizing `L_A ⊗ L_{A'}` through these sheet coordinates
(`IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates`): moving `e` to `g • e`
multiplies the coordinates of both factors by the action of `g`, which is the diagonal action on
`A ⊗ A'`.

A typical use twists a local system by a character. For a character `χ : G →* kˣ` and the
universal cover, `L_{D ⊗ k_χ}` is the tensor product of `L_D` with the rank-one local system
`L_{k_χ}`; this is how the target of the equivariant Thom isomorphism
(`TauCeti.quotientTwistedHomologyThomIso`) is identified with a local system twisted by the
orientation local system.

## Main definitions

* `IsQuotientCoveringMap.associatedLocalSystemTensorIso`: `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (A A' : Rep.{u} k G)

/-- The sheet coordinates of `L_A ⊗ L_{A'}`: those of the sheet `e` on both factors. -/
private abbrev tensorCoordinates {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystem k A ⊗ hG.associatedLocalSystem k A').obj x ≅
      ModuleCat.of k (A ⊗ A' : Rep.{u} k G) :=
  hG.associatedLocalSystemFiberIso k A e ⊗ᵢ hG.associatedLocalSystemFiberIso k A' e

/-- Moving the sheet by `g` composes the coordinates of both factors with the action of `g`, which
is the diagonal action on the tensor product. -/
private lemma tensorCoordinates_smul {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (g : G) :
    letI := hG.mulActionFiber x.as
    (tensorCoordinates hG k A A' (g • e)).hom =
      (tensorCoordinates hG k A A' e).hom ≫ ModuleCat.ofHom ((A ⊗ A' : Rep.{u} k G).ρ g) := by
  let := hG.mulActionFiber x.as
  rw [tensorIso_hom, tensorIso_hom, associatedLocalSystemFiberIso_hom_smul,
    associatedLocalSystemFiberIso_hom_smul, ← tensorHom_comp_tensorHom]
  -- The diagonal action of `g` on `A ⊗ A'` is the tensor product of the two actions.
  rfl

/-- Transport in `L_A ⊗ L_{A'}` is the identity in the coordinates of a sheet and of its transport,
factor by factor. -/
private lemma tensorCoordinates_map {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystem k A ⊗ hG.associatedLocalSystem k A').map γ ≫
        (tensorCoordinates hG k A A' (hG.isCoveringMap.monodromy γ e)).hom =
      (tensorCoordinates hG k A A' e).hom := by
  rw [tensorIso_hom, tensorIso_hom, Monoidal.tensorObj_map]
  -- `exact` sees through the pointwise tensor product of functors, which `rw` does not unfold.
  exact (tensorHom_comp_tensorHom _ _ _ _).trans (by
    rw [associatedLocalSystemFiberIso_map_hom, associatedLocalSystemFiberIso_map_hom])

/-- **The associated local system of a tensor product is the tensor product of the associated local
systems.** For representations `A` and `A'` of `G`, the local system associated to `A ⊗ A'` is the
pointwise tensor product `L_A ⊗ L_{A'}`, by the isomorphism which in the coordinates of any sheet
`e` is the identity of `A ⊗ A'` (`associatedLocalSystemTensorIso_hom_app_comp`): the class of
`(a ⊗ a') ⊗ [e]` goes to the tensor product of the classes of `a ⊗ [e]` and `a' ⊗ [e]`. -/
def associatedLocalSystemTensorIso :
    hG.associatedLocalSystem k (A ⊗ A') ≅
      hG.associatedLocalSystem k A ⊗ hG.associatedLocalSystem k A' :=
  hG.associatedLocalSystemIsoOfSheetCoordinates k (tensorCoordinates hG k A A')
    (tensorCoordinates_smul hG k A A') (tensorCoordinates_map hG k A A')

/-- In the coordinates of any sheet `e`, on the tensor product read factor by factor, the
isomorphism `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}` is the identity of `A ⊗ A'`. -/
-- Not a simp lemma: `simp` rewrites the coordinates `tensorIso` on the left-hand side first.
@[reassoc]
lemma associatedLocalSystemTensorIso_hom_app_comp {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemTensorIso k A A').hom.app x ≫
        (hG.associatedLocalSystemFiberIso k A e ⊗ᵢ hG.associatedLocalSystemFiberIso k A' e).hom =
      (hG.associatedLocalSystemFiberIso k (A ⊗ A') e).hom :=
  hG.associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp k (tensorCoordinates hG k A A')
    (tensorCoordinates_smul hG k A A') (tensorCoordinates_map hG k A A') e

/-- The isomorphism `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}` reads the fibre in the coordinates of a sheet `e`
and returns to the tensor product through the coordinates of `e` on both factors. -/
lemma associatedLocalSystemTensorIso_hom_app {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemTensorIso k A A').hom.app x =
      (hG.associatedLocalSystemFiberIso k (A ⊗ A') e).hom ≫
        (hG.associatedLocalSystemFiberIso k A e ⊗ᵢ hG.associatedLocalSystemFiberIso k A' e).inv :=
  (Iso.eq_comp_inv (tensorCoordinates hG k A A' e)).2
    (hG.associatedLocalSystemTensorIso_hom_app_comp k A A' e)

/-- The isomorphism `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}` sends the class of `(a ⊗ a') ⊗ [e]` to the tensor
product of the classes of `a ⊗ [e]` and `a' ⊗ [e]`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemTensorIso_hom_app_coinvariantsTensorMk_tmul
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (a : A) (a' : A') :
    ((hG.associatedLocalSystemTensorIso k A A').hom.app x).hom
        (Rep.coinvariantsTensorMk (A ⊗ A') (Rep.of (hG.fiberRepresentation k x.as))
          (a ⊗ₜ[k] a') (Finsupp.single e 1)) =
      Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e 1) ⊗ₜ[k]
        Rep.coinvariantsTensorMk A' (Rep.of (hG.fiberRepresentation k x.as)) a'
          (Finsupp.single e 1) := by
  rw [associatedLocalSystemTensorIso_hom_app hG k A A' e]
  -- In the coordinates of `e` itself, the class of `(a ⊗ a') ⊗ [e]` is `a ⊗ a'`.
  refine (congrArg (ModuleCat.Hom.hom ((hG.associatedLocalSystemFiberIso k A e).inv ⊗ₘ
    (hG.associatedLocalSystemFiberIso k A' e).inv))
    (hG.associatedLocalSystemFiberIso_hom_coinvariantsTensorMk k (A ⊗ A') e e (a ⊗ₜ a') 1)).trans
    ?_
  refine (ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _).trans ?_
  simp
  -- The two sides differ only in how the tensor product of the fibres is presented: as the fibre
  -- of the pointwise tensor product `L_A ⊗ L_{A'}`, or as `(L_A)_x ⊗ (L_{A'})_x`.
  rfl

/-- The isomorphism `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}` is natural in both representations. -/
@[reassoc]
lemma associatedLocalSystemTensorIso_hom_naturality {A₁ A₂ A₁' A₂' : Rep.{u} k G}
    (f : A₁ ⟶ A₂) (f' : A₁' ⟶ A₂') :
    hG.associatedLocalSystemMap k (f ⊗ₘ f') ≫ (hG.associatedLocalSystemTensorIso k A₂ A₂').hom =
      (hG.associatedLocalSystemTensorIso k A₁ A₁').hom ≫
        (hG.associatedLocalSystemMap k f ⊗ₘ hG.associatedLocalSystemMap k f') := by
  ext x : 2
  obtain ⟨z, hz⟩ := hG.surjective x.as
  let e : p ⁻¹' {x.as} := ⟨z, hz⟩
  -- Compare both sides in the coordinates of the sheet `e` on both factors.
  refine (cancel_mono (tensorCoordinates hG k A₂ A₂' e).hom).1 ?_
  rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc,
    associatedLocalSystemTensorIso_hom_app_comp, associatedLocalSystemFiberIso_hom_naturality]
  refine (congrArg (· ≫ _) (associatedLocalSystemTensorIso_hom_app_comp hG k A₁ A₁' e).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))
  -- Factor by factor, this is the naturality of the coordinates of `e` in the representation.
  refine Eq.trans ?_ (tensorHom_comp_tensorHom ((hG.associatedLocalSystemMap k f).app x)
    ((hG.associatedLocalSystemMap k f').app x) (hG.associatedLocalSystemFiberIso k A₂ e).hom
    (hG.associatedLocalSystemFiberIso k A₂' e).hom).symm
  rw [associatedLocalSystemFiberIso_hom_naturality, associatedLocalSystemFiberIso_hom_naturality,
    ← tensorHom_comp_tensorHom]
  -- The forgetful functor from representations sends `f ⊗ f'` to the tensor product of the maps.
  rfl

end IsQuotientCoveringMap
