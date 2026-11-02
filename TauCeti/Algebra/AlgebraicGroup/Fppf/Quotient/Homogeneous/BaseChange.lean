/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-!
# Base change of affine homogeneous quotients

Let `G = Spec H` be a geometrically reduced affine group of finite type over a field `k`, and let
`N` be a linearly reductive closed subgroup, cut out by the Hopf ideal `I`. Then the fppf
homogeneous quotient `G/N` is the affine scheme `Spec B`, where `B = O(G)^N` is the algebra of
functions invariant under right translation by `N`
(`TauCeti.HopfIdeal.fppfHomogeneousQuotientIsoCoinvariantsPoints`).

This file proves that the construction commutes with every extension `K / k` of the base field.
Both hypotheses survive the extension, so the quotient `G_K/N_K` of the scalar-extended groups is
again affine, and it is represented by the scalar extension `K ⊗[k] B` of the original invariant
algebra:

```text
G_K/N_K ≅ Spec (K ⊗[k] O(G)^N).
```

The quotient map sends a point `g : K ⊗[k] H → A` of `G_K` to its restriction
`g ∘ (K ⊗ (B ↪ H))`. Morphisms from `Spec (K ⊗[k] B)` to an fppf sheaf over `K` are therefore
exactly the natural maps from `G_K` invariant under right multiplication by `N_K`.

The field `K` need not be algebraic over `k`; the comparison of invariant algebras is
`TauCeti.CommHopfAlgCat.coinvariantsBaseChangeEquiv`, which holds for every flat extension.

## Main declarations

* `TauCeti.HopfIdeal.fppfHomogeneousQuotientBaseChangeIso`: **the identification
  `G_K/N_K ≅ Spec (K ⊗[k] O(G)^N)`**.
* `TauCeti.HopfIdeal.fppfHomogeneousQuotientBaseChangeIso_hom_app_projection`: the quotient map
  `G_K → Spec (K ⊗[k] O(G)^N)` is restriction along `K ⊗[k] O(G)^N → K ⊗[k] O(G)`; on the level
  of natural transformations this is
  `HopfIdeal.fppfHomogeneousQuotientProjection_comp_fppfHomogeneousQuotientBaseChangeIso_hom`.
* `TauCeti.HopfIdeal.baseChangeCoinvariantsPointsHomEquiv`: the universal property of
  `Spec (K ⊗[k] O(G)^N)` as the quotient `G_K/N_K`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c and Chapter 12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§12.1 and 16.3.
* Y. Matsushima, *Espaces homogènes de Stein des groupes de Lie complexes*, Nagoya Math. J.
  **16** (1960), 205–218.
-/

public section

open CategoryTheory Opposite WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H] (I : HopfIdeal k H)
  (K : Type u) [Field K] [Algebra k K]

/-- **The affine homogeneous quotient commutes with extension of the base field.** For a linearly
reductive closed subgroup `N` of a geometrically reduced affine group `G` of finite type over a
field `k`, and any field extension `K / k`, the fppf homogeneous quotient `G_K/N_K` is represented
by `Spec (K ⊗[k] O(G)^N)`, the scalar extension of the invariant algebra of `N`. -/
noncomputable def fppfHomogeneousQuotientBaseChangeIso
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal)) :
    CommHopfAlgCat.fppfHomogeneousQuotient (CommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) ≅
      (CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.obj
        (op (CommAlgCat.of K (K ⊗[k] I.coinvariants))) :=
  (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).fppfHomogeneousQuotientIsoCoinvariantsPoints
      (I.isLinearlyReductive_quotient_baseChangeHopfIdeal K hlr) ≪≫
    (CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.mapIso
      (CommAlgCat.isoMk (CommHopfAlgCat.coinvariantsBaseChangeEquiv (S := K) I)).op

/-- The quotient map `G_K → G_K/N_K ≅ Spec (K ⊗[k] O(G)^N)` is restriction of points of `G_K` to
the invariants of `N_K`, followed by the comparison of those invariants with
`K ⊗[k] O(G)^N`. -/
@[reassoc]
theorem fppfHomogeneousQuotientProjection_comp_fppfHomogeneousQuotientBaseChangeIso_hom
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal)) :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection _ _ ≫
        (I.fppfHomogeneousQuotientBaseChangeIso K hlr).hom.hom =
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).toCoinvariantsPoints ≫
        ((CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.map
          (CommAlgCat.isoMk
            (CommHopfAlgCat.coinvariantsBaseChangeEquiv (S := K) I)).hom.op).hom := by
  rw [fppfHomogeneousQuotientBaseChangeIso, Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom,
    fppfHomogeneousQuotientIsoCoinvariantsPoints_hom,
    fppfHomogeneousQuotientProjection_comp_toCoinvariantsPoints_assoc, Functor.mapIso_hom,
    Iso.op_hom]

/-- The quotient map `G_K → Spec (K ⊗[k] O(G)^N)` sends a point `g` of `G_K` to its restriction
along the scalar extension `K ⊗[k] O(G)^N → K ⊗[k] O(G)` of the inclusion of invariants. -/
@[simp]
theorem fppfHomogeneousQuotientBaseChangeIso_hom_app_projection
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal))
    (A : ((CommAlgCat.{u} K)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := K) (H := CommHopfAlgCat.baseChange (K := K) H) A.unop.unop) :
    dsimp% (I.fppfHomogeneousQuotientBaseChangeIso K hlr).hom.hom.app A
        ((CommHopfAlgCat.fppfHomogeneousQuotientProjection _ _).app A (ULift.up g)) =
      ULift.up (CommAlgCat.ofHom (g.ofConv.comp
        (Algebra.TensorProduct.map (AlgHom.id K K) I.coinvariants.val))).op := by
  -- Both composites are evaluated in `Type`, where composition is function composition.
  refine (congrArg (fun φ ↦ φ.app A (ULift.up g))
    (I.fppfHomogeneousQuotientProjection_comp_fppfHomogeneousQuotientBaseChangeIso_hom K hlr)).trans
    ?_
  refine (congrArg (((CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.map
      (CommAlgCat.isoMk (CommHopfAlgCat.coinvariantsBaseChangeEquiv (S := K) I)).hom.op).hom.app A)
    ((CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).toCoinvariantsPoints_app_apply A g)).trans ?_
  exact congrArg ULift.up (Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun x ↦
    congrArg g.ofConv (CommHopfAlgCat.coe_coinvariantsBaseChangeEquiv I x))))

/-- **Universal property of `Spec (K ⊗[k] O(G)^N)` as the quotient `G_K/N_K`.** Morphisms from
`Spec (K ⊗[k] O(G)^N)` to an fppf sheaf `F` over `K` are exactly the natural maps from `G_K` to `F`
invariant under right multiplication by `N_K`. The correspondence is composition with the quotient
map. -/
noncomputable def baseChangeCoinvariantsPointsHomEquiv
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal))
    (F : Sheaf (CommAlgCat.fppfTopology K) (Type (u + 1))) :
    ((CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.obj
        (op (CommAlgCat.of K (K ⊗[k] I.coinvariants))) ⟶ F) ≃
      {f : HopfAlgebra.pointsPresheaf (CommHopfAlgCat.baseChange (K := K) H) ⋙
          uliftFunctor.{u + 1, u} ⟶ F.obj //
        ∀ (A : ((CommAlgCat.{u} K)ᵒᵖ)ᵒᵖ)
          (g : HopfAlgebra.points (R := K) (H := CommHopfAlgCat.baseChange (K := K) H) A.unop.unop)
          (n : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.baseChange (K := K) H)
            (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) A.unop.unop),
          f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)} :=
  (I.fppfHomogeneousQuotientBaseChangeIso K hlr).homFromEquiv.symm.trans
    (CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv _ _ F)

/-- The universal property sends a morphism out of `Spec (K ⊗[k] O(G)^N)` to its composite with
the quotient map `G_K → Spec (K ⊗[k] O(G)^N)`. -/
@[simp]
theorem baseChangeCoinvariantsPointsHomEquiv_apply
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal))
    (F : Sheaf (CommAlgCat.fppfTopology K) (Type (u + 1)))
    (φ : (CommAlgCat.fppfTopology K).uliftYoneda.{u + 1}.obj
      (op (CommAlgCat.of K (K ⊗[k] I.coinvariants))) ⟶ F) :
    (I.baseChangeCoinvariantsPointsHomEquiv K hlr F φ).val =
      CommHopfAlgCat.fppfHomogeneousQuotientProjection _ _ ≫
        (I.fppfHomogeneousQuotientBaseChangeIso K hlr).hom.hom ≫ φ.hom := by
  simp [baseChangeCoinvariantsPointsHomEquiv,
    CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_apply]

/-- Descending an `N_K`-invariant natural map through `Spec (K ⊗[k] O(G)^N)` and restricting along
the quotient map recovers that map. -/
@[simp]
theorem baseChangeCoinvariantsPointsHomEquiv_symm_apply
    (hlr : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal))
    (F : Sheaf (CommAlgCat.fppfTopology K) (Type (u + 1)))
    (f : HopfAlgebra.pointsPresheaf (CommHopfAlgCat.baseChange (K := K) H) ⋙
      uliftFunctor.{u + 1, u} ⟶ F.obj)
    (hf : ∀ (A : ((CommAlgCat.{u} K)ᵒᵖ)ᵒᵖ)
      (g : HopfAlgebra.points (R := K) (H := CommHopfAlgCat.baseChange (K := K) H) A.unop.unop)
      (n : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) A.unop.unop),
      f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)) :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection _ _ ≫
        (I.fppfHomogeneousQuotientBaseChangeIso K hlr).hom.hom ≫
          ((I.baseChangeCoinvariantsPointsHomEquiv K hlr F).symm ⟨f, hf⟩).hom = f :=
  (I.baseChangeCoinvariantsPointsHomEquiv_apply K hlr F _).symm.trans
    (congrArg Subtype.val ((I.baseChangeCoinvariantsPointsHomEquiv K hlr F).apply_symm_apply
      ⟨f, hf⟩))

end TauCeti.HopfIdeal
