/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.AlgebraicTopology.Singular.RelativeCrossProduct
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv

/-!
# The local homology cross product at the origin

For topological spaces `V₁` and `V₂` with a zero, `V₁ × (V₂ ∖ {0}) ∪ (V₁ ∖ {0}) × V₂` equals
`(V₁ × V₂) ∖ {0}` (`TauCeti.compl_zero_prod_eq`), so pushing `TopCat.singularRelativeHomologyCross`
forward along `v : R ⊗ S ⟶ T` defines `TauCeti.complZeroPairHomologyCross`:
`Hₚ(V₁, V₁ ∖ {0}; R) ⊗ H_q(V₂, V₂ ∖ {0}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T)` (`p + q = n`),
natural under products of continuous linear equivalences via
`ContinuousLinearEquiv.complZeroPairIso`
(`TauCeti.singularHomologyMap_complZeroPairIso_hom_tensorHom_complZeroPairHomologyCross`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.B.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T : C}

/-- **The relative homology cross product on complements of the origin**
`Hₚ(V₁, V₁ ∖ {0}; R) ⊗ H_q(V₂, V₂ ∖ {0}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T)` (`p + q = n`),
pushing `TopCat.singularRelativeHomologyCross` forward along `v : R ⊗ S ⟶ T`. -/
def complZeroPairHomologyCross (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁]
    [TopologicalSpace V₂] [Zero V₂] (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularHomology R p ⊗
      (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularHomology S q ⟶
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularHomology T n :=
  TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
      ({0}ᶜ : Set (TopCat.of V₁)) ({0}ᶜ : Set (TopCat.of V₂)) p q n h ≫
    HomologicalComplex.homologyMap
      (K := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
      (L := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))).singularChainComplex T)
      (((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj
        (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
          snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))))) n ≫
    TopPair.singularHomologyMap (TopPair.ofSubsetMap
      (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))
      (B' := ({(0 : V₁ × V₂)}ᶜ : Set (V₁ × V₂)))
      (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) fun _ hx ↦ subset_compl_zero_prod V₁ V₂ hx) T n

/-- Definitional unfolding of `TauCeti.complZeroPairHomologyCross`. -/
theorem complZeroPairHomologyCross_def (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁]
    [TopologicalSpace V₂] [Zero V₂] (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    complZeroPairHomologyCross V₁ V₂ v p q n h =
      TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({0}ᶜ : Set (TopCat.of V₁)) ({0}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        HomologicalComplex.homologyMap
          (K := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
          (L := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
              snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))))) n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap
          (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))
          (B' := ({(0 : V₁ × V₂)}ᶜ : Set (V₁ × V₂)))
          (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) fun _ hx ↦ subset_compl_zero_prod V₁ V₂ hx) T n :=
  (rfl)

/-- **Naturality of `complZeroPairHomologyCross`** under products of continuous linear equivalences
`f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`. -/
@[reassoc]
theorem singularHomologyMap_complZeroPairIso_hom_tensorHom_complZeroPairHomologyCross
    {𝕜 : Type*} [Semiring 𝕜] {V₁ V₂ W₁ W₂ : Type w}
    [TopologicalSpace V₁] [AddCommMonoid V₁] [Module 𝕜 V₁]
    [TopologicalSpace V₂] [AddCommMonoid V₂] [Module 𝕜 V₂]
    [TopologicalSpace W₁] [AddCommMonoid W₁] [Module 𝕜 W₁]
    [TopologicalSpace W₂] [AddCommMonoid W₂] [Module 𝕜 W₂]
    (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap f₁.complZeroPairIso.hom R p ⊗ₘ
        TopPair.singularHomologyMap f₂.complZeroPairIso.hom S q) ≫
      complZeroPairHomologyCross W₁ W₂ v p q n h =
    complZeroPairHomologyCross V₁ V₂ v p q n h ≫
      TopPair.singularHomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom T n := by
  rw [f₁.complZeroPairIso_hom, f₂.complZeroPairIso_hom,
    complZeroPairHomologyCross_def, complZeroPairHomologyCross_def]
  let g₁ : TopCat.of V₁ ⟶ TopCat.of W₁ := TopCat.ofHom ((f₁ : V₁ →L[𝕜] W₁) : C(V₁, W₁))
  let g₂ : TopCat.of V₂ ⟶ TopCat.of W₂ := TopCat.ofHom ((f₂ : V₂ →L[𝕜] W₂) : C(V₂, W₂))
  let uPair := TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
    ((TopCat.mapsTo_tensorHom_preimage_fst g₁ g₂ f₁.mapsTo_compl_zero).union_union
      (TopCat.mapsTo_tensorHom_preimage_snd g₁ g₂ f₂.mapsTo_compl_zero))
  let idV := TopPair.ofSubsetMap (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
      snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂)) (B' := ({(0 : V₁ × V₂)}ᶜ : Set _))
    (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) (fun _ hx ↦ subset_compl_zero_prod V₁ V₂ hx)
  let idW := TopPair.ofSubsetMap (B := fst (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({0}ᶜ : Set W₁) ∪
      snd (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({0}ᶜ : Set W₂)) (B' := ({(0 : W₁ × W₂)}ᶜ : Set _))
    (𝟙 (TopCat.of W₁ ⊗ TopCat.of W₂)) (fun _ hx ↦ subset_compl_zero_prod W₁ W₂ hx)
  have hcoeff : TopPair.singularHomologyMap uPair (R ⊗ S) n ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n =
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n ≫
        TopPair.singularHomologyMap uPair T n := by
    change HomologicalComplex.homologyMap (SSetPair.chainComplexMap
        (TopPair.toSSetPair.map uPair) (R ⊗ S)) n ≫ _ =
      _ ≫ HomologicalComplex.homologyMap
        (SSetPair.chainComplexMap (TopPair.toSSetPair.map uPair) T) n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ((SSetPair.chainComplexFunctor C).map v).naturality (TopPair.toSSetPair.map uPair)]
  have hpair : uPair ≫ idW = idV ≫ (f₁.prodCongr f₂).complZeroPairIso.hom :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
      ((ConcreteCategory.congr_hom (TopPair.Hom.fst_comp uPair idW) x).trans <|
        (ConcreteCategory.comp_apply _ _ x).trans <|
        (congrArg (TopPair.Hom.fst idW) (TopPair.ofSubsetMap_fst_apply _ _ x)).trans <|
        (TopPair.ofSubsetMap_fst_apply _ _ ((g₁ ⊗ₘ g₂) x)).trans <|
        (TopCat.id_app (TopCat.of W₁ ⊗ TopCat.of W₂) ((g₁ ⊗ₘ g₂) x)).trans
          (TopCat.tensor_apply g₁ g₂ x)).trans
      ((ConcreteCategory.congr_hom
          (TopPair.Hom.fst_comp idV (f₁.prodCongr f₂).complZeroPairIso.hom) x).trans <|
        (ConcreteCategory.comp_apply _ _ x).trans <|
        (congrArg (TopPair.Hom.fst (f₁.prodCongr f₂).complZeroPairIso.hom)
          (TopPair.ofSubsetMap_fst_apply _ _ x)).trans <|
        ((f₁.prodCongr f₂).complZeroPairIso_hom_fst_apply _).trans
          (congrArg (f₁.prodCongr f₂) (TopCat.id_app (TopCat.of V₁ ⊗ TopCat.of V₂) x))).symm)
  refine (TopCat.singularRelativeHomologyCross_naturality_assoc g₁ g₂ f₁.mapsTo_compl_zero
    f₂.mapsTo_compl_zero R S p q n h _).trans ((Eq.trans ?_ (Category.assoc _ _ _).symm))
  refine whisker_eq _ ((Category.assoc _ _ _).symm.trans
    ((hcoeff =≫ _).trans ((Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))))
  exact whisker_eq _ ((TopPair.singularHomologyMap_comp uPair T idW n).symm.trans
    ((congrArg (fun φ ↦ TopPair.singularHomologyMap φ T n) hpair).trans
      (TopPair.singularHomologyMap_comp idV T (f₁.prodCongr f₂).complZeroPairIso.hom n)))

end TauCeti
