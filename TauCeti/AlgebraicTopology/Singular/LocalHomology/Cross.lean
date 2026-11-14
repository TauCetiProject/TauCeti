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
# The local homology cross product

For points `x₁ : V₁` and `x₂ : V₂` of topological spaces `V₁` and `V₂`, the union
`V₁ × (V₂ ∖ {x₂}) ∪ (V₁ ∖ {x₁}) × V₂` is contained in — and equal to — `(V₁ × V₂) ∖ {(x₁, x₂)}`
(`TauCeti.subset_compl_singleton_prod`, `TauCeti.compl_singleton_prod_eq`). Pushing
`TopCat.singularRelativeHomologyCross` forward along a coefficient morphism `v : R ⊗ S ⟶ T` and
`TauCeti.subset_compl_singleton_prod` defines `TauCeti.complSingletonPairHomologyCross`:

`Hₚ(V₁, V₁ ∖ {x₁}; R) ⊗ H_q(V₂, V₂ ∖ {x₂}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T)`
(`p + q = n`).

This is the homological counterpart paired via `TopPair.singularKronecker` with
`TauCeti.complSingletonPairCross` in `TauCeti.AlgebraicTopology.Cohomology.Local.Cross` to show that
local cohomology cross products preserve and reflect generators without flatness or Künneth
assumptions.

As in `TauCeti.AlgebraicTopology.Singular.RelativeCrossProduct`, each declaration assumes discrete
colimit preservation for `tensorLeft` and `tensorRight`, together with cokernel preservation
(`PreservesColimitsOfShape WalkingParallelPair`) for `tensorLeft` of `Hₚ(V₁, V₁ ∖ {x₁}; R)` and
`tensorRight` of `Z_q(V₂, V₂ ∖ {x₂}; S)` and `C_{q+1}(V₂, V₂ ∖ {x₂}; S)`.

## Main definitions and results

* `TauCeti.complSingletonPairHomologyCross`: the local homology cross product on complements of
  singletons `(x₁, x₂)`, unfolded by `TauCeti.complSingletonPairHomologyCross_def`.
* `TauCeti.complSingletonPairHomologyCross_naturality`: naturality under continuous maps carrying
  `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`.
* `TauCeti.singularHomologyMap_complZeroPairIso_hom_tensorHom_complSingletonPairHomologyCross`:
  specialization of naturality to products of continuous linear equivalences at `0` via
  `ContinuousLinearEquiv.complZeroPairIso`.

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

/-- **The relative homology cross product on complements of singletons**
`Hₚ(V₁, V₁ ∖ {x₁}; R) ⊗ H_q(V₂, V₂ ∖ {x₂}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T)`
(`p + q = n`), pushing `TopCat.singularRelativeHomologyCross` forward along `v : R ⊗ S ⟶ T` and
`TauCeti.subset_compl_singleton_prod`. -/
def complSingletonPairHomologyCross {V₁ V₂ : Type w} [TopologicalSpace V₁]
    [TopologicalSpace V₂] (x₁ : V₁) (x₂ : V₂) (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularHomology R p ⊗
      (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularHomology S q ⟶
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂))
          ({(x₁, x₂)}ᶜ : Set (V₁ × V₂))).singularHomology T n :=
  TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
      ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
    HomologicalComplex.homologyMap
      (K := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
      (L := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularChainComplex T)
      (((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj
        (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
          snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))))) n ≫
    TopPair.singularHomologyMap (TopPair.ofSubsetMap
      (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
        snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))
      (B' := ({(x₁, x₂)}ᶜ : Set _))
      (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) fun _ hx ↦ subset_compl_singleton_prod x₁ x₂ hx) T n

/-- Definitional unfolding of `TauCeti.complSingletonPairHomologyCross`. -/
theorem complSingletonPairHomologyCross_def {V₁ V₂ : Type w} [TopologicalSpace V₁]
    [TopologicalSpace V₂] (x₁ : V₁) (x₂ : V₂) (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    complSingletonPairHomologyCross x₁ x₂ v p q n h =
      TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        HomologicalComplex.homologyMap
          (K := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
          (L := (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
              snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))))) n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap
          (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))
          (B' := ({(x₁, x₂)}ᶜ : Set _))
          (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂))
          fun _ hx ↦ subset_compl_singleton_prod x₁ x₂ hx) T n :=
  (rfl)

/-- **Naturality of `complSingletonPairHomologyCross`** in continuous maps `g₁ : V₁ ⟶ W₁` and
`g₂ : V₂ ⟶ W₂` carrying `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`. -/
@[reassoc]
theorem complSingletonPairHomologyCross_naturality
    {V₁ V₂ W₁ W₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂]
    [TopologicalSpace W₁] [TopologicalSpace W₂] {x₁ : V₁} {x₂ : V₂} {y₁ : W₁} {y₂ : W₂}
    (g₁ : TopCat.of V₁ ⟶ TopCat.of W₁) (g₂ : TopCat.of V₂ ⟶ TopCat.of W₂)
    (hg₁ : Set.MapsTo g₁ ({x₁}ᶜ : Set V₁) ({y₁}ᶜ : Set W₁))
    (hg₂ : Set.MapsTo g₂ ({x₂}ᶜ : Set V₂) ({y₂}ᶜ : Set W₂))
    (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({y₁}ᶜ : Set (TopCat.of W₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({y₂}ᶜ : Set (TopCat.of W₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({y₂}ᶜ : Set (TopCat.of W₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap g₁ hg₁) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g₂ hg₂) S q) ≫
      complSingletonPairHomologyCross y₁ y₂ v p q n h =
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
          (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) T n := by
  let uPair := TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
    ((TopCat.mapsTo_tensorHom_preimage_fst g₁ g₂ hg₁).union_union
      (TopCat.mapsTo_tensorHom_preimage_snd g₁ g₂ hg₂))
  let idV := TopPair.ofSubsetMap (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
      snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂)) (B' := ({(x₁, x₂)}ᶜ : Set _))
    (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) (fun _ hx ↦ subset_compl_singleton_prod x₁ x₂ hx)
  let idW := TopPair.ofSubsetMap (B := fst (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₁}ᶜ : Set W₁) ∪
      snd (TopCat.of W₁) (TopCat.of W₂) ⁻¹' ({y₂}ᶜ : Set W₂)) (B' := ({(y₁, y₂)}ᶜ : Set _))
    (𝟙 (TopCat.of W₁ ⊗ TopCat.of W₂)) (fun _ hx ↦ subset_compl_singleton_prod y₁ y₂ hx)
  have hcoeff : TopPair.singularHomologyMap uPair (R ⊗ S) n ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n =
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n ≫
        TopPair.singularHomologyMap uPair T n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ((SSetPair.chainComplexFunctor C).map v).naturality (TopPair.toSSetPair.map uPair)]
  have hpair : uPair ≫ idW =
      idV ≫ TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
        (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂) :=
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by rw [Category.comp_id, Category.id_comp])
  -- `TopCat.of W₁ ⊗ TopCat.of W₂` and `TopCat.of (W₁ × W₂)` are defeq at `default` (not
  -- `implicit`) transparency, so rewrite `hmap` on `idW`/`idV` before unfolding the cross product.
  have hmap : TopPair.singularHomologyMap uPair T n ≫ TopPair.singularHomologyMap idW T n =
      TopPair.singularHomologyMap idV T n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
          (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) T n := by
    rw [← TopPair.singularHomologyMap_comp, hpair, TopPair.singularHomologyMap_comp]
  calc
    _ = TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        TopPair.singularHomologyMap uPair (R ⊗ S) n ≫
        HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n ≫
        TopPair.singularHomologyMap idW T n :=
      TopCat.singularRelativeHomologyCross_naturality_assoc g₁ g₂ hg₁ hg₂ R S p q n h
        (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n ≫
          TopPair.singularHomologyMap idW T n)
    _ = TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor C).map v).app _) n ≫
        (TopPair.singularHomologyMap idV T n ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
            (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) T n) := by
      rw [reassoc_of% hcoeff, hmap]
    _ = _ := ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm

/-- **Naturality of `complSingletonPairHomologyCross` at the origin** under products of continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`. -/
@[reassoc]
theorem singularHomologyMap_complZeroPairIso_hom_tensorHom_complSingletonPairHomologyCross
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
      complSingletonPairHomologyCross (0 : W₁) (0 : W₂) v p q n h =
    complSingletonPairHomologyCross (0 : V₁) (0 : V₂) v p q n h ≫
      TopPair.singularHomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom T n := by
  let g₁ : TopCat.of V₁ ⟶ TopCat.of W₁ := TopCat.ofHom ((f₁ : V₁ →L[𝕜] W₁) : C(V₁, W₁))
  let g₂ : TopCat.of V₂ ⟶ TopCat.of W₂ := TopCat.ofHom ((f₂ : V₂ →L[𝕜] W₂) : C(V₂, W₂))
  have hprod : (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
      (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ f₁.mapsTo_compl_zero f₂.mapsTo_compl_zero) :
      TopPair.ofSubset ({(0 : V₁ × V₂)}ᶜ : Set (TopCat.of (V₁ × V₂))) ⟶
        TopPair.ofSubset ({(0 : W₁ × W₂)}ᶜ : Set (TopCat.of (W₁ × W₂)))) =
      (f₁.prodCongr f₂).complZeroPairIso.hom := by
    rw [(f₁.prodCongr f₂).complZeroPairIso_hom]
    exact TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  rw [f₁.complZeroPairIso_hom, f₂.complZeroPairIso_hom]
  refine (complSingletonPairHomologyCross_naturality g₁ g₂ f₁.mapsTo_compl_zero
    f₂.mapsTo_compl_zero v p q n h).trans (whisker_eq _ ?_)
  exact congrArg (fun φ ↦ TopPair.singularHomologyMap φ T n) hprod

end TauCeti
