/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# Locally constant multiplication on singular chains

A locally constant natural-number-valued function acts on singular chains by multiplying each
simplex by its value at any point of that simplex. The value is independent of the point,
since a simplex is connected. The action commutes with the boundary and with continuous maps
when the functions are pulled back. On a connected subspace it is ordinary multiplication by
one natural number.

This is the chain operation needed to express the transfer formula for coverings of variable
degree. We use Mathlib's coproduct presentation `SSet.isColimitChainComplexXCofan` and its
alternating boundary formula. See Hatcher, *Algebraic Topology*, Section 3.G, for transfer.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial
open TauCeti.TopCat

universe w v u

namespace TauCeti

variable {B Y : TopCat.{w}} {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] (R : C)

private def locallyConstantNsmulX (d : LocallyConstant B ℕ) (n : ℕ) :
    ((TopCat.toSSet.obj B).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj B).chainComplex R).X n :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj B).isColimitChainComplexXCofan R n)
    fun σ ↦ d (simplexMap σ (SimplexCategory.toTopInitialVertex _)) •
      (TopCat.toSSet.obj B).ιChainComplex σ

@[reassoc]
private lemma ι_locallyConstantNsmulX (d : LocallyConstant B ℕ) {n : ℕ}
    (σ : (TopCat.toSSet.obj B) _⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ locallyConstantNsmulX R d n =
      d (simplexMap σ (SimplexCategory.toTopInitialVertex _)) •
        (TopCat.toSSet.obj B).ιChainComplex σ :=
  Cofan.IsColimit.fac _ _ σ

/-- Multiplication on singular chains by a locally constant natural-number-valued function.
On a singular simplex it multiplies by the value at the initial vertex. -/
def singularChainLocallyConstantNsmul (d : LocallyConstant B ℕ) :
    (TopCat.toSSet.obj B).chainComplex R ⟶ (TopCat.toSSet.obj B).chainComplex R where
  f := locallyConstantNsmulX R d
  comm' := by
    rintro _ n rfl
    ext σ
    simp only [ι_locallyConstantNsmulX_assoc, SSet.ιChainComplex_d_assoc,
      Preadditive.nsmul_comp, Preadditive.sum_comp, Preadditive.zsmul_comp,
      ι_locallyConstantNsmulX, SSet.ιChainComplex_d]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm]
    congr 1
    simp only [SimplicialObject.δ, simplexMap_map, ContinuousMap.comp_apply]
    exact congrArg (fun a ↦ a • (TopCat.toSSet.obj B).ιChainComplex
      ((TopCat.toSSet.obj B).δ i σ))
      ((d.comap (simplexMap σ)).apply_eq_of_preconnectedSpace _ _)

/-- On the summand of a simplex, locally constant multiplication is multiplication by its
value at any chosen point of the simplex. -/
@[reassoc]
lemma ιChainComplex_singularChainLocallyConstantNsmul_f
    (d : LocallyConstant B ℕ) {n : ℕ} (σ : (TopCat.toSSet.obj B) _⦋n⦌)
    (x : SimplexCategory.toTop.{w}.obj ⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ (singularChainLocallyConstantNsmul R d).f n =
      d (simplexMap σ x) • (TopCat.toSSet.obj B).ιChainComplex σ := by
  exact (ι_locallyConstantNsmulX R d σ).trans
    (congrArg (fun a ↦ a • (TopCat.toSSet.obj B).ιChainComplex σ)
      ((d.comap (simplexMap σ)).apply_eq_of_preconnectedSpace _ x))

/-- The canonical computation rule uses the initial vertex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_singularChainLocallyConstantNsmul_f_initial
    (d : LocallyConstant B ℕ) {n : ℕ} (σ : (TopCat.toSSet.obj B) _⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ (singularChainLocallyConstantNsmul R d).f n =
      d (simplexMap σ (SimplexCategory.toTopInitialVertex _)) •
        (TopCat.toSSet.obj B).ιChainComplex σ :=
  ιChainComplex_singularChainLocallyConstantNsmul_f R d σ _

/-- A constant function acts by ordinary multiplication on the whole chain complex. -/
@[simp]
lemma singularChainLocallyConstantNsmul_const (d : ℕ) :
    singularChainLocallyConstantNsmul R (LocallyConstant.const B d) = d • 𝟙 _ := by
  ext n σ
  simp

/-- Locally constant multiplication commutes with push-forward after pulling back the
function along the continuous map. -/
@[reassoc]
lemma singularChainLocallyConstantNsmul_naturality (f : Y ⟶ B) (d : LocallyConstant B ℕ) :
    singularChainLocallyConstantNsmul R (d.comap f.hom) ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ singularChainLocallyConstantNsmul R d := by
  ext n σ
  simp [simplexMap_app]

/-- On the image of a map from a preconnected space, locally constant multiplication is the
scalar given by its value at any point of that space. -/
@[reassoc]
lemma chainComplexMap_comp_singularChainLocallyConstantNsmul [PreconnectedSpace Y]
    (f : Y ⟶ B) (d : LocallyConstant B ℕ) (y : Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ singularChainLocallyConstantNsmul R d =
      d (f y) • SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  rw [← singularChainLocallyConstantNsmul_naturality]
  have hd : d.comap f.hom = LocallyConstant.const Y (d (f y)) :=
    (d.comap f.hom).eq_const y
  rw [hd, singularChainLocallyConstantNsmul_const, Preadditive.nsmul_comp, Category.id_comp]

end TauCeti
