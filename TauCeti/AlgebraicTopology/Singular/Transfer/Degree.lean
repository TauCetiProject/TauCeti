/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Degree
public import TauCeti.AlgebraicTopology.Singular.LocallyConstant
public import TauCeti.AlgebraicTopology.Singular.Transfer.Basic

/-!
# Transfer for coverings of variable degree

For a covering with finite fibres, projection after transfer multiplies a singular simplex
by the number of sheets over any point of that simplex. On a disconnected base this is not
in general a single scalar: it is the action of the locally constant function
`IsCoveringMap.degree`. This file proves the formula on chains and homology, then restricts it
to any preconnected subspace. In particular each connected component has its own degree.
The constant-degree formulas follow by specializing the degree to a constant function.
There is no connectedness, surjectivity, or uniform bound on the fibre cardinalities.

We reuse `IsCoveringMap.singularTransfer` and its summand formula. The mathematical reference
is Hatcher, *Algebraic Topology*, Section 3.G.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti

universe w v u

namespace IsCoveringMap

variable {E B Y : TopCat.{w}} {p : E ⟶ B}
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- **Variable-degree transfer formula on chains.** Projection after transfer is multiplication
by the locally constant fibre cardinality, rather than a single global degree. -/
theorem singularTransfer_comp_chainComplexMap_eq_locallyConstantNsmul
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) :
    hp.singularTransfer hfin R ≫ SSet.chainComplexMap (TopCat.toSSet.map p) R =
      singularChainLocallyConstantNsmul R hp.degree := by
  ext n σ
  rw [HomologicalComplex.comp_f,
    ιChainComplex_singularTransfer_f_comp_chainComplexMap_f hp hfin R σ
      (SimplexCategory.toTopInitialVertex _),
    ιChainComplex_singularChainLocallyConstantNsmul_f_initial, degree_apply]

/-- **Variable-degree transfer formula on homology.** Projection after transfer is the map
induced by multiplication of chains by the locally constant fibre cardinality. -/
theorem homologyMap_singularTransfer_comp_homologyMap_eq_locallyConstantNsmul
    [CategoryWithHomology C] (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map p) R n =
      HomologicalComplex.homologyMap (singularChainLocallyConstantNsmul R hp.degree) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    singularTransfer_comp_chainComplexMap_eq_locallyConstantNsmul]

/-- **The transfer formula** `p_* ∘ transfer = d • id` on singular chains, for a covering map
whose fibres all have `d` points. -/
theorem singularTransfer_comp_chainComplexMap (hp : IsCoveringMap p)
    (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {d : ℕ} (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) :
    hp.singularTransfer hfin R ≫ SSet.chainComplexMap (TopCat.toSSet.map p) R = d • 𝟙 _ := by
  have hdegree : hp.degree = LocallyConstant.const B d := by
    ext b
    simpa only [degree_apply, LocallyConstant.coe_const, Function.const_apply] using hd b
  rw [singularTransfer_comp_chainComplexMap_eq_locallyConstantNsmul, hdegree,
    singularChainLocallyConstantNsmul_const]

/-- **The transfer formula** `p_* ∘ transfer = d • id` on singular homology, for a covering map
whose fibres all have `d` points. -/
theorem homologyMap_singularTransfer_comp_homologyMap [CategoryWithHomology C]
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C) {d : ℕ}
    (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) (n : ℕ) :
    HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map p) R n = d • 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, singularTransfer_comp_chainComplexMap hp hfin R hd]
  exact (HomologicalComplex.homologyFunctor C _ n).map_nsmul.trans
    (congrArg (d • ·) ((HomologicalComplex.homologyFunctor C _ n).map_id _))

/-- On chains from a preconnected space mapping into the base, projection after transfer
multiplies by the fibre cardinality over the image of any chosen point of that space. -/
@[reassoc]
theorem chainComplexMap_comp_singularTransfer_comp_chainComplexMap [PreconnectedSpace Y]
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) (R : C)
    (f : Y ⟶ B) (y : Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ hp.singularTransfer hfin R ≫
        SSet.chainComplexMap (TopCat.toSSet.map p) R =
      Nat.card (p ⁻¹' {f y}) • SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  rw [singularTransfer_comp_chainComplexMap_eq_locallyConstantNsmul,
    chainComplexMap_comp_singularChainLocallyConstantNsmul R f hp.degree y, degree_apply]

/-- On homology classes coming from a preconnected space, projection after transfer is
multiplication by the number of sheets over that component. This includes degree zero. -/
@[reassoc]
theorem homologyMap_comp_singularTransfer_comp_homologyMap [CategoryWithHomology C]
    [PreconnectedSpace Y] (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (R : C) (f : Y ⟶ B) (y : Y) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map f) R n ≫
        HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map p) R n =
      Nat.card (p ⁻¹' {f y}) • SSet.homologyMap (TopCat.toSSet.map f) R n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    chainComplexMap_comp_singularTransfer_comp_chainComplexMap hp hfin R f y]
  exact (HomologicalComplex.homologyFunctor C _ n).map_nsmul

/-- **Componentwise transfer formula.** The restriction to the homology coming from a
connected component of the base uses the degree of that component, with no global degree
hypothesis. -/
@[reassoc]
theorem homologyMap_connectedComponent_comp_singularTransfer_comp_homologyMap
    [CategoryWithHomology C] (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (R : C) (b : B) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (connectedComponent b) ⟶ B))
        R n ≫ HomologicalComplex.homologyMap (hp.singularTransfer hfin R) n ≫
        SSet.homologyMap (TopCat.toSSet.map p) R n =
      Nat.card (p ⁻¹' {b}) • SSet.homologyMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of (connectedComponent b) ⟶ B))
        R n := by
  let := Subtype.preconnectedSpace (isPreconnected_connectedComponent (x := b))
  exact hp.homologyMap_comp_singularTransfer_comp_homologyMap hfin R
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    ⟨b, mem_connectedComponent⟩ n

end IsCoveringMap
