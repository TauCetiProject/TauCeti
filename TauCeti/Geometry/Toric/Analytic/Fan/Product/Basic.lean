/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.AffinePoint.Product
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Product

/-!
# Products of analytic toric realizations

The analytic realization of a product of regular fans is canonically homeomorphic to the
product of their analytic realizations. The forward map consists of the analytic maps of the
two fan projections. On every product-cone chart it restricts characters to the two lattice
factors, and its inverse multiplies their monomial values. The comparison is therefore
independent of bases and finite semigroup generating families, and also covers empty fans.

This supplies the topological product comparison for holomorphic toric maps.

## Main declarations

* `TauCeti.Toric.Fan.analyticAffineChartProdHomeomorph`: the product comparison on affine charts.
* `TauCeti.Toric.Fan.analyticProdHomeomorph`: the product comparison on realizations.
* `TauCeti.Toric.Fan.analyticProdHomeomorph_analyticAffineChartι`: its affine-chart formula.
* `TauCeti.Toric.Fan.analyticProdHomeomorph_naturality`: compatibility with toric maps.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The affine chart of a product cone is the product of the factor charts, by restriction
of characters to the lattice factors. -/
noncomputable def analyticAffineChartProdHomeomorph (σ : Φ.cones) (τ : Ψ.cones) :
    (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ) ≃ₜ
      Φ.analyticAffineChartDiagram.obj σ × Ψ.analyticAffineChartDiagram.obj τ :=
  AffineSemigroupComplexPoint.prodHomeomorph
    (dualSemigroupProdEquiv Φ.lattice Ψ.lattice σ.1 τ.1)
    ((Φ.prod Ψ).analyticChartGenerators (Φ.prodCone Ψ σ τ)).2
    (Φ.analyticChartGenerators σ).2 (Ψ.analyticChartGenerators τ).2

/-- The first affine product coordinate is the chart map induced by the first fan projection. -/
@[simp↓]
theorem analyticAffineChartProdHomeomorph_fst (σ : Φ.cones) (τ : Ψ.cones)
    (x : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ)) :
    (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).1 =
      (FanHom.fst Φ Ψ).analyticChartMap (σ := Φ.prodCone Ψ σ τ) (υ := σ)
        (by intro p hp; simpa only [FanHom.fst_realMap, LinearMap.fst_apply] using hp.1) x := by
  rw [analyticAffineChartProdHomeomorph]
  -- The chart topologies are the chosen monomial topologies, behind bundled chart wrappers.
  erw [AffineSemigroupComplexPoint.coe_prodHomeomorph, FanHom.analyticChartMap_apply]
  apply AffineSemigroupComplexPoint.ext
  intro m
  erw [AffineSemigroupComplexPoint.prodEquiv_fst_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  congr 3
  apply Subtype.ext
  ext n
  simp

/-- The second affine product coordinate is the chart map induced by the second fan projection. -/
@[simp↓]
theorem analyticAffineChartProdHomeomorph_snd (σ : Φ.cones) (τ : Ψ.cones)
    (x : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ)) :
    (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).2 =
      (FanHom.snd Φ Ψ).analyticChartMap (σ := Φ.prodCone Ψ σ τ) (υ := τ)
        (by intro p hp; simpa only [FanHom.snd_realMap, LinearMap.snd_apply] using hp.2) x := by
  rw [analyticAffineChartProdHomeomorph]
  -- As above, unwrap the bundled chart topologies and complex-point carriers.
  erw [AffineSemigroupComplexPoint.coe_prodHomeomorph, FanHom.analyticChartMap_apply]
  apply AffineSemigroupComplexPoint.ext
  intro m
  erw [AffineSemigroupComplexPoint.prodEquiv_snd_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  congr 3
  apply Subtype.ext
  ext n
  simp

/-- The affine comparison restricts characters using the canonical product splitting. -/
@[simp]
theorem coe_analyticAffineChartProdHomeomorph (σ : Φ.cones) (τ : Ψ.cones) :
    ⇑(Φ.analyticAffineChartProdHomeomorph Ψ σ τ) =
      AffineSemigroupComplexPoint.prodEquiv
        (dualSemigroupProdEquiv Φ.lattice Ψ.lattice σ.1 τ.1) := by
  rw [analyticAffineChartProdHomeomorph]
  exact AffineSemigroupComplexPoint.coe_prodHomeomorph _ _ _ _

/-- The inverse affine comparison combines the two characters by multiplying their values. -/
@[simp]
theorem coe_analyticAffineChartProdHomeomorph_symm (σ : Φ.cones) (τ : Ψ.cones) :
    ⇑(Φ.analyticAffineChartProdHomeomorph Ψ σ τ).symm =
      (AffineSemigroupComplexPoint.prodEquiv
        (dualSemigroupProdEquiv Φ.lattice Ψ.lattice σ.1 τ.1)).symm := by
  rw [analyticAffineChartProdHomeomorph]
  exact AffineSemigroupComplexPoint.coe_prodHomeomorph_symm _ _ _ _

/-- The canonical continuous product comparison, given by the analytic maps of the two
fan projections. -/
noncomputable def analyticProdComparison :
    C((Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ),
      Φ.analyticRealization hΦ × Ψ.analyticRealization hΨ) where
  toFun x := ((FanHom.fst Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΦ x,
    (FanHom.snd Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΨ x)
  continuous_toFun :=
    ((FanHom.fst Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΦ).hom.continuous.prodMk
    ((FanHom.snd Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΨ).hom.continuous

/-- The product comparison is given by the two fan projections. -/
@[simp]
theorem analyticProdComparison_apply
    (x : (Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ)) :
    Φ.analyticProdComparison Ψ hΦ hΨ x =
      ((FanHom.fst Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΦ x,
        (FanHom.snd Φ Ψ).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΨ x) := (rfl)

/-- On a product-cone chart, the comparison is the affine product homeomorphism followed
by the two factor chart inclusions. -/
theorem analyticProdComparison_analyticAffineChartι (σ : Φ.cones) (τ : Ψ.cones)
    (x : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ)) :
    Φ.analyticProdComparison Ψ hΦ hΨ
        ((Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) x) =
      (Φ.analyticAffineChartι hΦ σ (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).1,
        Ψ.analyticAffineChartι hΨ τ (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).2) := by
  simp only [analyticProdComparison_apply]
  apply Prod.ext
  · erw [(FanHom.fst Φ Ψ).analyticMap_analyticAffineChartι_of_mapsTo
      (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΦ (σ := Φ.prodCone Ψ σ τ) (υ := σ)
        (by intro p hp; simpa only [FanHom.fst_realMap, LinearMap.fst_apply] using hp.1),
      analyticAffineChartProdHomeomorph_fst]
  · erw [(FanHom.snd Φ Ψ).analyticMap_analyticAffineChartι_of_mapsTo
      (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΨ (σ := Φ.prodCone Ψ σ τ) (υ := τ)
        (by intro p hp; simpa only [FanHom.snd_realMap, LinearMap.snd_apply] using hp.2),
      analyticAffineChartProdHomeomorph_snd]

private theorem analyticAffineChartProdHomeomorph_map {σ σ' : Φ.cones} {τ τ' : Ψ.cones}
    (h : Φ.prodCone Ψ σ τ ⟶ Φ.prodCone Ψ σ' τ') (hσ : σ ⟶ σ') (hτ : τ ⟶ τ')
    (x : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ)) :
    Φ.analyticAffineChartProdHomeomorph Ψ σ' τ'
        ((Φ.prod Ψ).analyticAffineChartDiagram.map h x) =
      Prod.map (Φ.analyticAffineChartDiagram.map hσ) (Ψ.analyticAffineChartDiagram.map hτ)
        (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x) := by
  apply Prod.ext
  -- The projection formulas unwrap the bundled chart carriers before composing chart maps.
  · erw [Prod.map_fst, analyticAffineChartProdHomeomorph_fst,
      analyticAffineChartProdHomeomorph_fst,
      ← TopCat.comp_app, FanHom.map_comp_analyticChartMap,
      ← TopCat.comp_app, FanHom.analyticChartMap_comp_map]
  · erw [Prod.map_snd, analyticAffineChartProdHomeomorph_snd,
      analyticAffineChartProdHomeomorph_snd,
      ← TopCat.comp_app, FanHom.map_comp_analyticChartMap,
      ← TopCat.comp_app, FanHom.analyticChartMap_comp_map]

private theorem injective_analyticProdComparison :
    Function.Injective (Φ.analyticProdComparison Ψ hΦ hΨ) := by
  intro x y h
  obtain ⟨ξ, a, rfl⟩ := (Φ.prod Ψ).exists_analyticAffineChartι_apply_eq
    (Fan.IsRegular.prod Φ Ψ hΦ hΨ) x
  obtain ⟨ζ, b, rfl⟩ := (Φ.prod Ψ).exists_analyticAffineChartι_apply_eq
    (Fan.IsRegular.prod Φ Ψ hΦ hΨ) y
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
  obtain ⟨σ', τ', rfl⟩ := Φ.exists_prodCone_eq Ψ ζ
  rw [analyticProdComparison_analyticAffineChartι,
    analyticProdComparison_analyticAffineChartι] at h
  obtain ⟨c, hc, hc'⟩ := (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ _ _).mp
    (congrArg Prod.fst h)
  obtain ⟨d, hd, hd'⟩ := (Ψ.analyticAffineChartι_eq_analyticAffineChartι_iff hΨ _ _).mp
    (congrArg Prod.snd h)
  rw [analyticOverlapLeft_def] at hc hd
  rw [analyticOverlapRight_def] at hc' hd'
  let z := (Φ.analyticAffineChartProdHomeomorph Ψ (σ ⊓ σ') (τ ⊓ τ')).symm (c, d)
  -- Use the common face chart directly, avoiding transport of points across cone equalities.
  have key {υ : Φ.cones} {ω : Ψ.cones} (hσ : σ ⊓ σ' ⟶ υ) (hτ : τ ⊓ τ' ⟶ ω)
      (p : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ υ ω))
      (hp : Prod.map (Φ.analyticAffineChartDiagram.map hσ)
        (Ψ.analyticAffineChartDiagram.map hτ) (c, d) =
          Φ.analyticAffineChartProdHomeomorph Ψ υ ω p) :
      (Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ)
        (Φ.prodCone Ψ υ ω) p =
      (Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ)
        (Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ')) z := by
    let f : Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ') ⟶ Φ.prodCone Ψ υ ω :=
      homOfLE (by intro q hq; exact ⟨leOfHom hσ hq.1, leOfHom hτ hq.2⟩)
    have hz : (Φ.prod Ψ).analyticAffineChartDiagram.map f z = p := by
      apply (Φ.analyticAffineChartProdHomeomorph Ψ υ ω).injective
      rw [analyticAffineChartProdHomeomorph_map Φ Ψ f hσ hτ,
        Homeomorph.apply_symm_apply]
      exact hp
    rw [← hz]
    exact ConcreteCategory.congr_hom
      ((Φ.prod Ψ).analyticAffineChartDiagram_map_comp_analyticAffineChartι
        (Fan.IsRegular.prod Φ Ψ hΦ hΨ) f) z
  exact (key (homOfLE inf_le_left) (homOfLE inf_le_left) a (Prod.ext hc hd)).trans
    (key (homOfLE inf_le_right) (homOfLE inf_le_right) b (Prod.ext hc' hd')).symm

private theorem surjective_analyticProdComparison :
    Function.Surjective (Φ.analyticProdComparison Ψ hΦ hΨ) := by
  rintro ⟨x, y⟩
  obtain ⟨σ, a, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  obtain ⟨τ, b, rfl⟩ := Ψ.exists_analyticAffineChartι_apply_eq hΨ y
  refine ⟨(Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ)
    ((Φ.analyticAffineChartProdHomeomorph Ψ σ τ).symm (a, b)), ?_⟩
  rw [analyticProdComparison_analyticAffineChartι, Homeomorph.apply_symm_apply]

private theorem isOpenMap_analyticProdComparison :
    IsOpenMap (Φ.analyticProdComparison Ψ hΦ hΨ) := by
  let q : (Σ ξ : (Φ.prod Ψ).cones, (Φ.prod Ψ).analyticAffineChartDiagram.obj ξ) →
      (Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ) :=
    fun p ↦ (Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) p.1 p.2
  have hq : Continuous q := continuous_sigma fun ξ ↦
    ((Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ξ).hom.continuous
  have hsurj : Function.Surjective q := fun x ↦ by
    obtain ⟨ξ, y, rfl⟩ :=
      (Φ.prod Ψ).exists_analyticAffineChartι_apply_eq (Fan.IsRegular.prod Φ Ψ hΦ hΨ) x
    exact ⟨⟨ξ, y⟩, rfl⟩
  apply IsOpenMap.of_comp hq hsurj
  apply isOpenMap_sigma.2
  intro ξ
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
  have hchart : (fun x ↦ Φ.analyticProdComparison Ψ hΦ hΨ
      ((Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) x)) =
      Prod.map (Φ.analyticAffineChartι hΦ σ) (Ψ.analyticAffineChartι hΨ τ) ∘
        Φ.analyticAffineChartProdHomeomorph Ψ σ τ :=
    funext (Φ.analyticProdComparison_analyticAffineChartι Ψ hΦ hΨ σ τ)
  simp only [Function.comp_apply, q]
  rw [hchart]
  exact ((Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).isOpenMap.prodMap
    (Ψ.isOpenEmbedding_analyticAffineChartι hΨ τ).isOpenMap).comp
      (Φ.analyticAffineChartProdHomeomorph Ψ σ τ).isOpenMap

/-- The realization of a product of regular fans is canonically the product of the
realizations, including when either fan is empty. -/
noncomputable def analyticProdHomeomorph :
    (Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ≃ₜ
      Φ.analyticRealization hΦ × Ψ.analyticRealization hΨ :=
  (Equiv.ofBijective (Φ.analyticProdComparison Ψ hΦ hΨ)
    ⟨Φ.injective_analyticProdComparison Ψ hΦ hΨ,
      Φ.surjective_analyticProdComparison Ψ hΦ hΨ⟩).toHomeomorphOfContinuousOpen
        (Φ.analyticProdComparison Ψ hΦ hΨ).continuous
        (Φ.isOpenMap_analyticProdComparison Ψ hΦ hΨ)

@[simp]
theorem coe_analyticProdHomeomorph :
    ⇑(Φ.analyticProdHomeomorph Ψ hΦ hΨ) = Φ.analyticProdComparison Ψ hΦ hΨ := (rfl)

/-- The global product homeomorphism is the affine product homeomorphism on each chart. -/
@[simp]
theorem analyticProdHomeomorph_analyticAffineChartι (σ : Φ.cones) (τ : Ψ.cones)
    (x : (Φ.prod Ψ).analyticAffineChartDiagram.obj (Φ.prodCone Ψ σ τ)) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ
        ((Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) x) =
      (Φ.analyticAffineChartι hΦ σ (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).1,
        Ψ.analyticAffineChartι hΨ τ (Φ.analyticAffineChartProdHomeomorph Ψ σ τ x).2) :=
  Φ.analyticProdComparison_analyticAffineChartι Ψ hΦ hΨ σ τ x

/-- The inverse product comparison is multiplication of monomial values on affine charts. -/
@[simp]
theorem analyticProdHomeomorph_symm_analyticAffineChartι (σ : Φ.cones) (τ : Ψ.cones)
    (a : Φ.analyticAffineChartDiagram.obj σ) (b : Ψ.analyticAffineChartDiagram.obj τ) :
    (Φ.analyticProdHomeomorph Ψ hΦ hΨ).symm
        (Φ.analyticAffineChartι hΦ σ a, Ψ.analyticAffineChartι hΨ τ b) =
      (Φ.prod Ψ).analyticAffineChartι (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ)
        ((Φ.analyticAffineChartProdHomeomorph Ψ σ τ).symm (a, b)) := by
  apply (Φ.analyticProdHomeomorph Ψ hΦ hΨ).injective
  rw [Homeomorph.apply_symm_apply, analyticProdHomeomorph_analyticAffineChartι,
    Homeomorph.apply_symm_apply]

section Naturality

variable {N₁ N₂ V₁ V₂ : Type u} [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₁] [AddCommGroup V₂] [Module ℝ V₁] [Module ℝ V₂]
  {i₁ : N₁ →+ V₁} {i₂ : N₂ →+ V₂} {Φ₁ : Fan i₁} {Ψ₁ : Fan i₂}

/-- Under the product comparison, a componentwise product of fan morphisms acts as the
product of the corresponding analytic maps.

For `simp only`, supply the source regularity proofs explicitly:
`simp only [analyticProdHomeomorph_naturality Φ Ψ hΦ hΨ]`. -/
theorem analyticProdHomeomorph_naturality (f : FanHom Φ Φ₁) (g : FanHom Ψ Ψ₁)
    (hΦ₁ : Φ₁.IsRegular) (hΨ₁ : Ψ₁.IsRegular)
    (x : (Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ)) :
    Φ₁.analyticProdHomeomorph Ψ₁ hΦ₁ hΨ₁
        ((f.prodMap g).analyticMap (Fan.IsRegular.prod Φ Ψ hΦ hΨ)
          (Fan.IsRegular.prod Φ₁ Ψ₁ hΦ₁ hΨ₁) x) =
      Prod.map (f.analyticMap hΦ hΦ₁) (g.analyticMap hΨ hΨ₁)
        (Φ.analyticProdHomeomorph Ψ hΦ hΨ x) := by
  simp only [coe_analyticProdHomeomorph, analyticProdComparison_apply, Prod.map_apply]
  apply Prod.ext
  · have h := FanHom.analyticMap_comp (f.prodMap g)
      (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Fan.IsRegular.prod Φ₁ Ψ₁ hΦ₁ hΨ₁)
      (FanHom.fst Φ₁ Ψ₁) hΦ₁
    rw [FanHom.fst_comp_prodMap,
      FanHom.analyticMap_comp (FanHom.fst Φ Ψ)
        (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΦ f hΦ₁] at h
    exact (ConcreteCategory.congr_hom h x).symm
  · have h := FanHom.analyticMap_comp (f.prodMap g)
      (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Fan.IsRegular.prod Φ₁ Ψ₁ hΦ₁ hΨ₁)
      (FanHom.snd Φ₁ Ψ₁) hΨ₁
    rw [FanHom.snd_comp_prodMap,
      FanHom.analyticMap_comp (FanHom.snd Φ Ψ)
        (Fan.IsRegular.prod Φ Ψ hΦ hΨ) hΨ g hΨ₁] at h
    exact (ConcreteCategory.congr_hom h x).symm

end Naturality

end TauCeti.Toric.Fan
