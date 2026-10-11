/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.OverClass
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Naturality
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Manifold

/-!
# Products and the algebraic–analytic toric comparison

The scheme of a product fan is the fibre product of the factor schemes over `Spec ℂ`, with the
toric maps of the two fan projections as its projections. Hence a complex point of the
product-fan scheme, a morphism from `Spec ℂ` over `Spec ℂ`, is the same as a pair of complex
points of the factor schemes. This holds for all finite fans and is natural for products of fan
morphisms.

For regular fans, the algebraic–analytic comparison carries this identification to the
canonical product comparison of analytic realizations, whose forward map also consists of the
two projection maps. Consequently, the identification is a homeomorphism for the topologies glued
from the affine charts and a biholomorphism for the complex structures pulled back from the
analytic realizations.

## Main declarations

* `TauCeti.Toric.Fan.algebraicComplexPointProdEquiv`: complex points of the product-fan scheme
  are pairs of complex points of the factor schemes.
* `TauCeti.Toric.Fan.algebraicComplexPointProdEquiv_naturality`: compatibility with products of
  fan morphisms.
* `TauCeti.Toric.Fan.analyticProdHomeomorph_algebraicAnalyticEquiv`: the algebraic–analytic
  comparison commutes with the product identifications.
* `TauCeti.Toric.Fan.algebraicComplexPointProdHomeomorph` and
  `TauCeti.Toric.Fan.algebraicComplexPointProdDiffeomorph`: for regular fans, the product
  identification of complex points is a homeomorphism and a biholomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  (Φ : Fan i) (Ψ : Fan i')

/-- The complex points of the scheme of a product fan are the pairs of complex points of the
factor schemes: a point is sent to its images under the toric maps of the two fan projections.
This is the universal property of the scheme of `Φ.prod Ψ` as a fibre product over `Spec ℂ`. -/
noncomputable def algebraicComplexPointProdEquiv :
    (Φ.prod Ψ).AlgebraicComplexPoint ≃ Φ.AlgebraicComplexPoint × Ψ.AlgebraicComplexPoint :=
  (Φ.isPullback_fst_snd_algebraicMap Ψ).homIsOverEquiv (Spec (.of ℂ))

/-- The product identification of complex points applies the toric maps of the two fan
projections. -/
@[simp]
theorem algebraicComplexPointProdEquiv_apply (p : (Φ.prod Ψ).AlgebraicComplexPoint) :
    Φ.algebraicComplexPointProdEquiv Ψ p =
      ((FanHom.fst Φ Ψ).algebraicComplexPointMap p,
        (FanHom.snd Φ Ψ).algebraicComplexPointMap p) :=
  Prod.ext
    (Subtype.ext ((IsPullback.coe_homIsOverEquiv_apply_fst
      (Φ.isPullback_fst_snd_algebraicMap Ψ) p).trans
        (FanHom.coe_algebraicComplexPointMap _ p).symm))
    (Subtype.ext ((IsPullback.coe_homIsOverEquiv_apply_snd
      (Φ.isPullback_fst_snd_algebraicMap Ψ) p).trans
        (FanHom.coe_algebraicComplexPointMap _ p).symm))

/-- The first fan projection sends the complex point with given coordinates to its first
coordinate. -/
@[simp]
theorem fst_algebraicComplexPointMap_algebraicComplexPointProdEquiv_symm
    (q : Φ.AlgebraicComplexPoint × Ψ.AlgebraicComplexPoint) :
    (FanHom.fst Φ Ψ).algebraicComplexPointMap ((Φ.algebraicComplexPointProdEquiv Ψ).symm q) =
      q.1 := by
  have h := (Φ.algebraicComplexPointProdEquiv Ψ).apply_symm_apply q
  rw [algebraicComplexPointProdEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The second fan projection sends the complex point with given coordinates to its second
coordinate. -/
@[simp]
theorem snd_algebraicComplexPointMap_algebraicComplexPointProdEquiv_symm
    (q : Φ.AlgebraicComplexPoint × Ψ.AlgebraicComplexPoint) :
    (FanHom.snd Φ Ψ).algebraicComplexPointMap ((Φ.algebraicComplexPointProdEquiv Ψ).symm q) =
      q.2 := by
  have h := (Φ.algebraicComplexPointProdEquiv Ψ).apply_symm_apply q
  rw [algebraicComplexPointProdEquiv_apply] at h
  exact congrArg Prod.snd h

/-- The product identification is continuous for the topologies glued from the affine charts,
for all finite fans. -/
@[fun_prop]
theorem continuous_algebraicComplexPointProdEquiv :
    Continuous (Φ.algebraicComplexPointProdEquiv Ψ) := by
  simp only [funext (Φ.algebraicComplexPointProdEquiv_apply Ψ)]
  fun_prop

section Naturality

variable {N₀ N₁ N₂ V₀ V₁ V₂ : Type} [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂] [Module ℝ V₀] [Module ℝ V₁]
  [Module ℝ V₂] {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {i₂ : N₂ →+ V₂} {Ω : Fan i₀} {Φ₁ : Fan i₁}
  {Ψ₁ : Fan i₂}

/-- A fan morphism into a product fan acts on complex points by the pair of its components. -/
theorem algebraicComplexPointProdEquiv_algebraicComplexPointMap_prod (f : FanHom Ω Φ)
    (g : FanHom Ω Ψ) (p : Ω.AlgebraicComplexPoint) :
    Φ.algebraicComplexPointProdEquiv Ψ ((f.prod g).algebraicComplexPointMap p) =
      (f.algebraicComplexPointMap p, g.algebraicComplexPointMap p) := by
  simp only [algebraicComplexPointProdEquiv_apply, ← FanHom.algebraicComplexPointMap_comp,
    FanHom.fst_comp_prod, FanHom.snd_comp_prod]

/-- Under the product identification of complex points, a componentwise product of fan
morphisms acts as the product of the corresponding maps of complex points. -/
theorem algebraicComplexPointProdEquiv_naturality (f : FanHom Φ Φ₁) (g : FanHom Ψ Ψ₁)
    (p : (Φ.prod Ψ).AlgebraicComplexPoint) :
    Φ₁.algebraicComplexPointProdEquiv Ψ₁ ((f.prodMap g).algebraicComplexPointMap p) =
      Prod.map f.algebraicComplexPointMap g.algebraicComplexPointMap
        (Φ.algebraicComplexPointProdEquiv Ψ p) := by
  simp only [algebraicComplexPointProdEquiv_apply, Prod.map_apply,
    ← FanHom.algebraicComplexPointMap_comp, FanHom.fst_comp_prodMap, FanHom.snd_comp_prodMap]

end Naturality

/-! ### Compatibility with the analytic product comparison -/

variable {Φ Ψ} (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The algebraic–analytic comparison commutes with the product identifications: comparing a
complex point of the product-fan scheme and then splitting it in the analytic realization gives
the comparisons of its two coordinates. -/
theorem analyticProdHomeomorph_algebraicAnalyticEquiv (p : (Φ.prod Ψ).AlgebraicComplexPoint) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ (algebraicAnalyticEquiv (IsRegular.prod Φ Ψ hΦ hΨ) p) =
      Prod.map (algebraicAnalyticEquiv hΦ) (algebraicAnalyticEquiv hΨ)
        (Φ.algebraicComplexPointProdEquiv Ψ p) := by
  simp only [coe_analyticProdHomeomorph, analyticProdComparison_apply,
    algebraicComplexPointProdEquiv_apply, Prod.map_apply,
    FanHom.algebraicAnalyticEquiv_naturality _ (IsRegular.prod Φ Ψ hΦ hΨ)]

/-- The inverse product identification of complex points is the inverse analytic product
comparison, read through the algebraic–analytic comparisons. -/
theorem algebraicComplexPointProdEquiv_symm_eq :
    ⇑(Φ.algebraicComplexPointProdEquiv Ψ).symm =
      (algebraicAnalyticEquiv (IsRegular.prod Φ Ψ hΦ hΨ)).symm ∘
        (Φ.analyticProdHomeomorph Ψ hΦ hΨ).symm ∘
          Prod.map (algebraicAnalyticEquiv hΦ) (algebraicAnalyticEquiv hΨ) := by
  funext q
  rw [Equiv.symm_apply_eq]
  apply (Equiv.prodCongr (algebraicAnalyticEquiv hΦ) (algebraicAnalyticEquiv hΨ)).injective
  simp only [Equiv.prodCongr_apply, Function.comp_apply,
    ← analyticProdHomeomorph_algebraicAnalyticEquiv, Equiv.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- For regular fans, the product identification of complex points is a homeomorphism for the
topologies glued from the affine charts. -/
noncomputable def algebraicComplexPointProdHomeomorph :
    (Φ.prod Ψ).AlgebraicComplexPoint ≃ₜ Φ.AlgebraicComplexPoint × Ψ.AlgebraicComplexPoint where
  toEquiv := Φ.algebraicComplexPointProdEquiv Ψ
  continuous_toFun := Φ.continuous_algebraicComplexPointProdEquiv Ψ
  continuous_invFun := by
    simp only [Equiv.invFun_as_coe, algebraicComplexPointProdEquiv_symm_eq hΦ hΨ,
      ← coe_algebraicAnalyticHomeomorph_symm, ← coe_algebraicAnalyticHomeomorph]
    fun_prop

/-- The product homeomorphism of complex points is the product identification. -/
@[simp]
theorem coe_algebraicComplexPointProdHomeomorph :
    ⇑(algebraicComplexPointProdHomeomorph hΦ hΨ) = Φ.algebraicComplexPointProdEquiv Ψ :=
  (rfl)

/-- The inverse product homeomorphism of complex points is the inverse product
identification. -/
@[simp]
theorem coe_algebraicComplexPointProdHomeomorph_symm :
    ⇑(algebraicComplexPointProdHomeomorph hΦ hΨ).symm =
      (Φ.algebraicComplexPointProdEquiv Ψ).symm :=
  (rfl)

/-- For regular fans, the product identification of complex points is a biholomorphism for the
complex structures pulled back from the analytic realizations, at every smoothness order. -/
noncomputable def algebraicComplexPointProdDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := algebraicComplexPointChartedSpace hΦ
    letI := algebraicComplexPointChartedSpace hΨ
    (Φ.prod Ψ).AlgebraicComplexPoint ≃ₘ^n⟮𝓘(ℂ, Fin (Module.finrank ℤ (N × N')) → ℂ),
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ).prod 𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ)⟯
      Φ.AlgebraicComplexPoint × Ψ.AlgebraicComplexPoint :=
  letI := Φ.analyticChartedSpace hΦ
  letI := Ψ.analyticChartedSpace hΨ
  letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  letI := algebraicComplexPointChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  letI := algebraicComplexPointChartedSpace hΦ
  letI := algebraicComplexPointChartedSpace hΨ
  ((algebraicAnalyticDiffeomorph (IsRegular.prod Φ Ψ hΦ hΨ) n).trans
    (Φ.analyticProdDiffeomorph Ψ hΦ hΨ n)).trans
      ((algebraicAnalyticDiffeomorph hΦ n).prodCongr (algebraicAnalyticDiffeomorph hΨ n)).symm

/-- The product biholomorphism of complex points is the product identification. -/
@[simp]
theorem coe_algebraicComplexPointProdDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := algebraicComplexPointChartedSpace hΦ
    letI := algebraicComplexPointChartedSpace hΨ
    ⇑(algebraicComplexPointProdDiffeomorph hΦ hΨ n) = Φ.algebraicComplexPointProdEquiv Ψ := by
  let := algebraicComplexPointChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  let := algebraicComplexPointChartedSpace hΦ
  let := algebraicComplexPointChartedSpace hΨ
  funext p
  simp only [algebraicComplexPointProdDiffeomorph, Diffeomorph.coe_trans,
    Diffeomorph.prodCongr_symm, Diffeomorph.coe_prodCongr,
    coe_algebraicAnalyticDiffeomorph_symm, coe_algebraicAnalyticDiffeomorph,
    coe_analyticProdDiffeomorph, Function.comp_apply,
    analyticProdHomeomorph_algebraicAnalyticEquiv, Prod.map_map, Equiv.symm_comp_self,
    Prod.map_id, id_eq]

end TauCeti.Toric.Fan
