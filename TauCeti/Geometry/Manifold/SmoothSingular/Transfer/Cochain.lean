/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Basic

/-!
# Dual cochain transfer along a smooth domination

Applying the contravariant linear Yoneda functor `Hom(-, A)` to the transferred smooth-to-singular
chain homotopy equivalence `ContMDiff.smoothSingularChainHomotopyEquivOfRetract` produces a cochain
homotopy equivalence from continuous singular cochains to smooth singular cochains on `M`
(`TauCeti.smoothSingularCochainHomotopyEquivOfRetract`), whose forward map restricts cochains to
smooth simplices and whose inverse composes restriction along `j`, the dual inverse on `N`, and
pullback along `r`.

## Main definitions and results

* `TauCeti.smoothSingularCochainHomotopyEquivOfRetract`: dual cochain homotopy equivalence
  transferred along a smooth domination.
* `TauCeti.smoothSingularCochainHomotopyEquivOfRetract_hom`,
  `TauCeti.smoothSingularCochainHomotopyEquivOfRetract_inv`: identification of the forward and
  inverse cochain maps.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type*} [Category* C] [HasCoproducts.{u} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (A : C)

/-- **Dual transfer on cochains.** Applying `Hom(-, A)` to
`ContMDiff.smoothSingularChainHomotopyEquivOfRetract` produces a cochain homotopy equivalence from
the continuous singular cochain complex of `M` to the smooth singular cochain complex of `M`, whose
forward map restricts cochains to smooth simplices and whose inverse composes restriction along `j`,
the dual inverse on `N`, and pullback along `r`. -/
def smoothSingularCochainHomotopyEquivOfRetract {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    HomotopyEquiv ((TopCat.of M).singularCochainComplex R k A)
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k A) :=
  (hj.smoothSingularChainHomotopyEquivOfRetract hr hΦ hΦ₀ hΦ₁ R eN heN).linearYonedaFunctorMap
    k A

/-- The forward map of `smoothSingularCochainHomotopyEquivOfRetract` is restriction along the
inclusion of smooth singular simplices. -/
@[simp]
theorem smoothSingularCochainHomotopyEquivOfRetract_hom {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (smoothSingularCochainHomotopyEquivOfRetract R k A hj hr hΦ hΦ₀ hΦ₁ eN heN).hom =
      SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι := by
  rw [smoothSingularCochainHomotopyEquivOfRetract, HomotopyEquiv.linearYonedaFunctorMap_hom,
    ContMDiff.smoothSingularChainHomotopyEquivOfRetract_hom]

/-- The inverse of `smoothSingularCochainHomotopyEquivOfRetract` pulls smooth cochains of `M` back
along `j`, applies the dual inverse on `N`, and pulls continuous cochains of `N` back along `r`. -/
@[simp]
theorem smoothSingularCochainHomotopyEquivOfRetract_inv {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (smoothSingularCochainHomotopyEquivOfRetract R k A hj hr hΦ hΦ₀ hΦ₁ eN heN).inv =
      SSet.cochainComplexMap (smoothSingularSubcomplexMap j hj) ≫
        (ChainComplex.linearYonedaFunctor k A).map eN.inv.op ≫
          TopCat.singularCochainComplexMap (TopCat.ofHom ⟨r, hr.continuous⟩) := by
  simp [smoothSingularCochainHomotopyEquivOfRetract, TopCat.singularCochainComplexMap,
    SSet.cochainComplexMap]

end TauCeti
