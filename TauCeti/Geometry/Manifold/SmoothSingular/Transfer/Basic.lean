/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy

import TauCeti.Algebra.Homology.Homotopy
import TauCeti.Geometry.Manifold.ContMDiff.Homotopy

/-!
# Transfer of smooth singular chain homotopy equivalences

Let `M` and `N` be manifolds (possibly with boundary or corners) and let `j : N → M` and
`r : M → N` be smooth maps. Given a smooth-chain homotopy `r_* ≫ j_* ~ id` and a topological
homotopy `j ∘ r ~ id_M`, any chain homotopy equivalence `eN` from the smooth singular chains of `N`
to the continuous singular chains of `N` whose forward map is the subcomplex inclusion transfers to
a chain homotopy equivalence on `M` with forward map the subcomplex inclusion and inverse
`r_* ≫ eN.inv ≫ j_*` (`ContMDiff.smoothSingularChainHomotopyEquivOfHomotopyRetract`).

When `j ∘ r` is joined to `id_M` by a jointly smooth map `Φ : ℝ × M → M` with `Φ (0, x) = j (r x)`
and `Φ (1, x) = x`, the smooth prism operator (`ContMDiff.smoothSingularChainHomotopyOfRealProd`)
and the topological prism operator (`TauCeti.topCatHomotopyOfContMDiff`) supply both homotopy
witnesses, yielding `ContMDiff.smoothSingularChainHomotopyEquivOfRetract`. No homotopy between
`r ∘ j` and `id_N` is used: `N` need only dominate `M`, as happens when `N` is the boundaryless
interior of a manifold with boundary or corners deformed inward along an inward semiflow.

Because any two homotopy inverses of the same chain map are chain homotopic
(`HomotopyEquiv.homotopyInv`) and induce the same homology isomorphism
(`HomotopyEquiv.toHomologyIso_eq_of_homotopy`), the transferred homotopy inverse is independent up
to chain homotopy of the auxiliary manifold `N`, the maps `j` and `r`, the homotopies, and the
inverse `eN.inv`, and the resulting homology isomorphism is canonical.

Dual cochain transfer is in `TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Cochain`, concrete
inward-domination transfer on the closed half-line `[0, ∞)` is in
`TauCeti.Geometry.Manifold.SmoothSingular.Transfer.HalfLine`, and the obstruction showing that
without `j ∘ r ~ id_M` the transferred-inverse formula `r_* ≫ s ≫ j_*` can fail (witnessed for
`N = PUnit` on `Circle`) is in `TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Obstruction`.

## Main definitions and results

* `ContMDiff.smoothSingularChainHomotopyEquivOfHomotopyRetract`: core transfer of a
  smooth-to-singular chain homotopy equivalence from `N` to `M` along `j : N → M` and `r : M → N`
  from independent smooth-chain and topological domination homotopies.
* `ContMDiff.smoothSingularChainHomotopyEquivOfRetract`: specialization when the domination homotopy
  is given by a jointly smooth map `Φ : ℝ × M → M` from `j ∘ r` to `id_M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 9, Theorems 9.24–9.26 (inward
  flowouts and homotopy equivalence with the interior), and Chapter 18, Theorem 18.7 (smooth
  singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Set Simplicial Topology
open scoped Manifold ContDiff

universe u

section Retract

open TauCeti

namespace ContMDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- **Core transfer of smooth-chain homotopy equivalences along a domination.** Given smooth maps
`j : N → M` and `r : M → N`, a smooth-chain homotopy `hsm : r_* ≫ j_* ~ 𝟙`, and a topological
homotopy `htop : j ∘ r ~ 𝟙`, any chain homotopy equivalence `eN` from smooth to continuous singular
chains on `N` whose forward map is the subcomplex inclusion transfers to `M` with forward map the
subcomplex inclusion and inverse `r_* ≫ eN.inv ≫ j_*`. -/
def smoothSingularChainHomotopyEquivOfHomotopyRetract {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) (R : C)
    (hsm : Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplexMap r hr) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R) (𝟙 _))
    (htop : TopCat.Homotopy
      (TopCat.ofHom ⟨r, hr.continuous⟩ ≫ TopCat.ofHom ⟨j, hj.continuous⟩) (𝟙 (TopCat.of M)))
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  eN.ofHomotopyRetract (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    hsm
    ((Homotopy.ofEq (by rw [← Functor.map_comp, ← Functor.map_comp])).trans
      ((htop.toSSet.chainComplexMap R).trans
        (Homotopy.ofEq (by
          rw [TopCat.toSSet.map_id]
          exact ((SSet.chainComplexFunctor C).obj R).map_id _))))
    (.ofEq (by rw [heN, chainComplexMap_smoothSingularSubcomplexMap_ι hj R]))
    (.ofEq (by rw [heN, (chainComplexMap_smoothSingularSubcomplexMap_ι hr R).symm]))

/-- The forward map of `smoothSingularChainHomotopyEquivOfHomotopyRetract` is the inclusion of
smooth singular chains into continuous singular chains on `M`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfHomotopyRetract_hom {j : N → M}
    (hj : ContMDiff J I ∞ j) {r : M → N} (hr : ContMDiff I J ∞ r) (R : C)
    (hsm : Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplexMap r hr) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R) (𝟙 _))
    (htop : TopCat.Homotopy
      (TopCat.ofHom ⟨r, hr.continuous⟩ ≫ TopCat.ofHom ⟨j, hj.continuous⟩) (𝟙 (TopCat.of M)))
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (hj.smoothSingularChainHomotopyEquivOfHomotopyRetract hr R hsm htop eN heN).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  HomotopyEquiv.ofHomotopyRetract_hom _ _ _ _ _ _

/-- The homotopy inverse of `smoothSingularChainHomotopyEquivOfHomotopyRetract` pushes continuous
singular chains of `M` forward by `r`, applies `eN.inv` on `N`, and pushes smooth singular chains
of `N` forward by `j`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfHomotopyRetract_inv {j : N → M}
    (hj : ContMDiff J I ∞ j) {r : M → N} (hr : ContMDiff I J ∞ r) (R : C)
    (hsm : Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplexMap r hr) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R) (𝟙 _))
    (htop : TopCat.Homotopy
      (TopCat.ofHom ⟨r, hr.continuous⟩ ≫ TopCat.ofHom ⟨j, hj.continuous⟩) (𝟙 (TopCat.of M)))
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (hj.smoothSingularChainHomotopyEquivOfHomotopyRetract hr R hsm htop eN heN).inv =
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨r, hr.continuous⟩)) R ≫
        eN.inv ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R :=
  HomotopyEquiv.ofHomotopyRetract_inv _ _ _ _ _ _

private def homotopySmoothDomination {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplexMap r hr) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R) (𝟙 _) :=
  (Homotopy.ofEq (by
    rw [← Functor.map_comp, ← smoothSingularSubcomplexMap_comp hj hr])).trans
    ((hΦ.smoothSingularChainHomotopyOfRealProd (f := j ∘ r) (g := id) hΦ₀ hΦ₁ R).trans
      (Homotopy.ofEq (by simp [smoothSingularSubcomplexMap_id])))

private def homotopyTopDomination {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) :
    TopCat.Homotopy
      (TopCat.ofHom ⟨r, hr.continuous⟩ ≫ TopCat.ofHom ⟨j, hj.continuous⟩) (𝟙 (TopCat.of M)) where
  toFun p := topCatHomotopyOfContMDiff (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀ hΦ₁ p
  continuous_toFun :=
    (topCatHomotopyOfContMDiff (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀ hΦ₁).continuous
  map_zero_left x := by
    simp
  map_one_left x := by
    simp [TopCat.hom_id]

/-- **Transfer of smooth-chain homotopy equivalences along a smooth domination.** Given smooth maps
`j : N → M` and `r : M → N` and a smooth homotopy `Φ : ℝ × M → M` from `j ∘ r` to `id_M`, any
chain homotopy equivalence `eN` from the smooth singular chains of `N` to the continuous singular
chains of `N` whose forward map is the subcomplex inclusion transfers to a chain homotopy
equivalence on `M` with forward map the subcomplex inclusion and inverse `r_* ≫ eN.inv ≫ j_*`.
No homotopy between `r ∘ j` and `id_N` is required. -/
def smoothSingularChainHomotopyEquivOfRetract {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  hj.smoothSingularChainHomotopyEquivOfHomotopyRetract hr R
    (homotopySmoothDomination hj hr hΦ hΦ₀ hΦ₁ R)
    (homotopyTopDomination hj hr hΦ hΦ₀ hΦ₁)
    eN heN

/-- The forward map of `smoothSingularChainHomotopyEquivOfRetract` is the inclusion of smooth
singular chains into continuous singular chains on `M`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfRetract_hom {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (hj.smoothSingularChainHomotopyEquivOfRetract hr hΦ hΦ₀ hΦ₁ R eN heN).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  smoothSingularChainHomotopyEquivOfHomotopyRetract_hom hj hr R _ _ eN heN

/-- The homotopy inverse of `smoothSingularChainHomotopyEquivOfRetract` pushes continuous singular
chains of `M` forward by `r`, applies `eN.inv` on `N`, and pushes smooth singular chains of `N`
forward by `j`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfRetract_inv {j : N → M} (hj : ContMDiff J I ∞ j)
    {r : M → N} (hr : ContMDiff I J ∞ r) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J N : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :
    (hj.smoothSingularChainHomotopyEquivOfRetract hr hΦ hΦ₀ hΦ₁ R eN heN).inv =
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨r, hr.continuous⟩)) R ≫
        eN.inv ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R :=
  smoothSingularChainHomotopyEquivOfHomotopyRetract_inv hj hr R _ _ eN heN

end ContMDiff

end Retract
