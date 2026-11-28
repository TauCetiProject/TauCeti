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
`r : M → N` be smooth maps together with a smooth homotopy `Φ : ℝ × M → M` from `j ∘ r` to `id_M`
(`Φ (0, x) = j (r x)` and `Φ (1, x) = x`). Whenever the inclusion of smooth singular chains into
continuous singular chains is a chain homotopy equivalence on `N` with homotopy inverse `s`, the
composite `r_* ≫ s ≫ j_*` — applying `r_*` on continuous singular chains, `s` on `N`, and `j_*` on
smooth singular chains — is a chain homotopy inverse to the inclusion of smooth singular chains on
`M` (`ContMDiff.smoothSingularChainHomotopyEquivOfRetract`).

Both inverse identities follow from naturality of pushforwards with the subcomplex inclusion, the
smooth prism operator (`ContMDiff.smoothSingularChainHomotopyOfRealProd`) of the jointly smooth
map `Φ` on smooth chains, and the topological prism operator (`TopCat.Homotopy.toSSet`) of the
restriction of `Φ` to `[0, 1] × M` (`TauCeti.topCatHomotopyOfContMDiff`) on continuous singular
chains. No homotopy between `r ∘ j` and `id_N` is used: `N` need only dominate `M` smoothly, as
happens when `N` is the boundaryless interior of a manifold with boundary or corners deformed inward
along an inward semiflow.

Because any two homotopy inverses of the same chain map are chain homotopic
(`HomotopyEquiv.homotopyInv`) and induce the same homology isomorphism
(`HomotopyEquiv.toHomologyIso_eq_of_homotopy`), the transferred homotopy inverse is independent up
to chain homotopy of the auxiliary manifold `N`, the maps `j` and `r`, the homotopy `Φ`, and the
inverse `s`, and the resulting homology isomorphism is canonical.

Dual cochain transfer is in `TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Cochain`, concrete
inward-domination transfer on the closed half-line `[0, ∞)` is in
`TauCeti.Geometry.Manifold.SmoothSingular.Transfer.HalfLine`, and the obstruction showing that
without `j ∘ r ~ id_M` the transferred-inverse formula `r_* ≫ s ≫ j_*` can fail (witnessed for
`N = PUnit` on `Circle`) is in `TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Obstruction`.

## Main definitions and results

* `ContMDiff.smoothSingularChainHomotopyEquivOfRetract`: transfer of a smooth-to-singular chain
  homotopy equivalence from `N` to `M` along `j : N → M`, `r : M → N`, and `Φ : ℝ × M → M` from
  `j ∘ r` to `id_M`.

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
    (hΦ₀ : ∀ x, Φ (0, x) = j (r x)) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨r, hr.continuous⟩)) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨j, hj.continuous⟩)) R) (𝟙 _) :=
  (Homotopy.ofEq (by
    rw [← Functor.map_comp, ← Functor.map_comp, ← TopCat.ofHom_comp])).trans
    (((topCatHomotopyOfContMDiff (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀
      hΦ₁).toSSet.chainComplexMap R).trans
      (Homotopy.ofEq (by
        -- `topCatHomotopyOfContMDiff` bundles `id` with `(contMDiff_id ...).continuous`, which
        -- equals `ContinuousMap.id M` by extensionality.
        have hid : (⟨id, (contMDiff_id (I := I) (n := ∞)).continuous⟩ : C(M, M)) =
            ContinuousMap.id M :=
          ContinuousMap.ext fun _ ↦ by
            simp only [ContinuousMap.coe_mk, id_eq, ContinuousMap.id_apply]
        rw [hid, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
        exact ((SSet.chainComplexFunctor C).obj R).map_id _)))

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
  eN.ofHomotopyRetractOfComm (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (homotopySmoothDomination hj hr hΦ hΦ₀ hΦ₁ R)
    (homotopyTopDomination hj hr hΦ hΦ₀ hΦ₁ R)
    (by rw [heN, chainComplexMap_smoothSingularSubcomplexMap_ι hj R])
    (by rw [heN, (chainComplexMap_smoothSingularSubcomplexMap_ι hr R).symm])

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
  HomotopyEquiv.ofHomotopyRetractOfComm_hom _ _ _ _ _ _

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
  HomotopyEquiv.ofHomotopyRetractOfComm_inv _ _ _ _ _ _

end ContMDiff

end Retract
