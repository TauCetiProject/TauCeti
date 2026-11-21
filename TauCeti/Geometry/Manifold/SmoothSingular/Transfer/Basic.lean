/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
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
smooth prism operator (`ContMDiff.smoothSingularChainHomotopy`) of the jointly smooth map `Φ` on
smooth chains, and the topological prism operator (`TopCat.Homotopy.toSSet`) of the restriction of
`Φ` to `[0, 1] × M` (`TauCeti.topCatHomotopyOfContMDiff`) on continuous singular chains. No homotopy
between `r ∘ j` and `id_N` is used: `N` need only dominate `M` smoothly, as happens when `N` is the
boundaryless interior of a manifold with boundary or corners deformed inward along an inward
semiflow.

Because any two homotopy inverses of the same chain map are chain homotopic
(`TauCeti.smoothSingularChainHomotopyInv`), the transferred homotopy inverse is independent up to
chain homotopy of the auxiliary manifold `N`, the maps `j` and `r`, the homotopy `Φ`, and the
inverse `s` (`ContMDiff.smoothSingularChainHomotopyOfRetractInv`), and the resulting homology
isomorphism is canonical (`ContMDiff.toHomologyIso_smoothSingularChainHomotopyEquivOfRetract_eq`).
Applying `Hom(-, A)` dualizes the transfer to a cochain homotopy equivalence between continuous
singular cochains and smooth singular cochains
(`TauCeti.smoothSingularCochainHomotopyEquivOfRetract`).

Concrete inward-domination transfer on the closed half-line `[0, ∞)` is in
`TauCeti.Geometry.Manifold.SmoothSingular.Transfer.HalfLine`, and the obstruction showing that
`j ∘ r ~ id_M` cannot be omitted (witnessed on `Circle`) is in
`TauCeti.Geometry.Manifold.SmoothSingular.Transfer.Obstruction`.

## Main definitions and results

* `ContMDiff.smoothSingularChainHomotopyEquivOfRetract`: transfer of a smooth-to-singular chain
  homotopy equivalence from `N` to `M` along `j : N → M`, `r : M → N`, and `Φ : ℝ × M → M` from
  `j ∘ r` to `id_M`.
* `ContMDiff.smoothSingularChainHomotopyOfRetractInv`,
  `ContMDiff.toHomologyIso_smoothSingularChainHomotopyEquivOfRetract_eq`: independence of
  `(N, j, r, Φ, eN)` up to chain homotopy and on homology.
* `TauCeti.smoothSingularCochainHomotopyEquivOfRetract`: dual cochain homotopy equivalence.

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
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) := by
  let rTop : TopCat.of M ⟶ TopCat.of N := TopCat.ofHom ⟨r, hr.continuous⟩
  let jTop : TopCat.of N ⟶ TopCat.of M := TopCat.ofHom ⟨j, hj.continuous⟩
  have hcompTop : rTop ≫ jTop = TopCat.ofHom ⟨j ∘ r, (hj.comp hr).continuous⟩ := by
    ext x
    rfl
  have hidTop : TopCat.ofHom ⟨id, (contMDiff_id (I := I) (n := ∞)).continuous⟩ =
      𝟙 (TopCat.of M) := by
    ext x
    rfl
  have hK : Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplexMap r hr) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R) (𝟙 _) :=
    (Homotopy.ofEq (by
      rw [← Functor.map_comp, ← smoothSingularSubcomplexMap_comp hj hr])).trans
      ((hΦ.smoothSingularChainHomotopy (f := j ∘ r) (g := id) hΦ₀ hΦ₁ R).trans
        (Homotopy.ofEq (by simp [smoothSingularSubcomplexMap_id])))
  have hL : Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map rTop) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map jTop) R) (𝟙 _) :=
    (Homotopy.ofEq (by rw [← Functor.map_comp, ← Functor.map_comp, hcompTop])).trans
      (((topCatHomotopyOfContMDiff (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀
        hΦ₁).toSSet.chainComplexMap R).trans
        (Homotopy.ofEq (by simp [hidTop])))
  refine eN.ofHomotopyRetractOfComm (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    hK hL ?_ ?_
  · rw [heN, ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι hj]
  · rw [heN, ← Functor.map_comp, ← Functor.map_comp, ← smoothSingularSubcomplexMap_ι hr]

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
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := by
  simp [smoothSingularChainHomotopyEquivOfRetract]

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
        eN.inv ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R := by
  simp [smoothSingularChainHomotopyEquivOfRetract]

end ContMDiff

end Retract

/-! ### Independence of auxiliary domination data and dual cochain transfer -/

section Independence

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {J₁ : ModelWithCorners ℝ E₁ H₁} {N₁ : Type u} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {J₂ : ModelWithCorners ℝ E₂ H₂} {N₂ : Type u} [TopologicalSpace N₂] [ChartedSpace H₂ N₂]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

open TauCeti

namespace ContMDiff

/-- **Independence of the auxiliary domination data.** Two smooth-chain homotopy inverses on `M`
transferred along possibly different manifolds `N₁` and `N₂`, maps `(j₁, r₁)` and `(j₂, r₂)`,
homotopies `Φ₁` and `Φ₂`, and inverses `eN₁` and `eN₂` are chain homotopic. -/
def smoothSingularChainHomotopyOfRetractInv
    {j₁ : N₁ → M} (hj₁ : ContMDiff J₁ I ∞ j₁) {r₁ : M → N₁} (hr₁ : ContMDiff I J₁ ∞ r₁)
    {Φ₁ : ℝ × M → M} (hΦ₁ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ₁)
    (hΦ₁₀ : ∀ x, Φ₁ (0, x) = j₁ (r₁ x)) (hΦ₁₁ : ∀ x, Φ₁ (1, x) = x)
    {j₂ : N₂ → M} (hj₂ : ContMDiff J₂ I ∞ j₂) {r₂ : M → N₂} (hr₂ : ContMDiff I J₂ ∞ r₂)
    {Φ₂ : ℝ × M → M} (hΦ₂ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ₂)
    (hΦ₂₀ : ∀ x, Φ₂ (0, x) = j₂ (r₂ x)) (hΦ₂₁ : ∀ x, Φ₂ (1, x) = x) (R : C)
    (eN₁ : HomotopyEquiv ((smoothSingularSubcomplex J₁ N₁ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₁)).chainComplex R))
    (heN₁ : eN₁.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₁ N₁).ι R)
    (eN₂ : HomotopyEquiv ((smoothSingularSubcomplex J₂ N₂ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₂)).chainComplex R))
    (heN₂ : eN₂.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₂ N₂).ι R) :
    Homotopy
      (hj₁.smoothSingularChainHomotopyEquivOfRetract hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).inv
      (hj₂.smoothSingularChainHomotopyEquivOfRetract hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).inv :=
  smoothSingularChainHomotopyInv R _ _
    (hj₁.smoothSingularChainHomotopyEquivOfRetract_hom hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁)
    (hj₂.smoothSingularChainHomotopyEquivOfRetract_hom hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂)

/-- The homology isomorphism induced by `smoothSingularChainHomotopyEquivOfRetract` is independent
of the auxiliary domination data `(N, j, r, Φ, eN)`. -/
theorem toHomologyIso_smoothSingularChainHomotopyEquivOfRetract_eq [CategoryWithHomology C]
    {j₁ : N₁ → M} (hj₁ : ContMDiff J₁ I ∞ j₁) {r₁ : M → N₁} (hr₁ : ContMDiff I J₁ ∞ r₁)
    {Φ₁ : ℝ × M → M} (hΦ₁ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ₁)
    (hΦ₁₀ : ∀ x, Φ₁ (0, x) = j₁ (r₁ x)) (hΦ₁₁ : ∀ x, Φ₁ (1, x) = x)
    {j₂ : N₂ → M} (hj₂ : ContMDiff J₂ I ∞ j₂) {r₂ : M → N₂} (hr₂ : ContMDiff I J₂ ∞ r₂)
    {Φ₂ : ℝ × M → M} (hΦ₂ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ₂)
    (hΦ₂₀ : ∀ x, Φ₂ (0, x) = j₂ (r₂ x)) (hΦ₂₁ : ∀ x, Φ₂ (1, x) = x) (R : C)
    (eN₁ : HomotopyEquiv ((smoothSingularSubcomplex J₁ N₁ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₁)).chainComplex R))
    (heN₁ : eN₁.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₁ N₁).ι R)
    (eN₂ : HomotopyEquiv ((smoothSingularSubcomplex J₂ N₂ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₂)).chainComplex R))
    (heN₂ : eN₂.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₂ N₂).ι R) (n : ℕ) :
    (hj₁.smoothSingularChainHomotopyEquivOfRetract hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).toHomologyIso n =
      (hj₂.smoothSingularChainHomotopyEquivOfRetract hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).toHomologyIso
        n :=
  HomotopyEquiv.toHomologyIso_eq_of_hom_eq
    ((hj₁.smoothSingularChainHomotopyEquivOfRetract_hom hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).trans
      (hj₂.smoothSingularChainHomotopyEquivOfRetract_hom hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).symm) n

end ContMDiff

end Independence

section Cochains

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

end Cochains
