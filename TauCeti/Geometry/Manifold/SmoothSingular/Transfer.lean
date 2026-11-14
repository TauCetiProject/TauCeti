/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Geometry.Manifold.DeRham.Circle
import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod

/-!
# Transfer of smooth singular chain homotopy equivalences

Let `M` and `N` be manifolds (possibly with boundary or corners) and let `j : N → M` and
`r : M → N` be smooth maps together with a smooth homotopy `Φ : ℝ × M → M` from `j ∘ r` to `id_M`
(`Φ (0, x) = j (r x)` and `Φ (1, x) = x`). Whenever the inclusion of smooth singular chains into
continuous singular chains is a chain homotopy equivalence on `N` with homotopy inverse `s`, the
composite `r_* ≫ s ≫ j_*` — applying `r_*` on continuous singular chains, `s` on `N`, and `j_*` on
smooth singular chains — is a chain homotopy inverse to the inclusion of smooth singular chains on
`M` (`TauCeti.smoothSingularChainHomotopyEquivOfRetract`).

Both inverse identities follow from naturality of pushforwards with the subcomplex inclusion, the
smooth prism operator (`TauCeti.smoothSingularChainHomotopy`) of the jointly smooth map `Φ` on
smooth chains, and the topological prism operator (`TopCat.Homotopy.toSSet`) of the restriction of
`Φ` to `[0, 1] × M` on continuous singular chains. No homotopy between `r ∘ j` and `id_N` is used:
`N` need only dominate `M` smoothly, as happens when `N` is the boundaryless interior of a manifold
with boundary or corners deformed inward along an inward semiflow.

Because any two homotopy inverses of the same chain map are chain homotopic
(`HomotopyEquiv.homotopyInvOfHomEq`), the transferred homotopy inverse is independent up to chain
homotopy of the auxiliary manifold `N`, the maps `j` and `r`, the homotopy `Φ`, and the inverse `s`
(`TauCeti.smoothSingularChainHomotopyOfRetractInv`), and the resulting homology isomorphism is
canonical and natural under smooth maps
(`TauCeti.homologyMap_comp_toHomologyIso_inv_smoothSingular`). Applying `Hom(-, A)` dualizes the
transfer to a cochain homotopy equivalence between continuous singular cochains and smooth singular
cochains (`TauCeti.smoothSingularCochainHomotopyEquivOfRetract`).

When `P` is a subsingleton (empty or a single point), every continuous simplex in `P` is constant
and hence smooth (`TauCeti.smoothSingularSubcomplex_eq_top_of_subsingleton`), so the inclusion of
smooth chains is an isomorphism (`TauCeti.smoothSingularChainHomotopyEquivOfSubsingleton`).
Transferring along a contraction onto a point therefore yields an unconditional chain homotopy
equivalence between smooth and continuous singular chains for every smoothly contractible manifold
(`TauCeti.smoothSingularChainHomotopyEquivOfContractible`), every nonempty model space of a real
model with corners (`TauCeti.smoothSingularChainHomotopyEquivModelSpace`), and every star-convex
open subset of a real normed space (`TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`).

Finally, we record concrete witnesses and sharpness checks:
* For `N = M`, `j = r = id`, and the constant homotopy, the transferred inverse is `s` itself
  (`TauCeti.smoothSingularChainHomotopyEquivOfRetract_id_inv`).
* On the closed half-line `[0, ∞)` (`EuclideanHalfSpace 1`), inward translation `r(x) = x + 1` into
  the open half-line `(0, ∞)` with deformation `Φ(t, x) = x + (1 - t)²` transfers the star-convex
  equivalence of `(0, ∞)` to `[0, ∞)` (`TauCeti.smoothSingularChainHomotopyEquivHalfLine`), sending
  the boundary `0`-simplex `[0]` to the interior smooth `0`-simplex `[1]`, whose difference from
  `[0]` is the boundary of the smooth curve `t ↦ t²` (`TauCeti.ιChainComplex_halfLineBridge_d`).
* The homotopy `j ∘ r ~ id_M` cannot be omitted: for `N = PUnit`, `M = Circle`, `r` constant, and
  `j` a point inclusion, for every chain map `s` on `PUnit` the candidate `r_* ≫ s ≫ j_*` induces
  zero on first homology (`TauCeti.homologyMap_pointTransferCandidate_eq_zero`), whereas the
  inclusion of smooth chains on `Circle` is nonzero on `H₁`, so `r_* ≫ s ≫ j_*` is neither a left
  nor a right chain homotopy inverse (`TauCeti.isEmpty_homotopy_circle_pointTransfer_hom_inv`,
  `TauCeti.isEmpty_homotopy_circle_pointTransfer_inv_hom`).

## Main definitions and results

* `TauCeti.smoothSingularChainHomotopyOfContMDiff`: smooth prism homotopy from a smooth map
  `ℝ × M → N` with prescribed values at `0` and `1`.
* `TauCeti.smoothSingularChainHomotopyEquivOfRetract`: transfer of a smooth-to-singular chain
  homotopy equivalence from `N` to `M` along `j : N → M`, `r : M → N`, and `Φ : ℝ × M → M` from
  `j ∘ r` to `id_M`.
* `TauCeti.smoothSingularChainHomotopyOfRetractInv`,
  `TauCeti.toHomologyIso_smoothSingularChainHomotopyEquivOfRetract_eq`: independence of `(N, j, r,
  Φ, eN)` up to chain homotopy and on homology.
* `TauCeti.smoothSingularChainHomotopyInvNaturality`,
  `TauCeti.homologyMap_comp_toHomologyIso_inv_smoothSingular`: naturality under smooth maps.
* `TauCeti.smoothSingularCochainHomotopyEquivOfRetract`: dual cochain homotopy equivalence.
* `TauCeti.smoothSingularChainHomotopyEquivOfSubsingleton`,
  `TauCeti.smoothSingularChainHomotopyEquivOfContractible`,
  `TauCeti.smoothSingularChainHomotopyEquivModelSpace`,
  `TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`: unconditional smooth-chain homotopy
  equivalences on subsingletons, smoothly contractible manifolds, model spaces, and star-convex
  opens.
* `TauCeti.smoothSingularChainHomotopyEquivHalfLine`: concrete inward-retract transfer from
  `(0, ∞)` to `[0, ∞)`.
* `TauCeti.isEmpty_homotopy_circle_pointTransfer_hom_inv`,
  `TauCeti.isEmpty_homotopy_circle_pointTransfer_inv_hom`: necessity of `j ∘ r ~ id_M` on `Circle`.

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

namespace TauCeti

section Retract

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- The continuous `[0, 1]`-homotopy obtained by restricting a smooth map `F : ℝ × M → N` with
`F (0, ·) = f` and `F (1, ·) = g`. -/
def contMDiffToTopCatHomotopy {f g : M → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    TopCat.Homotopy (TopCat.ofHom ⟨f, hf.continuous⟩) (TopCat.ofHom ⟨g, hg.continuous⟩) where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

/-- **The smooth prism homotopy from a jointly smooth map on `ℝ × M`.** A smooth map
`F : ℝ × M → N` with `F (0, ·) = f` and `F (1, ·) = g` induces a chain homotopy between the maps
on smooth singular chain complexes induced by `f` and `g`. -/
def smoothSingularChainHomotopyOfContMDiff {f g : M → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F) (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x)
    (R : C) :
    Homotopy (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (smoothSingularSubcomplexMap g hg) R) :=
  smoothSingularChainHomotopy hf hg (contMDiffToTopCatHomotopy hf hg hF h₀ h₁) hF (fun _ ↦ rfl) R

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
      ((smoothSingularChainHomotopyOfContMDiff (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀ hΦ₁
        R).trans (Homotopy.ofEq (by simp [smoothSingularSubcomplexMap_id])))
  have hL : Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map rTop) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map jTop) R) (𝟙 _) :=
    (Homotopy.ofEq (by rw [← Functor.map_comp, ← Functor.map_comp, hcompTop])).trans
      (((contMDiffToTopCatHomotopy (hj.comp hr) (contMDiff_id (I := I)) hΦ hΦ₀
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
    (smoothSingularChainHomotopyEquivOfRetract hj hr hΦ hΦ₀ hΦ₁ R eN heN).hom =
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
    (smoothSingularChainHomotopyEquivOfRetract hj hr hΦ hΦ₀ hΦ₁ R eN heN).inv =
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨r, hr.continuous⟩)) R ≫
        eN.inv ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap j hj) R := by
  simp [smoothSingularChainHomotopyEquivOfRetract]

/-- When `N = M`, `j = r = id`, and `Φ` is the constant homotopy `(t, x) ↦ x`, the transferred
chain homotopy inverse is `e.inv` itself. -/
theorem smoothSingularChainHomotopyEquivOfRetract_id_inv (R : C)
    (e : HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R))
    (he : e.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :
    (smoothSingularChainHomotopyEquivOfRetract (I := I) (J := I) (M := M) (N := M)
      (contMDiff_id (I := I)) (contMDiff_id (I := I)) contMDiff_snd
      (fun _ ↦ rfl) (fun _ ↦ rfl) R e he).inv = e.inv := by
  have hid : TopCat.ofHom ⟨(id : M → M), (contMDiff_id (I := I) (n := ∞)).continuous⟩ =
      𝟙 (TopCat.of M) := by
    ext x
    rfl
  simp [smoothSingularChainHomotopyEquivOfRetract_inv, hid]

end Retract

/-! ### Uniqueness up to homotopy, naturality, and dual cochain transfer -/

section Naturality

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {J₁ : ModelWithCorners ℝ E₁ H₁} {N₁ : Type u} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {J₂ : ModelWithCorners ℝ E₂ H₂} {N₂ : Type u} [TopologicalSpace N₂] [ChartedSpace H₂ N₂]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- Any two chain homotopy equivalences from smooth singular chains to continuous singular chains
whose forward map is the subcomplex inclusion have chain-homotopic inverses. -/
def smoothSingularChainHomotopyInv (R : C)
    (e₁ e₂ : HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R))
    (he₁ : e₁.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (he₂ : e₂.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :
    Homotopy e₁.inv e₂.inv :=
  e₁.homotopyInvOfHomEq e₂ (he₁.trans he₂.symm)

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
      (smoothSingularChainHomotopyEquivOfRetract hj₁ hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).inv
      (smoothSingularChainHomotopyEquivOfRetract hj₂ hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).inv :=
  smoothSingularChainHomotopyInv R _ _
    (smoothSingularChainHomotopyEquivOfRetract_hom hj₁ hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁)
    (smoothSingularChainHomotopyEquivOfRetract_hom hj₂ hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂)

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
    (smoothSingularChainHomotopyEquivOfRetract hj₁ hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).toHomologyIso n =
      (smoothSingularChainHomotopyEquivOfRetract hj₂ hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).toHomologyIso
        n :=
  HomotopyEquiv.toHomologyIso_eq_of_hom_eq
    ((smoothSingularChainHomotopyEquivOfRetract_hom hj₁ hr₁ hΦ₁ hΦ₁₀ hΦ₁₁ R eN₁ heN₁).trans
      (smoothSingularChainHomotopyEquivOfRetract_hom hj₂ hr₂ hΦ₂ hΦ₂₀ hΦ₂₁ R eN₂ heN₂).symm) n

/-- **Chain-homotopy naturality of smooth-chain homotopy inverses.** For any smooth map `f : M → N₁`
and smooth-chain homotopy equivalences `eM` on `M` and `eN` on `N₁` whose forward maps are the
subcomplex inclusions, `f_* ≫ eN.inv` is chain homotopic to `eM.inv ≫ f_*`. -/
def smoothSingularChainHomotopyInvNaturality {f : M → N₁} (hf : ContMDiff I J₁ ∞ f) (R : C)
    (eM : HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R))
    (heM : eM.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J₁ N₁ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₁)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₁ N₁).ι R) :
    Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫ eN.inv)
      (eM.inv ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R) :=
  eM.homotopyInvOfComm eN
    (by rw [heM, heN, ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι hf])

/-- **Naturality on homology of the smooth-chain inverse isomorphism.** For a smooth map
`f : M → N₁`, the inverse homology isomorphisms `(toHomologyIso n).inv` commute with pushforward on
continuous and smooth singular homology. -/
@[reassoc]
theorem homologyMap_comp_toHomologyIso_inv_smoothSingular [CategoryWithHomology C]
    {f : M → N₁} (hf : ContMDiff I J₁ ∞ f) (R : C)
    (eM : HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R))
    (heM : eM.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (eN : HomotopyEquiv ((smoothSingularSubcomplex J₁ N₁ : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of N₁)).chainComplex R))
    (heN : eN.hom = SSet.chainComplexMap (smoothSingularSubcomplex J₁ N₁).ι R) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (eN.toHomologyIso n).inv =
      (eM.toHomologyIso n).inv ≫ SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n :=
  eM.homologyMap_comp_toHomologyIso_inv_of_comm eN
    (fK := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
    (fL := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R)
    (by rw [heM, heN, ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι hf]) n

end Naturality

section Cochains

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type*} [Category* C] [HasCoproducts.{u} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (A : C)

/-- **Dual transfer on cochains.** Applying `Hom(-, A)` to
`smoothSingularChainHomotopyEquivOfRetract` produces a cochain homotopy equivalence from the
continuous singular cochain complex of `M` to the smooth singular cochain complex of `M`, whose
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
  (smoothSingularChainHomotopyEquivOfRetract hj hr hΦ hΦ₀ hΦ₁ R eN heN).linearYonedaFunctorMap k A

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
    smoothSingularChainHomotopyEquivOfRetract_hom]

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

end Cochains

/-! ### Subsingletons, smoothly contractible manifolds, model spaces, and star-convex opens -/

section Subsingleton

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (P : Type u) [TopologicalSpace P] [ChartedSpace H P]

/-- On a subsingleton manifold `P` (empty or a single point), every continuous singular simplex is
constant and therefore smooth. -/
theorem smoothSingularSubcomplex_eq_top_of_subsingleton [Subsingleton P] :
    smoothSingularSubcomplex I P = ⊤ := by
  ext k σ
  simp only [mem_smoothSingularSubcomplex_iff, Subfunctor.top_obj, mem_univ, iff_true]
  let p₀ : P := (TopCat.of P).toSSetObjEquiv k σ
    (fullSimplexEquivStdSimplex k.unop.len ⟨0, zero_mem_fullSimplex k.unop.len⟩)
  have hconst : (TopCat.of P).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len =
      fun _ ↦ p₀ := funext fun _ ↦ Subsingleton.elim _ _
  rw [hconst]
  exact contMDiffOnSubset_const I ∞ p₀

/-- On a subsingleton manifold, the inclusion of the smooth singular subcomplex into the singular
simplicial set is an isomorphism of simplicial sets. -/
def smoothSingularSubcomplexIsoOfSubsingleton [Subsingleton P] :
    (smoothSingularSubcomplex I P : SSet) ≅ TopCat.toSSet.obj (TopCat.of P) :=
  SSet.Subcomplex.eqToIso (smoothSingularSubcomplex_eq_top_of_subsingleton I P) ≪≫
    SSet.Subcomplex.topIso (TopCat.toSSet.obj (TopCat.of P))

/-- The forward morphism of `smoothSingularSubcomplexIsoOfSubsingleton` is the subcomplex
inclusion. -/
@[simp]
theorem smoothSingularSubcomplexIsoOfSubsingleton_hom [Subsingleton P] :
    (smoothSingularSubcomplexIsoOfSubsingleton I P).hom = (smoothSingularSubcomplex I P).ι := by
  simp [smoothSingularSubcomplexIsoOfSubsingleton]

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- On a subsingleton manifold `P`, the inclusion of smooth singular chains into continuous
singular chains is an isomorphism of chain complexes, hence a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfSubsingleton [Subsingleton P] (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I P : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of P)).chainComplex R) :=
  HomotopyEquiv.ofIso (((SSet.chainComplexFunctor C).obj R).mapIso
    (smoothSingularSubcomplexIsoOfSubsingleton I P))

/-- The forward map of `smoothSingularChainHomotopyEquivOfSubsingleton` is the inclusion of smooth
singular chains into continuous singular chains on `P`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfSubsingleton_hom [Subsingleton P] (R : C) :
    (smoothSingularChainHomotopyEquivOfSubsingleton I P R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I P).ι R := by
  simp [smoothSingularChainHomotopyEquivOfSubsingleton, HomotopyEquiv.ofIso]

/-- In degree zero on a subsingleton manifold, the inverse of
`smoothSingularChainHomotopyEquivOfSubsingleton` sends each singular `0`-simplex to the
corresponding smooth `0`-simplex. -/
@[reassoc (attr := simp)]
theorem ι_smoothSingularChainHomotopyEquivOfSubsingleton_inv_f_zero [Subsingleton P] (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of P)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of P)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfSubsingleton I P R).inv.f 0 =
      (smoothSingularSubcomplex I P : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ I P).symm ((TopCat.of P).toSSetObj₀Equiv σ)) := by
  dsimp [smoothSingularChainHomotopyEquivOfSubsingleton, HomotopyEquiv.ofIso]
  rw [SSet.ι_chainComplexMap_f]
  congr 1
  apply Subtype.ext
  exact (TopCat.of P).toSSetObj₀Equiv.injective (Subsingleton.elim _ _)

end Subsingleton

section Contractible

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- **Smooth-chain homotopy equivalence for smoothly contractible manifolds.** If `Φ : ℝ × M → M`
is a smooth map joining a constant map `Φ (0, ·) = c` to the identity `Φ (1, ·) = id`, then the
inclusion of smooth singular chains into continuous singular chains on `M` is a chain homotopy
equivalence, obtained by transferring the isomorphism on `PUnit` along `r = const` and
`j = const c`. -/
def smoothSingularChainHomotopyEquivOfContractible (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  smoothSingularChainHomotopyEquivOfRetract
    (J := 𝓘(ℝ, PUnit.{u + 1})) (N := PUnit.{u + 1})
    (j := fun _ ↦ c) contMDiff_const
    (r := fun _ ↦ PUnit.unit) contMDiff_const
    hΦ hΦ₀ hΦ₁ R
    (smoothSingularChainHomotopyEquivOfSubsingleton 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} R)
    (smoothSingularChainHomotopyEquivOfSubsingleton_hom 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} R)

/-- The forward map of `smoothSingularChainHomotopyEquivOfContractible` is the inclusion of smooth
singular chains into continuous singular chains on `M`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContractible_hom (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    (smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := by
  simp [smoothSingularChainHomotopyEquivOfContractible]

/-- On a smoothly contractible manifold with contraction centre `c`, the transferred homotopy
inverse sends the summand of every singular `0`-simplex to the summand of the smooth `0`-simplex at
`c`. -/
@[reassoc (attr := simp)]
theorem ι_smoothSingularChainHomotopyEquivOfContractible_inv_f_zero (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of M)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).inv.f 0 =
      (smoothSingularSubcomplex I M : SSet).ιChainComplex ((SmoothSimplex.equiv₀ I M).symm c) := by
  rw [smoothSingularChainHomotopyEquivOfContractible, smoothSingularChainHomotopyEquivOfRetract_inv,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    ι_smoothSingularChainHomotopyEquivOfSubsingleton_inv_f_zero_assoc, SSet.ι_chainComplexMap_f]
  congr 1
  exact SmoothSimplex.smoothSingularSubcomplexMap_app_equiv₀_symm contMDiff_const _

/-- On a smoothly contractible manifold, the inclusion of smooth singular simplices induces an
isomorphism on homology in every degree (including degree zero). -/
theorem isIso_homologyMap_smoothSingularSubcomplex_ι_of_contractible [CategoryWithHomology C]
    (c : M) {Φ : ℝ × M → M} (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = c) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) (n : ℕ) :
    IsIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n) := by
  have h := ((smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).toHomologyIso
    n).isIso_hom
  rwa [HomotopyEquiv.toHomologyIso_hom, smoothSingularChainHomotopyEquivOfContractible_hom] at h

end Contractible

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u} [TopologicalSpace H]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- **Smooth-chain homotopy equivalence on any model space with corners.** Because `range I` is
convex in `E`, the straight-line contraction `(t, x) ↦ I.symm (I x₀ + ψ(t) • (I x - I x₀))` stays
in `range I` and is jointly smooth on `ℝ × H`, so the inclusion of smooth singular chains on `H` is
a chain homotopy equivalence around any basepoint `x₀ : H`. -/
def smoothSingularChainHomotopyEquivModelSpace (I : ModelWithCorners ℝ E H) (x₀ : H) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I H : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of H)).chainComplex R) := by
  let ΦE : ℝ × H → E := fun p ↦
    I x₀ + Real.smoothTransition p.1 • (I p.2 - I x₀)
  have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × H ↦ Real.smoothTransition p.1 :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hI : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × H ↦ I p.2 :=
    I.contMDiff.comp contMDiff_snd
  have hΦE : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ ΦE :=
    contMDiff_const.add (hψ.smul (hI.sub contMDiff_const))
  have hmem : ∀ p : ℝ × H, ΦE p ∈ range I := fun p ↦
    (I.convex_range.starConvex (mem_range_self x₀)).add_smul_sub_mem (mem_range_self p.2)
      (Real.smoothTransition.nonneg p.1) (Real.smoothTransition.le_one p.1)
  have hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × H ↦ I.symm (ΦE p)) :=
    I.contMDiffOn_symm.comp_contMDiff hΦE hmem
  exact smoothSingularChainHomotopyEquivOfContractible x₀ hΦ
    (fun x ↦ by simp [ΦE, Real.smoothTransition.zero])
    (fun x ↦ by simp [ΦE, Real.smoothTransition.one]) R

/-- The forward map of `smoothSingularChainHomotopyEquivModelSpace` is the inclusion of smooth
singular chains into continuous singular chains on `H`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivModelSpace_hom (I : ModelWithCorners ℝ E H) (x₀ : H)
    (R : C) :
    (smoothSingularChainHomotopyEquivModelSpace I x₀ R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I H).ι R := by
  simp [smoothSingularChainHomotopyEquivModelSpace]

end ModelSpace

section StarConvex

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def starConvexContraction {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (p : ℝ × U) : U :=
  ⟨c + Real.smoothTransition p.1 • ((p.2 : V) - c),
    hU.add_smul_sub_mem p.2.2 (Real.smoothTransition.nonneg p.1)
      (Real.smoothTransition.le_one p.1)⟩

private lemma contMDiff_starConvexContraction {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ (starConvexContraction hU) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  have hψ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞
      fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hx : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ fun p : ℝ × U ↦ (p.2 : V) :=
    contMDiff_subtype_val.comp contMDiff_snd
  exact contMDiff_const.add (hψ.smul (hx.sub contMDiff_const))

private lemma starConvexContraction_zero {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U) (x : U) :
    starConvexContraction hU (0, x) = ⟨c, hc⟩ :=
  Subtype.ext (by simp [starConvexContraction, Real.smoothTransition.zero])

private lemma starConvexContraction_one {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    starConvexContraction hU (1, x) = x :=
  Subtype.ext (by simp [starConvexContraction, Real.smoothTransition.one])

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

open Classical in
/-- **Smooth-chain homotopy equivalence on star-convex open subsets of normed spaces.** For every
star-convex open subset `U` of a real normed space `V` (empty or nonempty, without finite-dimension
assumptions), the inclusion of smooth singular chains into continuous singular chains on `U` is a
chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfStarConvex {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R) :=
  if hne : (U : Set V).Nonempty then
    smoothSingularChainHomotopyEquivOfContractible ⟨c, hU.mem hne⟩
      (contMDiff_starConvexContraction hU)
      (starConvexContraction_zero hU (hU.mem hne))
      (starConvexContraction_one hU) R
  else
    have : Subsingleton U := ⟨fun x _ ↦ False.elim (hne ⟨x.1, x.2⟩)⟩
    smoothSingularChainHomotopyEquivOfSubsingleton 𝓘(ℝ, V) U R

private lemma smoothSingularChainHomotopyEquivOfStarConvex_of_mem
    {U : TopologicalSpace.Opens V} {c : V} (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U)
    (R : C) :
    smoothSingularChainHomotopyEquivOfStarConvex hU R =
      smoothSingularChainHomotopyEquivOfContractible ⟨c, hc⟩
        (contMDiff_starConvexContraction hU)
        (starConvexContraction_zero hU hc)
        (starConvexContraction_one hU) R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  exact dite_eq_left_of_eq_true (eq_true (⟨c, hc⟩ : (U : Set V).Nonempty))

/-- The forward map of `smoothSingularChainHomotopyEquivOfStarConvex` is the inclusion of smooth
singular chains into continuous singular chains on `U`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfStarConvex_hom {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (R : C) :
    (smoothSingularChainHomotopyEquivOfStarConvex hU R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex 𝓘(ℝ, V) U).ι R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  split_ifs <;> simp

/-- On a nonempty star-convex open subset `U` with star-centre `c`, the inverse of
`smoothSingularChainHomotopyEquivOfStarConvex` sends every singular `0`-simplex to the smooth
`0`-simplex at `c`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero
    {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U) (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of U)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfStarConvex hU R).inv.f 0 =
      (smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ 𝓘(ℝ, V) U).symm ⟨c, hc⟩) := by
  rw [smoothSingularChainHomotopyEquivOfStarConvex_of_mem hU hc R,
    ι_smoothSingularChainHomotopyEquivOfContractible_inv_f_zero]

end StarConvex

/-! ### Concrete inward-domination transfer on the closed half-line `[0, ∞)` -/

section HalfLine

/-- The open positive half-line `(0, ∞)` as an open submanifold of `ℝ`. -/
def openHalfLine : TopologicalSpace.Opens ℝ :=
  ⟨Ioi 0, isOpen_Ioi⟩

/-- Inclusion of the open half-line `(0, ∞)` into the closed half-line `EuclideanHalfSpace 1`. -/
def openHalfLineInclusion (y : openHalfLine) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 y.1)

/-- The `0`-th coordinate of `openHalfLineInclusion y` is `y`. -/
@[simp]
theorem coe_openHalfLineInclusion_apply (y : openHalfLine) :
    (openHalfLineInclusion y).1 0 = y.1 := by
  have hy : 0 ≤ (EuclideanSpace.single 0 y.1 : EuclideanSpace ℝ (Fin 1)) 0 := by
    simpa using y.2.le
  rw [openHalfLineInclusion, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]
  simp

/-- The inclusion `(0, ∞) → [0, ∞)` is smooth with respect to `𝓘(ℝ, ℝ)` and `𝓡∂ 1`. -/
theorem contMDiff_openHalfLineInclusion :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ openHalfLineInclusion := by
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (fun y : openHalfLine ↦ EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 1) y.1) :=
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff.contMDiff.comp
        contMDiff_subtype_val).congr fun y ↦ by
      ext i
      rw [Subsingleton.elim i 0]
      simp
  refine (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hlin fun y ↦ ?_
  rw [range_modelWithCornersEuclideanHalfSpace]
  simpa using y.2.le

/-- Smooth inward translation `r(x) = x + 1` from the closed half-line `[0, ∞)` into its open
interior `(0, ∞)`. -/
def halfLineInwardRetract (x : EuclideanHalfSpace 1) : openHalfLine :=
  ⟨x.1 0 + 1, add_pos_of_nonneg_of_pos x.2 zero_lt_one⟩

/-- The underlying real value of `halfLineInwardRetract x` is `x.1 0 + 1`. -/
@[simp]
theorem coe_halfLineInwardRetract (x : EuclideanHalfSpace 1) :
    (halfLineInwardRetract x : ℝ) = x.1 0 + 1 :=
  (rfl)

/-- The inward translation `r(x) = x + 1` is smooth from `EuclideanHalfSpace 1` to `(0, ∞)`. -/
theorem contMDiff_halfLineInwardRetract :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ halfLineInwardRetract := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
    (𝓡∂ 1).contMDiff).add contMDiff_const

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` on `ℝ × [0, ∞)`: because `(1 - t)² ≥ 0` for all
`t ∈ ℝ`, it stays in `[0, ∞)` globally in `t`, starts at `j(r(x)) = x + 1` at `t = 0`, and reaches
`x` at `t = 1`. -/
def halfLineInwardDeformation (p : ℝ × EuclideanHalfSpace 1) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2))

/-- The `0`-th coordinate of `halfLineInwardDeformation (t, x)` is `x + (1 - t)²`. -/
@[simp]
theorem coe_halfLineInwardDeformation_apply (p : ℝ × EuclideanHalfSpace 1) :
    (halfLineInwardDeformation p).1 0 = p.2.1 0 + (1 - p.1) ^ 2 := by
  have hp : 0 ≤ (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) :
      EuclideanSpace ℝ (Fin 1)) 0 := by
    have hx : 0 ≤ p.2.1 0 := p.2.2
    have hsq : 0 ≤ (1 - p.1) ^ 2 := sq_nonneg (1 - p.1)
    simpa using add_nonneg hx hsq
  rw [halfLineInwardDeformation, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hp]
  simp

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` preserves the open interior `(0, ∞)` at every
time `t ∈ ℝ`. -/
theorem halfLineInwardDeformation_pos {t : ℝ} {x : EuclideanHalfSpace 1} (hx : 0 < x.1 0) :
    0 < (halfLineInwardDeformation (t, x)).1 0 := by
  rw [coe_halfLineInwardDeformation_apply]
  nlinarith [sq_nonneg (1 - t)]

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` is jointly smooth on `ℝ × [0, ∞)`. -/
theorem contMDiff_halfLineInwardDeformation :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ halfLineInwardDeformation := by
  have hcoord : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) := by
    have hx : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
        (𝓡∂ 1).contMDiff).comp contMDiff_snd
    have ht : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (1 - p.1) ^ 2) :=
      ((contDiff_const.sub contDiff_id).pow 2).contMDiff.comp contMDiff_fst
    exact hx.add ht
  have hlin : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (fun p : ℝ × EuclideanHalfSpace 1 ↦
        EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 1) ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2)) :=
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff.contMDiff.comp hcoord).congr fun p ↦ by
      ext i
      rw [Subsingleton.elim i 0]
      simp
  refine (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hlin fun p ↦ ?_
  rw [range_modelWithCornersEuclideanHalfSpace]
  have hx : 0 ≤ p.2.1 0 := p.2.2
  have hsq : 0 ≤ (1 - p.1) ^ 2 := sq_nonneg (1 - p.1)
  simpa using add_nonneg hx hsq

/-- At `t = 0`, `halfLineInwardDeformation` agrees with `j ∘ r`. -/
@[simp]
theorem halfLineInwardDeformation_zero (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (0, x) = openHalfLineInclusion (halfLineInwardRetract x) := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply, coe_openHalfLineInclusion_apply,
    coe_halfLineInwardRetract]
  ring

/-- At `t = 1`, `halfLineInwardDeformation` is the identity on `[0, ∞)`. -/
@[simp]
theorem halfLineInwardDeformation_one (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (1, x) = x := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply]
  ring

/-- The open positive half-line `(0, ∞)` is star-convex around `1`. -/
theorem starConvex_openHalfLine : StarConvex ℝ 1 (openHalfLine : Set ℝ) :=
  (convex_Ioi (0 : ℝ)).starConvex (zero_lt_one : (1 : ℝ) ∈ Ioi 0)

/-- The point `1` of the closed half-line `[0, ∞)`. -/
def halfLineOne : EuclideanHalfSpace 1 :=
  openHalfLineInclusion ⟨1, zero_lt_one⟩

/-- **Smooth-chain homotopy equivalence on `[0, ∞)` transferred from `(0, ∞)`.** Combining the
star-convex equivalence on `(0, ∞)` (centred at `1`) with
`smoothSingularChainHomotopyEquivOfRetract` along `r(x) = x + 1` and `Φ(t, x) = x + (1 - t)²`
yields a chain homotopy equivalence on `EuclideanHalfSpace 1`. -/
def smoothSingularChainHomotopyEquivHalfLine
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    HomotopyEquiv
      ((smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))).chainComplex R) :=
  smoothSingularChainHomotopyEquivOfRetract
    contMDiff_openHalfLineInclusion contMDiff_halfLineInwardRetract
    contMDiff_halfLineInwardDeformation
    halfLineInwardDeformation_zero halfLineInwardDeformation_one R
    (smoothSingularChainHomotopyEquivOfStarConvex starConvex_openHalfLine R)
    (smoothSingularChainHomotopyEquivOfStarConvex_hom starConvex_openHalfLine R)

/-- The forward map of `smoothSingularChainHomotopyEquivHalfLine` is the inclusion of smooth
singular chains into continuous singular chains on `[0, ∞)`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivHalfLine_hom
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularChainHomotopyEquivHalfLine R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1)).ι R := by
  simp [smoothSingularChainHomotopyEquivHalfLine]

/-- On `[0, ∞)`, the transferred inverse sends every singular `0`-simplex (and in particular the
boundary vertex `[0]`) via `(0, ∞)` to the interior smooth `0`-simplex `[1]`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivHalfLine_inv_f_zero
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of (EuclideanHalfSpace 1))).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivHalfLine R).inv.f 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm halfLineOne) := by
  rw [smoothSingularChainHomotopyEquivHalfLine, smoothSingularChainHomotopyEquivOfRetract_inv,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero_assoc starConvex_openHalfLine
      (zero_lt_one : (1 : ℝ) ∈ openHalfLine) R,
    SSet.ι_chainComplexMap_f]
  congr 1
  exact SmoothSimplex.smoothSingularSubcomplexMap_app_equiv₀_symm
    contMDiff_openHalfLineInclusion ⟨1, zero_lt_one⟩

/-- The smooth curve `t ↦ t²` in `[0, ∞)`, which meets the boundary `0` with vanishing velocity so
that it extends smoothly across `t = 0` on all of `ℝ`, bundled as a smooth `1`-simplex from `0` to
`1`. -/
def halfLineBridge : SmoothSimplex (𝓡∂ 1) (EuclideanHalfSpace 1) 1 := by
  let γ : ℝ → EuclideanHalfSpace 1 := fun t ↦ (𝓡∂ 1).symm (EuclideanSpace.single 0 (t ^ 2))
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (fun t : ℝ ↦ EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 1) (t ^ 2)) :=
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff.contMDiff.comp
        (contDiff_id.pow 2).contMDiff).congr fun t ↦ by
      ext i
      rw [Subsingleton.elim i 0]
      simp
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ γ :=
    (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hlin fun t ↦ by
      rw [range_modelWithCornersEuclideanHalfSpace]
      simpa using sq_nonneg t
  exact SmoothSimplex.ofCurve hγ

/-- In the smooth singular chain complex of `[0, ∞)`, the boundary of `halfLineBridge` is
`[1] - [0]`, witnessing that the transferred image `[1]` of the boundary vertex `[0]` is smoothly
homologous to `[0]`. -/
theorem ιChainComplex_halfLineBridge_d
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex halfLineBridge ≫
        ((smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).chainComplex R).d 1 0 =
      (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm halfLineOne) -
        (smoothSingularSubcomplex (𝓡∂ 1) (EuclideanHalfSpace 1) : SSet).ιChainComplex
          ((SmoothSimplex.equiv₀ (𝓡∂ 1) (EuclideanHalfSpace 1)).symm 0) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  have h1 : (𝓡∂ 1).symm (EuclideanSpace.single 0 (1 : ℝ)) = halfLineOne := rfl
  have h0 : (𝓡∂ 1).symm (EuclideanSpace.single 0 (0 : ℝ)) = (0 : EuclideanHalfSpace 1) := by
    ext i
    rw [Subsingleton.elim i 0, modelWithCornersEuclideanHalfSpace_symm_apply_of_le (by simp)]
    simp
    rfl
  simp [halfLineBridge, SmoothSimplex.δ_zero_ofCurve, SmoothSimplex.δ_one_ofCurve, h1, h0,
    sub_eq_add_neg]

end HalfLine

/-! ### Necessity of `j ∘ r ~ id_M`: point-retract obstruction and the circle -/

section Necessity

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- The candidate chain map `r_* ≫ s ≫ j_*` from continuous singular chains of `M` to smooth
singular chains of `M` associated to the constant map `r : M → PUnit`, a point inclusion
`j = const c`, and an arbitrary chain map `s` on `PUnit`. -/
def pointTransferCandidate (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R)) :
    ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) ⟶
      ((smoothSingularSubcomplex I M : SSet).chainComplex R) :=
  SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const M PUnit.unit))) R ≫
    s ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap (fun _ : PUnit.{u + 1} ↦ c)
      contMDiff_const) R

/-- Because `PUnit` has vanishing positive-degree singular homology, `pointTransferCandidate`
induces the zero map on homology in every positive degree `n ≠ 0`, for every choice of `s`. -/
theorem homologyMap_pointTransferCandidate_eq_zero [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0) :
    HomologicalComplex.homologyMap (pointTransferCandidate (I := I) c R s) n = 0 := by
  have hpt : IsZero
      (((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R).homology n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R
      (TopCat.of PUnit.{u + 1}) hn
  have hconst : HomologicalComplex.homologyMap
      (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const M PUnit.unit))) R) n = 0 :=
    hpt.eq_of_tgt _ 0
  rw [pointTransferCandidate, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, hconst, zero_comp]

/-- Whenever `M` has non-zero smooth singular homology in positive degree `n`, no chain map `s` on
`PUnit` can make `pointTransferCandidate c R s` a right homotopy inverse of the smooth-chain
inclusion on `M`. -/
theorem isEmpty_homotopy_pointTransferCandidate_hom_inv [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0)
    (hH : ¬ IsZero (((smoothSingularSubcomplex I M : SSet).chainComplex R).homology n)) :
    IsEmpty (Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        pointTransferCandidate (I := I) c R s) (𝟙 _)) := by
  refine ⟨fun h ↦ hH ?_⟩
  have hid := h.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp, homologyMap_pointTransferCandidate_eq_zero c R s hn,
    comp_zero, HomologicalComplex.homologyMap_id] at hid
  exact (IsZero.iff_id_eq_zero _).mpr hid.symm

/-- Whenever `M` has non-zero continuous singular homology in positive degree `n`, no chain map `s`
on `PUnit` can make `pointTransferCandidate c R s` a left homotopy inverse of the smooth-chain
inclusion on `M`. -/
theorem isEmpty_homotopy_pointTransferCandidate_inv_hom [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0)
    (hH : ¬ IsZero (((TopCat.toSSet.obj (TopCat.of M)).chainComplex R).homology n)) :
    IsEmpty (Homotopy
      (pointTransferCandidate (I := I) c R s ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) (𝟙 _)) := by
  refine ⟨fun h ↦ hH ?_⟩
  have hid := h.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp, homologyMap_pointTransferCandidate_eq_zero c R s hn,
    zero_comp, HomologicalComplex.homologyMap_id] at hid
  exact (IsZero.iff_id_eq_zero _).mpr hid.symm

/-- Smoothness of the standard circuit `t ↦ exp(2π i t)` of the unit circle `S¹`. -/
theorem contMDiff_circleLoop :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun t : ℝ ↦ Circle.exp (2 * Real.pi * t)) :=
  (contMDiff_circleExp (m := ∞)).comp
    (((contDiff_const (c := 2 * Real.pi)).mul contDiff_id).contMDiff)

/-- The standard smooth circuit `t ↦ exp(2π i t)` of the unit circle `S¹`, as a smooth singular
`1`-simplex. -/
def smoothCircleLoop : SmoothSimplex (𝓡 1) Circle 1 :=
  SmoothSimplex.ofCurve contMDiff_circleLoop

/-- The smooth circuit `smoothCircleLoop` is a `1`-cycle in the smooth singular chain complex of
`Circle` with coefficients in any object `R`. -/
theorem ιChainComplex_smoothCircleLoop_d
    {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] (R : C) :
    (smoothSingularSubcomplex (𝓡 1) Circle : SSet).ιChainComplex smoothCircleLoop ≫
        ((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex R).d 1 0 = 0 := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp [smoothCircleLoop, SmoothSimplex.δ_zero_ofCurve, SmoothSimplex.δ_one_ofCurve]

/-- The integral of `circleAngularForm` along the continuous path of `smoothCircleLoop` is `2π`. -/
private theorem pathClassIntegral_circleAngularForm_smoothCircleLoop :
    pathClassIntegral circleAngularForm (.mk (TauCeti.TopCat.path₁ smoothCircleLoop.1)) =
      2 * Real.pi := by
  have hclosed : mextDeriv circleAngularForm = 0 := by
    simpa [coe_circleAngularClosedForm] using
      (mem_closedForms (𝓡 1) circleAngularClosedForm.1).mp circleAngularClosedForm.2
  rw [smoothCircleLoop, SmoothSimplex.coe_ofCurve,
    pathClassIntegral_mk_eq_pathIntegral (isSmoothForm_circleAngularForm.of_le (by norm_num))
      hclosed (contMDiff_circleLoop.of_le (by norm_num))
      (fun t ↦ TauCeti.TopCat.path₁_simplex₁_apply _ t)]
  have hchg := pathIntegral_comp_mul_add (isSmoothForm_circleAngularForm.of_le zero_le)
    (contMDiff_circleExp (m := 1)) (2 * Real.pi) 0 0 1
  simp only [add_zero, mul_zero, mul_one, pathIntegral_circleAngularForm_circleExp, sub_zero]
    at hchg
  exact hchg

/-- On `Circle`, the inclusion of smooth singular chains into continuous singular chains is nonzero
on `H₁(Circle; ℤ)`: the class of `smoothCircleLoop` has period `2π ≠ 0` under
`homologyPeriodHom circleAngularForm`. -/
theorem homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero :
    SSet.homologyMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ) 1 ≠ 0 := by
  intro hzero
  let K := (smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)
  let φ := SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ)
  have hz : K.d 1 0
      ((smoothSingularSubcomplex (𝓡 1) Circle : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        smoothCircleLoop (1 : ℤ)) = 0 := by
    have h := ConcreteCategory.congr_hom
      (ιChainComplex_smoothCircleLoop_d (ModuleCat.of ℤ ℤ)) (1 : ℤ)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  let zK : K.cycles 1 := K.moduleCatCyclesMk _ 0 (by simp) hz
  let w := HomologicalComplex.cyclesMap φ 1 zK
  have himg := ConcreteCategory.congr_hom hzero (K.homologyπ 1 zK)
  dsimp [SSet.homologyMap] at himg
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply] at himg
  have hper :
      chainsDesc
        (fun s ↦ pathClassIntegral circleAngularForm (.mk (TauCeti.TopCat.path₁ s)))
        ((((singularChains ℤ).obj (.of Circle)).iCycles 1).hom w) = 0 :=
    (homologyPeriodHom_homologyπ (φ := circleAngularForm) w).symm.trans
      ((congrArg (homologyPeriodHom circleAngularForm) himg).trans (map_zero _))
  have hi : (((singularChains ℤ).obj (.of Circle)).iCycles 1).hom w =
      simplexChain smoothCircleLoop.1 (1 : ℤ) :=
    (K.moduleCat_iCycles_cyclesMap_apply 1 φ zK).trans
      ((congrArg (φ.f 1) (K.iCycles_moduleCatCyclesMk 1 _ 0 (by simp) hz)).trans
        (ConcreteCategory.congr_hom
          (SSet.ι_chainComplexMap_f _ _ (smoothSingularSubcomplex (𝓡 1) Circle).ι
            (ModuleCat.of ℤ ℤ) smoothCircleLoop) (1 : ℤ)))
  rw [hi, chainsDesc_simplexChain_one,
    pathClassIntegral_circleAngularForm_smoothCircleLoop] at hper
  linarith [Real.pi_pos]

/-- **Necessity of `j ∘ r ~ id_M` (right inverse).** On `Circle`, for any point `c` and any chain
map `s` on `PUnit`, the point-retract candidate `r_* ≫ s ≫ j_*` is not a right chain homotopy
inverse of the smooth-chain inclusion. -/
theorem isEmpty_homotopy_circle_pointTransfer_hom_inv (c : Circle)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{1})).chainComplex (ModuleCat.of ℤ ℤ)) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{1}) PUnit.{1} : SSet).chainComplex
        (ModuleCat.of ℤ ℤ))) :
    IsEmpty (Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ) ≫
        pointTransferCandidate (I := 𝓡 1) c (ModuleCat.of ℤ ℤ) s) (𝟙 _)) :=
  isEmpty_homotopy_pointTransferCandidate_hom_inv c (ModuleCat.of ℤ ℤ) s one_ne_zero fun hZ ↦
    homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero (hZ.eq_of_src _ _)

/-- **Necessity of `j ∘ r ~ id_M` (left inverse).** On `Circle`, for any point `c` and any chain
map `s` on `PUnit`, the point-retract candidate `r_* ≫ s ≫ j_*` is not a left chain homotopy
inverse of the smooth-chain inclusion. -/
theorem isEmpty_homotopy_circle_pointTransfer_inv_hom (c : Circle)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{1})).chainComplex (ModuleCat.of ℤ ℤ)) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{1}) PUnit.{1} : SSet).chainComplex
        (ModuleCat.of ℤ ℤ))) :
    IsEmpty (Homotopy
      (pointTransferCandidate (I := 𝓡 1) c (ModuleCat.of ℤ ℤ) s ≫
        SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ))
      (𝟙 _)) :=
  isEmpty_homotopy_pointTransferCandidate_inv_hom c (ModuleCat.of ℤ ℤ) s one_ne_zero fun hZ ↦
    homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero (hZ.eq_of_tgt _ _)

end Necessity

end TauCeti
