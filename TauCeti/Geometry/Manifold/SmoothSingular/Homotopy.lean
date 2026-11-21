/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import TauCeti.Topology.Homotopy.RealProd

import TauCeti.Algebra.Homology.Homotopy
import TauCeti.Geometry.Manifold.ContMDiff.Homotopy

/-!
# Homotopy invariance of smooth singular homology

Let `f g : M → N` be smooth maps of manifolds and let `F : ℝ × M → N` be a smooth map with
`F (0, x) = f x` and `F (1, x) = g x`, so that its restriction to `[0, 1] × M` is a homotopy `H`
from `f` to `g`. The singular simplicial set functor turns `H` into a simplicial homotopy
`H.toSSet : Sing M ⊗ Δ[1] ⟶ Sing N` (Mathlib's `TopCat.Homotopy.toSSet`), whose value on a pair
of an `n`-simplex `σ` and a vertex map `α : ⦋n⦌ ⟶ ⦋1⦌` is the singular simplex
`w ↦ H (t_α w, σ w)`, where `t_α w` is the total barycentric weight of the vertices that `α` sends
to `1`. The coordinate `t_α` is affine, so when `σ` is smooth this simplex is the composite of the
smooth map `F` with a pair of smooth maps on the standard simplex, and it is smooth again
(`TauCeti.range_whiskerRight_ι_comp_toSSet_h_le_smoothSingularSubcomplex`).

Thus `H.toSSet` restricts to a simplicial homotopy between the maps of smooth singular subcomplexes
induced by `f` and `g` (`TauCeti.smoothSingularSubcomplexHomotopy`). Mathlib's homotopy invariance
of simplicial homology (`SSet.Homotopy.chainComplexMap`) turns it into a chain homotopy of smooth
singular chain complexes, the smooth prism operator (`TauCeti.smoothSingularChainHomotopy`), so
smoothly homotopic maps induce the same maps on smooth singular homology, with coefficients in any
object of a preadditive category with coproducts
(`TauCeti.homologyMap_smoothSingularSubcomplexMap_eq`). The homotopy of smooth subcomplexes is the
restriction of the homotopy of singular simplicial sets
(`TauCeti.smoothSingularSubcomplexHomotopy_h_ι`).

The homotopy is required to be the restriction of a smooth map on all of `ℝ × M`
(`TauCeti.homotopyOfRealProd`), not merely smooth on `[0, 1] × M`: a smooth simplex is locally the
restriction of a smooth map on an open subset of `ℝⁿ`, and the affine coordinate `t_α` takes values
outside `[0, 1]` off the simplex.

Any two chain homotopy equivalences from smooth singular chains to continuous singular chains whose
forward map is the subcomplex inclusion have chain-homotopic inverses
(`TauCeti.smoothSingularChainHomotopyInv`), and the resulting homotopy inverses and homology
isomorphisms are natural under smooth maps (`ContMDiff.smoothSingularChainHomotopyInvNaturality`,
`ContMDiff.homologyMap_comp_toHomologyIso_inv_smoothSingular`). On a subsingleton manifold, the
inclusion of smooth singular chains is an isomorphism and hence a chain homotopy equivalence
(`ModelWithCorners.smoothSingularChainHomotopyEquivOfSubsingleton`).

Homotopy invariance is an input of the comparison of smooth with continuous singular homology by a
Mayer–Vietoris induction; its consequences for smoothly contractible manifolds are in
`TauCeti.Geometry.Manifold.SmoothSingular.Contractible`.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplexHomotopy`: a smooth homotopy induces a simplicial homotopy of
  the maps of smooth singular subcomplexes, restricting the homotopy of singular simplicial sets.
* `TauCeti.smoothSingularChainHomotopy`: the induced chain homotopy of smooth singular chains.
* `ContMDiff.smoothSingularChainHomotopy`: the smooth singular chain homotopy obtained directly from
  a jointly smooth map `F : ℝ × M → N` with prescribed endpoint slices `F (0, ·) = f` and
  `F (1, ·) = g`.
* `TauCeti.homologyMap_smoothSingularSubcomplexMap_eq`: smoothly homotopic maps induce the same map
  on smooth singular homology.
* `TauCeti.smoothSingularChainHomotopyInv`,
  `ContMDiff.smoothSingularChainHomotopyInvNaturality`,
  `ContMDiff.homologyMap_comp_toHomologyIso_inv_smoothSingular`: uniqueness up to homotopy and
  naturality of homotopy inverses for the smooth-to-singular chain inclusion.
* `ModelWithCorners.smoothSingularChainHomotopyEquivOfSubsingleton`: chain homotopy equivalence on
  a subsingleton manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Smooth Singular Homology*,
  proof of Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial Opposite Set Convexity
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

section Homotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {f g : M → N} {F : ℝ × M → N}

/-- **The prism of a smooth simplex under a smooth homotopy is smooth.** Let `H` be a homotopy from
`f` to `g` that is the restriction to `[0, 1] × M` of a smooth map `F : ℝ × M → N`. The simplicial
homotopy `H.toSSet` of singular simplicial sets sends the pairs of a smooth simplex and a vertex map
`⦋n⦌ ⟶ ⦋1⦌` to smooth simplices. -/
theorem range_whiskerRight_ι_comp_toSSet_h_le_smoothSingularSubcomplex
    {f g : TopCat.of M ⟶ TopCat.of N} (H : TopCat.Homotopy f g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F) (hFH : ∀ p : unitInterval × M, F (p.1, p.2) = H p) :
    SSet.Subcomplex.range (((smoothSingularSubcomplex I M).ι ▷ Δ[1]) ≫ H.toSSet.h) ≤
      smoothSingularSubcomplex J N := by
  rintro ⟨k⟩ _ ⟨⟨σ, α⟩, rfl⟩
  induction k using SimplexCategory.rec with | _ n => ?_
  -- The prism simplex is `F` composed with the affine time coordinate of `α` and with `σ`.
  have hval : ∀ x : fullSimplex n,
      ((TopCat.of N).toSSetObjEquiv _
          ((((smoothSingularSubcomplex I M).ι ▷ Δ[1]) ≫ H.toSSet.h).app _ (σ, α)) ∘
        fullSimplexEquivStdSimplex n) x =
      F (simplexMapAmbient (SSet.stdSimplex.objEquiv α) x.val 0,
        SmoothSimplex.toContinuousMap (I := I) σ x) := by
    intro x
    rw [simplexMapAmbient_coe_apply, Fin.succ_zero_eq_one,
      ← SSet.stdSimplex.coe_homeomorph_toSSetObjEquiv_toSSetObjI_app,
      SmoothSimplex.toContinuousMap_apply]
    refine Eq.trans ?_ (hFH (TopCat.I.homeomorph _, _)).symm
    -- The value of the image of `(σ, α)` under `toSSet.map H.h` is that of `H.h` on the pair of
    -- simplices assembled by `μ`, whose components are `σ` and the interval simplex of `α`
    -- (`simplexMap_μ_apply`). Then `H.h (a, b) = H (I.homeomorph b, a)` holds by definition
    -- (`TopCat.Homotopy.h_hom_apply`), and `simplexMap` is `toSSetObjEquiv` read on `ULift`.
    exact congrArg (ConcreteCategory.hom H.h) (TauCeti.TopCat.simplexMap_μ_apply σ.val
      (SSet.stdSimplex.toSSetObjI.app _ α) (ULift.up (fullSimplexEquivStdSimplex n x)))
  rw [mem_smoothSingularSubcomplex_iff, funext hval]
  have hA : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞
      fun y ↦ simplexMapAmbient (SSet.stdSimplex.objEquiv α) y 0 :=
    ((EuclideanSpace.proj (0 : Fin 1)).contDiff.comp
      (simplexMapAmbient (SSet.stdSimplex.objEquiv α)).contDiff).contMDiff
  exact hF.comp_contMDiffOnSubset
    ((hA.contMDiffOnSubset (s := fullSimplex n)).prodMk
      (SmoothSimplex.contMDiffOnSubset_toContinuousMap (I := I) σ))

variable (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
  (H : TopCat.Homotopy (TopCat.ofHom ⟨f, hf.continuous⟩) (TopCat.ofHom ⟨g, hg.continuous⟩))
  (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F) (hFH : ∀ p : unitInterval × M, F (p.1, p.2) = H p)

/-- **A smooth homotopy induces a homotopy of smooth singular subcomplexes.** A homotopy `H` from
`f` to `g` that is the restriction to `[0, 1] × M` of a smooth map `F : ℝ × M → N` induces a
simplicial homotopy between the maps of smooth singular subcomplexes induced by `f` and `g`: the
restriction of the simplicial homotopy `H.toSSet` of singular simplicial sets. -/
def smoothSingularSubcomplexHomotopy :
    SSet.Homotopy (smoothSingularSubcomplexMap f hf) (smoothSingularSubcomplexMap g hg) where
  h := SSet.Subcomplex.lift (((smoothSingularSubcomplex I M).ι ▷ Δ[1]) ≫ H.toSSet.h)
    (range_whiskerRight_ι_comp_toSSet_h_le_smoothSingularSubcomplex H hF hFH)
  h₀ := by
    rw [← cancel_mono (smoothSingularSubcomplex J N).ι, Category.assoc, SSet.Subcomplex.lift_ι,
      SSet.ι₀_comp_assoc, H.toSSet.h₀]
    exact (smoothSingularSubcomplexMap_ι hf).symm
  h₁ := by
    rw [← cancel_mono (smoothSingularSubcomplex J N).ι, Category.assoc, SSet.Subcomplex.lift_ι,
      SSet.ι₁_comp_assoc, H.toSSet.h₁]
    exact (smoothSingularSubcomplexMap_ι hg).symm
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- The homotopy of smooth singular subcomplexes induced by a smooth homotopy is the restriction of
the homotopy of singular simplicial sets. -/
@[reassoc (attr := simp)]
theorem smoothSingularSubcomplexHomotopy_h_ι :
    (smoothSingularSubcomplexHomotopy hf hg H hF hFH).h ≫ (smoothSingularSubcomplex J N).ι =
      ((smoothSingularSubcomplex I M).ι ▷ Δ[1]) ≫ H.toSSet.h :=
  SSet.Subcomplex.lift_ι _
    (range_whiskerRight_ι_comp_toSSet_h_le_smoothSingularSubcomplex H hF hFH)

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C] (R : C)

/-- **The smooth prism operator.** A smooth homotopy from `f` to `g` induces a chain homotopy
between the maps of smooth singular chain complexes induced by `f` and `g`, with coefficients in
`R`. -/
def smoothSingularChainHomotopy :
    Homotopy (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (smoothSingularSubcomplexMap g hg) R) :=
  (smoothSingularSubcomplexHomotopy hf hg H hF hFH).chainComplexMap R

include hF hFH in
/-- **Homotopy invariance of smooth singular homology.** Maps that are homotopic through a homotopy
which is the restriction of a smooth map `ℝ × M → N` induce the same map on smooth singular
homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq [CategoryWithHomology C] (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  (smoothSingularSubcomplexHomotopy hf hg H hF hFH).congr_homologyMap R n

omit hf hg in
/-- Smooth maps `f` and `g` joined by a smooth map `F : ℝ × M → N`, with `F (0, ·) = f` and
`F (1, ·) = g`, induce the same map on smooth singular homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff [CategoryWithHomology C]
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  homologyMap_smoothSingularSubcomplexMap_eq hf hg (homotopyOfRealProd hF.continuous h₀ h₁) hF
    (fun p ↦ (homotopyOfRealProd_apply hF.continuous h₀ h₁ p).symm) R n

end Homotopy

end TauCeti

namespace ContMDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {f g : M → N} {F : ℝ × M → N}

/-- **The smooth prism homotopy from a jointly smooth map on `ℝ × M`.** A smooth map
`F : ℝ × M → N` with `F (0, ·) = f` and `F (1, ·) = g` induces a chain homotopy between the maps
on smooth singular chain complexes induced by `f` and `g`. -/
def smoothSingularChainHomotopy {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F) (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x)
    (R : C) :
    Homotopy
      (SSet.chainComplexMap
        (TauCeti.smoothSingularSubcomplexMap f
          ((hF.comp (contMDiff_const.prodMk contMDiff_id)).congr fun x ↦ (h₀ x).symm)) R)
      (SSet.chainComplexMap
        (TauCeti.smoothSingularSubcomplexMap g
          ((hF.comp (contMDiff_const.prodMk contMDiff_id)).congr fun x ↦ (h₁ x).symm)) R) :=
  TauCeti.smoothSingularChainHomotopy _ _
    (TauCeti.homotopyOfRealProd
      (f := ⟨f, (hF.continuous.comp (continuous_const.prodMk continuous_id)).congr h₀⟩)
      (g := ⟨g, (hF.continuous.comp (continuous_const.prodMk continuous_id)).congr h₁⟩)
      hF.continuous h₀ h₁)
    hF (fun p ↦ (TauCeti.homotopyOfRealProd_apply hF.continuous h₀ h₁ p).symm) R

end ContMDiff

namespace TauCeti

/-! ### Chain homotopy equivalence for subsingleton and smoothly contractible spaces -/

section Contractible

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- On a subsingleton charted space, the inclusion of smooth singular chains into singular chains
is a quasi-isomorphism. -/
instance quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton [Subsingleton M]
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :=
  inferInstance

private def homotopy_ι_comp_constToSmoothSingularSubcomplex
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        SSet.chainComplexMap (constToSmoothSingularSubcomplex I (TopCat.of M) c) R)
      (𝟙 _) := by
  refine (Homotopy.ofEq ?_).trans
    (((smoothSingularChainHomotopy (contMDiff_id (I := I))
      (contMDiff_const : ContMDiff I I ∞ _)
      (topCatHomotopyOfContMDiff (contMDiff_id (I := I)) contMDiff_const hF h₀ h₁)
      hF (fun p ↦ (topCatHomotopyOfContMDiff_apply _ _ _ _ _ p).symm) R).symm).trans
      (Homotopy.ofEq ?_))
  · rw [← Functor.map_comp, ι_comp_constToSmoothSingularSubcomplex]
  · rw [smoothSingularSubcomplexMap_id]
    exact ((SSet.chainComplexFunctor C).obj R).map_id _

private def homotopy_constToSmoothSingularSubcomplex_comp_ι
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    Homotopy
      (SSet.chainComplexMap (constToSmoothSingularSubcomplex I (TopCat.of M) c) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
      (𝟙 _) := by
  refine (Homotopy.ofEq ?_).trans
    ((((topCatHomotopyOfContMDiff (contMDiff_id (I := I))
      (contMDiff_const : ContMDiff I I ∞ _) hF h₀ h₁).toSSet.chainComplexMap R).symm).trans
      (Homotopy.ofEq ?_))
  · rw [← Functor.map_comp, constToSmoothSingularSubcomplex_ι]
    exact congrArg (fun f ↦ SSet.chainComplexMap (TopCat.toSSet.map f) R) (by ext; simp)
  · have hid : (TopCat.ofHom ⟨id, (contMDiff_id (I := I) (n := ∞)).continuous⟩ :
        TopCat.of M ⟶ TopCat.of M) = 𝟙 (TopCat.of M) := by
      ext
      simp
    rw [hid, CategoryTheory.Functor.map_id]
    exact ((SSet.chainComplexFunctor C).obj R).map_id _

/-- **Chain homotopy equivalence on a smoothly contractible charted space.** If `F : ℝ × M → M` is
a smooth homotopy from the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
inclusion of smooth singular chains into singular chains is a chain homotopy equivalence, with
inverse induced by collapsing `M` to the constant smooth `0`-simplex at `c`. -/
def smoothSingularChainHomotopyEquivOfContMDiff
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) where
  hom := SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R
  inv := SSet.chainComplexMap (constToSmoothSingularSubcomplex I (TopCat.of M) c) R
  homotopyHomInvId := homotopy_ι_comp_constToSmoothSingularSubcomplex R hF c h₀ h₁
  homotopyInvHomId := homotopy_constToSmoothSingularSubcomplex_comp_ι R hF c h₀ h₁

/-- The forward map of `smoothSingularChainHomotopyEquivOfContMDiff` is the chain map induced by the
inclusion of smooth singular simplices. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContMDiff_hom
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContMDiff R hF c h₀ h₁).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := by
  rfl

/-- The inverse map of `smoothSingularChainHomotopyEquivOfContMDiff` is the chain map induced by
collapsing `M` to the constant smooth `0`-simplex at `c`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContMDiff_inv
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContMDiff R hF c h₀ h₁).inv =
      SSet.chainComplexMap (constToSmoothSingularSubcomplex I (TopCat.of M) c) R := by
  rfl

/-- On a smoothly contractible charted space, the inclusion of smooth singular chains into singular
chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfContMDiff_hom R hF c h₀ h₁]
  exact (smoothSingularChainHomotopyEquivOfContMDiff R hF c h₀ h₁).quasiIso_hom

end Contractible

end TauCeti

/-! ### Uniqueness up to homotopy, naturality, and subsingleton equivalence -/

section Naturality

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {J₁ : ModelWithCorners ℝ E₁ H₁} {N₁ : Type u} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

namespace TauCeti

/-- Any two chain homotopy equivalences from smooth singular chains to continuous singular chains
whose forward map is the subcomplex inclusion have chain-homotopic inverses. -/
def smoothSingularChainHomotopyInv (R : C)
    (e₁ e₂ : HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R))
    (he₁ : e₁.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (he₂ : e₂.hom = SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :
    Homotopy e₁.inv e₂.inv :=
  e₁.homotopyInvOfHomEq e₂ (he₁.trans he₂.symm)

end TauCeti

open TauCeti

namespace ContMDiff

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

end ContMDiff

end Naturality

section Subsingleton

open TauCeti

namespace ModelWithCorners

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (P : Type u) [TopologicalSpace P] [ChartedSpace H P]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- On a subsingleton manifold `P`, the inclusion of smooth singular chains into continuous
singular chains is an isomorphism of chain complexes, hence a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfSubsingleton [Subsingleton P] (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I P : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of P)).chainComplex R) :=
  HomotopyEquiv.ofIso (((SSet.chainComplexFunctor C).obj R).mapIso
    (asIso (smoothSingularSubcomplex I P).ι))

/-- The forward map of `smoothSingularChainHomotopyEquivOfSubsingleton` is the inclusion of smooth
singular chains into continuous singular chains on `P`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfSubsingleton_hom [Subsingleton P] (R : C) :
    (I.smoothSingularChainHomotopyEquivOfSubsingleton P R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I P).ι R := by
  simp [smoothSingularChainHomotopyEquivOfSubsingleton, HomotopyEquiv.ofIso]

/-- The inverse map of `smoothSingularChainHomotopyEquivOfSubsingleton` is the chain map induced by
`inv (smoothSingularSubcomplex I P).ι`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfSubsingleton_inv [Subsingleton P] (R : C) :
    (I.smoothSingularChainHomotopyEquivOfSubsingleton P R).inv =
      SSet.chainComplexMap (inv (smoothSingularSubcomplex I P).ι) R := by
  simp [smoothSingularChainHomotopyEquivOfSubsingleton, HomotopyEquiv.ofIso]

end ModelWithCorners

end Subsingleton
