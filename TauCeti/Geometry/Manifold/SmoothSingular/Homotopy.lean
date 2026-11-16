/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Geometry.Manifold.ContMDiff.Contraction
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import TauCeti.Topology.Homotopy.Real

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

Consequently a smoothly contractible manifold has the smooth singular homology of a point: if the
identity of `M` is smoothly homotopic to a constant map, the positive-degree smooth singular
homology of `M` vanishes (`TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`). The
homotopy is required to be smooth on all of `ℝ × M`, not merely on `[0, 1] × M`: a smooth simplex
is locally the restriction of a smooth map on an open subset of `ℝⁿ`, and the affine coordinate
`t_α` takes values outside `[0, 1]` off the simplex.

Let `M` be smoothly contractible, through a smooth map `F : ℝ × M → M` from the identity to the
constant map at a point `c : M`. Then the inclusion of smooth singular chains into singular chains
is a chain homotopy equivalence (`TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`), hence a
quasi-isomorphism (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`).
Both complexes retract onto the chains of a point: a homotopy inverse sends every singular simplex
to the constant simplex at `c`, and the two composites are joined to the identities by the smooth
prism operator of `F` and by the singular prism operator of the continuous homotopy underlying `F`.
The inclusion is also a quasi-isomorphism on the empty manifold, where both complexes vanish
(`TauCeti.smoothSingularSubcomplex_eq_top`).

A *star-convex chart domain* is an open `U` in the source of a chart `e` of the maximal smooth
atlas whose image `e.extend I '' U` is star-convex; boundary and corners are allowed. If nonempty,
it is smoothly contractible (`TauCeti.exists_contMDiff_contraction_of_starConvex`). So its smooth
singular homology vanishes in positive degrees
(`TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`), and the inclusion of its smooth
singular chains into singular chains is a chain homotopy equivalence
(`TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`). In particular this holds on the domains
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' s` of the preferred charts, for an open `s ⊆ E` with
`s ∩ range I` star-convex and contained in the target of the extended chart at `x`
(`TauCeti.smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfStarConvex`).

These are the inputs, homotopy invariance and the comparison on convex coordinate domains, of the
comparison of smooth with continuous singular homology by a Mayer–Vietoris induction.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplexHomotopy`: a smooth homotopy induces a simplicial homotopy of
  the maps of smooth singular subcomplexes, restricting the homotopy of singular simplicial sets.
* `TauCeti.smoothSingularChainHomotopy`: the induced chain homotopy of smooth singular chains.
* `TauCeti.smoothSingularSubcomplexHomotopyOfContMDiff`,
  `TauCeti.smoothSingularChainHomotopyOfContMDiff`: the same constructions directly from a jointly
  smooth real-parameter family and its endpoint equations.
* `TauCeti.homologyMap_smoothSingularSubcomplexMap_eq`: smoothly homotopic maps induce the same map
  on smooth singular homology.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`: a smoothly contractible manifold
  has no smooth singular homology in positive degrees.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`: a star-convex chart domain
  has no smooth singular homology in positive degrees.
* `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`: on a smoothly
  contractible manifold, smooth singular chains include into singular chains by a chain homotopy
  equivalence, hence by a quasi-isomorphism.
* `TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`,
  `TauCeti.smoothSingularChainHomotopyEquivOfConvex`: chain homotopy equivalences on star-convex
  and convex chart domains, respectively.
* `TauCeti.smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfStarConvex`,
  `TauCeti.smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfConvex`: their forms on the
  domains `(chartAt H x).source ∩ (extChartAt I x)⁻¹' s`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Smooth Singular Homology*,
  proof of Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial Opposite Set Convexity
open scoped Manifold ContDiff

universe u

namespace TauCeti

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
      F (simplexMapAmbient (SSet.stdSimplex.objEquiv α) x.1 0,
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
    exact congrArg (ConcreteCategory.hom H.h) (TauCeti.TopCat.simplexMap_μ_apply σ.1
      (SSet.stdSimplex.toSSetObjI.app _ α) (ULift.up (fullSimplexEquivStdSimplex n x)))
  rw [mem_smoothSingularSubcomplex_iff, funext hval]
  have hA : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞
      fun y ↦ simplexMapAmbient (SSet.stdSimplex.objEquiv α) y 0 :=
    ((EuclideanSpace.proj (0 : Fin 1)).contDiff.comp
      (simplexMapAmbient (SSet.stdSimplex.objEquiv α)).contDiff).contMDiff
  exact hF.comp_contMDiffOnSubset
    ((hA.contMDiffOnSubset (s := fullSimplex n)).prodMk
      (SmoothSimplex.contMDiffOnSubset_toContinuousMap (I := I) σ))

section SmoothHomotopy

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

/-- The smooth prism operator is the chain homotopy induced by the simplicial homotopy of smooth
singular subcomplexes. -/
theorem smoothSingularChainHomotopy_def :
    smoothSingularChainHomotopy hf hg H hF hFH R =
      (smoothSingularSubcomplexHomotopy hf hg H hF hFH).chainComplexMap R :=
  (rfl)

include hF hFH in
/-- **Homotopy invariance of smooth singular homology.** Maps that are homotopic through a homotopy
which is the restriction of a smooth map `ℝ × M → N` induce the same map on smooth singular
homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq [CategoryWithHomology C] (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  (smoothSingularSubcomplexHomotopy hf hg H hF hFH).congr_homologyMap R n

omit hf hg in
/-- A jointly smooth real-parameter family induces a homotopy of smooth singular subcomplexes. -/
def smoothSingularSubcomplexHomotopyOfContMDiff
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    SSet.Homotopy (smoothSingularSubcomplexMap f hf) (smoothSingularSubcomplexMap g hg) :=
  smoothSingularSubcomplexHomotopy hf hg
    (ContinuousMap.Homotopy.ofReal hF.continuous h₀ h₁) hF
    (fun p ↦ (ContinuousMap.Homotopy.ofReal_apply hF.continuous h₀ h₁ p).symm)

omit hf hg in
/-- The homotopy from a jointly smooth family restricts the underlying singular homotopy. -/
@[reassoc (attr := simp)]
theorem smoothSingularSubcomplexHomotopyOfContMDiff_h_ι
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    (smoothSingularSubcomplexHomotopyOfContMDiff hf hg hF h₀ h₁).h ≫
        (smoothSingularSubcomplex J N).ι =
      ((smoothSingularSubcomplex I M).ι ▷ Δ[1]) ≫
        (TopCat.Homotopy.toSSet (f := TopCat.ofHom ⟨f, hf.continuous⟩)
          (g := TopCat.ofHom ⟨g, hg.continuous⟩)
          (ContinuousMap.Homotopy.ofReal hF.continuous h₀ h₁)).h :=
  smoothSingularSubcomplexHomotopy_h_ι _ _ _ _ _

omit hf hg in
/-- The smooth prism operator of a jointly smooth real-parameter family. -/
def smoothSingularChainHomotopyOfContMDiff
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    Homotopy (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (smoothSingularSubcomplexMap g hg) R) :=
  (smoothSingularSubcomplexHomotopyOfContMDiff hf hg hF h₀ h₁).chainComplexMap R

omit hf hg in
/-- The smooth prism operator of a jointly smooth family is the chain homotopy induced by its
homotopy of smooth singular subcomplexes. -/
theorem smoothSingularChainHomotopyOfContMDiff_def
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    smoothSingularChainHomotopyOfContMDiff R hf hg hF h₀ h₁ =
      (smoothSingularSubcomplexHomotopyOfContMDiff hf hg hF h₀ h₁).chainComplexMap R :=
  (rfl)

omit hf hg in
/-- Smooth maps `f` and `g` joined by a smooth map `F : ℝ × M → N`, with `F (0, ·) = f` and
`F (1, ·) = g`, induce the same map on smooth singular homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff [CategoryWithHomology C]
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  (smoothSingularSubcomplexHomotopyOfContMDiff hf hg hF h₀ h₁).congr_homologyMap R n

end SmoothHomotopy

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C] (R : C)

/-! ### Smoothly contractible manifolds -/

/-- **A smoothly contractible manifold has the smooth singular homology of a point.** If a smooth
map `F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
smooth singular homology of `M` vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I M : SSet).homology R n) := by
  -- The constant map factors through the singular simplicial set of a point (`SSet.comp_const`).
  have hpt : IsZero ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).homology R n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R _ hn
  let y := (SmoothSimplex.equiv₀ I M).symm c
  have hid : SSet.homologyMap (smoothSingularSubcomplexMap id (contMDiff_id (I := I))) R n =
      SSet.homologyMap (SSet.const ((TopCat.of PUnit.{u + 1}).toSSetObj₀Equiv.symm PUnit.unit) ≫
        SSet.const y) R n := by
    rw [SSet.comp_const, ← smoothSingularSubcomplexMap_const c (contMDiff_const (I := I) (I' := I))]
    exact homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const hF
      h₀ h₁ n
  rw [smoothSingularSubcomplexMap_id, SSet.homologyMap_id, SSet.homologyMap_comp] at hid
  rw [IsZero.iff_id_eq_zero, hid,
    hpt.eq_of_src (SSet.homologyMap (SSet.const y) R n) 0, comp_zero]

/-- **Smooth singular chains of a smoothly contractible manifold.** If a smooth map
`F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
inclusion of smooth singular chains into singular chains, with coefficients in `R`, is a chain
homotopy equivalence. A homotopy inverse sends every singular simplex to the constant simplex at
`c`. -/
def smoothSingularChainHomotopyEquivOfContMDiff {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) where
  hom := SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R
  inv := SSet.chainComplexMap (SSet.const ((SmoothSimplex.equiv₀ I M).symm c)) R
  homotopyHomInvId := by
    -- The composite on smooth chains is induced by the constant map `c`, and the smooth prism
    -- operator of `F` joins it to the identity.
    refine (Homotopy.ofEq ?_).trans ((smoothSingularChainHomotopyOfContMDiff R
      contMDiff_id contMDiff_const hF h₀ h₁).symm.trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp, SSet.comp_const, smoothSingularSubcomplexMap_const]
    · rw [smoothSingularSubcomplexMap_id]
      exact ((SSet.chainComplexFunctor C).obj R).map_id _
  homotopyInvHomId := by
    -- The composite on singular chains is induced by the constant map `c`, and the homotopy
    -- underlying `F` joins it to the identity.
    let H : TopCat.Homotopy (𝟙 (TopCat.of M)) (TopCat.const c) :=
      ContinuousMap.Homotopy.ofReal hF.continuous h₀ h₁
    refine (Homotopy.ofEq ?_).trans
      ((H.toSSet.chainComplexMap R).symm.trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp, SSet.const_comp, TopCat.toSSet_map_const]
      simp
    · rw [TopCat.toSSet.map_id]
      exact ((SSet.chainComplexFunctor C).obj R).map_id _

/-- The chain homotopy equivalence of a smoothly contractible manifold is the inclusion of smooth
singular chains into singular chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContMDiff_hom {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContMDiff R hF c h₀ h₁).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  (rfl)

/-- The homotopy inverse of the chain homotopy equivalence of a smoothly contractible manifold
sends every singular simplex to the constant simplex at the contraction point. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContMDiff_inv {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContMDiff R hF c h₀ h₁).inv =
      SSet.chainComplexMap (SSet.const ((SmoothSimplex.equiv₀ I M).symm c)) R :=
  (rfl)

/-- On a manifold whose identity is joined to a constant map by a smooth map `ℝ × M → M`, the
inclusion of smooth singular chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfContMDiff_hom R hF c h₀ h₁]
  infer_instance

/-! ### Star-convex chart domains -/

/-- **A star-convex chart domain has vanishing positive-degree smooth singular homology.** Let
`U` be an open subset of the source of a chart `e` in the maximal smooth atlas of `M`, whose image
under the extended chart `e.extend I` is star-convex. Then the smooth singular homology of `U`
vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_starConvex [CategoryWithHomology C]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : TopologicalSpace.Opens M} (hUe : (U : Set M) ⊆ e.source) {c : E}
    (hUc : StarConvex ℝ c (e.extend I '' U)) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I U : SSet).homology R n) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · -- An empty open set is totally disconnected, so all of its simplices are smooth.
    exact IsZero.of_iso
      (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R
        (TopCat.of U) hn)
      ((SSet.homologyFunctor R n).mapIso (asIso (smoothSingularSubcomplex I U).ι))
  obtain ⟨F, c', hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex he hUe hUc
  exact isZero_homology_smoothSingularSubcomplex_of_contMDiff R hF c' h₀ h₁ hn

/-- **Smooth singular chains of a star-convex chart domain.** Let `U` be an open subset of the
source of a chart `e` in the maximal smooth atlas of `M`, whose image under the extended chart
`e.extend I` is star-convex. Then the inclusion of smooth singular chains of `U` into singular
chains is a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfStarConvex {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {U : TopologicalSpace.Opens M}
    (hUe : (U : Set M) ⊆ e.source) {c : E} (hUc : StarConvex ℝ c (e.extend I '' U)) :
    HomotopyEquiv ((smoothSingularSubcomplex I U : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R) := by
  classical
  exact if hU : IsEmpty U then
    HomotopyEquiv.ofIso (asIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
  else by
    have : Nonempty U := not_isEmpty_iff.mp hU
    choose F c' hF h₀ h₁ using exists_contMDiff_contraction_of_starConvex he hUe hUc
    exact smoothSingularChainHomotopyEquivOfContMDiff R hF c' h₀ h₁

/-- The equivalence on a star-convex chart domain uses the inclusion of smooth chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfStarConvex_hom {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {U : TopologicalSpace.Opens M}
    (hUe : (U : Set M) ⊆ e.source) {c : E} (hUc : StarConvex ℝ c (e.extend I '' U)) :
    (smoothSingularChainHomotopyEquivOfStarConvex R he hUe hUc).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  dsimp only
  split <;> rfl

/-- On a star-convex chart domain the inclusion of smooth chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex [CategoryWithHomology C]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : TopologicalSpace.Opens M} (hUe : (U : Set M) ⊆ e.source) {c : E}
    (hUc : StarConvex ℝ c (e.extend I '' U)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfStarConvex_hom R he hUe hUc]
  infer_instance

/-- **Smooth singular chains of a convex chart domain.** Let `U` be an open subset of the source of
a chart `e` in the maximal smooth atlas of `M`, whose image under the extended chart `e.extend I`
is convex. Then the inclusion of smooth singular chains of `U` into singular chains is a chain
homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfConvex {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {U : TopologicalSpace.Opens M}
    (hUe : (U : Set M) ⊆ e.source) (hUc : Convex ℝ (e.extend I '' U)) :
    HomotopyEquiv ((smoothSingularSubcomplex I U : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R) := by
  classical
  exact if h : (e.extend I '' U).Nonempty then
    smoothSingularChainHomotopyEquivOfStarConvex R he hUe (hUc.starConvex h.choose_spec)
  else
    smoothSingularChainHomotopyEquivOfStarConvex R he hUe (c := 0)
      (Set.not_nonempty_iff_eq_empty.mp h ▸ starConvex_empty 0)

/-- The equivalence on a convex chart domain uses the inclusion of smooth chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfConvex_hom {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {U : TopologicalSpace.Opens M}
    (hUe : (U : Set M) ⊆ e.source) (hUc : Convex ℝ (e.extend I '' U)) :
    (smoothSingularChainHomotopyEquivOfConvex R he hUe hUc).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R := by
  unfold smoothSingularChainHomotopyEquivOfConvex
  split <;> simp only [smoothSingularChainHomotopyEquivOfStarConvex_hom]

/-- On a convex chart domain the inclusion of smooth chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convex [CategoryWithHomology C]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : TopologicalSpace.Opens M} (hUe : (U : Set M) ⊆ e.source)
    (hUc : Convex ℝ (e.extend I '' U)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfConvex_hom R he hUe hUc]
  infer_instance

/-! ### Chart domains of the preferred charts -/

section ChartAt

variable [IsManifold I ∞ M]

/-- **Smooth singular chains of a star-convex chart domain at `x`.** Let `s ⊆ E` be open, with
`s ∩ range I` star-convex and contained in the target of the extended chart at `x`. On the open
set `(chartAt H x).source ∩ (extChartAt I x)⁻¹' s`, which the chart identifies with `s ∩ range I`,
the inclusion of smooth singular chains into singular chains is a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfStarConvex
    (x : M) {s : Set E} (hs : IsOpen s) {c : E} (hsc : StarConvex ℝ c (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    HomotopyEquiv ((smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M) : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of
        (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
          TopologicalSpace.Opens M))).chainComplex R) :=
  smoothSingularChainHomotopyEquivOfStarConvex R (IsManifold.chart_mem_maximalAtlas x)
    inter_subset_left (extChartAt_image_chartAt_source_inter_preimage x hst ▸ hsc)

/-- The equivalence on a star-convex chart domain at `x` uses the inclusion of smooth chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfStarConvex_hom
    (x : M) {s : Set E} (hs : IsOpen s) {c : E} (hsc : StarConvex ℝ c (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    (smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfStarConvex R x hs hsc hst).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I
        (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
          TopologicalSpace.Opens M)).ι R :=
  smoothSingularChainHomotopyEquivOfStarConvex_hom R _ _ _

/-- On a star-convex chart domain at `x` the inclusion of smooth chains is a quasi-isomorphism. -/
theorem
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage_of_starConvex
    [CategoryWithHomology C]
    (x : M) {s : Set E} (hs : IsOpen s) {c : E} (hsc : StarConvex ℝ c (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M)).ι R) :=
  quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex R
    (IsManifold.chart_mem_maximalAtlas x) inter_subset_left
    (extChartAt_image_chartAt_source_inter_preimage x hst ▸ hsc)

/-- **Smooth singular chains of a convex chart domain at `x`.** Let `s ⊆ E` be open, with
`s ∩ range I` convex and contained in the target of the extended chart at `x`. On the open set
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' s` the inclusion of smooth singular chains into
singular chains is a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfConvex
    (x : M) {s : Set E} (hs : IsOpen s) (hsc : Convex ℝ (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    HomotopyEquiv ((smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M) : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of
        (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
          TopologicalSpace.Opens M))).chainComplex R) :=
  smoothSingularChainHomotopyEquivOfConvex R (IsManifold.chart_mem_maximalAtlas x)
    inter_subset_left (extChartAt_image_chartAt_source_inter_preimage x hst ▸ hsc)

/-- The equivalence on a convex chart domain at `x` uses the inclusion of smooth chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfConvex_hom
    (x : M) {s : Set E} (hs : IsOpen s) (hsc : Convex ℝ (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    (smoothSingularChainHomotopyEquivChartAtSourceInterPreimageOfConvex R x hs hsc hst).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I
        (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
          TopologicalSpace.Opens M)).ι R :=
  smoothSingularChainHomotopyEquivOfConvex_hom R _ _ _

/-- On a convex chart domain at `x` the inclusion of smooth chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage_of_convex
    [CategoryWithHomology C]
    (x : M) {s : Set E} (hs : IsOpen s) (hsc : Convex ℝ (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M)).ι R) :=
  quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convex R
    (IsManifold.chart_mem_maximalAtlas x) inter_subset_left
    (extChartAt_image_chartAt_source_inter_preimage x hst ▸ hsc)

end ChartAt

end TauCeti
