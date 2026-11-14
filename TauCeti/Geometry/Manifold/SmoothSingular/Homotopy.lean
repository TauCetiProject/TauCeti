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
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul

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
homology of `M` vanishes (`TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`). This
applies to every star-convex open subset of a real normed space
(`TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`), the contraction being
`(t, x) ↦ c + (1 - ψ t) • (x - c)` for a smooth `ψ : ℝ → [0, 1]` with `ψ 0 = 0` and `ψ 1 = 1`. The
homotopy is required to be smooth on all of `ℝ × M`, not merely on `[0, 1] × M`: a smooth simplex is
locally the restriction of a smooth map on an open subset of `ℝⁿ`, and the affine coordinate `t_α`
takes values outside `[0, 1]` off the simplex.

On such a manifold the inclusion of smooth singular chains into singular chains is a chain
homotopy equivalence (`TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`), hence a
quasi-isomorphism (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`).
Both complexes retract onto the chains of a point: a homotopy inverse sends every singular simplex
to the constant simplex at `c`, and the two composites are joined to the identities by the smooth
prism operator of `F` and by the singular prism operator of the continuous homotopy underlying `F`.
The inclusion is also a quasi-isomorphism on the empty manifold, where both complexes vanish
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`). Together these cover
every *star-convex chart domain* of a manifold over a model with corners: for an open `s ⊆ E`
with `s ∩ range I` star-convex and contained in the target of the extended chart at `x`, the chart
identifies `(chartAt H x).source ∩ (extChartAt I x)⁻¹' s` with `s ∩ range I`, and the straight-line
contraction of `s ∩ range I`, read through the chart, is smooth on the chart domain
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage`).
The contraction stays in `range I`, so boundary and corners are allowed.

These are the inputs, homotopy invariance and the comparison on convex coordinate domains, of the
comparison of smooth with continuous singular homology by a Mayer–Vietoris induction.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplexHomotopy`: a smooth homotopy induces a simplicial homotopy of
  the maps of smooth singular subcomplexes, restricting the homotopy of singular simplicial sets.
* `TauCeti.smoothSingularChainHomotopy`: the induced chain homotopy of smooth singular chains.
* `TauCeti.homologyMap_smoothSingularSubcomplexMap_eq`: smoothly homotopic maps induce the same map
  on smooth singular homology.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`: a smoothly contractible manifold
  has no smooth singular homology in positive degrees.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`: neither has a star-convex open
  subset of a normed space.
* `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`: on a smoothly
  contractible manifold, smooth singular chains include into singular chains by a chain homotopy
  equivalence, hence by a quasi-isomorphism.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`: the same on the empty
  manifold.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage`:
  the same on a star-convex chart domain, and on a convex one by its `_of_convex` variant.

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

include hF hFH in
/-- **Homotopy invariance of smooth singular homology.** Maps that are homotopic through a homotopy
which is the restriction of a smooth map `ℝ × M → N` induce the same map on smooth singular
homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq [CategoryWithHomology C] (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  (smoothSingularSubcomplexHomotopy hf hg H hF hFH).congr_homologyMap R n

omit hf hg in
/-- The homotopy from `f` to `g` obtained by restricting to `[0, 1] × M` a continuous map
`F : ℝ × M → N` with `F (0, ·) = f` and `F (1, ·) = g`. -/
private def homotopyOfContinuous (hfc : Continuous f) (hgc : Continuous g) (hFc : Continuous F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    TopCat.Homotopy (TopCat.ofHom ⟨f, hfc⟩) (TopCat.ofHom ⟨g, hgc⟩) where
  toFun p := F (p.1, p.2)
  continuous_toFun := hFc.comp (continuous_subtype_val.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

omit hf hg in
/-- Smooth maps `f` and `g` joined by a smooth map `F : ℝ × M → N`, with `F (0, ·) = f` and
`F (1, ·) = g`, induce the same map on smooth singular homology. -/
theorem homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff [CategoryWithHomology C]
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) (hF : ContMDiff (𝓘(ℝ).prod I) J ∞ F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n :=
  homologyMap_smoothSingularSubcomplexMap_eq hf hg
    (homotopyOfContinuous hf.continuous hg.continuous hF.continuous h₀ h₁) hF (fun _ ↦ rfl) R n

end SmoothHomotopy

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C] (R : C)

/-! ### Smoothly contractible manifolds -/

variable (I) in
/-- The point `c` of `M`, read on the singular simplices of a point: every such simplex is
constant, so smooth in `M`. -/
private def smoothSingularSubcomplexOfPoint (c : M) :
    TopCat.toSSet.obj (TopCat.of PUnit.{u + 1}) ⟶ (smoothSingularSubcomplex I M : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const _ c))) (by
    rintro k _ ⟨σ, rfl⟩
    rw [mem_smoothSingularSubcomplex_iff]
    exact contMDiffOnSubset_const I ∞ c)

@[reassoc (attr := simp)]
private theorem smoothSingularSubcomplexOfPoint_ι (c : M) :
    smoothSingularSubcomplexOfPoint I c ≫ (smoothSingularSubcomplex I M).ι =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const _ c)) :=
  SSet.Subcomplex.lift_ι _ _

variable (M) in
/-- The map `M → pt` to a point, as a map of topological spaces. -/
private abbrev toPoint : TopCat.of M ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom (ContinuousMap.const M PUnit.unit)

/-- The constant map `c`, read on singular simplices, factors through the singular simplicial set
of a point. -/
private theorem toPoint_comp_const (c : M) :
    toPoint M ≫
        (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} c) : TopCat.of PUnit ⟶ TopCat.of M) =
      TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩ := by
  ext
  rfl

/-- Mapping a smooth simplex to a point and reading the result in `M` at `c` is the map of smooth
singular subcomplexes induced by the constant map `c`. -/
private theorem ι_toPoint_smoothSingularSubcomplexOfPoint (c : M) :
    (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (toPoint M) ≫
        smoothSingularSubcomplexOfPoint I c =
      smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) := by
  rw [← cancel_mono (smoothSingularSubcomplex I M).ι, smoothSingularSubcomplexMap_ι,
    Category.assoc, Category.assoc, smoothSingularSubcomplexOfPoint_ι, ← Functor.map_comp,
    toPoint_comp_const]

/-- **A smoothly contractible manifold has the smooth singular homology of a point.** If a smooth
map `F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
smooth singular homology of `M` vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I M : SSet).homology R n) := by
  -- The constant map factors through the singular simplicial set of a point.
  have hpt : IsZero ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).homology R n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R _ hn
  have hid : SSet.homologyMap (smoothSingularSubcomplexMap id (contMDiff_id (I := I))) R n =
      SSet.homologyMap (((smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (toPoint M)) ≫
        smoothSingularSubcomplexOfPoint I c) R n := by
    rw [Category.assoc, ι_toPoint_smoothSingularSubcomplexOfPoint]
    exact homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const hF
      h₀ h₁ n
  rw [smoothSingularSubcomplexMap_id, SSet.homologyMap_id, SSet.homologyMap_comp] at hid
  rw [IsZero.iff_id_eq_zero, hid,
    hpt.eq_of_src (SSet.homologyMap (smoothSingularSubcomplexOfPoint I c) R n) 0, comp_zero]

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
  inv := SSet.chainComplexMap
    (TopCat.toSSet.map (toPoint M) ≫ smoothSingularSubcomplexOfPoint I c) R
  homotopyHomInvId := by
    -- The composite on smooth chains is induced by the constant map `c`, and the smooth prism
    -- operator of `F` joins it to the identity.
    refine (Homotopy.ofEq ?_).trans ((smoothSingularChainHomotopy contMDiff_id contMDiff_const
      (homotopyOfContinuous continuous_id continuous_const hF.continuous h₀ h₁) hF (fun _ ↦ rfl)
      R).symm.trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp, ι_toPoint_smoothSingularSubcomplexOfPoint]
    · rw [smoothSingularSubcomplexMap_id]
      exact ((SSet.chainComplexFunctor C).obj R).map_id _
  homotopyInvHomId := by
    -- The composite on singular chains is induced by the constant map `c`, and the homotopy
    -- underlying `F` joins it to the identity.
    refine (Homotopy.ofEq ?_).trans (((homotopyOfContinuous continuous_id continuous_const
      hF.continuous h₀ h₁).toSSet.chainComplexMap R).symm.trans (Homotopy.ofEq ?_))
    · rw [← Functor.map_comp, Category.assoc, smoothSingularSubcomplexOfPoint_ι,
        ← Functor.map_comp, toPoint_comp_const]
    · -- `TopCat.ofHom_id` is stated for `ContinuousMap.id`, which is `⟨id, continuous_id⟩`.
      rw [show (TopCat.ofHom ⟨id, continuous_id⟩ : TopCat.of M ⟶ TopCat.of M) = 𝟙 _ from
        TopCat.ofHom_id, TopCat.toSSet.map_id]
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

/-- On a manifold whose identity is joined to a constant map by a smooth map `ℝ × M → M`, the
inclusion of smooth singular chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfContMDiff_hom R hF c h₀ h₁]
  infer_instance

/-- **A star-convex open subset has vanishing positive-degree smooth singular homology.**
The smooth contraction `(t, x) ↦ c + (1 - ψ t) • (x - c)` towards the centre `c`, with `ψ` the
smooth transition function from `0` to `1`, stays in the subset, so its smooth singular homology
vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_starConvex [CategoryWithHomology C]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).homology R n) := by
  rcases (U : Set V).eq_empty_or_nonempty with hempty | hne
  · -- An empty open set has no smooth simplices at all.
    have : (smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).HasDimensionLT 0 := by
      refine (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦ ?_
      have hx : ((TopCat.of U).toSSetObjEquiv _ σ.1 (StdSimplex.single 0) : V) ∈ (U : Set V) :=
        ((TopCat.of U).toSSetObjEquiv _ σ.1 (StdSimplex.single 0)).2
      rw [hempty] at hx
      exact hx
    exact (HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)
  have hmem : ∀ p : ℝ × U, c + (1 - Real.smoothTransition p.1) • ((p.2 : V) - c) ∈ U :=
    fun p ↦ hU.add_smul_sub_mem p.2.2 (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  let F : ℝ × U → U := fun p ↦ ⟨_, hmem p⟩
  have hF : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ F := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    have hψ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞ fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have hx : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ fun p : ℝ × U ↦ (p.2 : V) :=
      contMDiff_subtype_val.comp contMDiff_snd
    exact ContMDiff.add contMDiff_const
      (ContMDiff.smul (ContMDiff.sub contMDiff_const hψ) (hx.sub contMDiff_const))
  exact isZero_homology_smoothSingularSubcomplex_of_contMDiff R hF ⟨c, hU.mem hne⟩
    (fun x ↦ Subtype.ext (by simp [F, Real.smoothTransition.zero]))
    (fun x ↦ Subtype.ext (by simp [F, Real.smoothTransition.one])) hn

/-! ### The empty manifold -/

section Empty

variable (I M) in
/-- On the empty manifold the inclusion of smooth singular chains into singular chains is a
quasi-isomorphism, both chain complexes being zero. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty [CategoryWithHomology C]
    [IsEmpty M] :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  -- The singular simplicial set of the empty space has no simplices, nor does its subcomplex.
  have hT : (TopCat.toSSet.obj (TopCat.of M)).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ)
  have hS : (smoothSingularSubcomplex I M : SSet).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ.1)
  have : IsIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :=
    ⟨0, (SSet.isZero_chainComplex _ R).eq_of_src _ _, (SSet.isZero_chainComplex _ R).eq_of_src _ _⟩
  infer_instance

end Empty

/-! ### Convex chart domains -/

section ChartDomain

variable [IsManifold I ∞ M] [CategoryWithHomology C]

/-- **Smooth singular chains of a star-convex chart domain.** Let `s ⊆ E` be open, with
`s ∩ range I` star-convex and contained in the target of the extended chart at `x`. On the open
set `(chartAt H x).source ∩ (extChartAt I x)⁻¹' s`, which the chart identifies with `s ∩ range I`,
the inclusion of smooth singular chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage
    (x : M) {s : Set E} (hs : IsOpen s) {c : E} (hsc : StarConvex ℝ c (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M)).ι R) := by
  set D : TopologicalSpace.Opens M :=
    ⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩
  set e := extChartAt I x
  rcases (D : Set M).eq_empty_or_nonempty with hD | ⟨y₀, hy₀⟩
  · have : IsEmpty D := Set.isEmpty_coe_sort.2 hD
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty I D R
  -- The chart sends `D` into `s ∩ range I`.
  have hmem : ∀ y : D, e y ∈ s ∩ range I := fun y ↦
    ⟨y.2.2, extChartAt_target_subset_range x
      (e.map_source (by rw [extChartAt_source]; exact y.2.1))⟩
  -- The straight-line contraction of `s ∩ range I` onto `c`, read through the chart.
  let G : ℝ × D → E := fun p ↦ c + (1 - Real.smoothTransition p.1) • (e p.2 - c)
  have hG : ∀ p, G p ∈ s ∩ range I := fun p ↦
    hsc.add_smul_sub_mem (hmem p.2) (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hGD : ∀ p, e.symm (G p) ∈ (D : Set M) := fun p ↦
    ⟨by rw [← extChartAt_source I]; exact e.map_target (hst (hG p)),
      by rw [mem_preimage, e.right_inv (hst (hG p))]; exact (hG p).1⟩
  let F : ℝ × D → D := fun p ↦ ⟨e.symm (G p), hGD p⟩
  have hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    have he : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × D ↦ e p.2 :=
      contMDiffOn_extChartAt.comp_contMDiff (contMDiff_subtype_val.comp contMDiff_snd)
        fun p ↦ p.2.2.1
    have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × D ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    exact (contMDiffOn_extChartAt_symm x).comp_contMDiff
      (contMDiff_const.add ((contMDiff_const.sub hψ).smul (he.sub contMDiff_const)))
      fun p ↦ hst (hG p)
  have hc' : e.symm c ∈ (D : Set M) := by
    simpa [G, Real.smoothTransition.one] using hGD (1, ⟨y₀, hy₀⟩)
  refine quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF ⟨e.symm c, hc'⟩
    (fun y ↦ Subtype.ext ?_) (fun y ↦ Subtype.ext ?_)
  · simp only [F, G, Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact e.left_inv (by rw [extChartAt_source]; exact y.2.1)
  · simp [F, G, Real.smoothTransition.one]

/-- **Smooth singular chains of a convex chart domain.** Let `s ⊆ E` be open, with `s ∩ range I`
convex and contained in the target of the extended chart at `x`. On the open set
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' s` the inclusion of smooth singular chains into
singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage_of_convex
    (x : M) {s : Set E} (hs : IsOpen s) (hsc : Convex ℝ (s ∩ range I))
    (hst : s ∩ range I ⊆ (extChartAt I x).target) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I
      (⟨(chartAt H x).source ∩ extChartAt I x ⁻¹' s, isOpen_extChartAt_preimage x hs⟩ :
        TopologicalSpace.Opens M)).ι R) := by
  rcases (s ∩ range I).eq_empty_or_nonempty with h | ⟨c, hc⟩
  · exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage R x hs
      (c := 0) (h ▸ starConvex_empty 0) hst
  · exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_chartAt_source_inter_preimage R x hs
      (hsc.starConvex hc) hst

end ChartDomain

end TauCeti
