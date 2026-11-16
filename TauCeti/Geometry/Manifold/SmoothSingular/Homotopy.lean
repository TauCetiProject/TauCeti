/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

These are the inputs, homotopy invariance and the acyclicity of convex coordinate domains, of the
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
  homologyMap_smoothSingularSubcomplexMap_eq hf hg
    { toFun := fun p ↦ F (p.1, p.2)
      continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
      map_zero_left := h₀
      map_one_left := h₁ } hF (fun _ ↦ rfl) R n

/-! ### Smoothly contractible manifolds -/

omit hf hg in
/-- **A smoothly contractible manifold has the smooth singular homology of a point.** If a smooth
map `F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
smooth singular homology of `M` vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I M : SSet).homology R n) := by
  let pt : TopCat.{u} := TopCat.of PUnit
  -- The constant map factors through the singular simplicial set of a point.
  let a : TopCat.of M ⟶ pt := TopCat.ofHom (ContinuousMap.const M PUnit.unit)
  let b : pt ⟶ TopCat.of M := TopCat.ofHom (ContinuousMap.const pt c)
  have hab : a ≫ b = TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩ := by
    ext
    rfl
  let p : (smoothSingularSubcomplex I M : SSet) ⟶ TopCat.toSSet.obj pt :=
    (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map a
  let s : TopCat.toSSet.obj pt ⟶ (smoothSingularSubcomplex I M : SSet) :=
    SSet.Subcomplex.lift (TopCat.toSSet.map b) (by
      rintro k _ ⟨σ, rfl⟩
      rw [mem_smoothSingularSubcomplex_iff]
      exact contMDiffOnSubset_const I ∞ c)
  have hs : s ≫ (smoothSingularSubcomplex I M).ι = TopCat.toSSet.map b :=
    SSet.Subcomplex.lift_ι _ _
  have hps : smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) =
      p ≫ s := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι, smoothSingularSubcomplexMap_ι,
      Category.assoc, hs, Category.assoc, ← Functor.map_comp, hab]
  have hpt : IsZero ((TopCat.toSSet.obj pt).homology R n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R pt hn
  have hid : SSet.homologyMap (smoothSingularSubcomplexMap id (contMDiff_id (I := I))) R n =
      SSet.homologyMap (p ≫ s) R n := by
    rw [← hps]
    exact homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const hF
      h₀ h₁ n
  rw [smoothSingularSubcomplexMap_id, SSet.homologyMap_id, SSet.homologyMap_comp] at hid
  rw [IsZero.iff_id_eq_zero, hid, hpt.eq_of_src (SSet.homologyMap s R n) 0, comp_zero]

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

end TauCeti
