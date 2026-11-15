/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

import TauCeti.Topology.MayerVietoris

/-!
# The smoothing theorem for smooth singular chains

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a real model with corners
`I : ModelWithCorners ℝ E H` over a finite-dimensional normed vector space `E`. This file proves
Lee's smoothing theorem (Theorem 18.7): the inclusion of smooth singular chains into ordinary
singular chains is a quasi-isomorphism for arbitrary coefficients in an abelian category in which
countable coproducts are exact (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`),
and a chain homotopy equivalence when the coefficient object `R` is projective
(`TauCeti.smoothSingularChainHomotopyEquiv`), covering in particular coefficients in `ℝ`, in `ℤ`,
or in any projective module over a ring.

Because `M` may have boundary or corners, relative Whitney approximation simplex-by-simplex over
the skeleta is unavailable: a continuous simplex into `[0, ∞)` whose coordinate faces are smooth
need not be homotopic relative to its boundary to a smooth simplex. Instead, the proof proceeds by
two stages of Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`):

1. **Smoothly contractible spaces.** Whenever `M` admits a smooth contraction `F : ℝ × M → M` from
   the identity to a constant map, factoring the constant map through a point constructs an explicit
   chain homotopy equivalence `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff` between smooth
   and continuous singular chains in all degrees simultaneously.
2. **Extended chart domains.** For each `x : M`, the open subsets of `(extChartAt I x).source`
   whose image under `extChartAt I x` is convex in `E` form an intersection-stable basis: `range I`
   is convex in `E`, so intersecting Euclidean balls with `range I` produces convex neighbourhoods
   inside `(extChartAt I x).target`. Every nonempty member of this basis is smoothly contractible
   via straight-line interpolation in chart coordinates reparametrized by `Real.smoothTransition`.
   Mayer–Vietoris induction on `(extChartAt I x).source`, combining the binary-union step from
   `TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris` and the countable disjoint-union step
   from `TauCeti.Geometry.Manifold.SmoothSingular.Additivity`, proves the quasi-isomorphism on all
   open subsets of `(extChartAt I x).source`.
3. **Global manifold.** The open subsets of `M` contained in some `(extChartAt I x).source` form a
   second intersection-stable basis of `M`, and a second Mayer–Vietoris induction extends the
   quasi-isomorphism to all open subsets of `M` and hence to `M` itself.

When `R` is projective in `C`, every term of both chain complexes is projective
(`SSet.projective_chainComplex_X_of_projective`), so the quasi-isomorphism upgrades to a chosen
chain homotopy equivalence `TauCeti.smoothSingularChainHomotopyEquiv` whose inverse is natural up
to a chosen chain homotopy (`TauCeti.smoothSingularChainHomotopyEquivInvNaturality`). Applying
`Hom(-, Y)` yields the dual cochain homotopy equivalence
`TauCeti.smoothSingularCochainHomotopyEquiv` and the cohomology isomorphism
`TauCeti.smoothSingularCohomologyIso`.

## Main definitions and results

* `TauCeti.isIso_smoothSingularSubcomplex_ι_of_subsingleton` and
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton`: on a subsingleton
  charted space (including the empty space and a point), the inclusion of smooth singular simplices
  is an isomorphism.
* `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff` and
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`: explicit chain
  homotopy equivalence and quasi-isomorphism for smoothly contractible charted spaces.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens` and
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: the smoothing quasi-isomorphism on
  open subsets of `M` and on `M`.
* `TauCeti.smoothSingularHomologyIso`: the induced natural isomorphism between smooth singular
  homology and singular homology.
* `TauCeti.smoothSingularChainHomotopyEquiv`,
  `TauCeti.homologyMap_smoothSingularChainHomotopyEquiv_inv`, and
  `TauCeti.smoothSingularChainHomotopyEquivInvNaturality`: the smoothing chain homotopy equivalence
  for projective coefficients, compatibility of its inverse with `smoothSingularHomologyIso`, and
  the chain homotopy witnessing naturality of its inverse.
* `TauCeti.smoothSingularCochainHomotopyEquiv`,
  `TauCeti.quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι`,
  `TauCeti.smoothSingularCohomologyIso`, and
  `TauCeti.homologyMap_smoothSingularCochainHomotopyEquiv_inv`: the induced cochain homotopy
  equivalence, cochain quasi-isomorphism, cohomology isomorphism, and compatibility of the cochain
  inverse with `smoothSingularCohomologyIso`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

/-! ### Subsingleton and smoothly contractible charted spaces -/

section Contractible

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- On a subsingleton charted space (in particular on the empty space or on a point), every
singular simplex is constant and hence smooth, so the inclusion of the smooth singular subcomplex
into the singular simplicial set is an isomorphism. -/
instance isIso_smoothSingularSubcomplex_ι_of_subsingleton [Subsingleton M] :
    IsIso (smoothSingularSubcomplex I M).ι := by
  rw [← Subfunctor.eq_top_iff_isIso, eq_top_iff]
  rintro ⟨k⟩ σ -
  induction k using SimplexCategory.rec with | _ n => ?_
  obtain ⟨t⟩ : Nonempty (Convexity.StdSimplex ℝ (Fin (n + 1))) := inferInstance
  rw [mem_smoothSingularSubcomplex_iff]
  convert contMDiffOnSubset_const I ∞ ((TopCat.of M).toSSetObjEquiv _ σ t) using 1

/-- On a subsingleton charted space, the inclusion of smooth singular chains into singular chains
is a quasi-isomorphism. -/
instance quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton [Subsingleton M]
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :=
  inferInstance

private def constSmoothSubcomplexLift (c : M) :
    TopCat.toSSet.obj (TopCat.of PUnit.{u + 1}) ⟶ (smoothSingularSubcomplex I M : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} c))) (by
      rintro k _ ⟨σ, rfl⟩
      rw [mem_smoothSingularSubcomplex_iff]
      exact contMDiffOnSubset_const I ∞ c)

private lemma constSmoothSubcomplexLift_ι (c : M) :
    constSmoothSubcomplexLift (I := I) c ≫ (smoothSingularSubcomplex I M).ι =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} c)) :=
  SSet.Subcomplex.lift_ι _ _

private def constSmoothSubcomplexRetract (c : M) :
    TopCat.toSSet.obj (TopCat.of M) ⟶ (smoothSingularSubcomplex I M : SSet) :=
  TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const M PUnit.unit)) ≫
    constSmoothSubcomplexLift (I := I) c

private lemma constSmoothSubcomplexRetract_ι (c : M) :
    constSmoothSubcomplexRetract (I := I) c ≫ (smoothSingularSubcomplex I M).ι =
      TopCat.toSSet.map
        (TopCat.ofHom ⟨fun _ ↦ c, (contMDiff_const : ContMDiff I I ∞ _).continuous⟩) := by
  rw [constSmoothSubcomplexRetract, Category.assoc, constSmoothSubcomplexLift_ι,
    ← Functor.map_comp]
  rfl

private def contMDiffHomotopyToConst {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F)
    (c : M) (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    TopCat.Homotopy
      (TopCat.ofHom ⟨id, (contMDiff_id (I := I) (n := ∞)).continuous⟩)
      (TopCat.ofHom ⟨fun _ ↦ c, (contMDiff_const : ContMDiff I I ∞ _).continuous⟩) where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

private def homotopy_ι_comp_constSmoothSubcomplexRetract
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        SSet.chainComplexMap (constSmoothSubcomplexRetract (I := I) c) R)
      (𝟙 _) := by
  have hcomp : (smoothSingularSubcomplex I M).ι ≫ constSmoothSubcomplexRetract (I := I) c =
      smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι, Category.assoc,
      constSmoothSubcomplexRetract_ι, smoothSingularSubcomplexMap_ι]
  refine (Homotopy.ofEq ?_).trans
    (((smoothSingularChainHomotopy (contMDiff_id (I := I))
      (contMDiff_const : ContMDiff I I ∞ _) (contMDiffHomotopyToConst hF c h₀ h₁)
      hF (fun _ ↦ rfl) R).symm).trans (Homotopy.ofEq ?_))
  · rw [← Functor.map_comp, hcomp]
  · rw [smoothSingularSubcomplexMap_id]
    exact ((SSet.chainComplexFunctor C).obj R).map_id _

private def homotopy_constSmoothSubcomplexRetract_comp_ι
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    Homotopy
      (SSet.chainComplexMap (constSmoothSubcomplexRetract (I := I) c) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
      (𝟙 _) := by
  refine (Homotopy.ofEq ?_).trans
    ((((contMDiffHomotopyToConst hF c h₀ h₁).toSSet.chainComplexMap R).symm).trans
      (Homotopy.ofEq ?_))
  · rw [← Functor.map_comp, constSmoothSubcomplexRetract_ι]
  · have hid : (TopCat.ofHom ⟨id, (contMDiff_id (I := I) (n := ∞)).continuous⟩ :
        TopCat.of M ⟶ TopCat.of M) = 𝟙 (TopCat.of M) := by ext; rfl
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
  inv := SSet.chainComplexMap (constSmoothSubcomplexRetract (I := I) c) R
  homotopyHomInvId := homotopy_ι_comp_constSmoothSubcomplexRetract R hF c h₀ h₁
  homotopyInvHomId := homotopy_constSmoothSubcomplexRetract_comp_ι R hF c h₀ h₁

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

/-! ### Mayer–Vietoris induction on extended charts and on manifolds -/

section QuasiIso

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C]

private abbrev extChartAtOpens (I : ModelWithCorners ℝ E H) (x : M) : Opens M :=
  ⟨(extChartAt I x).source, isOpen_extChartAt_source x⟩

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
private lemma quasiIso_iSup_nat {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
    (R : C) (s : ℕ → Opens X) (hs : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (h : ∀ n, QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I (s n)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(⨆ n, s n)).ι R) := by
  have : HasCoproducts.{0} C := hasCoproducts_shrink
  have : HasExactColimitsOfShape (Discrete (ULift.{u} ℕ)) C :=
    HasExactColimitsOfShape.of_domain_equivalence C
      (Discrete.equivalence (Equiv.ulift.symm : ℕ ≃ ULift.{u} ℕ))
  let s' : ULift.{u} ℕ → Opens X := fun i ↦ s i.down
  have heq : (⨆ n, s n) = ⨆ i, s' i :=
    le_antisymm (iSup_le fun n ↦ le_iSup s' (ULift.up n)) (iSup_le fun i ↦ le_iSup s i.down)
  rw [heq]
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup s' C R
    (fun i j hij ↦ hs i.down j.down fun hd ↦ hij (ULift.ext hd))
    (fun i ↦ h i.down)

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [HasExactColimitsOfShape (Discrete ℕ) C] in
private lemma exists_contMDiff_contraction_of_convex_image_extChartAt (x : M)
    {V : Opens (extChartAtOpens I x)} (c : V)
    (hV : Convex ℝ ((fun y : extChartAtOpens I x ↦ extChartAt I x y.1) '' (V : Set _))) :
    ∃ F : ℝ × V → V, ContMDiff (𝓘(ℝ).prod I) I ∞ F ∧
      (∀ z, F (0, z) = z) ∧ (∀ z, F (1, z) = c) := by
  let φ : extChartAtOpens I x → E := fun y ↦ extChartAt I x y.1
  have hφ : ContMDiff I 𝓘(ℝ, E) ∞ φ :=
    (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞)).comp_contMDiff
      (contMDiff_subtype_val (I := I) (U := extChartAtOpens I x))
      fun y ↦ (extChartAt_source I x) ▸ y.2
  let G : ℝ × V → E := fun p ↦ φ c.1 + (1 - Real.smoothTransition p.1) • (φ p.2.1 - φ c.1)
  have hG_im (p : ℝ × V) : G p ∈ φ '' (V : Set _) :=
    (hV.starConvex ⟨c.1, c.2, rfl⟩).add_smul_sub_mem ⟨p.2.1, p.2.2, rfl⟩
      (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hG_tgt (p : ℝ × V) : G p ∈ (extChartAt I x).target := by
    obtain ⟨w, -, hw⟩ := hG_im p
    exact hw ▸ (extChartAt I x).map_source w.2
  have hF_V (p : ℝ × V) : (⟨(extChartAt I x).symm (G p),
      (extChartAt I x).map_target (hG_tgt p)⟩ : extChartAtOpens I x) ∈ V := by
    obtain ⟨w, hwV, hw⟩ := hG_im p
    have heq : (⟨(extChartAt I x).symm (G p),
        (extChartAt I x).map_target (hG_tgt p)⟩ : extChartAtOpens I x) = w :=
      Subtype.ext (by dsimp only; rw [← hw]; exact (extChartAt I x).left_inv w.2)
    exact heq.symm ▸ hwV
  have hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ G := by
    have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × V ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have hz : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × V ↦ φ p.2.1 :=
      hφ.comp ((contMDiff_subtype_val (I := I) (U := V)).comp contMDiff_snd)
    exact ContMDiff.add contMDiff_const
      (ContMDiff.smul (ContMDiff.sub contMDiff_const hψ) (hz.sub contMDiff_const))
  refine ⟨fun p ↦ ⟨⟨_, (extChartAt I x).map_target (hG_tgt p)⟩, hF_V p⟩, ?_, ?_, ?_⟩
  · rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp_contMDiff hG hG_tgt
  · intro z
    refine Subtype.ext (Subtype.ext ?_)
    dsimp only [G, φ]
    rw [Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact (extChartAt I x).left_inv z.1.2
  · intro z
    refine Subtype.ext (Subtype.ext ?_)
    dsimp only [G, φ]
    rw [Real.smoothTransition.one, sub_self, zero_smul, add_zero]
    exact (extChartAt I x).left_inv c.1.2

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [HasExactColimitsOfShape (Discrete ℕ) C] in
private lemma quasiIso_of_convex_image_extChartAt (R : C) (x : M)
    {V : Opens (extChartAtOpens I x)}
    (hV : Convex ℝ ((fun y : extChartAtOpens I x ↦ extChartAt I x y.1) '' (V : Set _))) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R) := by
  rcases (V : Set (extChartAtOpens I x)).eq_empty_or_nonempty with hempty | ⟨c₀, hc₀⟩
  · have : IsEmpty V :=
      ⟨fun z ↦ by have hz : z.1 ∈ (V : Set (extChartAtOpens I x)) := z.2; rwa [hempty] at hz⟩
    infer_instance
  · obtain ⟨F, hF, h₀, h₁⟩ :=
      exists_contMDiff_contraction_of_convex_image_extChartAt x ⟨c₀, hc₀⟩ hV
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF ⟨c₀, hc₀⟩ h₀ h₁

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private lemma isBasis_convex_image_extChartAt (x : M) :
    Opens.IsBasis {V : Opens (extChartAtOpens I x) |
      Convex ℝ ((fun y : extChartAtOpens I x ↦ extChartAt I x y.1) '' (V : Set _))} := by
  let φ : extChartAtOpens I x → E := fun y ↦ extChartAt I x y.1
  have hφ : Continuous φ :=
    ((contMDiffOn_extChartAt (I := I) (x := x) (n := ∞)).comp_contMDiff
      (contMDiff_subtype_val (I := I) (U := extChartAtOpens I x))
      fun y ↦ (extChartAt_source I x) ▸ y.2).continuous
  refine Opens.isBasis_iff_nbhd.2 fun {U y} hy ↦ ?_
  have hUM : IsOpen (Subtype.val '' (U : Set (extChartAtOpens I x))) :=
    (extChartAtOpens I x).isOpen.isOpenMap_subtype_val _ U.isOpen
  have hpre : (extChartAt I x).symm ⁻¹' (Subtype.val '' (U : Set (extChartAtOpens I x))) ∈
      𝓝 (φ y) :=
    (continuousAt_extChartAt_symm' y.2).preimage_mem_nhds
      (hUM.mem_nhds ⟨y, hy, ((extChartAt I x).left_inv y.2).symm⟩)
  obtain ⟨r, hr_pos, hr⟩ := Metric.mem_nhdsWithin_iff.1
    (Filter.inter_mem (extChartAt_target_mem_nhdsWithin' y.2) (nhdsWithin_le_nhds hpre))
  let V : Opens (extChartAtOpens I x) := ⟨φ ⁻¹' Metric.ball (φ y) r, Metric.isOpen_ball.preimage hφ⟩
  have hV_im : φ '' (V : Set _) = Metric.ball (φ y) r ∩ Set.range I := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hz, extChartAt_target_subset_range x ((extChartAt I x).map_source z.2)⟩
    · rintro v hv
      have hv_tgt : v ∈ (extChartAt I x).target := (hr hv).1
      have hφ_symm : φ ⟨(extChartAt I x).symm v, (extChartAt I x).map_target hv_tgt⟩ = v :=
        (extChartAt I x).right_inv hv_tgt
      exact ⟨⟨(extChartAt I x).symm v, (extChartAt I x).map_target hv_tgt⟩,
        Set.mem_preimage.2 (hφ_symm.symm ▸ hv.1), hφ_symm⟩
  refine ⟨V, ?_, Metric.mem_ball_self hr_pos, fun z hz ↦ ?_⟩
  · rw [Set.mem_ofPred_eq]
    dsimp only [φ] at hV_im
    rw [hV_im]
    exact (convex_ball (φ y) r).inter I.convex_range
  · have hz_mem := (hr ⟨hz, extChartAt_target_subset_range x ((extChartAt I x).map_source z.2)⟩).2
    rw [Set.mem_preimage, (extChartAt I x).left_inv z.2] at hz_mem
    obtain ⟨w, hwU, hw⟩ := hz_mem
    exact Subtype.ext hw ▸ hwU

private lemma quasiIso_of_subset_extChartAt_source (R : C) (x : M) {U : Opens M}
    (hU : (U : Set M) ⊆ (extChartAt I x).source) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace (extChartAtOpens I x) :=
    (extChartAtOpens I x).isOpen.locallyCompactSpace
  let φ : extChartAtOpens I x → E := fun y ↦ extChartAt I x y.1
  have hφ_inj : Function.Injective φ :=
    fun y₁ y₂ h ↦ Subtype.ext ((extChartAt I x).injOn y₁.2 y₂.2 h)
  have hW : ∀ V : Opens (extChartAtOpens I x),
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R) :=
    mayerVietoris_induction
      (fun V ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
      {V | Convex ℝ (φ '' (V : Set _))}
      (isBasis_convex_image_extChartAt x)
      (fun V₁ h₁ V₂ h₂ ↦ by
        rw [Set.mem_ofPred_eq, Opens.coe_inf, Set.image_inter hφ_inj]
        exact h₁.inter h₂)
      (by
        have : IsEmpty ↥(⊥ : Opens (extChartAtOpens I x)) := Subtype.isEmpty_false
        infer_instance)
      (fun V hV ↦ quasiIso_of_convex_image_extChartAt R x hV)
      (fun V₁ V₂ ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup R V₁ V₂)
      (fun s hs h ↦ quasiIso_iSup_nat R s hs h)
  let U' : Opens (extChartAtOpens I x) :=
    ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  let f : U → U' := fun z ↦ ⟨⟨z.1, hU z.2⟩, z.2⟩
  let g : U' → U := fun z ↦ ⟨z.1.1, z.2⟩
  have hf : ContMDiff I I ∞ f := by
    rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_subtype_val (I := I) (U := U)
  have hg : ContMDiff I I ∞ g := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_subtype_val (I := I) (U := extChartAtOpens I x)).comp
      (contMDiff_subtype_val (I := I) (U := U'))
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R hf hg
    (fun _ ↦ rfl) (fun _ ↦ rfl) (hW U')

/-- **The smoothing theorem on open subsets.** For any open subset `U` of a Hausdorff `σ`-compact
smooth manifold `M` modelled on a finite-dimensional real model with corners `I`, the inclusion of
smooth singular chains into singular chains with coefficients in `R` is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (R : C) (U : Opens M) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact mayerVietoris_induction
    (fun V ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    {V : Opens M | ∃ x : M, (V : Set M) ⊆ (extChartAt I x).source}
    (Opens.isBasis_iff_nbhd.2 fun {W x} hx ↦
      ⟨W ⊓ extChartAtOpens I x, ⟨x, Set.inter_subset_right⟩,
        ⟨hx, mem_extChartAt_source x⟩, inf_le_left⟩)
    (by
      rintro V₁ ⟨x, hx⟩ V₂ -
      exact ⟨x, Set.inter_subset_left.trans hx⟩)
    (by
      have : IsEmpty ↥(⊥ : Opens M) := Subtype.isEmpty_false
      infer_instance)
    (by
      rintro V ⟨x, hx⟩
      exact quasiIso_of_subset_extChartAt_source R x hx)
    (fun V₁ V₂ ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup R V₁ V₂)
    (fun s hs h ↦ quasiIso_iSup_nat R s hs h)
    U

/-- **The smoothing theorem (quasi-isomorphism form, Lee Theorem 18.7).** On a Hausdorff
`σ`-compact smooth manifold `M` modelled on a finite-dimensional real model with corners `I`, the
inclusion of smooth singular chains into singular chains with coefficients in `R` is a
quasi-isomorphism whenever countable coproducts are exact in `C`. -/
instance quasiIso_chainComplexMap_smoothSingularSubcomplex_ι (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let f : M → ↥(⊤ : Opens M) := fun x ↦ ⟨x, trivial⟩
  have hf : ContMDiff I I ∞ f := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_id (I := I)
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R
    hf (contMDiff_subtype_val (I := I) (U := ⊤))
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens R ⊤)

end QuasiIso

/-! ### Smooth singular homology isomorphism, chain homotopy equivalence, and cohomology -/

section HomotopyEquiv

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  (N : Type u) [TopologicalSpace N] [ChartedSpace H' N]
  [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

/-- **The smoothing isomorphism on homology.** The inclusion of smooth singular chains into singular
chains induces an isomorphism `Hₙ^∞(M; R) ≅ Hₙ(M; R)` in every degree `n`. -/
def smoothSingularHomologyIso (n : ℕ) :
    (smoothSingularSubcomplex I M : SSet).homology R n ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology R n :=
  asIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)

/-- The forward map of `smoothSingularHomologyIso` is the map on homology induced by the inclusion
of smooth singular simplices. -/
@[simp]
theorem smoothSingularHomologyIso_hom (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n := by
  rw [smoothSingularHomologyIso, asIso_hom]

variable {I M J N} in
/-- `smoothSingularHomologyIso` is natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
        (smoothSingularHomologyIso J N R n).hom := by
  rw [smoothSingularHomologyIso_hom, smoothSingularHomologyIso_hom,
    ← SSet.homologyMap_comp, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- The inverse of `smoothSingularHomologyIso` is natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_inv_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).inv ≫
        SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (smoothSingularHomologyIso J N R n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    smoothSingularHomologyIso_hom_naturality R hf]

section Projective

variable [Projective R]

/-- **The smoothing theorem (chain homotopy equivalence form, Lee Theorem 18.7).** When `R` is a
projective object of `C` (for instance `R = ModuleCat.of ℝ ℝ` or `R = ModuleCat.of ℤ ℤ`), every
degree of both the smooth and ordinary singular chain complexes is projective, so the inclusion of
smooth singular chains into singular chains is a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquiv :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  let h := (ChainComplex.quasiIso_iff_of_projective
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)).1 inferInstance
  h.choose.copy (Homotopy.ofEq h.choose_spec)

/-- The forward map of `smoothSingularChainHomotopyEquiv` is the chain map induced by the inclusion
of smooth singular simplices. -/
@[simp]
theorem smoothSingularChainHomotopyEquiv_hom :
    (smoothSingularChainHomotopyEquiv I M R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := by
  rw [smoothSingularChainHomotopyEquiv, HomotopyEquiv.copy_hom]

/-- The map induced on homology by the inverse of `smoothSingularChainHomotopyEquiv` is the inverse
of `smoothSingularHomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularChainHomotopyEquiv_inv (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularChainHomotopyEquiv I M R).inv n =
      (smoothSingularHomologyIso I M R n).inv := by
  rw [← cancel_mono (smoothSingularHomologyIso I M R n).hom, Iso.inv_hom_id,
    smoothSingularHomologyIso_hom, SSet.homologyMap, ← smoothSingularChainHomotopyEquiv_hom,
    ← HomologicalComplex.homologyMap_comp,
    (smoothSingularChainHomotopyEquiv I M R).homotopyInvHomId.homologyMap_eq,
    HomologicalComplex.homologyMap_id]

variable {I M J N} in
/-- The forward map of `smoothSingularChainHomotopyEquiv` commutes strictly with the chain maps
induced by a smooth map `f : M → N`. -/
@[reassoc]
theorem smoothSingularChainHomotopyEquiv_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    (smoothSingularChainHomotopyEquiv I M R).hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R =
      SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R ≫
        (smoothSingularChainHomotopyEquiv J N R).hom := by
  rw [smoothSingularChainHomotopyEquiv_hom, smoothSingularChainHomotopyEquiv_hom,
    ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- **Naturality up to chain homotopy of the smoothing inverse.** For any smooth map `f : M → N`,
composing the smoothing homotopy inverse on `M` with the smooth pushforward along `f` is chain
homotopic to pushing forward singular chains along `f` and then applying the smoothing homotopy
inverse on `N`. -/
def smoothSingularChainHomotopyEquivInvNaturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    Homotopy
      ((smoothSingularChainHomotopyEquiv I M R).inv ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫
        (smoothSingularChainHomotopyEquiv J N R).inv) :=
  let eM := smoothSingularChainHomotopyEquiv I M R
  let eN := smoothSingularChainHomotopyEquiv J N R
  let fS := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R
  let fT := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R
  (Homotopy.ofEq (Category.comp_id (eM.inv ≫ fS)).symm).trans <|
    (eN.homotopyHomInvId.symm.compLeft (eM.inv ≫ fS)).trans <|
      (Homotopy.ofEq (by
        dsimp only [eM, eN, fS, fT]
        rw [Category.assoc, ← Category.assoc _ (smoothSingularChainHomotopyEquiv J N R).hom,
          ← smoothSingularChainHomotopyEquiv_hom_naturality R hf,
          Category.assoc, ← Category.assoc (smoothSingularChainHomotopyEquiv I M R).inv])).trans <|
        (eM.homotopyInvHomId.compRight (fT ≫ eN.inv)).trans <|
          Homotopy.ofEq (Category.id_comp (fT ≫ eN.inv))

/-! ### Cochain homotopy equivalence and singular cohomology comparison -/

variable (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- **The dual smoothing cochain homotopy equivalence.** Applying `Hom(-, Y)` to
`smoothSingularChainHomotopyEquiv` yields a cochain homotopy equivalence from the singular cochain
complex of `M` to the smooth singular cochain complex `Hom(C_*^∞(M; R), Y)`. -/
def smoothSingularCochainHomotopyEquiv :
    HomotopyEquiv ((TopCat.of M).singularCochainComplex R k Y)
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Y) :=
  (smoothSingularChainHomotopyEquiv I M R).linearYonedaFunctorMap k Y

/-- The forward map of `smoothSingularCochainHomotopyEquiv` is restriction of singular cochains to
smooth singular chains. -/
@[simp]
theorem smoothSingularCochainHomotopyEquiv_hom :
    (smoothSingularCochainHomotopyEquiv I M R k Y).hom =
      SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι := by
  rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_hom,
    smoothSingularChainHomotopyEquiv_hom]

/-- The inverse map of `smoothSingularCochainHomotopyEquiv` is precomposition with the inverse of
`smoothSingularChainHomotopyEquiv`. -/
theorem smoothSingularCochainHomotopyEquiv_inv :
    (smoothSingularCochainHomotopyEquiv I M R k Y).inv =
      (ChainComplex.linearYonedaFunctor k Y).map
        (smoothSingularChainHomotopyEquiv I M R).inv.op := by
  rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_inv]

/-- Restriction from singular cochains to smooth singular cochains is a quasi-isomorphism when the
chain coefficient object `R` is projective. -/
instance quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
      (smoothSingularSubcomplex I M).ι) := by
  rw [← smoothSingularCochainHomotopyEquiv_hom I M R k Y]
  exact (smoothSingularCochainHomotopyEquiv I M R k Y).quasiIso_hom

variable {I M J N} in
/-- **Naturality up to cochain homotopy of the dual smoothing inverse.** For any smooth map
`f : M → N`, pulling back smooth cochains along `f` and extending to singular cochains on `M` is
cochain homotopic to extending on `N` first and then pulling back singular cochains along `f`. -/
def smoothSingularCochainHomotopyEquivInvNaturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    Homotopy
      (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf) ≫
        (smoothSingularCochainHomotopyEquiv I M R k Y).inv)
      ((smoothSingularCochainHomotopyEquiv J N R k Y).inv ≫
        TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩)) :=
  (Homotopy.ofEq (by
    rw [smoothSingularCochainHomotopyEquiv_inv]
    exact ((ChainComplex.linearYonedaFunctor k Y).map_comp _ _).symm)).trans <|
    ((smoothSingularChainHomotopyEquivInvNaturality R hf).linearYonedaFunctorMap k Y).trans <|
      Homotopy.ofEq (by
        rw [smoothSingularCochainHomotopyEquiv_inv]
        exact (ChainComplex.linearYonedaFunctor k Y).map_comp _ _)

/-- **The smoothing isomorphism on cohomology.** Restriction to smooth singular chains induces an
isomorphism in every degree `n` between the singular cohomology of `M` and the cohomology of the
smooth singular cochain complex `Hom(C_*^∞(M; R), Y)`. -/
def smoothSingularCohomologyIso (n : ℕ) :
    (TopCat.of M).singularCohomology R k Y n ≅
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Y).homology n :=
  asIso (HomologicalComplex.homologyMap
    (SSet.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularSubcomplex I M).ι) n)

/-- The forward map of `smoothSingularCohomologyIso` is the map on cohomology induced by restriction
to smooth singular chains. -/
@[simp]
theorem smoothSingularCohomologyIso_hom (n : ℕ) :
    (smoothSingularCohomologyIso I M R k Y n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι) n := by
  rw [smoothSingularCohomologyIso, asIso_hom]

/-- The map induced on cohomology by the inverse of `smoothSingularCochainHomotopyEquiv` is the
inverse of `smoothSingularCohomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularCochainHomotopyEquiv_inv (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularCochainHomotopyEquiv I M R k Y).inv n =
      (smoothSingularCohomologyIso I M R k Y n).inv := by
  rw [← cancel_mono (smoothSingularCohomologyIso I M R k Y n).hom, Iso.inv_hom_id,
    smoothSingularCohomologyIso_hom, ← smoothSingularCochainHomotopyEquiv_hom,
    ← HomologicalComplex.homologyMap_comp,
    (smoothSingularCochainHomotopyEquiv I M R k Y).homotopyInvHomId.homologyMap_eq,
    HomologicalComplex.homologyMap_id]

variable {I M J N} in
/-- `smoothSingularCohomologyIso` is contravariantly natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n ≫
        (smoothSingularCohomologyIso I M R k Y n).hom =
      (smoothSingularCohomologyIso J N R k Y n).hom ≫
        HomologicalComplex.homologyMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf))
          n := by
  rw [smoothSingularCohomologyIso_hom, smoothSingularCohomologyIso_hom,
    TopCat.singularCohomologyMap, TopCat.singularCochainComplexMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- The inverse of `smoothSingularCohomologyIso` (from smooth singular cohomology to singular
cohomology) is contravariantly natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_inv_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    HomologicalComplex.homologyMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)) n ≫
        (smoothSingularCohomologyIso I M R k Y n).inv =
      (smoothSingularCohomologyIso J N R k Y n).inv ≫
        TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    smoothSingularCohomologyIso_hom_naturality R k Y hf]

end Projective

end HomotopyEquiv

end TauCeti
