/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Geometry.Manifold.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

/-!
# The smoothing theorem for smooth singular chains

On a second-countable locally compact Hausdorff smooth manifold `M` (possibly with boundary or
corners, modelled on a `ModelWithCorners ℝ E H`), the inclusion of the smooth singular subcomplex
`smoothSingularSubcomplex I M` into the singular simplicial set `TopCat.toSSet.obj (TopCat.of M)`
induces a quasi-isomorphism of chain complexes with coefficients in any object `R` of an abelian
category `C` having exact countable coproducts:
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`.

Every finite-dimensional σ-compact Hausdorff manifold satisfies `[LocallyCompactSpace M]` and
`[SecondCountableTopology M]` (via `ChartedSpace.locallyCompactSpace` and
`ChartedSpace.secondCountable_of_sigmaCompact`), and every module category `ModuleCat.{u} k` (such
as `ModuleCat ℝ` or `ModuleCat ℤ`) has exact coproducts of every size `u` (`AB4`), so the
coefficient hypotheses discharge automatically for the standard smooth-manifold settings.

The proof follows Lee's Mayer–Vietoris induction over open subsets of `M`
(`TauCeti.mayerVietoris_induction_extChartAt`):

1. **Empty set**: both simplicial sets have `HasDimensionLT 0`, so both chain complexes are zero
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`).
2. **Smoothly contractible manifolds and convex chart domains**: a smooth contraction
   `F : ℝ × M → M` identifies both smooth and continuous singular homology with the homology of a
   point, compatibly with the inclusion
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`). On a chart domain
   `(chartAt H x).source ∩ (extChartAt I x)⁻¹' C'` with `C'` convex and
   `C' ∩ range I ⊆ (extChartAt I x).target`, convexity of `C' ∩ range I` yields a smooth
   straight-line contraction reparametrized by `Real.smoothTransition`
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convexChartDomain`).
3. **Binary unions**: handled by the five-lemma step on the compatible smooth and singular
   Mayer–Vietoris sequences (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`).
4. **Countable disjoint unions**: handled by additivity of smooth and singular homology over
   pairwise disjoint open sets (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`).

Passing to homology yields natural isomorphisms
`TauCeti.smoothSingularHomologyIso : Hₙ^∞(M; R) ≅ Hₙ(M; R)` in every degree `n`. When `R` is
projective (in particular `R = ℝ`, `R = ℤ`, or any projective module over a ring), the smooth and
singular chain complexes are degreewise projective, so the quasi-isomorphism upgrades to a chain
homotopy equivalence `TauCeti.smoothSingularChainHomotopyEquiv` whose forward map is the inclusion
and whose inverse is natural up to chain homotopy in smooth maps
(`TauCeti.smoothSingularChainInvNaturalityHomotopy`). Dualizing by the contravariant linear Yoneda
functor `Hom(-, A)` yields a cochain homotopy equivalence
`TauCeti.smoothSingularCochainHomotopyEquiv` (with homotopy-natural inverse
`TauCeti.smoothSingularCochainInvNaturalityHomotopy`) and natural cohomology isomorphisms
`TauCeti.smoothSingularCohomologyIso : Hⁿ(M; A) ≅ Hⁿ_∞(M; A)` for every coefficient object `A`.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convexChartDomain`:
  the base cases of the smoothing theorem.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: **the smoothing theorem** — the
  inclusion of smooth singular chains into singular chains is a quasi-isomorphism.
* `TauCeti.smoothSingularHomologyIso`: natural isomorphism between smooth and singular homology
  (`TauCeti.smoothSingularHomologyIso_hom_naturality`,
  `TauCeti.smoothSingularHomologyIso_inv_naturality`).
* `TauCeti.smoothSingularChainHomotopyEquiv`: chain homotopy equivalence between smooth and
  singular chains for projective coefficients `R`, with naturality of the inverse up to chain
  homotopy (`TauCeti.smoothSingularChainInvNaturalityHomotopy`).
* `TauCeti.smoothSingularCochainHomotopyEquiv`,
  `TauCeti.quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι`,
  `TauCeti.smoothSingularCohomologyIso`: dual cochain homotopy equivalence, quasi-isomorphism, and
  natural isomorphism between singular and smooth singular cohomology for projective chain
  coefficients `R` and arbitrary value object `A`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 (the smoothing
  theorem for singular chains and isomorphism of smooth and continuous singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Set TopologicalSpace TopCat Convexity Function
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

/-! ### Base cases: empty manifolds, smoothly contractible manifolds, and convex chart domains -/

section BaseCases

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]

variable (I M) in
/-- **Empty-manifold base case of the smoothing theorem.** On an empty charted space, both the
smooth singular subcomplex and the singular simplicial set are empty, so the inclusion of smooth
singular chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty [IsEmpty M] (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have hS : (smoothSingularSubcomplex I M : SSet).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      IsEmpty.false ((TopCat.of M).toSSetObjEquiv _ σ.1 (StdSimplex.single 0))
  have hT : (TopCat.toSSet.obj (TopCat.of M)).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      IsEmpty.false ((TopCat.of M).toSSetObjEquiv _ σ (StdSimplex.single 0))
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact ((HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)).isIso
    ((HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)) _

/-- **Smoothly contractible base case of the smoothing theorem.** If a smooth map `F : ℝ × M → M`
joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the inclusion of smooth
singular chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff (R : C)
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let pt : TopCat.{u} := TopCat.of PUnit
  let a : TopCat.of M ⟶ pt := TopCat.ofHom (ContinuousMap.const M PUnit.unit)
  let b : pt ⟶ TopCat.of M := TopCat.ofHom (ContinuousMap.const pt c)
  have hab : a ≫ b = TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩ := by
    ext
    rfl
  have hba : b ≫ a = 𝟙 pt := by
    ext
  let p : (smoothSingularSubcomplex I M : SSet) ⟶ TopCat.toSSet.obj pt :=
    (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map a
  let s : TopCat.toSSet.obj pt ⟶ (smoothSingularSubcomplex I M : SSet) :=
    SSet.Subcomplex.lift (TopCat.toSSet.map b) (by
      rintro k _ ⟨σ, rfl⟩
      rw [mem_smoothSingularSubcomplex_iff]
      exact contMDiffOnSubset_const I ∞ c)
  have hs : s ≫ (smoothSingularSubcomplex I M).ι = TopCat.toSSet.map b :=
    SSet.Subcomplex.lift_ι _ _
  have hsp : s ≫ p = 𝟙 (TopCat.toSSet.obj pt) := by
    rw [← Category.assoc, hs, ← CategoryTheory.Functor.map_comp, hba,
      CategoryTheory.Functor.map_id]
  have hps : smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) =
      p ≫ s := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι, smoothSingularSubcomplexMap_ι,
      Category.assoc, hs, Category.assoc, ← CategoryTheory.Functor.map_comp, hab]
  let H : TopCat.Homotopy (𝟙 (TopCat.of M)) (a ≫ b) :=
    { toFun := fun q ↦ F (q.1, q.2)
      continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
      map_zero_left := h₀
      map_one_left := h₁ }
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hsIso : IsIso (SSet.homologyMap s R n) := by
    refine ⟨⟨SSet.homologyMap p R n, ?_, ?_⟩⟩
    · rw [← SSet.homologyMap_comp, hsp, SSet.homologyMap_id]
    · rw [← SSet.homologyMap_comp, ← hps,
        ← homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const
          hF h₀ h₁ n,
        smoothSingularSubcomplexMap_id, SSet.homologyMap_id]
  have hbIso : IsIso (SSet.homologyMap (TopCat.toSSet.map b) R n) := by
    refine ⟨⟨SSet.homologyMap (TopCat.toSSet.map a) R n, ?_, ?_⟩⟩
    · rw [← SSet.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hba,
        CategoryTheory.Functor.map_id, SSet.homologyMap_id]
    · rw [← SSet.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
        ← H.toSSet.congr_homologyMap R n, CategoryTheory.Functor.map_id, SSet.homologyMap_id]
  have hcomp : IsIso (SSet.homologyMap s R n ≫
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n) := by
    rw [← SSet.homologyMap_comp, hs]
    exact hbIso
  exact IsIso.of_isIso_comp_left (SSet.homologyMap s R n)
    (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)

/-- **Convex chart-domain base case of the smoothing theorem.** On an open subset
`U = (chartAt H x).source ∩ (extChartAt I x)⁻¹' C'` of a smooth manifold `M`, where `C' ⊆ E` is
convex and `C' ∩ range I ⊆ (extChartAt I x).target`, the inclusion of smooth singular chains into
singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convexChartDomain
    [IsManifold I ∞ M] (R : C) (x : M) {C' : Set E} {U : Opens M}
    (hC' : Convex ℝ C') (hCt : C' ∩ range I ⊆ (extChartAt I x).target)
    (hU : (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C') :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  rcases (U : Set M).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · have : IsEmpty U := Set.isEmpty_coe_sort.2 hempty
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty I U R
  have hU_mem : ∀ u : U, (u : M) ∈ (chartAt H x).source ∧ extChartAt I x u ∈ C' := by
    intro u
    have hu : (u : M) ∈ (U : Set M) := u.2
    rw [hU] at hu
    exact hu
  have hU_ext : ∀ u : U, extChartAt I x u ∈ C' ∩ range I := fun u ↦
    ⟨(hU_mem u).2, extChartAt_target_subset_range x
      ((extChartAt I x).map_source (by rw [extChartAt_source]; exact (hU_mem u).1))⟩
  let u₀ : U := ⟨x₀, hx₀⟩
  let z₀ : E := extChartAt I x u₀
  let g : ℝ × U → E := fun p ↦ z₀ + (1 - Real.smoothTransition p.1) • (extChartAt I x p.2 - z₀)
  have hg_mem : ∀ p : ℝ × U, g p ∈ C' ∩ range I := fun p ↦
    ((hC'.inter I.convex_range).starConvex (hU_ext u₀)).add_smul_sub_mem (hU_ext p.2)
      (sub_nonneg.2 (Real.smoothTransition.le_one p.1))
      (sub_le_self _ (Real.smoothTransition.nonneg p.1))
  have hg_target : ∀ p : ℝ × U, g p ∈ (extChartAt I x).target := fun p ↦ hCt (hg_mem p)
  have hF_mem : ∀ p : ℝ × U, (extChartAt I x).symm (g p) ∈ U := by
    intro p
    -- Membership in the open `U` is membership in its underlying carrier set `(U : Set M)`.
    change (extChartAt I x).symm (g p) ∈ (U : Set M)
    rw [hU]
    refine ⟨?_, ?_⟩
    · rw [← extChartAt_source I]
      exact (extChartAt I x).map_target (hg_target p)
    · rw [mem_preimage, (extChartAt I x).right_inv (hg_target p)]
      exact (hg_mem p).1
  let F : ℝ × U → U := fun p ↦ ⟨(extChartAt I x).symm (g p), hF_mem p⟩
  have hg_smooth : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ g := by
    have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have hcoord : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × U ↦ extChartAt I x p.2 :=
      (contMDiffOn_extChartAt (I := I) (x := x)).comp_contMDiff
        (contMDiff_subtype_val.comp contMDiff_snd) (fun p ↦ (hU_mem p.2).1)
    exact contMDiff_const.add ((contMDiff_const.sub hψ).smul (hcoord.sub contMDiff_const))
  have hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F :=
    (ContMDiff.subtypeVal_comp_iff (I := 𝓘(ℝ).prod I) (I' := I) U F).mp
      ((contMDiffOn_extChartAt_symm (I := I) x).comp_contMDiff hg_smooth hg_target)
  refine quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF u₀ ?_ ?_
  · intro u
    apply Subtype.ext
    have h0 : g (0, u) = extChartAt I x u := by
      simp [g, Real.smoothTransition.zero]
    dsimp only [F]
    rw [h0]
    exact (extChartAt I x).left_inv (by rw [extChartAt_source]; exact (hU_mem u).1)
  · intro u
    apply Subtype.ext
    have h1 : g (1, u) = extChartAt I x u₀ := by
      simp [g, z₀, Real.smoothTransition.one]
    dsimp only [F]
    rw [h1]
    exact (extChartAt I x).left_inv (by rw [extChartAt_source]; exact (hU_mem u₀).1)

end BaseCases

/-! ### The smoothing theorem and smooth-to-singular homology isomorphism -/

section Smoothing

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete (ULift.{u} ℕ)) C]

variable (I) in
/-- **The smoothing theorem for open subsets of a smooth manifold.** On any open subset `U` of a
second-countable locally compact Hausdorff smooth manifold `M`, the inclusion of smooth singular
chains into singular chains with coefficients in `R` is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (U : Opens M) (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  refine mayerVietoris_induction_extChartAt I
    (fun W : Opens M ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I W).ι R))
    ?_ ?_ ?_ ?_ U
  · have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.2⟩
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty I ↥(⊥ : Opens M) R
  · intro x C' W _ hC' hCt hW _
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_convexChartDomain R x hC' hCt hW
  · exact fun U' V' hU' hV' hI' ↦
      quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup R U' V' hU' hV' hI'
  · intro s hdisj hs
    let s' : ULift.{u} ℕ → Opens M := fun n ↦ s n.down
    have hdisj' : Pairwise (Disjoint on s') := fun i j hij ↦
      hdisj i.down j.down (fun h ↦ hij (ULift.ext h))
    have hsup : (⨆ n, s' n) = ⨆ n, s n := Equiv.ulift.iSup_comp
    rw [← hsup]
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup s' C R hdisj'
      (fun n ↦ hs n.down)

variable (I M) in
/-- **The smoothing theorem.** On a second-countable locally compact Hausdorff smooth manifold `M`
(possibly with boundary or corners), the inclusion of smooth singular chains into singular chains
with coefficients in `R` is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let e : (⊤ : Opens M) ≃ M :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, trivial⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have he : ContMDiff I I ∞ e := contMDiff_subtype_val (I := I) (U := (⊤ : Opens M))
  have hes : ContMDiff I I ∞ e.symm :=
    (ContMDiff.subtypeVal_comp_iff (I := I) (I' := I) (⊤ : Opens M) e.symm).mp contMDiff_id
  exact (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_equiv R e he hes).1
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens I ⊤ R)

variable (I M) in
/-- The inclusion of smooth singular simplices into singular simplices induces an isomorphism on
homology in every degree `n`. -/
theorem isIso_homologyMap_smoothSingularSubcomplex_ι (R : C) (n : ℕ) :
    IsIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n) := by
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

variable (I M) in
/-- **Isomorphism between smooth and continuous singular homology.** In every degree `n`, the
inclusion of smooth singular chains induces an isomorphism `Hₙ^∞(M; R) ≅ Hₙ(M; R)`. -/
def smoothSingularHomologyIso (R : C) (n : ℕ) :
    (smoothSingularSubcomplex I M : SSet).homology R n ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology R n :=
  @asIso _ _ _ _ _ (isIso_homologyMap_smoothSingularSubcomplex_ι I M R n)

/-- The forward map of `smoothSingularHomologyIso` is the homology map induced by the inclusion of
smooth singular simplices. -/
@[simp]
lemma smoothSingularHomologyIso_hom (R : C) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n := (rfl)

/-- Naturality of the forward map of `smoothSingularHomologyIso` in smooth maps `f : M → N`. -/
@[reassoc]
theorem smoothSingularHomologyIso_hom_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) (f : M → N) (hf : ContMDiff I J ∞ f) (n : ℕ) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
        (smoothSingularHomologyIso J N R n).hom =
      (smoothSingularHomologyIso I M R n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n := by
  simp only [smoothSingularHomologyIso_hom, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]

/-- Naturality of the inverse map of `smoothSingularHomologyIso` in smooth maps `f : M → N`. -/
@[reassoc]
theorem smoothSingularHomologyIso_inv_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) (f : M → N) (hf : ContMDiff I J ∞ f) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (smoothSingularHomologyIso J N R n).inv =
      (smoothSingularHomologyIso I M R n).inv ≫
        SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    smoothSingularHomologyIso_hom_naturality R f hf n]

/-! ### Chain homotopy equivalence and dual cohomology isomorphism for projective coefficients -/

section Projective

variable (I M) in
/-- **Chain homotopy equivalence between smooth and singular chains (existence).** For a projective
coefficient object `R` (such as `ℝ`, `ℤ`, or any projective module over a ring), the inclusion of
smooth singular chains into singular chains is a chain homotopy equivalence. -/
theorem homotopyEquivalences_chainComplexMap_smoothSingularSubcomplex_ι (R : C) [Projective R] :
    HomologicalComplex.homotopyEquivalences _ _
      (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R
  exact (ChainComplex.quasiIso_iff_of_projective _).1 this

variable (I M) in
/-- **Chain homotopy equivalence between smooth and singular chains.** For a projective coefficient
object `R`, the inclusion of smooth singular chains into singular chains is the forward map of a
chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquiv (R : C) [Projective R] :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  let h := homotopyEquivalences_chainComplexMap_smoothSingularSubcomplex_ι I M R
  h.choose.copy (Homotopy.ofEq h.choose_spec)

/-- The forward map of `smoothSingularChainHomotopyEquiv` is the chain map induced by the inclusion
of smooth singular simplices. -/
@[simp]
lemma smoothSingularChainHomotopyEquiv_hom (R : C) [Projective R] :
    (smoothSingularChainHomotopyEquiv I M R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := (rfl)

/-- The homology isomorphism induced by `smoothSingularChainHomotopyEquiv` agrees with
`smoothSingularHomologyIso`. -/
@[simp]
lemma smoothSingularChainHomotopyEquiv_toHomologyIso (R : C) [Projective R] (n : ℕ) :
    (smoothSingularChainHomotopyEquiv I M R).toHomologyIso n =
      smoothSingularHomologyIso I M R n := by
  ext
  rfl

/-- **Naturality up to chain homotopy of the smoothing inverse.** For any smooth map `f : M → N`,
the chosen homotopy inverse to the inclusion of smooth singular chains commutes with the induced
chain maps up to an explicit chain homotopy. -/
def smoothSingularChainInvNaturalityHomotopy
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) [Projective R] (f : M → N) (hf : ContMDiff I J ∞ f) :
    Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫
        (smoothSingularChainHomotopyEquiv J N R).inv)
      ((smoothSingularChainHomotopyEquiv I M R).inv ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R) := by
  let eM := smoothSingularChainHomotopyEquiv I M R
  let eN := smoothSingularChainHomotopyEquiv J N R
  let Sf := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R
  let Cf := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R
  have hcomm : Sf ≫ eN.hom = eM.hom ≫ Cf := by
    rw [smoothSingularChainHomotopyEquiv_hom, smoothSingularChainHomotopyEquiv_hom,
      ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι]
  exact ((eM.homotopyInvHomId.compRightId (Cf ≫ eN.inv)).symm.trans
    (Homotopy.ofEq (by
      rw [Category.assoc, ← Category.assoc eM.hom, ← hcomm, Category.assoc, Category.assoc]))).trans
    (eN.homotopyHomInvId.compLeftId (eM.inv ≫ Sf))

variable (I M) in
/-- **Cochain homotopy equivalence between singular and smooth singular cochains.** Dualizing
`smoothSingularChainHomotopyEquiv` by `Hom(-, A)` yields a cochain homotopy equivalence whose
forward map is restriction of singular cochains to smooth singular simplices. -/
def smoothSingularCochainHomotopyEquiv (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) :
    HomotopyEquiv ((TopCat.of M).singularCochainComplex R k A)
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k A) :=
  (smoothSingularChainHomotopyEquiv I M R).linearYonedaFunctorMap k A

/-- The forward map of `smoothSingularCochainHomotopyEquiv` is restriction of singular cochains to
smooth singular simplices. -/
@[simp]
lemma smoothSingularCochainHomotopyEquiv_hom (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) :
    (smoothSingularCochainHomotopyEquiv I M R k A).hom =
      SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι :=
  HomotopyEquiv.linearYonedaFunctorMap_hom k A (smoothSingularChainHomotopyEquiv I M R)

/-- **Naturality up to cochain homotopy of the cochain smoothing inverse.** For any smooth map
`f : M → N`, the chosen homotopy inverse to restriction of cochains commutes with pullback up to
an explicit cochain homotopy. -/
def smoothSingularCochainInvNaturalityHomotopy
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) [Projective R] (k : Type*) [Ring k] [Linear k C] (A : C)
    (f : M → N) (hf : ContMDiff I J ∞ f) :
    Homotopy
      (SSet.cochainComplexMap (R := R) (k := k) (M := A) (smoothSingularSubcomplexMap f hf) ≫
        (smoothSingularCochainHomotopyEquiv I M R k A).inv)
      ((smoothSingularCochainHomotopyEquiv J N R k A).inv ≫
        TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩)) := by
  have h1 :
      SSet.cochainComplexMap (R := R) (k := k) (M := A) (smoothSingularSubcomplexMap f hf) ≫
          (smoothSingularCochainHomotopyEquiv I M R k A).inv =
        (ChainComplex.linearYonedaFunctor k A).map
          ((smoothSingularChainHomotopyEquiv I M R).inv ≫
            SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R).op := by
    rw [op_comp, CategoryTheory.Functor.map_comp, smoothSingularCochainHomotopyEquiv,
      HomotopyEquiv.linearYonedaFunctorMap_inv]
    rfl
  have h2 :
      (ChainComplex.linearYonedaFunctor k A).map
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫
            (smoothSingularChainHomotopyEquiv J N R).inv).op =
        (smoothSingularCochainHomotopyEquiv J N R k A).inv ≫
          TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩) := by
    rw [op_comp, CategoryTheory.Functor.map_comp, smoothSingularCochainHomotopyEquiv,
      HomotopyEquiv.linearYonedaFunctorMap_inv]
    rfl
  exact (Homotopy.ofEq h1).trans
    (((smoothSingularChainInvNaturalityHomotopy R f hf).symm.linearYonedaFunctorMap
      k A).trans (Homotopy.ofEq h2))

variable (I M) in
/-- **Dual smoothing theorem for cochains.** Restriction of singular cochains to smooth singular
simplices is a quasi-isomorphism for any projective chain coefficient object `R` and any value
object `A`. -/
theorem quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := A)
      (smoothSingularSubcomplex I M).ι) := by
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R
  exact ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) k A

variable (I M) in
/-- Restriction of singular cochains to smooth singular simplices induces an isomorphism on
cohomology in every degree `n`. -/
theorem isIso_homologyMap_cochainComplexMap_smoothSingularSubcomplex_ι (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SSet.cochainComplexMap (R := R) (k := k) (M := A) (smoothSingularSubcomplex I M).ι) n) := by
  have := quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι I M R k A
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

variable (I M) in
/-- **Isomorphism between singular cohomology and smooth singular cohomology.** In every degree
`n`, restriction of singular cochains to smooth singular simplices induces an isomorphism
`Hⁿ(M; A) ≅ Hⁿ_∞(M; A)` for any projective chain coefficient object `R` and value object `A`. -/
def smoothSingularCohomologyIso (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) (n : ℕ) :
    (TopCat.of M).singularCohomology R k A n ≅
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k A).homology n :=
  (smoothSingularCochainHomotopyEquiv I M R k A).toHomologyIso n

/-- The forward map of `smoothSingularCohomologyIso` is the cohomology map induced by restricting
singular cochains to smooth singular simplices. -/
@[simp]
lemma smoothSingularCohomologyIso_hom (R : C) [Projective R]
    (k : Type*) [Ring k] [Linear k C] (A : C) (n : ℕ) :
    (smoothSingularCohomologyIso I M R k A n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := R) (k := k) (M := A)
          (smoothSingularSubcomplex I M).ι) n := by
  dsimp [smoothSingularCohomologyIso, HomotopyEquiv.toHomologyIso]
  rw [smoothSingularCochainHomotopyEquiv_hom]

/-- Naturality of the forward map of `smoothSingularCohomologyIso` in smooth maps `f : M → N`. -/
@[reassoc]
theorem smoothSingularCohomologyIso_hom_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) [Projective R] (k : Type*) [Ring k] [Linear k C] (A : C)
    (f : M → N) (hf : ContMDiff I J ∞ f) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := A) (TopCat.ofHom ⟨f, hf.continuous⟩) n ≫
        (smoothSingularCohomologyIso I M R k A n).hom =
      (smoothSingularCohomologyIso J N R k A n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (R := R) (k := k) (M := A)
            (smoothSingularSubcomplexMap f hf)) n := by
  simp only [smoothSingularCohomologyIso_hom, TopCat.singularCohomologyMap,
    TopCat.singularCochainComplexMap, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, smoothSingularSubcomplexMap_ι]

/-- Naturality of the inverse map of `smoothSingularCohomologyIso` in smooth maps `f : M → N`. -/
@[reassoc]
theorem smoothSingularCohomologyIso_inv_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
    (R : C) [Projective R] (k : Type*) [Ring k] [Linear k C] (A : C)
    (f : M → N) (hf : ContMDiff I J ∞ f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := R) (k := k) (M := A)
          (smoothSingularSubcomplexMap f hf)) n ≫
        (smoothSingularCohomologyIso I M R k A n).inv =
      (smoothSingularCohomologyIso J N R k A n).inv ≫
        TopCat.singularCohomologyMap (R := R) (k := k) (M := A)
          (TopCat.ofHom ⟨f, hf.continuous⟩) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    smoothSingularCohomologyIso_hom_naturality R k A f hf n]

end Projective

end Smoothing

end TauCeti
