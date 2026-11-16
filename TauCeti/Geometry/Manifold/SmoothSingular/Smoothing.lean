/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Analysis.Convex.Star
public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Algebra.Category.ModuleCat.AB
import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
import TauCeti.Algebra.Homology.Semisimple
import TauCeti.Algebra.Homology.Split
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
import TauCeti.Geometry.Manifold.MayerVietoris
import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy
import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision
import TauCeti.Topology.Sets.FinTwo

/-!
# The smoothing theorem for smooth singular chains

Let `M` be a Hausdorff, σ-compact smooth manifold modelled on a locally compact (equivalently,
finite-dimensional) real model with corners `I : ModelWithCorners ℝ E H`. This file proves the
smoothing theorem: the inclusion `(smoothSingularSubcomplex I M).ι` of the smooth singular chains
of `M` into its singular chains is a quasi-isomorphism with coefficients in any object `R` of an
abelian category `C` with exact countable coproducts
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`), and therefore induces a natural
isomorphism between smooth and continuous singular homology in every degree
(`TauCeti.smoothSingularHomologyIso`).

Over any semisimple ring `K` — in particular over any division ring or field such as `ℝ` —
every chain complex of `K`-modules splits, so this quasi-isomorphism upgrades to an explicit
chain homotopy equivalence (`TauCeti.smoothSingularChainHomotopyEquiv`) whose forward map is the
inclusion and whose homotopy inverse is natural up to chain homotopy under smooth maps
(`TauCeti.smoothSingularChainHomotopyEquivInvNaturality`). For a commutative semisimple ring `K`,
applying `Hom(-, B)` yields a cochain homotopy equivalence between singular cochains and smooth
singular cochains (`TauCeti.smoothSingularCochainHomotopyEquiv`) and a natural isomorphism on
cohomology (`TauCeti.smoothSingularCohomologyIso`).

The proof proceeds by Mayer–Vietoris induction on open subsets of `M`
(`ModelWithCorners.mayerVietoris_induction`), which works uniformly over arbitrary real models with
corners (including manifolds with boundary and corners):

1. **Empty and smoothly contractible opens:** On an empty manifold both chain complexes are zero
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`). On a smoothly
   contractible manifold, the contraction induces inverse isomorphisms on both smooth and singular
   homology with a point, so the inclusion is a quasi-isomorphism in every degree
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`). This applies to
   every nonempty open subset contained in a smooth chart whose extended-chart image is star-convex
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`), in particular to
   every convex-in-chart open set.
2. **Binary unions:** For two open subsets `U` and `V` of `M`, the smooth singular subcomplexes of
   `U ⊓ V`, `U`, and `V` form a pushout square with the smooth simplices of `U ⊔ V` subordinate
   to `{U, V}`, mapping into the corresponding pushout square of singular simplicial sets. Applying
   the five lemma (`HomologicalComplex.HomologySequence.quasiIso_τ₃`) to the resulting map of
   Mayer–Vietoris short exact sequences of chain complexes and combining with the small-chain
   theorem for both smooth and singular chains yields the binary-union step
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`).
3. **Countable disjoint unions:** Additivity over pairwise disjoint open sets
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`) closes the induction,
   yielding the result on every open subset of `M`
   (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens`) and hence on `M` itself.

## Main definitions and results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`: the inclusion is a
  quasi-isomorphism on any empty manifold.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`: the inclusion is a
  quasi-isomorphism on any smoothly contractible manifold.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`: the inclusion is a
  quasi-isomorphism on any open subset of a smooth chart whose extended-chart image is star-convex.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the binary Mayer–Vietoris
  step comparing smooth and singular chains on `U ⊔ V`.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: the smoothing theorem as a
  quasi-isomorphism on every open subset of `M` and on `M`.
* `TauCeti.smoothSingularHomologyIso`: the natural isomorphism between smooth and continuous
  singular homology.
* `TauCeti.smoothSingularChainHomotopyEquiv`,
  `TauCeti.smoothSingularChainHomotopyEquivInvNaturality`: the smoothing theorem as a chain
  homotopy equivalence over a semisimple ring, with homotopy-natural inverse.
* `TauCeti.smoothSingularCochainHomotopyEquiv`,
  `TauCeti.smoothSingularCochainHomotopyEquivInvNaturality`,
  `TauCeti.smoothSingularCohomologyIso`: the dual cochain homotopy equivalence (with
  homotopy-natural inverse) and natural cohomology isomorphism over a commutative semisimple ring.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Set Function Simplicial Opposite
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

/-! ### Empty and smoothly contractible manifolds -/

section Contractible

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
  [CategoryWithHomology C] (R : C)

variable (I M) in
/-- On an empty manifold, both the smooth and continuous singular chain complexes are zero, so
the inclusion of smooth chains into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty [IsEmpty M] :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have hsing : (TopCat.toSSet.obj (TopCat.of M)).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      IsEmpty.false ((TopCat.of M).toSSetObjEquiv _ σ (Convexity.StdSimplex.single 0))
  have hsm : (smoothSingularSubcomplex I M : SSet).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦
      IsEmpty.false ((TopCat.of M).toSSetObjEquiv _ σ.1 (Convexity.StdSimplex.single 0))
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₁ : IsZero ((smoothSingularSubcomplex I M : SSet).homology R n) :=
    (HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)
  have h₂ : IsZero ((TopCat.toSSet.obj (TopCat.of M)).homology R n) :=
    (HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)
  exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

/-- **Smoothly contractible manifolds satisfy the smoothing theorem.** If a smooth map
`F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
inclusion of smooth singular chains into singular chains is a quasi-isomorphism in every degree. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M)
    (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let pt : TopCat.{u} := TopCat.of PUnit
  let a : TopCat.of M ⟶ pt := TopCat.ofHom (ContinuousMap.const M PUnit.unit)
  let b : pt ⟶ TopCat.of M := TopCat.ofHom (ContinuousMap.const pt c)
  have hba : b ≫ a = 𝟙 pt := by ext
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
    rw [← Category.assoc, hs, ← Functor.map_comp, hba, CategoryTheory.Functor.map_id]
  have hps : p ≫ s =
      smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι, smoothSingularSubcomplexMap_ι,
      Category.assoc, hs, Category.assoc, ← Functor.map_comp]
    rfl
  -- On smooth homology, `s` and `p` induce mutually inverse isomorphisms.
  have hs_iso : IsIso (SSet.homologyMap s R n) := ⟨⟨SSet.homologyMap p R n,
    by rw [← SSet.homologyMap_comp, hsp, SSet.homologyMap_id],
    by rw [← SSet.homologyMap_comp, hps,
        ← homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const
          hF h₀ h₁ n,
        smoothSingularSubcomplexMap_id, SSet.homologyMap_id]⟩⟩
  -- On singular homology, `b` and `a` likewise induce mutually inverse isomorphisms via `F`.
  let H : TopCat.Homotopy (𝟙 (TopCat.of M)) (a ≫ b) :=
    { toFun := fun q ↦ F (q.1, q.2)
      continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
      map_zero_left := h₀
      map_one_left := h₁ }
  have hb_iso : IsIso (SSet.homologyMap (TopCat.toSSet.map b) R n) :=
    ⟨⟨SSet.homologyMap (TopCat.toSSet.map a) R n,
      by rw [← SSet.homologyMap_comp, ← Functor.map_comp, hba, CategoryTheory.Functor.map_id,
          SSet.homologyMap_id],
      by rw [← SSet.homologyMap_comp, ← Functor.map_comp]
         have hH := (H.congr_homologyMap_singularChainComplexFunctor R n).symm
         rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at hH
         exact hH⟩⟩
  have hcomp : SSet.homologyMap s R n ≫ SSet.homologyMap (smoothSingularSubcomplex I M).ι R n =
      SSet.homologyMap (TopCat.toSSet.map b) R n := by
    rw [← SSet.homologyMap_comp, hs]
  have : IsIso
      (SSet.homologyMap s R n ≫ SSet.homologyMap (smoothSingularSubcomplex I M).ι R n) :=
    hcomp ▸ hb_iso
  exact IsIso.of_isIso_comp_left (SSet.homologyMap s R n) _

/-- **Star-convex coordinate domains satisfy the smoothing theorem.** Let `U` be an open subset
contained in the source of a smooth chart `e ∈ IsManifold.maximalAtlas I ∞ M` whose
extended-chart image `e.extend I '' U` is star-convex about `e.extend I c` for some `c ∈ U`. Then
`U` is smoothly contractible, so the inclusion of its smooth singular chains into its singular
chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : Opens M} (hUe : (U : Set M) ⊆ e.source) {c : M} (hc : c ∈ U)
    (hstar : StarConvex ℝ (e.extend I c) (e.extend I '' (U : Set M))) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  let g : ℝ × U → E := fun p ↦
    e.extend I c + (1 - Real.smoothTransition p.1) • (e.extend I p.2.1 - e.extend I c)
  have hg_mem (p : ℝ × U) : g p ∈ e.extend I '' (U : Set M) :=
    hstar.add_smul_sub_mem ⟨p.2.1, p.2.2, rfl⟩
      (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hF_mem (p : ℝ × U) : (e.extend I).symm (g p) ∈ U := by
    obtain ⟨x, hxU, hxe⟩ := hg_mem p
    rw [← hxe, (e.extend I).left_inv (by rw [e.extend_source]; exact hUe hxU)]
    exact hxU
  let F : ℝ × U → U := fun p ↦ ⟨(e.extend I).symm (g p), hF_mem p⟩
  have hg_smooth : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ g := by
    have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have hx : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × U ↦ e.extend I p.2.1 :=
      (e.contMDiffOn_extend he).comp_contMDiff (contMDiff_subtype_val.comp contMDiff_snd)
        (fun p ↦ hUe p.2.2)
    exact ContMDiff.add contMDiff_const
      (ContMDiff.smul (ContMDiff.sub contMDiff_const hψ) (hx.sub contMDiff_const))
  have hF_smooth : ContMDiff (𝓘(ℝ).prod I) I ∞ F := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    refine (contMDiffOn_extend_symm he).comp_contMDiff hg_smooth fun p ↦ ?_
    obtain ⟨x, hxU, hxe⟩ := hg_mem p
    exact hxe ▸ ⟨e x, e.map_source (hUe hxU), rfl⟩
  refine quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF_smooth ⟨c, hc⟩
    (fun x ↦ Subtype.ext ?_) (fun x ↦ Subtype.ext ?_)
  · simp only [F, g, Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact (e.extend I).left_inv (by rw [e.extend_source]; exact hUe x.2)
  · simp only [F, g, Real.smoothTransition.one, sub_self, zero_smul, add_zero]
    exact (e.extend I).left_inv (by rw [e.extend_source]; exact hUe hc)

end Contractible

/-! ### The binary Mayer–Vietoris step -/

section MayerVietorisStep

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

private abbrev openInclHom {U W : Opens M} (h : U ≤ W) :
    TopCat.of ↥U ⟶ TopCat.of ↥W :=
  TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩

private lemma mono_toSSet_openInclHom {U W : Opens M} (h : U ≤ W) :
    Mono (TopCat.toSSet.map (openInclHom h)) :=
  have : Mono (openInclHom h) := (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)
  Functor.map_mono _ _

private lemma mono_smoothSingular_openInclHom (I : ModelWithCorners ℝ E H) {U W : Opens M}
    (h : U ≤ W) :
    Mono ((smoothSingularSubcomplex I U).ι ≫ TopCat.toSSet.map (openInclHom h)) :=
  have := mono_toSSet_openInclHom h
  mono_comp _ _

private lemma mem_range_toSSet_openInclHom_iff {U W : Opens M} (h : U ≤ W)
    {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj (TopCat.of ↥W)).obj n) :
    σ ∈ (SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom h))).obj n ↔
      Set.range ((TopCat.of ↥W).toSSetObjEquiv n σ) ⊆ Subtype.val ⁻¹' (U : Set M) := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨t, rfl⟩
    rw [TopCat.toSSetObjEquiv_toSSet_map_app]
    exact ((TopCat.of ↥U).toSSetObjEquiv n τ t).2
  · intro hsub
    let f : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), ↥U) :=
      ⟨fun t ↦ ⟨((TopCat.of ↥W).toSSetObjEquiv n σ t).1, hsub ⟨t, rfl⟩⟩,
        (continuous_subtype_val.comp
          ((TopCat.of ↥W).toSSetObjEquiv n σ).continuous).subtype_mk _⟩
    refine ⟨((TopCat.of ↥U).toSSetObjEquiv n).symm f, ?_⟩
    apply ((TopCat.of ↥W).toSSetObjEquiv n).injective
    ext t
    rw [TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply, Equiv.apply_symm_apply]
    rfl

private lemma range_smoothSingular_openInclHom (I : ModelWithCorners ℝ E H) {U W : Opens M}
    (h : U ≤ W) :
    SSet.Subcomplex.range
        ((smoothSingularSubcomplex I U).ι ≫ TopCat.toSSet.map (openInclHom h)) =
      SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom h)) ⊓
        smoothSingularSubcomplex I W := by
  ext n σ
  simp only [Subfunctor.min_obj, Set.mem_inter_iff]
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨⟨τ.1, rfl⟩, ?_⟩
    exact (smoothSingularSubcomplex_le_preimage (I := I) (J := I) (contMDiff_inclusion h)) n τ.2
  · rintro ⟨⟨τ, rfl⟩, hσ⟩
    have hτ : τ ∈ (smoothSingularSubcomplex I U).obj n := by
      rw [← smoothSingularSubcomplex_preimage_inclusion h]
      exact hσ
    exact ⟨⟨τ, hτ⟩, rfl⟩

/-- The small singular subcomplex of `U ⊔ V` subordinate to the open cover `{U, V}`. -/
private abbrev smallSingularOpens (U V : Opens M) :
    (TopCat.toSSet.obj (TopCat.of ↥(U ⊔ V))).Subcomplex :=
  (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
    ![Subtype.val ⁻¹' (U : Set M), Subtype.val ⁻¹' (V : Set M)]

private lemma range_openInclHom_inf (U V : Opens M) :
    SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ⊓
        SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) =
      SSet.Subcomplex.range (TopCat.toSSet.map
        (openInclHom (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V))) := by
  ext n σ
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_range_toSSet_openInclHom_iff]
  exact Set.subset_inter_iff.symm

private lemma range_openInclHom_sup (U V : Opens M) :
    SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ⊔
        SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) =
      smallSingularOpens U V := by
  ext n σ
  simp only [Subfunctor.max_obj, Set.mem_union, mem_range_toSSet_openInclHom_iff,
    TopCat.mem_smallSingularSubcomplex_iff, Fin.exists_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private lemma range_openInclHom_left_le (U V : Opens M) :
    SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ≤
      smallSingularOpens U V :=
  range_openInclHom_sup U V ▸ le_sup_left

private lemma range_openInclHom_right_le (U V : Opens M) :
    SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) ≤
      smallSingularOpens U V :=
  range_openInclHom_sup U V ▸ le_sup_right

private lemma isPushout_toSSet_opens (U V : Opens M) :
    IsPushout
      (TopCat.toSSet.map (openInclHom (inf_le_left : U ⊓ V ≤ U)))
      (TopCat.toSSet.map (openInclHom (inf_le_right : U ⊓ V ≤ V)))
      (SSet.Subcomplex.lift (TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V)))
        (range_openInclHom_left_le U V))
      (SSet.Subcomplex.lift (TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V)))
        (range_openInclHom_right_le U V)) := by
  have := mono_toSSet_openInclHom (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V)
  have := mono_toSSet_openInclHom (le_sup_left : U ≤ U ⊔ V)
  have := mono_toSSet_openInclHom (le_sup_right : V ≤ U ⊔ V)
  have bicart : SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range
        (TopCat.toSSet.map (openInclHom (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V))))
      (SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))))
      (SSet.Subcomplex.range (TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))))
      (smallSingularOpens U V) :=
    ⟨range_openInclHom_sup U V, range_openInclHom_inf U V⟩
  refine bicart.isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange _)) (asIso (SSet.Subcomplex.toRange _))
    (asIso (SSet.Subcomplex.toRange _)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (SSet.Subcomplex.range _).ι]
    simp only [Category.assoc, asIso_hom, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
      ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (SSet.Subcomplex.range _).ι]
    simp only [Category.assoc, asIso_hom, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
      ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (smallSingularOpens U V).ι]
    simp only [Category.assoc, asIso_hom, Iso.refl_hom, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, SSet.Subcomplex.lift_ι]
  · rw [← cancel_mono (smallSingularOpens U V).ι]
    simp only [Category.assoc, asIso_hom, Iso.refl_hom, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, SSet.Subcomplex.lift_ι]

private lemma range_smoothSingular_left_le (I : ModelWithCorners ℝ E H) (U V : Opens M) :
    SSet.Subcomplex.range
        ((smoothSingularSubcomplex I U).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ≤
      smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V := by
  rw [range_smoothSingular_openInclHom]
  exact le_inf inf_le_right (inf_le_left.trans (range_openInclHom_left_le U V))

private lemma range_smoothSingular_right_le (I : ModelWithCorners ℝ E H) (U V : Opens M) :
    SSet.Subcomplex.range
        ((smoothSingularSubcomplex I V).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) ≤
      smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V := by
  rw [range_smoothSingular_openInclHom]
  exact le_inf inf_le_right (inf_le_left.trans (range_openInclHom_right_le U V))

private lemma isPushout_smoothSingular_opens (I : ModelWithCorners ℝ E H) (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion (I := I) _))
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion (I := I) _))
      (SSet.Subcomplex.lift
        ((smoothSingularSubcomplex I U).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V)))
        (range_smoothSingular_left_le I U V))
      (SSet.Subcomplex.lift
        ((smoothSingularSubcomplex I V).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V)))
        (range_smoothSingular_right_le I U V)) := by
  have := mono_smoothSingular_openInclHom I (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V)
  have := mono_smoothSingular_openInclHom I (le_sup_left : U ≤ U ⊔ V)
  have := mono_smoothSingular_openInclHom I (le_sup_right : V ≤ U ⊔ V)
  have h_inf : SSet.Subcomplex.range
        ((smoothSingularSubcomplex I U).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ⊓
      SSet.Subcomplex.range
        ((smoothSingularSubcomplex I V).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) =
      SSet.Subcomplex.range
        ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
          TopCat.toSSet.map
            (openInclHom (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V))) := by
    rw [range_smoothSingular_openInclHom, range_smoothSingular_openInclHom,
      range_smoothSingular_openInclHom, ← range_openInclHom_inf]
    exact (inf_inf_distrib_right _ _ _).symm
  have h_sup : SSet.Subcomplex.range
        ((smoothSingularSubcomplex I U).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_left : U ≤ U ⊔ V))) ⊔
      SSet.Subcomplex.range
        ((smoothSingularSubcomplex I V).ι ≫
          TopCat.toSSet.map (openInclHom (le_sup_right : V ≤ U ⊔ V))) =
      smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V := by
    rw [range_smoothSingular_openInclHom, range_smoothSingular_openInclHom,
      ← Subfunctor.max_min, range_openInclHom_sup, inf_comm]
  have bicart : SSet.Subcomplex.BicartSq _ _ _
      (smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V) := ⟨h_sup, h_inf⟩
  refine bicart.isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange _)) (asIso (SSet.Subcomplex.toRange _))
    (asIso (SSet.Subcomplex.toRange _)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (SSet.Subcomplex.range _).ι]
    simp only [Category.assoc, asIso_hom, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
      smoothSingularSubcomplexMap_ι_assoc, ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (SSet.Subcomplex.range _).ι]
    simp only [Category.assoc, asIso_hom, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
      smoothSingularSubcomplexMap_ι_assoc, ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V).ι]
    simp only [Category.assoc, asIso_hom, Iso.refl_hom, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, SSet.Subcomplex.lift_ι]
  · rw [← cancel_mono (smoothSingularSubcomplex I ↥(U ⊔ V) ⊓ smallSingularOpens U V).ι]
    simp only [Category.assoc, asIso_hom, Iso.refl_hom, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, SSet.Subcomplex.lift_ι]

/-- **The binary Mayer–Vietoris step of the smoothing theorem.** In an abelian category `C` with
coproducts, if the inclusion of smooth singular chains into singular chains with coefficients in `R`
is a quasi-isomorphism on open subsets `U`, `V`, and `U ⊓ V` of `M`, then it is a
quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup
    {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)
    (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  let K := smallSingularOpens U V
  have := mono_toSSet_openInclHom (inf_le_left : U ⊓ V ≤ U)
  have := mono_smoothSingular_openInclHom I (inf_le_left : U ⊓ V ≤ U)
  have ht_sm_mono : Mono (smoothSingularSubcomplexMap (I := I) (J := I)
      (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion (I := I) _)) :=
    mono_of_mono_fac
      (smoothSingularSubcomplexMap_ι (I := I) (J := I)
        (contMDiff_inclusion (I := I) (inf_le_left : U ⊓ V ≤ U)))
  let sq_sm := isPushout_smoothSingular_opens I U V
  let sq_sing := isPushout_toSSet_opens U V
  let φ := SSet.mayerVietorisShortComplexMap R sq_sm sq_sing
    (φ₁ := (smoothSingularSubcomplex I ↥(U ⊓ V)).ι)
    (φ₂ := (smoothSingularSubcomplex I U).ι)
    (φ₃ := (smoothSingularSubcomplex I V).ι)
    (φ₄ := SSet.Subcomplex.homOfLE (inf_le_right : S ⊓ K ≤ K))
    (smoothSingularSubcomplexMap_ι (contMDiff_inclusion _))
    (smoothSingularSubcomplexMap_ι (contMDiff_inclusion _))
    (by
      rw [← cancel_mono K.ι, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.lift_ι,
        Category.assoc, SSet.Subcomplex.lift_ι])
    (by
      rw [← cancel_mono K.ι, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.lift_ι,
        Category.assoc, SSet.Subcomplex.lift_ι])
  have hτ₂ : QuasiIso φ.τ₂ := by
    rw [SSet.mayerVietorisShortComplexMap_τ₂]
    exact HomologicalComplex.quasiIso_biprod_map _ _
  have hτ₃ : QuasiIso φ.τ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (SSet.shortExact_mayerVietorisShortComplex R sq_sm)
    (SSet.shortExact_mayerVietorisShortComplex R sq_sing)
    (by rwa [SSet.mayerVietorisShortComplexMap_τ₁]) hτ₂
  rw [SSet.mayerVietorisShortComplexMap_τ₃] at hτ₃
  have hτ₃' : QuasiIso
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : S ⊓ K ≤ K)) R) := hτ₃
  -- Combine with the small-chain theorem for both smooth and singular chains on `U ⊔ V`.
  have hU' : IsOpen (Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)) :=
    U.isOpen.preimage continuous_subtype_val
  have hV' : IsOpen (Subtype.val ⁻¹' (V : Set M) : Set ↥(U ⊔ V)) :=
    V.isOpen.preimage continuous_subtype_val
  have hcov : ⋃ i, (![Subtype.val ⁻¹' (U : Set M), Subtype.val ⁻¹' (V : Set M)] i :
      Set ↥(U ⊔ V)) = Set.univ := by
    ext ⟨x, hx⟩
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_univ, iff_true, Set.mem_preimage]
    exact hx
  have hsm_small : QuasiIso
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ K ≤ S)) R) :=
    quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R S _ (hU'.vecCons hV') hcov
  have hsing_small : QuasiIso (SSet.chainComplexMap K.ι R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplex_ι R _ (hU'.vecCons hV') hcov
  have hcomm : SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ K ≤ S)) R ≫
        SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : S ⊓ K ≤ K)) R ≫
        SSet.chainComplexMap K.ι R := by
    rw [← Functor.map_comp, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.homOfLE_ι]
  have hcomp : QuasiIso
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ K ≤ S)) R ≫
        SSet.chainComplexMap S.ι R) := by
    rw [hcomm]
    infer_instance
  exact (quasiIso_iff_comp_left
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ K ≤ S)) R)
    (SSet.chainComplexMap S.ι R)).mp hcomp

end MayerVietorisStep

/-! ### The smoothing theorem (quasi-isomorphism and homology isomorphism) -/

section QuasiIso

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete (ULift.{u} ℕ)) C] (R : C)

/-- **The smoothing theorem on open subsets.** On every open subset `U` of a Hausdorff, σ-compact
smooth manifold modelled on a locally compact real model with corners `I`, the inclusion of smooth
singular chains into singular chains with coefficients in `R` is a quasi-isomorphism, whenever
countable coproducts are exact in `C`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (U : Opens M) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  refine I.mayerVietoris_induction
    (fun U : Opens M ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    ?_ ?_ ?_ ?_ U
  · have : IsEmpty ↥(⊥ : Opens M) := ⟨fun x ↦ x.2⟩
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty I ↥(⊥ : Opens M) R
  · intro e he U ⟨c, hc⟩ hUe hconv
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex R
      (IsManifold.subset_maximalAtlas he) hUe hc (hconv.starConvex ⟨c, hc, rfl⟩)
  · intro U V hU hV hUV
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup R U V hU hV hUV
  · intro s hs hPs
    let s' : ULift.{u} ℕ → Opens M := s ∘ ULift.down
    have hs' : Pairwise (Disjoint on s') := fun i j hij ↦ hs fun h ↦ hij (ULift.ext h)
    have hsup : (⨆ i : ULift.{u} ℕ, s' i) = ⨆ n : ℕ, s n := Equiv.ulift.iSup_comp (g := s)
    rw [← hsup]
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup (I := I) s' C R hs'
      fun i ↦ hPs i.down

/-- **The smoothing theorem.** For a Hausdorff, σ-compact smooth manifold `M` modelled on a locally
compact real model with corners `I`, the inclusion of smooth singular chains into singular chains
with coefficients in `R` is a quasi-isomorphism, whenever countable coproducts are exact in `C`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have htop := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens I M R ⊤
  let toM : ↥(⊤ : Opens M) → M := Subtype.val
  let ofM : M → ↥(⊤ : Opens M) := fun x ↦ ⟨x, trivial⟩
  have htoM : ContMDiff I I ∞ toM := contMDiff_subtype_val
  have hofM : ContMDiff I I ∞ ofM := (ContMDiff.subtypeVal_comp_iff ⊤ ofM).mp contMDiff_id
  let f_sm := smoothSingularSubcomplexMap toM htoM
  let g_sm := smoothSingularSubcomplexMap ofM hofM
  have hf_sm_iso : IsIso f_sm := ⟨⟨g_sm,
    by rw [← smoothSingularSubcomplexMap_comp]; exact smoothSingularSubcomplexMap_id,
    by rw [← smoothSingularSubcomplexMap_comp]; exact smoothSingularSubcomplexMap_id⟩⟩
  let toMTop : TopCat.of ↥(⊤ : Opens M) ⟶ TopCat.of M :=
    TopCat.ofHom ⟨toM, htoM.continuous⟩
  let ofMTop : TopCat.of M ⟶ TopCat.of ↥(⊤ : Opens M) :=
    TopCat.ofHom ⟨ofM, hofM.continuous⟩
  have hto_of : toMTop ≫ ofMTop = 𝟙 _ := rfl
  have hof_to : ofMTop ≫ toMTop = 𝟙 _ := rfl
  let f_sing := TopCat.toSSet.map toMTop
  let g_sing := TopCat.toSSet.map ofMTop
  have hf_sing_iso : IsIso f_sing := ⟨⟨g_sing,
    by rw [← Functor.map_comp, hto_of, CategoryTheory.Functor.map_id],
    by rw [← Functor.map_comp, hof_to, CategoryTheory.Functor.map_id]⟩⟩
  have hcomm : SSet.chainComplexMap f_sm R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R =
      SSet.chainComplexMap (smoothSingularSubcomplex I ↥(⊤ : Opens M)).ι R ≫
        SSet.chainComplexMap f_sing R := by
    rw [← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι]
  have hcomp : QuasiIso (SSet.chainComplexMap f_sm R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
    rw [hcomm]
    infer_instance
  exact (quasiIso_iff_comp_left (SSet.chainComplexMap f_sm R)
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)).mp hcomp

/-- **Isomorphism between smooth and continuous singular homology.** On a Hausdorff, σ-compact
smooth manifold modelled on a locally compact real model with corners, the inclusion of smooth
singular simplices induces an isomorphism on homology in every degree, natural in smooth maps. -/
def smoothSingularHomologyIso (n : ℕ) :
    (smoothSingularSubcomplex I M : SSet).homology R n ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology R n :=
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R
  asIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)

/-- The forward map of `smoothSingularHomologyIso` is the map on homology induced by the inclusion
of smooth singular simplices. -/
@[simp]
theorem smoothSingularHomologyIso_hom (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n :=
  (rfl)

/-- The isomorphism between smooth and continuous singular homology is natural in smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
        (smoothSingularHomologyIso J N R n).hom := by
  rw [smoothSingularHomologyIso_hom, smoothSingularHomologyIso_hom,
    ← SSet.homologyMap_comp, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]

/-- The inverse of `smoothSingularHomologyIso` is natural in smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_inv_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).inv ≫
        SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (smoothSingularHomologyIso J N R n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, smoothSingularHomologyIso_naturality I M R hf n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end QuasiIso

/-! ### Chain homotopy equivalence and dual cochain equivalence over semisimple rings -/

section HomotopyEquiv

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

section ChainEquiv

variable {K : Type v} [Ring K] [IsSemisimpleRing K] (A : ModuleCat.{max u v} K)

/-- **The smoothing theorem as a chain homotopy equivalence.** Over any semisimple ring `K` — in
particular over any field such as `ℝ` — the inclusion of smooth singular chains into singular
chains of a Hausdorff, σ-compact smooth manifold `M` modelled on a locally compact real model with
corners is a chain homotopy equivalence, with chosen homotopy inverse and chain homotopies. -/
def smoothSingularChainHomotopyEquiv :
    HomotopyEquiv
      ((smoothSingularSubcomplex I M : SSet).chainComplex A)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex A) := by
  have : AB4OfSize.{u} (ModuleCat.{max u v} K) := AB4OfSize_shrink.{u, v} _
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M A
  exact HomotopyEquiv.ofQuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι A)

/-- The forward map of `smoothSingularChainHomotopyEquiv` is the inclusion of smooth singular
chains into singular chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquiv_hom :
    (smoothSingularChainHomotopyEquiv I M A).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι A := by
  have : AB4OfSize.{u} (ModuleCat.{max u v} K) := AB4OfSize_shrink.{u, v} _
  have := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M A
  exact HomotopyEquiv.ofQuasiIso_hom _

/-- **Naturality up to homotopy of the smoothing inverse.** For any smooth map `f : M → N`, the
chosen homotopy inverse of `smoothSingularChainHomotopyEquiv` commutes up to an explicit chain
homotopy with the chain maps induced by `f`. -/
def smoothSingularChainHomotopyEquivInvNaturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    Homotopy
      ((smoothSingularChainHomotopyEquiv I M A).inv ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) A)
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) A ≫
        (smoothSingularChainHomotopyEquiv J N A).inv) := by
  let eM := smoothSingularChainHomotopyEquiv I M A
  let eN := smoothSingularChainHomotopyEquiv J N A
  let f_sm := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) A
  let f_sing := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) A
  have hcomm :
      (eM.inv ≫ f_sm) ≫ (eN.hom ≫ eN.inv) = (eM.inv ≫ eM.hom) ≫ (f_sing ≫ eN.inv) := by
    have h : f_sm ≫ eN.hom = eM.hom ≫ f_sing := by
      simp only [eM, eN, f_sm, f_sing, smoothSingularChainHomotopyEquiv_hom, ← Functor.map_comp,
        smoothSingularSubcomplexMap_ι]
    simp only [Category.assoc, reassoc_of% h]
  exact (Homotopy.ofEq (Category.comp_id _).symm).trans
    ((eN.homotopyHomInvId.symm.compLeft _).trans
      ((Homotopy.ofEq hcomm).trans
        ((eM.homotopyInvHomId.compRight _).trans (Homotopy.ofEq (Category.id_comp _)))))

end ChainEquiv

section CochainEquiv

variable {K : Type v} [CommRing K] [IsSemisimpleRing K] (A B : ModuleCat.{max u v} K)

/-- **The dual smoothing theorem as a cochain homotopy equivalence.** Over any commutative
semisimple ring `K` — in particular over any field such as `ℝ` — restriction of singular
cochains to smooth singular simplices is a cochain homotopy equivalence. -/
def smoothSingularCochainHomotopyEquiv :
    HomotopyEquiv
      ((TopCat.of M).singularCochainComplex A K B)
      (((smoothSingularSubcomplex I M : SSet).chainComplex A).linearYonedaObj K B) :=
  (smoothSingularChainHomotopyEquiv I M A).linearYonedaFunctorMap K B

/-- The forward map of `smoothSingularCochainHomotopyEquiv` is restriction of singular cochains to
smooth singular simplices. -/
@[simp]
theorem smoothSingularCochainHomotopyEquiv_hom :
    (smoothSingularCochainHomotopyEquiv I M A B).hom =
      SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι := by
  rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_hom,
    smoothSingularChainHomotopyEquiv_hom]

/-- Restriction of singular cochains to smooth singular simplices is a quasi-isomorphism over any
commutative semisimple ring `K`. -/
theorem quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.cochainComplexMap (R := A) (k := K) (M := B)
      (smoothSingularSubcomplex I M).ι) := by
  rw [← smoothSingularCochainHomotopyEquiv_hom I M A B]
  exact (smoothSingularCochainHomotopyEquiv I M A B).quasiIso_hom

/-- **Naturality up to homotopy of the cochain smoothing inverse.** For any smooth map
`f : M → N`, the chosen homotopy inverse of `smoothSingularCochainHomotopyEquiv` commutes up to
an explicit cochain homotopy with the pullback maps on cochains induced by `f`. -/
def smoothSingularCochainHomotopyEquivInvNaturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    Homotopy
      (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf) ≫
        (smoothSingularCochainHomotopyEquiv I M A B).inv)
      ((smoothSingularCochainHomotopyEquiv J N A B).inv ≫
        TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩)) := by
  have hlhs : SSet.cochainComplexMap (R := A) (k := K) (M := B)
      (smoothSingularSubcomplexMap f hf) ≫
        (smoothSingularCochainHomotopyEquiv I M A B).inv =
      (ChainComplex.linearYonedaFunctor K B).map
        ((smoothSingularChainHomotopyEquiv I M A).inv ≫
          SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) A).op := by
    rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_inv]
    exact ((ChainComplex.linearYonedaFunctor K B).map_comp
      (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) A).op
      (smoothSingularChainHomotopyEquiv I M A).inv.op).symm
  have hrhs : (ChainComplex.linearYonedaFunctor K B).map
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) A ≫
          (smoothSingularChainHomotopyEquiv J N A).inv).op =
      (smoothSingularCochainHomotopyEquiv J N A B).inv ≫
        TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩) := by
    rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_inv]
    exact (ChainComplex.linearYonedaFunctor K B).map_comp
      (smoothSingularChainHomotopyEquiv J N A).inv.op
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) A).op
  exact (Homotopy.ofEq hlhs).trans
    (((smoothSingularChainHomotopyEquivInvNaturality I M A hf).linearYonedaFunctorMap K B).trans
      (Homotopy.ofEq hrhs))

/-- **Isomorphism between singular cohomology and smooth singular cohomology.** Over any
commutative semisimple ring `K` (such as `ℝ`), restriction of singular cochains to smooth singular
simplices induces a natural isomorphism in every degree. -/
def smoothSingularCohomologyIso (n : ℕ) :
    (TopCat.of M).singularCohomology A K B n ≅
      (((smoothSingularSubcomplex I M : SSet).chainComplex A).linearYonedaObj K B).homology n :=
  (smoothSingularCochainHomotopyEquiv I M A B).toHomologyIso n

/-- The forward map of `smoothSingularCohomologyIso` is the cohomology map induced by restricting
singular cochains to smooth singular simplices. -/
@[simp]
theorem smoothSingularCohomologyIso_hom (n : ℕ) :
    (smoothSingularCohomologyIso I M A B n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι) n :=
  congrArg (HomologicalComplex.homologyMap · n)
    (smoothSingularCochainHomotopyEquiv_hom I M A B)

/-- The isomorphism between singular cohomology and smooth singular cohomology is natural in smooth
maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n ≫
        (smoothSingularCohomologyIso I M A B n).hom =
      (smoothSingularCohomologyIso J N A B n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)) n := by
  rw [smoothSingularCohomologyIso_hom, smoothSingularCohomologyIso_hom,
    TopCat.singularCohomologyMap, TopCat.singularCochainComplexMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp,
    smoothSingularSubcomplexMap_ι]

/-- The inverse of `smoothSingularCohomologyIso` is natural in smooth maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_inv_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)) n ≫
        (smoothSingularCohomologyIso I M A B n).inv =
      (smoothSingularCohomologyIso J N A B n).inv ≫
        TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n := by
  rw [Iso.comp_inv_eq, Category.assoc, smoothSingularCohomologyIso_naturality I M A B hf n,
    Iso.inv_hom_id_assoc]

end CochainEquiv

end HomotopyEquiv

end TauCeti
