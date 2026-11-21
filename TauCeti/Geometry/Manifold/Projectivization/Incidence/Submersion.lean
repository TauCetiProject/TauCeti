/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Projectivization.Incidence.Basic
public import TauCeti.Topology.Algebra.Projectivization.Incidence
import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Parameter-preserving charts for projective incidence

At a full-rank point of a homogeneous polynomial family, one can straighten the incidence equations
without changing the parameter. In the resulting complex coordinates the incidence space is a
coordinate slice and the parameter projection on the slice is an ordinary product projection.
Over an open set with full-rank fibers this gives a proper holomorphic submersion.
A finite-dimensional parameter space can map to the homogeneous coefficients by any continuous
linear map; for the universal family one uses the inverse monomial-coefficient equivalence.

The construction uses the submersion normal form for the joint map to parameters and equation
values (cf. J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 4).
-/

public section

open Function Set MvPolynomial Projectivization Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {ι F : Type*} {n : ℕ} {d : ι → ℕ} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local notation "A" => (Fin n → ℂ)
local notation "P" => (Projectivization ℂ (Fin (n + 1) → ℂ))
local notation "V" => (ι → ℂ)
local notation "D" => (Fin (n - Fintype.card ι) → ℂ)

variable (Φ : F →L[ℂ] (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)))

/-- The augmented equations in affine coordinates keep the parameter as their first output. -/
private noncomputable def augmentedEquations (i : Fin (n + 1)) (z : A × F) : F × V :=
  (z.2, projectiveIncidenceChartEquations i z.1 (Φ z.2))

private theorem contDiff_augmentedEquations (i : Fin (n + 1)) :
    ContDiff ℂ ω (augmentedEquations Φ i) :=
  contDiff_snd.prodMk <| AnalyticOnNhd.contDiff fun z _ ↦
    analyticAt_projectiveIncidenceChartEquations_comp Φ i z

omit [Fintype ι] in
private theorem surjective_fderiv_augmentedEquations [Finite ι] (i : Fin (n + 1)) (a : A) (b : F)
    (hrank : Surjective (fderiv ℂ (fun x ↦ projectiveIncidenceChartEquations i x (Φ b)) a)) :
    Surjective (fderiv ℂ (augmentedEquations Φ i) (a, b)) := by
  let := Fintype.ofFinite ι
  have h := hasFDerivAt_projectiveIncidenceChartEquations_comp Φ i a b
  unfold augmentedEquations
  rw [(hasFDerivAt_snd.prodMk h).fderiv]
  intro y
  obtain ⟨x, hx⟩ := hrank (y.2 - projectiveIncidenceChartEquations i a (Φ y.1))
  exact ⟨(x, y.1), by
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.comp_apply, hx, sub_add_cancel]
    rfl⟩

private theorem exists_augmentedEquations_chart [FiniteDimensional ℂ F]
    (i : Fin (n + 1)) (a : A) (b : F)
    (hrank : Surjective (fderiv ℂ (fun x ↦ projectiveIncidenceChartEquations i x (Φ b)) a)) :
    ∃ e : OpenPartialHomeomorph (A × F) ((F × D) × V), (a, b) ∈ e.source ∧
      ContDiffOn ℂ ω e e.source ∧ ContDiffOn ℂ ω e.symm e.target ∧
      ∀ z ∈ e.source, ((e z).1.1, (e z).2) = augmentedEquations Φ i z := by
  have hs : Surjective (mfderiv 𝓘(ℂ, A × F) 𝓘(ℂ, F × V) (augmentedEquations Φ i) (a, b)) := by
    rw [mfderiv_eq_fderiv]
    exact surjective_fderiv_augmentedEquations Φ i a b hrank
  obtain ⟨φ, L, hz, hφ, _, hEq⟩ :=
    (contDiff_augmentedEquations Φ i).contMDiff.contMDiffOn
      |>.exists_domChart_mem_maximalAtlas_of_surjective_mfderiv (U := univ) isOpen_univ
        (mem_univ (a, b)) (by simp) hs
  have hdim : Module.finrank ℂ (A × F) - Module.finrank ℂ (F × V) = n - Fintype.card ι := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  let K₀ := Fin (Module.finrank ℂ (A × F) - Module.finrank ℂ (F × V)) → ℂ
  let k : K₀ ≃L[ℂ] D := ContinuousLinearEquiv.ofFinrankEq (by
    dsimp only [K₀]
    simp only [Module.finrank_fin_fun, hdim])
  let perm : ((F × V) × K₀) ≃L[ℂ] (F × D) × V :=
    (ContinuousLinearEquiv.prodAssoc ℂ F V K₀).trans <|
      ((ContinuousLinearEquiv.refl ℂ F).prodCongr
        ((ContinuousLinearEquiv.prodComm ℂ V K₀).trans
          (k.prodCongr (ContinuousLinearEquiv.refl ℂ V)))).trans
        (ContinuousLinearEquiv.prodAssoc ℂ F D V).symm
  let e := φ.transHomeomorph (L.trans perm).toHomeomorph
  have hφ₁ := contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_maximalAtlas hφ)
  have hφ₂ := contMDiffOn_iff_contDiffOn.mp (contMDiffOn_symm_of_mem_maximalAtlas hφ)
  refine ⟨e, hz, (L.trans perm).contDiff.comp_contDiffOn hφ₁, ?_, ?_⟩
  · exact hφ₂.comp (L.trans perm).symm.contDiff.contDiffOn fun v hv ↦ hv
  · intro z hz'
    simp only [OpenPartialHomeomorph.extend_modelWithCornersSelf, chartAt_self_eq] at hEq
    have h := hEq (φ.map_source hz')
    simpa [e, perm, φ.left_inv hz', OpenPartialHomeomorph.transHomeomorph_apply] using h.symm

/-- At an incidence point with surjective cone Jacobian, there is a holomorphic chart of the
ambient product in which the first coordinate is the parameter and the last coordinate is the
family of affine chart equations. On the chart source, vanishing of the last coordinate is
exactly membership in the pulled-back incidence space. The middle coordinate has complex
dimension `n - |ι|`. -/
theorem exists_complexProjectiveIncidence_submersionChart [FiniteDimensional ℂ F]
    {b : F} {L : P} {i : Fin (n + 1)} (hi : L ∈ affineOpen i)
    (hL : (Φ b, L) ∈ complexProjectiveIncidence (n + 1) d)
    (hrank : Surjective (jacobiMatrixAt (fun k ↦ (Φ b k : MvPolynomial (Fin (n + 1)) ℂ))
      L.rep).mulVec) :
    ∃ e : OpenPartialHomeomorph (F × P) ((F × D) × V), (b, L) ∈ e.source ∧
      ContMDiffOn (𝓘(ℂ, F).prod 𝓘(ℂ, A)) 𝓘(ℂ, (F × D) × V) ω e e.source ∧
      ContMDiffOn 𝓘(ℂ, (F × D) × V) (𝓘(ℂ, F).prod 𝓘(ℂ, A)) ω e.symm e.target ∧
      ∀ z ∈ e.source, z.2 ∈ affineOpen i ∧ (e z).1.1 = z.1 ∧
        (e z).2 = projectiveIncidenceChartEquations i (affineChart i z.2) (Φ z.1) := by
  have hs := (surjective_fderiv_eval_dehomogenize_affineChart_iff i
    (fun k ↦ (mem_homogeneousSubmodule _ _).mp (Φ b k).property)
    (mem_complexProjectiveIncidence.mp hL) hi).2 hrank
  obtain ⟨e₁, he₁, he₁f, he₁b, he₁eq⟩ :=
    exists_augmentedEquations_chart Φ i (affineChart i L) b (by simpa only
      [projectiveIncidenceChartEquations_apply] using hs)
  let e₀ := ((OpenPartialHomeomorph.refl F).prod (affineOpenPartialHomeomorph i)).transHomeomorph
    (Homeomorph.prodComm F A)
  let e := e₀.trans e₁
  have he₀_apply (z : F × P) : e₀ z = (affineChart i z.2, z.1) := by
    simp [e₀, OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.prod_apply,
      coe_affineOpenPartialHomeomorph]
  have he₀_symm_apply (z : A × F) : e₀.symm z = (z.2, (affineChart i).symm z.1) := by
    simp [e₀, OpenPartialHomeomorph.transHomeomorph_symm_apply,
      coe_affineOpenPartialHomeomorph_symm]
  have he₀_source : e₀.source = univ ×ˢ affineOpen i := by
    simp [e₀]
  have he₀f : ContMDiffOn (𝓘(ℂ, F).prod 𝓘(ℂ, A)) 𝓘(ℂ, A × F) ω e₀ e₀.source := by
    apply ContMDiffOn.congr _ (fun z _ ↦ he₀_apply z)
    exact ((contMDiffOn_affineChart (𝕜 := ℂ) i ω).comp contMDiffOn_snd
      (fun z hz ↦ ((he₀_source ▸ hz) : z ∈ univ ×ˢ affineOpen i).2)).prodMk_space
      contMDiffOn_fst
  have he₀b : ContMDiffOn 𝓘(ℂ, A × F) (𝓘(ℂ, F).prod 𝓘(ℂ, A)) ω e₀.symm e₀.target := by
    refine ContMDiffOn.congr ?_ (fun z _ ↦ he₀_symm_apply z)
    have h : ContMDiffOn (𝓘(ℂ, A).prod 𝓘(ℂ, F)) (𝓘(ℂ, F).prod 𝓘(ℂ, A)) ω
        (fun z : A × F ↦ (z.2, (affineChart i).symm z.1)) e₀.target :=
      contMDiffOn_snd.prodMk ((contMDiff_affineChart_symm (𝕜 := ℂ) i ω).comp
        contMDiff_fst).contMDiffOn
    rwa [chartedSpaceSelf_prod, ← modelWithCornersSelf_prod] at h
  have hsource : ∀ z ∈ e₀.source, z.2 ∈ affineOpen i :=
    fun z hz ↦ ((he₀_source ▸ hz) : z ∈ univ ×ˢ affineOpen i).2
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · simp only [e, OpenPartialHomeomorph.trans_source, he₀_source, mem_inter_iff,
      mem_prod, mem_univ, mem_preimage, he₀_apply, true_and]
    exact ⟨hi, he₁⟩
  · exact he₁f.contMDiffOn.comp (he₀f.mono inter_subset_left) inter_subset_right
  · exact he₀b.comp (he₁b.contMDiffOn.mono inter_subset_left) inter_subset_right
  · intro z hz
    have h : ((e z).1.1, (e z).2) = (z.1,
        projectiveIncidenceChartEquations i (affineChart i z.2) (Φ z.1)) := by
      simpa only [e, OpenPartialHomeomorph.coe_trans, Function.comp_apply, augmentedEquations,
        he₀_apply] using he₁eq (e₀ z) hz.2
    exact ⟨hsource z hz.1, congrArg Prod.fst h, congrArg Prod.snd h⟩

section Family

variable [FiniteDimensional ℂ F] (U : TopologicalSpace.Opens F)

local notation "S" => (Set.inter (complexProjectiveFamily (fun b : F ↦ Φ b))
  (Set.preimage (@Prod.fst F P) (U : Set F)))

private theorem exists_familySliceChart (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec)
    (x : S) :
    ∃ e : OpenPartialHomeomorph (F × P) ((F × D) × V), x.val ∈ e.source ∧
      ContMDiffOn (𝓘(ℂ, F).prod 𝓘(ℂ, A)) 𝓘(ℂ, (F × D) × V) ω e e.source ∧
      ContMDiffOn 𝓘(ℂ, (F × D) × V) (𝓘(ℂ, F).prod 𝓘(ℂ, A)) ω e.symm e.target ∧
      IsSliceChart e (univ ×ˢ ({0} : Set V)) S ∧ ∀ z ∈ e.source, (e z).1.1 = z.1 := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x.val.2
  have hx : (Φ x.val.1, x.val.2) ∈ complexProjectiveIncidence (n + 1) d :=
    mem_complexProjectiveIncidence.mpr (mem_complexProjectiveFamily.mp x.property.1)
  obtain ⟨e, he, hf, hb, h⟩ :=
    exists_complexProjectiveIncidence_submersionChart Φ hi hx (hrank x)
  let W : Set (F × P) := Prod.fst ⁻¹' (U : Set F)
  have hW : IsOpen W := U.isOpen.preimage continuous_fst
  refine ⟨e.restrOpen W hW, ⟨he, x.property.2⟩, hf.mono inter_subset_left,
    hb.mono inter_subset_left, isSliceChart_iff.2 ?_, fun z hz ↦ (h z hz.1).2.1⟩
  intro z hz
  obtain ⟨hzi, _, hval⟩ := h z hz.1
  simp only [mem_prod, mem_univ, true_and, mem_singleton_iff,
    OpenPartialHomeomorph.coe_restrOpen, hval]
  exact (and_iff_left hz.2).trans (mem_complexProjectiveFamily.trans
    (mem_complexProjectiveIncidence.symm.trans
      (mem_complexProjectiveIncidence_iff_projectiveIncidenceChartEquations_eq_zero _ hzi)))

private noncomputable def familySliceChart (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec)
    (x : S) : OpenPartialHomeomorph (F × P) ((F × D) × V) :=
  (exists_familySliceChart Φ U hrank x).choose

private theorem familySliceChart_spec (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec)
    (x : S) :
    x.val ∈ (familySliceChart Φ U hrank x).source ∧
      ContMDiffOn (𝓘(ℂ, F).prod 𝓘(ℂ, A)) 𝓘(ℂ, (F × D) × V) ω
        (familySliceChart Φ U hrank x) (familySliceChart Φ U hrank x).source ∧
      ContMDiffOn 𝓘(ℂ, (F × D) × V) (𝓘(ℂ, F).prod 𝓘(ℂ, A)) ω
        (familySliceChart Φ U hrank x).symm (familySliceChart Φ U hrank x).target ∧
      IsSliceChart (familySliceChart Φ U hrank x) (univ ×ˢ ({0} : Set V)) S ∧
      ∀ (z : F × P), z ∈ (familySliceChart Φ U hrank x).source →
        (familySliceChart Φ U hrank x z).1.1 = z.1 :=
  (exists_familySliceChart Φ U hrank x).choose_spec

/-- The complex atlas of a projective incidence family over an open parameter set whose fibers
are all full rank. Its charts retain the parameter as their first coordinate. -/
@[instance_reducible]
noncomputable def complexProjectiveFamilyChartedSpace (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec) :
    ChartedSpace (F × D) S :=
  linearSliceChartedSpace (familySliceChart Φ U hrank)
    (fun x ↦ (familySliceChart_spec Φ U hrank x).2.2.2.1)
    (fun x ↦ (familySliceChart_spec Φ U hrank x).1)

/-- The parameter-preserving slice charts form a complex manifold atlas. -/
theorem isManifold_complexProjectiveFamily (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec) :
    letI := complexProjectiveFamilyChartedSpace Φ U hrank
    IsManifold 𝓘(ℂ, F × D) ω S :=
  isManifold_linearSliceChartedSpace _ _
    (fun x _ hz ↦ (familySliceChart_spec Φ U hrank x).2.1.contMDiffAt
      ((familySliceChart Φ U hrank x).open_source.mem_nhds hz))
    (fun x _ hz ↦ (familySliceChart_spec Φ U hrank x).2.2.1.contMDiffAt
      ((familySliceChart Φ U hrank x).open_target.mem_nhds hz)) _

/-- In the incidence atlas the first coordinate of each chart is the parameter projection. -/
theorem fst_chartAt_complexProjectiveFamily (hrank : ∀ x : S, Surjective
    (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec)
    (x y : S)
    (hy : y ∈ (@chartAt _ _ _ _ (complexProjectiveFamilyChartedSpace Φ U hrank) x).source) :
    (@chartAt _ _ _ _ (complexProjectiveFamilyChartedSpace Φ U hrank) x y).1 = y.val.1 := by
  rw [complexProjectiveFamilyChartedSpace, linearSliceChartedSpace_chartAt, linearSliceChart_source,
    mem_preimage] at hy
  rw [complexProjectiveFamilyChartedSpace, linearSliceChartedSpace_chartAt, linearSliceChart_apply]
  exact (familySliceChart_spec Φ U hrank x).2.2.2.2 _ hy

/-- Over an open set of parameters with full-rank fibers, the parameter projection is proper and
is a holomorphic submersion with complement of complex dimension `n - |ι|`. -/
theorem isProperMap_and_isSubmersionOfComplement_fst_complexProjectiveFamily
    (hrank : ∀ x : S, Surjective
      (jacobiMatrixAt (fun k ↦ (Φ x.val.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.val.2.rep).mulVec) :
    letI := complexProjectiveFamilyChartedSpace Φ U hrank
    let p : S → U := fun x ↦ ⟨x.val.1, x.property.2⟩
    IsProperMap p ∧ IsSubmersionOfComplement D 𝓘(ℂ, F × D) 𝓘(ℂ, F) ω p := by
  let := complexProjectiveFamilyChartedSpace Φ U hrank
  have := isManifold_complexProjectiveFamily Φ U hrank
  refine ⟨?_, isSubmersionOfComplement_iff.mpr fun x ↦ ?_⟩
  · let i : S → complexProjectiveFamily (fun b : F ↦ Φ b) := Set.inclusion inter_subset_left
    have hi : Topology.IsEmbedding i := Topology.IsEmbedding.inclusion _
    refine (ComplexProjectiveFamily.isProperMap_fst _ Φ.continuous).of_isEmbedding_of_range_eq
      hi Topology.IsEmbedding.subtypeVal rfl ?_
    simp only [i, Set.range_inclusion, Subtype.range_coe_subtype]
    ext y
    exact and_iff_right y.property
  let p : S → U := fun y ↦ ⟨y.val.1, y.property.2⟩
  let a := chartAt (F × D) x
  let b := chartAt F (p x)
  have hb : ∀ y : U, b y = y.val := by
    intro y
    simp [b, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  have hb' : b.source = univ := by
    simp [b, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  refine IsSubmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.refl ℂ _) a b
    (mem_chart_source _ _) (mem_chart_source _ _) (IsManifold.chart_mem_maximalAtlas _)
    (IsManifold.chart_mem_maximalAtlas _) (by simp [hb']) ?_
  intro v hv
  have hv' : v ∈ a.target := by
    simpa only [OpenPartialHomeomorph.extend_modelWithCornersSelf] using hv
  have h := fst_chartAt_complexProjectiveFamily Φ U hrank x (a.symm v) (a.map_target hv')
  rw [a.right_inv hv'] at h
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_modelWithCornersSelf,
    OpenPartialHomeomorph.coe_toPartialEquiv, hb, ContinuousLinearEquiv.refl_apply]
  exact h.symm

end Family

end TauCeti
