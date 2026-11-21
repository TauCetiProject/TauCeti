/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich
public import TauCeti.Analysis.Sobolev.W1p.CompactMultiplication.Basic

/-!
# Compact multiplication by rough sections of a real hom bundle

For finite-dimensional real bundles over a compact boundaryless manifold of positive dimension
`n`, an order-zero Sobolev section of the real hom bundle with exponent `p > n` acts boundedly on
`W^{1,q}` sections with values in `W^{0,q}`, for every finite `1 ≤ q ≤ p`. For each fixed
coefficient the operator is compact. On a closed surface this includes every finite `1 < q ≤ p`,
including `q = p`, `q = 2` and `q < 2`, as well as the natural endpoint `q = 1`. The surface case
supplies the boundaryless case `ℓ = k = 1` of McDuff--Salamon, Lemma C.2.2. Bordered surfaces
and higher-order cases are not covered here.

The construction uses the native finite-atlas Sobolev spaces. Interior mixed multiplication and
Rellich compactness are transferred between charts and glued over a finite cover. The hom bundle
is over `ℝ`, so the coefficient need not be complex linear; no nonzero-rank assumption is made.

## Main declarations

* `TauCeti.SobolevSection.homMulL`: the bounded real bilinear multiplication operator; it is
  linear and continuous in the coefficient as an operator on the section space.
* `TauCeti.SobolevSection.chartValueL_homMulL_ae`,
  `TauCeti.SobolevSection.chartValueL_homMulL_ae_coord`: agreement with chart readings and
  with actual section representatives.
* `TauCeti.SobolevSection.exists_norm_homMulL_apply_le`: a uniform bilinear norm estimate.
* `TauCeti.SobolevSection.isCompactOperator_homMulL`: compactness with each coefficient fixed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Lemma C.2.2.
-/

public section
noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal NNReal Topology

universe u

namespace TauCeti.SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F₁ V₁)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

private def coefficientChartL (i : Fin A.n) {Q : Opens E} (hQ : Q ≤ A.image i) :
    SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ] Lp (F₁ →L[ℝ] F₂) p (μ.restrict Q) :=
  (Lp.LpToLpOfMeasureLeSMul (by simp)
    (show μ.restrict (Q : Set E) ≤ (1 : ℝ≥0∞) •
        μ.restrict ((A.hom (𝕜 := ℝ) h).sectionChartData.image i : Set E) by
      rw [one_smul, (A.hom (𝕜 := ℝ) h).sectionChartData_image i,
        FiniteBundleAtlas.image_hom]
      exact Measure.restrict_mono_set μ (SetLike.coe_subset_coe.2 hQ))).comp
    (((A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i).comp
      ((A.hom (𝕜 := ℝ) h).sectionChartData.sobolevSections μ p 0).subtypeL)

omit [Nontrivial E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem coefficientChartL_ae (i : Fin A.n) {Q : Opens E} (hQ : Q ≤ A.image i)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) :
    coefficientChartL A h μ i hQ α =ᵐ[μ.restrict Q]
      (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α := by
  dsimp only [coefficientChartL, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

private def inputComponentL (i : Fin A.n) (l : Fin (finrank ℝ F₁)) :
    SobolevSection A μ q 1 →L[ℝ] W1p μ (A.image i) q :=
  (ContinuousLinearMap.proj l).comp ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun i : Fin A.sectionChartData.n ↦
      ∀ _ : Fin (finrank ℝ F₁), Wkp μ (A.sectionChartData.image i) q 1) i).comp
        (A.sectionChartData.sobolevSections μ q 1).subtypeL)

omit [Nontrivial E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem inputComponentL_apply (i : Fin A.n) (l : Fin (finrank ℝ F₁))
    (ξ : SobolevSection A μ q 1) :
    inputComponentL A μ i l ξ = (ξ : A.sectionChartData.SobolevData μ q 1) i l :=
  (rfl)

private def columnBilin (l : Fin (finrank ℝ F₁)) : (F₁ →L[ℝ] F₂) →L[ℝ] ℝ →L[ℝ] F₂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip.comp
    (ContinuousLinearMap.apply ℝ F₂ (finBasis ℝ F₁ l))

private def localHomMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i) :
    SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ]
      SobolevSection A μ q 1 →L[ℝ] Lp F₂ q (μ.restrict Q) := by
  -- Naming the inherited component structures keeps instance search local in nested operators.
  letI : NormedAddCommGroup (SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) := inferInstance
  letI : NormedSpace ℝ (SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) := inferInstance
  letI : NormedAddCommGroup (SobolevSection A μ q 1) := inferInstance
  letI : NormedSpace ℝ (SobolevSection A μ q 1) := inferInstance
  exact ∑ l : Fin (finrank ℝ F₁),
    (W1p.mixedBilinL hp hqp hQc hQ (columnBilin (F₂ := F₂) l)).bilinearComp
    (coefficientChartL A h μ i (SetLike.coe_subset_coe.1 (subset_closure.trans hQ)))
    (inputComponentL A μ i l)

omit [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem localHomMulL_ae (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1) :
    localHomMulL A h μ hp hqp i hQc hQ α ξ =ᵐ[μ.restrict Q] fun y ↦
      coefficientChartL A h μ i (SetLike.coe_subset_coe.1 (subset_closure.trans hQ)) α y
        (∑ l, W1p.value (inputComponentL A μ i l ξ) y • finBasis ℝ F₁ l) := by
  let a := coefficientChartL A h μ i (SetLike.coe_subset_coe.1 (subset_closure.trans hQ)) α
  have heq : localHomMulL A h μ hp hqp i hQc hQ α ξ =
      ∑ l : Fin (finrank ℝ F₁), W1p.mixedBilinL hp hqp hQc hQ
        (columnBilin (F₂ := F₂) l) a (inputComponentL A μ i l ξ) := by
    simp only [localHomMulL, sum_apply, ContinuousLinearMap.bilinearComp_apply, a]
  rw [heq]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  filter_upwards [ae_all_iff.2 fun l ↦ W1p.coeFn_mixedBilinL hp hqp hQc hQ
    (columnBilin (F₂ := F₂) l) a (inputComponentL A μ i l ξ)] with y hy
  simp only [Finset.sum_apply]
  simp_rw [hy]
  simp only [columnBilin, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.apply_apply, map_sum, map_smul, a]

omit [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem localHomMulL_ae_coord (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x)
    (hα : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α
      =ᵐ[μ.restrict (A.image i)] (A.hom (𝕜 := ℝ) h).coord i φ)
    (hξ : A.sectionChartData.chartValueL μ q 1 i ξ
      =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    localHomMulL A h μ hp hqp i hQc hQ α ξ =ᵐ[μ.restrict Q]
      (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) := by
  have hsub : (Q : Set E) ⊆ A.image i := subset_closure.trans hQ
  filter_upwards [localHomMulL_ae A h μ hp hqp i hQc hQ α ξ,
    coefficientChartL_ae A h μ i (SetLike.coe_subset_coe.1 hsub) α,
    ae_restrict_of_ae_restrict_of_subset hsub hα,
    ae_restrict_of_ae_restrict_of_subset hsub
      (A.sectionChartData.chartValueL_apply_ae μ q 1 i ξ),
    ae_restrict_of_ae_restrict_of_subset hsub hξ,
    ae_restrict_mem Q.isOpen.measurableSet] with y hy hc hα hdata hξ hyQ
  simp only [inputComponentL_apply] at hy
  simp only [Wkp.value_one] at hdata
  rw [hy, hc, hα]
  exact (congrArg ((A.hom (𝕜 := ℝ) h).coord i φ y) (hdata.symm.trans hξ)).trans
    (A.coord_hom_apply h i φ s (hsub hyQ))

omit [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem isCompactOperator_localHomMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) :
    IsCompactOperator (localHomMulL A h μ hp hqp i hQc hQ α) := by
  let a := coefficientChartL A h μ i (SetLike.coe_subset_coe.1 (subset_closure.trans hQ)) α
  have heq : localHomMulL A h μ hp hqp i hQc hQ α =
      ∑ l : Fin (finrank ℝ F₁), (W1p.mixedBilinL hp hqp hQc hQ
        (columnBilin (F₂ := F₂) l) a).comp (inputComponentL A μ i l) := by
    ext ξ : 1
    simp only [localHomMulL, sum_apply, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.comp_apply, a]
  rw [heq]
  exact (compactOperator (RingHom.id ℝ) _ _).sum_mem fun l _ ↦
    (W1p.isCompactOperator_mixedBilinL hp hqp hQc hQ (columnBilin (F₂ := F₂) l) a).comp_clm
      (inputComponentL A μ i l)

private def localHomComponentsL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i) :
    SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ] SobolevSection A μ q 1 →L[ℝ]
      (Fin (finrank ℝ F₂) → Wkp μ Q q 0) :=
  ContinuousLinearMap.piBilin fun m ↦
    ((ContinuousLinearMap.compL ℝ (SobolevSection A μ q 1) _ _)
      (((finBasis ℝ F₂).coord m).toContinuousLinearMap.compLpL q (μ.restrict Q))).comp
        (localHomMulL A h μ hp hqp i hQc hQ)

omit [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem localHomComponentsL_ae_coord (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i : Fin A.n) {Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x)
    (hα : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α
      =ᵐ[μ.restrict (A.image i)] (A.hom (𝕜 := ℝ) h).coord i φ)
    (hξ : A.sectionChartData.chartValueL μ q 1 i ξ
      =ᵐ[μ.restrict (A.image i)] A.coord i s) (m : Fin (finrank ℝ F₂)) :
    (Wkp.value 0 (localHomComponentsL A h μ hp hqp i hQc hQ α ξ m) : E → ℝ)
      =ᵐ[μ.restrict Q] fun y ↦ (finBasis ℝ F₂).repr
        ((A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) y) m := by
  simp only [localHomComponentsL, ContinuousLinearMap.piBilin_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, Wkp.value_zero]
  filter_upwards [((finBasis ℝ F₂).coord m).toContinuousLinearMap.coeFn_compLpL
      (localHomMulL A h μ hp hqp i hQc hQ α ξ),
    localHomMulL_ae_coord A h μ hp hqp i hQc hQ α ξ φ s hα hξ] with y hy hz
  rw [hy, hz]
  simp only [LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]

omit [Nontrivial E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem exists_hom_section_ae_eq_coord
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) :
    ∃ φ : ∀ x, V₁ x →L[ℝ] V₂ x, ∀ i,
      (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α
        =ᵐ[μ.restrict (A.image i)] (A.hom (𝕜 := ℝ) h).coord i φ := by
  obtain ⟨φ, hφ⟩ := exists_ae_eq_coord α
  refine ⟨φ, fun i ↦ ?_⟩
  rw [← FiniteBundleAtlas.image_hom (A := A) (h := h) (𝕜 := ℝ) i]
  exact hφ i

omit [Nontrivial E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem chartHomProduct_ae_coord
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x) (i : Fin A.n)
    (hα : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α
      =ᵐ[μ.restrict (A.image i)] (A.hom (𝕜 := ℝ) h).coord i φ)
    (hξ : A.sectionChartData.chartValueL μ q 1 i ξ
      =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    (fun y ↦ (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α y
      (A.sectionChartData.chartValueL μ q 1 i ξ y))
      =ᵐ[μ.restrict ((A.ofBaseSet h).image i)] (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) := by
  rw [FiniteBundleAtlas.image_ofBaseSet]
  filter_upwards [hα, hξ, ae_restrict_mem (A.image i).isOpen.measurableSet] with y hα hξ hy
  rw [hα, hξ]
  exact A.coord_hom_apply h i φ s hy

private def pieceHomMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i j : Fin A.n) {P Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ (A.ofBaseSet h).transferDomain i j)
    (hPQ : MapsTo (((A.ofBaseSet h).chart j).symm ≫ₕ (A.ofBaseSet h).chart i) P Q)
    (m : Fin (finrank ℝ F₂)) :
    SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ] SobolevSection A μ q 1 →L[ℝ]
      Wkp μ P q 0 :=
  ((ContinuousLinearMap.compL ℝ (SobolevSection A μ q 1) _ _)
    ((ContinuousLinearMap.proj m).comp
      ((A.ofBaseSet h).transferL μ q 0 i j hPc hPD hPQ))).comp
        (localHomComponentsL A h μ hp hqp i hQc hQ)

omit [T2Space M] in
private theorem pieceHomMulL_ae_coord (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i j : Fin A.n) {P Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (hP : (P : Set E) ⊆ (A.ofBaseSet h).overlap i j)
    (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ (A.ofBaseSet h).transferDomain i j)
    (hPQ : MapsTo (((A.ofBaseSet h).chart j).symm ≫ₕ (A.ofBaseSet h).chart i) P Q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x)
    (hα : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 i α
      =ᵐ[μ.restrict (A.image i)] (A.hom (𝕜 := ℝ) h).coord i φ)
    (hξ : A.sectionChartData.chartValueL μ q 1 i ξ
      =ᵐ[μ.restrict (A.image i)] A.coord i s) (m : Fin (finrank ℝ F₂)) :
    (Wkp.value 0 (pieceHomMulL A h μ hp hqp i j hQc hQ hPc hPD hPQ m α ξ) : E → ℝ)
      =ᵐ[μ.restrict P] fun y ↦ (finBasis ℝ F₂).repr
        ((A.ofBaseSet h).coord j (fun x ↦ φ x (s x)) y) m := by
  simp only [pieceHomMulL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.proj_apply]
  exact (A.ofBaseSet h).value_transferL_ae_of_coord μ q 0 hP hPc hPD hPQ
    (fun x ↦ φ x (s x)) _
    (localHomComponentsL_ae_coord A h μ hp hqp i hQc hQ α ξ φ s hα hξ) m

omit [T2Space M] in
private theorem pieceHomMulL_ae (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i j : Fin A.n) {P Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i)
    (hP : (P : Set E) ⊆ (A.ofBaseSet h).overlap i j)
    (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ (A.ofBaseSet h).transferDomain i j)
    (hPQ : MapsTo (((A.ofBaseSet h).chart j).symm ≫ₕ (A.ofBaseSet h).chart i) P Q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (m : Fin (finrank ℝ F₂)) :
    (Wkp.value 0 (pieceHomMulL A h μ hp hqp i j hQc hQ hPc hPD hPQ m α ξ) : E → ℝ)
      =ᵐ[μ.restrict P] fun y ↦ (finBasis ℝ F₂).repr
        ((A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
          (A.sectionChartData.chartValueL μ q 1 j ξ y)) m := by
  obtain ⟨φ, hφ⟩ := exists_hom_section_ae_eq_coord A h μ α
  obtain ⟨s, hs⟩ := exists_ae_eq_coord ξ
  have ht := pieceHomMulL_ae_coord A h μ hp hqp i j hQc hQ hP hPc hPD hPQ
    α ξ φ s (hφ i) (hs i) m
  have hg := chartHomProduct_ae_coord A h μ α ξ φ s j (hφ j) (hs j)
  have hsub : (P : Set E) ⊆ (A.ofBaseSet h).image j :=
    hP.trans ((A.ofBaseSet h).overlap_subset_image i j)
  filter_upwards [ht, ae_restrict_of_ae_restrict_of_subset hsub hg] with y hy hz
  exact hy.trans (congrArg (fun v ↦ (finBasis ℝ F₂).repr v m) hz.symm)

omit [T2Space M] in
private theorem isCompactOperator_pieceHomMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (i j : Fin A.n) {P Q : Opens E} (hQc : IsCompact (closure (Q : Set E)))
    (hQ : closure (Q : Set E) ⊆ A.image i) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ (A.ofBaseSet h).transferDomain i j)
    (hPQ : MapsTo (((A.ofBaseSet h).chart j).symm ≫ₕ (A.ofBaseSet h).chart i) P Q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (m : Fin (finrank ℝ F₂)) :
    IsCompactOperator (pieceHomMulL A h μ hp hqp i j hQc hQ hPc hPD hPQ m α) := by
  have hlocal : IsCompactOperator (localHomComponentsL A h μ hp hqp i hQc hQ α) := by
    apply IsCompactOperator.pi
    intro l
    convert (isCompactOperator_localHomMulL A h μ hp hqp i hQc hQ α).clm_comp
      (((finBasis ℝ F₂).coord l).toContinuousLinearMap.compLpL q (μ.restrict Q)) using 1
    funext ξ
    simp only [localHomComponentsL, ContinuousLinearMap.piBilin_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, Function.comp_apply]
  convert hlocal.clm_comp ((ContinuousLinearMap.proj m).comp
    ((A.ofBaseSet h).transferL μ q 0 i j hPc hPD hPQ)) using 1
  funext ξ
  simp only [pieceHomMulL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    Function.comp_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [∀ x, Module ℝ (V₁ x)] [∀ x, AddCommGroup (V₁ x)]
  [VectorBundle ℝ F₁ V₁] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, Module ℝ (V₂ x)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
private theorem exists_hom_transfer_cover :
    let B := A.ofBaseSet h
    ∃ (P : Fin A.n → Fin A.n → Opens E) (Q : Fin A.n → Opens E),
      (∀ i j, (P i j : Set E) ⊆ B.overlap i j) ∧
      (∀ i j, IsCompact (closure (P i j : Set E))) ∧
      (∀ i j, closure (P i j : Set E) ⊆ B.transferDomain i j) ∧
      (∀ i, IsCompact (closure (Q i : Set E))) ∧
      (∀ i, closure (Q i : Set E) ⊆ A.image i) ∧
      (∀ i j, MapsTo ((B.chart j).symm ≫ₕ B.chart i) (P i j) (Q i)) ∧
      (∀ j, B.image j ≤ ⨆ i, P i j) ∧ (∀ i j, P i j ≤ B.image j) := by
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := (A.ofBaseSet h).exists_transfer_cover
  refine ⟨P, Q, hP, hPc, hPD, hQc, ?_, hPQ, hcov, ?_⟩
  · intro i
    simpa only [FiniteBundleAtlas.image_ofBaseSet] using hQ i
  · exact fun i j ↦ SetLike.coe_subset_coe.1
      ((hP i j).trans ((A.ofBaseSet h).overlap_subset_image i j))

private theorem exists_homMulComponents (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) :
    ∃ Φ : ∀ (j : Fin A.n) (_ : Fin (finrank ℝ F₂)),
      SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ] SobolevSection A μ q 1 →L[ℝ]
        Wkp μ ((A.ofBaseSet h).image j) q 0,
      ∀ α ξ j m, (Wkp.value 0 (Φ j m α ξ) : E → ℝ)
        =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] fun y ↦ (finBasis ℝ F₂).repr
          ((A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
            (A.sectionChartData.chartValueL μ q 1 j ξ y)) m := by
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQA, hPQ, hcov, hPj⟩ := exists_hom_transfer_cover A h
  let f (j : Fin A.n) (m : Fin (finrank ℝ F₂)) (i : Fin A.n) :=
    pieceHomMulL A h μ hp hqp i j (hQc i) (hQA i) (hPc i j) (hPD i j) (hPQ i j) m
  have hf (j : Fin A.n) (m : Fin (finrank ℝ F₂)) (i : Fin A.n)
      (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1) :
      (Wkp.value 0 (f j m i α ξ) : E → ℝ) =ᵐ[μ.restrict (P i j)] fun y ↦
        (finBasis ℝ F₂).repr ((A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
          (A.sectionChartData.chartValueL μ q 1 j ξ y)) m := by
    exact pieceHomMulL_ae A h μ hp hqp i j (hQc i) (hQA i) (hP i j)
      (hPc i j) (hPD i j) (hPQ i j) α ξ m
  choose Φ hΦ using fun j m ↦ Wkp.exists_continuousBilinearMap_value_ae_eq
    (fun i ↦ hPj i j) (hcov j) (f j m) _ (hf j m)
  exact ⟨Φ, fun α ξ j m ↦ hΦ j m α ξ⟩

/-- **Bounded multiplication by rough hom sections.** On a positive-dimensional base with
`dim E < p < ∞` and `1 ≤ q ≤ p`, there is a bounded real bilinear action of order-zero `Lᵖ` hom
sections on `W^{1,q}` sections, valued in the native `W^{0,q}` space of the target bundle.
Its chart readings are pointwise application of coefficient readings to input readings. -/
theorem exists_homMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) :
    ∃ T : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ]
      SobolevSection A μ q 1 →L[ℝ] SobolevSection (A.ofBaseSet h) μ q 0,
      ∀ α ξ j, (A.ofBaseSet h).sectionChartData.chartValueL μ q 0 j (T α ξ)
        =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] fun y ↦
          (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
            (A.sectionChartData.chartValueL μ q 1 j ξ y) := by
  obtain ⟨Φ, hΦ⟩ := exists_homMulComponents A h μ hp hqp
  let B := A.ofBaseSet h
  let D := ContinuousLinearMap.piBilin fun j ↦ ContinuousLinearMap.piBilin (Φ j)
  have hD (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
      (j : Fin A.n) : B.sectionChartData.chartValueL μ q 0 j (D α ξ)
        =ᵐ[μ.restrict (B.image j)] fun y ↦
          (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
            (A.sectionChartData.chartValueL μ q 1 j ξ y) := by
    filter_upwards [B.sectionChartData.chartValueL_apply_ae μ q 0 j (D α ξ),
      ae_all_iff.2 (hΦ α ξ j)] with y hy hm
    simp only [D, ContinuousLinearMap.piBilin_apply] at hy
    refine hy.trans ?_
    exact (Finset.sum_congr rfl fun m _ ↦
      congrArg (fun t : ℝ ↦ t • finBasis ℝ F₂ m) (hm m)).trans
        ((finBasis ℝ F₂).sum_repr _)
  have hmem (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1) :
      D α ξ ∈ B.sectionChartData.sobolevSections μ q 0 := by
    obtain ⟨φ, hφ⟩ := exists_hom_section_ae_eq_coord A h μ α
    obtain ⟨s, hs⟩ := exists_ae_eq_coord ξ
    have hcoord (j : Fin A.n) : B.sectionChartData.chartValueL μ q 0 j (D α ξ)
        =ᵐ[μ.restrict (B.image j)] B.sectionChartData.coord j (fun x ↦ φ x (s x)) := by
      have hg := chartHomProduct_ae_coord A h μ α ξ φ s j (hφ j) (hs j)
      exact (hD α ξ j).trans (hg.trans (B.sectionChartData_coord_ae_eq μ j _).symm)
    -- The membership criterion uses `Fin B.sectionChartData.n` and `B.sectionChartData.image`;
    -- these are `Fin A.n` and `B.image` by definition, so this fact needs no index cast.
    exact (B.sectionChartData.mem_sobolevSections_iff μ q 0).2 ⟨fun x ↦ φ x (s x), hcoord⟩
  refine ⟨D.codRestrictBilin (B.sectionChartData.sobolevSections μ q 0) hmem, fun α ξ j ↦ ?_⟩
  have hco := ContinuousLinearMap.coe_codRestrictBilin_apply D
    (B.sectionChartData.sobolevSections μ q 0) hmem α ξ
  have hL := congrArg (fun z ↦ (B.sectionChartData.chartValueL μ q 0 j z : E → F₂)) hco
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun y ↦ congrFun hL y) (hD α ξ j)

/-- The bounded real bilinear multiplication of rough hom sections and first-order Sobolev
sections, constructed on the native finite-atlas carriers. -/
def homMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) :
    SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ]
      SobolevSection A μ q 1 →L[ℝ] SobolevSection (A.ofBaseSet h) μ q 0 :=
  (exists_homMulL A h μ hp hqp).choose

/-- The chart readings of hom multiplication are pointwise application over `ℝ`. -/
theorem chartValueL_homMulL_ae (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (j : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ q 0 j (homMulL A h μ hp hqp α ξ)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] fun y ↦
        (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
          (A.sectionChartData.chartValueL μ q 1 j ξ y) :=
  (exists_homMulL A h μ hp hqp).choose_spec α ξ j

/-- Applying actual section representatives agrees with the native hom multiplication, almost
everywhere in each chart. Both sections may be rough. -/
theorem chartValueL_homMulL_ae_coord (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x) (j : Fin A.n)
    (hα : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α
      =ᵐ[μ.restrict (A.image j)] (A.hom (𝕜 := ℝ) h).coord j φ)
    (hξ : A.sectionChartData.chartValueL μ q 1 j ξ
      =ᵐ[μ.restrict (A.image j)] A.coord j s) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ q 0 j (homMulL A h μ hp hqp α ξ)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] (A.ofBaseSet h).coord j
        (fun x ↦ φ x (s x)) := by
  exact (chartValueL_homMulL_ae A h μ hp hqp α ξ j).trans
    (chartHomProduct_ae_coord A h μ α ξ φ s j hα hξ)

/-- The chartwise almost-everywhere product formula uniquely determines the native bilinear
multiplication operator. -/
theorem homMulL_unique (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {T : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0 →L[ℝ]
      SobolevSection A μ q 1 →L[ℝ] SobolevSection (A.ofBaseSet h) μ q 0}
    (hT : ∀ α ξ j, (A.ofBaseSet h).sectionChartData.chartValueL μ q 0 j (T α ξ)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] fun y ↦
        (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
          (A.sectionChartData.chartValueL μ q 1 j ξ y)) : T = homMulL A h μ hp hqp := by
  apply ContinuousLinearMap.ext
  intro α
  apply ContinuousLinearMap.ext
  intro ξ
  exact SectionChartData.eq_of_chartValueL_ae_eq fun j ↦
    (hT α ξ j).trans (chartValueL_homMulL_ae A h μ hp hqp α ξ j).symm

/-- Each scalar component of hom multiplication is the corresponding real coordinate of the
pointwise application of the chart readings. -/
theorem value_homMulL_component_ae (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection A μ q 1)
    (j : Fin A.n) (m : Fin (finrank ℝ F₂)) :
    (Wkp.value 0 ((homMulL A h μ hp hqp α ξ :
      (A.ofBaseSet h).sectionChartData.SobolevData μ q 0) j m) : E → ℝ)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image j)] fun y ↦ (finBasis ℝ F₂).repr
        ((A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL μ p 0 j α y
          (A.sectionChartData.chartValueL μ q 1 j ξ y)) m := by
  filter_upwards [(A.ofBaseSet h).sectionChartData.chartValueL_apply_ae μ q 0 j
      (homMulL A h μ hp hqp α ξ), chartValueL_homMulL_ae A h μ hp hqp α ξ j]
    with y hy hz
  have hv := congrArg (fun v ↦ (finBasis ℝ F₂).repr v m) (hy.symm.trans hz)
  simpa only [(finBasis ℝ F₂).repr_sum_self] using hv

/-- There is one nonnegative constant `C`, independent of the coefficient `α` and section `ξ`,
such that `‖homMulL A h μ hp hqp α ξ‖ ≤ C * ‖α‖ * ‖ξ‖` for every pair of native sections. -/
theorem exists_norm_homMulL_apply_le (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0)
      (ξ : SobolevSection A μ q 1), ‖homMulL A h μ hp hqp α ξ‖ ≤ C * ‖α‖ * ‖ξ‖ := by
  -- The operator norm uses the inherited component norms on all three native section spaces.
  let _ : NormedAddCommGroup (SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection A μ q 1) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection A μ q 1) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection (A.ofBaseSet h) μ q 0) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection (A.ofBaseSet h) μ q 0) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection A μ q 1 →L[ℝ]
    SobolevSection (A.ofBaseSet h) μ q 0) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection A μ q 1 →L[ℝ]
    SobolevSection (A.ofBaseSet h) μ q 0) := inferInstance
  exact ⟨‖homMulL A h μ hp hqp‖, norm_nonneg _, (homMulL A h μ hp hqp).le_opNorm₂⟩

/-- **Compact multiplication by a rough real hom section.** For every fixed order-zero
coefficient of exponent `p > dim E`, its action `W^{1,q}(V₁) → W^{0,q}(V₂)` is compact for every
finite `1 ≤ q ≤ p`. Compactness is asserted in the section variable with the coefficient fixed. -/
theorem isCompactOperator_homMulL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) h) μ p 0) :
    IsCompactOperator (homMulL A h μ hp hqp α) := by
  let B := A.ofBaseSet h
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQA, hPQ, hcov, hPj⟩ := exists_hom_transfer_cover A h
  refine SectionChartData.isCompactOperator_of_forall_apply (B.aeTransition_sectionChartData μ)
    fun j m ↦ ?_
  refine Wkp.isCompactOperator_of_restrictL (fun i ↦ hPj i j) (hcov j) fun i ↦ ?_
  have heq : (fun ξ : SobolevSection A μ q 1 ↦ Wkp.restrictL (hPj i j) 0
      ((homMulL A h μ hp hqp α ξ : B.sectionChartData.SobolevData μ q 0) j m)) =
      pieceHomMulL A h μ hp hqp i j (hQc i) (hQA i) (hPc i j) (hPD i j) (hPQ i j) m α := by
    funext ξ
    apply Wkp.ext 0
    apply Lp.ext
    exact Filter.EventuallyEq.trans (Wkp.value_restrictL_ae (hPj i j) 0 _)
      (Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hPj i j))
          (value_homMulL_component_ae A h μ hp hqp α ξ j m))
        (pieceHomMulL_ae A h μ hp hqp i j (hQc i) (hQA i) (hP i j)
          (hPc i j) (hPD i j) (hPQ i j) α ξ m).symm)
  rw [heq]
  exact isCompactOperator_pieceHomMulL A h μ hp hqp i j (hQc i) (hQA i)
    (hPc i j) (hPD i j) (hPQ i j) α m

end TauCeti.SobolevSection
