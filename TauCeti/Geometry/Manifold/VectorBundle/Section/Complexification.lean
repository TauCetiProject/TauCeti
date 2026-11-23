/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Section.ScalarTopology

/-!
# The topology of complexified bundle sections

Equip native `C^n` real sections with `ContMDiffSection.frameTopology` for any chosen family of
atlas frames and open domains. Give complexified sections the same topology using the existing
complexifications of those frames on the same domains. The real and imaginary projections and the
real and imaginary inclusions are continuous linear maps. The existing algebraic real/imaginary
splitting becomes a continuous linear equivalence, with the original section carriers.

No frame-cover, finite-rank, compactness, local compactness, completeness, or nonempty assumption
is needed. Every regularity order, including zero, smooth, and analytic, is allowed. For covering
frame domains, `Section.FrameCover` supplies topology independence under its own hypotheses.
This is a statement about native section topologies; test-section LF topologies and distribution
complexification require their own comparisons.

## Main definitions

* `ContMDiffSection.realPartCLM`, `imaginaryPartCLM`, `oneTmulCLM`, and `ITmulCLM`: the existing
  section linear maps with continuity for matched frame topologies.
* `ContMDiffSection.complexificationEquivProdCLE`: complexified sections as a real topological
  product of two original section spaces.
* `ContMDiffSection.conjCLE`: the existing conjugation as a continuous conjugate-linear equivalence.
* `ContMDiffSection.realPointsConjEquivCLE`: original sections as the existing native real-point
  subspace, with its induced topology.
-/

public section

noncomputable section
open Bundle TauCeti Set TopologicalSpace
open scoped ContDiff Manifold TensorProduct TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The existing fibrewise real-part section map is continuous in matched frame topologies. -/
def realPartCLM :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ →L[ℝ] Cₛ^n⟮I; F, V⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  refine ⟨realPartLinearMap I F n V, ?_⟩
  rw [LinearMap.toFun_eq_coe]
  apply continuous_frameTopology_of_frameCoordinates_eq_clm_apply
    (fun i ↦ (e i).complexification) U (Trivialization.subset_baseSet_complexification e hU)
    e hU (fun _ ↦ Complexification.reCLM F)
  intro i σ x
  simp only [Trivialization.frameCoordinates_apply, realPartLinearMap_apply,
    Complexification.reCLM_apply, Trivialization.complexification_apply_re,
    (e i).coe_linearMapAt_of_mem (hU i x.property)]

/-- Real-part continuity leaves the existing section map unchanged. -/
@[simp]
theorem realPartCLM_apply (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    ContMDiffSection.realPartCLM e U hU σ = realPartLinearMap I F n V σ := by
  rfl

/-- The existing fibrewise imaginary-part section map is continuous in matched frame topologies. -/
def imaginaryPartCLM :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ →L[ℝ] Cₛ^n⟮I; F, V⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  refine ⟨imaginaryPartLinearMap I F n V, ?_⟩
  rw [LinearMap.toFun_eq_coe]
  apply continuous_frameTopology_of_frameCoordinates_eq_clm_apply
    (fun i ↦ (e i).complexification) U (Trivialization.subset_baseSet_complexification e hU)
    e hU (fun _ ↦ Complexification.imCLM F)
  intro i σ x
  simp only [Trivialization.frameCoordinates_apply, imaginaryPartLinearMap_apply,
    Complexification.imCLM_apply, Trivialization.complexification_apply_im,
    (e i).coe_linearMapAt_of_mem (hU i x.property)]

/-- Imaginary-part continuity leaves the existing section map unchanged. -/
@[simp]
theorem imaginaryPartCLM_apply (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    ContMDiffSection.imaginaryPartCLM e U hU σ = imaginaryPartLinearMap I F n V σ := by
  rfl

/-- Real inclusion is continuous for the original and complexified frame topologies. -/
def oneTmulCLM :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; F, V⟯ →L[ℝ] Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  refine ⟨oneTmulLinearMap I F n V, ?_⟩
  rw [LinearMap.toFun_eq_coe]
  apply continuous_frameTopology_of_frameCoordinates_eq_clm_apply e U hU
    (fun i ↦ (e i).complexification) (Trivialization.subset_baseSet_complexification e hU)
    (fun _ ↦ (Complexification.ofRealLI F).toContinuousLinearMap)
  intro i σ x
  ext <;> simp [Trivialization.complexification_apply_re,
    Trivialization.complexification_apply_im, (e i).coe_linearMapAt_of_mem (hU i x.property),
    ((e i).linear ℝ (hU i x.property)).map_zero]

/-- The continuous real inclusion is the existing real section inclusion. -/
@[simp]
theorem oneTmulCLM_apply (σ : Cₛ^n⟮I; F, V⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    ContMDiffSection.oneTmulCLM e U hU σ = oneTmulLinearMap I F n V σ := by
  rfl

/-- Imaginary inclusion is continuous, using native continuous complex scalar multiplication. -/
def ITmulCLM :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; F, V⟯ →L[ℝ] Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  letI := continuousSMul_frameTopology_ofNormedAlgebra (𝕜' := ℂ) (I := I) (n := n)
    (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
  refine ⟨ITmulLinearMap I F n V, ?_⟩
  rw [LinearMap.toFun_eq_coe]
  exact ((ContMDiffSection.oneTmulCLM (I := I) (n := n) e U hU).continuous.const_smul
    Complex.I).congr fun s ↦ by
      simpa only [Pi.smul_apply, oneTmulCLM_apply] using I_smul_oneTmulLinearMap s

/-- The continuous imaginary inclusion is the existing imaginary section inclusion. -/
@[simp]
theorem ITmulCLM_apply (σ : Cₛ^n⟮I; F, V⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    ContMDiffSection.ITmulCLM e U hU σ = ITmulLinearMap I F n V σ := by
  rfl

/-- The existing real/imaginary section splitting, with both directions continuous for matched
frame topologies. No covering or local-compactness assumption is used. -/
def complexificationEquivProdCLE :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ ≃L[ℝ]
      Cₛ^n⟮I; F, V⟯ × Cₛ^n⟮I; F, V⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  letI := isTopologicalAddGroup_frameTopology (I := I) (n := n)
    (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
  refine { complexificationEquivProd I F n V with
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    exact ((ContMDiffSection.realPartCLM e U hU).continuous.prodMk
      (ContMDiffSection.imaginaryPartCLM e U hU).continuous).congr fun σ ↦ by
        simp only [realPartCLM_apply, imaginaryPartCLM_apply, complexificationEquivProd_apply]
  · rw [LinearEquiv.invFun_eq_symm]
    exact (((ContMDiffSection.oneTmulCLM e U hU).continuous.comp continuous_fst).add
      ((ContMDiffSection.ITmulCLM e U hU).continuous.comp continuous_snd)).congr fun p ↦ by
        simp only [Function.comp_apply, Pi.add_apply, oneTmulCLM_apply, ITmulCLM_apply,
          complexificationEquivProd_symm_apply]

/-- The topological splitting has the same underlying real/imaginary pair as the algebraic one. -/
@[simp]
theorem complexificationEquivProdCLE_apply
    (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    complexificationEquivProdCLE e U hU σ = complexificationEquivProd I F n V σ := by
  rfl

/-- The inverse topological splitting reconstructs the native included real and imaginary parts. -/
@[simp]
theorem complexificationEquivProdCLE_symm_apply (p : Cₛ^n⟮I; F, V⟯ × Cₛ^n⟮I; F, V⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    (complexificationEquivProdCLE e U hU).symm p =
      oneTmulLinearMap I F n V p.1 + ITmulLinearMap I F n V p.2 := by
  exact complexificationEquivProd_symm_apply p

/-- Native section conjugation is a continuous conjugate-linear equivalence. In real/imaginary
coordinates it acts by the continuous map `(s, t) ↦ (s, -t)`. -/
def conjCLE :
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ ≃L⋆[ℂ]
      Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯ := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  letI := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let L := complexificationEquivProdCLE (I := I) (n := n) e U hU
  have hc : Continuous (fun σ ↦ L.symm ((L σ).1, -(L σ).2)) :=
    L.symm.continuous.comp (L.continuous.fst.prodMk L.continuous.snd.neg)
  have hconj : Continuous (conjEquiv I F n V) := hc.congr fun σ ↦ by
    apply L.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [L, complexificationEquivProdCLE_apply] using
      (complexificationEquivProd_conjEquiv σ).symm
  exact { conjEquiv I F n V with
    continuous_toFun := by simpa only [LinearEquiv.toFun_eq_coe] using hconj
    continuous_invFun := by
      simpa only [LinearEquiv.invFun_eq_symm, conjEquiv_symm] using hconj }

/-- The continuous conjugation is the existing native section conjugation. -/
@[simp]
theorem conjCLE_apply (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    conjCLE e U hU σ = conjEquiv I F n V σ := by
  rfl

/-- Inverse continuous conjugation is the same native conjugation. -/
@[simp]
theorem conjCLE_symm_apply (σ : Cₛ^n⟮I; Complexification F, fun x ↦ ℂ ⊗[ℝ] V x⟯) :
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    (conjCLE e U hU).symm σ = conjEquiv I F n V σ := by
  exact congrArg (fun g ↦ g σ) (conjEquiv_symm (IB := I) (F := F) (n := n) (E := V))

/-- Real sections are continuously linearly equivalent to the existing native real-point
submodule of conjugation, with its subspace topology from complexified frame coordinates. -/
def realPointsConjEquivCLE :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    Cₛ^n⟮I; F, V⟯ ≃L[ℝ] realPoints (conjEquiv I F n V).toLinearMap := by
  letI := frameTopology (I := I) (n := n) e U hU
  letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
    (Trivialization.subset_baseSet_complexification e hU)
  refine { realPointsConjEquiv I F n V with
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · rw [LinearEquiv.toFun_eq_coe]
    apply continuous_induced_rng.mpr
    exact (ContMDiffSection.oneTmulCLM e U hU).continuous.congr fun s ↦ by
      simp only [Function.comp_apply, oneTmulCLM_apply, coe_realPointsConjEquiv_apply]
  · rw [LinearEquiv.invFun_eq_symm]
    exact ((ContMDiffSection.realPartCLM e U hU).continuous.comp
      continuous_subtypeVal).congr fun σ ↦ by
        simp only [Function.comp_apply, realPartCLM_apply, realPointsConjEquiv_symm_apply]

/-- The continuous fixed-point comparison has the existing algebraic fixed-point value. -/
@[simp]
theorem realPointsConjEquivCLE_apply (s : Cₛ^n⟮I; F, V⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    realPointsConjEquivCLE e U hU s = realPointsConjEquiv I F n V s := by
  rfl

/-- The continuous inverse fixed-point comparison is the native real-part inverse. -/
@[simp]
theorem realPointsConjEquivCLE_symm_apply (σ : realPoints (conjEquiv I F n V).toLinearMap) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) (fun i ↦ (e i).complexification) U
      (Trivialization.subset_baseSet_complexification e hU)
    (realPointsConjEquivCLE e U hU).symm σ = realPartLinearMap I F n V σ := by
  exact realPointsConjEquiv_symm_apply σ

end ContMDiffSection
