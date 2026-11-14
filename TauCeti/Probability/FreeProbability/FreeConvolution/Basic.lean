/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Probability.FreeProbability.Law.Cumulant
public import TauCeti.Probability.FreeProbability.Variables
import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval
import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.FreeProbability.Distribution.Free
import TauCeti.Probability.FreeProbability.FreeProduct.Reduced
import TauCeti.Probability.FreeProbability.WeakClosure

/-!
# Free additive convolution of compactly supported probability measures

For compactly supported Borel probability measures `μ` and `ν` on `ℝ`, Voiculescu's reduced
C⋆-free product realizes freely independent selfadjoint elements `a` and `b` with laws `μ` and
`ν` in a unital C⋆-algebra equipped with a state, and `μ ⊞ ν` (`MeasureTheory.Measure.freeConv`)
is defined as the spectral law of `a + b`. Outside compactly supported probability measures,
`μ ⊞ ν` is set to `0`, making commutativity, associativity, Dirac addition, translation,
reflection, and interval support bounds hold unconditionally on all Borel measures on `ℝ`.

## Main definitions

* `MeasureTheory.Measure.freeConv` (`μ ⊞ ν`, scoped in `MeasureTheory`): the free additive
  convolution of Borel measures on `ℝ`.

## Main results

* `TauCeti.exists_cstar_isFreelyIndependentElements_law_eq` and
  `TauCeti.exists_vonNeumannAlgebra_isFreelyIndependent_law_eq`: C⋆-algebra and concrete von
  Neumann algebra realizations of arbitrary families of compactly supported Borel probability
  measures on `ℝ` by freely independent selfadjoint elements.
* `PositiveLinearMap.law_add_eq_freeConv`,
  `PositiveLinearMap.law_add_eq_freeConv_of_isFreelyIndependentElements`, and
  `PositiveLinearMap.law_innerPositiveLinearMap_add_eq_freeConv_of_mem_weakOperatorClosure`:
  independence of realization in any unital C⋆-algebra or concrete von Neumann algebra, and
  transport across weak-operator closures under normalized vector states.
* `MeasureTheory.Measure.rSeries_freeConv` and `MeasureTheory.Measure.freeCumulant_freeConv`:
  additivity of the formal R-series and positive-order free cumulants under `⊞`.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`,
  `MeasureTheory.Measure.dirac_zero_freeConv`, `MeasureTheory.Measure.freeConv_dirac_zero`, and
  `MeasureTheory.Measure.dirac_freeConv_dirac`: algebraic laws and point-mass identities.
* `MeasureTheory.Measure.freeConv_map_add`, `MeasureTheory.Measure.freeConv_neg`,
  `MeasureTheory.Measure.freeConv_map_mul_left`, and `MeasureTheory.Measure.freeConv_map_affine`:
  translation, reflection, dilation, and affine pushforward laws.
* `MeasureTheory.Measure.support_freeConv_subset_Icc`: if `μ` is supported in `[a₁, b₁]` and `ν`
  in `[a₂, b₂]`, then `μ ⊞ ν` is supported in `[a₁ + a₂, b₁ + b₂]`.
* `TauCeti.Probability.semicircleReal_freeConv_semicircleReal`: additivity of real semicircle
  laws `semicircleReal a v ⊞ semicircleReal b w = semicircleReal (a + b) (v + w)`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§3.1–3.3.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory PowerSeries
open scoped ENNReal NNReal InnerProductSpace ComplexOrder

universe u

namespace TauCeti

/-! ### C⋆-algebra and von Neumann algebra realizations of free selfadjoint families -/

private noncomputable def lawFactorPositiveLinearMap (μ : Measure ℝ) [CompactSpace μ.support]
    [IsProbabilityMeasure μ] : C(μ.support, ℂ) →ₚ[ℂ] ℂ :=
  ContinuousMap.integralPositiveLinearMap (μ.comap ((↑) : μ.support → ℝ))

private noncomputable def lawFactorFunctional (μ : Measure ℝ) [CompactSpace μ.support]
    [IsProbabilityMeasure μ] : StarPositiveFunctional C(μ.support, ℂ) :=
  StarPositiveFunctional.ofPositiveLinearMap (lawFactorPositiveLinearMap μ)

private def lawFactorGenerator (μ : Measure ℝ) : C(μ.support, ℂ) :=
  ((ContinuousMap.restrict μ.support (ContinuousMap.id ℝ)).realToRCLike ℂ)

private lemma isSelfAdjoint_lawFactorGenerator (μ : Measure ℝ) :
    IsSelfAdjoint (lawFactorGenerator μ) :=
  ContinuousMap.isSelfAdjoint_realToRCLike ℂ

private lemma law_lawFactorGenerator (μ : Measure ℝ) [CompactSpace μ.support]
    [IsProbabilityMeasure μ] :
    (lawFactorPositiveLinearMap μ).law (lawFactorGenerator μ) = μ :=
  PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id Measure.measure_compl_support

private lemma lawFactorFunctional_one (μ : Measure ℝ) [CompactSpace μ.support]
    [IsProbabilityMeasure μ] : lawFactorFunctional μ 1 = 1 := by
  rw [lawFactorFunctional, StarPositiveFunctional.ofPositiveLinearMap_apply,
    ← PositiveLinearMap.ofReal_law_real_univ _ (isSelfAdjoint_lawFactorGenerator μ),
    law_lawFactorGenerator]
  simp

private lemma norm_lawFactorGenerator_le (μ : Measure ℝ) [CompactSpace μ.support] {r : ℝ}
    (hr : 0 ≤ r) (hsupp : μ.support ⊆ Set.Icc (-r) r) :
    ‖lawFactorGenerator μ‖ ≤ r := by
  refine (ContinuousMap.norm_le _ hr).mpr fun x ↦ ?_
  simpa [lawFactorGenerator, Real.norm_eq_abs] using abs_le.mpr (hsupp x.2)

-- Abstracting the GNS Hilbert carrier prevents typeclass synthesis on `StarSubalgebra` and
-- `VonNeumannAlgebra` from unfolding the algebraic GNS quotient of the free product.
private theorem reducedRealization {ι : Type u} {A : ι → Type}
    [∀ i, CStarAlgebra (A i)] (ψ : ∀ i, StarPositiveFunctional (A i)) (hψ : ∀ i, ψ i 1 = 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (R : StarSubalgebra ℂ (H →L[ℂ] H)) (_ : IsClosed (R : Set (H →L[ℂ] H)))
      (ξ : H) (f : ∀ i, A i →⋆ₐ[ℂ] R) (ω : R →ₚ[ℂ] ℂ),
      ‖ξ‖ = 1 ∧ (∀ x : R, ω x = ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ) ∧ ω 1 = 1 ∧
        (∀ i a, ω (f i a) = ψ i a) ∧
        IsFreelyIndependent ω.toLinearMap (fun i ↦ (f i).toAlgHom.range) := by
  classical
  exact ⟨ReducedFreeProduct.HilbertSpace ψ hψ, inferInstance, inferInstance, inferInstance,
    ReducedFreeProduct.algebra ψ hψ, ReducedFreeProduct.isClosed_algebra ψ hψ,
    ReducedFreeProduct.vacuum ψ hψ, ReducedFreeProduct.factor ψ hψ,
    ReducedFreeProduct.state ψ hψ, ReducedFreeProduct.norm_vacuum ψ hψ,
    ReducedFreeProduct.state_apply ψ hψ, ReducedFreeProduct.state_one ψ hψ,
    ReducedFreeProduct.state_factor ψ hψ, ReducedFreeProduct.isFreelyIndependent_factor ψ hψ⟩

private theorem exists_cstar_realization_with_norm {ι : Type u} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : ι → A),
      φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ (∀ i, φ.law (a i) = μ i) ∧
        ∀ i (r : ℝ), 0 ≤ r → (μ i).support ⊆ Set.Icc (-r) r → ‖a i‖ ≤ r := by
  let _ : ∀ i, CompactSpace (μ i).support := fun i ↦ isCompact_iff_compactSpace.mp (hμ i)
  let ψ : ∀ i, StarPositiveFunctional C((μ i).support, ℂ) := fun i ↦ lawFactorFunctional (μ i)
  have hψ : ∀ i, ψ i 1 = 1 := fun i ↦ lawFactorFunctional_one (μ i)
  obtain ⟨H, _, _, _, R, _, _, f, ω, -, -, hω₁, hω_f, hfree⟩ := reducedRealization ψ hψ
  let a : ι → R := fun i ↦ f i (lawFactorGenerator (μ i))
  refine ⟨R, inferInstance, inferInstance, inferInstance, ω, a, hω₁,
    fun i ↦ (isSelfAdjoint_lawFactorGenerator (μ i)).map (f i), ?_, fun i ↦ ?_,
    fun i r hr hsupp ↦ ?_⟩
  · rw [isFreelyIndependentElements_iff]
    exact hfree.mono fun i ↦
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨lawFactorGenerator (μ i), rfl⟩)
  · rw [PositiveLinearMap.law_apply_eq_law (lawFactorPositiveLinearMap (μ i)) ω (f i)
      (fun g ↦ (hω_f i g).trans (StarPositiveFunctional.ofPositiveLinearMap_apply _ g))
      (isSelfAdjoint_lawFactorGenerator (μ i))]
    exact law_lawFactorGenerator (μ i)
  · exact (NonUnitalStarAlgHom.norm_apply_le (f i).toNonUnitalStarAlgHom _).trans
      (norm_lawFactorGenerator_le (μ i) hr hsupp)

/-- Any family of compactly supported Borel probability measures on `ℝ` is realized by freely
independent selfadjoint elements in a unital C⋆-algebra equipped with a normalized positive
state. -/
theorem exists_cstar_isFreelyIndependentElements_law_eq {ι : Type u} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : ι → A),
      φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ ∀ i, φ.law (a i) = μ i := by
  obtain ⟨A, hA₁, hA₂, hA₃, φ, a, hφ₁, hsa, hfree, hlaw, -⟩ :=
    exists_cstar_realization_with_norm μ hμ
  exact ⟨A, hA₁, hA₂, hA₃, φ, a, hφ₁, hsa, hfree, hlaw⟩

/-- Any family of compactly supported Borel probability measures on `ℝ` is realized by freely
independent selfadjoint operators in a concrete von Neumann algebra `M` acting on a complex
Hilbert space `H` with respect to the normal vector state of a unit vector `ξ : H`. -/
theorem exists_vonNeumannAlgebra_isFreelyIndependent_law_eq {ι : Type u} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (M : VonNeumannAlgebra H) (ξ : H) (ω : M →ₚ[ℂ] ℂ) (a : ι → M),
      ‖ξ‖ = 1 ∧ (∀ x : M, ω x = ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ) ∧ ω 1 = 1 ∧
        (∀ i, IsSelfAdjoint (a i)) ∧ IsFreelyIndependentElements ω.toLinearMap a ∧
        ∀ i, ω.law (a i) = μ i := by
  let _ : ∀ i, CompactSpace (μ i).support := fun i ↦ isCompact_iff_compactSpace.mp (hμ i)
  let ψ : ∀ i, StarPositiveFunctional C((μ i).support, ℂ) := fun i ↦ lawFactorFunctional (μ i)
  have hψ : ∀ i, ψ i 1 = 1 := fun i ↦ lawFactorFunctional_one (μ i)
  obtain ⟨H, _, _, _, R, _, ξ, f, ωR, hξ, hωR_apply, hωR₁, hωR_f, hfreeR⟩ :=
    reducedRealization ψ hψ
  let M : VonNeumannAlgebra H := VonNeumannAlgebra.adjoin (R : Set (H →L[ℂ] H))
  let ιM : R →⋆ₐ[ℂ] M :=
    R.subtype.codRestrict M.toStarSubalgebra fun x ↦ VonNeumannAlgebra.subset_adjoin _ x.2
  let ω : M →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀
      ((ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap.comp
        M.toStarSubalgebra.subtype.toAlgHom.toLinearMap)
      fun x hx ↦ (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).map_nonneg hx
  let a : ι → M := fun i ↦ ιM (f i (lawFactorGenerator (μ i)))
  have hω_apply (x : M) : ω x = ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ :=
    ContinuousLinearMap.innerPositiveLinearMap_apply ξ (x : H →L[ℂ] H)
  have hω_ιM (x : R) : ω (ιM x) = ωR x := (hω_apply (ιM x)).trans (hωR_apply x).symm
  have hω₁ : ω 1 = 1 := by simpa only [map_one] using (hω_ιM 1).trans hωR₁
  refine ⟨H, inferInstance, inferInstance, inferInstance, M, ξ, ω, a, hξ, hω_apply, hω₁,
    fun i ↦ ((isSelfAdjoint_lawFactorGenerator (μ i)).map (f i)).map ιM, ?_, fun i ↦ ?_⟩
  · have hfree_elem : IsFreelyIndependentElements ωR.toLinearMap
        (fun i ↦ f i (lawFactorGenerator (μ i))) := by
      rw [isFreelyIndependentElements_iff]
      exact hfreeR.mono fun i ↦
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨lawFactorGenerator (μ i), rfl⟩)
    exact hfree_elem.map ιM.toAlgHom (LinearMap.ext hω_ιM)
  · rw [PositiveLinearMap.law_apply_eq_law ωR ω ιM hω_ιM
      ((isSelfAdjoint_lawFactorGenerator (μ i)).map (f i)),
      PositiveLinearMap.law_apply_eq_law (lawFactorPositiveLinearMap (μ i)) ωR (f i)
        (fun g ↦ (hωR_f i g).trans (StarPositiveFunctional.ofPositiveLinearMap_apply _ g))
        (isSelfAdjoint_lawFactorGenerator (μ i))]
    exact law_lawFactorGenerator (μ i)

end TauCeti

namespace MeasureTheory.Measure

/-! ### Definition and basic properties of free additive convolution -/

private structure FreeConvRealization (μ ν : Measure ℝ) : Type 1 where
  A : Type
  instCStar : CStarAlgebra A
  instPO : PartialOrder A
  instSOR : StarOrderedRing A
  φ : A →ₚ[ℂ] ℂ
  a : Bool → A
  hφ₁ : φ 1 = 1
  hsa : ∀ k, IsSelfAdjoint (a k)
  hfree : TauCeti.IsFreelyIndependentElements φ.toLinearMap a
  hlaw_true : φ.law (a true) = μ
  hlaw_false : φ.law (a false) = ν
  hnorm_true : ∀ r : ℝ, 0 ≤ r → μ.support ⊆ Set.Icc (-r) r → ‖a true‖ ≤ r
  hnorm_false : ∀ r : ℝ, 0 ≤ r → ν.support ⊆ Set.Icc (-r) r → ‖a false‖ ≤ r

attribute [instance] FreeConvRealization.instCStar FreeConvRealization.instPO
  FreeConvRealization.instSOR

private noncomputable def canonicalFreeConvRealization (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    FreeConvRealization μ ν := by
  have hex := @TauCeti.exists_cstar_realization_with_norm Bool (Bool.rec ν μ)
    (Bool.rec ‹_› ‹_›) (Bool.rec hν hμ)
  let A := Classical.choose hex
  let h1 := Classical.choose_spec hex
  let instCStar := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let instPO := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let instSOR := Classical.choose h3
  let h4 := Classical.choose_spec h3
  let φ := Classical.choose h4
  let h5 := Classical.choose_spec h4
  let a := Classical.choose h5
  let hspec := Classical.choose_spec h5
  exact
    { A := A
      instCStar := instCStar
      instPO := instPO
      instSOR := instSOR
      φ := φ
      a := a
      hφ₁ := hspec.1
      hsa := hspec.2.1
      hfree := hspec.2.2.1
      hlaw_true := hspec.2.2.2.1 true
      hlaw_false := hspec.2.2.2.1 false
      hnorm_true := hspec.2.2.2.2 true
      hnorm_false := hspec.2.2.2.2 false }

private noncomputable def freeConvAux (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) : Measure ℝ :=
  let R := canonicalFreeConvRealization μ ν hμ hν
  R.φ.law (R.a true + R.a false)

/-- **Free additive convolution** of Borel measures on `ℝ`. For compactly supported probability
measures `μ` and `ν`, `μ ⊞ ν` is the spectral law of `a + b` where `a` and `b` are freely
independent selfadjoint elements with laws `μ` and `ν` in the reduced C⋆-free product; otherwise
`μ ⊞ ν = 0`. -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  open scoped Classical in
  if h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support then
    @freeConvAux μ ν h.1 h.2.2.1 h.2.1 h.2.2.2
  else
    0

/-- Scoped notation `μ ⊞ ν` for the free additive convolution `MeasureTheory.Measure.freeConv`. -/
scoped[MeasureTheory] infixr:80 " ⊞ " => MeasureTheory.Measure.freeConv

open scoped MeasureTheory

private lemma freeConv_eq_freeConvAux {μ ν : Measure ℝ} [hμp : IsProbabilityMeasure μ]
    [hνp : IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ ⊞ ν = freeConvAux μ ν hμ hν := by
  simp [freeConv, hμp, hμ, hνp, hν]

private lemma freeConv_of_not {μ ν : Measure ℝ}
    (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support)) :
    μ ⊞ ν = 0 := by
  simp [freeConv, h]

/-- If `μ` is not a probability measure, `μ ⊞ ν = 0`. -/
theorem freeConv_of_not_isProbabilityMeasure_left {μ ν : Measure ℝ}
    (h : ¬IsProbabilityMeasure μ) : μ ⊞ ν = 0 :=
  freeConv_of_not fun h' ↦ h h'.1

/-- If `ν` is not a probability measure, `μ ⊞ ν = 0`. -/
theorem freeConv_of_not_isProbabilityMeasure_right {μ ν : Measure ℝ}
    (h : ¬IsProbabilityMeasure ν) : μ ⊞ ν = 0 :=
  freeConv_of_not fun h' ↦ h h'.2.2.1

/-- If `μ` does not have compact support, `μ ⊞ ν = 0`. -/
theorem freeConv_of_not_isCompact_support_left {μ ν : Measure ℝ}
    (h : ¬IsCompact μ.support) : μ ⊞ ν = 0 :=
  freeConv_of_not fun h' ↦ h h'.2.1

/-- If `ν` does not have compact support, `μ ⊞ ν = 0`. -/
theorem freeConv_of_not_isCompact_support_right {μ ν : Measure ℝ}
    (h : ¬IsCompact ν.support) : μ ⊞ ν = 0 :=
  freeConv_of_not fun h' ↦ h h'.2.2.2

@[simp]
theorem zero_freeConv (ν : Measure ℝ) : (0 : Measure ℝ) ⊞ ν = 0 :=
  freeConv_of_not_isProbabilityMeasure_left fun h ↦ one_ne_zero h.measure_univ.symm

@[simp]
theorem freeConv_zero (μ : Measure ℝ) : μ ⊞ (0 : Measure ℝ) = 0 :=
  freeConv_of_not_isProbabilityMeasure_right fun h ↦ one_ne_zero h.measure_univ.symm

/-- Free additive convolution always produces a finite Borel measure on `ℝ`. -/
instance isFiniteMeasure_freeConv (μ ν : Measure ℝ) : IsFiniteMeasure (μ ⊞ ν) := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμp, hμ, hνp, hν⟩ := h
    rw [freeConv_eq_freeConvAux hμ hν, freeConvAux]
    infer_instance
  · rw [freeConv_of_not h]
    infer_instance

/-- Free additive convolution always produces a measure with compact topological support. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ ⊞ ν).support := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμp, hμ, hνp, hν⟩ := h
    rw [freeConv_eq_freeConvAux hμ hν, freeConvAux]
    exact PositiveLinearMap.isCompact_support_law _ _
  · rw [freeConv_of_not h]
    simp

/-- Free additive convolution of compactly supported probability measures is a probability
measure. -/
theorem isProbabilityMeasure_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ ⊞ ν) := by
  rw [freeConv_eq_freeConvAux hμ hν, freeConvAux]
  let R := canonicalFreeConvRealization μ ν hμ hν
  exact R.φ.isProbabilityMeasure_law R.hφ₁ ((R.hsa true).add (R.hsa false))

/-- `μ ⊞ ν` is a probability measure if and only if both `μ` and `ν` are compactly supported
probability measures. -/
theorem isProbabilityMeasure_freeConv_iff {μ ν : Measure ℝ} :
    IsProbabilityMeasure (μ ⊞ ν) ↔
      IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
        IsProbabilityMeasure ν ∧ IsCompact ν.support := by
  constructor
  · intro hprob
    by_contra h
    rw [freeConv_of_not h] at hprob
    exact one_ne_zero hprob.measure_univ.symm
  · rintro ⟨hμp, hμ, hνp, hν⟩
    exact isProbabilityMeasure_freeConv hμ hν

end MeasureTheory.Measure

namespace PositiveLinearMap

open scoped MeasureTheory

/-! ### Realization independence and operator-algebraic transport -/

/-- **Realization independence of free additive convolution.** In any unital C⋆-algebra (including
any concrete von Neumann algebra), if `B` is a freely independent family of subalgebras for a
state `φ` (`φ 1 = 1`), then the law of `a + b` for selfadjoint `a ∈ B i` and `b ∈ B j` (`i ≠ j`)
is `φ.law a ⊞ φ.law b`. -/
theorem law_add_eq_freeConv {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {B : ι → Subalgebra ℂ A}
    (hfree : TauCeti.IsFreelyIndependent φ.toLinearMap B) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (haB : a ∈ B i) (hbB : b ∈ B j) :
    φ.law (a + b) = φ.law a ⊞ φ.law b := by
  let μ := φ.law a
  let ν := φ.law b
  have _ : IsProbabilityMeasure μ := φ.isProbabilityMeasure_law hφ ha
  have _ : IsProbabilityMeasure ν := φ.isProbabilityMeasure_law hφ hb
  have hμ : IsCompact μ.support := φ.isCompact_support_law a
  have hν : IsCompact ν.support := φ.isCompact_support_law b
  rw [Measure.freeConv_eq_freeConvAux hμ hν, Measure.freeConvAux]
  let R := Measure.canonicalFreeConvRealization μ ν hμ hν
  let c : Bool → A := Bool.rec b a
  have hc_free : TauCeti.IsFreelyIndependentElements φ.toLinearMap c := by
    rw [TauCeti.isFreelyIndependentElements_iff]
    have hinj : Function.Injective (Bool.rec j i : Bool → ι) := by
      rintro (_ | _) (_ | _) <;> simp [hij, hij.symm]
    refine (hfree.comp hinj).mono fun k ↦ Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    cases k <;> assumption
  have hmom (k : Bool) (n : ℕ) : φ (c k ^ n) = R.φ (R.a k ^ n) := by
    cases k
    · exact (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ R.φ hb (R.hsa false)).mp
        R.hlaw_false.symm n
    · exact (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ R.φ ha (R.hsa true)).mp
        R.hlaw_true.symm n
  have hjoint := hc_free.jointDistribution_eq_of_forall_pow R.hfree hφ R.hφ₁ hmom
  refine (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ R.φ (ha.add hb)
    ((R.hsa true).add (R.hsa false))).mpr fun n ↦ ?_
  simpa [TauCeti.jointDistribution_apply, c] using
    LinearMap.congr_fun hjoint ((FreeAlgebra.ι ℂ true + FreeAlgebra.ι ℂ false) ^ n)

/-- Element-level specialization of `PositiveLinearMap.law_add_eq_freeConv`: for distinct indices
`i ≠ j` in a freely independent family `a`, the law of `a i + a j` is `φ.law (a i) ⊞ φ.law (a j)`.
-/
theorem law_add_eq_freeConv_of_isFreelyIndependentElements {A ι : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {a : ι → A}
    (hfree : TauCeti.IsFreelyIndependentElements φ.toLinearMap a) {i j : ι} (hij : i ≠ j)
    (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j)) :
    φ.law (a i + a j) = φ.law (a i) ⊞ φ.law (a j) :=
  φ.law_add_eq_freeConv hφ (TauCeti.isFreelyIndependentElements_iff.mp hfree) hij hai haj
    (Algebra.self_mem_adjoin_singleton ℂ (a i)) (Algebra.self_mem_adjoin_singleton ℂ (a j))

/-- **Weak-operator-closure transport for free additive convolution.** If `B` is a family of
subalgebras of `H →L[ℂ] H` that is freely independent with respect to the vector state of a unit
vector `ξ`, then selfadjoint operators `S` and `T` belonging to the weak-operator closures of
`B i` and `B j` (`i ≠ j`) satisfy `ω_ξ.law (S + T) = ω_ξ.law S ⊞ ω_ξ.law T`. -/
theorem law_innerPositiveLinearMap_add_eq_freeConv_of_mem_weakOperatorClosure
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ξ : H} (hξ : ‖ξ‖ = 1) {B : ι → Subalgebra ℂ (H →L[ℂ] H)}
    (hfree : TauCeti.IsFreelyIndependent
      (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap B)
    {i j : ι} (hij : i ≠ j) {S T : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hSB : ContinuousLinearMapWOT.ofCLM S ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (B i : Set (H →L[ℂ] H))))
    (hTB : ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (B j : Set (H →L[ℂ] H)))) :
    (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).law (S + T) =
      (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).law S ⊞
        (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).law T := by
  let ω := ContinuousLinearMap.innerPositiveLinearMap ℂ ξ
  let e := ContinuousLinearMapWOT.algEquiv (𝕜₁ := ℂ) (E := H) ℂ
  have hω₁ : ω 1 = 1 := by simp [ω, hξ]
  have hfree_wot : TauCeti.IsFreelyIndependent (ω.toLinearMap.comp e.toLinearMap)
      (fun k ↦ ((B k).map e.symm.toAlgHom).topologicalClosure) :=
    (TauCeti.isFreelyIndependent_weakOperatorClosure_iff_of_vectorState hω₁ ξ
      fun X ↦ ContinuousLinearMap.innerPositiveLinearMap_apply ξ X).mpr hfree
  have hfree_cl : TauCeti.IsFreelyIndependent ω.toLinearMap
      (fun k ↦ (((B k).map e.symm.toAlgHom).topologicalClosure).map e.toAlgHom) :=
    hfree_wot.map e.toAlgHom (by ext X; simp [e])
  refine ω.law_add_eq_freeConv hω₁ hfree_cl hij hS hT ?_ ?_
  · exact ⟨ContinuousLinearMapWOT.ofCLM S, hSB, rfl⟩
  · exact ⟨ContinuousLinearMapWOT.ofCLM T, hTB, rfl⟩

end PositiveLinearMap

namespace MeasureTheory.Measure

open scoped MeasureTheory

/-! ### Additivity of the formal R-series and free cumulants -/

/-- **Additivity of the formal R-series under free additive convolution.** For compactly supported
Borel probability measures `μ` and `ν` on `ℝ`, `(μ ⊞ ν).rSeries = μ.rSeries + ν.rSeries`. -/
@[simp]
theorem rSeries_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    (μ ⊞ ν).rSeries = μ.rSeries + ν.rSeries := by
  rw [freeConv_eq_freeConvAux hμ hν, freeConvAux]
  let R := canonicalFreeConvRealization μ ν hμ hν
  have hmap := PositiveLinearMap.map_rSeries_law R.φ ((R.hsa true).add (R.hsa false))
  have hadd := R.hfree.rSeries_add R.hφ₁ (by decide : true ≠ false)
  change TauCeti.rSeries R.φ (R.a true + R.a false) =
    TauCeti.rSeries R.φ (R.a true) + TauCeti.rSeries R.φ (R.a false) at hadd
  rw [hadd,
    ← PositiveLinearMap.map_rSeries_law R.φ (R.hsa true),
    ← PositiveLinearMap.map_rSeries_law R.φ (R.hsa false),
    R.hlaw_true, R.hlaw_false] at hmap
  ext n
  exact Complex.ofReal_injective (by simpa using congrArg (coeff n) hmap)

/-- **Additivity of positive-order free cumulants.** For compactly supported Borel probability
measures `μ` and `ν` on `ℝ` and every `n ≠ 0`,
`(μ ⊞ ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n`. -/
theorem freeCumulant_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) {n : ℕ} (hn : n ≠ 0) :
    (μ ⊞ ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa using congrArg (coeff k) (rSeries_freeConv hμ hν)

/-! ### Commutativity, associativity, and point-mass laws -/

/-- Free additive convolution of Borel measures on `ℝ` is commutative. -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ ⊞ ν = ν ⊞ μ := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμp, hμ, hνp, hν⟩ := h
    have _ := isProbabilityMeasure_freeConv hμ hν
    have _ := isProbabilityMeasure_freeConv hν hμ
    rw [eq_iff_rSeries_eq (isCompact_support_freeConv μ ν) (isCompact_support_freeConv ν μ),
      rSeries_freeConv hμ hν, rSeries_freeConv hν hμ, add_comm]
  · have h' : ¬(IsProbabilityMeasure ν ∧ IsCompact ν.support ∧
        IsProbabilityMeasure μ ∧ IsCompact μ.support) := by tauto
    rw [freeConv_of_not h, freeConv_of_not h']

instance instCommutativeFreeConv : Std.Commutative (freeConv : Measure ℝ → Measure ℝ → Measure ℝ) :=
  ⟨freeConv_comm⟩

/-- Free additive convolution of Borel measures on `ℝ` is associative. -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) : (μ ⊞ ν) ⊞ ρ = μ ⊞ (ν ⊞ ρ) := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support ∧
      IsProbabilityMeasure ρ ∧ IsCompact ρ.support
  · obtain ⟨hμp, hμ, hνp, hν, hρp, hρ⟩ := h
    have _ := isProbabilityMeasure_freeConv hμ hν
    have _ := isProbabilityMeasure_freeConv hν hρ
    have _ := isProbabilityMeasure_freeConv (isCompact_support_freeConv μ ν) hρ
    have _ := isProbabilityMeasure_freeConv hμ (isCompact_support_freeConv ν ρ)
    rw [eq_iff_rSeries_eq (isCompact_support_freeConv _ _) (isCompact_support_freeConv _ _),
      rSeries_freeConv (isCompact_support_freeConv μ ν) hρ, rSeries_freeConv hμ hν,
      rSeries_freeConv hμ (isCompact_support_freeConv ν ρ), rSeries_freeConv hν hρ, add_assoc]
  · have hL : ¬(IsProbabilityMeasure (μ ⊞ ν) ∧ IsCompact (μ ⊞ ν).support ∧
        IsProbabilityMeasure ρ ∧ IsCompact ρ.support) := by
      rw [isProbabilityMeasure_freeConv_iff]
      have := isCompact_support_freeConv μ ν
      tauto
    have hR : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
        IsProbabilityMeasure (ν ⊞ ρ) ∧ IsCompact (ν ⊞ ρ).support) := by
      rw [isProbabilityMeasure_freeConv_iff]
      have := isCompact_support_freeConv ν ρ
      tauto
    rw [freeConv_of_not hL, freeConv_of_not hR]

instance instAssociativeFreeConv : Std.Associative (freeConv : Measure ℝ → Measure ℝ → Measure ℝ) :=
  ⟨freeConv_assoc⟩

theorem freeConv_left_comm (μ ν ρ : Measure ℝ) : μ ⊞ (ν ⊞ ρ) = ν ⊞ (μ ⊞ ρ) := by
  rw [← freeConv_assoc, freeConv_comm μ ν, freeConv_assoc]

theorem freeConv_right_comm (μ ν ρ : Measure ℝ) : (μ ⊞ ν) ⊞ ρ = (μ ⊞ ρ) ⊞ ν := by
  rw [freeConv_assoc, freeConv_comm ν ρ, ← freeConv_assoc]

private lemma isCompact_support_dirac (c : ℝ) : IsCompact (Measure.dirac c).support := by
  rw [Measure.support_dirac (a := c), closure_singleton]
  exact isCompact_singleton

private lemma isCompact_support_map_affine_iff {μ : Measure ℝ} {a b : ℝ} (hb : b ≠ 0) :
    IsCompact (μ.map fun x ↦ a + b * x).support ↔ IsCompact μ.support := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.smulOfNeZero b hb).trans (Homeomorph.addLeft a)
  have he : (e : ℝ → ℝ) = fun x ↦ a + b * x := by
    ext x
    simp [e, smul_eq_mul]
  rw [TauCeti.Probability.support_map_affine hb, ← he]
  exact e.isCompact_image

/-- Free additive convolution with a point mass `δ_c` on the left translates a compactly supported
probability measure by `c`. -/
theorem dirac_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : Measure.dirac c ⊞ μ = μ.map (c + ·) := by
  have hc := isCompact_support_dirac c
  have _ := isProbabilityMeasure_freeConv hc hμ
  have hmap_comp : IsCompact (μ.map (c + ·)).support := by
    have h1 : (μ.map (c + ·)) = μ.map (fun x ↦ c + 1 * x) := by simp
    rw [h1]
    exact (isCompact_support_map_affine_iff one_ne_zero).mpr hμ
  rw [eq_iff_rSeries_eq (isCompact_support_freeConv _ _) hmap_comp,
    rSeries_freeConv hc hμ, rSeries_dirac,
    rSeries_map_add_left (fun n ↦ integrable_pow_of_isCompact_support hμ n) c, add_comm]

/-- Free additive convolution with a point mass `δ_c` on the right translates a compactly supported
probability measure by `c`. -/
theorem freeConv_dirac {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : μ ⊞ Measure.dirac c = μ.map (· + c) := by
  simpa only [freeConv_comm, add_comm c] using dirac_freeConv hμ c

/-- The point mass `δ₀` is the left identity for free additive convolution on compactly supported
probability measures. -/
@[simp]
theorem dirac_zero_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    Measure.dirac 0 ⊞ μ = μ := by
  simpa using dirac_freeConv hμ 0

/-- The point mass `δ₀` is the right identity for free additive convolution on compactly supported
probability measures. -/
@[simp]
theorem freeConv_dirac_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    μ ⊞ Measure.dirac 0 = μ := by
  simpa using freeConv_dirac hμ 0

/-- Free additive convolution of two point masses adds their atoms. -/
@[simp]
theorem dirac_freeConv_dirac (a b : ℝ) :
    Measure.dirac a ⊞ Measure.dirac b = Measure.dirac (a + b) := by
  rw [dirac_freeConv (isCompact_support_dirac b) a, Measure.map_dirac' (by fun_prop)]

/-! ### Affine pushforwards, translations, reflections, and dilations -/

/-- Nonconstant affine pushforwards with a common nonzero slope commute with free additive
convolution unconditionally on all Borel measures on `ℝ`. -/
theorem freeConv_map_affine_of_ne_zero (μ ν : Measure ℝ) (a c : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (μ.map fun x ↦ a + b * x) ⊞ (ν.map fun x ↦ c + b * x) =
      (μ ⊞ ν).map fun x ↦ a + c + b * x := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμp, hμ, hνp, hν⟩ := h
    have hμ' : IsCompact (μ.map fun x ↦ a + b * x).support :=
      (isCompact_support_map_affine_iff hb).mpr hμ
    have hν' : IsCompact (ν.map fun x ↦ c + b * x).support :=
      (isCompact_support_map_affine_iff hb).mpr hν
    have _ : IsProbabilityMeasure (μ ⊞ ν) := isProbabilityMeasure_freeConv hμ hν
    have _ := isProbabilityMeasure_freeConv hμ' hν'
    have hconv_comp : IsCompact ((μ ⊞ ν).map fun x ↦ a + c + b * x).support :=
      (isCompact_support_map_affine_iff hb).mpr (isCompact_support_freeConv μ ν)
    rw [eq_iff_rSeries_eq (isCompact_support_freeConv _ _) hconv_comp,
      rSeries_freeConv hμ' hν',
      rSeries_map_affine (fun n ↦ integrable_pow_of_isCompact_support hμ n) a b,
      rSeries_map_affine (fun n ↦ integrable_pow_of_isCompact_support hν n) c b,
      rSeries_map_affine
        (fun n ↦ integrable_pow_of_isCompact_support (isCompact_support_freeConv μ ν) n)
        (a + c) b,
      rSeries_freeConv hμ hν, map_add, smul_add, map_add]
    ring
  · have hL : ¬(IsProbabilityMeasure (μ.map fun x ↦ a + b * x) ∧
        IsCompact (μ.map fun x ↦ a + b * x).support ∧
        IsProbabilityMeasure (ν.map fun x ↦ c + b * x) ∧
        IsCompact (ν.map fun x ↦ c + b * x).support) := by
      rwa [Measure.isProbabilityMeasure_map_iff (by fun_prop),
        isCompact_support_map_affine_iff hb,
        Measure.isProbabilityMeasure_map_iff (by fun_prop),
        isCompact_support_map_affine_iff hb]
    rw [freeConv_of_not hL, freeConv_of_not h, Measure.map_zero]

/-- Translating `μ` by `a` and `ν` by `c` translates `μ ⊞ ν` by `a + c`. -/
theorem freeConv_map_add (μ ν : Measure ℝ) (a c : ℝ) :
    (μ.map (a + ·)) ⊞ (ν.map (c + ·)) = (μ ⊞ ν).map (a + c + ·) := by
  simpa using freeConv_map_affine_of_ne_zero μ ν a c one_ne_zero

/-- Reflection commutes with free additive convolution. -/
theorem freeConv_neg (μ ν : Measure ℝ) : μ.neg ⊞ ν.neg = (μ ⊞ ν).neg := by
  have hneg (ρ : Measure ℝ) : ρ.neg = ρ.map fun x ↦ 0 + (-1 : ℝ) * x := by
    rw [Measure.neg_def]
    congr 1
    ext x
    ring
  simpa only [← hneg, add_zero] using
    freeConv_map_affine_of_ne_zero μ ν 0 0 (neg_ne_zero.mpr one_ne_zero)

/-- Nonzero left dilation commutes with free additive convolution on all Borel measures on `ℝ`. -/
theorem freeConv_map_mul_left_of_ne_zero (μ ν : Measure ℝ) {b : ℝ} (hb : b ≠ 0) :
    (μ.map (b * ·)) ⊞ (ν.map (b * ·)) = (μ ⊞ ν).map (b * ·) := by
  simpa using freeConv_map_affine_of_ne_zero μ ν 0 0 hb

/-- **Affine pushforward law for free additive convolution.** For compactly supported probability
measures `μ` and `ν` on `ℝ` and any real parameters `a`, `c`, and `b` (including `b = 0`),
`(μ.map fun x ↦ a + b * x) ⊞ (ν.map fun x ↦ c + b * x) = (μ ⊞ ν).map fun x ↦ a + c + b * x`. -/
theorem freeConv_map_affine {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (a c b : ℝ) :
    (μ.map fun x ↦ a + b * x) ⊞ (ν.map fun x ↦ c + b * x) =
      (μ ⊞ ν).map fun x ↦ a + c + b * x := by
  by_cases hb : b = 0
  · subst hb
    have _ := isProbabilityMeasure_freeConv hμ hν
    simp [Measure.map_const]
  · exact freeConv_map_affine_of_ne_zero μ ν a c hb

/-- Left dilation commutes with free additive convolution of compactly supported probability
measures at every real scale `b` (including `b = 0`). -/
theorem freeConv_map_mul_left {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (b : ℝ) :
    (μ.map (b * ·)) ⊞ (ν.map (b * ·)) = (μ ⊞ ν).map (b * ·) := by
  simpa using freeConv_map_affine hμ hν 0 0 b

/-! ### Interval support bounds -/

private lemma support_freeConv_subset_symmetric_Icc {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {r₁ r₂ : ℝ} (hμ : μ.support ⊆ Set.Icc (-r₁) r₁)
    (hν : ν.support ⊆ Set.Icc (-r₂) r₂) :
    (μ ⊞ ν).support ⊆ Set.Icc (-(r₁ + r₂)) (r₁ + r₂) := by
  have hr₁ : 0 ≤ r₁ := by
    obtain ⟨x, hx⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
    linarith [(hμ hx).1, (hμ hx).2]
  have hr₂ : 0 ≤ r₂ := by
    obtain ⟨x, hx⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero ν)
    linarith [(hν hx).1, (hν hx).2]
  have hμc : IsCompact μ.support := isCompact_Icc.of_isClosed_subset Measure.isClosed_support hμ
  have hνc : IsCompact ν.support := isCompact_Icc.of_isClosed_subset Measure.isClosed_support hν
  rw [freeConv_eq_freeConvAux hμc hνc, freeConvAux]
  let R := canonicalFreeConvRealization μ ν hμc hνc
  have hsa : IsSelfAdjoint (R.a true + R.a false) := (R.hsa true).add (R.hsa false)
  have hnorm : ‖R.a true + R.a false‖ ≤ r₁ + r₂ :=
    (norm_add_le _ _).trans (add_le_add (R.hnorm_true r₁ hr₁ hμ) (R.hnorm_false r₂ hr₂ hν))
  have hspec : spectrum ℝ (R.a true + R.a false) ⊆ Set.Icc (-(r₁ + r₂)) (r₁ + r₂) :=
    (hsa.norm_le_iff_spectrum_subset_Icc (add_nonneg hr₁ hr₂)).mp hnorm
  exact (PositiveLinearMap.support_law_subset_spectrum R.φ _).trans hspec

/-- **Support bound for free additive convolution.** If `μ.support ⊆ [a₁, b₁]` and
`ν.support ⊆ [a₂, b₂]`, then `(μ ⊞ ν).support ⊆ [a₁ + a₂, b₁ + b₂]`. -/
theorem support_freeConv_subset_Icc {μ ν : Measure ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hμ : μ.support ⊆ Set.Icc a₁ b₁) (hν : ν.support ⊆ Set.Icc a₂ b₂) :
    (μ ⊞ ν).support ⊆ Set.Icc (a₁ + a₂) (b₁ + b₂) := by
  classical
  by_cases hp : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν
  · obtain ⟨hμp, hνp⟩ := hp
    let m₁ := (a₁ + b₁) / 2
    let r₁ := (b₁ - a₁) / 2
    let m₂ := (a₂ + b₂) / 2
    let r₂ := (b₂ - a₂) / 2
    have hsupp₁ : (μ.map (-m₁ + ·)).support ⊆ Set.Icc (-r₁) r₁ := by
      have heq : μ.map (-m₁ + ·) = μ.map fun x ↦ -m₁ + 1 * x := by simp
      rw [heq, TauCeti.Probability.support_map_affine one_ne_zero]
      rintro _ ⟨x, hx, rfl⟩
      have hx' := hμ hx
      dsimp only [m₁, r₁]
      exact ⟨by linarith [hx'.1, hx'.2], by linarith [hx'.1, hx'.2]⟩
    have hsupp₂ : (ν.map (-m₂ + ·)).support ⊆ Set.Icc (-r₂) r₂ := by
      have heq : ν.map (-m₂ + ·) = ν.map fun x ↦ -m₂ + 1 * x := by simp
      rw [heq, TauCeti.Probability.support_map_affine one_ne_zero]
      rintro _ ⟨x, hx, rfl⟩
      have hx' := hν hx
      dsimp only [m₂, r₂]
      exact ⟨by linarith [hx'.1, hx'.2], by linarith [hx'.1, hx'.2]⟩
    have hsym := support_freeConv_subset_symmetric_Icc hsupp₁ hsupp₂
    rw [freeConv_map_add] at hsym
    have heq : (μ ⊞ ν).map (-m₁ + -m₂ + ·) = (μ ⊞ ν).map fun x ↦ (-m₁ + -m₂) + 1 * x := by simp
    rw [heq, TauCeti.Probability.support_map_affine one_ne_zero] at hsym
    intro y hy
    have hy' := hsym ⟨y, hy, rfl⟩
    dsimp only [m₁, r₁, m₂, r₂] at hy'
    exact ⟨by linarith [hy'.1, hy'.2], by linarith [hy'.1, hy'.2]⟩
  · rw [freeConv_of_not fun h ↦ hp ⟨h.1, h.2.2.1⟩]
    simp

/-- Almost-everywhere interval concentration under free additive convolution. -/
theorem ae_mem_Icc_freeConv {μ ν : Measure ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a₁ b₁) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a₂ b₂) :
    ∀ᵐ x ∂(μ ⊞ ν), x ∈ Set.Icc (a₁ + a₂) (b₁ + b₂) := by
  have hμs : μ.support ⊆ Set.Icc a₁ b₁ := Measure.support_subset_of_isClosed isClosed_Icc hμ
  have hνs : ν.support ⊆ Set.Icc a₂ b₂ := Measure.support_subset_of_isClosed isClosed_Icc hν
  filter_upwards [Measure.support_mem_ae (μ := μ ⊞ ν)] with x hx
  exact support_freeConv_subset_Icc hμs hνs hx

end MeasureTheory.Measure

namespace TauCeti.Probability

open scoped MeasureTheory

private lemma isCompact_support_semicircleReal (a : ℝ) (v : ℝ≥0) :
    IsCompact (semicircleReal a v).support :=
  support_semicircleReal a v ▸ isCompact_Icc

/-- **Free additive convolution of real semicircle laws.** Means and variances add:
`semicircleReal a v ⊞ semicircleReal b w = semicircleReal (a + b) (v + w)`. -/
@[simp]
theorem semicircleReal_freeConv_semicircleReal (a : ℝ) (v : ℝ≥0) (b : ℝ) (w : ℝ≥0) :
    semicircleReal a v ⊞ semicircleReal b w = semicircleReal (a + b) (v + w) := by
  have hv := isCompact_support_semicircleReal a v
  have hw := isCompact_support_semicircleReal b w
  have hvw := isCompact_support_semicircleReal (a + b) (v + w)
  have _ := Measure.isProbabilityMeasure_freeConv hv hw
  rw [Measure.eq_iff_rSeries_eq (Measure.isCompact_support_freeConv _ _) hvw,
    Measure.rSeries_freeConv hv hw, rSeries_semicircleReal, rSeries_semicircleReal,
    rSeries_semicircleReal]
  simp only [NNReal.coe_add, map_add]
  ring

end TauCeti.Probability
