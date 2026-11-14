/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.FreeProbability.FreeProduct.Reduced
public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Probability.FreeProbability.WeakClosure
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
import TauCeti.MeasureTheory.Measure.Support

/-!
# Canonical C⋆- and von Neumann free product realizations of compactly supported laws

Each compactly supported Borel probability measure `μ i` on `ℝ` is realized on `(μ i).support` as
the scalar law of `x ↦ (x : ℂ)` in `C((μ i).support, ℂ)` under `(μ i).comap (↑)`. Taking the reduced
C⋆-free product (`TauCeti.ReducedFreeProduct`) yields a C⋆-probability space
`TauCeti.FreeLawRealization.algebra μ` on `TauCeti.FreeLawRealization.HilbertSpace μ` and generated
concrete von Neumann algebra `TauCeti.FreeLawRealization.vonNeumannAlgebra μ` whose canonical
selfadjoint generators are freely independent (with freely independent generated von Neumann
subalgebras), have scalar laws `μ i` and real spectra in `(μ i).support`, and carry tracial vacuum
states.

## Main definitions

* `TauCeti.FreeLawRealization.HilbertSpace`, `TauCeti.FreeLawRealization.vacuum`,
  `TauCeti.FreeLawRealization.vectorState`, `TauCeti.FreeLawRealization.algebra`,
  `TauCeti.FreeLawRealization.state`, `TauCeti.FreeLawRealization.factor`,
  `TauCeti.FreeLawRealization.generator`: C⋆-free product realization of `μ`.
* `TauCeti.FreeLawRealization.vonNeumannAlgebra`, `TauCeti.FreeLawRealization.toVonNeumannAlgebra`,
  `TauCeti.FreeLawRealization.vonNeumannState`, `TauCeti.FreeLawRealization.vonNeumannGenerator`:
  generated concrete von Neumann realization of `μ`.

## Main results

* `TauCeti.FreeLawRealization.isFreelyIndependent_factor`,
  `TauCeti.FreeLawRealization.isFreelyIndependentElements_generator`,
  `TauCeti.FreeLawRealization.law_generator`,
  `TauCeti.FreeLawRealization.spectrum_generator_subset_support`,
  `TauCeti.FreeLawRealization.state_mul_comm`: freeness, laws, spectral bounds, and traciality in
  `algebra μ`.
* `TauCeti.FreeLawRealization.isFreelyIndependentElements_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.isFreelyIndependent_vonNeumannAlgebra_adjoin_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.law_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.vonNeumannState_mul_comm`: von Neumann counterparts.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §§1.5, 3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 5 and 7.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder InnerProductSpace

namespace TauCeti
namespace FreeLawRealization

section Factor

variable {ι : Type*} (μ : ι → Measure ℝ)

private def factorCoordinate (i : ι) : C((μ i).support, ℂ) :=
  (ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ)).realToRCLike ℂ

private theorem isSelfAdjoint_factorCoordinate (i : ι) : IsSelfAdjoint (factorCoordinate μ i) :=
  ContinuousMap.isSelfAdjoint_realToRCLike ℂ

private theorem spectrum_factorCoordinate_subset_support (i : ι) :
    spectrum ℝ (factorCoordinate μ i) ⊆ (μ i).support := by
  rintro r hr; rw [ContinuousMap.spectrum_eq_preimage_range] at hr
  rcases hr with ⟨x, hx⟩; exact (Complex.ofReal_injective hx : x.1 = r) ▸ x.2

variable [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

private def factorPositiveLinearMap (i : ι) : C((μ i).support, ℂ) →ₚ[ℂ] ℂ :=
  ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : (μ i).support → ℝ))

private def factorFunctional (i : ι) : StarPositiveFunctional C((μ i).support, ℂ) :=
  StarPositiveFunctional.ofPositiveLinearMap (factorPositiveLinearMap μ i)

private theorem factorFunctional_one (i : ι) : factorFunctional μ i 1 = 1 := by
  simp [factorFunctional, factorPositiveLinearMap]

private theorem law_factorCoordinate (i : ι) :
    (factorPositiveLinearMap μ i).law (factorCoordinate μ i) = μ i :=
  PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
    (Measure.measure_compl_support (μ := μ i))

end Factor

private theorem apply_mul_comm_of_mem_closure {R E : Type*} [TopologicalSpace R] [Ring R]
    [IsSemitopologicalRing R] [TopologicalSpace E] [T2Space E] {f : R → E} (hf : Continuous f)
    {s : Set R} (hs : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f (y * x))
    {x y : R} (hx : x ∈ closure s) (hy : y ∈ closure s) : f (x * y) = f (y * x) :=
  closure_minimal (fun a ha => closure_minimal (fun b hb => hs a ha b hb)
    (isClosed_eq (hf.comp (continuous_const_mul a)) (hf.comp (continuous_mul_const a))) hy)
    (isClosed_eq (hf.comp (continuous_mul_const y)) (hf.comp (continuous_const_mul y))) hx

section Product

variable {ι : Type*} [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

-- Keep `HilbertSpace` an unexposed `def` with explicit Hilbert-space instances so internal factor
-- functionals stay private while definitions here unify with `ReducedFreeProduct.HilbertSpace`.
/-- The completed GNS Hilbert space of the reduced free product realizing `μ`. -/
def HilbertSpace : Type _ :=
  ReducedFreeProduct.HilbertSpace (factorFunctional μ) (factorFunctional_one μ)

instance : NormedAddCommGroup (HilbertSpace μ) :=
  inferInstanceAs (NormedAddCommGroup (ReducedFreeProduct.HilbertSpace
    (fun i => StarPositiveFunctional.ofPositiveLinearMap
      (ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : (μ i).support → ℝ))))
    (fun i => by simp [StarPositiveFunctional.ofPositiveLinearMap_apply])))

instance : InnerProductSpace ℂ (HilbertSpace μ) :=
  inferInstanceAs (InnerProductSpace ℂ (ReducedFreeProduct.HilbertSpace
    (fun i => StarPositiveFunctional.ofPositiveLinearMap
      (ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : (μ i).support → ℝ))))
    (fun i => by simp [StarPositiveFunctional.ofPositiveLinearMap_apply])))

instance : CompleteSpace (HilbertSpace μ) := by
  exact inferInstanceAs
    (CompleteSpace (ReducedFreeProduct.HilbertSpace (factorFunctional μ) (factorFunctional_one μ)))

/-- The unit cyclic vacuum vector in `HilbertSpace μ`. -/
def vacuum : HilbertSpace μ :=
  ReducedFreeProduct.vacuum (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum vector has unit norm. -/
@[simp] theorem norm_vacuum : ‖vacuum μ‖ = 1 := by
  exact ReducedFreeProduct.norm_vacuum (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum vector state on all bounded operators on `HilbertSpace μ`. -/
def vectorState : (HilbertSpace μ →L[ℂ] HilbertSpace μ) →ₚ[ℂ] ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap ℂ (vacuum μ)

/-- Evaluation of `vectorState μ` as an inner product at `vacuum μ`. -/
theorem vectorState_apply (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) :
    vectorState μ T = ⟪vacuum μ, T (vacuum μ)⟫_ℂ := by
  exact ContinuousLinearMap.innerPositiveLinearMap_apply (vacuum μ) T

/-- The vacuum vector state is normalized. -/
@[simp] theorem vectorState_one : vectorState μ 1 = 1 := by simp [vectorState]

/-- The vacuum vector state is continuous for the weak operator topology. -/
theorem continuous_wot_vectorState :
    Continuous fun T : HilbertSpace μ →WOT[ℂ] HilbertSpace μ => vectorState μ T.toCLM := by
  simp_rw [vectorState_apply]
  exact ContinuousLinearMapWOT.continuous_dual_apply (vacuum μ) (innerSL ℂ (vacuum μ))

/-- The canonical reduced C⋆-free product algebra realizing `μ`. -/
def algebra : StarSubalgebra ℂ (HilbertSpace μ →L[ℂ] HilbertSpace μ) :=
  ReducedFreeProduct.algebra (factorFunctional μ) (factorFunctional_one μ)

instance isClosed_algebra :
    IsClosed (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ)) := by
  exact ReducedFreeProduct.isClosed_algebra (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum state on the canonical C⋆-free product algebra realizing `μ`. -/
def state : algebra μ →ₚ[ℂ] ℂ :=
  ReducedFreeProduct.state (factorFunctional μ) (factorFunctional_one μ)

/-- Evaluation of `state μ` as the vacuum vector state restricted to `algebra μ`. -/
theorem state_apply (T : algebra μ) :
    state μ T = ⟪vacuum μ, (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) (vacuum μ)⟫_ℂ := by
  exact ReducedFreeProduct.state_apply (factorFunctional μ) (factorFunctional_one μ) T

/-- The vacuum state on `algebra μ` is normalized. -/
@[simp] theorem state_one : state μ 1 = 1 := by
  exact ReducedFreeProduct.state_one (factorFunctional μ) (factorFunctional_one μ)

/-- The `i`-th canonical factor `⋆`-homomorphism from `C((μ i).support, ℂ)` into `algebra μ`. -/
def factor (i : ι) : C((μ i).support, ℂ) →⋆ₐ[ℂ] algebra μ :=
  ReducedFreeProduct.factor (factorFunctional μ) (factorFunctional_one μ) i

/-- Evaluating `state μ` on the `i`-th factor integrates against `μ i` on `(μ i).support`. -/
@[simp] theorem state_factor (i : ι) (x : C((μ i).support, ℂ)) :
    state μ (factor μ i x) = ∫ t, x t ∂(μ i).comap ((↑) : (μ i).support → ℝ) := by
  exact (ReducedFreeProduct.state_factor (factorFunctional μ) (factorFunctional_one μ) i x).trans
    ((StarPositiveFunctional.ofPositiveLinearMap_apply _ _).trans
      (ContinuousMap.integralPositiveLinearMap_apply _ x))

/-- The canonical factor subalgebras in `algebra μ` are freely independent for `state μ`. -/
theorem isFreelyIndependent_factor :
    IsFreelyIndependent (state μ).toLinearMap (fun i => (factor μ i).toAlgHom.range) := by
  exact ReducedFreeProduct.isFreelyIndependent_factor (factorFunctional μ) (factorFunctional_one μ)

/-- Commutativity of each factor `C((μ i).support, ℂ)`, freeness, and norm density make `state μ`
tracial on `algebra μ`. -/
theorem state_mul_comm (x y : algebra μ) : state μ (x * y) = state μ (y * x) := by
  let S : Subalgebra ℂ (algebra μ) := ⨆ i, (factor μ i).toAlgHom.range
  have htrS : ∀ a ∈ (S : Set (algebra μ)), ∀ b ∈ (S : Set (algebra μ)),
      state μ (a * b) = state μ (b * a) := fun a ha b hb =>
    (isFreelyIndependent_factor μ).apply_mul_comm_of_mem_iSup (state_one μ)
      (by rintro i _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; rw [← map_mul, mul_comm u v, map_mul]) ha hb
  have hle : (⊤ : Subalgebra ℂ _) ≤ S.comap
      (ReducedFreeProduct.ofAlgebraic (factorFunctional μ) (factorFunctional_one μ)).toAlgHom := by
    rw [← LinearAlgebra.FreeProduct.iSup_range_ι]
    refine iSup_le fun i => ?_
    rintro _ ⟨f, rfl⟩
    exact le_iSup (fun j => (factor μ j).toAlgHom.range) i
      ⟨f, ReducedFreeProduct.factor_apply (factorFunctional μ) (factorFunctional_one μ) i f⟩
  have hdense (z : algebra μ) : z ∈ closure (S : Set (algebra μ)) :=
    closure_mono (by rintro _ ⟨w, rfl⟩; exact hle trivial)
      (ReducedFreeProduct.denseRange_ofAlgebraic (factorFunctional μ) (factorFunctional_one μ) z)
  have hcont : Continuous (state μ) := by
    have hfn : (state μ : algebra μ → ℂ) = fun T : algebra μ =>
        ⟪vacuum μ, (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) (vacuum μ)⟫_ℂ := funext (state_apply μ)
    exact hfn ▸ continuous_const.inner (continuous_subtype_val.clm_apply continuous_const)
  exact apply_mul_comm_of_mem_closure hcont htrS (hdense x) (hdense y)

/-- The `i`-th canonical selfadjoint generator in `algebra μ` realizing `μ i`. -/
def generator (i : ι) : algebra μ :=
  factor μ i (factorCoordinate μ i)

/-- `generator μ i` is `factor μ i` applied to the inclusion coordinate `x ↦ (x : ℂ)`. -/
theorem generator_eq_factor (i : ι) :
    generator μ i =
      factor μ i ((ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ)).realToRCLike ℂ) := by
  rfl

/-- Every canonical generator in `algebra μ` is selfadjoint. -/
theorem isSelfAdjoint_generator (i : ι) : IsSelfAdjoint (generator μ i) := by
  exact (isSelfAdjoint_factorCoordinate μ i).map (factor μ i)

/-- The `i`-th canonical generator in the C⋆-free product realization has law `μ i`. -/
@[simp] theorem law_generator (i : ι) : (state μ).law (generator μ i) = μ i := by
  refine (PositiveLinearMap.law_starAlgHom (factorPositiveLinearMap μ i) (state μ) (factor μ i)
    (isSelfAdjoint_factorCoordinate μ i) fun x => ?_).trans (law_factorCoordinate μ i)
  exact (state_factor μ i x).trans (ContinuousMap.integralPositiveLinearMap_apply _ x).symm

/-- The real spectrum of `generator μ i` is contained in `(μ i).support`. -/
theorem spectrum_generator_subset_support (i : ι) :
    spectrum ℝ (generator μ i) ⊆ (μ i).support := by
  exact (AlgHom.spectrum_apply_subset ((factor μ i).toAlgHom.restrictScalars ℝ)
    (factorCoordinate μ i)).trans (spectrum_factorCoordinate_subset_support μ i)

/-- The canonical generators in `algebra μ` are freely independent for `state μ`. -/
theorem isFreelyIndependentElements_generator :
    IsFreelyIndependentElements (state μ).toLinearMap (generator μ) := by
  exact (isFreelyIndependent_factor μ).isFreelyIndependentElements fun i =>
    ⟨factorCoordinate μ i, rfl⟩

/-! #### Concrete von Neumann algebra realization -/

/-- The concrete von Neumann algebra on `HilbertSpace μ` generated by `algebra μ`. -/
def vonNeumannAlgebra : VonNeumannAlgebra (HilbertSpace μ) :=
  VonNeumannAlgebra.adjoin (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ))

/-- The canonical `⋆`-algebra inclusion from `algebra μ` into `vonNeumannAlgebra μ`. -/
def toVonNeumannAlgebra : algebra μ →⋆ₐ[ℂ] vonNeumannAlgebra μ where
  toFun x := ⟨x.1, VonNeumannAlgebra.subset_adjoin _ x.2⟩
  map_one' := rfl; map_mul' _ _ := rfl; map_zero' := rfl
  map_add' _ _ := rfl; commutes' _ := rfl; map_star' _ := rfl

/-- Coercing `toVonNeumannAlgebra μ T` to a bounded operator recovers `T`. -/
@[simp] theorem coe_toVonNeumannAlgebra (T : algebra μ) :
    ((toVonNeumannAlgebra μ T : vonNeumannAlgebra μ) :
      HilbertSpace μ →L[ℂ] HilbertSpace μ) = T := by rfl

/-- The vacuum vector state restricted to `vonNeumannAlgebra μ`. -/
def vonNeumannState : vonNeumannAlgebra μ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((vectorState μ).toLinearMap.comp (vonNeumannAlgebra μ).toStarSubalgebra.subtype.toLinearMap)
    fun _ hT => (vectorState μ).map_nonneg hT

/-- Evaluation of `vonNeumannState μ` via `vectorState μ`. -/
theorem vonNeumannState_apply (T : vonNeumannAlgebra μ) :
    vonNeumannState μ T = vectorState μ (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) := by rfl

/-- The vacuum state on `vonNeumannAlgebra μ` is normalized. -/
@[simp] theorem vonNeumannState_one : vonNeumannState μ 1 = 1 := by
  rw [vonNeumannState_apply, OneMemClass.coe_one, vectorState_one]

/-- The inclusion `toVonNeumannAlgebra μ` intertwines `state μ` and `vonNeumannState μ`. -/
@[simp] theorem vonNeumannState_toVonNeumannAlgebra (T : algebra μ) :
    vonNeumannState μ (toVonNeumannAlgebra μ T) = state μ T := by
  rw [vonNeumannState_apply, coe_toVonNeumannAlgebra, vectorState_apply, state_apply]

/-- Traciality of `state μ` extends by WOT density and continuity to `vonNeumannAlgebra μ`. -/
theorem vonNeumannState_mul_comm (x y : vonNeumannAlgebra μ) :
    vonNeumannState μ (x * y) = vonNeumannState μ (y * x) := by
  let s : Set (HilbertSpace μ →WOT[ℂ] HilbertSpace μ) :=
    ContinuousLinearMapWOT.ofCLM '' (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ))
  have hmul (A B : HilbertSpace μ →L[ℂ] HilbertSpace μ) :
      (ContinuousLinearMapWOT.ofCLM A * ContinuousLinearMapWOT.ofCLM B).toCLM = A * B := by
    rw [← ContinuousLinearMapWOT.ofCLM_mul, ContinuousLinearMapWOT.toCLM_ofCLM]
  have hs : ∀ a ∈ s, ∀ b ∈ s, vectorState μ (a * b).toCLM = vectorState μ (b * a).toCLM := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    simpa only [hmul, vectorState_apply, state_apply, MulMemClass.coe_mul] using
      state_mul_comm μ ⟨A, hA⟩ ⟨B, hB⟩
  have hmem (z : vonNeumannAlgebra μ) :
      ContinuousLinearMapWOT.ofCLM (z : HilbertSpace μ →L[ℂ] HilbertSpace μ) ∈ closure s := by
    dsimp only [s]
    rw [← StarAlgebra.adjoin_eq (algebra μ), ← VonNeumannAlgebra.image_ofCLM_adjoin_eq_closure]
    exact ⟨z, z.2, rfl⟩
  simpa only [vonNeumannState_apply, MulMemClass.coe_mul, hmul] using
    apply_mul_comm_of_mem_closure (continuous_wot_vectorState μ) hs (hmem x) (hmem y)

/-- The `i`-th canonical selfadjoint element inside `vonNeumannAlgebra μ` realizing `μ i`. -/
def vonNeumannGenerator (i : ι) : vonNeumannAlgebra μ :=
  toVonNeumannAlgebra μ (generator μ i)

/-- Including `generator μ i` into `vonNeumannAlgebra μ` gives `vonNeumannGenerator μ i`. -/
@[simp] theorem toVonNeumannAlgebra_generator (i : ι) :
    toVonNeumannAlgebra μ (generator μ i) = vonNeumannGenerator μ i := by rfl

/-- Coercing `vonNeumannGenerator μ i` to a bounded operator agrees with `generator μ i`. -/
@[simp] theorem coe_vonNeumannGenerator (i : ι) :
    ((vonNeumannGenerator μ i : vonNeumannAlgebra μ) :
      HilbertSpace μ →L[ℂ] HilbertSpace μ) = generator μ i := by rfl

/-- Evaluating `vonNeumannState μ` on `vonNeumannGenerator μ i` agrees with `state μ` on
`generator μ i`. -/
@[simp] theorem vonNeumannState_vonNeumannGenerator (i : ι) :
    vonNeumannState μ (vonNeumannGenerator μ i) = state μ (generator μ i) := by
  exact vonNeumannState_toVonNeumannAlgebra μ (generator μ i)

/-- Every canonical generator in `vonNeumannAlgebra μ` is selfadjoint. -/
theorem isSelfAdjoint_vonNeumannGenerator (i : ι) : IsSelfAdjoint (vonNeumannGenerator μ i) := by
  exact (isSelfAdjoint_generator μ i).map (toVonNeumannAlgebra μ)

/-- The `i`-th canonical generator in `vonNeumannAlgebra μ` has law `μ i`. -/
@[simp] theorem law_vonNeumannGenerator (i : ι) :
    (vonNeumannState μ).law (vonNeumannGenerator μ i) = μ i := by
  exact (PositiveLinearMap.law_starAlgHom (state μ) (vonNeumannState μ) (toVonNeumannAlgebra μ)
    (isSelfAdjoint_generator μ i) (vonNeumannState_toVonNeumannAlgebra μ)).trans (law_generator μ i)

/-- The real spectrum of `vonNeumannGenerator μ i` is contained in `(μ i).support`. -/
theorem spectrum_vonNeumannGenerator_subset_support (i : ι) :
    spectrum ℝ (vonNeumannGenerator μ i) ⊆ (μ i).support := by
  exact (AlgHom.spectrum_apply_subset ((toVonNeumannAlgebra μ).toAlgHom.restrictScalars ℝ)
    (generator μ i)).trans (spectrum_generator_subset_support μ i)

/-- The canonical generators in `vonNeumannAlgebra μ` are freely independent for
`vonNeumannState μ`. -/
theorem isFreelyIndependentElements_vonNeumannGenerator :
    IsFreelyIndependentElements (vonNeumannState μ).toLinearMap (vonNeumannGenerator μ) := by
  exact (isFreelyIndependentElements_generator μ).map (toVonNeumannAlgebra μ).toAlgHom <|
    LinearMap.ext (vonNeumannState_toVonNeumannAlgebra μ)

/-- The concrete von Neumann subalgebras generated by `vonNeumannGenerator μ i` on `HilbertSpace μ`
are freely independent for the weak-operator continuous vacuum vector state. -/
theorem isFreelyIndependent_vonNeumannAlgebra_adjoin_vonNeumannGenerator :
    IsFreelyIndependent (vectorState μ).toLinearMap
      (fun i => (VonNeumannAlgebra.adjoin
        {(vonNeumannGenerator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ)}).toSubalgebra) := by
  simp_rw [coe_vonNeumannGenerator]
  refine (isFreelyIndependent_vonNeumannAlgebra_adjoin_singleton_iff_of_isSelfAdjoint
    (T := fun i => (generator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ)) (vectorState_one μ)
    (continuous_wot_vectorState μ) fun i => (isSelfAdjoint_generator μ i).map (algebra μ).subtype
    ).mpr <| (isFreelyIndependentElements_generator μ).map (algebra μ).subtype.toAlgHom <|
      LinearMap.ext fun x => by simp [vectorState_apply, state_apply]

end Product

end FreeLawRealization
end TauCeti
