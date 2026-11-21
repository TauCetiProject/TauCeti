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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
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
subalgebras), have scalar laws `μ i` and real spectra `(μ i).support`, and carry tracial vacuum
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

* `TauCeti.FreeLawRealization.denseRange_algebra_vacuum`,
  `TauCeti.FreeLawRealization.factor_injective`,
  `TauCeti.FreeLawRealization.topologicalClosure_iSup_range_factor`,
  `TauCeti.FreeLawRealization.topologicalClosure_starAlgebra_adjoin_range_generator`,
  `TauCeti.FreeLawRealization.starAlgHom_ext`,
  `TauCeti.FreeLawRealization.isFreelyIndependent_factor`,
  `TauCeti.FreeLawRealization.isFreelyIndependentElements_generator`,
  `TauCeti.FreeLawRealization.law_generator`,
  `TauCeti.FreeLawRealization.spectrum_generator`,
  `TauCeti.FreeLawRealization.state_mul_comm`: cyclicity, density, uniqueness, freeness, laws,
  spectra, and traciality in `algebra μ`.
* `TauCeti.FreeLawRealization.vonNeumannAlgebra_eq_adjoin`,
  `TauCeti.FreeLawRealization.vonNeumannAlgebra_eq_adjoin_range_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.isFreelyIndependentElements_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.isFreelyIndependent_vonNeumannAlgebra_adjoin_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.law_vonNeumannGenerator`,
  `TauCeti.FreeLawRealization.spectrum_vonNeumannGenerator`,
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

/-- The vacuum vector `vacuum μ` is cyclic for `algebra μ`. -/
theorem denseRange_algebra_vacuum :
    DenseRange (fun T : algebra μ =>
      (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) (vacuum μ)) :=
  ReducedFreeProduct.denseRange_algebra_vacuum (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum state on the canonical C⋆-free product algebra realizing `μ`. -/
def state : algebra μ →ₚ[ℂ] ℂ :=
  ReducedFreeProduct.state (factorFunctional μ) (factorFunctional_one μ)

/-- Evaluation of `state μ` as the vacuum vector state restricted to `algebra μ`. -/
theorem state_apply (T : algebra μ) :
    state μ T = ⟪vacuum μ, (T : HilbertSpace μ →L[ℂ] HilbertSpace μ) (vacuum μ)⟫_ℂ :=
  ReducedFreeProduct.state_apply (factorFunctional μ) (factorFunctional_one μ) T

/-- The vacuum state on `algebra μ` is normalized. -/
@[simp] theorem state_one : state μ 1 = 1 :=
  ReducedFreeProduct.state_one (factorFunctional μ) (factorFunctional_one μ)

/-- The `i`-th canonical factor `⋆`-homomorphism from `C((μ i).support, ℂ)` into `algebra μ`. -/
def factor (i : ι) : C((μ i).support, ℂ) →⋆ₐ[ℂ] algebra μ :=
  ReducedFreeProduct.factor (factorFunctional μ) (factorFunctional_one μ) i

/-- The canonical factor subalgebras generate a norm-dense subalgebra of `algebra μ`. -/
theorem topologicalClosure_iSup_range_factor :
    (⨆ i, (factor μ i).toAlgHom.range).topologicalClosure = ⊤ := by
  let f : LinearAlgebra.FreeProduct ℂ (fun i => C((μ i).support, ℂ)) →⋆ₐ[ℂ] algebra μ :=
    ReducedFreeProduct.ofAlgebraic (factorFunctional μ) (factorFunctional_one μ)
  have hranges : (⨆ i, (factor μ i).toAlgHom.range) = f.toAlgHom.range := by
    have hcomp : ∀ i, (factor μ i).toAlgHom.range =
        (LinearAlgebra.FreeProduct.ι ℂ _ i).range.map f.toAlgHom := fun i => by
      have hf : (factor μ i).toAlgHom = f.toAlgHom.comp (LinearAlgebra.FreeProduct.ι ℂ _ i) :=
        AlgHom.ext fun x => ReducedFreeProduct.factor_apply (factorFunctional μ)
          (factorFunctional_one μ) i x
      rw [hf, AlgHom.range_comp]
    simp_rw [hcomp, ← (Subalgebra.gc_map_comap f.toAlgHom).l_iSup,
      LinearAlgebra.FreeProduct.iSup_range_ι, Algebra.map_top]
  exact SetLike.coe_injective <| by
    rw [Subalgebra.topologicalClosure_coe, hranges, AlgHom.coe_range, Algebra.coe_top]
    exact (ReducedFreeProduct.denseRange_ofAlgebraic (factorFunctional μ)
      (factorFunctional_one μ)).closure_eq

/-- Evaluating `state μ` on the `i`-th factor integrates against `μ i` on `(μ i).support`. -/
@[simp] theorem state_factor (i : ι) (x : C((μ i).support, ℂ)) :
    state μ (factor μ i x) = ∫ t, x t ∂(μ i).comap ((↑) : (μ i).support → ℝ) :=
  (ReducedFreeProduct.state_factor (factorFunctional μ) (factorFunctional_one μ) i x).trans
    ((StarPositiveFunctional.ofPositiveLinearMap_apply _ _).trans
      (ContinuousMap.integralPositiveLinearMap_apply _ x))

/-- Each canonical factor `⋆`-homomorphism `factor μ i` is injective. -/
theorem factor_injective (i : ι) : Function.Injective (factor μ i) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hstate : state μ (factor μ i (star f * f)) = 0 := by
    rw [map_mul, map_star, hf, star_zero, zero_mul, map_zero]
  rw [state_factor] at hstate
  have hfun : (fun t : (μ i).support => (star f * f) t) = fun t => ((‖f t‖ ^ 2 : ℝ) : ℂ) := by
    ext t
    simp [Complex.conj_mul']
  rw [show (∫ t, (star f * f) t ∂(μ i).comap ((↑) : (μ i).support → ℝ)) =
      ∫ t, ((‖f t‖ ^ 2 : ℝ) : ℂ) ∂(μ i).comap ((↑) : (μ i).support → ℝ) from
    integral_congr_ae (Filter.Eventually.of_forall fun t => congrFun hfun t),
    integral_complex_ofReal, Complex.ofReal_eq_zero] at hstate
  refine ContinuousMap.ext fun t => by_contra fun ht => ?_
  have hpos : 0 < ∫ x, ‖f x‖ ^ 2 ∂(μ i).comap ((↑) : (μ i).support → ℝ) :=
    integral_pos_of_integrable_nonneg_ne_zero (f.continuous.norm.pow 2)
      ((f.continuous.norm.pow 2).integrable_of_hasCompactSupport (.of_compactSpace _))
      (fun _ => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr ht))
  exact hpos.ne' hstate

/-- The canonical factor subalgebras in `algebra μ` are freely independent for `state μ`. -/
theorem isFreelyIndependent_factor :
    IsFreelyIndependent (state μ).toLinearMap (fun i => (factor μ i).toAlgHom.range) :=
  ReducedFreeProduct.isFreelyIndependent_factor (factorFunctional μ) (factorFunctional_one μ)

/-- The vacuum state `state μ` is tracial on `algebra μ`. -/
theorem state_mul_comm (x y : algebra μ) : state μ (x * y) = state μ (y * x) :=
  ReducedFreeProduct.state_mul_comm (factorFunctional μ) (factorFunctional_one μ)
    (fun _ a b => by rw [mul_comm]) x y

/-- The `i`-th canonical selfadjoint generator in `algebra μ` realizing `μ i`. -/
def generator (i : ι) : algebra μ :=
  factor μ i (factorCoordinate μ i)

/-- `generator μ i` is `factor μ i` applied to the inclusion coordinate `x ↦ (x : ℂ)`. -/
theorem generator_eq_factor (i : ι) :
    generator μ i =
      factor μ i ((ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ)).realToRCLike ℂ) := by
  rfl

/-- Every canonical generator in `algebra μ` is selfadjoint. -/
theorem isSelfAdjoint_generator (i : ι) : IsSelfAdjoint (generator μ i) :=
  (isSelfAdjoint_factorCoordinate μ i).map (factor μ i)

/-- The `i`-th canonical generator in the C⋆-free product realization has law `μ i`. -/
@[simp] theorem law_generator (i : ι) : (state μ).law (generator μ i) = μ i := by
  refine (PositiveLinearMap.law_starAlgHom (factorPositiveLinearMap μ i) (state μ) (factor μ i)
    (isSelfAdjoint_factorCoordinate μ i) fun x => ?_).trans (law_factorCoordinate μ i)
  exact (state_factor μ i x).trans (ContinuousMap.integralPositiveLinearMap_apply _ x).symm

/-- The real spectrum of `generator μ i` equals `(μ i).support`. -/
@[simp] theorem spectrum_generator (i : ι) : spectrum ℝ (generator μ i) = (μ i).support := by
  refine Set.Subset.antisymm ?_
    (law_generator μ i ▸ PositiveLinearMap.support_law_subset_spectrum (state μ) (generator μ i))
  refine (AlgHom.spectrum_apply_subset ((factor μ i).toAlgHom.restrictScalars ℝ)
    (factorCoordinate μ i)).trans ?_
  rw [factorCoordinate, ContinuousMap.spectrum_realToRCLike, ContinuousMap.spectrum_eq_range]
  rintro _ ⟨x, rfl⟩
  exact x.property

/-- The canonical generators in `algebra μ` are freely independent for `state μ`. -/
theorem isFreelyIndependentElements_generator :
    IsFreelyIndependentElements (state μ).toLinearMap (generator μ) :=
  (isFreelyIndependent_factor μ).isFreelyIndependentElements fun i => ⟨factorCoordinate μ i, rfl⟩

/-- The `⋆`-subalgebra generated by `Set.range (generator μ)` is norm dense in `algebra μ`. -/
theorem topologicalClosure_starAlgebra_adjoin_range_generator :
    (StarAlgebra.adjoin ℂ (Set.range (generator μ))).topologicalClosure = ⊤ := by
  let S : StarSubalgebra ℂ (algebra μ) := StarAlgebra.adjoin ℂ (Set.range (generator μ))
  have hfactor : ∀ i, (factor μ i).toAlgHom.range ≤ S.topologicalClosure.toSubalgebra := by
    intro i
    let T : StarSubalgebra ℂ C((μ i).support, ℂ) := StarAlgebra.adjoin ℂ {factorCoordinate μ i}
    have hsep : T.SeparatesPoints := fun x y hxy =>
      ⟨factorCoordinate μ i,
        ⟨factorCoordinate μ i, StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _), rfl⟩,
        fun heq => hxy (Subtype.ext (Complex.ofReal_injective heq))⟩
    have hT : T.topologicalClosure = ⊤ :=
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hsep
    have hle : T.topologicalClosure ≤ S.topologicalClosure.comap (factor μ i) := by
      refine T.topologicalClosure_minimal ?_ ?_
      · exact StarAlgebra.adjoin_le fun x hx => by
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact S.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)
      · open scoped CStarAlgebra in
        exact S.isClosed_topologicalClosure.preimage (map_continuous (factor μ i))
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ S.topologicalClosure.comap (factor μ i) := hle (hT ▸ trivial)
    exact ha
  have htop : (⊤ : Subalgebra ℂ (algebra μ)) ≤ S.topologicalClosure.toSubalgebra := by
    rw [← topologicalClosure_iSup_range_factor μ]
    exact Subalgebra.topologicalClosure_minimal (iSup_le hfactor) S.isClosed_topologicalClosure
  exact StarSubalgebra.toSubalgebra_injective (top_le_iff.mp htop)

/-- Continuous `⋆`-algebra homomorphisms out of `algebra μ` are determined by their values on the
canonical generators `generator μ i`. -/
theorem starAlgHom_ext {B : Type*} [Semiring B] [Algebra ℂ B] [Star B]
    [TopologicalSpace B] [T2Space B] {f g : algebra μ →⋆ₐ[ℂ] B}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ i, f (generator μ i) = g (generator μ i)) : f = g := by
  let E : StarSubalgebra ℂ (algebra μ) :=
    { toSubalgebra := AlgHom.equalizer f.toAlgHom g.toAlgHom
      star_mem' := fun {a} (ha : f a = g a) => by
        change f (star a) = g (star a)
        rw [map_star, map_star, ha] }
  have hle : (StarAlgebra.adjoin ℂ (Set.range (generator μ))).topologicalClosure ≤ E :=
    StarSubalgebra.topologicalClosure_minimal
      (StarAlgebra.adjoin_le <| by rintro _ ⟨i, rfl⟩; exact h i) (isClosed_eq hf hg)
  rw [topologicalClosure_starAlgebra_adjoin_range_generator μ] at hle
  exact DFunLike.ext f g fun x => hle trivial

/-! #### Concrete von Neumann algebra realization -/

/-- The concrete von Neumann algebra on `HilbertSpace μ` generated by `algebra μ`. -/
def vonNeumannAlgebra : VonNeumannAlgebra (HilbertSpace μ) :=
  VonNeumannAlgebra.adjoin (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ))

/-- `vonNeumannAlgebra μ` is the concrete von Neumann algebra generated by `algebra μ`. -/
theorem vonNeumannAlgebra_eq_adjoin :
    vonNeumannAlgebra μ =
      VonNeumannAlgebra.adjoin (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ)) := by
  rfl

/-- The canonical `⋆`-algebra inclusion from `algebra μ` into `vonNeumannAlgebra μ`. -/
def toVonNeumannAlgebra : algebra μ →⋆ₐ[ℂ] vonNeumannAlgebra μ :=
  StarSubalgebra.inclusion (S₁ := algebra μ) (S₂ := (vonNeumannAlgebra μ).toStarSubalgebra)
    (VonNeumannAlgebra.subset_adjoin _)

/-- Coercing `toVonNeumannAlgebra μ T` to a bounded operator recovers `T`. -/
@[simp] theorem coe_toVonNeumannAlgebra (T : algebra μ) :
    ((toVonNeumannAlgebra μ T : vonNeumannAlgebra μ) :
      HilbertSpace μ →L[ℂ] HilbertSpace μ) = T := by rfl

/-- The vacuum vector state restricted to `vonNeumannAlgebra μ`. -/
def vonNeumannState : vonNeumannAlgebra μ →ₚ[ℂ] ℂ :=
  (vectorState μ).comp (PositiveLinearMap.ofClass (vonNeumannAlgebra μ).toStarSubalgebra.subtype)

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

/-- The vacuum state `vonNeumannState μ` is tracial on `vonNeumannAlgebra μ`. -/
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
    exact ⟨z, z.property, rfl⟩
  have hc := continuous_wot_vectorState μ
  simpa only [vonNeumannState_apply, MulMemClass.coe_mul, hmul] using
    eqOn_closure₂' hs
      (fun a => hc.comp (continuous_const_mul a)) (fun b => hc.comp (continuous_mul_const b))
      (fun a => hc.comp (continuous_mul_const a)) (fun b => hc.comp (continuous_const_mul b))
      _ (hmem x) _ (hmem y)

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

/-- `vonNeumannAlgebra μ` is the concrete von Neumann algebra generated by the coerced canonical
generators `vonNeumannGenerator μ`. -/
theorem vonNeumannAlgebra_eq_adjoin_range_vonNeumannGenerator :
    vonNeumannAlgebra μ =
      VonNeumannAlgebra.adjoin
        (Set.range fun i => (vonNeumannGenerator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ)) := by
  let s : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ) :=
    Set.range fun i => (vonNeumannGenerator μ i : HilbertSpace μ →L[ℂ] HilbertSpace μ)
  refine le_antisymm ?_ (VonNeumannAlgebra.adjoin_le_iff.mpr ?_)
  · change VonNeumannAlgebra.adjoin (algebra μ : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ)) ≤
      VonNeumannAlgebra.adjoin s
    rw [VonNeumannAlgebra.adjoin_le_iff]
    intro T hT
    have hmem : (⟨T, hT⟩ : algebra μ) ∈
        (StarAlgebra.adjoin ℂ (Set.range (generator μ))).topologicalClosure :=
      (topologicalClosure_starAlgebra_adjoin_range_generator μ).symm ▸ trivial
    have hnorm :
        T ∈ closure (StarAlgebra.adjoin ℂ s : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ)) := by
      refine map_mem_closure continuous_subtypeVal hmem ?_
      rintro x hx
      have hle : StarAlgebra.adjoin ℂ (Set.range (generator μ)) ≤
          (StarAlgebra.adjoin ℂ s).comap (algebra μ).subtype :=
        StarAlgebra.adjoin_le <| by
          rintro _ ⟨i, rfl⟩
          exact StarAlgebra.subset_adjoin ℂ s ⟨i, rfl⟩
      exact hle hx
    have hwot : ContinuousLinearMapWOT.ofCLM T ∈
        closure (ContinuousLinearMapWOT.ofCLM ''
          (StarAlgebra.adjoin ℂ s : Set (HilbertSpace μ →L[ℂ] HilbertSpace μ))) :=
      map_mem_closure ContinuousLinearMapWOT.continuous_ofCLM hnorm fun _ hx => ⟨_, hx, rfl⟩
    rw [← VonNeumannAlgebra.image_ofCLM_adjoin_eq_closure] at hwot
    obtain ⟨U, hU, hTU⟩ := hwot
    exact ContinuousLinearMapWOT.ofCLM_injective hTU ▸ hU
  · rintro _ ⟨i, rfl⟩
    exact VonNeumannAlgebra.subset_adjoin _ (generator μ i).property

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

/-- The real spectrum of `vonNeumannGenerator μ i` equals `(μ i).support`. -/
@[simp] theorem spectrum_vonNeumannGenerator (i : ι) :
    spectrum ℝ (vonNeumannGenerator μ i) = (μ i).support :=
  Set.Subset.antisymm
    ((AlgHom.spectrum_apply_subset ((toVonNeumannAlgebra μ).toAlgHom.restrictScalars ℝ)
      (generator μ i)).trans (spectrum_generator μ i).subset)
    (law_vonNeumannGenerator μ i ▸
      PositiveLinearMap.support_law_subset_spectrum (vonNeumannState μ) (vonNeumannGenerator μ i))

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
