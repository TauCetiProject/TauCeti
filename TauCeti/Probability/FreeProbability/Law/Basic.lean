/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# The law of a selfadjoint element in a C⋆-probability space

Let `A` be a unital C⋆-algebra, `φ : A →ₚ[ℂ] ℂ` a positive linear functional and `a ∈ A`
selfadjoint. The functional `f ↦ φ (f(a))` on real continuous functions on `spectrum ℝ a` is
positive, because the continuous functional calculus sends nonnegative functions to positive
elements. By the Riesz–Markov–Kakutani theorem it is integration against a unique finite Borel
measure. Pushed forward to `ℝ`, this is the **law** (or distribution) `μ_a` of `a`:

`φ (f(a)) = ∫ f dμ_a` for every `f` continuous on `spectrum ℝ a`.

It is concentrated on the compact set `spectrum ℝ a`, has total mass `φ 1`, so it is a probability
measure when `φ` is a state, and its moments are the moments `φ (a ^ n)` of `a`. The law turns
statements about a single selfadjoint noncommutative random variable into statements about a
compactly supported measure on the line, which is how free convolutions and free limit theorems
are formulated analytically.

Conversely, the law is determined by the moments: a compactly supported finite measure whose
moments are the `φ (a ^ n)` is `μ_a`, so two selfadjoint elements, possibly in different
C⋆-algebras, have the same law exactly when they have the same moments. And every compactly
supported finite measure `μ` on `ℝ` is a law, realized in a commutative C⋆-algebra: if `μ` is
concentrated on the compact set `K`, it is the law of the coordinate `x ↦ x` in `C(K, ℂ)` with
respect to integration against `μ` on `K`, which is a state when `μ` is a probability measure. So
the laws of selfadjoint elements with respect to states are exactly the compactly supported
probability measures on `ℝ`.

## Main declarations

* `PositiveLinearMap.law φ a`: the law of `a` with respect to `φ`, a finite measure on `ℝ`; it is
  the zero measure when `a` is not selfadjoint.
* `PositiveLinearMap.ofReal_integral_law`: `∫ f dμ_a = φ (cfc f a)`.
* `PositiveLinearMap.eq_law_iff`: `μ_a` is the only finite measure on `ℝ` with this property for
  continuous `f`.
* `PositiveLinearMap.law_compl_spectrum`: `μ_a` is concentrated on `spectrum ℝ a`.
* `PositiveLinearMap.integrable_law`: every `f` continuous on `spectrum ℝ a` is `μ_a`-integrable.
* `PositiveLinearMap.isProbabilityMeasure_law`: `μ_a` is a probability measure when `φ 1 = 1`.
* `PositiveLinearMap.ofReal_integral_pow_law`: the moments of `μ_a` are `φ (a ^ n)`.
* `PositiveLinearMap.law_cfc`, `PositiveLinearMap.law_aeval`,
  `PositiveLinearMap.law_smul_add_algebraMap`: the law of `g(a)`, of `p(a)` for a real
  polynomial `p`, and of `r • a + c` is the pushforward of `μ_a` along `g`, `p` and `x ↦ r x + c`.
* `PositiveLinearMap.eq_law_iff_forall_integral_pow`: a compactly supported finite measure is
  `μ_a` exactly when its moments are the `φ (a ^ n)`.
* `PositiveLinearMap.law_eq_law_iff_forall_apply_pow`: two selfadjoint elements have the same law
  exactly when they have the same moments.
* `PositiveLinearMap.law_integralPositiveLinearMap_realToRCLike`: in `C(X, ℂ)` for a compact
  space `X`, the law of a real function `g` with respect to integration against `ν` is the
  pushforward of `ν` along `g`.
* `PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id`: every finite measure on
  `ℝ` concentrated on a compact set `K` is the law of the coordinate `x ↦ x` in `C(K, ℂ)`.

## Implementation notes

The construction follows `ContinuousLinearMap.diagMeasure` in
`TauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`, which applies the same
Riesz–Markov–Kakutani step to a vector state of a normal operator on a Hilbert space.

Moment determinacy is `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support`, the
Stone–Weierstrass argument on a compact set containing both supports. The realization in
`C(X, ℂ)` is identified with the pushforward through its moments rather than through the
continuous functional calculus, so it uses only powers of the element.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lecture 3.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §1.1.
-/

public section

noncomputable section

open MeasureTheory Polynomial
open scoped ComplexOrder CompactlySupported

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- The positive functional `g ↦ Re φ (g(a))` on real continuous functions on the spectrum of a
selfadjoint element `a`, whose Riesz–Markov–Kakutani measure is the law of `a` on the spectrum. -/
private def lawFunctional (ha : IsSelfAdjoint a) : C_c(spectrum ℝ a, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := (φ (cfcHom ha g.toContinuousMap)).re
      -- `toContinuousMap` commutes with `+` and `•` by definition, but `rw` matches
      -- syntactically: restating the coercion lets `map_add` and `map_smul` of `cfcHom` fire.
      map_add' g h := by
        rw [show (g + h).toContinuousMap = g.toContinuousMap + h.toContinuousMap from rfl,
          map_add, map_add, Complex.add_re]
      map_smul' c g := by
        rw [show (c • g).toContinuousMap = c • g.toContinuousMap from rfl, map_smul,
          ← Complex.coe_smul, map_smul]
        simp }
    fun g hg => by
      have hT : 0 ≤ cfcHom ha g.toContinuousMap := by
        rw [cfcHom_nonneg_iff]
        intro x
        simpa using hg x
      exact (Complex.nonneg_iff.mp (φ.map_nonneg hT)).1

/-- The law of a selfadjoint element on its spectrum, before pushing forward to `ℝ`. -/
private def spectrumLaw (ha : IsSelfAdjoint a) : Measure (spectrum ℝ a) :=
  RealRMK.rieszMeasure (lawFunctional φ ha)

open scoped Classical in
/-- The **law** `μ_a` of an element `a` of a C⋆-algebra with respect to a positive linear
functional `φ`: for selfadjoint `a`, the finite Borel measure on `ℝ`, concentrated on
`spectrum ℝ a` (`law_compl_spectrum`), with `∫ f dμ_a = φ (cfc f a)` for every `f` continuous on
the spectrum (`ofReal_integral_law`), and characterized by this property (`eq_law_iff`). For `a`
not selfadjoint it is the zero measure (`law_of_not_isSelfAdjoint`). -/
def law (φ : A →ₚ[ℂ] ℂ) (a : A) : Measure ℝ :=
  if ha : IsSelfAdjoint a then (spectrumLaw φ ha).map Subtype.val else 0

private lemma law_of_isSelfAdjoint (ha : IsSelfAdjoint a) :
    law φ a = (spectrumLaw φ ha).map Subtype.val := by
  simp [law, ha]

/-- The law of an element that is not selfadjoint is, by convention, the zero measure. -/
@[simp]
theorem law_of_not_isSelfAdjoint (ha : ¬IsSelfAdjoint a) : law φ a = 0 := by
  simp [law, ha]

/-- The law of any element is a finite measure. -/
instance (a : A) : IsFiniteMeasure (law φ a) := by
  by_cases ha : IsSelfAdjoint a
  · rw [law_of_isSelfAdjoint φ ha]
    unfold spectrumLaw
    infer_instance
  · rw [law_of_not_isSelfAdjoint φ ha]
    infer_instance

/-- The law `μ_a` is concentrated on the spectrum of `a`. -/
@[simp]
theorem law_compl_spectrum (a : A) : law φ a (spectrum ℝ a)ᶜ = 0 := by
  by_cases ha : IsSelfAdjoint a
  · rw [law_of_isSelfAdjoint φ ha,
      Measure.map_apply measurable_subtype_coe (spectrum.isClosed a).measurableSet.compl]
    simp
  · simp [law_of_not_isSelfAdjoint φ ha]

/-- The law `μ_a` is concentrated on the spectrum of `a`, as a restriction. -/
@[simp]
theorem restrict_spectrum_law (a : A) : (law φ a).restrict (spectrum ℝ a) = law φ a :=
  Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (law_compl_spectrum φ a))

/-- Every function continuous on the spectrum of `a` is integrable against the law `μ_a`. -/
theorem integrable_law (a : A) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac) : Integrable f (law φ a) := by
  rw [← restrict_spectrum_law]
  exact hf.integrableOn_compact (ContinuousFunctionalCalculus.isCompact_spectrum a)

/-- Every real polynomial is integrable against the law `μ_a`. -/
theorem integrable_eval_law (a : A) (p : ℝ[X]) : Integrable (fun x ↦ p.eval x) (law φ a) :=
  integrable_law φ a (fun x ↦ p.eval x)

/-- Every power `x ^ n` is integrable against the law `μ_a`. -/
theorem integrable_pow_law (a : A) (n : ℕ) : Integrable (· ^ n) (law φ a) :=
  integrable_law φ a (· ^ n)

/-- The defining identity of the law on the spectrum. -/
private lemma ofReal_integral_spectrumLaw (ha : IsSelfAdjoint a) (g : C(spectrum ℝ a, ℝ)) :
    ((∫ x, g x ∂(spectrumLaw φ ha) : ℝ) : ℂ) = φ (cfcHom ha g) := by
  have h := RealRMK.integral_rieszMeasure (lawFunctional φ ha) ⟨g, .of_compactSpace _⟩
  rw [CompactlySupportedContinuousMap.coe_mk] at h
  rw [spectrumLaw, h]
  -- A real symbol gives a selfadjoint element, on which a positive functional is real.
  have hsa : IsSelfAdjoint (φ (cfcHom ha g)) :=
    ((IsSelfAdjoint.all g).map (cfcHom ha)).map' φ
  exact Complex.conj_eq_iff_re.mp hsa.star_eq

/-- Integration against the law `μ_a` of a selfadjoint element `a` computes `φ` on the continuous
functional calculus: `∫ f dμ_a = φ (f(a))` for `f` continuous on the spectrum of `a`. -/
theorem ofReal_integral_law (ha : IsSelfAdjoint a) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac) :
    ((∫ x, f x ∂(law φ a) : ℝ) : ℂ) = φ (cfc f a) := by
  rw [law_of_isSelfAdjoint φ ha,
    (MeasurableEmbedding.subtype_coe (spectrum.isClosed a).measurableSet).integral_map,
    cfc_apply f a]
  exact ofReal_integral_spectrumLaw φ ha ⟨_, hf.domRestrict⟩

variable {φ} in
/-- The law `μ_a` of a selfadjoint element `a` is the unique finite measure on `ℝ` that
represents `f ↦ φ (f(a))` on continuous functions. -/
theorem eq_law_iff (ha : IsSelfAdjoint a) {μ : Measure ℝ} [IsFiniteMeasure μ] :
    μ = law φ a ↔
      ∀ f : ℝ → ℝ, Continuous f → ((∫ x, f x ∂μ : ℝ) : ℂ) = φ (cfc f a) := by
  refine ⟨fun h f hf ↦ h ▸ ofReal_integral_law φ ha f, fun h ↦ ?_⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ Complex.ofReal_injective ?_
  rw [h g g.continuous, ofReal_integral_law φ ha g]

/-- The total mass of the law of a selfadjoint element is `φ 1`. -/
theorem ofReal_law_real_univ (ha : IsSelfAdjoint a) :
    (((law φ a).real Set.univ : ℝ) : ℂ) = φ 1 := by
  simpa [cfc_const_one ℝ a] using ofReal_integral_law φ ha (fun _ ↦ 1)

/-- The law of a selfadjoint element with respect to a state is a probability measure. -/
theorem isProbabilityMeasure_law (hφ : φ 1 = 1) (ha : IsSelfAdjoint a) :
    IsProbabilityMeasure (law φ a) := by
  refine ⟨?_⟩
  have h := ofReal_law_real_univ φ ha
  rw [hφ, Complex.ofReal_eq_one] at h
  rw [← ofReal_measureReal, h, ENNReal.ofReal_one]

/-- The polynomial moments of the law of a selfadjoint element `a` are the corresponding values
of `φ`: `∫ p dμ_a = φ (p(a))`. -/
theorem ofReal_integral_eval_law (ha : IsSelfAdjoint a) (p : ℝ[X]) :
    ((∫ x, p.eval x ∂(law φ a) : ℝ) : ℂ) = φ (aeval a p) := by
  rw [ofReal_integral_law φ ha (fun x ↦ p.eval x), cfc_polynomial p a]

/-- The moments of the law of a selfadjoint element `a` are the moments of `a`:
`∫ x ^ n dμ_a = φ (a ^ n)`. -/
theorem ofReal_integral_pow_law (ha : IsSelfAdjoint a) (n : ℕ) :
    ((∫ x, x ^ n ∂(law φ a) : ℝ) : ℂ) = φ (a ^ n) := by
  rw [ofReal_integral_law φ ha (· ^ n), cfc_pow_id a n]

/-- The law of `g(a)`, for `a` selfadjoint and `g` continuous on its spectrum, is the
pushforward of the law of `a` along `g`. -/
theorem law_cfc (ha : IsSelfAdjoint a) (g : ℝ → ℝ)
    (hg : ContinuousOn g (spectrum ℝ a) := by cfc_cont_tac) :
    law φ (cfc g a) = (law φ a).map g := by
  have hgm : AEMeasurable g (law φ a) := by
    rw [← restrict_spectrum_law]
    exact hg.aemeasurable (spectrum.isClosed a).measurableSet
  refine ((eq_law_iff (cfc_predicate g a)).2 fun f hf ↦ ?_).symm
  rw [integral_map hgm hf.aestronglyMeasurable, ← cfc_comp f g a]
  exact ofReal_integral_law φ ha (f ∘ g) (hf.comp_continuousOn hg)

/-- The law of `p(a)`, for `a` selfadjoint and `p` a real polynomial, is the pushforward of the
law of `a` along `p`. -/
theorem law_aeval (ha : IsSelfAdjoint a) (p : ℝ[X]) :
    law φ (aeval a p) = (law φ a).map (fun x ↦ p.eval x) := by
  rw [← cfc_polynomial p a, law_cfc φ ha (fun x ↦ p.eval x)]

/-- The law of the affine image `r • a + c` of a selfadjoint element `a` is the pushforward of
the law of `a` along `x ↦ r * x + c`. -/
theorem law_smul_add_algebraMap (ha : IsSelfAdjoint a) (r c : ℝ) :
    law φ (r • a + algebraMap ℝ A c) = (law φ a).map (fun x ↦ r * x + c) := by
  rw [← cfc_const_mul_id r a, ← cfc_add_const c _ a, law_cfc φ ha (fun x ↦ r * x + c)]

/-! ### Moment determinacy -/

variable {φ} in
/-- **Moment determinacy of the law.** A finite measure on `ℝ` concentrated on a compact set is
the law `μ_a` of a selfadjoint element `a` exactly when its moments are the moments of `a`:
`∫ x ^ n dμ = φ (a ^ n)` for every `n`.

The support hypothesis cannot be dropped: the moments are Bochner integrals, which are `0` for
non-integrable integrands, so a heavy-tailed `μ` can match the moments of `a` without being
`μ_a`. -/
theorem eq_law_iff_forall_integral_pow (ha : IsSelfAdjoint a) {μ : Measure ℝ} [IsFiniteMeasure μ]
    {K : Set ℝ} (hK : IsCompact K) (hμ : μ Kᶜ = 0) :
    μ = law φ a ↔ ∀ n : ℕ, ((∫ x, x ^ n ∂μ : ℝ) : ℂ) = φ (a ^ n) := by
  refine ⟨fun h n ↦ h ▸ ofReal_integral_pow_law φ ha n, fun h ↦ ?_⟩
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support
    (hK.union (ContinuousFunctionalCalculus.isCompact_spectrum a)) ?_ ?_ fun n ↦ ?_
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_left) hμ
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_right)
      (law_compl_spectrum φ a)
  · exact Complex.ofReal_injective ((h n).trans (ofReal_integral_pow_law φ ha n).symm)

/-- Two selfadjoint elements, possibly in different C⋆-algebras and with respect to different
positive functionals, have the same law exactly when they have the same moments:
`μ_a = μ_b ↔ ∀ n, φ (a ^ n) = ψ (b ^ n)`. -/
theorem law_eq_law_iff_forall_apply_pow {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (ψ : B →ₚ[ℂ] ℂ) {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    law φ a = law ψ b ↔ ∀ n : ℕ, φ (a ^ n) = ψ (b ^ n) := by
  rw [eq_law_iff_forall_integral_pow hb (ContinuousFunctionalCalculus.isCompact_spectrum a)
    (law_compl_spectrum φ a)]
  simp_rw [ofReal_integral_pow_law φ ha]

/-! ### Realization of compactly supported measures -/

section Realization

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- In the commutative C⋆-algebra `C(X, ℂ)` of a compact space `X`, the law of a real continuous
function `g` with respect to integration against a finite measure `ν` is the pushforward `ν ∘ g⁻¹`
of `ν` along `g`. -/
theorem law_integralPositiveLinearMap_realToRCLike (ν : Measure X) [IsFiniteMeasure ν]
    (g : C(X, ℝ)) :
    law (ContinuousMap.integralPositiveLinearMap ν) (g.realToRCLike ℂ) = ν.map g := by
  have hK := isCompact_range g.continuous
  refine ((eq_law_iff_forall_integral_pow (ContinuousMap.isSelfAdjoint_realToRCLike ℂ) hK ?_).2
    fun n ↦ ?_).symm
  · rw [Measure.map_apply g.continuous.measurable hK.isClosed.measurableSet.compl]
    simp
  · rw [integral_map g.continuous.aemeasurable (by fun_prop),
      ContinuousMap.integralPositiveLinearMap_apply, ← integral_complex_ofReal]
    simp

/-- **Realization of compactly supported laws.** A finite measure `μ` on `ℝ` concentrated on a
compact set `K` is the law of the coordinate function `x ↦ x` in the commutative C⋆-algebra
`C(K, ℂ)`, with respect to integration against `μ` on `K`. This functional is a state when `μ` is
a probability measure (`ContinuousMap.integralPositiveLinearMap_one`). -/
theorem law_integralPositiveLinearMap_comap_restrict_id {K : Set ℝ} [CompactSpace K]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ Kᶜ = 0) :
    law (ContinuousMap.integralPositiveLinearMap (μ.comap ((↑) : K → ℝ)))
      ((ContinuousMap.restrict K (ContinuousMap.id ℝ)).realToRCLike ℂ) = μ := by
  have hK : IsCompact K := isCompact_iff_compactSpace.2 ‹_›
  rw [law_integralPositiveLinearMap_realToRCLike]
  exact (map_comap_subtype_coe hK.measurableSet μ).trans
    (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ))

end Realization

end PositiveLinearMap
