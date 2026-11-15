/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.FreeProduct.Reduced
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Free additive convolution of compactly supported laws

The free additive convolution `μ ⊞ ν` of two compactly supported probability measures on `ℝ` is
the law of `a + b`, where `a` and `b` are freely independent selfadjoint elements of a
C⋆-probability space with laws `μ` and `ν`. This file constructs such realizations and shows that
the resulting law does not depend on the choice, which makes `⊞` well defined, and derives its
basic algebraic properties.

Free copies of selfadjoint elements are obtained from the algebraic free product of their
C⋆-algebras: its positive free-product state has a bounded GNS representation, and the images of
the factors are free for the vacuum vector state on all bounded operators of the GNS space. A
compactly supported law is realized by the coordinate function on its support. Independence of
the realization is the fact that free families with the same one-variable moments have the same
joint distribution, together with moment determinacy of compactly supported laws.

## Main declarations

* `TauCeti.exists_isFreelyIndependentElements_law_eq_law`: selfadjoint elements of
  C⋆-probability spaces have free copies with the same laws in a single C⋆-probability space.
* `TauCeti.exists_isFreelyIndependentElements_law_eq`: every family of compactly supported
  probability measures on `ℝ` is the family of laws of free selfadjoint elements.
* `TauCeti.IsFreelyIndependentElements.law_sum_eq_law_sum`: the law of a sum of free selfadjoint
  elements depends only on the laws of the summands.
* `MeasureTheory.Measure.freeConv μ ν`: the free additive convolution `μ ⊞ ν`, defined to be `0`
  unless `μ` and `ν` are compactly supported probability measures.
* `TauCeti.IsFreelyIndependentElements.law_add`: for free selfadjoint `a` and `b` in any
  C⋆-probability space, the law of `a + b` is the free convolution of their laws.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`: commutativity
  and associativity.
* `MeasureTheory.Measure.freeConv_dirac`, `MeasureTheory.Measure.freeConv_dirac_zero`:
  convolution with `δ_a` is translation by `a`, and `δ_0` is the unit.
* `MeasureTheory.Measure.map_const_mul_freeConv`: compatibility with dilations `x ↦ r x`.
* `MeasureTheory.Measure.isProbabilityMeasure_freeConv`,
  `MeasureTheory.Measure.isCompact_support_freeConv`,
  `MeasureTheory.Measure.support_freeConv_subset_Icc`: `μ ⊞ ν` is a compactly supported
  probability measure, supported in `[a + c, b + d]` when `μ` and `ν` are supported in `[a, b]` and
  `[c, d]`.

## References

* D. V. Voiculescu, *Addition of certain non-commuting random variables*, J. Funct. Anal. 66
  (1986), 323–346.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), Chapter 3.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lectures 7 and 12.
-/

public section

noncomputable section

open MeasureTheory LinearAlgebra.FreeProduct
open scoped ComplexOrder InnerProductSpace

universe u v

namespace TauCeti

/-! ### Free copies of selfadjoint elements -/

section FreeCopies

variable {I : Type u} {A : I → Type v} [∀ i, CStarAlgebra (A i)] [∀ i, PartialOrder (A i)]
  [∀ i, StarOrderedRing (A i)]

/-- A star homomorphism from the algebraic free product into a C⋆-probability space that
intertwines the free-product state sends selfadjoint elements of the factors to free
selfadjoint elements with the same laws and no larger spectra. -/
private theorem law_starAlgHom_ι [DecidableEq I] {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (ω : ∀ i, A i →ₚ[ℂ] ℂ) (hω : ∀ i, ω i 1 = 1) (ψ : B →ₚ[ℂ] ℂ)
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B)
    (hπ : ∀ x, ψ (π x) = freeProductExpectation (fun i => (ω i).toLinearMap) hω x)
    (a : ∀ i, A i) (ha : ∀ i, IsSelfAdjoint (a i)) :
    ψ 1 = 1 ∧ IsFreelyIndependentElements ψ.toLinearMap (fun i => π (ι ℂ A i (a i))) ∧
      ∀ i, IsSelfAdjoint (π (ι ℂ A i (a i))) ∧ ψ.law (π (ι ℂ A i (a i))) = (ω i).law (a i) ∧
        spectrum ℝ (π (ι ℂ A i (a i))) ⊆ spectrum ℝ (a i) := by
  have hψπ (i : I) (x : A i) : ψ (π (ι ℂ A i x)) = ω i x := by
    rw [hπ, freeProductExpectation_ι, PositiveLinearMap.coe_toLinearMap]
  refine ⟨by simpa using hπ 1, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · exact (isFreelyIndependentElements_ι (fun i => (ω i).toLinearMap) hω a).map π.toAlgHom
      (LinearMap.ext hπ)
  · simpa only [StarAlgHom.comp_apply, ιStar_apply] using (ha i).map (π.comp (ιStar ℂ A i))
  · refine (PositiveLinearMap.law_eq_law_iff_forall_apply_pow _ _ ?_ (ha i)).2 fun n => ?_
    · simpa only [StarAlgHom.comp_apply, ιStar_apply] using (ha i).map (π.comp (ιStar ℂ A i))
    rw [← map_pow, ← map_pow, hψπ]
  · rw [← spectrum.preimage_algebraMap ℂ, ← spectrum.preimage_algebraMap ℂ (a := a i)]
    exact Set.preimage_mono (AlgHom.spectrum_apply_subset (π.toAlgHom.comp (ι ℂ A i)) (a i))

/-- The realization of `law_starAlgHom_ι` by bounded operators on an abstract Hilbert space with a
vector state. -/
private theorem exists_of_representation [DecidableEq I] {H : Type (max u v)} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ω : ∀ i, A i →ₚ[ℂ] ℂ) (hω : ∀ i, ω i 1 = 1)
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hπ : ∀ x, ⟪ξ, π x ξ⟫_ℂ = freeProductExpectation (fun i => (ω i).toLinearMap) hω x)
    (a : ∀ i, A i) (ha : ∀ i, IsSelfAdjoint (a i)) :
    ∃ (B : Type (max u v)) (_ : CStarAlgebra B) (_ : PartialOrder B) (_ : StarOrderedRing B)
      (ψ : B →ₚ[ℂ] ℂ) (c : I → B), ψ 1 = 1 ∧ IsFreelyIndependentElements ψ.toLinearMap c ∧
        ∀ i, IsSelfAdjoint (c i) ∧ ψ.law (c i) = (ω i).law (a i) ∧
          spectrum ℝ (c i) ⊆ spectrum ℝ (a i) :=
  ⟨H →L[ℂ] H, inferInstance, inferInstance, inferInstance, _, _,
    law_starAlgHom_ι ω hω (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ) π
      (fun x => by rw [ContinuousLinearMap.innerPositiveLinearMap_apply, hπ]) a ha⟩

/-- **Free copies of selfadjoint elements.** Given selfadjoint elements `a i` of C⋆-probability
spaces `(A i, ω i)`, there are freely independent selfadjoint elements `c i` of a single
C⋆-probability space with the same laws and with spectra contained in those of the `a i`.

They are the images of the `a i` in the GNS representation of the algebraic free product, with
the vacuum vector state on all bounded operators of the GNS space. -/
theorem exists_isFreelyIndependentElements_law_eq_law (ω : ∀ i, A i →ₚ[ℂ] ℂ)
    (hω : ∀ i, ω i 1 = 1) (a : ∀ i, A i) (ha : ∀ i, IsSelfAdjoint (a i)) :
    ∃ (B : Type (max u v)) (_ : CStarAlgebra B) (_ : PartialOrder B) (_ : StarOrderedRing B)
      (ψ : B →ₚ[ℂ] ℂ) (c : I → B), ψ 1 = 1 ∧ IsFreelyIndependentElements ψ.toLinearMap c ∧
        ∀ i, IsSelfAdjoint (c i) ∧ ψ.law (c i) = (ω i).law (a i) ∧
          spectrum ℝ (c i) ⊆ spectrum ℝ (a i) := by
  classical
  let φ (i : I) := StarPositiveFunctional.ofPositiveLinearMap (ω i)
  have hφ (i : I) : φ i 1 = 1 := (StarPositiveFunctional.ofPositiveLinearMap_apply _ _).trans (hω i)
  refine exists_of_representation ω hω (ReducedFreeProduct.representation φ hφ)
    (freeProductPositiveFunctional φ hφ).hilbertCyclicVector (fun x => ?_) a ha
  have h := ReducedFreeProduct.hilbertPositiveLinearMap_representation φ hφ x
  rw [StarPositiveFunctional.hilbertPositiveLinearMap_apply,
    freeProductPositiveFunctional_apply] at h
  simpa only [φ, StarPositiveFunctional.toLinearMap_ofPositiveLinearMap] using h

end FreeCopies

/-! ### Free realizations of compactly supported laws -/

/-- **Free realization of compactly supported laws.** Every family of compactly supported
probability measures on `ℝ` is the family of laws of freely independent selfadjoint elements of a
C⋆-probability space. The spectrum of each element lies in the support of its law. -/
theorem exists_isFreelyIndependentElements_law_eq {ι : Type u} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, IsCompact (μ i).support) :
    ∃ (B : Type u) (_ : CStarAlgebra B) (_ : PartialOrder B) (_ : StarOrderedRing B)
      (ψ : B →ₚ[ℂ] ℂ) (c : ι → B), ψ 1 = 1 ∧ IsFreelyIndependentElements ψ.toLinearMap c ∧
        ∀ i, IsSelfAdjoint (c i) ∧ ψ.law (c i) = μ i ∧ spectrum ℝ (c i) ⊆ (μ i).support := by
  classical
  have (i : ι) : CompactSpace (μ i).support := isCompact_iff_compactSpace.1 (hμ i)
  have hK (i : ι) : μ i (μ i).supportᶜ = 0 := Measure.measure_compl_support
  have hone (i : ι) : ContinuousMap.integralPositiveLinearMap
      ((μ i).comap ((↑) : (μ i).support → ℝ)) (1 : C((μ i).support, ℂ)) = 1 := by
    have hs : MeasurableSet (μ i).support := Measure.isClosed_support.measurableSet
    rw [ContinuousMap.integralPositiveLinearMap_one, Measure.real,
      comap_subtype_coe_apply hs, Set.image_univ, Subtype.range_coe,
      (prob_compl_eq_zero_iff hs).1 (hK i)]
    simp
  obtain ⟨B, _, _, _, ψ, c, h1, hfree, hc⟩ :=
    exists_isFreelyIndependentElements_law_eq_law
      (A := fun i => C((μ i).support, ℂ))
      (fun i => ContinuousMap.integralPositiveLinearMap ((μ i).comap ((↑) : (μ i).support → ℝ)))
      hone (fun i => (ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ)).realToRCLike ℂ)
      (fun _ => ContinuousMap.isSelfAdjoint_realToRCLike ℂ)
  refine ⟨B, _, _, _, ψ, c, h1, hfree, fun i => ⟨(hc i).1, (hc i).2.1.trans ?_,
    (hc i).2.2.trans ?_⟩⟩
  · exact PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id (hK i)
  · have h := ContinuousMap.spectrum_realToRCLike (𝕜 := ℂ)
      (ContinuousMap.restrict (μ i).support (ContinuousMap.id ℝ))
    rw [ContinuousMap.spectrum_eq_range] at h
    exact h.trans_subset (by simp)

/-- The law of a sum of freely independent selfadjoint elements depends only on the laws of the
summands: two free families with the same laws, possibly in different C⋆-probability spaces, have
sums with the same law. -/
theorem IsFreelyIndependentElements.law_sum_eq_law_sum {ι B B' : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    {ψ : B →ₚ[ℂ] ℂ} {ψ' : B' →ₚ[ℂ] ℂ} {c : ι → B} {c' : ι → B'}
    (h : IsFreelyIndependentElements ψ.toLinearMap c)
    (h' : IsFreelyIndependentElements ψ'.toLinearMap c') (hψ : ψ 1 = 1) (hψ' : ψ' 1 = 1)
    (hc : ∀ i, IsSelfAdjoint (c i)) (hc' : ∀ i, IsSelfAdjoint (c' i))
    (hlaw : ∀ i, ψ.law (c i) = ψ'.law (c' i)) (s : Finset ι) :
    ψ.law (∑ i ∈ s, c i) = ψ'.law (∑ i ∈ s, c' i) := by
  have hjoint := h.jointDistribution_eq_of_forall_pow h' hψ hψ' fun i n =>
    (PositiveLinearMap.law_eq_law_iff_forall_apply_pow ψ ψ' (hc i) (hc' i)).1 (hlaw i) n
  refine (PositiveLinearMap.law_eq_law_iff_forall_apply_pow ψ ψ'
    (isSelfAdjoint_sum s fun i _ => hc i) (isSelfAdjoint_sum s fun i _ => hc' i)).2 fun n => ?_
  simpa [jointDistribution_apply, map_sum] using
    LinearMap.congr_fun hjoint ((∑ i ∈ s, FreeAlgebra.ι ℂ i) ^ n)

/-- Two compactly supported probability measures are the laws of two free selfadjoint elements;
the law of their sum is used to define `Measure.freeConv`. -/
private theorem exists_law_add (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∃ ρ : Measure ℝ, ∃ (B : Type) (_ : CStarAlgebra B) (_ : PartialOrder B)
      (_ : StarOrderedRing B) (ψ : B →ₚ[ℂ] ℂ) (c : Fin 2 → B), ψ 1 = 1 ∧
        IsFreelyIndependentElements ψ.toLinearMap c ∧ (∀ i, IsSelfAdjoint (c i)) ∧
          ψ.law (c 0) = μ ∧ ψ.law (c 1) = ν ∧ spectrum ℝ (c 0) ⊆ μ.support ∧
            spectrum ℝ (c 1) ⊆ ν.support ∧ ψ.law (c 0 + c 1) = ρ := by
  have : ∀ i, IsProbabilityMeasure (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  obtain ⟨B, _, _, _, ψ, c, h1, hfree, hc⟩ :=
    exists_isFreelyIndependentElements_law_eq ![μ, ν] (Fin.forall_fin_two.2 ⟨hμ, hν⟩)
  exact ⟨_, B, _, _, _, ψ, c, h1, hfree, fun i => (hc i).1, (hc 0).2.1, (hc 1).2.1,
    (hc 0).2.2, (hc 1).2.2, rfl⟩

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

open Classical in
/-- The **free additive convolution** `μ ⊞ ν` of two compactly supported probability measures on
`ℝ`: the law of `a + b` for freely independent selfadjoint elements `a`, `b` of a C⋆-probability
space with laws `μ` and `ν`. It does not depend on the realization
(`TauCeti.IsFreelyIndependentElements.law_add`). By convention it is `0` unless both measures are
compactly supported probability measures. -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  if h : (IsProbabilityMeasure μ ∧ IsCompact μ.support) ∧
      (IsProbabilityMeasure ν ∧ IsCompact ν.support) then
    haveI := h.1.1
    haveI := h.2.1
    (exists_law_add μ ν h.1.2 h.2.2).choose
  else 0

/-- Free convolution with a measure that is not a compactly supported probability measure is `0`
by convention. -/
theorem freeConv_of_not_left {μ : Measure ℝ} (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support))
    (ν : Measure ℝ) : μ.freeConv ν = 0 :=
  dite_eq_right fun h' => h h'.1

/-- Free convolution with a measure that is not a compactly supported probability measure is `0`
by convention. -/
theorem freeConv_of_not_right (μ : Measure ℝ) {ν : Measure ℝ}
    (h : ¬(IsProbabilityMeasure ν ∧ IsCompact ν.support)) : μ.freeConv ν = 0 :=
  dite_eq_right fun h' => h h'.2

/-- The zero measure is not a probability measure, so its free convolutions vanish. -/
@[simp]
theorem zero_freeConv (ν : Measure ℝ) : (0 : Measure ℝ).freeConv ν = 0 :=
  freeConv_of_not_left (fun h => haveI := h.1; IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl) ν

/-- The zero measure is not a probability measure, so its free convolutions vanish. -/
@[simp]
theorem freeConv_zero (μ : Measure ℝ) : μ.freeConv 0 = 0 :=
  freeConv_of_not_right μ (fun h => haveI := h.1; IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl)

end MeasureTheory.Measure

namespace TauCeti

/-- The free convolution of two compactly supported probability measures is the law of the sum of
two free selfadjoint elements with these laws, with spectra in their supports. -/
private theorem exists_law_add_eq_freeConv (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : PartialOrder B)
      (_ : StarOrderedRing B) (ψ : B →ₚ[ℂ] ℂ) (c : Fin 2 → B), ψ 1 = 1 ∧
        IsFreelyIndependentElements ψ.toLinearMap c ∧ (∀ i, IsSelfAdjoint (c i)) ∧
          ψ.law (c 0) = μ ∧ ψ.law (c 1) = ν ∧ spectrum ℝ (c 0) ⊆ μ.support ∧
            spectrum ℝ (c 1) ⊆ ν.support ∧ ψ.law (c 0 + c 1) = μ.freeConv ν := by
  rw [Measure.freeConv, dite_eq_left ⟨⟨‹_›, hμ⟩, ⟨‹_›, hν⟩⟩]
  exact (exists_law_add μ ν hμ hν).choose_spec

/-- **Free convolution is the law of free sums.** If `c i` and `c j`, for `i ≠ j`, are selfadjoint
members of a freely independent family in a C⋆-probability space, the law of `c i + c j` is the
free convolution of the laws of `c i` and `c j`. -/
theorem IsFreelyIndependentElements.law_add {ι B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {ψ : B →ₚ[ℂ] ℂ} {c : ι → B}
    (h : IsFreelyIndependentElements ψ.toLinearMap c) (hψ : ψ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hi : IsSelfAdjoint (c i)) (hj : IsSelfAdjoint (c j)) :
    ψ.law (c i + c j) = (ψ.law (c i)).freeConv (ψ.law (c j)) := by
  have := ψ.isProbabilityMeasure_law hψ hi
  have := ψ.isProbabilityMeasure_law hψ hj
  obtain ⟨B', _, _, _, ψ', c', hψ', h', hc', h0, h1, -, -, hconv⟩ :=
    exists_law_add_eq_freeConv _ _ (ψ.isCompact_support_law (c i))
      (ψ.isCompact_support_law (c j))
  have he : Function.Injective ![i, j] := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [hij.symm]
  rw [← hconv]
  have hsum := (h.comp he).law_sum_eq_law_sum h' hψ hψ'
    (fun k => by fin_cases k <;> simpa) hc' (fun k => by fin_cases k <;> simp [h0, h1])
    Finset.univ
  simpa [Fin.sum_univ_two] using hsum

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

variable {μ ν : Measure ℝ}

/-- The free convolution of two compactly supported probability measures is a probability
measure. -/
theorem isProbabilityMeasure_freeConv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ.freeConv ν) := by
  obtain ⟨B, _, _, _, ψ, c, hψ, -, hc, -, -, -, -, hconv⟩ := exists_law_add_eq_freeConv μ ν hμ hν
  exact hconv ▸ ψ.isProbabilityMeasure_law hψ ((hc 0).add (hc 1))

/-- The free convolution of two measures has compact support. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ.freeConv ν).support := by
  by_cases h : (IsProbabilityMeasure μ ∧ IsCompact μ.support) ∧
      (IsProbabilityMeasure ν ∧ IsCompact ν.support)
  · obtain ⟨⟨_, hμ⟩, ⟨_, hν⟩⟩ := h
    obtain ⟨B, _, _, _, ψ, c, -, -, -, -, -, -, -, hconv⟩ := exists_law_add_eq_freeConv μ ν hμ hν
    exact hconv ▸ ψ.isCompact_support_law _
  · rw [freeConv, dite_eq_right h, support_zero]
    exact isCompact_empty

/-- **Support bound for free convolution.** If `μ` is supported in `[a, b]` and `ν` in `[c, d]`,
then `μ ⊞ ν` is supported in `[a + c, b + d]`. -/
theorem support_freeConv_subset_Icc {a b c d : ℝ} (hμ : μ.support ⊆ Set.Icc a b)
    (hν : ν.support ⊆ Set.Icc c d) : (μ.freeConv ν).support ⊆ Set.Icc (a + c) (b + d) := by
  by_cases h : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν
  · obtain ⟨_, _⟩ := h
    obtain ⟨B, _, _, _, ψ, x, -, -, hx, -, -, hx0, hx1, hconv⟩ := exists_law_add_eq_freeConv μ ν
      (isCompact_Icc.of_isClosed_subset isClosed_support hμ)
      (isCompact_Icc.of_isClosed_subset isClosed_support hν)
    have hle (k : Fin 2) {l u : ℝ} (hk : spectrum ℝ (x k) ⊆ Set.Icc l u) :
        algebraMap ℝ B l ≤ x k ∧ x k ≤ algebraMap ℝ B u :=
      ⟨(algebraMap_le_iff_le_spectrum (hx k)).2 fun y hy => (hk hy).1,
        (le_algebraMap_iff_spectrum_le (hx k)).2 fun y hy => (hk hy).2⟩
    obtain ⟨h0l, h0u⟩ := hle 0 (hx0.trans hμ)
    obtain ⟨h1l, h1u⟩ := hle 1 (hx1.trans hν)
    have hsa := (hx 0).add (hx 1)
    refine hconv ▸ (ψ.support_law_subset_spectrum _).trans fun y hy => ⟨?_, ?_⟩
    · exact (algebraMap_le_iff_le_spectrum hsa).1
        (by rw [map_add]; exact add_le_add h0l h1l) y hy
    · exact (le_algebraMap_iff_spectrum_le hsa).1
        (by rw [map_add]; exact add_le_add h0u h1u) y hy
  · rw [not_and_or] at h
    rcases h with h | h
    · rw [freeConv_of_not_left (fun h' => h h'.1), support_zero]
      exact Set.empty_subset _
    · rw [freeConv_of_not_right μ (fun h' => h h'.1), support_zero]
      exact Set.empty_subset _

/-- **Free convolution is commutative.** -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ.freeConv ν = ν.freeConv μ := by
  by_cases h : (IsProbabilityMeasure μ ∧ IsCompact μ.support) ∧
      (IsProbabilityMeasure ν ∧ IsCompact ν.support)
  · obtain ⟨⟨_, hμ⟩, ⟨_, hν⟩⟩ := h
    obtain ⟨B, _, _, _, ψ, x, hψ, hfree, hx, h0, h1, -, -, hconv⟩ :=
      exists_law_add_eq_freeConv μ ν hμ hν
    rw [← hconv, add_comm, hfree.law_add hψ (by decide) (hx 1) (hx 0), h0, h1]
  · rw [freeConv, dite_eq_right h, freeConv, dite_eq_right fun h' => h ⟨h'.2, h'.1⟩]

/-- Convolving with a point mass translates: `μ ⊞ δ_a` is the pushforward of `μ` along
`x ↦ x + a`. -/
theorem freeConv_dirac [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (a : ℝ) :
    μ.freeConv (dirac a) = μ.map (· + a) := by
  have hδ : (dirac a).support = {a} := by rw [Measure.support_dirac, closure_singleton]
  obtain ⟨B, _, _, _, ψ, x, -, -, hx, h0, -, -, hx1, hconv⟩ := exists_law_add_eq_freeConv μ
    (dirac a) hμ (hδ ▸ isCompact_singleton)
  have hx1a : x 1 = algebraMap ℝ B a :=
    CFC.eq_algebraMap_of_spectrum_subset_singleton (x 1) a (hδ ▸ hx1) (hx 1)
  rw [← hconv, hx1a, ← one_smul ℝ (x 0), ψ.law_smul_add_algebraMap (hx 0), h0]
  simp

/-- Convolving with a point mass translates: `δ_a ⊞ μ` is the pushforward of `μ` along
`x ↦ x + a`. -/
theorem dirac_freeConv [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (a : ℝ) :
    (dirac a).freeConv μ = μ.map (· + a) := by
  rw [freeConv_comm, freeConv_dirac hμ]

/-- The point mass at `0` is the unit of free convolution. -/
@[simp]
theorem freeConv_dirac_zero [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    μ.freeConv (dirac 0) = μ := by
  simp [freeConv_dirac hμ]

/-- The point mass at `0` is the unit of free convolution. -/
@[simp]
theorem dirac_zero_freeConv [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    (dirac 0).freeConv μ = μ := by
  rw [freeConv_comm, freeConv_dirac_zero hμ]

/-- **Free convolution commutes with dilations**: the pushforward of `μ ⊞ ν` along `x ↦ r x` is
the free convolution of the pushforwards of `μ` and `ν`. -/
theorem map_const_mul_freeConv (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (r : ℝ) :
    (μ.freeConv ν).map (r * ·) = (μ.map (r * ·)).freeConv (ν.map (r * ·)) := by
  -- Pushforward preserves the total mass, so both sides vanish unless both are probabilities.
  have hprob {ρ : Measure ℝ} (h : IsProbabilityMeasure (ρ.map (r * ·))) :
      IsProbabilityMeasure ρ :=
    ⟨by simpa [map_apply (measurable_const_mul r) MeasurableSet.univ] using h.measure_univ⟩
  by_cases hμp : IsProbabilityMeasure μ
  swap
  · rw [freeConv_of_not_left (fun h => hμp h.1), Measure.map_zero,
      freeConv_of_not_left (fun h => hμp (hprob h.1))]
  by_cases hνp : IsProbabilityMeasure ν
  swap
  · rw [freeConv_of_not_right μ (fun h => hνp h.1), Measure.map_zero,
      freeConv_of_not_right _ (fun h => hνp (hprob h.1))]
  obtain ⟨B, _, _, _, ψ, x, hψ, hfree, hx, h0, h1, -, -, hconv⟩ :=
    exists_law_add_eq_freeConv μ ν hμ hν
  have hlaw (k : Fin 2) : ψ.law (r • x k) = (ψ.law (x k)).map (r * ·) := by
    simpa using ψ.law_smul_add_algebraMap (hx k) r 0
  have hfree' : IsFreelyIndependentElements ψ.toLinearMap (fun k => r • x k) :=
    hfree.of_mem_adjoin_image_fiber (by simpa using hψ) id fun k => by
      simpa using Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton ℂ (x k)) (r : ℂ)
  have hsum := hfree'.law_add (by simpa using hψ) (i := 0) (j := 1) (by decide)
    ((IsSelfAdjoint.all r).smul (hx 0)) ((IsSelfAdjoint.all r).smul (hx 1))
  rw [← smul_add r (x 0) (x 1), hlaw 0, hlaw 1, h0, h1] at hsum
  rw [← hsum, ← hconv]
  simpa using (ψ.law_smul_add_algebraMap ((hx 0).add (hx 1)) r 0).symm

/-- **Free convolution is associative.** -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) :
    (μ.freeConv ν).freeConv ρ = μ.freeConv (ν.freeConv ρ) := by
  by_cases hμ : IsProbabilityMeasure μ ∧ IsCompact μ.support
  swap
  · rw [freeConv_of_not_left hμ, zero_freeConv, freeConv_of_not_left hμ]
  by_cases hν : IsProbabilityMeasure ν ∧ IsCompact ν.support
  swap
  · rw [freeConv_of_not_left hν, freeConv_of_not_right μ hν, zero_freeConv, freeConv_zero]
  by_cases hρ : IsProbabilityMeasure ρ ∧ IsCompact ρ.support
  swap
  · rw [freeConv_of_not_right _ hρ, freeConv_of_not_right ν hρ, freeConv_zero]
  obtain ⟨_, hμ⟩ := hμ
  obtain ⟨_, hν⟩ := hν
  obtain ⟨_, hρ⟩ := hρ
  have : ∀ i, IsProbabilityMeasure (![μ, ν, ρ] i) := by
    intro i
    fin_cases i <;> simpa
  obtain ⟨B, _, _, _, ψ, x, hψ, hfree, hx⟩ :=
    exists_isFreelyIndependentElements_law_eq ![μ, ν, ρ] (by intro i; fin_cases i <;> simpa)
  have hmem (i : Fin 3) {k : Fin 2} (g : Fin 3 → Fin 2) (hi : g i = k) :
      x i ∈ Algebra.adjoin ℂ (x '' (g ⁻¹' {k})) :=
    Algebra.subset_adjoin (Set.mem_image_of_mem x hi)
  have hL : IsFreelyIndependentElements ψ.toLinearMap ![x 0 + x 1, x 2] :=
    hfree.of_mem_adjoin_image_fiber hψ ![0, 0, 1] fun k => by
      fin_cases k
      · exact Subalgebra.add_mem _ (hmem 0 _ rfl) (hmem 1 _ rfl)
      · exact hmem 2 _ rfl
  have hR : IsFreelyIndependentElements ψ.toLinearMap ![x 0, x 1 + x 2] :=
    hfree.of_mem_adjoin_image_fiber hψ ![0, 1, 1] fun k => by
      fin_cases k
      · exact hmem 0 _ rfl
      · exact Subalgebra.add_mem _ (hmem 1 _ rfl) (hmem 2 _ rfl)
  have h01 := hfree.law_add hψ (i := 0) (j := 1) (by decide) (hx 0).1 (hx 1).1
  have h12 := hfree.law_add hψ (i := 1) (j := 2) (by decide) (hx 1).1 (hx 2).1
  have hLsum := hL.law_add hψ (i := 0) (j := 1) (by decide) ((hx 0).1.add (hx 1).1) (hx 2).1
  have hRsum := hR.law_add hψ (i := 0) (j := 1) (by decide) (hx 0).1 ((hx 1).1.add (hx 2).1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLsum hRsum
  rw [h01, (hx 0).2.1, (hx 1).2.1, (hx 2).2.1] at hLsum
  rw [h12, (hx 0).2.1, (hx 1).2.1, (hx 2).2.1, ← add_assoc, hLsum] at hRsum
  simpa using hRsum

end MeasureTheory.Measure
