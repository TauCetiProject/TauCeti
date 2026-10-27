/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# The Eisenstein region of coefficient space

Serre's mass formula is proved by integrating over the space of Eisenstein polynomials. A monic
polynomial of degree `n` over a nonarchimedean local field `K` is identified with its coefficient
vector `a : Fin n → K`, through `TauCeti.Polynomial.monicOfCoeff a = X ^ n + ∑ i, a i * X ^ i`,
and the *Eisenstein region* `TauCeti.eisensteinSet K n` is the set of coefficient vectors all of
whose entries lie in the open unit ball and whose polynomial has constant term of valuation at least
that of every element of valuation below `1`. For `0 < n` the constant term is the entry `a 0`, so
this says it has the valuation of a uniformizer; for `n = 0` the constant term is `1` and the region
is all of the one-point space `Fin 0 → K`. Whenever `𝒪[K]` is a discrete valuation ring, as for a
nonarchimedean local field, `TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt` identifies these
with the coefficient vectors of the polynomials over `𝒪[K]` that are Eisenstein at `𝓂[K]` (for
`n = 0`, only the constant polynomial `1`, which Mathlib's predicate counts as Eisenstein).

The coefficient space `ι → K` carries the additive Haar measure normalized so that the integer box
`TauCeti.integerBox K ι = 𝒪[K] ^ ι` has volume `1`. For such a measure, writing `q` for the
cardinality of the residue field, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume
`q ^ (-∑ i, e i)`, since it is the image of the integer box under the diagonal matrix with entries
`ϖ ^ e i` for a uniformizer `ϖ`. For `0 < n` the Eisenstein region is the difference of two such
boxes (`TauCeti.eisensteinSet_eq_sdiff`), so its volume is `q ^ (-n) (1 - q⁻¹)`
(`TauCeti.measure_eisensteinSet`).

The measure statements assume only left invariance of the measure and the normalization; no
product structure on the measure is used.

## Main definitions

* `TauCeti.eisensteinSet K n`: the Eisenstein region in `Fin n → K`.

## Main results

* `TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt`: a coefficient vector lies in the
  Eisenstein region exactly when it is the coefficient vector of a polynomial over `𝒪[K]` that is
  Eisenstein at `𝓂[K]`.
* `TauCeti.eisensteinSet_eq_sdiff`: for `0 < n`, the Eisenstein region is the box `𝓂[K] ^ n` minus
  the box whose constant coordinate lies in `𝓂[K] ^ 2`.
* `TauCeti.measurableSet_eisensteinSet`: the Eisenstein region is measurable.
* `TauCeti.measure_eisensteinSet`: for `0 < n`, the Eisenstein region has volume
  `q ^ (-n) (1 - q⁻¹)`.

## Implementation notes

The volume of a box of ideals is `MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow`,
which reads it off the scaling law `MeasureTheory.Measure.measure_image_mulVec_integerBox`
applied to the diagonal matrix `Matrix.diagonal fun i ↦ ϖ ^ e i`, whose determinant is
`ϖ ^ ∑ i, e i`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2.
-/

public section
noncomputable section

open Polynomial MeasureTheory ValuativeRel TauCeti.Polynomial
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

section CoefficientSpace

variable (K) in
/-- The Eisenstein region in the space `Fin n → K` of coefficient vectors of monic polynomials of
degree `n`: every coefficient has valuation below `1`, and the constant term of `monicOfCoeff a`
has valuation at least that of every element of valuation below `1`. For `0 < n` the constant term
is `a 0`, which then has the valuation of a uniformizer; for `n = 0` it is `1`, and the region is
the whole one-point space. When `𝒪[K]` is a discrete valuation ring,
`TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt` identifies these with the coefficient vectors
of the polynomials over `𝒪[K]` that are Eisenstein at `𝓂[K]`. -/
def eisensteinSet (n : ℕ) : Set (Fin n → K) :=
  {a | (∀ i, valuation K (a i) < 1) ∧
    ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((monicOfCoeff a).coeff 0)}

/-- Membership in the Eisenstein region, unfolded. -/
theorem mem_eisensteinSet {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔ (∀ i, valuation K (a i) < 1) ∧
      ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((monicOfCoeff a).coeff 0) :=
  Iff.rfl

end CoefficientSpace

section EisensteinPolynomial

variable [IsDiscreteValuationRing 𝒪[K]]

/-- **The Eisenstein region is the set of Eisenstein polynomials**: a coefficient vector lies in
`eisensteinSet K n` exactly when it is the coefficient vector of a polynomial over `𝒪[K]` that is
Eisenstein at `𝓂[K]`. -/
theorem mem_eisensteinSet_iff_exists_isEisensteinAt {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔
      ∃ f : 𝒪[K][X], f.map (algebraMap 𝒪[K] K) = monicOfCoeff a ∧ f.IsEisensteinAt 𝓂[K] := by
  have h1 : (1 : 𝒪[K]) ∉ 𝓂[K] := Ideal.one_notMem _
  constructor
  · rintro ⟨ha, h0⟩
    let c : Fin n → 𝒪[K] := fun i ↦ ⟨a i, (Valuation.mem_integer_iff _ _).2 (ha i).le⟩
    have hc : ∀ i, c i ∈ 𝓂[K] := fun i ↦ (valuation K).mem_maximalIdeal_iff.2 (ha i)
    refine ⟨monicOfCoeff c, by rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring],
      ⟨?_, fun {i} hi ↦ ?_, ?_⟩⟩
    · rwa [(monic_monicOfCoeff c).leadingCoeff]
    · rw [natDegree_monicOfCoeff] at hi
      rw [coeff_monicOfCoeff c ⟨i, hi⟩]
      exact hc _
    · rcases n.eq_zero_or_pos with rfl | hn
      · rw [coeff_monicOfCoeff_self c]
        exact fun h ↦ h1 (Ideal.pow_le_self two_ne_zero h)
      · rw [coeff_monicOfCoeff c ⟨0, hn⟩]
        rw [coeff_monicOfCoeff a ⟨0, hn⟩] at h0
        exact forall_valuation_le_iff_notMem_maximalIdeal_sq.1 h0
  · rintro ⟨f, hf, hE⟩
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
        natDegree_monicOfCoeff]
    have hcoeff (i : ℕ) : (monicOfCoeff a).coeff i = f.coeff i := by
      rw [← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [← coeff_monicOfCoeff a i, hcoeff]
      exact (valuation K).mem_maximalIdeal_iff.1 (hE.mem (hdeg ▸ i.isLt))
    · rw [hcoeff]
      exact forall_valuation_le_iff_notMem_maximalIdeal_sq.2 hE.notMem

/-- **The Eisenstein region as a difference of boxes**: for `0 < n`, it is the box `𝓂[K] ^ n`
minus the box whose constant coordinate lies in `𝓂[K] ^ 2` and whose other coordinates lie in
`𝓂[K]`. -/
theorem eisensteinSet_eq_sdiff {n : ℕ} (hn : 0 < n) :
    eisensteinSet K n = (Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑𝓂[K]) \
      Set.univ.pi fun i ↦
        ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update (fun _ ↦ 1) ⟨0, hn⟩ 2 i) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e : Fin n → ℕ := Function.update (fun _ ↦ 1) i₀ 2
  have he₀ : e i₀ = 2 := Function.update_self ..
  have he₁ (i : Fin n) (hi : i ≠ i₀) : e i = 1 := Function.update_of_ne hi ..
  ext a
  simp only [Set.mem_sdiff, Set.mem_univ_pi, ← valuation_lt_one_iff_mem_image_maximalIdeal,
    mem_eisensteinSet, coeff_monicOfCoeff a ⟨0, hn⟩]
  refine and_congr_right fun ha ↦ ?_
  refine (forall_valuation_le_iff_notMem_maximalIdeal_sq
    (c := ⟨a i₀, (Valuation.mem_integer_iff _ _).2 (ha i₀).le⟩)).trans
    (not_congr ⟨fun h i ↦ ?_, fun h ↦ ?_⟩)
  · rcases eq_or_ne i i₀ with rfl | hi
    · rw [he₀]
      exact ⟨_, h, rfl⟩
    · rw [he₁ i hi, pow_one, ← valuation_lt_one_iff_mem_image_maximalIdeal]
      exact ha i
  · obtain ⟨c, hc, hca⟩ := h i₀
    rw [he₀] at hc
    obtain rfl : c = ⟨a i₀, (Valuation.mem_integer_iff _ _).2 (ha i₀).le⟩ := Subtype.ext hca
    exact hc

end EisensteinPolynomial

section Measure

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The Eisenstein region is measurable. -/
theorem measurableSet_eisensteinSet {n : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinSet K n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Subsingleton.measurableSet
  · have h₁ := measurableSet_univ_pi_image_maximalIdeal_pow (K := K) fun (_ : Fin n) ↦ 1
    simp only [pow_one] at h₁
    rw [eisensteinSet_eq_sdiff hn]
    exact h₁.diff (measurableSet_univ_pi_image_maximalIdeal_pow _)

/-- **The volume of the Eisenstein region**: for a left-invariant measure on `Fin n → K`
normalized on the integer box, the Eisenstein region has volume `q ^ (-n) (1 - q⁻¹)` for
`0 < n`, where `q = Nat.card 𝓀[K]`. -/
theorem measure_eisensteinSet {n : ℕ} (hn : 0 < n) [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinSet K n) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set e : Fin n → ℕ := Function.update (fun _ ↦ 1) ⟨0, hn⟩ 2
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := fun _ ↦ 1) (e := e)
    (le_update_iff.2 ⟨one_le_two, fun _ _ ↦ le_rfl⟩)
  have he : ∑ i, e i = n + 1 := by
    simp only [e, Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sum_const,
      Finset.card_univ_sdiff, Finset.card_singleton, smul_eq_mul, mul_one, Fintype.card_fin]
    omega
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ fun _ ↦ 1
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e
  rw [hμ, mul_one] at h₁ h₂
  simp only [pow_one, Fin.sum_const, smul_eq_mul, mul_one] at hsub h₁
  rw [he] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [eisensteinSet_eq_sdiff hn, measure_sdiff hsub
    (measurableSet_univ_pi_image_maximalIdeal_pow e).nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

end Measure

end TauCeti
