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
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Topology.Algebra.Module.Compact
import TauCeti.MeasureTheory.Group.LocalFieldScaling

/-!
# The Eisenstein region of coefficient space

Serre's mass formula is proved by integrating over the space of Eisenstein polynomials. A monic
polynomial of degree `n` over a nonarchimedean local field `K` is identified with its coefficient
vector `a : Fin n → K`, through `TauCeti.Polynomial.monicOfCoeff a = X ^ n + ∑ i, a i * X ^ i`,
and the *Eisenstein region* `TauCeti.eisensteinSet K n` is the set of coefficient vectors all of
whose entries lie in the open unit ball, the constant term having the largest valuation below `1`,
that of a uniformizer. By `TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt` these are exactly
the coefficient vectors of the polynomials over `𝒪[K]` that are Eisenstein at `𝓂[K]`.

The coefficient space `ι → K` carries the additive Haar measure normalized so that the integer box
`TauCeti.integerBox K ι = 𝒪[K] ^ ι` has volume `1`. For such a measure, writing `q` for the
cardinality of the residue field, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume
`q ^ (-∑ i, e i)`, since it is the image of the integer box under the diagonal matrix with entries
`ϖ ^ e i` for a uniformizer `ϖ`. The Eisenstein region is the difference of two such boxes, so its
volume is `q ^ (-n) (1 - q⁻¹)`.

The measure statements assume only left invariance of the measure and the normalization; no
product structure on the measure is used.

## Main definitions

* `TauCeti.eisensteinSet K n`: the Eisenstein region in `Fin n → K`.
* `TauCeti.integerBox K ι`: the integer box `𝒪[K] ^ ι` in `ι → K`.

## Main results

* `TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt`: a coefficient vector lies in the
  Eisenstein region exactly when it is the coefficient vector of a polynomial over `𝒪[K]` that is
  Eisenstein at `𝓂[K]`.
* `TauCeti.measure_univ_pi_image_maximalIdeal_pow`: the box with factors `𝓂[K] ^ e i` has volume
  `q ^ (-∑ i, e i)`.
* `TauCeti.measure_eisensteinSet`: the Eisenstein region has volume `q ^ (-n) (1 - q⁻¹)`.

## Implementation notes

The volume of a box of ideals is read off the scaling law
`MeasureTheory.Measure.measure_image_mulVec_univ_pi_integer`, applied to the diagonal matrix
`Matrix.diagonal fun i ↦ ϖ ^ e i`, whose determinant is `ϖ ^ ∑ i, e i`.

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
degree `n`: every coefficient has valuation below `1`, and the constant term has the largest
valuation below `1`, that of a uniformizer. By
`TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt` these are the coefficient vectors of the
Eisenstein polynomials over `𝒪[K]`. -/
def eisensteinSet (n : ℕ) : Set (Fin n → K) :=
  {a | (∀ i, valuation K (a i) < 1) ∧
    ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((monicOfCoeff a).coeff 0)}

/-- Membership in the Eisenstein region, unfolded. -/
theorem mem_eisensteinSet {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔ (∀ i, valuation K (a i) < 1) ∧
      ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((monicOfCoeff a).coeff 0) :=
  Iff.rfl

variable (K) in
/-- The integer box `𝒪[K] ^ ι` of the coefficient space `ι → K`, on which the Haar measure of the
coefficient space is normalized. -/
def integerBox (ι : Type*) : Set (ι → K) :=
  Set.univ.pi fun _ ↦ (𝒪[K] : Set K)

/-- Membership in the integer box: every coordinate is integral. -/
@[simp]
theorem mem_integerBox {ι : Type*} {a : ι → K} : a ∈ integerBox K ι ↔ ∀ i, a i ∈ 𝒪[K] := by
  simp [integerBox]

end CoefficientSpace

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Valuation

/-- An element of `K` has valuation below `1` exactly when it lies in the maximal ideal of
`𝒪[K]`. -/
private theorem valuation_lt_one_iff_mem_image {x : K} :
    valuation K x < 1 ↔ x ∈ ((↑) : 𝒪[K] → K) '' ↑𝓂[K] := by
  refine ⟨fun hx ↦ ⟨⟨x, (Valuation.mem_integer_iff _ _).2 hx.le⟩,
    (valuation K).mem_maximalIdeal_iff.2 hx, rfl⟩, ?_⟩
  rintro ⟨c, hc, rfl⟩
  exact (valuation K).mem_maximalIdeal_iff.1 hc

/-- An element `c` of the maximal ideal of `𝒪[K]` has the largest valuation below `1`, that of a
uniformizer, exactly when it does not lie in the square of the maximal ideal. -/
private theorem forall_valuation_le_iff_notMem_sq {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    (∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K c) ↔ c ∉ 𝓂[K] ^ 2 := by
  constructor
  · -- If `c = ϖ ^ 2 * d`, then `c` has valuation below that of the uniformizer `ϖ`.
    intro h hc2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc2
    obtain ⟨d, rfl⟩ := hc2
    have hϖ1 : valuation K ϖ < 1 :=
      (valuation K).mem_maximalIdeal_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    have hϖ0 : 0 < valuation K ϖ := by
      rw [zero_lt_iff, Ne, map_eq_zero, ZeroMemClass.coe_eq_zero]
      exact hϖ.ne_zero
    have hd : valuation K d ≤ 1 := (Valuation.mem_integer_iff _ _).1 d.2
    have hle := h ϖ hϖ1
    rw [MulMemClass.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow] at hle
    exact (hle.trans (mul_le_of_le_one_right' hd)).not_gt (pow_lt_self_of_lt_one₀ hϖ0 hϖ1
      one_lt_two)
  · -- If `y ∈ 𝓂` had larger valuation than `c`, then `c = y * (c / y)` would lie in `𝓂 ^ 2`.
    intro hc2 y hy
    by_contra! hlt
    have hy0 : 0 < valuation K y := zero_le.trans_lt hlt
    have hz : valuation K (c / y) < 1 := by
      rwa [map_div₀, div_lt_one₀ hy0]
    refine hc2 ?_
    have hcy : c = ⟨y, (Valuation.mem_integer_iff _ _).2 hy.le⟩ *
        ⟨c / y, (Valuation.mem_integer_iff _ _).2 hz.le⟩ := by
      ext
      rw [MulMemClass.coe_mul, mul_div_cancel₀ _ ((_root_.map_ne_zero _).1 hy0.ne')]
    rw [hcy, pow_two]
    exact Ideal.mul_mem_mul ((valuation K).mem_maximalIdeal_iff.2 hy)
      ((valuation K).mem_maximalIdeal_iff.2 hz)

end Valuation

section EisensteinPolynomial

/-- **The Eisenstein region is the set of Eisenstein polynomials**: a coefficient vector lies in
`eisensteinSet K n` exactly when it is the coefficient vector of a polynomial over `𝒪[K]` that is
Eisenstein at `𝓂[K]`. -/
theorem mem_eisensteinSet_iff_exists_isEisensteinAt {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔
      ∃ f : 𝒪[K][X], f.map (algebraMap 𝒪[K] K) = monicOfCoeff a ∧ f.IsEisensteinAt 𝓂[K] := by
  constructor
  · rintro ⟨ha, h0⟩
    let c : Fin n → 𝒪[K] := fun i ↦ ⟨a i, (Valuation.mem_integer_iff _ _).2 (ha i).le⟩
    have hc : ∀ i, c i ∈ 𝓂[K] := fun i ↦ (valuation K).mem_maximalIdeal_iff.2 (ha i)
    refine ⟨monicOfCoeff c, by rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring],
      ⟨?_, fun {i} hi ↦ ?_, ?_⟩⟩
    · rw [(monic_monicOfCoeff c).leadingCoeff]
      exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
    · rw [natDegree_monicOfCoeff] at hi
      rw [coeff_monicOfCoeff c ⟨i, hi⟩]
      exact hc _
    · rcases n.eq_zero_or_pos with rfl | hn
      · rw [show (monicOfCoeff c).coeff 0 = 1 by
          simpa using (monic_monicOfCoeff c).coeff_natDegree]
        exact fun h ↦ (Ideal.ne_top_iff_one _).1
          (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top (Ideal.pow_le_self two_ne_zero h)
      · rw [coeff_monicOfCoeff c ⟨0, hn⟩]
        rw [coeff_monicOfCoeff a ⟨0, hn⟩] at h0
        exact (forall_valuation_le_iff_notMem_sq (hc _)).1 h0
  · rintro ⟨f, hf, hE⟩
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
        natDegree_monicOfCoeff]
    have hcoeff (i : ℕ) : (monicOfCoeff a).coeff i = f.coeff i := by
      rw [← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [← coeff_monicOfCoeff a i, hcoeff]
      exact (valuation K).mem_maximalIdeal_iff.1 (hE.mem (hdeg ▸ i.isLt))
    · rcases n.eq_zero_or_pos with rfl | hn
      · intro y hy
        rw [show (monicOfCoeff a).coeff 0 = 1 by
          simpa using (monic_monicOfCoeff a).coeff_natDegree, map_one]
        exact hy.le
      · rw [hcoeff]
        exact (forall_valuation_le_iff_notMem_sq (hE.mem (hdeg ▸ hn))).2 hE.notMem

end EisensteinPolynomial

section Measure

variable {ι : Type*}

private theorem isClosed_univ_pi_image_maximalIdeal_pow (e : ι → ℕ) :
    IsClosed (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) :=
  isClosed_set_pi fun _ _ ↦
    ((IsNoetherianRing.isClosed_ideal _).isCompact.image continuous_subtype_val).isClosed

/-- **The volume of a box of ideals**: for an additive Haar measure on `ι → K` normalized on the
integer box, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume `q ^ (-∑ i, e i)`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_univ_pi_image_maximalIdeal_pow [Fintype ι] [MeasurableSpace (ι → K)]
    [BorelSpace (ι → K)] (μ : Measure (ι → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K ι) = 1) (e : ι → ℕ) :
    μ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ∑ i, e i := by
  classical
  -- The box is the image of the integer box under the diagonal matrix with entries `ϖ ^ e i`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h := Measure.measure_image_mulVec_univ_pi_integer μ hϖ (k := ∑ i, e i)
    (A := Matrix.diagonal fun i ↦ ϖ ^ e i) (by rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum])
  rw [integerBox] at hμ
  rw [hμ, mul_one, Matrix.diagonal_map (map_zero _)] at h
  refine Eq.trans (congrArg μ ?_) h
  rw [show (Matrix.diagonal fun i ↦ algebraMap 𝒪[K] K (ϖ ^ e i)).mulVec =
      Pi.map fun i y ↦ algebraMap 𝒪[K] K (ϖ ^ e i) * y from
    funext fun _ ↦ funext fun _ ↦ Matrix.mulVec_diagonal .., Set.piMap_image_univ_pi]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc
    exact ⟨d, d.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ϖ ^ e i * ⟨y, hy⟩, Ideal.mem_span_singleton.2 (dvd_mul_right _ _), rfl⟩

/-- **The volume of the Eisenstein region**: for an additive Haar measure on `Fin n → K` normalized
on the integer box, the Eisenstein region has volume `q ^ (-n) (1 - q⁻¹)`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_eisensteinSet {n : ℕ} (hn : 0 < n) [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinSet K n) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e : Fin n → ℕ := Function.update (fun _ ↦ 1) i₀ 2
  have he₀ : e i₀ = 2 := Function.update_self ..
  have he₁ (i : Fin n) (hi : i ≠ i₀) : e i = 1 := Function.update_of_ne hi ..
  -- The Eisenstein region is the box `𝓂[K] ^ n` minus the box with the constant term in `𝓂[K] ^ 2`.
  have hE : eisensteinSet K n = (Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 1)) \
      Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i) := by
    ext a
    simp only [Set.mem_sdiff, Set.mem_univ_pi, pow_one, ← valuation_lt_one_iff_mem_image,
      mem_eisensteinSet, coeff_monicOfCoeff a ⟨0, hn⟩]
    refine and_congr_right fun ha ↦ ?_
    have hc : (⟨a i₀, (Valuation.mem_integer_iff _ _).2 (ha i₀).le⟩ : 𝒪[K]) ∈ 𝓂[K] :=
      (valuation K).mem_maximalIdeal_iff.2 (ha i₀)
    refine (forall_valuation_le_iff_notMem_sq hc).trans (not_congr ⟨fun h i ↦ ?_, fun h ↦ ?_⟩)
    · rcases eq_or_ne i i₀ with rfl | hi
      · rw [he₀]
        exact ⟨_, h, rfl⟩
      · rw [he₁ i hi, pow_one, ← valuation_lt_one_iff_mem_image]
        exact ha i
    · obtain ⟨c, hc, hca⟩ := h i₀
      rw [he₀] at hc
      rwa [show (⟨a i₀, _⟩ : 𝒪[K]) = c from Subtype.ext hca.symm]
  have hsub : (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) ⊆
      Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 1) :=
    Set.pi_mono fun i _ ↦ Set.image_mono <| Ideal.pow_le_pow_right <| by
      rcases eq_or_ne i i₀ with rfl | hi
      · rw [he₀]
        exact one_le_two
      · rw [he₁ i hi]
  have he : ∑ i, e i = n + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ _)),
      Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
    omega
  have h₁ := measure_univ_pi_image_maximalIdeal_pow μ hμ fun _ ↦ 1
  have h₂ := measure_univ_pi_image_maximalIdeal_pow μ hμ e
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h₁
  rw [he] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [hE, measure_sdiff hsub
    (isClosed_univ_pi_image_maximalIdeal_pow e).measurableSet.nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

end Measure

end TauCeti
