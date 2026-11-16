/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint.Topology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Basic
public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.Valuation.Continuous.Valued

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.Restricted.GaussValuation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# The unit Gauss point of a closed polydisc and closure of rational points

Let `K` be an ultrametric normed field and `D = closedPolydisc n K` the closed unit polydisc
`Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` of dimension `n`. Applying the general unit-radius Gauss
valuation `TauCeti.Huber.weightedGaussValuation` to `NormedField.valuation` yields a continuous
valuation on `K⟨T₁, …, Tₙ⟩` bounded by `1` on `K⟨T₁, …, Tₙ⟩°`, whose real value is the unit Gauss
norm `‖∑ a_α T^α‖ = max_α ‖a_α‖`. Its equivalence class is the *unit Gauss point*
`unitGaussPoint n K : closedPolydisc n K`, which is uniquely characterized by the predicate
`IsUnitGaussPoint` comparing series by their unit Gauss norms. At `n = 1` it coincides with the
one-variable Gauss point `gaussPoint zero_lt_one le_rfl`; at `n = 0` it coincides with the unique
classical point; for `n ≥ 1` it has trivial support and is not classical.

Now assume `K` is complete and nontrivially normed. Every rational neighbourhood `R(T/s)` of
`unitGaussPoint n K` can be rescaled by the inverse of a coefficient attaining the Gauss norm of
`s` so that `‖s‖ = 1` and `‖f‖ ≤ 1` for all `f ∈ T`. Then `s` has a nonzero polynomial reduction
`p ∈ 𝓀[K][T₁, …, Tₙ]`, and every integral tuple `a ∈ 𝒪[K]ⁿ` whose residue `ā` satisfies
`p(ā) ≠ 0` gives a classical point `classicalPoint x a ha ∈ R(T/s)`. When the canonical reduction
`K° / K°° ≃+* 𝓀[K]` is infinite, `MvPolynomial.funext` provides such a tuple `ā`, which lifts to
`𝒪[K]ⁿ`. Since rational subsets form a basis of `closedPolydisc n K`, every open neighbourhood of
`unitGaussPoint n K` meets the `K`-rational points, so `unitGaussPoint n K` lies in their closure.

In particular, any closed subset of `closedPolydisc n K` (or of any topological space receiving a
continuous map from `closedPolydisc n K`) containing the images of all `K`-rational points also
contains the image of `unitGaussPoint n K`. For `n ≥ 1`, the rational points are therefore not
closed when `K° / K°°` is infinite.

Conversely, when `K° / K°° ≃+* 𝓀[K]` is finite of cardinality `q` and `n ≥ 1`, the rational open
`R({1} / (T₀^q - T₀))` contains `unitGaussPoint n K` (since the coefficient of `T₀` is `-1`) but
no `K`-rational point (since `a₀^q - a₀` has zero residue and hence norm strictly less than `1`).
Thus for `n ≥ 1`, `unitGaussPoint n K` lies in the closure of the `K`-rational points if and only
if the residue field `K° / K°°` is infinite. In dimension `0`, membership in the closure holds
unconditionally.

## Main definitions

* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K` for any
  ultrametric normed field `K`.
* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: the predicate characterizing the valuation class of
  the unit Gauss point via `MvPowerSeries.gaussNorm`.

## Main results

* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: `unitGaussPoint n K` is the
  unique point satisfying `IsUnitGaussPoint`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: in dimension `1`,
  `unitGaussPoint 1 K` agrees with `gaussPoint zero_lt_one le_rfl`.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero`:
  normalized rational neighbourhoods of `unitGaussPoint n K` contain every classical point whose
  reduction does not vanish on the reduced denominator.
* `TauCeti.ValuationSpectrum.exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem`:
  over a complete nontrivially normed field with infinite residue field, every rational
  neighbourhood of `unitGaussPoint n K` contains a `K`-rational classical point.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: `unitGaussPoint n K` lies in
  the closure of the `K`-rational points.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem` and
  `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem`:
  closed subsets containing the `K`-rational points (or their images under a continuous map) contain
  the unit Gauss point (or its image).
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_range_classicalPoint_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint_iff`: for `n ≥ 1`,
  `unitGaussPoint n K` lies in the closure of the `K`-rational points if and only if the residue
  field is infinite.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
* B. Bhatt and D. Hansen, *The six functors for Zariski-constructible sheaves in rigid geometry*,
  arXiv:2101.09759v2, Example 2.1, p. 6.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

section Definition

/-- A point `η` of the closed unit polydisc of dimension `n` over `K` is the unit Gauss point if it
compares restricted power series as their unit Gauss norms `‖∑ a_α T^α‖ = max ‖a_α‖` do. -/
def IsUnitGaussPoint (K : Type*) [SeminormedCommRing K] [NonarchimedeanRing K] (n : ℕ)
    (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring
      (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.1.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin n) K) ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (g : MvPowerSeries (Fin n) K)

/-- Unfolding rule for `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_def {K : Type*} [SeminormedCommRing K] [NonarchimedeanRing K] {n : ℕ}
    {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔
      ∀ f g : weightedRestrictedSubring
          (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
        η.1.toValuativeRel.vle f g ↔
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
            (f : MvPowerSeries (Fin n) K) ≤
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
            (g : MvPowerSeries (Fin n) K) :=
  Iff.rfl

end Definition

section UnitGaussPoint

open scoped NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The unit Gauss point of the closed polydisc `closedPolydisc n K`**: the point of
`Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` defined by the unit-radius Gauss valuation
`f ↦ max_ν ‖coeff ν f‖`. -/
noncomputable def unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    closedPolydisc n K :=
  ⟨ofValuation (weightedGaussValuation n (Valued.isContinuous_v (R := K))),
    (mem_closedPolydisc_iff n K _).mpr
      ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_weightedGaussValuation _),
        fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
          rw [map_one]
          exact weightedGaussValuation_le_one_of_mem_powerBoundedSubring n hf⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T⟩` is the valuation spectrum point of
the unit-radius Gauss valuation. -/
theorem unitGaussPoint_val (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (unitGaussPoint n K).1 =
      ofValuation (weightedGaussValuation n (Valued.isContinuous_v (R := K))) :=
  (rfl)

/-- The unit Gauss point compares restricted power series by their unit Gauss norms. -/
@[simp]
theorem unitGaussPoint_vle_iff (n : ℕ)
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
        MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K) := by
  rw [unitGaussPoint_val, vle_ofValuation, ← NNReal.coe_le_coe,
    coe_weightedGaussValuation_normedField, coe_weightedGaussValuation_normedField]

/-- The unit Gauss point compares restricted power series by the Gauss norms of their images under
`restrictedMvPowerSeriesGaussEquiv`. -/
theorem unitGaussPoint_vle_iff_norm (n : ℕ)
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  rw [unitGaussPoint_vle_iff, MvPowerSeries.norm_eq_gaussNorm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv, coe_restrictedMvPowerSeriesGaussEquiv]

/-- The unit Gauss point sends a series to `0` if and only if the series is `0`. -/
theorem unitGaussPoint_vle_zero_iff (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff_norm, map_zero, norm_zero, norm_le_zero_iff,
    map_eq_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective]

/-- The support of the unit Gauss point is trivial. -/
@[simp]
theorem supp_unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (unitGaussPoint n K).1.supp = ⊥ := by
  ext f
  rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    IsUnitGaussPoint K n (unitGaussPoint n K) :=
  fun f g ↦ unitGaussPoint_vle_iff n f g

/-- **Uniqueness of the unit Gauss point.** A point of `closedPolydisc n K` satisfies
`IsUnitGaussPoint` if and only if it equals `unitGaussPoint n K`. -/
theorem isUnitGaussPoint_iff_eq_unitGaussPoint {n : ℕ} {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔ η = unitGaussPoint n K := by
  refine ⟨fun h ↦ Subtype.ext (ext' fun f g ↦ ?_), fun h ↦ h ▸ isUnitGaussPoint_unitGaussPoint n K⟩
  rw [isUnitGaussPoint_def.mp h f g, unitGaussPoint_vle_iff]

/-- Over a complete ultrametric normed field, the unit Gauss point is not classical in positive
dimension. -/
theorem unitGaussPoint_ne_classicalPoint [CompleteSpace K] {n : ℕ} [NeZero n]
    (x : spa (powerBoundedSubring K)) (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_unitGaussPoint n K) x a ha

/-- **In dimension `0`, the unit Gauss point equals the unique classical point.** -/
theorem unitGaussPoint_zero_eq_classicalPoint [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K = classicalPoint x Fin.elim0 (fun i ↦ i.elim0) :=
  eq_classicalPoint_zero x (unitGaussPoint 0 K)

/-- **In dimension `0`, the unit Gauss point lies in the closure of the `K`-rational points
unconditionally**, without any hypothesis on the residue field. -/
theorem unitGaussPoint_zero_mem_closure_range_classicalPoint [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ closure (Set.range
      (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) :=
  subset_closure ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩, (unitGaussPoint_zero_eq_classicalPoint x).symm⟩

end UnitGaussPoint

/-- **In dimension `1`, `unitGaussPoint 1 K` coincides with the one-variable Gauss point at radius
`1`.** -/
theorem unitGaussPoint_one_eq_gaussPoint {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  have hval : ∀ f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight,
      (closedDiscGaussValuation (R := K) zero_lt_one le_rfl f : ℝ) =
        ‖restrictedMvPowerSeriesGaussEquiv f‖ := fun f ↦ by
    refine le_antisymm ?_ ?_
    · refine closedDiscGaussValuation_le_of_forall_norm_coeff_le zero_lt_one le_rfl fun ν ↦ ?_
      rw [← coe_restrictedMvPowerSeriesGaussEquiv]
      exact MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f) ν
    · obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm
        (restrictedMvPowerSeriesGaussEquiv f)
      have hν' : ν = Finsupp.single 0 (ν 0) :=
        Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
      rw [← hν, coe_restrictedMvPowerSeriesGaussEquiv, hν']
      simpa using norm_coeff_mul_pow_le_closedDiscGaussValuation (R := K) zero_lt_one le_rfl f (ν 0)
  refine Subtype.ext (ext' fun f g ↦ ?_)
  rw [unitGaussPoint_vle_iff_norm, gaussPoint_vle_iff, ← NNReal.coe_le_coe, hval f, hval g]

section Closure

open scoped NormedField

section InfiniteResidueField

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- Every nonzero restricted power series over a nontrivially normed ultrametric field can be
rescaled by a constant unit to have unit Gauss norm `1`, scaling all other norms by `‖s‖⁻¹`. -/
private theorem exists_isUnit_norm_mul_eq_one
    {s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hs0 : s ≠ 0) :
    ∃ u : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
      IsUnit u ∧ ‖restrictedMvPowerSeriesGaussEquiv (s * u)‖ = 1 ∧
        ∀ t, ‖restrictedMvPowerSeriesGaussEquiv t‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv s‖ →
          ‖restrictedMvPowerSeriesGaussEquiv (t * u)‖ ≤ 1 := by
  have hsnorm_pos : 0 < ‖restrictedMvPowerSeriesGaussEquiv s‖ :=
    norm_pos_iff.mpr ((map_ne_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective).mpr hs0)
  obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm (restrictedMvPowerSeriesGaussEquiv s)
  set c : K := MvPowerSeries.coeff ν (s : MvPowerSeries (Fin n) K)
  have hc_norm : ‖c‖ = ‖restrictedMvPowerSeriesGaussEquiv s‖ := by
    simpa only [c, coe_restrictedMvPowerSeriesGaussEquiv] using hν
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hc_norm.symm ▸ hsnorm_pos)
  refine ⟨weightedC _ isWeightFamily_one_weight c⁻¹,
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc0)).map _, ?_, ?_⟩
  · rw [map_mul, norm_mul, restrictedMvPowerSeriesGaussEquiv_weightedC,
      MvPowerSeries.norm_algebraMap_isRestrictedSubring, norm_inv, ← hc_norm,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc0)]
  · intro t ht
    rw [← hc_norm] at ht
    rw [map_mul, norm_mul, restrictedMvPowerSeriesGaussEquiv_weightedC,
      MvPowerSeries.norm_algebraMap_isRestrictedSubring, norm_inv]
    exact (mul_le_mul_of_nonneg_right ht (inv_nonneg.mpr (norm_nonneg c))).trans
      (mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc0)).le

/-- **Normalized rational-neighbourhood containment.** Let `R(T/g)` be a rational subset of
`closedPolydisc n K` whose denominator `g` has unit Gauss norm `1` and whose numerators `f ∈ T`
all have unit Gauss norm at most `1`. Then every integral tuple `a ∈ 𝒪[K]ⁿ` whose residue does not
annihilate the polynomial reduction of `g` in `𝓀[K][T₁, …, Tₙ]` produces a classical point lying in
`R(T/g)`. -/
theorem classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hg : ‖restrictedMvPowerSeriesGaussEquiv g‖ = 1)
    (hT : ∀ f ∈ T, ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ 1)
    (a : Fin n → Valued.integer K)
    (heval : MvPolynomial.eval (fun i ↦ IsLocalRing.residue (Valued.integer K) (a i))
      (TauCeti.MvPowerSeries.restrictedReduction
        ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩) ≠ 0) :
    classicalPoint x (fun i ↦ (a i : K))
        (fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).2)) ∈
      Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T g := by
  set a' : Fin n → K := fun i ↦ (a i : K)
  set ha' : ∀ i, IsPowerBounded (a' i) :=
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).2)
  have ha_norm : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ Valued.integer.mem_iff.mp (a i).2
  set gball : Subring.unitClosedBall
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
    ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩
  have hg_not_lt : ¬ ‖evalAtHom a' ha' g‖ < 1 := by
    rw [evalAtHom_eq_restrictedEval₂ a' ha' ha_norm g]
    have hiff := TauCeti.MvPowerSeries.norm_restrictedEval₂_lt_one_iff (RingHom.id K)
      (fun _ ↦ le_rfl) a gball
    simp only [RingHom.integerRestrict_id, IsLocalRing.ResidueField.map_id,
      MvPolynomial.eval₂_id] at hiff
    exact hiff.not.mpr heval
  have hg_ge : 1 ≤ ‖evalAtHom a' ha' g‖ := le_of_not_gt hg_not_lt
  rw [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def]
  refine ⟨(classicalPoint x a' ha').2, fun f hf ↦ ?_, ?_⟩
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2]
    exact (norm_evalAtHom_le a' ha' ha_norm f).trans ((hT f hf).trans hg_ge)
  · rw [classicalPoint_vle, map_zero, vle_iff_norm_le_of_mem_spa x.2, norm_zero, not_le]
    exact zero_lt_one.trans_le hg_ge

open scoped Classical in
/-- **Every rational neighbourhood of the unit Gauss point contains a `K`-rational point**, when
the canonical reduction `K° / K°°` is infinite. Rescaling by a coefficient attaining the Gauss norm
of `s` reduces to `‖s‖ = 1` and `‖f‖ ≤ 1` for all `f ∈ T`, and `MvPolynomial.funext` over the
infinite residue field `𝓀[K]` produces a non-root of the nonzero polynomial reduction. -/
theorem exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hs : unitGaussPoint n K ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      classicalPoint x a.1 a.2 ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
  rw [Set.mem_preimage, mem_rationalSubset_iff] at hs
  obtain ⟨-, hTle, hs_ne⟩ := hs
  have hs0 : s ≠ 0 := fun h ↦ hs_ne (by simp [h])
  obtain ⟨u, hu_unit, hg_norm, hscale⟩ := exists_isUnit_norm_mul_eq_one hs0
  set g := s * u
  set T' := T.image fun t ↦ t * u
  have hT'_norm : ∀ f ∈ T', ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ 1 := by
    rintro _ hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    exact hscale t ((unitGaussPoint_vle_iff_norm n t s).mp (hTle t ht))
  -- The reduced denominator is nonzero; over the infinite residue field it is nonvanishing.
  set gball : Subring.unitClosedBall
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
    ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg_norm.le⟩
  have hred_ne : TauCeti.MvPowerSeries.restrictedReduction gball ≠ 0 :=
    TauCeti.MvPowerSeries.restrictedReduction_ne_zero_iff.mpr hg_norm
  have : Infinite (Valued.ResidueField K) :=
    (canonicalReductionEquivResidueField K).toEquiv.infinite_iff.mp ‹_›
  have hex : ∃ ā : Fin n → Valued.ResidueField K,
      MvPolynomial.eval ā (TauCeti.MvPowerSeries.restrictedReduction gball) ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hall ā)
  obtain ⟨ā, hā⟩ := hex
  choose a ha_res using fun i ↦ IsLocalRing.residue_surjective (ā i)
  have hmem := classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero x T' g
    hg_norm hT'_norm a (by simpa [ha_res] using hā)
  have hrat : rationalSubset (powerBoundedSubring _) T' g =
      rationalSubset (powerBoundedSubring _) T s := by
    convert rationalSubset_image_mul_right (powerBoundedSubring _) T s u hu_unit
  rw [hrat] at hmem
  exact ⟨⟨fun i ↦ (a i : K),
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).2)⟩, hmem⟩

/-- **Gauss-point closure.** Over a complete nontrivially normed ultrametric field `K` whose
canonical reduction `K° / K°°` is infinite, the unit Gauss point `unitGaussPoint n K` lies in the
closure of the `K`-rational evaluation points of `closedPolydisc n K`. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) := by
  rw [mem_closure_iff]
  intro U hU hηU
  have : IsHuberRing (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight) :=
    isHuberRing_weightedRestrictedSubring
  let e := Homeomorph.setCongr (closedPolydisc_def n K)
  have hbasis := isTopologicalBasis_spaRationalFamily (powerBoundedSubring
    (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight))
  have heU : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hηeU : e (unitGaussPoint n K) ∈ e.symm ⁻¹' U := by simpa [e] using hηU
  obtain ⟨V, hVmem, hηV, hVU⟩ := hbasis.exists_subset_of_mem_open hηeU heU
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hVmem
  have hηV' : unitGaussPoint n K ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s :=
    hηV
  obtain ⟨a, ha⟩ := exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem x T s hηV'
  have haU : classicalPoint x a.1 a.2 ∈ U := by
    have : e (classicalPoint x a.1 a.2) ∈ e.symm ⁻¹' U := hVU ha
    simpa [e] using this
  exact ⟨classicalPoint x a.1 a.2, haU, ⟨a, rfl⟩⟩

/-- **A closed subset of `closedPolydisc n K` containing all `K`-rational points contains the unit
Gauss point**, when the residue field `K° / K°°` is infinite. -/
theorem unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z)
    (hmem : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), classicalPoint x a ha ∈ Z) :
    unitGaussPoint n K ∈ Z :=
  hZ.closure_subset_iff.mpr
    (Set.range_subset_iff.mpr fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ hmem a.1 a.2)
    (unitGaussPoint_mem_closure_range_classicalPoint x)

/-- **Closed-set propagation along a continuous map from a closed polydisc.** If `φ` maps
`closedPolydisc n K` continuously into a topological space `X` (for instance an affinoid open
chart of an adic space) and a closed subset `Z ⊆ X` contains `φ (classicalPoint x a ha)` for all
`a ∈ (K°)ⁿ`, then `Z` contains `φ (unitGaussPoint n K)`. -/
theorem map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite (CanonicalReduction K)] {X : Type*} [TopologicalSpace X]
    {φ : closedPolydisc n K → X} (hφ : Continuous φ) (x : spa (powerBoundedSubring K))
    {Z : Set X} (hZ : IsClosed Z)
    (hmem : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), φ (classicalPoint x a ha) ∈ Z) :
    φ (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem x (hZ.preimage hφ) hmem

/-- **In positive dimension over a field with infinite residue field, the `K`-rational points of a
closed polydisc do not form a closed subset**: their closure contains the non-classical unit Gauss
point. -/
theorem not_isClosed_range_classicalPoint [Infinite (CanonicalReduction K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2)) := fun hclosed ↦ by
  obtain ⟨a, ha⟩ := hclosed.closure_eq ▸ unitGaussPoint_mem_closure_range_classicalPoint (n := n) x
  exact unitGaussPoint_ne_classicalPoint x a.1 a.2 ha.symm

end InfiniteResidueField

section FiniteResidueField

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- For `q > 1` and `n ≥ 1`, the restricted series `T₀ ^ q - T₀` has `T₀`-coefficient `-1`, hence
unit Gauss norm at least `1`. -/
private theorem one_le_norm_weightedX_pow_sub_weightedX [NeZero n] {q : ℕ} (hq : 1 < q) :
    1 ≤ ‖restrictedMvPowerSeriesGaussEquiv
      ((weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ^ q -
        weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight 0)‖ := by
  set T₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  have hcoeff_pow : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
      ((T₀ ^ q : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight) : MvPowerSeries (Fin n) K) = 0 := by
    have hXpow : ((T₀ ^ q : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight) : MvPowerSeries (Fin n) K) =
        MvPowerSeries.monomial (Finsupp.single (0 : Fin n) q) (1 : K) := by
      rw [Subring.coe_pow, coe_weightedX, MvPowerSeries.X_pow_eq]
    rw [hXpow, MvPowerSeries.coeff_monomial_ne]
    intro heq
    have h1q : 1 = q := by
      have := congrArg (fun f : Fin n →₀ ℕ ↦ f 0) heq
      simpa using this
    omega
  have hcoeff_s : MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
      (((T₀ ^ q - T₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight) : MvPowerSeries (Fin n) K)) = -1 := by
    rw [AddSubgroupClass.coe_sub, map_sub, hcoeff_pow, coe_weightedX]
    simp [MvPowerSeries.coeff_X]
  have hle := MvPowerSeries.norm_coeff_le_norm
    (restrictedMvPowerSeriesGaussEquiv (T₀ ^ q - T₀)) (Finsupp.single (0 : Fin n) 1)
  rw [coe_restrictedMvPowerSeriesGaussEquiv, hcoeff_s, norm_neg, norm_one] at hle
  exact hle

/-- **Failure of Gauss-point closure for finite residue fields.** When `K° / K°°` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` is a neighbourhood of
`unitGaussPoint n K` disjoint from all `K`-rational points, because `a₀^q - a₀` reduces to `0` in
the residue field and therefore has norm strictly less than `1`. -/
theorem unitGaussPoint_notMem_closure_range_classicalPoint_of_finite
    [Finite (CanonicalReduction K)] [NeZero n] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) := by
  have hfin_res : Finite (Valued.ResidueField K) :=
    (canonicalReductionEquivResidueField K).toEquiv.finite_iff.mp ‹_›
  let : Fintype (Valued.ResidueField K) := Fintype.ofFinite (Valued.ResidueField K)
  set q : ℕ := Fintype.card (Valued.ResidueField K)
  set T₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  set s := T₀ ^ q - T₀
  set U : Set (closedPolydisc n K) :=
    Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) {1} s
  have hUopen : IsOpen U := by
    have h := isOpen_val_preimage_rationalSubset
      (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight)) {1} s
    rw [← closedPolydisc_def] at h
    exact h
  have hs_norm_ge : 1 ≤ ‖restrictedMvPowerSeriesGaussEquiv s‖ :=
    one_le_norm_weightedX_pow_sub_weightedX Fintype.one_lt_card
  have hηU : unitGaussPoint n K ∈ U := by
    rw [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def]
    refine ⟨(unitGaussPoint n K).2, ?_, ?_⟩
    · intro f hf
      rw [Finset.mem_singleton.mp hf, unitGaussPoint_vle_iff_norm, map_one, norm_one]
      exact hs_norm_ge
    · rw [unitGaussPoint_vle_zero_iff]
      intro hs0
      have : (1 : ℝ) ≤ 0 := by simpa [hs0] using hs_norm_ge
      linarith
  intro hcl
  obtain ⟨_, hpU, ⟨a, rfl⟩⟩ := mem_closure_iff.mp hcl U hUopen hηU
  rw [Set.mem_preimage, mem_rationalSubset_iff] at hpU
  have h1le := hpU.2.1 1 (Finset.mem_singleton_self 1)
  rw [classicalPoint_vle, map_one, vle_iff_norm_le_of_mem_spa x.2, norm_one] at h1le
  -- Every `a₀ ∈ 𝒪[K]` satisfies `a₀^q - a₀ ∈ 𝓂[K]`, so `‖a₀^q - a₀‖ < 1`.
  have heval_s : evalAtHom a.1 a.2 s = a.1 0 ^ q - a.1 0 := by simp [s, T₀]
  let b : Valued.integer K :=
    powerBoundedSubringEquivInteger K ⟨a.1 0, mem_powerBoundedSubring.mpr (a.2 0)⟩
  have hres : IsLocalRing.residue (Valued.integer K) (b ^ q - b) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hlt : ‖evalAtHom a.1 a.2 s‖ < 1 := by
    simpa only [heval_s, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, b,
      coe_powerBoundedSubringEquivInteger] using
      Valued.integer.residue_eq_zero_iff_norm_lt_one.mp hres
  exact hlt.not_ge h1le

end FiniteResidueField

section EquivalenceAndHeadline

/-- **Exact characterization of Gauss-point closure in positive dimension.** Over a complete
nontrivially normed ultrametric field `K`, for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K`
lies in the closure of the `K`-rational evaluation points if and only if the canonical reduction
`K° / K°°` is infinite. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint_iff {n : ℕ} [NeZero n]
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) ↔
      Infinite (CanonicalReduction K) := by
  refine ⟨fun h ↦ ?_, fun h ↦ unitGaussPoint_mem_closure_range_classicalPoint x⟩
  by_contra hnot
  have : Finite (CanonicalReduction K) := not_infinite_iff_finite.mp hnot
  exact unitGaussPoint_notMem_closure_range_classicalPoint_of_finite x h

/-- **Gauss-point closure.** Over a complete nontrivially normed ultrametric field `K` whose
canonical reduction `K° / K°°` is infinite, the unit Gauss point exists on the closed unit polydisc
of every dimension `n` and lies in the closure of the evaluation points at tuples of power-bounded
elements of `K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (CanonicalReduction K)] (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.1 a.2)) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K,
    unitGaussPoint_mem_closure_range_classicalPoint x⟩

end EquivalenceAndHeadline

end Closure

end TauCeti.ValuationSpectrum
