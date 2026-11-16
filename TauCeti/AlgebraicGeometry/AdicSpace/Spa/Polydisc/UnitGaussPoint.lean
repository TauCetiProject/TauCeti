/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.PointTopology
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic

/-!
# The unit Gauss point of the closed unit polydisc and its rational-point closure

Let `K` be a nontrivially normed nonarchimedean field and
`D = Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` the closed unit polydisc of dimension `n` over `K`.
The *unit Gauss valuation* on `K⟨T₁, …, Tₙ⟩` is the multiplicative ultrametric Gauss norm

```text
|∑ a_α T^α| = sup_α ‖a_α‖,
```

transported from `MvPowerSeries.IsRestricted.subring` via
`TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`. It is continuous, has trivial support, and is
bounded by `1` precisely on the power-bounded elements `K⟨T₁, …, Tₙ⟩°`, so it defines the
*unit Gauss point* `η ∈ closedPolydisc n K`. In dimension `n = 1` it coincides with the
radius-`1` Gauss point `gaussPoint zero_lt_one le_rfl`; in dimension `n = 0` it coincides with
the unique classical point; for `n ≥ 1` and complete `K` it is not classical.

The main theorem concerns the closure of the `K`-rational classical points `D(K) ⊆ |D|` when `K`
is complete and its residue field `K° ⧸ K°° ≃ 𝓀[K]` is infinite:

1. **Normalized rational neighbourhoods.** Given a finite-numerator basic open `Spv(K⟨T⟩)(T/g)`
   normalized so that `‖g‖ = 1` and `‖f‖ ≤ 1` for every `f ∈ T`, every integral tuple
   `a ∈ (𝒪[K])ⁿ` whose residue `ā ∈ 𝓀[K]ⁿ` is not a root of the reduced polynomial
   `restrictedReduction g ∈ 𝓀[K][T₁, …, Tₙ]` defines a classical point lying in
   `Spv(K⟨T⟩)(T/g)`.
2. **Gauss point in the closure of `D(K)`.** Any rational neighbourhood `R(T/g)` of `η` has
   `g ≠ 0`; dividing `T` and `g` by a coefficient attaining `‖g‖` normalizes the presentation
   without changing the rational subset. The reduced polynomial `restrictedReduction g` is nonzero,
   so when the residue field is infinite, `MvPolynomial.funext` supplies a residue tuple `ā`
   where `restrictedReduction g` does not vanish, lifting to a `K`-rational point in `R(T/g)`.
   Since rational subsets form a basis of `closedPolydisc n K`, `η` lies in the closure of
   `D(K)`. In particular, any closed subset of a topological space containing the image of
   `D(K)` under a continuous map from `closedPolydisc n K` also contains the image of `η`, and
   for `n ≥ 1` the subspace `D(K)` is not closed in `|D|`.
3. **Sharpness of hypotheses.** In dimension `0`, `η` lies in `D(K)` (hence in its closure) over
   every complete `K`, regardless of residue field cardinality. For `n ≥ 1` and a finite residue
   field of cardinality `q`, the open neighbourhood `{|T₀^q - T₀| ≥ 1}` of `η` misses `D(K)`,
   so `η` does not lie in the closure of `D(K)`.

## Main definitions

* `TauCeti.ValuationSpectrum.unitGaussValuation`: the unit-radius multivariate Gauss norm as an
  `ℝ≥0`-valued valuation on `R⟨T₁, …, Tₙ⟩`, for a normed commutative ring `R` with
  multiplicative ultrametric norm and `‖1‖ = 1`.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point `η` of `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: the predicate characterizing `η` by its valuation
  comparison against `MvPowerSeries.gaussNorm norm (fun _ ↦ 1)`.

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_unitGaussValuation` and
  `TauCeti.ValuationSpectrum.unitGaussValuation_le_one_iff_isPowerBounded`: continuity and
  power-boundedness characterization of the unit Gauss valuation.
* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: in dimension `1`, `unitGaussPoint`
  agrees with `gaussPoint zero_lt_one le_rfl`.
* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq`: `IsUnitGaussPoint K n η` holds if and only
  if `η = unitGaussPoint n K`.
* Normalized rational neighbourhoods:
  `TauCeti.ValuationSpectrum.classicalPoint_mem_basicOpenFinset_of_eval_restrictedReduction_ne_zero`
  shows that a normalized rational neighbourhood of `η` contains every integral point whose residue
  avoids the vanishing locus of the reduced denominator.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: when `K` is complete with
  infinite residue field, the unit Gauss point lies in the closure of the `K`-rational points.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_of_isClosed` and
  `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed`: closed-set consequences for
  `closedPolydisc n K` and continuous images of polydisc charts.
* `TauCeti.ValuationSpectrum.not_isClosed_range_classicalPoint`: for `n ≥ 1` and infinite residue
  field, `D(K)` is not closed in `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_range_classicalPoint_of_finite`:
  dimension-`0` coincidence without residue infinitude, and failure for `n ≥ 1` over finite
  residue fields.

## References

* S. Howe and C. Klevdal, *p*-adic families of automorphic forms, proof of Lemma 9.3.5.
* B. Bhatt and D. Hansen, *The six functors for Zariski-constructible sheaves in rigid geometry*,
  Compos. Math. 158 (2022), Example 2.1.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.29 and
  Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal NormedField Valued

section NormedRing

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]
  [NormMulClass R] [NormOneClass R]

/-- **The unit-radius Gauss valuation on `R⟨T₁, …, Tₙ⟩`**: the multiplicative ultrametric
norm `f ↦ sup_α ‖a_α‖` viewed as an `ℝ≥0`-valued valuation through the Gauss comparison. -/
noncomputable def unitGaussValuation :
    Valuation (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) ℝ≥0 where
  toFun f := ‖restrictedMvPowerSeriesGaussEquiv f‖₊
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by simp
  map_add_le_max' f g := by
    rw [map_add, ← NNReal.coe_le_coe, NNReal.coe_max, coe_nnNorm, coe_nnNorm, coe_nnNorm]
    exact IsUltrametricDist.norm_add_le_max _ _

/-- The unit Gauss valuation evaluates to the `nnnorm` under `restrictedMvPowerSeriesGaussEquiv`. -/
theorem unitGaussValuation_apply
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    unitGaussValuation f = ‖restrictedMvPowerSeriesGaussEquiv f‖₊ :=
  (rfl)

/-- Viewed in `ℝ`, the unit Gauss valuation is `MvPowerSeries.gaussNorm` at polyradius `1`. -/
theorem coe_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (unitGaussValuation f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) R) := by
  rw [unitGaussValuation_apply, coe_nnNorm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv]

/-- The unit Gauss valuation of a constant is its norm. -/
@[simp]
theorem unitGaussValuation_weightedC (a : R) :
    unitGaussValuation (weightedC (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight a) =
      ‖a‖₊ :=
  NNReal.eq <| by
    rw [unitGaussValuation_apply, coe_nnNorm, coe_nnNorm,
      restrictedMvPowerSeriesGaussEquiv_weightedC,
      MvPowerSeries.norm_algebraMap_isRestrictedSubring]

/-- The unit Gauss valuation takes value `1` on each variable `Tᵢ`. -/
@[simp]
theorem unitGaussValuation_weightedX (i : Fin n) :
    unitGaussValuation (weightedX (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight i) =
      1 :=
  NNReal.eq <| by
    rw [unitGaussValuation_apply, coe_nnNorm, NNReal.coe_one,
      restrictedMvPowerSeriesGaussEquiv_weightedX]
    exact MvPowerSeries.norm_X (c := fun _ : Fin n ↦ (1 : ℝ)) i

/-- The unit Gauss valuation vanishes only at zero. -/
@[simp]
theorem unitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    unitGaussValuation f = 0 ↔ f = 0 := by
  simp [unitGaussValuation_apply]

/-- **The unit Gauss valuation is continuous** for the Huber restricted-series topology. -/
theorem isContinuous_unitGaussValuation :
    (unitGaussValuation (n := n) (R := R)).IsContinuous := by
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  have heq : {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
        isWeightFamily_one_weight | unitGaussValuation f < γ} =
      restrictedMvPowerSeriesGaussEquiv ⁻¹' Metric.ball 0 (γ : ℝ) := by
    ext f
    simp [unitGaussValuation_apply, Metric.mem_ball, dist_zero_right, ← NNReal.coe_lt_coe]
  rw [heq]
  exact Metric.isOpen_ball.preimage continuous_restrictedMvPowerSeriesGaussEquiv

end NormedRing

section NontriviallyNormedField

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K]

/-- Over a nontrivially normed ultrametric field, a series in `K⟨T₁, …, Tₙ⟩` has unit Gauss
valuation at most `1` if and only if it is power-bounded. -/
theorem unitGaussValuation_le_one_iff_isPowerBounded
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation f ≤ 1 ↔ IsPowerBounded f := by
  rw [unitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one,
    ← Subring.mem_unitClosedBall, ← TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall,
    mem_powerBoundedSubring, isPowerBounded_ringEquiv_iff restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_restrictedMvPowerSeriesGaussEquiv_symm]

/-- **The unit Gauss point of the closed unit polydisc `closedPolydisc n K`**: the point of
`Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` defined by the unit-radius Gauss norm `f ↦ sup_α ‖a_α‖`. -/
noncomputable def unitGaussPoint (n : ℕ) (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [NonarchimedeanRing K] : closedPolydisc n K :=
  ⟨ofValuation (unitGaussValuation (n := n) (R := K)),
    (mem_closedPolydisc_iff _ _ _).mpr
      ⟨(isContinuous_ofValuation_iff _).mpr isContinuous_unitGaussValuation,
        fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
          rw [map_one]
          exact unitGaussValuation_le_one_iff_isPowerBounded.mpr
            (mem_powerBoundedSubring.mp hf)⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T₁, …, Tₙ⟩` is defined by
`unitGaussValuation`. -/
theorem unitGaussPoint_val :
    (unitGaussPoint n K).1 = ofValuation (unitGaussValuation (n := n) (R := K)) :=
  (rfl)

/-- The unit Gauss point compares two series by their unit Gauss valuations. -/
@[simp]
theorem unitGaussPoint_vle_iff
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      unitGaussValuation f ≤ unitGaussValuation g := by
  rw [unitGaussPoint_val, vle_ofValuation]

/-- The unit Gauss point compares two series by their `MvPowerSeries.gaussNorm` at polyradius
`1`. -/
theorem unitGaussPoint_vle_iff_gaussNorm
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).1.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K) := by
  rw [unitGaussPoint_vle_iff, ← NNReal.coe_le_coe, coe_unitGaussValuation, coe_unitGaussValuation]

/-- The unit Gauss point kills only the zero series. -/
theorem unitGaussPoint_vle_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (unitGaussPoint n K).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero, unitGaussValuation_eq_zero_iff]

/-- **The support of the unit Gauss point is trivial.** -/
@[simp]
theorem supp_unitGaussPoint : (unitGaussPoint n K).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- **In positive dimension over a complete field, the unit Gauss point is not classical.** -/
theorem unitGaussPoint_ne_classicalPoint [CompleteSpace K] [NeZero n]
    (x : spa (powerBoundedSubring K)) (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ supp_unitGaussPoint x a ha

/-- **In dimension `1`, `unitGaussPoint` agrees with the radius-`1` Gauss point**
`gaussPoint zero_lt_one le_rfl`. -/
theorem unitGaussPoint_one_eq_gaussPoint :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  have hval (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight) :
      (unitGaussValuation f : ℝ) = (closedDiscGaussValuation zero_lt_one le_rfl f : ℝ) := by
    rw [unitGaussValuation_apply, coe_nnNorm, coe_closedDiscGaussValuation]
    refine le_antisymm ?_ ?_
    · refine MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_
      have hν : ν = Finsupp.single 0 (ν 0) :=
        Finsupp.ext fun i ↦ by rw [Fin.eq_zero i]; simp
      have hbdd : BddAbove (Set.range fun m : ℕ ↦
          ‖MvPowerSeries.coeff (Finsupp.single 0 m) (f : MvPowerSeries (Fin 1) K)‖ *
            (1 : ℝ) ^ m) :=
        ⟨‖restrictedMvPowerSeriesGaussEquiv f‖, by
          rintro _ ⟨m, rfl⟩
          simpa using MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f)
            (Finsupp.single 0 m)⟩
      have hle := le_ciSup hbdd (ν 0)
      rw [← hν] at hle
      simpa using hle
    · refine Real.iSup_le (fun m ↦ ?_) (norm_nonneg _)
      simpa using MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f)
        (Finsupp.single 0 m)
  refine Subtype.ext <| ext' fun f g ↦ ?_
  rw [unitGaussPoint_vle_iff, gaussPoint_vle_iff, ← NNReal.coe_le_coe, ← NNReal.coe_le_coe,
    hval f, hval g]

/-- **In dimension `0`, the unit Gauss point coincides with every classical point.** -/
theorem unitGaussPoint_zero_eq_classicalPoint [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) (a : Fin 0 → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint 0 K = classicalPoint x a ha := by
  have := subsingleton_closedPolydisc_zero (K := K)
  exact Subsingleton.elim _ _

/-- **Predicate characterizing the unit Gauss point of `closedPolydisc n K`**: `η` compares
restricted power series by their unit-radius Gauss norms `MvPowerSeries.gaussNorm norm 1`. -/
def IsUnitGaussPoint (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [NonarchimedeanRing K] (n : ℕ) (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring
      (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.1.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin n) K) ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (g : MvPowerSeries (Fin n) K)

/-- A point of `closedPolydisc n K` satisfies `IsUnitGaussPoint` if and only if it equals
`unitGaussPoint n K`. -/
theorem isUnitGaussPoint_iff_eq {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔ η = unitGaussPoint n K := by
  constructor
  · intro h
    refine Subtype.ext <| ext' fun f g ↦ ?_
    rw [h f g, unitGaussPoint_vle_iff_gaussNorm]
  · rintro rfl f g
    exact unitGaussPoint_vle_iff_gaussNorm f g

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint`. -/
@[simp]
theorem isUnitGaussPoint_unitGaussPoint : IsUnitGaussPoint K n (unitGaussPoint n K) :=
  isUnitGaussPoint_iff_eq.mpr rfl

/-- Any point satisfying `IsUnitGaussPoint` equals `unitGaussPoint n K`. -/
theorem IsUnitGaussPoint.eq_unitGaussPoint {η : closedPolydisc n K}
    (hη : IsUnitGaussPoint K n η) : η = unitGaussPoint n K :=
  isUnitGaussPoint_iff_eq.mp hη

end NontriviallyNormedField

section Closure

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K] [CompleteSpace K]

/-- **Normalized rational neighbourhoods of the unit Gauss point.** Suppose `‖g‖ = 1` and
`‖f‖ ≤ 1` for every `f ∈ T`. Then every integral point `a : Fin n → 𝒪[K]` whose residue avoids
the vanishing locus of the reduced polynomial `restrictedReduction g` defines a classical point
in `Spv(K⟨T₁, …, Tₙ⟩)(T / g)`. -/
theorem classicalPoint_mem_basicOpenFinset_of_eval_restrictedReduction_ne_zero
    (x : spa (powerBoundedSubring K))
    {T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hT : ∀ f ∈ T, ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ 1)
    (hg : ‖restrictedMvPowerSeriesGaussEquiv g‖ = 1)
    (a : Fin n → 𝒪[K])
    (heval :
      (TauCeti.MvPowerSeries.restrictedReduction
        ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩).eval
          (fun i ↦ IsLocalRing.residue 𝒪[K] (a i)) ≠ 0) :
    (classicalPoint x (fun i ↦ (a i : K))
        (fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.norm_le_one (a i)))).1 ∈
      basicOpenFinset T g := by
  let ha : ∀ i, IsPowerBounded ((a i : 𝒪[K]) : K) :=
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.norm_le_one (a i))
  have hmap_id :
      IsLocalRing.ResidueField.map ((RingHom.id K).integerRestrict fun _ ↦ le_rfl) =
        RingHom.id 𝓀[K] := by
    refine RingHom.ext fun y ↦ ?_
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪[K]) y
    rw [IsLocalRing.ResidueField.map_residue, RingHom.id_apply]
    exact congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext (by simp))
  have hg_ge_one : 1 ≤ ‖evalAtHom (fun i ↦ (a i : K)) ha g‖ := by
    rw [evalAtHom_eq_restrictedEval₂]
    by_contra! hlt
    have hzero := (TauCeti.MvPowerSeries.norm_restrictedEval₂_lt_one_iff
      (RingHom.id K) (fun _ ↦ le_rfl) a
      ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩).mp hlt
    rw [hmap_id, MvPolynomial.eval₂_id] at hzero
    exact heval hzero
  rw [mem_basicOpenFinset_iff]
  refine ⟨fun f hf ↦ ?_, ?_⟩
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2, evalAtHom_eq_restrictedEval₂]
    exact ((MvPowerSeries.norm_restrictedEval₂_le (RingHom.id K) (fun i ↦ (a i : K))
      (fun _ ↦ le_rfl) (fun i ↦ Valued.integer.norm_le_one (a i))
      (restrictedMvPowerSeriesGaussEquiv f)).trans (hT f hf)).trans hg_ge_one
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2, map_zero, norm_zero, not_le]
    exact zero_lt_one.trans_le hg_ge_one

open scoped Classical in
/-- **Every finite-numerator basic open containing the unit Gauss point contains a `K`-rational
classical point**, provided the residue field `K° ⧸ K°°` is infinite. -/
theorem exists_classicalPoint_mem_basicOpenFinset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K))
    {T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hη : (unitGaussPoint n K).1 ∈ basicOpenFinset T g) :
    ∃ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      (classicalPoint x a ha).1 ∈ basicOpenFinset T g := by
  rw [mem_basicOpenFinset_iff] at hη
  obtain ⟨hTle, hg0⟩ := hη
  have hgnorm_pos : 0 < ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
    rw [unitGaussPoint_vle_zero_iff] at hg0
    exact norm_pos_iff.mpr
      ((map_ne_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective).mpr hg0)
  obtain ⟨ν, hν⟩ :=
    MvPowerSeries.exists_norm_coeff_eq_norm (restrictedMvPowerSeriesGaussEquiv g)
  set c : K :=
    MvPowerSeries.coeff ν (restrictedMvPowerSeriesGaussEquiv g : MvPowerSeries (Fin n) K)
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (hν.symm ▸ hgnorm_pos)
  let u := weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight c⁻¹
  have hu : IsUnit u := (IsUnit.mk0 c⁻¹ (inv_ne_zero hc_ne)).map _
  have hu_norm : ‖restrictedMvPowerSeriesGaussEquiv u‖ = ‖c‖⁻¹ := by
    rw [restrictedMvPowerSeriesGaussEquiv_weightedC,
      MvPowerSeries.norm_algebraMap_isRestrictedSubring, norm_inv]
  have hg'_norm : ‖restrictedMvPowerSeriesGaussEquiv (g * u)‖ = 1 := by
    rw [map_mul, norm_mul, hu_norm, hν, mul_inv_cancel₀ hgnorm_pos.ne']
  have hT'_le : ∀ f' ∈ T.image (· * u), ‖restrictedMvPowerSeriesGaussEquiv f'‖ ≤ 1 := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hf'
    have hfle :
        ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
      have h := (unitGaussPoint_vle_iff f g).mp (hTle f hf)
      simpa only [unitGaussValuation_apply, ← NNReal.coe_le_coe, coe_nnNorm] using h
    rw [map_mul, norm_mul, hu_norm, hν]
    exact (mul_le_mul_of_nonneg_right hfle (inv_nonneg.mpr hgnorm_pos.le)).trans_eq
      (mul_inv_cancel₀ hgnorm_pos.ne')
  have hred_ne :
      TauCeti.MvPowerSeries.restrictedReduction
        ⟨restrictedMvPowerSeriesGaussEquiv (g * u),
          Subring.mem_unitClosedBall.mpr hg'_norm.le⟩ ≠ 0 :=
    TauCeti.MvPowerSeries.restrictedReduction_ne_zero_iff.mpr hg'_norm
  have : Infinite 𝓀[K] :=
    (Equiv.infinite_iff (canonicalReductionEquivResidueField K).toEquiv).mp inferInstance
  have hex : ∃ ā : Fin n → 𝓀[K],
      (TauCeti.MvPowerSeries.restrictedReduction
        ⟨restrictedMvPowerSeriesGaussEquiv (g * u),
          Subring.mem_unitClosedBall.mpr hg'_norm.le⟩).eval ā ≠ 0 := by
    by_contra! hzero
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hzero ā)
  obtain ⟨ā, hā⟩ := hex
  have hlift : ∀ i : Fin n, ∃ b : 𝒪[K], IsLocalRing.residue 𝒪[K] b = ā i :=
    fun i ↦ IsLocalRing.residue_surjective (ā i)
  choose a ha_res using hlift
  have hmem := classicalPoint_mem_basicOpenFinset_of_eval_restrictedReduction_ne_zero x hT'_le
    hg'_norm a (by simpa only [ha_res] using hā)
  refine ⟨fun i ↦ (a i : K),
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.norm_le_one (a i)), ?_⟩
  rw [← basicOpenFinset_image_mul_right T g u hu]
  convert hmem using 2
  ext
  simp

/-- **The unit Gauss point lies in the closure of the `K`-rational classical points** when `K` is
complete with infinite residue field. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) := by
  let A := weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
  let e : closedPolydisc n K ≃ₜ spa (powerBoundedSubring A) :=
    Homeomorph.setCongr (closedPolydisc_def n K)
  rw [mem_closure_iff]
  intro U hU hηU
  obtain ⟨W, hW, hηW, hWU⟩ :=
    (isTopologicalBasis_spaRationalFamily (powerBoundedSubring A)).exists_subset_of_mem_open
      (show e (unitGaussPoint n K) ∈ e.symm ⁻¹' U by simpa using hηU)
      (hU.preimage e.symm.continuous)
  obtain ⟨T, g, -, rfl⟩ := mem_spaRationalFamily_iff.mp hW
  have hηB : (unitGaussPoint n K).1 ∈ basicOpenFinset T g := by
    have hmem : (e (unitGaussPoint n K)).1 ∈ rationalSubset (powerBoundedSubring A) T g := hηW
    exact (rationalSubset_def _ T g ▸ Set.inter_subset_right) hmem
  obtain ⟨a, ha, hcl⟩ := exists_classicalPoint_mem_basicOpenFinset x hηB
  have hclW : e (classicalPoint x a ha) ∈
      Subtype.val ⁻¹' rationalSubset (powerBoundedSubring A) T g := by
    rw [Set.mem_preimage, rationalSubset_def]
    exact ⟨(e (classicalPoint x a ha)).2, hcl⟩
  have hclU : classicalPoint x a ha ∈ U := by
    have := hWU hclW
    simpa using this
  exact ⟨classicalPoint x a ha, hclU, ⟨⟨a, ha⟩, rfl⟩⟩

/-- **Existence and rational-point closure of the unit Gauss point.** Over a complete nontrivially
normed ultrametric field with infinite residue field, the closed unit polydisc `closedPolydisc n K`
has a unit Gauss point lying in the closure of its `K`-rational classical points. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [NonarchimedeanRing K] [CompleteSpace K]
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.1 a.2)) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint,
    unitGaussPoint_mem_closure_range_classicalPoint x⟩

/-- **Any closed subset of `closedPolydisc n K` containing all `K`-rational classical points
contains the unit Gauss point**, provided the residue field is infinite. -/
theorem unitGaussPoint_mem_of_isClosed
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K)) {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z)
    (h : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), classicalPoint x a ha ∈ Z) :
    unitGaussPoint n K ∈ Z :=
  (hZ.closure_subset_iff.mpr <| Set.range_subset_iff.mpr fun ⟨a, ha⟩ ↦ h a ha)
    (unitGaussPoint_mem_closure_range_classicalPoint x)

/-- **Closed-set consequence for a continuous map from a polydisc chart.** If `φ` is a continuous
map from `closedPolydisc n K` into a topological space `S` and `Z ⊆ S` is a closed subset
containing `φ` of every `K`-rational classical point, then `Z` contains `φ (unitGaussPoint n K)`,
provided the residue field is infinite. -/
theorem map_unitGaussPoint_mem_of_isClosed
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    {S : Type*} [TopologicalSpace S] (x : spa (powerBoundedSubring K))
    {φ : closedPolydisc n K → S} (hφ : Continuous φ) {Z : Set S} (hZ : IsClosed Z)
    (h : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      φ (classicalPoint x a ha) ∈ Z) :
    φ (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed x (hZ.preimage hφ) h

/-- **In positive dimension over a field with infinite residue field, the `K`-rational classical
points do not form a closed subset** of `closedPolydisc n K`: their closure contains the
nonclassical unit Gauss point. -/
theorem not_isClosed_range_classicalPoint
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  intro hclosed
  obtain ⟨⟨a, ha⟩, heq⟩ :=
    unitGaussPoint_mem_of_isClosed x hclosed fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩
  exact unitGaussPoint_ne_classicalPoint x a ha heq.symm

/-- **In dimension `0`, the unit Gauss point is a `K`-rational classical point**, with no
residue-field infinitude assumption. -/
theorem unitGaussPoint_zero_mem_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ Set.range (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) := by
  rw [range_classicalPoint_zero_eq_univ]
  trivial

/-- **In dimension `0`, the unit Gauss point lies in the closure of the `K`-rational points**, with
no residue-field infinitude assumption. -/
theorem unitGaussPoint_zero_mem_closure_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ closure (Set.range
      (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) :=
  subset_closure (unitGaussPoint_zero_mem_range_classicalPoint x)

/-- **Sharpness of residue-field infinitude.** When `n ≥ 1` and the residue field `K° ⧸ K°°`
is finite (of cardinality `q`), the unit Gauss point does not lie in the closure of the
`K`-rational classical points: the open neighbourhood `{|T₀^q - T₀| ≥ 1}` contains
`unitGaussPoint n K` but misses every classical point, since `|a₀^q - a₀| < 1` for every
`a₀ ∈ 𝒪[K]`. -/
theorem unitGaussPoint_notMem_closure_range_classicalPoint_of_finite
    [Finite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2)) := by
  have : Finite 𝓀[K] :=
    (Equiv.finite_iff (canonicalReductionEquivResidueField K).toEquiv).mp inferInstance
  let _ : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]
  let q : ℕ := Fintype.card 𝓀[K]
  have hq : 1 < q := Fintype.one_lt_card
  let X0 : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight 0
  let g := X0 ^ q - X0
  intro hmem
  rw [mem_closure_iff] at hmem
  have hηU : unitGaussPoint n K ∈ Subtype.val ⁻¹' basicOpen 1 g := by
    rw [Set.mem_preimage, mem_basicOpen_iff, unitGaussPoint_vle_iff, unitGaussPoint_vle_zero_iff,
      map_one]
    have hcoeff :
        MvPowerSeries.coeff (Finsupp.single (0 : Fin n) 1)
          (restrictedMvPowerSeriesGaussEquiv g : MvPowerSeries (Fin n) K) = -1 := by
      simp only [coe_restrictedMvPowerSeriesGaussEquiv, g, X0, AddSubgroupClass.coe_sub,
        SubmonoidClass.coe_pow, coe_weightedX, map_sub, MvPowerSeries.coeff_X_pow,
        MvPowerSeries.coeff_X]
      have hne : Finsupp.single (0 : Fin n) 1 ≠ Finsupp.single 0 q := by
        intro heq
        have h1 : (1 : ℕ) = q := by
          simpa using DFunLike.congr_fun heq 0
        omega
      simp [hne]
    have hge : 1 ≤ unitGaussValuation g := by
      rw [unitGaussValuation_apply, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnNorm]
      have hle := MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv g)
        (Finsupp.single 0 1)
      rw [hcoeff, norm_neg, norm_one] at hle
      exact hle
    refine ⟨hge, fun hg0 ↦ ?_⟩
    rw [hg0, map_zero] at hge
    simp at hge
  obtain ⟨_, hclU, ⟨⟨a, ha⟩, rfl⟩⟩ := hmem (Subtype.val ⁻¹' basicOpen 1 g)
    ((isOpen_basicOpen 1 g).preimage continuous_subtype_val) hηU
  rw [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle,
    vle_iff_norm_le_of_mem_spa x.2] at hclU
  have hnorm_ge : 1 ≤ ‖a 0 ^ q - a 0‖ := by
    simpa only [g, X0, map_one, map_sub, map_pow, evalAtHom_weightedX, norm_one] using hclU.1
  let a₀ : 𝒪[K] :=
    ⟨a 0, Valued.integer.mem_iff.mpr (isPowerBounded_iff_norm_le_one.mp (ha 0))⟩
  have hres_zero : IsLocalRing.residue 𝒪[K] (a₀ ^ q - a₀) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hnorm_lt : ‖a 0 ^ q - a 0‖ < 1 := by
    simpa [a₀] using Valued.integer.residue_eq_zero_iff_norm_lt_one.mp hres_zero
  exact hnorm_lt.not_ge hnorm_ge

end Closure

end TauCeti.ValuationSpectrum
