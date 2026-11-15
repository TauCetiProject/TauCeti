/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval

/-!
# Completed Gauss comparisons and evaluation for multiplicative-unit weights

When each weight set is a single multiplicative unit `uᵢ` (`TauCeti.IsNormMulUnit`) with reciprocal
norm `cᵢ` (`‖uᵢ‖ * cᵢ = 1`), `TauCeti.Huber.weightedRestrictedGaussAlgEquiv` identifies the Huber
weighted restricted-series ring `R⟨X⟩_{u}` with the Gauss-normed ring `R{X/c}` of series restricted
at the polyradii `c`. Because singleton weight families are bounded, `R⟨X⟩_{u}` is already complete
and Hausdorff over a complete ultrametric base
(`TauCeti.Huber.completeSpace_weightedRestrictedSubring_singleton`), so passing to the uniform
completion yields a topological algebra isomorphism between the completed Huber carrier and
`R{X/c}`.

This file develops the completed multiplicative-unit Gauss comparison, converts topological weight
bounds explicitly to and from coordinate norm bounds, and proves that polynomial inclusions,
bounded coefficient maps, and evaluations commute with the comparison before and after completion.

For a bounded homomorphism `φ : R →+* S`, coordinate bounds `‖aᵢ‖ ≤ cᵢ` together with
`‖uᵢ‖ * cᵢ ≤ 1` imply power-boundedness of `φ(uᵢ) * aᵢ`, hence `IsWeightBounded` for singleton
weights. Conversely, when `φ` is contractive and the `uᵢ` are multiplicative units, the unit's
inverse has norm `cᵢ`, so `‖φ(uᵢ) * aᵢ‖ ≤ 1` is equivalent to `‖aᵢ‖ ≤ cᵢ`. In target rings whose
power-bounded elements are the closed unit ball — normed fields, or seminormed rings with a
pseudouniformiser and power-multiplicative norm — topological weight-boundedness is therefore
equivalent to `‖aᵢ‖ ≤ cᵢ`.

## Main definitions

* `TauCeti.Huber.weightedRestrictedCompletionGaussEquiv` and
  `TauCeti.Huber.weightedRestrictedCompletionGaussAlgEquiv`: the topological ring and `R`-algebra
  equivalences between the completed unit-weighted Huber algebra and `R{X/c}`.

## Main results

* `TauCeti.Huber.isWeightBounded_singleton_of_norm_le`: coordinate norm bounds imply topological
  weight-boundedness along any bounded ring homomorphism.
* `TauCeti.Huber.IsPseudoUniformizer.isWeightBounded_units_iff_norm_le` and
  `TauCeti.Huber.isWeightBounded_units_iff_norm_le`: weight-boundedness is equivalent to
  coordinate norm bounds `‖aᵢ‖ ≤ cᵢ` when power-boundedness is characterised by `‖·‖ ≤ 1`.
* `TauCeti.Huber.continuous_weightedRestrictedCompletionGaussEquiv` and
  `TauCeti.Huber.continuous_weightedRestrictedCompletionGaussEquiv_symm`: the completed comparison
  is a homeomorphism onto the Gauss-normed algebra.
* `TauCeti.Huber.weightedRestrictedGaussAlgEquiv_weightedMap` and
  `TauCeti.Huber.weightedRestrictedCompletionGaussEquiv_weightedMapCompletion`: coefficient-map
  naturality before and after completion.
* `TauCeti.Huber.weightedEvalHom_units_eq_restrictedEval₂OfBound` and
  `TauCeti.Huber.weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound`: topological evaluation
  agrees with bounded Gauss-normed evaluation, and obeys the same norm bound.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), §1.3 and Definition 1.20.
* T. Wedhorn, *Adic Spaces*, §5.6, Propositions 5.49 and 5.50.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

/-! ### Converting between weight bounds and norm bounds -/

section WeightBounds

/-- **Norm bounds imply singleton weight-boundedness.** Along any bounded ring homomorphism `φ`,
if `‖uᵢ‖ * cᵢ ≤ 1` and `‖aᵢ‖ ≤ cᵢ` for every coordinate, then `a` is weight-bounded for the
singleton weights `{uᵢ}`. -/
theorem isWeightBounded_singleton_of_norm_le {k : ℕ} {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} {u : Fin k → R} {c : Fin k → ℝ}
    {a : Fin k → S} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (hu : ∀ i, ‖u i‖ * c i ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) :
    IsWeightBounded φ (fun i ↦ ({u i} : Set R)) a :=
  (isWeightBounded_singleton_iff_forall_isPowerBounded φ u a).mpr fun i ↦
    isPowerBounded_map_mul_of_norm_le hφ (hu i) (ha i)

/-- **Equivalence of unit weight bounds and norm bounds under a power-multiplicative norm.** In a
seminormed target ring with a pseudouniformiser and power-multiplicative norm, weight-boundedness
along a contractive map at multiplicative-unit weights `uᵢ` with `‖uᵢ‖ * cᵢ = 1` is equivalent to
`∀ i, ‖aᵢ‖ ≤ cᵢ`. -/
theorem IsPseudoUniformizer.isWeightBounded_units_iff_norm_le {k : ℕ} {R S : Type*}
    [SeminormedCommRing R] [SeminormedCommRing S] {ϖ : S} (hϖ : IsPseudoUniformizer ϖ)
    (hpow : IsPowMul (‖·‖ : S → ℝ)) (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1) {φ : R →+* S}
    (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {a : Fin k → S} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i := by
  rw [isWeightBounded_singleton_iff_forall_isPowerBounded]
  exact forall_congr' fun i ↦
    (hϖ.isPowerBounded_iff_norm_le_one hpow).trans
      (norm_map_unit_mul_le_one_iff (u i) (hu i) (hc i) hφ (a i))

/-- **Equivalence of unit weight bounds and norm bounds into a normed field.** Along a contractive
homomorphism into a normed field, weight-boundedness at multiplicative-unit weights `uᵢ` with
`‖uᵢ‖ * cᵢ = 1` is equivalent to `∀ i, ‖aᵢ‖ ≤ cᵢ`. -/
theorem isWeightBounded_units_iff_norm_le {k : ℕ} {R K : Type*} [SeminormedCommRing R]
    [NormedField K] (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ}
    (hc : ∀ i, ‖(u i : R)‖ * c i = 1) {φ : R →+* K} (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {a : Fin k → K} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i := by
  rw [isWeightBounded_singleton_iff_forall_isPowerBounded]
  exact forall_congr' fun i ↦
    isPowerBounded_iff_norm_le_one.trans
      (norm_map_unit_mul_le_one_iff (u i) (hu i) (hc i) hφ (a i))

end WeightBounds

/-! ### Completed Gauss comparison for multiplicative-unit weights -/

section Completion

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  (u : Fin n → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin n → ℝ}
  (hc : ∀ i, ‖(u i : R)‖ * c i = 1)

/-- The multiplicative-unit Gauss comparison sends the Huber polynomial inclusion to the
Gauss-normed polynomial inclusion at radii `c`. -/
@[simp]
theorem weightedRestrictedGaussAlgEquiv_weightedPolynomialHom (p : MvPolynomial (Fin n) R) :
    weightedRestrictedGaussAlgEquiv u hu hc (weightedPolynomialHom _ (isWeightFamily_units u) p) =
      polynomialToRestricted c p :=
  Subtype.ext (by simp)

variable [CompleteSpace R]

/-- Over a complete ultrametric normed commutative ring, the completed Huber restricted-series ring
for multiplicative-unit weights `Tᵢ = {uᵢ}` with `‖uᵢ‖ * cᵢ = 1` is isomorphic as a ring to the
Gauss-normed restricted-series ring `R{X/c}`. -/
noncomputable def weightedRestrictedCompletionGaussEquiv :
    UniformSpace.Completion
        (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) ≃+*
      IsRestricted.subring (R := R) c :=
  (UniformSpace.Completion.completeRingEquivSelf _).trans
    (weightedRestrictedGaussAlgEquiv u hu hc).toRingEquiv

/-- Over a complete ultrametric normed commutative ring, the completed multiplicative-unit Gauss
comparison is an `R`-algebra equivalence. -/
noncomputable def weightedRestrictedCompletionGaussAlgEquiv :
    UniformSpace.Completion
        (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) ≃ₐ[R]
      IsRestricted.subring (R := R) c :=
  (UniformSpace.Completion.completeAlgEquivSelf _ R).trans
    (weightedRestrictedGaussAlgEquiv u hu hc)

/-- The completed algebra Gauss comparison has the same underlying map as the ring comparison. -/
@[simp]
theorem coe_weightedRestrictedCompletionGaussAlgEquiv :
    ⇑(weightedRestrictedCompletionGaussAlgEquiv u hu hc) =
      ⇑(weightedRestrictedCompletionGaussEquiv u hu hc) := by
  simp [weightedRestrictedCompletionGaussAlgEquiv, weightedRestrictedCompletionGaussEquiv,
    AlgEquiv.coe_trans, RingEquiv.coe_trans]

/-- The inverse completed algebra Gauss comparison has the same underlying map as the inverse ring
comparison. -/
@[simp]
theorem coe_weightedRestrictedCompletionGaussAlgEquiv_symm :
    ⇑(weightedRestrictedCompletionGaussAlgEquiv u hu hc).symm =
      ⇑(weightedRestrictedCompletionGaussEquiv u hu hc).symm := by
  funext f
  simp [weightedRestrictedCompletionGaussAlgEquiv, weightedRestrictedCompletionGaussEquiv]

/-- On the canonical image of a weighted restricted series, the completed comparison agrees with
`weightedRestrictedGaussAlgEquiv`. -/
@[simp]
theorem weightedRestrictedCompletionGaussEquiv_coe
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedCompletionGaussEquiv u hu hc (f : UniformSpace.Completion _) =
      weightedRestrictedGaussAlgEquiv u hu hc f := by
  simp [weightedRestrictedCompletionGaussEquiv]

/-- The inverse completed comparison sends a Gauss-normed restricted series to the canonical image
of its inverse under `weightedRestrictedGaussAlgEquiv`. -/
@[simp]
theorem weightedRestrictedCompletionGaussEquiv_symm_apply (f : IsRestricted.subring (R := R) c) :
    (weightedRestrictedCompletionGaussEquiv u hu hc).symm f =
      ((weightedRestrictedGaussAlgEquiv u hu hc).symm f : UniformSpace.Completion _) := by
  simp [weightedRestrictedCompletionGaussEquiv]

/-- The completed comparison sends `algebraMap` scalars to `algebraMap` scalars. -/
theorem weightedRestrictedCompletionGaussEquiv_algebraMap (r : R) :
    weightedRestrictedCompletionGaussEquiv u hu hc (algebraMap R _ r) = algebraMap R _ r := by
  rw [← coe_weightedRestrictedCompletionGaussAlgEquiv, AlgEquiv.commutes]

/-- The completed comparison sends the canonical image of `weightedC r` to `algebraMap R _ r`. -/
theorem weightedRestrictedCompletionGaussEquiv_coe_weightedC (r : R) :
    weightedRestrictedCompletionGaussEquiv u hu hc
        ((weightedC _ (isWeightFamily_units u) r : weightedRestrictedSubring _ _) :
          UniformSpace.Completion _) =
      algebraMap R _ r := by
  simp

/-- The completed comparison sends the canonical image of `weightedX i` to `X i`. -/
theorem weightedRestrictedCompletionGaussEquiv_coe_weightedX (i : Fin n) :
    weightedRestrictedCompletionGaussEquiv u hu hc
        ((weightedX _ (isWeightFamily_units u) i : weightedRestrictedSubring _ _) :
          UniformSpace.Completion _) =
      ⟨X i, isRestricted_X c i⟩ := by
  simp

/-- Under the completed multiplicative-unit Gauss comparison, the Huber polynomial inclusion into
the completion agrees with `polynomialToRestricted`. -/
theorem weightedRestrictedCompletionGaussEquiv_comp_weightedPolynomialHom :
    (weightedRestrictedCompletionGaussEquiv u hu hc).toRingHom.comp
        (UniformSpace.Completion.coeRingHom.comp
          (weightedPolynomialHom _ (isWeightFamily_units u))) =
      (polynomialToRestricted (R := R) c).toRingHom :=
  RingHom.ext fun p ↦ by simp [UniformSpace.Completion.coeRingHom]

/-- The inverse completed multiplicative-unit Gauss comparison sends `polynomialToRestricted` to
the Huber polynomial inclusion into the completion. -/
theorem weightedRestrictedCompletionGaussEquiv_symm_comp_polynomialToRestricted :
    (weightedRestrictedCompletionGaussEquiv u hu hc).symm.toRingHom.comp
        (polynomialToRestricted (R := R) c).toRingHom =
      UniformSpace.Completion.coeRingHom.comp
        (weightedPolynomialHom _ (isWeightFamily_units u)) := by
  rw [← weightedRestrictedCompletionGaussEquiv_comp_weightedPolynomialHom u hu hc,
    ← RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

variable [∀ i, Fact (0 < c i)]

/-- The completed multiplicative-unit Gauss comparison is continuous from the completion topology
to the Gauss norm topology. -/
theorem continuous_weightedRestrictedCompletionGaussEquiv :
    Continuous (weightedRestrictedCompletionGaussEquiv u hu hc) :=
  (continuous_weightedRestrictedGaussAlgEquiv u hu hc).comp
    (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf _).continuous

/-- The inverse completed multiplicative-unit Gauss comparison is continuous from the Gauss norm
topology to the completion topology. -/
theorem continuous_weightedRestrictedCompletionGaussEquiv_symm :
    Continuous (weightedRestrictedCompletionGaussEquiv u hu hc).symm :=
  (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm _).continuous.comp
    (continuous_weightedRestrictedGaussAlgEquiv_symm u hu hc)

end Completion

/-! ### Coefficient-map and evaluation naturality at multiplicative-unit weights -/

section Coefficients

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}
  (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  (v : Fin k → Sˣ) (hv : ∀ i, IsNormMulUnit (v i : S))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1) (hc' : ∀ i, ‖(v i : S)‖ * c i = 1)
  (huv : ∀ i, φ '' ({(u i : R)} : Set R) ⊆ {(v i : S)})

/-- The multiplicative-unit Gauss comparisons commute with bounded coefficient maps preserving the
unit weights. -/
theorem weightedRestrictedGaussAlgEquiv_weightedMap
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedGaussAlgEquiv v hv hc'
        (weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f) =
      restrictedMap φ hφ (weightedRestrictedGaussAlgEquiv u hu hc f) := by
  apply Subtype.ext
  simp only [coe_weightedRestrictedGaussAlgEquiv, coe_weightedMap, coe_restrictedMap]

variable [CompleteSpace R] [CompleteSpace S] [∀ i, Fact (0 < c i)]

/-- The completed multiplicative-unit Gauss comparisons commute with `weightedMapCompletion`. -/
theorem weightedRestrictedCompletionGaussEquiv_weightedMapCompletion
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    weightedRestrictedCompletionGaussEquiv v hv hc'
        (weightedMapCompletion hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f) =
      restrictedMap φ hφ (weightedRestrictedCompletionGaussEquiv u hu hc f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    ((continuous_weightedRestrictedCompletionGaussEquiv v hv hc').comp
      (continuous_weightedMapCompletion _ _ _ _))
    ((continuous_restrictedMap φ hφ).comp
      (continuous_weightedRestrictedCompletionGaussEquiv u hu hc))) ?_
  intro g
  simp only [weightedMapCompletion_coe, weightedRestrictedCompletionGaussEquiv_coe,
    weightedRestrictedGaussAlgEquiv_weightedMap hφc hφ u hu v hv hc hc' huv]

include hφ in
/-- A bounded coefficient map on completed unit-weighted Huber algebras obeys the same bound in the
compared Gauss norms. -/
theorem norm_weightedRestrictedCompletionGaussEquiv_weightedMapCompletion_le
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    ‖weightedRestrictedCompletionGaussEquiv v hv hc'
        (weightedMapCompletion hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f)‖ ≤
      C * ‖weightedRestrictedCompletionGaussEquiv u hu hc f‖ := by
  rw [weightedRestrictedCompletionGaussEquiv_weightedMapCompletion hφc hφ u hu v hv hc hc' huv]
  exact norm_restrictedMap_le φ hφ _

end Coefficients

section Evaluation

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {φ : R →+* S} {C : ℝ}
  {a : Fin k → S} (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)
  (hφc : ContinuousAt φ 0) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (ha : ∀ i, ‖a i‖ ≤ c i)
  (hb : IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a)

/-- Huber evaluation on unit-weighted series agrees with bounded Gauss-normed evaluation at radii
`c`. Any witness `hb` of weight-boundedness may be supplied; in particular
`isWeightBounded_singleton_of_norm_le hφ (fun i ↦ (hc i).le) ha` provides one from the norm bounds
alone. -/
theorem weightedEvalHom_units_eq_restrictedEval₂OfBound
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedEvalHom (isWeightFamily_units u) hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (weightedRestrictedGaussAlgEquiv u hu hc f) := by
  rw [coe_weightedEvalHom, RingHom.restrictedEval₂OfBound_apply,
    coe_weightedRestrictedGaussAlgEquiv]

section NormedEval

variable [∀ i, Fact (0 < c i)]

include hφ ha in
/-- Huber evaluation on unit-weighted series obeys the coefficient homomorphism's bound in the
Gauss norm at radii `c`. -/
theorem norm_weightedEvalHom_units_le
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    ‖weightedEvalHom (isWeightFamily_units u) hφc hb f‖ ≤
      C * ‖weightedRestrictedGaussAlgEquiv u hu hc f‖ := by
  rw [weightedEvalHom_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

variable [CompleteSpace R]

/-- Completed Huber evaluation on unit-weighted series agrees with bounded Gauss-normed evaluation
through `weightedRestrictedCompletionGaussEquiv`. -/
theorem weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    weightedEvalHomCompletion (isWeightFamily_units u) hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (weightedRestrictedCompletionGaussEquiv u hu hc f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((φ.continuous_restrictedEval₂OfBound a hφ ha).comp
      (continuous_weightedRestrictedCompletionGaussEquiv u hu hc))) ?_
  intro g
  rw [weightedEvalHomCompletion_coe, weightedRestrictedCompletionGaussEquiv_coe,
    weightedEvalHom_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]

include hφ ha in
/-- Completed Huber evaluation on unit-weighted series obeys the coefficient homomorphism's bound
in the Gauss norm transported by `weightedRestrictedCompletionGaussEquiv`. -/
theorem norm_weightedEvalHomCompletion_units_le
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    ‖weightedEvalHomCompletion (isWeightFamily_units u) hφc hb f‖ ≤
      C * ‖weightedRestrictedCompletionGaussEquiv u hu hc f‖ := by
  rw [weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

end NormedEval

end Evaluation

end TauCeti.Huber
