/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedEval.Finite
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval

/-!
# Completed comparison, weight bounds, and naturality for unit weights

When each weight is a singleton multiplicative unit `Tᵢ = {uᵢ}` (`TauCeti.IsNormMulUnit`) and
`‖uᵢ‖ * cᵢ = 1`, `TauCeti.Huber.weightedRestrictedGaussAlgEquiv` identifies the Huber weighted
restricted-series subring `R⟨X⟩_T` with the Gauss-normed ring `R{X/c}` at polyradii `c`. This file
extends that comparison to completions, converts between topological weight bounds and norm bounds
at `c`, and establishes naturality for polynomials, variable renamings, bounded coefficient maps,
and bounded evaluation.

## Main definitions

* `TauCeti.Huber.weightedRestrictedCompletionGaussAlgEquiv`: the completed `R`-algebra comparison
  between the separated completion of `R⟨X⟩_T` for `Tᵢ = {uᵢ}` and `R{X/c}` over a complete
  ultrametric base `R`.

## Main results

* `TauCeti.Huber.weightedRestrictedGaussAlgEquiv_weightedPolynomialHom`,
  `TauCeti.Huber.coe_weightedRestrictedGaussAlgEquiv_weightedRename`, and
  `TauCeti.Huber.weightedRestrictedGaussAlgEquiv_weightedRename_equiv`: compatibility with
  polynomial inclusions and variable renamings.
* `TauCeti.Huber.continuous_weightedRestrictedCompletionGaussAlgEquiv` and its `_symm`:
  continuity of the completed unit-weight Gauss comparison in both directions.
* `TauCeti.Huber.isWeightBounded_singleton_of_norm_le`,
  `TauCeti.Huber.IsPseudoUniformizer.isWeightBounded_units_iff_norm_le`, and
  `TauCeti.Huber.isWeightBounded_units_iff_norm_le`: conversion between `IsWeightBounded` for
  singleton weights and coordinatewise norm bounds `‖aᵢ‖ ≤ cᵢ`.
* `TauCeti.Huber.weightedRestrictedGaussAlgEquiv_weightedMap` and
  `TauCeti.Huber.weightedRestrictedCompletionGaussAlgEquiv_weightedMapCompletion`: naturality for
  bounded coefficient homomorphisms before and after completion.
* `TauCeti.Huber.weightedEvalHom_units_eq_restrictedEval₂OfBound` and
  `TauCeti.Huber.weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound`: Huber weighted
  evaluation agrees with `RingHom.restrictedEval₂OfBound` and satisfies the same operator-norm
  bound.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §5.6, Propositions 5.49 and 5.50.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

section WeightBounded

variable {k : ℕ}

/-- Norm bounds `‖tᵢ‖ * cᵢ ≤ 1` and `‖aᵢ‖ ≤ cᵢ` imply `IsWeightBounded` for singleton weights
`Tᵢ = {tᵢ}` along any bounded ring homomorphism `‖φ r‖ ≤ C * ‖r‖`, without assuming contractivity,
multiplicativity of norms, or `‖1‖ = 1`. -/
theorem isWeightBounded_singleton_of_norm_le {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {t : Fin k → R} {c : Fin k → ℝ} (htc : ∀ i, ‖t i‖ * c i ≤ 1)
    {a : Fin k → S} (ha : ∀ i, ‖a i‖ ≤ c i) :
    IsWeightBounded φ (fun i ↦ ({t i} : Set R)) a := by
  rw [isWeightBounded_singleton_iff_forall_isPowerBounded]
  intro i
  refine isPowerBounded_iff.mpr
    ((isBounded_closedBall_zero (R := S) (max ‖(1 : S)‖ (max C 0))).subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [mem_closedBall_zero_iff]
  cases n with
  | zero => simp
  | succ m =>
    have hci : 0 ≤ c i := (norm_nonneg (a i)).trans (ha i)
    have hpow_t : ‖φ (t i ^ (m + 1))‖ ≤ max C 0 * ‖t i‖ ^ (m + 1) :=
      (hφ _).trans <| (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (norm_pow_le' (t i) m.succ_pos) (le_max_right C 0))
    have hpow_a : ‖a i ^ (m + 1)‖ ≤ c i ^ (m + 1) :=
      (norm_pow_le' (a i) m.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg _) (ha i) _)
    calc ‖(φ (t i) * a i) ^ (m + 1)‖
        = ‖φ (t i ^ (m + 1)) * a i ^ (m + 1)‖ := by rw [mul_pow, map_pow]
      _ ≤ ‖φ (t i ^ (m + 1))‖ * ‖a i ^ (m + 1)‖ := norm_mul_le _ _
      _ ≤ (max C 0 * ‖t i‖ ^ (m + 1)) * c i ^ (m + 1) :=
          mul_le_mul hpow_t hpow_a (norm_nonneg _) (by positivity)
      _ = max C 0 * (‖t i‖ * c i) ^ (m + 1) := by rw [mul_assoc, ← mul_pow]
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (mul_nonneg (norm_nonneg _) hci) (htc i)) (le_max_right C 0)
      _ ≤ max ‖(1 : S)‖ (max C 0) := by rw [mul_one]; exact le_max_right _ _

private theorem norm_le_of_isWeightBounded_units {R S : Type*} [SeminormedCommRing R]
    [SeminormedCommRing S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ}
    (hc : ∀ i, ‖(u i : R)‖ * c i = 1) (hS : IsPowMul (‖·‖ : S → ℝ))
    (hpb : ∀ x : S, IsPowerBounded x → ‖x‖ ≤ 1)
    {a : Fin k → S} (hb : IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a) (i : Fin k) :
    ‖a i‖ ≤ c i := by
  have hle1 : ‖φ (u i) * a i‖ ≤ 1 :=
    hpb _ ((isWeightBounded_singleton_iff_forall_isPowerBounded φ _ a).mp hb i)
  have hu0 : ‖(u i : R)‖ ≠ 0 := fun h0 ↦ by simpa [h0] using hc i
  have : NormOneClass R := ⟨NormedRing.norm_one_of_norm_mul hu0 (hu i).norm_mul⟩
  have hinv : ‖(((u i)⁻¹ : Rˣ) : R)‖ = c i := by
    rw [(Units.isNormMulUnit_iff_norm_inv (u i)).mp (hu i)]
    exact mul_left_cancel₀ hu0 ((mul_inv_cancel₀ hu0).trans (hc i).symm)
  have hci : 0 < c i := lt_of_le_of_ne (hinv ▸ norm_nonneg _) fun h0 ↦ by
    simpa [← h0] using hc i
  by_contra! hgt
  have hdiv : 1 < ‖a i‖ / c i := (one_lt_div hci).mpr hgt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max C 1) hdiv
  have hcancel : a i ^ (n + 1) =
      φ ((((u i)⁻¹ : Rˣ) : R) ^ (n + 1)) * (φ (u i) * a i) ^ (n + 1) := by
    rw [map_pow, mul_pow, ← mul_assoc, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow,
      one_mul]
  have hpow : ‖a i‖ ^ (n + 1) ≤ max C 1 * c i ^ (n + 1) := by
    calc ‖a i‖ ^ (n + 1) = ‖a i ^ (n + 1)‖ := (hS (a i) n.succ_pos).symm
      _ = ‖φ ((((u i)⁻¹ : Rˣ) : R) ^ (n + 1)) * (φ (u i) * a i) ^ (n + 1)‖ :=
          congrArg norm hcancel
      _ ≤ ‖φ ((((u i)⁻¹ : Rˣ) : R) ^ (n + 1))‖ * ‖(φ (u i) * a i) ^ (n + 1)‖ := norm_mul_le _ _
      _ ≤ (max C 1 * c i ^ (n + 1)) * 1 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · exact (hφ _).trans (by
              rw [(hu i).units_inv.norm_pow, hinv]
              exact mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))
          · exact (norm_pow_le' _ n.succ_pos).trans (pow_le_one₀ (norm_nonneg _) hle1)
      _ = max C 1 * c i ^ (n + 1) := mul_one _
  have hdiv_le : (‖a i‖ / c i) ^ (n + 1) ≤ max C 1 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact hpow
  exact (hn.trans_le (pow_le_pow_right₀ hdiv.le n.le_succ)).not_ge hdiv_le

/-- **Weight bounds equal polydisc bounds under a pseudouniformiser and a power-multiplicative
norm.** Along any bounded ring homomorphism `φ : R →+* S` into a seminormed commutative ring with a
pseudouniformiser and power-multiplicative norm, a tuple `a` is weight-bounded for multiplicative
units `Tᵢ = {uᵢ}` (`‖uᵢ‖ * cᵢ = 1`) precisely when `‖aᵢ‖ ≤ cᵢ` for every `i`. -/
theorem IsPseudoUniformizer.isWeightBounded_units_iff_norm_le {R S : Type*}
    [SeminormedCommRing R] [SeminormedCommRing S] {ϖ : S} (hϖ : IsPseudoUniformizer ϖ)
    (hS : IsPowMul (‖·‖ : S → ℝ)) {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ}
    (hc : ∀ i, ‖(u i : R)‖ * c i = 1) {a : Fin k → S} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i :=
  ⟨norm_le_of_isWeightBounded_units hφ u hu hc hS
      fun _ hx ↦ (hϖ.isPowerBounded_iff_norm_le_one hS).mp hx,
    isWeightBounded_singleton_of_norm_le hφ fun i ↦ (hc i).le⟩

/-- **Weight bounds equal polydisc bounds over a normed field.** Along any bounded homomorphism
into a normed field `K`, a tuple `a` is weight-bounded for multiplicative units `Tᵢ = {uᵢ}`
(`‖uᵢ‖ * cᵢ = 1`) precisely when `‖aᵢ‖ ≤ cᵢ` for every `i`. -/
theorem isWeightBounded_units_iff_norm_le {R K : Type*} [SeminormedCommRing R] [NormedField K]
    {φ : R →+* K} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (u : Fin k → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)
    {a : Fin k → K} :
    IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a ↔ ∀ i, ‖a i‖ ≤ c i :=
  ⟨norm_le_of_isWeightBounded_units hφ u hu hc (fun x n _ ↦ norm_pow x n)
      fun _ ↦ isPowerBounded_iff_norm_le_one.mp,
    isWeightBounded_singleton_of_norm_le hφ fun i ↦ (hc i).le⟩

/-- When singleton weights `{tᵢ}` map into `{s_{e i}}` and satisfy `‖tᵢ‖ * cᵢ = 1` and
`‖sⱼ‖ * dⱼ = 1`, the target polyradii reindex to `c`. -/
theorem radii_comp_eq_of_singleton_subset {m : ℕ} {R : Type*} [Norm R]
    {t : Fin k → R} {c : Fin k → ℝ} (hc : ∀ i, ‖t i‖ * c i = 1)
    {s : Fin m → R} {d : Fin m → ℝ} (hd : ∀ j, ‖s j‖ * d j = 1)
    (e : Fin k → Fin m) (hts : ∀ i, ({t i} : Set R) ⊆ {s (e i)}) :
    d ∘ e = c := by
  funext i
  have hi : t i = s (e i) := Set.singleton_subset_singleton.mp (hts i)
  have hne : ‖t i‖ ≠ 0 := fun h0 ↦ by simpa [h0] using hc i
  exact mul_left_cancel₀ hne (by rw [Function.comp_apply, hc i, ← hd (e i), hi])

end WeightBounded

section Completion

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)

/-- The unit-weight Gauss comparison carries the Huber polynomial inclusion to
`TauCeti.MvPowerSeries.polynomialToRestricted`. -/
@[simp]
theorem weightedRestrictedGaussAlgEquiv_weightedPolynomialHom (p : MvPolynomial (Fin k) R) :
    weightedRestrictedGaussAlgEquiv u hu hc
        (weightedPolynomialHom _ (isWeightFamily_units u) p) =
      polynomialToRestricted c p :=
  Subtype.ext (by simp)

/-- The inverse unit-weight Gauss comparison carries `polynomialToRestricted` to the Huber
polynomial inclusion. -/
@[simp]
theorem weightedRestrictedGaussAlgEquiv_symm_polynomialToRestricted
    (p : MvPolynomial (Fin k) R) :
    (weightedRestrictedGaussAlgEquiv u hu hc).symm (polynomialToRestricted c p) =
      weightedPolynomialHom _ (isWeightFamily_units u) p :=
  Subtype.ext (by simp)

/-- On underlying formal power series, the unit-weight Gauss comparison commutes with renaming
variables along any embedding `e : Fin k ↪ Fin m`. -/
theorem coe_weightedRestrictedGaussAlgEquiv_weightedRename
    (v : Fin m → Rˣ) (hv : ∀ j, IsNormMulUnit (v j : R)) {d : Fin m → ℝ}
    (hd : ∀ j, ‖(v j : R)‖ * d j = 1) (e : Fin k ↪ Fin m)
    (huv : ∀ i, ({(u i : R)} : Set R) ⊆ {(v (e i) : R)})
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    (weightedRestrictedGaussAlgEquiv v hv hd
        (weightedRename e (isWeightFamily_units u) (isWeightFamily_units v) huv f) :
      MvPowerSeries (Fin m) R) =
      rename e (weightedRestrictedGaussAlgEquiv u hu hc f : MvPowerSeries (Fin k) R) := by
  simp only [coe_weightedRestrictedGaussAlgEquiv, coe_weightedRename]

/-- Along an equivalence of variables `e : Fin k ≃ Fin m`, the unit-weight Gauss comparison
intertwines `TauCeti.Huber.weightedRename` with `MvPowerSeries.IsRestricted.renameAlgEquivOfEq`. -/
theorem weightedRestrictedGaussAlgEquiv_weightedRename_equiv
    (v : Fin m → Rˣ) (hv : ∀ j, IsNormMulUnit (v j : R)) {d : Fin m → ℝ}
    (hd : ∀ j, ‖(v j : R)‖ * d j = 1) (e : Fin k ≃ Fin m)
    (huv : ∀ i, ({(u i : R)} : Set R) ⊆ {(v (e i) : R)})
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedGaussAlgEquiv v hv hd
        (weightedRename e.toEmbedding (isWeightFamily_units u) (isWeightFamily_units v) huv f) =
      IsRestricted.renameAlgEquivOfEq e d (radii_comp_eq_of_singleton_subset hc hd e huv)
        (weightedRestrictedGaussAlgEquiv u hu hc f) :=
  Subtype.ext (by simp [renameEquiv_apply])

variable [CompleteSpace R]

/-- **The completed unit-weight Gauss comparison.** Over a complete ultrametric normed commutative
ring `R`, the separated completion of `R⟨X⟩_T` at singleton multiplicative-unit weights
`Tᵢ = {uᵢ}` (`‖uᵢ‖ * cᵢ = 1`) is isomorphic as an `R`-algebra to `R{X/c}`. -/
noncomputable def weightedRestrictedCompletionGaussAlgEquiv :
    UniformSpace.Completion
        (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) ≃ₐ[R]
      IsRestricted.subring (R := R) c :=
  (UniformSpace.Completion.completeAlgEquivSelf
    (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) R).trans
    (weightedRestrictedGaussAlgEquiv u hu hc)

/-- On elements of the uncompleted subring, the completed unit-weight Gauss comparison agrees
with `weightedRestrictedGaussAlgEquiv`. -/
@[simp]
theorem weightedRestrictedCompletionGaussAlgEquiv_coe
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedCompletionGaussAlgEquiv u hu hc
        (f : UniformSpace.Completion
          (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) =
      weightedRestrictedGaussAlgEquiv u hu hc f := by
  simp [weightedRestrictedCompletionGaussAlgEquiv]

/-- The inverse completed unit-weight Gauss comparison sends a restricted series to its canonical
image in the completion. -/
@[simp]
theorem weightedRestrictedCompletionGaussAlgEquiv_symm_apply
    (f : IsRestricted.subring (R := R) c) :
    (weightedRestrictedCompletionGaussAlgEquiv u hu hc).symm f =
      ((weightedRestrictedGaussAlgEquiv u hu hc).symm f :
        UniformSpace.Completion
          (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R))
            (isWeightFamily_units u))) := by
  simp [weightedRestrictedCompletionGaussAlgEquiv]

/-- The completed unit-weight Gauss comparison sends the Huber constant `r` to `algebraMap R _ r`.
-/
theorem weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC (r : R) :
    weightedRestrictedCompletionGaussAlgEquiv u hu hc
        ((weightedC _ (isWeightFamily_units u) r :
          weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
          UniformSpace.Completion _) =
      algebraMap R _ r := by
  rw [weightedRestrictedCompletionGaussAlgEquiv_coe, weightedRestrictedGaussAlgEquiv_weightedC]

/-- The completed unit-weight Gauss comparison sends the Huber variable `Xᵢ` to `Xᵢ`. -/
theorem weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX (i : Fin k) :
    weightedRestrictedCompletionGaussAlgEquiv u hu hc
        ((weightedX _ (isWeightFamily_units u) i :
          weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
          UniformSpace.Completion _) =
      ⟨X i, isRestricted_X c i⟩ := by
  rw [weightedRestrictedCompletionGaussAlgEquiv_coe, weightedRestrictedGaussAlgEquiv_weightedX]

/-- Under the completed unit-weight Gauss comparison, the polynomial map into the completion is
`TauCeti.MvPowerSeries.polynomialToRestricted`. -/
theorem weightedRestrictedCompletionGaussAlgEquiv_comp_weightedPolynomialHom :
    (weightedRestrictedCompletionGaussAlgEquiv u hu hc).toRingHom.comp
        (UniformSpace.Completion.coeRingHom.comp
          (weightedPolynomialHom _ (isWeightFamily_units u))) =
      (polynomialToRestricted c).toRingHom :=
  RingHom.ext fun p ↦ by simp [UniformSpace.Completion.coeRingHom]

/-- The inverse completed unit-weight Gauss comparison sends `polynomialToRestricted` to the
polynomial map into the completion. -/
theorem weightedRestrictedCompletionGaussAlgEquiv_symm_comp_polynomialToRestricted :
    (weightedRestrictedCompletionGaussAlgEquiv u hu hc).symm.toRingHom.comp
        (polynomialToRestricted c).toRingHom =
      UniformSpace.Completion.coeRingHom.comp
        (weightedPolynomialHom _ (isWeightFamily_units u)) :=
  RingHom.ext fun p ↦ by simp [UniformSpace.Completion.coeRingHom]

include hu in
/-- Over a complete ultrametric normed domain, the completion of `R⟨X⟩_T` at multiplicative-unit
weights `Tᵢ = {uᵢ}` is an integral domain. -/
theorem isDomain_completion_weightedRestrictedSubring_units [IsDomain R] :
    IsDomain (UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :=
  (weightedRestrictedCompletionGaussAlgEquiv u hu
    (c := fun i ↦ ‖(u i : R)‖⁻¹)
    (fun i ↦ mul_inv_cancel₀ (norm_ne_zero_iff.mpr (u i).ne_zero))).toMulEquiv.isDomain _

variable [∀ i, Fact (0 < c i)]

/-- The completed unit-weight Gauss comparison is continuous from the completion topology to the
Gauss norm topology. -/
theorem continuous_weightedRestrictedCompletionGaussAlgEquiv :
    Continuous (weightedRestrictedCompletionGaussAlgEquiv u hu hc) := by
  change Continuous ((weightedRestrictedGaussAlgEquiv u hu hc) ∘
    (UniformSpace.Completion.completeAlgEquivSelf
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) R))
  rw [UniformSpace.Completion.coe_completeAlgEquivSelf]
  exact (continuous_weightedRestrictedGaussAlgEquiv u hu hc).comp
    (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf _).continuous

/-- The inverse completed unit-weight Gauss comparison is continuous from the Gauss norm topology
to the completion topology. -/
theorem continuous_weightedRestrictedCompletionGaussAlgEquiv_symm :
    Continuous (weightedRestrictedCompletionGaussAlgEquiv u hu hc).symm := by
  change Continuous ((UniformSpace.Completion.completeAlgEquivSelf
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))
      R).symm ∘ (weightedRestrictedGaussAlgEquiv u hu hc).symm)
  rw [UniformSpace.Completion.coe_completeAlgEquivSelf_symm]
  exact (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm _).continuous.comp
    (continuous_weightedRestrictedGaussAlgEquiv_symm u hu hc)

/-- On completions, the unit-weight Gauss comparison commutes with renaming variables along an
equivalence `e : Fin k ≃ Fin m`. -/
theorem weightedRestrictedCompletionGaussAlgEquiv_mapRingHom_weightedRename_equiv
    (v : Fin m → Rˣ) (hv : ∀ j, IsNormMulUnit (v j : R)) {d : Fin m → ℝ}
    [∀ j, Fact (0 < d j)] (hd : ∀ j, ‖(v j : R)‖ * d j = 1) (e : Fin k ≃ Fin m)
    (huv : ∀ i, ({(u i : R)} : Set R) ⊆ {(v (e i) : R)})
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    weightedRestrictedCompletionGaussAlgEquiv v hv hd
        (UniformSpace.Completion.mapRingHom
          (weightedRename e.toEmbedding (isWeightFamily_units u) (isWeightFamily_units v) huv)
          (continuous_weightedRename e.toEmbedding _ _ huv) f) =
      IsRestricted.renameAlgEquivOfEq e d (radii_comp_eq_of_singleton_subset hc hd e huv)
        (weightedRestrictedCompletionGaussAlgEquiv u hu hc f) := by
  have hcont : Continuous (IsRestricted.renameAlgEquivOfEq (R := R) e d
      (radii_comp_eq_of_singleton_subset hc hd e huv)) :=
    (AddMonoidHomClass.isometry_iff_norm _ |>.mpr
      (IsRestricted.norm_renameAlgEquivOfEq e d _)).continuous
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    ((continuous_weightedRestrictedCompletionGaussAlgEquiv v hv hd).comp
      UniformSpace.Completion.continuous_map)
    (hcont.comp (continuous_weightedRestrictedCompletionGaussAlgEquiv u hu hc))) fun g ↦ ?_
  rw [UniformSpace.Completion.mapRingHom_coe, weightedRestrictedCompletionGaussAlgEquiv_coe,
    weightedRestrictedCompletionGaussAlgEquiv_coe,
    weightedRestrictedGaussAlgEquiv_weightedRename_equiv]

end Completion

section Coefficients

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}
  (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  (v : Fin k → Sˣ) (hv : ∀ i, IsNormMulUnit (v i : S))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1) (hvc : ∀ i, ‖(v i : S)‖ * c i = 1)
  (huv : ∀ i, φ '' ({(u i : R)} : Set R) ⊆ {(v i : S)})

/-- The unit-weight Gauss comparison commutes with bounded coefficient maps preserving the
polyradii. -/
theorem weightedRestrictedGaussAlgEquiv_weightedMap
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedRestrictedGaussAlgEquiv v hv hvc
        (weightedMap hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f) =
      restrictedMap φ hφ (weightedRestrictedGaussAlgEquiv u hu hc f) :=
  Subtype.ext (by simp only [coe_weightedRestrictedGaussAlgEquiv, coe_weightedMap,
    coe_restrictedMap])

variable [∀ i, Fact (0 < c i)] [CompleteSpace R] [CompleteSpace S]

/-- The completed unit-weight Gauss comparison commutes with `weightedMapCompletion` and
`restrictedMap`. -/
theorem weightedRestrictedCompletionGaussAlgEquiv_weightedMapCompletion
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    weightedRestrictedCompletionGaussAlgEquiv v hv hvc
        (weightedMapCompletion hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f) =
      restrictedMap φ hφ (weightedRestrictedCompletionGaussAlgEquiv u hu hc f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    ((continuous_weightedRestrictedCompletionGaussAlgEquiv v hv hvc).comp
      (continuous_weightedMapCompletion _ _ _ _))
    ((continuous_restrictedMap φ hφ).comp
      (continuous_weightedRestrictedCompletionGaussAlgEquiv u hu hc))) fun g ↦ ?_
  simp only [weightedMapCompletion_coe, weightedRestrictedCompletionGaussAlgEquiv_coe,
    weightedRestrictedGaussAlgEquiv_weightedMap hφc hφ u hu v hv hc hvc huv]

include hφ in
/-- A bounded coefficient map on unit-weight completions obeys the same operator-norm bound in the
transported Gauss norms. -/
theorem norm_weightedRestrictedCompletionGaussAlgEquiv_weightedMapCompletion_le
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    ‖weightedRestrictedCompletionGaussAlgEquiv v hv hvc
        (weightedMapCompletion hφc (isWeightFamily_units u) (isWeightFamily_units v) huv f)‖ ≤
      C * ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc f‖ := by
  rw [weightedRestrictedCompletionGaussAlgEquiv_weightedMapCompletion hφc hφ u hu v hv hc hvc huv]
  exact norm_restrictedMap_le φ hφ _

end Coefficients

section Evaluation

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  {φ : R →+* S} {C : ℝ} {a : Fin k → S}
  (u : Fin k → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
  {c : Fin k → ℝ} (hc : ∀ i, ‖(u i : R)‖ * c i = 1)
  (hφc : ContinuousAt φ 0) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)
  (hb : IsWeightBounded φ (fun i ↦ ({(u i : R)} : Set R)) a)

/-- Huber weighted evaluation for unit weights `Tᵢ = {uᵢ}` agrees with bounded normed evaluation
`RingHom.restrictedEval₂OfBound` at polyradii `c`. Any `IsWeightBounded` witness may be used,
including `isWeightBounded_singleton_of_norm_le hφ (fun i ↦ (hc i).le) ha`. -/
theorem weightedEvalHom_units_eq_restrictedEval₂OfBound
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    weightedEvalHom (isWeightFamily_units u) hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (weightedRestrictedGaussAlgEquiv u hu hc f) := by
  rw [coe_weightedEvalHom, RingHom.restrictedEval₂OfBound_apply,
    coe_weightedRestrictedGaussAlgEquiv]

variable [∀ i, Fact (0 < c i)]

include hφ ha in
/-- Huber weighted evaluation for unit weights obeys the coefficient-map bound in the Gauss norm at
polyradii `c`. -/
theorem norm_weightedEvalHom_units_le
    (f : weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u)) :
    ‖weightedEvalHom (isWeightFamily_units u) hφc hb f‖ ≤
      C * ‖weightedRestrictedGaussAlgEquiv u hu hc f‖ := by
  rw [weightedEvalHom_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

variable [CompleteSpace R]

/-- Completed Huber weighted evaluation for unit weights agrees with bounded normed evaluation
through `weightedRestrictedCompletionGaussAlgEquiv`. -/
theorem weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    weightedEvalHomCompletion (isWeightFamily_units u) hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha
        (weightedRestrictedCompletionGaussAlgEquiv u hu hc f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((φ.continuous_restrictedEval₂OfBound a hφ ha).comp
      (continuous_weightedRestrictedCompletionGaussAlgEquiv u hu hc))) fun g ↦ ?_
  rw [weightedEvalHomCompletion_coe, weightedRestrictedCompletionGaussAlgEquiv_coe,
    weightedEvalHom_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]

include hφ ha in
/-- Completed Huber weighted evaluation for unit weights obeys the coefficient-map bound in the
Gauss norm transported by `weightedRestrictedCompletionGaussAlgEquiv`. -/
theorem norm_weightedEvalHomCompletion_units_le
    (f : UniformSpace.Completion
      (weightedRestrictedSubring (fun i ↦ ({(u i : R)} : Set R)) (isWeightFamily_units u))) :
    ‖weightedEvalHomCompletion (isWeightFamily_units u) hφc hb f‖ ≤
      C * ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc f‖ := by
  rw [weightedEvalHomCompletion_units_eq_restrictedEval₂OfBound u hu hc hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

end Evaluation

end TauCeti.Huber
