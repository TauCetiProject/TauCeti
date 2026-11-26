/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.TateSeries
public import TauCeti.RingTheory.Huber.WeightedEval.Newton

/-!
# Multivariable Newton–Hensel lifting for `tateSeries`

Let `C` be a complete Hausdorff nonarchimedean ring with a pair of definition `P` whose ring of
definition `C₀` contains a pseudouniformiser `ϖ` of `C`. Given `F : Fin N → tateSeries N C` with
`F i ∈ tateSeriesPlus N C C₀`, a point `t : Fin N → C₀` with scaled Jacobian inverse
`M * J(t) = ϖ ^ k • 1`, and a residual bound `Fᵢ(t) ∈ ϖ ^ e • C₀` (`2 * k + 1 ≤ e`), this file
specialises `TauCeti.Huber.existsUnique_weightedEval_eq_zero`,
`TauCeti.Huber.pow_dvd_sub_of_weightedEval_eq_zero`, and `TauCeti.Huber.eq_of_weightedEval_eq_zero`
to `tateSeries N C` and establishes functoriality under continuous ring homomorphisms:

1. **Existence, uniqueness, and error bound** (`existsUnique_weightedEval_tateSeries_eq_zero`): `F`
   has a unique zero `u ∈ C₀^N` with `u ≡ t mod ϖ ^ (k + 1)`, and `u ≡ t mod ϖ ^ (e - k)`.
2. **Local uniqueness** (`eq_of_weightedEval_tateSeries_eq_zero`): any two zeros in
   `t + ϖ ^ (k + 1) C₀^N` coincide, with no residual hypothesis on `F(t)`.
3. **Functoriality** (`map_weightedEval_tateSeries`, `map_weightedEval_tateSeries_eq_zero`):
   continuous ring homomorphisms commute with `weightedEval` at power-bounded tuples and preserve
   Newton roots.

## Main results

* `TauCeti.Huber.existsUnique_weightedEval_tateSeries_eq_zero`: multivariable Newton–Hensel lifting
  and quantitative error bound `u ≡ t mod ϖ ^ (e - k)` on `tateSeries N C`.
* `TauCeti.Huber.eq_of_weightedEval_tateSeries_eq_zero`: uniqueness of zeros in
  `t + ϖ ^ (k + 1) C₀^N` without a residual hypothesis on `F(t)`.
* `TauCeti.Huber.map_weightedEval_tateSeries` and
  `TauCeti.Huber.map_weightedEval_tateSeries_eq_zero`: compatibility of evaluation and Newton roots
  with continuous ring homomorphisms.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996),
  Proposition 1.7.1.
* O. Gabber and L. Ramero, *Almost Ring Theory*, Lecture Notes in Math. **1800**, Springer (2003),
  Lemma 5.4.8.
-/

public section

open Matrix Pointwise

namespace TauCeti.Huber

section Newton

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]

/-- **Multivariable Newton–Hensel lifting for `tateSeries`:** if `F : Fin N → tateSeries N C` has
coefficients in `P.ringOfDefinition`, its Jacobian at `t` has an integral `ϖ ^ k`-scaled left
inverse `M`, and `F(t) ≡ 0 mod ϖ ^ e` with `2 * k + 1 ≤ e`, then `F` has a unique zero `u` in
`P.ringOfDefinition^N` congruent to `t` modulo `ϖ ^ (k + 1)`, and `u` satisfies
`u ≡ t mod ϖ ^ (e - k)`. -/
theorem existsUnique_weightedEval_tateSeries_eq_zero
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    (N : ℕ) (F : Fin N → tateSeries N C)
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) (k e : ℕ) (he : 2 * k + 1 ≤ e)
    (M : Matrix (Fin N) (Fin N) P.ringOfDefinition)
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hFt : ∀ i, ∃ r : P.ringOfDefinition,
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (F i : MvPowerSeries (Fin N) C) =
        (ϖ : C) ^ e * (r : C)) :
    ∃! u : Fin N → P.ringOfDefinition,
      (∀ i, ϖ ^ (k + 1) ∣ u i - t i) ∧
      (∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (F i : MvPowerSeries (Fin N) C) = 0) ∧
      (∀ i, ϖ ^ (e - k) ∣ u i - t i) := by
  have hFres (i) := mem_weightedRestrictedSubring.mp (F i).2
  have hF₀ (i) := mem_tateSeriesPlus_iff.mp (hF i)
  have hFt_smul (i) : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈ (ϖ : C) ^ e • (P.ringOfDefinition : Set C) := by
    obtain ⟨r, hr⟩ := hFt i; exact ⟨r, r.2, hr.symm⟩
  have hFt_base (i) : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ (2 * k + 1) • (P.ringOfDefinition : Set C) := by
    obtain ⟨r, hr⟩ := hFt i
    refine ⟨(ϖ ^ (e - (2 * k + 1)) * r : P.ringOfDefinition), SetLike.coe_mem _, ?_⟩
    push_cast; rw [hr, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_of_le he]
  obtain ⟨u, ⟨hu_mod, hu_zero⟩, hu_uniq⟩ :=
    existsUnique_weightedEval_eq_zero P hϖ hFres hF₀ t hJ hFt_base
  exact ⟨u, ⟨hu_mod, hu_zero,
    pow_dvd_sub_of_weightedEval_eq_zero P hϖ.isUnit hFres hF₀ hJ hFt_smul hu_mod hu_zero⟩,
    fun u' ⟨hu'_mod, hu'_zero, _⟩ ↦ hu_uniq u' ⟨hu'_mod, hu'_zero⟩⟩

/-- **Uniqueness of zeros in `t + ϖ ^ (k + 1) C₀^N`:** any two zeros `u, u' ∈ P.ringOfDefinition^N`
of `F` congruent to `t` modulo `ϖ ^ (k + 1)` are equal, provided the Jacobian of `F` at `t` has an
integral `ϖ ^ k`-scaled left inverse `M` (with no residual hypothesis on `F(t)`). -/
theorem eq_of_weightedEval_tateSeries_eq_zero
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    {N : ℕ} {F : Fin N → tateSeries N C}
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    {u u' : Fin N → P.ringOfDefinition}
    (hu : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hFu : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
      (F i : MvPowerSeries (Fin N) C) = 0)
    (hu' : ∀ i, ϖ ^ (k + 1) ∣ u' i - t i)
    (hFu' : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u' l : C))
      (F i : MvPowerSeries (Fin N) C) = 0) :
    u = u' :=
  eq_of_weightedEval_eq_zero P hϖ
    (fun i ↦ mem_weightedRestrictedSubring.mp (F i).2)
    (fun i ↦ mem_tateSeriesPlus_iff.mp (hF i))
    hJ hu hFu hu' hFu'

end Newton

section Functoriality

/-- **Compatibility of `weightedEval` on `tateSeries` with continuous ring homomorphisms:** if
`φ : C →+* C'` is continuous into a Hausdorff nonarchimedean ring `C'` and `x : Fin N → C` consists
of power-bounded elements, then evaluating `g : tateSeries N C` at `x` and applying `φ` agrees with
evaluating `tateSeries.mapRingHom hφ g` at `φ ∘ x`. -/
theorem map_weightedEval_tateSeries
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C]
    {C' : Type*} [CommRing C'] [TopologicalSpace C'] [NonarchimedeanRing C'] [T2Space C']
    {φ : C →+* C'} (hφ : Continuous φ)
    {N : ℕ} {x : Fin N → C} (hx : ∀ l, IsPowerBounded (x l)) (g : tateSeries N C) :
    φ (weightedEval (RingHom.id C) x (g : MvPowerSeries (Fin N) C)) =
      weightedEval (RingHom.id C') (fun l ↦ φ (x l))
        (tateSeries.mapRingHom hφ g : MvPowerSeries (Fin N) C') := by
  have hid : ContinuousAt (RingHom.id C) 0 := continuous_id.continuousAt
  have hsum := (hasSum_weightedEval_of_forall_isPowerBounded hid hx
    (mem_weightedRestrictedSubring.mp g.2)).map φ hφ
  have hsum' : HasSum (weightedEvalTerm (RingHom.id C') (fun l ↦ φ (x l))
      (tateSeries.mapRingHom hφ g : MvPowerSeries (Fin N) C'))
      (φ (weightedEval (RingHom.id C) x (g : MvPowerSeries (Fin N) C))) := by
    convert hsum using 1
    ext ν
    simp [weightedEvalTerm_def, map_prod]
  symm
  rw [weightedEval_def]
  exact hsum'.tsum_eq

/-- **Functoriality of Newton roots along a continuous ring homomorphism:** if `u ∈ C₀^N` is a
zero of `F` congruent to `t` modulo `ϖ ^ (k + 1)` under the Newton hypotheses over `(C, P, ϖ)`,
and `φ : C →+* C'` is continuous with `φ(C₀) ⊆ C'₀`, then `φ ∘ u` is the unique zero of the mapped
system `tateSeries.mapRingHom hφ ∘ F` congruent to `φ ∘ t` modulo `(φ ϖ) ^ (k + 1)`. -/
theorem map_weightedEval_tateSeries_eq_zero
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    {C' : Type*} [CommRing C'] [UniformSpace C'] [IsUniformAddGroup C']
    [NonarchimedeanRing C'] [CompleteSpace C'] [T0Space C'] (P' : PairOfDefinition C')
    {φ : C →+* C'} (hφ : Continuous φ)
    (hPφ : ∀ a ∈ P.ringOfDefinition, φ a ∈ P'.ringOfDefinition)
    {N : ℕ} (F : Fin N → tateSeries N C)
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) {k : ℕ}
    (M : Matrix (Fin N) (Fin N) P.ringOfDefinition)
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    {u : Fin N → P.ringOfDefinition}
    (hu_mod : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hu_zero : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
      (F i : MvPowerSeries (Fin N) C) = 0) :
    let ϖ' : P'.ringOfDefinition := ⟨φ ϖ, hPφ _ ϖ.2⟩
    let t' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (t l), hPφ _ (t l).2⟩
    let u' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (u l), hPφ _ (u l).2⟩
    (∀ i, ϖ' ^ (k + 1) ∣ u' i - t' i) ∧
    (∀ i, weightedEval (RingHom.id C') (fun l ↦ (u' l : C'))
      (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0) ∧
    ∀ v' : Fin N → P'.ringOfDefinition,
      (∀ i, ϖ' ^ (k + 1) ∣ v' i - t' i) →
      (∀ i, weightedEval (RingHom.id C') (fun l ↦ (v' l : C'))
        (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0) →
      v' = u' := by
  intro ϖ' t' u'
  have hu'_mod (i) : ϖ' ^ (k + 1) ∣ u' i - t' i := by
    obtain ⟨q, hq⟩ := hu_mod i
    exact ⟨⟨φ q, hPφ _ q.2⟩, Subtype.ext <| by
      simpa only [u', t', ϖ', AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_pow,
        map_sub, map_mul, map_pow] using congrArg (fun z : P.ringOfDefinition ↦ φ (z : C)) hq⟩
  have hu'_zero (i) : weightedEval (RingHom.id C') (fun l ↦ (u' l : C'))
      (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0 := by
    dsimp only [u']
    rw [← map_weightedEval_tateSeries hφ
      (fun l ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (u l).2) (F i),
      hu_zero i, map_zero]
  refine ⟨hu'_mod, hu'_zero, fun v' hv'_mod hv'_zero ↦ ?_⟩
  let M' : Matrix (Fin N) (Fin N) P'.ringOfDefinition :=
    M.map (φ.restrict P.ringOfDefinition P'.ringOfDefinition hPφ)
  have hF' (i) := tateSeries.mapRingHom_mem_tateSeriesPlus hφ hPφ (hF i)
  have hJ' : M'.map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C') (fun l ↦ (t' l : C'))
        (MvPowerSeries.pderiv j (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C'))) =
      (ϖ' : C') ^ k • (1 : Matrix (Fin N) (Fin N) C') := by
    ext i j
    have hij := congrArg φ (congrFun (congrFun hJ i) j)
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, map_sum, map_mul, map_pow] at hij ⊢
    convert hij using 1
    · refine Finset.sum_congr rfl fun l _ ↦ congrArg (φ (M i l : C) * ·) ?_
      rw [← tateSeries.coe_pderiv, tateSeries.pderiv_mapRingHom,
        ← map_weightedEval_tateSeries hφ
          (fun m ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (t m).2)
          (tateSeries.pderiv j (F l)),
        tateSeries.coe_pderiv]
    · split_ifs <;> simp [ϖ']
  exact eq_of_weightedEval_tateSeries_eq_zero P' ϖ' (hϖ.map hφ) hF' hJ'
    hv'_mod hv'_zero hu'_mod hu'_zero

end Functoriality

end TauCeti.Huber

end
