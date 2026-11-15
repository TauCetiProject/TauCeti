/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Semicircular.Law
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Free cumulants and formal series of real measures

For a Borel measure `μ` on `ℝ`, the functional `f ↦ ∫ x, f x ∂μ` on the pointwise monoid `ℝ → ℝ`
evaluated at the coordinate `id : ℝ → ℝ` defines the real **moment series** `μ.momentSeries`, the
**free cumulants** `μ.freeCumulant n`, the **free cumulant series** `μ.freeCumulantSeries`, and the
formal **R-series** `μ.rSeries`.

When `μ` is the law `φ.law a` of a selfadjoint element `a` in a C⋆-algebra, pushing coefficients
from `ℝ` to `ℂ` identifies these real quantities with the algebraic series and free cumulants of
`a` with respect to `φ`. For probability measures on `ℝ`, the moment–cumulant functional equations
`C(z M(z)) = M(z)` and `M(z) = 1 + z M(z) R(z M(z))` hold as identities in `ℝ⟦X⟧`. For compactly
supported probability measures, moments determine the measure, so two compactly supported
probability measures are equal if and only if they have the same R-series or the same free
cumulants of every positive order.

For non-integrable powers, Bochner integrals vanish by convention, so the affine transport formulas
`rSeries_map_affine_of_integrable` and `rSeries_map_affine` genuinely require finite moments of all
orders (in particular compact support), while cumulant determinacy requires compact support.

## Main declarations

* `MeasureTheory.Measure.momentSeries`: the formal moment series `∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n`.
* `MeasureTheory.Measure.freeCumulant`: the `n`-th free cumulant `κ_n(μ)` of a measure on `ℝ`.
* `MeasureTheory.Measure.freeCumulantSeries` and `MeasureTheory.Measure.rSeries`: the formal free
  cumulant series `1 + ∑_{n ≥ 1} κ_n(μ) z ^ n` and formal R-series `∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n`.
* `PositiveLinearMap.map_ofReal_momentSeries_law`,
  `PositiveLinearMap.map_ofReal_freeCumulantSeries_law`,
  `PositiveLinearMap.map_ofReal_rSeries_law`, `PositiveLinearMap.ofReal_freeCumulant_law`:
  compatibility with the algebraic series and cumulants of a selfadjoint C⋆-element.
* `MeasureTheory.Measure.momentSeries_eq_iff`, `MeasureTheory.Measure.freeCumulantSeries_eq_iff`,
  `MeasureTheory.Measure.rSeries_eq_iff`, `MeasureTheory.Measure.forall_freeCumulant_eq_iff`:
  determinacy of compactly supported probability measures by their formal series or cumulants.
* `MeasureTheory.Measure.rSeries_map_affine_of_integrable`,
  `MeasureTheory.Measure.freeCumulant_map_affine_of_integrable`,
  `MeasureTheory.Measure.rSeries_map_affine`, `MeasureTheory.Measure.freeCumulant_map_affine`:
  transformation of the R-series and free cumulants under affine pushforwards.
* `MeasureTheory.Measure.rSeries_dirac`, `MeasureTheory.Measure.rSeries_semicircleReal`: explicit
  R-series and cumulants of point masses and semicircle laws.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 11, 12, 16.
* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
-/

public section

noncomputable section

open MeasureTheory PowerSeries
open scoped ComplexOrder NNReal

namespace MeasureTheory.Measure

/-- The formal **moment series** `M_μ(z) = ∑_{n ≥ 0} (∫ x ^ n ∂μ) z ^ n` of a measure `μ` on `ℝ`. -/
def momentSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id

/-- The `n`-th coefficient of `μ.momentSeries` is the `n`-th moment `∫ x ^ n ∂μ`. -/
@[simp]
theorem coeff_momentSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.momentSeries = ∫ x, x ^ n ∂μ := by
  rw [momentSeries, TauCeti.coeff_momentSeries]
  rfl

/-- The constant coefficient of `μ.momentSeries` is the total real mass `μ.real Set.univ`. -/
@[simp]
theorem constantCoeff_momentSeries (μ : Measure ℝ) :
    constantCoeff μ.momentSeries = μ.real Set.univ := by
  rw [momentSeries, TauCeti.constantCoeff_momentSeries]
  simp [integral_const]

/-- The `n`-th **free cumulant** `κ_n(μ)` of a measure `μ` on `ℝ`, obtained by Möbius inversion on
`NC(n)` from the moments `∫ x ^ k ∂μ`. At `n = 0` it takes the formal value `1`. -/
def freeCumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : Fin n => id) Finset.univ

@[simp]
theorem freeCumulant_zero (μ : Measure ℝ) : μ.freeCumulant 0 = 1 := by
  rw [freeCumulant, Finset.univ_eq_empty, TauCeti.freeCumulant_empty]

@[simp]
theorem freeCumulant_one (μ : Measure ℝ) : μ.freeCumulant 1 = ∫ x, x ∂μ := by
  rw [freeCumulant, Finset.univ_unique, TauCeti.freeCumulant_singleton]
  rfl

/-- The second free cumulant of `μ` is `∫ x ^ 2 ∂μ - (∫ x ∂μ) ^ 2`. -/
theorem freeCumulant_two (μ : Measure ℝ) :
    μ.freeCumulant 2 = (∫ x, x ^ 2 ∂μ) - (∫ x, x ∂μ) ^ 2 := by
  rw [freeCumulant, Finset.univ_fin2, TauCeti.freeCumulant_pair _ _ Fin.zero_lt_one, sq]
  simp_rw [Pi.mul_apply, id_eq, ← sq]

/-- The formal **free cumulant series** `C_μ(z) = 1 + ∑_{n ≥ 1} κ_n(μ) z ^ n` of `μ`. -/
def freeCumulantSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id

@[simp]
theorem coeff_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.freeCumulantSeries = μ.freeCumulant n := by
  rw [freeCumulantSeries, TauCeti.coeff_freeCumulantSeries, freeCumulant]

@[simp]
theorem constantCoeff_freeCumulantSeries (μ : Measure ℝ) :
    constantCoeff μ.freeCumulantSeries = 1 :=
  TauCeti.constantCoeff_freeCumulantSeries _ _

/-- The formal **R-series** `R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n` of `μ`, the formal power-series
counterpart of Voiculescu's R-transform. -/
def rSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id

@[simp]
theorem coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.rSeries = μ.freeCumulant (n + 1) := by
  rw [rSeries, TauCeti.coeff_rSeries, freeCumulant]

@[simp]
theorem constantCoeff_rSeries (μ : Measure ℝ) :
    constantCoeff μ.rSeries = ∫ x, x ∂μ := by
  rw [rSeries, TauCeti.constantCoeff_rSeries]
  rfl

/-- The free cumulant series and the R-series satisfy `C_μ(z) = 1 + z R_μ(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rSeries (μ : Measure ℝ) :
    μ.freeCumulantSeries = 1 + X * μ.rSeries :=
  TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries _ _

/-- For a probability measure `μ`, the moment and free cumulant series satisfy
`C_μ(z M_μ(z)) = M_μ(z)`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.freeCumulantSeries.subst (X * μ.momentSeries) = μ.momentSeries :=
  TauCeti.freeCumulantSeries_subst_X_mul_momentSeries id (by simp [integral_const])

/-- For a probability measure `μ`, the moment series and R-series satisfy
`M_μ(z) = 1 + z M_μ(z) R_μ(z M_μ(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    μ.momentSeries = 1 + X * μ.momentSeries * μ.rSeries.subst (X * μ.momentSeries) :=
  TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst id
    (by simp [integral_const])

end MeasureTheory.Measure

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- Complexifying the moment series of the law `φ.law a` of a selfadjoint element `a` recovers the
algebraic moment series of `a`. -/
theorem map_ofReal_momentSeries_law (ha : IsSelfAdjoint a) :
    (law φ a).momentSeries.map Complex.ofRealHom = TauCeti.momentSeries φ.toLinearMap a := by
  ext n
  simp [Measure.coeff_momentSeries, ofReal_integral_pow_law φ ha n]

/-- Complexifying the free cumulant series of `φ.law a` recovers the algebraic free cumulant series
of `a`. -/
theorem map_ofReal_freeCumulantSeries_law (ha : IsSelfAdjoint a) :
    (law φ a).freeCumulantSeries.map Complex.ofRealHom =
      TauCeti.freeCumulantSeries φ.toLinearMap a := by
  rw [Measure.freeCumulantSeries, TauCeti.map_freeCumulantSeries]
  refine TauCeti.freeCumulantSeries_congr _ id ?_
  rw [← TauCeti.map_momentSeries]
  exact map_ofReal_momentSeries_law φ ha

/-- Complexifying the R-series of `φ.law a` recovers the algebraic R-series of `a`. -/
theorem map_ofReal_rSeries_law (ha : IsSelfAdjoint a) :
    (law φ a).rSeries.map Complex.ofRealHom = TauCeti.rSeries φ.toLinearMap a := by
  rw [Measure.rSeries, TauCeti.map_rSeries]
  refine TauCeti.rSeries_congr _ id ?_
  rw [← TauCeti.map_momentSeries]
  exact map_ofReal_momentSeries_law φ ha

/-- The `n`-th free cumulant of `φ.law a`, coerced to `ℂ`, is the `n`-th algebraic free cumulant
of `a`. -/
theorem ofReal_freeCumulant_law (ha : IsSelfAdjoint a) (n : ℕ) :
    (((law φ a).freeCumulant n : ℝ) : ℂ) =
      TauCeti.freeCumulant φ.toLinearMap (fun _ : Fin n => a) Finset.univ := by
  simpa [Measure.coeff_freeCumulantSeries] using
    congrArg (coeff n) (map_ofReal_freeCumulantSeries_law φ ha)

end PositiveLinearMap

namespace MeasureTheory.Measure

private theorem map_ofRealHom_injective {f g : ℝ⟦X⟧}
    (h : f.map Complex.ofRealHom = g.map Complex.ofRealHom) : f = g := by
  ext n
  exact Complex.ofReal_injective (by simpa using congrArg (coeff n) h)

section Determinacy

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Two compactly supported probability measures on `ℝ` have equal moment series if and only if
they are equal. -/
theorem momentSeries_eq_iff (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ.momentSeries = ν.momentSeries ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (hμ.union hν) ?_ ?_ fun n => ?_
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_left) μ.measure_compl_support
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_right)
      ν.measure_compl_support
  · simpa using congrArg (coeff n) h

/-- Two compactly supported probability measures on `ℝ` have equal free cumulant series if and only
if they are equal. -/
theorem freeCumulantSeries_eq_iff (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ.freeCumulantSeries = ν.freeCumulantSeries ↔ μ = ν := by
  rw [freeCumulantSeries, freeCumulantSeries,
    TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq id (by simp [integral_const])
      (by simp [integral_const]),
    ← momentSeries, ← momentSeries, momentSeries_eq_iff hμ hν]

/-- Two compactly supported probability measures on `ℝ` have equal R-series if and only if they are
equal. -/
theorem rSeries_eq_iff (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ.rSeries = ν.rSeries ↔ μ = ν := by
  rw [rSeries, rSeries,
    TauCeti.rSeries_eq_iff_momentSeries_eq id (by simp [integral_const])
      (by simp [integral_const]),
    ← momentSeries, ← momentSeries, momentSeries_eq_iff hμ hν]

/-- Two compactly supported probability measures on `ℝ` agree on all positive-order free cumulants
if and only if they are equal. -/
theorem forall_freeCumulant_eq_iff (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    (∀ n : ℕ, n ≠ 0 → μ.freeCumulant n = ν.freeCumulant n) ↔ μ = ν := by
  rw [← freeCumulantSeries_eq_iff hμ hν, PowerSeries.ext_iff]
  refine ⟨fun h n => ?_, fun h n _ => by simpa using h n⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa using h n hn

end Determinacy

section AffineAndExamples

private theorem constantCoeff_rescale_eq {R : Type*} [CommSemiring R] (a : R) (f : R⟦X⟧) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff]

private theorem integrable_pow_of_isCompact_support {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) : Integrable (fun x => x ^ n) μ := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hμ.isBounded
  refine Integrable.of_bound (by fun_prop) (max r 0 ^ n) ?_
  filter_upwards [ae_iff.2 μ.measure_compl_support] with x hx
  have hxr : ‖x‖ ≤ max r 0 := (mem_closedBall_zero_iff.1 (hr hx)).trans (le_max_left r 0)
  simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg x) hxr n

/-- Under an affine pushforward `x ↦ a + b * x`, the R-series of any probability measure on `ℝ`
with finite moments of all orders transforms by `R_{a + b X}(z) = a + b R_X(b z)`. -/
theorem rSeries_map_affine_of_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ n : ℕ, Integrable (fun x => x ^ n) μ) (a b : ℝ) :
    (μ.map fun x => a + b * x).rSeries = PowerSeries.C a + b • rescale b μ.rSeries := by
  have hint (p : Polynomial ℝ) : Integrable (fun x => p.eval x) μ := by
    simp_rw [Polynomial.eval_eq_sum_range]
    exact integrable_finsetSum _ fun n _ => (hμ n).const_mul _
  let ψ : Polynomial ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun p => ∫ x, p.eval x ∂μ
      map_add' := fun p q => by
        simp_rw [Polynomial.eval_add]
        exact integral_add (hint p) (hint q)
      map_smul' := fun c p => by
        simp_rw [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hψ1 : ψ 1 = 1 := by simp [ψ, integral_const]
  have hMX : TauCeti.momentSeries ψ Polynomial.X =
      TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
    ext n
    simp [ψ]
  have hMaff : TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.map fun x => a + b * x)) id =
      TauCeti.momentSeries ψ (b • Polynomial.X + algebraMap ℝ (Polynomial ℝ) a) := by
    ext n
    rw [TauCeti.coeff_momentSeries, TauCeti.coeff_momentSeries]
    simp_rw [Pi.pow_apply, id_eq]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [ψ, add_comm]
  rw [rSeries, TauCeti.rSeries_congr _ _ hMaff, TauCeti.rSeries_add_algebraMap hψ1,
    TauCeti.rSeries_smul, TauCeti.rSeries_congr _ _ hMX, ← rSeries, add_comm]

/-- Under an affine pushforward `x ↦ a + b * x`, the R-series of a compactly supported probability
measure transforms by `R_{a + b X}(z) = a + b R_X(b z)`. -/
theorem rSeries_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (a b : ℝ) :
    (μ.map fun x => a + b * x).rSeries = PowerSeries.C a + b • rescale b μ.rSeries :=
  rSeries_map_affine_of_integrable (integrable_pow_of_isCompact_support hμ) a b

/-- Under `x ↦ a + b * x`, free cumulants of order `n ≥ 2` of any probability measure with finite
moments of all orders scale by `b ^ n`, while the first cumulant becomes `a + b * κ₁(μ)`. -/
theorem freeCumulant_map_affine_of_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ k : ℕ, Integrable (fun x => x ^ k) μ) (a b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (μ.map fun x => a + b * x).freeCumulant n =
      (if n = 1 then a else 0) + b ^ n * μ.freeCumulant n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← coeff_rSeries, rSeries_map_affine_of_integrable hμ a b]
  rcases m with _ | m
  · simp [constantCoeff_rescale_eq]
  · simp [pow_succ', mul_assoc]

/-- Under `x ↦ a + b * x`, free cumulants of order `n ≥ 2` of a compactly supported probability
measure scale by `b ^ n`, while the first cumulant becomes `a + b * κ₁(μ)`. -/
theorem freeCumulant_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (a b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (μ.map fun x => a + b * x).freeCumulant n =
      (if n = 1 then a else 0) + b ^ n * μ.freeCumulant n :=
  freeCumulant_map_affine_of_integrable (integrable_pow_of_isCompact_support hμ) a b hn

/-- The R-series of the point mass at `0` vanishes. -/
theorem rSeries_dirac_zero : (Measure.dirac (0 : ℝ)).rSeries = 0 := by
  have h : Measure.dirac (0 : ℝ) = (Measure.dirac (0 : ℝ)).map fun x => 0 + 0 * x := by simp
  conv_lhs => rw [h]
  rw [rSeries_map_affine_of_integrable (fun _ => integrable_dirac (by simp))]
  simp

/-- The R-series of the point mass at `c` is the constant power series `c`. -/
@[simp]
theorem rSeries_dirac (c : ℝ) : (Measure.dirac c).rSeries = PowerSeries.C c := by
  have h : Measure.dirac c = (Measure.dirac (0 : ℝ)).map fun x => c + 0 * x := by simp
  rw [h, rSeries_map_affine_of_integrable (fun _ => integrable_dirac (by simp)), rSeries_dirac_zero]
  simp

/-- The positive-order free cumulants of `Measure.dirac c` are `c` at `n = 1` and `0` for
`n ≥ 2`. -/
theorem freeCumulant_dirac (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (Measure.dirac c).freeCumulant n = if n = 1 then c else 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← coeff_rSeries, rSeries_dirac]
  rcases m with _ | m <;> simp

/-- The R-series of the semicircle law `semicircleReal a v` with centre `a` and variance `v` is the
linear polynomial `a + v z`. -/
@[simp]
theorem rSeries_semicircleReal (a : ℝ) (v : ℝ≥0) :
    (TauCeti.Probability.semicircleReal a v).rSeries =
      PowerSeries.C a + PowerSeries.C (v : ℝ) * X := by
  have h0 : (TauCeti.Probability.semicircleReal 0 v).rSeries = PowerSeries.C (v : ℝ) * X := by
    let K : Set ℝ := Set.Icc (-(2 * Real.sqrt v)) (2 * Real.sqrt v)
    have : CompactSpace K := isCompact_iff_compactSpace.1 isCompact_Icc
    let φ : C(K, ℂ) →ₚ[ℂ] ℂ := ContinuousMap.integralPositiveLinearMap
      ((TauCeti.Probability.semicircleReal 0 v).comap ((↑) : K → ℝ))
    let x : C(K, ℂ) := (ContinuousMap.restrict K (ContinuousMap.id ℝ)).realToRCLike ℂ
    have hlaw : φ.law x = TauCeti.Probability.semicircleReal 0 v :=
      PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
        (by simpa only [K, zero_sub, zero_add, Set.ofPred_mem_eq] using
          mem_ae_iff.1 (TauCeti.Probability.ae_mem_Icc_semicircleReal 0 v))
    have hsc : TauCeti.IsSemicircular φ.toLinearMap x ((v : ℝ) : ℂ) :=
      TauCeti.isSemicircular_integralPositiveLinearMap_semicircleReal v
    apply map_ofRealHom_injective
    rw [← hlaw, φ.map_ofReal_rSeries_law (ContinuousMap.isSelfAdjoint_realToRCLike ℂ)]
    ext n
    have hκ := hsc.freeCumulant_const (Finset.univ_nonempty (α := Fin (n + 1)))
    rw [Finset.card_univ, Fintype.card_fin] at hκ
    rw [TauCeti.coeff_rSeries, hκ]
    rcases n with _ | _ | n <;> simp
  have haff : TauCeti.Probability.semicircleReal a v =
      (TauCeti.Probability.semicircleReal 0 v).map fun x => a + 1 * x := by
    rw [TauCeti.Probability.map_affine_semicircleReal]
    simp
  rw [haff,
    rSeries_map_affine_of_integrable (TauCeti.Probability.integrable_pow_semicircleReal 0 v),
    h0, rescale_one, RingHom.id_apply, one_smul]

/-- The positive-order free cumulants of `semicircleReal a v` are `a` at `n = 1`, `v` at `n = 2`,
and `0` for `n ≥ 3`. -/
theorem freeCumulant_semicircleReal (a : ℝ) (v : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    (TauCeti.Probability.semicircleReal a v).freeCumulant n =
      if n = 1 then a else if n = 2 then (v : ℝ) else 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← coeff_rSeries, rSeries_semicircleReal]
  rcases m with _ | _ | m <;> simp

end AffineAndExamples

end MeasureTheory.Measure
