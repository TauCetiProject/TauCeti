/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Robba.Basic
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Order.Interval.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Compact Laurent annuli

Over a complete ultrametric normed field, the coefficient families converging at both endpoints
of a positive compact interval form a Banach algebra for the maximum of the endpoint Gauss norms.
Equal endpoints are allowed, so circles are included. Restriction to a smaller interval preserves
coefficients.

These are the compact annular factors used in the projective presentation of analytic functions
on an open annulus.

## References

* K. S. Kedlaya, *Slope filtrations revisited*, §2.4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*, §2.
-/

public section

open Filter Topology

namespace TauCeti

/-- Nonempty compact intervals of positive Laurent radii, ordered by inclusion. -/
abbrev CompactAnnulus := NonemptyInterval (Set.Ioi (0 : ℝ))

namespace CompactAnnulus

/-- The inner Laurent radius. -/
abbrev inner (A : CompactAnnulus) : ℝ := A.fst.val

/-- The outer Laurent radius. -/
abbrev outer (A : CompactAnnulus) : ℝ := A.snd.val

end CompactAnnulus

variable {R : Type*}

/-- A Laurent weight inside a positive interval is bounded by an endpoint weight. -/
private theorem laurentWeight_le_max {α ρ β : ℝ} (hα : 0 < α) (hαρ : α ≤ ρ) (hρβ : ρ ≤ β)
    (n : ℤ) : ρ ^ n ≤ max (α ^ n) (β ^ n) := by
  rcases le_total 0 n with hn | hn
  · exact (zpow_le_zpow_left₀ hn (hα.trans_le hαρ).le hρβ).trans (le_max_right _ _)
  · have h := inv_anti₀ (zpow_pos hα (-n)) (zpow_le_zpow_left₀ (neg_nonneg.mpr hn) hα.le hαρ)
    simpa only [zpow_neg, inv_inv] using h.trans (le_max_left _ _)

/-- Endpoint convergence implies convergence at every intermediate radius. -/
theorem LaurentConvergesAt.of_endpoints [SeminormedAddGroup R] {α ρ β : ℝ}
    (hα : 0 < α) (hαρ : α ≤ ρ) (hρβ : ρ ≤ β) {a : ℤ → R}
    (ha : LaurentConvergesAt α a) (hb : LaurentConvergesAt β a) : LaurentConvergesAt ρ a := by
  rw [laurentConvergesAt_iff]
  have hmax : Tendsto (fun n ↦ max (‖a n‖ * α ^ n) (‖a n‖ * β ^ n)) cofinite (𝓝 0) := by
    simpa only [max_self] using (laurentConvergesAt_iff.mp ha).max (laurentConvergesAt_iff.mp hb)
  refine squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos (hα.trans_le hαρ) n).le)
    (fun n ↦ ?_) hmax
  rw [← mul_max_of_nonneg _ _ (norm_nonneg (a n))]
  exact mul_le_mul_of_nonneg_left (laurentWeight_le_max hα hαρ hρβ n) (norm_nonneg _)

/-- Every intermediate Gauss norm is bounded by the maximum of the endpoint Gauss norms. -/
theorem laurentGaussNorm_le_max_endpoints [SeminormedAddGroup R] {α ρ β : ℝ}
    (hα : 0 < α) (hαρ : α ≤ ρ) (hρβ : ρ ≤ β) {a : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * α ^ n))
    (hb : BddAbove (Set.range fun n ↦ ‖a n‖ * β ^ n)) :
    laurentGaussNorm ρ a ≤ max (laurentGaussNorm α a) (laurentGaussNorm β a) := by
  refine laurentGaussNorm_le fun n ↦ ?_
  calc ‖a n‖ * ρ ^ n ≤ ‖a n‖ * max (α ^ n) (β ^ n) :=
        mul_le_mul_of_nonneg_left (laurentWeight_le_max hα hαρ hρβ n) (norm_nonneg _)
    _ = max (‖a n‖ * α ^ n) (‖a n‖ * β ^ n) := mul_max_of_nonneg _ _ (norm_nonneg _)
    _ ≤ _ := max_le_max (le_laurentGaussNorm ha n) (le_laurentGaussNorm hb n)

/-- Laurent coefficient families converging on the compact annulus, specified at its endpoints. -/
def compactAnnularCoeff (R : Type*) [SeminormedRing R] (A : CompactAnnulus) :
    Submodule R (ℤ → R) where
  carrier := {a | LaurentConvergesAt A.inner a ∧ LaurentConvergesAt A.outer a}
  zero_mem' := ⟨laurentConvergesAt_zero _, laurentConvergesAt_zero _⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  smul_mem' c _ ha := ⟨ha.1.smul c, ha.2.smul c⟩

/-- Membership is equivalent to Laurent convergence at both endpoints. -/
@[simp]
theorem mem_compactAnnularCoeff [SeminormedRing R] {A : CompactAnnulus} {a : ℤ → R} :
    a ∈ compactAnnularCoeff R A ↔
      LaurentConvergesAt A.inner a ∧ LaurentConvergesAt A.outer a := (Iff.rfl)

/-- Endpoint convergence is equivalent to convergence throughout the closed interval. -/
theorem mem_compactAnnularCoeff_iff_forall [SeminormedRing R] {A : CompactAnnulus}
    {a : ℤ → R} : a ∈ compactAnnularCoeff R A ↔
      ∀ ρ ∈ Set.Icc A.inner A.outer, LaurentConvergesAt ρ a := by
  constructor
  · intro ha ρ hρ
    exact ha.1.of_endpoints A.fst.property hρ.1 hρ.2 ha.2
  · intro ha
    exact ⟨ha _ ⟨le_rfl, A.fst_le_snd⟩, ha _ ⟨A.fst_le_snd, le_rfl⟩⟩

instance instIsConvolutionRingCompactAnnularCoeff [SeminormedRing R] [IsUltrametricDist R]
    [CompleteSpace R] (A : CompactAnnulus) : IsConvolutionRing (compactAnnularCoeff R A) where
  single_mem n c := ⟨laurentConvergesAt_single _ n c, laurentConvergesAt_single _ n c⟩
  addRingConvolution_mem ha hb :=
    ⟨ha.1.addRingConvolution A.fst.property hb.1, ha.2.addRingConvolution A.snd.property hb.2⟩
  addConvolutionExists ha hb := ha.1.addConvolutionExists A.fst.property hb.1
  summable_sigma_addFiber_mul_mul ha hb hc :=
    ha.1.summable_sigma_addFiber_mul_mul A.fst.property hb.1 hc.1

namespace compactAnnularCoeff

variable [SeminormedRing R] {A : CompactAnnulus}

/-- The endpoint-weighted coefficients of a chart vanish outside finite subsets of degrees. -/
theorem tendsto_norm_coeff (f : compactAnnularCoeff R A) :
    Tendsto (fun n ↦ ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n)) cofinite (𝓝 0) := by
  simp_rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
  simpa only [max_self] using
    (laurentConvergesAt_iff.mp f.property.1).max (laurentConvergesAt_iff.mp f.property.2)

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R] {A : CompactAnnulus}

private noncomputable def endpointNorm (f : compactAnnularCoeff R A) : ℝ :=
  max (laurentGaussNorm A.inner (f : ℤ → R)) (laurentGaussNorm A.outer (f : ℤ → R))

omit [IsUltrametricDist R] [CompleteSpace R] in
private theorem endpointNorm_nonneg (f : compactAnnularCoeff R A) : 0 ≤ endpointNorm f := by
  exact (laurentGaussNorm_nonneg A.inner (f : ℤ → R)).trans (le_max_left _ _)

omit [CompleteSpace R] in
private theorem endpointNorm_add_le (f g : compactAnnularCoeff R A) :
    endpointNorm (f + g) ≤ max (endpointNorm f) (endpointNorm g) := by
  dsimp only [endpointNorm]
  apply max_le
  · exact (laurentGaussNorm_add_le A.fst.property.le
      f.property.1.bddAbove g.property.1.bddAbove).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact (laurentGaussNorm_add_le A.snd.property.le
      f.property.2.bddAbove g.property.2.bddAbove).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _))

/-- The compact annular norm is the maximum of the two endpoint Gauss norms. -/
noncomputable instance instNormedRing : NormedRing (compactAnnularCoeff R A) := by
  exact RingNorm.toNormedRing
    { toFun f := max (laurentGaussNorm A.inner (f : ℤ → R))
          (laurentGaussNorm A.outer (f : ℤ → R))
      map_zero' := by simp
      neg' f := by simp
      add_le' f g := by
        exact (endpointNorm_add_le f g).trans
          (max_le_add_of_nonneg (endpointNorm_nonneg f) (endpointNorm_nonneg g))
      mul_le' f g := by
        apply max_le
        · exact (laurentGaussNorm_addRingConvolution_le A.fst.property
            f.property.1.bddAbove g.property.1.bddAbove).trans
            (mul_le_mul (le_max_left _ _) (le_max_left _ _)
              (laurentGaussNorm_nonneg _ _) (endpointNorm_nonneg _))
        · exact (laurentGaussNorm_addRingConvolution_le A.snd.property
            f.property.2.bddAbove g.property.2.bddAbove).trans
            (mul_le_mul (le_max_right _ _) (le_max_right _ _)
              (laurentGaussNorm_nonneg _ _) (endpointNorm_nonneg _))
      eq_zero_of_map_eq_zero' f hf := by
        apply Subtype.ext
        funext n
        have h := (le_laurentGaussNorm f.property.1.bddAbove n).trans
          ((le_max_left _ _).trans_eq hf)
        exact norm_eq_zero.mp (le_antisymm
          ((mul_le_mul_iff_left₀ (zpow_pos A.fst.property n)).mp
            (by simpa [mul_comm] using h)) (norm_nonneg _)) }

-- The explicit projections select the norm uniformity on the chart's coefficient subtype.
/-- The metric on a compact annulus is the metric of its endpoint maximum norm. -/
noncomputable instance instMetricSpace : MetricSpace (compactAnnularCoeff R A) :=
  instNormedRing.toMetricSpace

/-- The compact annular uniformity is induced by the endpoint maximum norm. -/
noncomputable instance instUniformSpace : UniformSpace (compactAnnularCoeff R A) :=
  instMetricSpace.toUniformSpace

/-- The compact annular topology is induced by the endpoint maximum norm. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (compactAnnularCoeff R A) :=
  instUniformSpace.toTopologicalSpace

/-- Characteristic equation for the compact annular norm. -/
theorem norm_eq (f : compactAnnularCoeff R A) :
    ‖f‖ = max (laurentGaussNorm A.inner (f : ℤ → R)) (laurentGaussNorm A.outer (f : ℤ → R)) := (rfl)

/-- Every endpoint weighted coefficient is bounded by the annular norm. -/
theorem norm_coeff_le (f : compactAnnularCoeff R A) (n : ℤ) :
    ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ ‖f‖ := by
  rw [norm_eq, mul_max_of_nonneg _ _ (norm_nonneg _)]
  exact max_le_max (le_laurentGaussNorm f.property.1.bddAbove n)
    (le_laurentGaussNorm f.property.2.bddAbove n)

/-- Bounds on the annular norm are exactly uniform bounds on the weighted coefficients. -/
theorem norm_le_iff {f : compactAnnularCoeff R A} {C : ℝ} :
    ‖f‖ ≤ C ↔ ∀ n, ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ C := by
  constructor
  · exact fun h n ↦ (norm_coeff_le f n).trans h
  · intro h
    rw [norm_eq]
    refine max_le (laurentGaussNorm_le fun n ↦ ?_) (laurentGaussNorm_le fun n ↦ ?_)
    · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)).trans (h n)
    · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)).trans (h n)

/-- The coefficient ring acts boundedly, also when it is not commutative. -/
private theorem norm_smul_le (c : R) (f : compactAnnularCoeff R A) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  refine norm_le_iff.mpr fun n ↦ ?_
  calc ‖((c • f : compactAnnularCoeff R A) : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n)
      ≤ ‖c‖ * (‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          ((zpow_pos A.fst.property n).le.trans (le_max_left _ _))
    _ ≤ ‖c‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coeff_le f n) (norm_nonneg c)

instance instIsBoundedSMul : IsBoundedSMul R (compactAnnularCoeff R A) := by
  exact IsBoundedSMul.of_norm_smul_le norm_smul_le

/-- Each Laurent coefficient is uniformly continuous for the compact annular norm. -/
theorem uniformContinuous_coeff (n : ℤ) :
    UniformContinuous fun f : compactAnnularCoeff R A ↦ (f : ℤ → R) n := by
  let ev : compactAnnularCoeff R A →+ R :=
    { toFun := fun f ↦ (f : ℤ → R) n
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  refine AddMonoidHomClass.uniformContinuous_of_bound ev
    (max (A.inner ^ n) (A.outer ^ n))⁻¹ fun f ↦ ?_
  rw [inv_mul_eq_div, le_div_iff₀ ((zpow_pos A.fst.property n).trans_le (le_max_left _ _))]
  exact norm_coeff_le f n

instance instIsUltrametricDist : IsUltrametricDist (compactAnnularCoeff R A) := by
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm endpointNorm_add_le

/-- The norm of a Laurent monomial, including negative exponents. -/
@[simp]
theorem norm_monomial (n : ℤ) (c : R) :
    ‖(IsConvolutionRing.monomial n c : compactAnnularCoeff R A)‖ =
      ‖c‖ * max (A.inner ^ n) (A.outer ^ n) := by
  simp only [norm_eq, IsConvolutionRing.coe_monomial,
    laurentGaussNorm_single A.fst.property.le, laurentGaussNorm_single A.snd.property.le,
    mul_max_of_nonneg _ _ (norm_nonneg _)]

/-- The annular norm preserves the unit norm of the coefficient ring. -/
instance instNormOneClass [NormOneClass R] : NormOneClass (compactAnnularCoeff R A) where
  norm_one := by
    rw [← IsConvolutionRing.monomial_zero_one, norm_monomial]
    simp

private theorem exists_limit (F : ℕ → compactAnnularCoeff R A) (hF : CauchySeq F) :
    ∃ a : ℤ → R, a ∈ compactAnnularCoeff R A ∧ ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ n,
      ‖(F k : ℤ → R) n - a n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ ε := by
  let w : ℤ → ℝ := fun n ↦ max (A.inner ^ n) (A.outer ^ n)
  have hw (n : ℤ) : 0 ≤ w n := (zpow_pos A.fst.property n).le.trans (le_max_left _ _)
  obtain ⟨a, hunif⟩ := TauCeti.MvPowerSeries.exists_weighted_uniform_limit w
    (fun k ↦ (F k : ℤ → R)) (by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
      refine ⟨N, fun k hk l hl n ↦ ?_⟩
      exact (norm_coeff_le (F k - F l) n).trans_lt
        ((dist_eq_norm _ _).symm.trans_lt (hN k hk l hl)))
  have ha : Tendsto (fun n ↦ ‖a n‖ * w n) cofinite (𝓝 0) := by
    refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun n ↦
      hb.trans_le (mul_nonneg (norm_nonneg _) (hw n)), fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [(tendsto_norm_coeff (F N)).eventually (gt_mem_nhds (half_pos hε))] with n hn
    calc ‖a n‖ * w n ≤ ‖(F N : ℤ → R) n‖ * w n +
        ‖(F N : ℤ → R) n - a n‖ * w n := by
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _) (hw n)
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hn (hN N le_rfl n)
      _ = ε := add_halves ε
  refine ⟨a, ⟨?_, ?_⟩, hunif⟩
  · apply laurentConvergesAt_iff.mpr
    exact squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos A.fst.property n).le)
      (fun n ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)) ha
  · apply laurentConvergesAt_iff.mpr
    exact squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos A.snd.property n).le)
      (fun n ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)) ha

/-- Compact Laurent annuli are complete over a complete coefficient ring. -/
instance instCompleteSpace : CompleteSpace (compactAnnularCoeff R A) := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  obtain ⟨a, ha, hunif⟩ := exists_limit F hF
  refine ⟨⟨a, ha⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff]
  exact hN k hk

/-- The Laurent polynomial retaining precisely the degrees in `s`. -/
def truncate (s : Finset ℤ) (f : compactAnnularCoeff R A) : compactAnnularCoeff R A :=
  ∑ n ∈ s, IsConvolutionRing.monomial n ((f : ℤ → R) n)

/-- Finite Laurent truncation retains its chosen coefficients and kills the others. -/
@[simp]
theorem coe_truncate_apply (s : Finset ℤ) (f : compactAnnularCoeff R A) (n : ℤ) :
    (truncate s f : ℤ → R) n = if n ∈ s then (f : ℤ → R) n else 0 := by
  classical
  simp [truncate, Finset.sum_apply, Pi.single_apply]

/-- Finite Laurent truncations converge in the annular norm. -/
theorem tendsto_truncate (f : compactAnnularCoeff R A) :
    Tendsto (fun s : Finset ℤ ↦ truncate s f) atTop (𝓝 f) := by
  classical
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  have hs : {n | ε / 2 ≤ ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n)}.Finite := by
    simpa only [eventually_cofinite, not_lt] using
      (tendsto_norm_coeff f).eventually (gt_mem_nhds (half_pos hε))
  refine ⟨hs.toFinset, fun s hss ↦ ?_⟩
  rw [dist_eq_norm]
  refine (norm_le_iff.mpr fun n ↦ ?_).trans_lt (half_lt_self hε)
  by_cases hn : n ∈ s
  · simpa [coe_truncate_apply, hn] using (half_pos hε).le
  · simpa [Submodule.coe_sub, coe_truncate_apply, hn] using
      (not_le.mp fun h ↦ hn (hss (hs.mem_toFinset.mpr h))).le

/-- Laurent polynomials, viewed as coefficient families of finite support, are dense. -/
theorem dense_finiteSupport :
    Dense {f : compactAnnularCoeff R A | (Function.support (f : ℤ → R)).Finite} := by
  intro f
  apply mem_closure_of_tendsto (tendsto_truncate f)
  apply Eventually.of_forall
  intro s
  exact s.finite_toSet.subset fun n hn ↦ by
    by_contra hns
    have hns' : n ∉ s := hns
    exact hn (by simp [coe_truncate_apply, hns'])

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {A B C : CompactAnnulus}

/-- The compact annular norm is compatible with the convolution commutative ring. -/
noncomputable instance instNormedCommRing : NormedCommRing (compactAnnularCoeff R A) :=
  { instNormedRing with mul_comm := mul_comm }

/-- Constant Laurent series retain their coefficient norm. -/
@[simp]
theorem norm_algebraMap (c : R) : ‖algebraMap R (compactAnnularCoeff R A) c‖ = ‖c‖ := by
  rw [← IsConvolutionRing.monomial_zero_left, norm_monomial]
  simp

/-- Coefficientwise restriction from a compact annulus to a smaller compact annulus. -/
def restrict (h : B ≤ A) : compactAnnularCoeff R A →ₐ[R] compactAnnularCoeff R B where
  toFun f := by
    have h := NonemptyInterval.le_def.mp h
    exact ⟨f, (mem_compactAnnularCoeff_iff_forall.mp f.property _
      ⟨h.1, B.fst_le_snd.trans h.2⟩),
    (mem_compactAnnularCoeff_iff_forall.mp f.property _
      ⟨h.1.trans B.fst_le_snd, h.2⟩)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Restriction leaves the coefficient family unchanged. -/
@[simp]
theorem coe_restrict (h : B ≤ A) (f : compactAnnularCoeff R A) :
    (restrict h f : ℤ → R) = (f : ℤ → R) := (rfl)

/-- Restriction is contractive for the endpoint maximum norms. -/
theorem norm_restrict_le (h : B ≤ A) (f : compactAnnularCoeff R A) :
    ‖restrict h f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq, coe_restrict]
  have h := NonemptyInterval.le_def.mp h
  exact max_le
    (laurentGaussNorm_le_max_endpoints A.fst.property h.1
      (B.fst_le_snd.trans h.2) f.property.1.bddAbove f.property.2.bddAbove)
    (laurentGaussNorm_le_max_endpoints A.fst.property (h.1.trans B.fst_le_snd)
      h.2 f.property.1.bddAbove f.property.2.bddAbove)

/-- Restriction is uniformly continuous for the annular norm uniformities. -/
theorem uniformContinuous_restrict (h : B ≤ A) :
    UniformContinuous (restrict (R := R) h) :=
  AddMonoidHomClass.uniformContinuous_of_bound (restrict h) 1 fun f ↦ by
    simpa only [one_mul] using norm_restrict_le h f

/-- Restriction retains every Laurent coefficient, so it is injective. -/
theorem restrict_injective (h : B ≤ A) : Function.Injective (restrict (R := R) h) := by
  intro f g hfg
  apply Subtype.ext
  simpa only [coe_restrict] using congrArg (fun a : compactAnnularCoeff R B ↦ (a : ℤ → R)) hfg

@[simp]
theorem restrict_self : restrict (R := R) (A := A) le_rfl = AlgHom.id R _ := by
  ext f n
  rfl

/-- Restrictions compose coefficientwise. -/
theorem restrict_comp (hAB : B ≤ A) (hBC : C ≤ B) :
    (restrict (R := R) hBC).comp (restrict hAB) = restrict (hBC.trans hAB) := by
  ext f n
  rfl

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedField R] [IsUltrametricDist R] [CompleteSpace R] {A : CompactAnnulus}

/-- Compact annuli over a complete ultrametric field are normed algebras over that field. -/
noncomputable instance instNormedAlgebra : NormedAlgebra R (compactAnnularCoeff R A) where
  toAlgebra := inferInstance
  norm_smul_le := _root_.norm_smul_le

end compactAnnularCoeff

end TauCeti
