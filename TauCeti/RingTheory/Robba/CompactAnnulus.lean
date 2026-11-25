/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.Interval.Basic
public import TauCeti.RingTheory.Robba.LaurentGauss
import Mathlib.Analysis.Normed.Group.Seminorm
import TauCeti.Analysis.Normed.Group.WeightedLimit

/-!
# Compact Laurent annuli

Over a complete ultrametric normed field, the coefficient families converging at both endpoints
of a positive compact interval form a Banach algebra for the maximum of the endpoint Gauss norms.
Equal endpoints are allowed, so circles are included. Restriction to a smaller interval preserves
coefficients. The additive norm only requires a normed coefficient ring.

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

/-- Shrinking the interval enlarges the submodule of convergent coefficient families. -/
theorem compactAnnularCoeff_anti [SeminormedRing R] {A B : CompactAnnulus} (h : B ≤ A) :
    compactAnnularCoeff R A ≤ compactAnnularCoeff R B := by
  intro f hf
  have h := NonemptyInterval.le_def.mp h
  exact ⟨mem_compactAnnularCoeff_iff_forall.mp hf _ ⟨h.1, B.fst_le_snd.trans h.2⟩,
    mem_compactAnnularCoeff_iff_forall.mp hf _ ⟨h.1.trans B.fst_le_snd, h.2⟩⟩

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
theorem tendsto_norm_coeff_mul_max (f : compactAnnularCoeff R A) :
    Tendsto (fun n ↦ ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n)) cofinite (𝓝 0) :=
  (laurentConvergesAt_endpoints_iff A.fst.property A.snd.property).mp f.property

/-- The Laurent polynomial retaining precisely the degrees in `s`. -/
def truncate (s : Finset ℤ) (f : compactAnnularCoeff R A) : compactAnnularCoeff R A :=
  ∑ n ∈ s, ⟨Pi.single n ((f : ℤ → R) n),
    laurentConvergesAt_single _ n _, laurentConvergesAt_single _ n _⟩

/-- Finite Laurent truncation retains its chosen coefficients and kills the others. -/
@[simp]
theorem coe_truncate_apply (s : Finset ℤ) (f : compactAnnularCoeff R A) (n : ℤ) :
    (truncate s f : ℤ → R) n = if n ∈ s then (f : ℤ → R) n else 0 := by
  classical
  simp [truncate, Finset.sum_apply, Pi.single_apply]

/-- Truncation to the empty set of degrees is zero. -/
@[simp]
theorem truncate_empty (f : compactAnnularCoeff R A) : truncate ∅ f = 0 := by
  simp [truncate]

/-- Coefficient inclusion commutes with truncation to a finite set of degrees. -/
@[simp]
theorem inclusion_truncate {B : CompactAnnulus} (h : compactAnnularCoeff R A ≤
    compactAnnularCoeff R B) (s : Finset ℤ) (f : compactAnnularCoeff R A) :
    Submodule.inclusion h (truncate s f) = truncate s (Submodule.inclusion h f) := by
  ext n
  simp

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedRing R] {A : CompactAnnulus}

private theorem endpointNorm_le_iff {f : compactAnnularCoeff R A} {C : ℝ} :
    max (laurentGaussNorm A.inner (f : ℤ → R)) (laurentGaussNorm A.outer (f : ℤ → R)) ≤ C ↔
      ∀ n, ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ C := by
  simp only [max_le_iff, laurentGaussNorm_le_iff f.property.1.bddAbove,
    laurentGaussNorm_le_iff f.property.2.bddAbove,
    mul_max_of_nonneg _ _ (norm_nonneg _), forall_and]

/-- The endpoint maximum norm gives a normed additive group over any normed coefficient ring. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (compactAnnularCoeff R A) := by
  exact AddGroupNorm.toNormedAddCommGroup
    { toFun f := max (laurentGaussNorm A.inner (f : ℤ → R))
          (laurentGaussNorm A.outer (f : ℤ → R))
      map_zero' := by simp
      neg' f := by simp
      add_le' f g := by
        refine endpointNorm_le_iff.mpr fun n ↦ ?_
        rw [Submodule.coe_add, Pi.add_apply]
        have hw : 0 ≤ max (A.inner ^ n) (A.outer ^ n) :=
          (zpow_pos A.fst.property n).le.trans (le_max_left _ _)
        calc
          _ ≤ (‖(f : ℤ → R) n‖ + ‖(g : ℤ → R) n‖) * max (A.inner ^ n) (A.outer ^ n) :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
          _ ≤ _ := by
            rw [add_mul]
            exact add_le_add ((endpointNorm_le_iff (f := f)).mp le_rfl n)
              ((endpointNorm_le_iff (f := g)).mp le_rfl n)
      eq_zero_of_map_eq_zero' f hf := by
        apply Subtype.ext
        funext n
        have h := (le_laurentGaussNorm f.property.1.bddAbove n).trans
          ((le_max_left _ _).trans_eq hf)
        exact norm_eq_zero.mp (le_antisymm
          ((mul_le_mul_iff_left₀ (zpow_pos A.fst.property n)).mp
            (by simpa [mul_comm] using h)) (norm_nonneg _)) }

-- These projections select the endpoint norm topology on the coefficient subtype.
/-- The metric on a compact annulus is the metric of its endpoint maximum norm. -/
noncomputable instance instMetricSpace : MetricSpace (compactAnnularCoeff R A) :=
  instNormedAddCommGroup.toMetricSpace

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
theorem norm_coeff_mul_max_le (f : compactAnnularCoeff R A) (n : ℤ) :
    ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ ‖f‖ := by
  rw [norm_eq, mul_max_of_nonneg _ _ (norm_nonneg _)]
  exact max_le_max (le_laurentGaussNorm f.property.1.bddAbove n)
    (le_laurentGaussNorm f.property.2.bddAbove n)

/-- Bounds on the annular norm are exactly uniform bounds on the weighted coefficients. -/
theorem norm_le_iff {f : compactAnnularCoeff R A} {C : ℝ} :
    ‖f‖ ≤ C ↔ ∀ n, ‖(f : ℤ → R) n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ C := by
  rw [norm_eq, endpointNorm_le_iff]

/-- The coefficient ring acts boundedly, also when it is not commutative. -/
private theorem norm_smul_le (c : R) (f : compactAnnularCoeff R A) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  simp only [norm_eq, Submodule.coe_smul, mul_max_of_nonneg _ _ (norm_nonneg c)]
  exact max_le_max
    (laurentGaussNorm_smul_le A.fst.property.le f.property.1.bddAbove c)
    (laurentGaussNorm_smul_le A.snd.property.le f.property.2.bddAbove c)

instance instIsBoundedSMul : IsBoundedSMul R (compactAnnularCoeff R A) := by
  exact IsBoundedSMul.of_norm_smul_le norm_smul_le

/-- Each Laurent coefficient is uniformly continuous for the compact annular norm. -/
theorem uniformContinuous_coeff (n : ℤ) :
    UniformContinuous fun f : compactAnnularCoeff R A ↦ (f : ℤ → R) n := by
  let ev := ((LinearMap.proj n).comp (compactAnnularCoeff R A).subtype).toAddMonoidHom
  refine AddMonoidHomClass.uniformContinuous_of_bound ev
    (max (A.inner ^ n) (A.outer ^ n))⁻¹ fun f ↦ ?_
  rw [inv_mul_eq_div, le_div_iff₀ ((zpow_pos A.fst.property n).trans_le (le_max_left _ _))]
  exact norm_coeff_mul_max_le f n

/-- The endpoint maximum norm is ultrametric whenever the coefficient norm is. -/
instance instIsUltrametricDist [IsUltrametricDist R] :
    IsUltrametricDist (compactAnnularCoeff R A) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g ↦ by
    simp only [norm_eq, Submodule.coe_add]
    exact max_le
      ((laurentGaussNorm_add_le A.fst.property.le
        f.property.1.bddAbove g.property.1.bddAbove).trans
        (max_le_max (le_max_left _ _) (le_max_left _ _)))
      ((laurentGaussNorm_add_le A.snd.property.le
        f.property.2.bddAbove g.property.2.bddAbove).trans
        (max_le_max (le_max_right _ _) (le_max_right _ _)))

section CompleteSpace

variable [CompleteSpace R]

private theorem exists_limit (F : ℕ → compactAnnularCoeff R A) (hF : CauchySeq F) :
    ∃ a : ℤ → R, a ∈ compactAnnularCoeff R A ∧ ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ n,
      ‖(F k : ℤ → R) n - a n‖ * max (A.inner ^ n) (A.outer ^ n) ≤ ε := by
  let w : ℤ → ℝ := fun n ↦ max (A.inner ^ n) (A.outer ^ n)
  have hw (n : ℤ) : 0 ≤ w n := (zpow_pos A.fst.property n).le.trans (le_max_left _ _)
  obtain ⟨a, ha, _, hunif⟩ := TauCeti.exists_weighted_coefficient_limit (w := w) hw
    (fun k ↦ (F k : ℤ → R)) (fun k ↦ tendsto_norm_coeff_mul_max (F k)) (by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
      refine ⟨N, fun k hk l hl n ↦ ?_⟩
      have h := norm_coeff_mul_max_le (F k - F l) n
      rw [Submodule.coe_sub, Pi.sub_apply] at h
      have hdist := hN k hk l hl
      rw [dist_eq_norm] at hdist
      exact h.trans_lt hdist)
  exact ⟨a, (laurentConvergesAt_endpoints_iff A.fst.property A.snd.property).mpr ha, hunif⟩

/-- Compact Laurent annuli are complete over a complete coefficient ring. -/
instance instCompleteSpace : CompleteSpace (compactAnnularCoeff R A) := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  obtain ⟨a, ha, hunif⟩ := exists_limit F hF
  refine ⟨⟨a, ha⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff]
  intro n
  rw [Submodule.coe_sub, Pi.sub_apply]
  exact hN k hk n

end CompleteSpace

/-- Finite Laurent truncations converge in the annular norm. -/
theorem tendsto_truncate (f : compactAnnularCoeff R A) :
    Tendsto (fun s : Finset ℤ ↦ truncate s f) atTop (𝓝 f) := by
  refine TauCeti.tendsto_finset_of_weighted_coeff
    (fun f : compactAnnularCoeff R A ↦ (f : ℤ → R))
    (fun n ↦ max (A.inner ^ n) (A.outer ^ n))
    (fun _ _ h ↦ norm_le_iff.mpr h) (tendsto_norm_coeff_mul_max f) ?_
  intro s n
  by_cases hn : n ∈ s <;> simp [coe_truncate_apply, hn]

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

/-- The coefficient inclusion is contractive for the endpoint maximum norms. -/
theorem norm_inclusion_le {B : CompactAnnulus} (h : B ≤ A) (f : compactAnnularCoeff R A) :
    ‖Submodule.inclusion (compactAnnularCoeff_anti h) f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq, Submodule.coe_inclusion]
  have h := NonemptyInterval.le_def.mp h
  exact max_le
    (laurentGaussNorm_le_max_endpoints A.fst.property h.1
      (B.fst_le_snd.trans h.2) f.property.1.bddAbove f.property.2.bddAbove)
    (laurentGaussNorm_le_max_endpoints A.fst.property (h.1.trans B.fst_le_snd)
      h.2 f.property.1.bddAbove f.property.2.bddAbove)

/-- The coefficient inclusion is uniformly continuous for the annular norm uniformities. -/
theorem uniformContinuous_inclusion {B : CompactAnnulus} (h : B ≤ A) :
    UniformContinuous (Submodule.inclusion (compactAnnularCoeff_anti (R := R) h)) :=
  AddMonoidHomClass.uniformContinuous_of_bound (Submodule.inclusion (compactAnnularCoeff_anti h))
    1 fun f ↦ by simpa only [one_mul] using norm_inclusion_le h f

section Convolution

variable [IsUltrametricDist R] [CompleteSpace R]

/-- The convolution ring uses the same endpoint maximum norm as the additive group. -/
noncomputable instance instNormedRing : NormedRing (compactAnnularCoeff R A) where
  __ := IsConvolutionRing.instRing
  __ := instNormedAddCommGroup
  norm_mul_le f g := by
    have hf := norm_nonneg f
    rw [norm_eq] at hf
    simp only [norm_eq, IsConvolutionRing.coe_mul]
    apply max_le
    · exact (laurentGaussNorm_addRingConvolution_le A.fst.property
        f.property.1.bddAbove g.property.1.bddAbove).trans
        (mul_le_mul (le_max_left _ _) (le_max_left _ _)
          (laurentGaussNorm_nonneg _ _) hf)
    · exact (laurentGaussNorm_addRingConvolution_le A.snd.property
        f.property.2.bddAbove g.property.2.bddAbove).trans
        (mul_le_mul (le_max_right _ _) (le_max_right _ _)
          (laurentGaussNorm_nonneg _ _) hf)

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

end Convolution

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

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [SeminormedCommRing R] [T3Space R] [IsUltrametricDist R] [CompleteSpace R]
  {A B C : CompactAnnulus}

/-- Coefficientwise restriction from a compact annulus to a smaller compact annulus. -/
noncomputable def restrict (h : B ≤ A) : compactAnnularCoeff R A →ₐ[R] compactAnnularCoeff R B :=
  AlgHom.ofLinearMap (Submodule.inclusion (compactAnnularCoeff_anti h))
    (Subtype.ext (by simp only [Submodule.coe_inclusion, IsConvolutionRing.coe_one]))
    (fun f g ↦ Subtype.ext
      (by simp only [Submodule.coe_inclusion, IsConvolutionRing.coe_mul]))

/-- The underlying linear map of restriction is the inclusion of coefficient submodules. -/
@[simp]
theorem toLinearMap_restrict (h : B ≤ A) :
    (restrict (R := R) h).toLinearMap = Submodule.inclusion (compactAnnularCoeff_anti h) := by
  rw [restrict, AlgHom.toLinearMap_ofLinearMap]

/-- Restriction leaves the coefficient family unchanged. -/
@[simp]
theorem coe_restrict (h : B ≤ A) (f : compactAnnularCoeff R A) :
    (restrict h f : ℤ → R) = (f : ℤ → R) := (rfl)

/-- Restriction retains every Laurent coefficient, so it is injective. -/
theorem restrict_injective (h : B ≤ A) : Function.Injective (restrict (R := R) h) :=
  Submodule.inclusion_injective (compactAnnularCoeff_anti h)

/-- Restriction to the same annulus is the identity. -/
@[simp]
theorem restrict_self : restrict (R := R) (A := A) le_rfl = AlgHom.id R _ := by
  apply AlgHom.ext
  intro f
  exact Subtype.ext (by simp only [AlgHom.id_apply, coe_restrict])

/-- Restrictions compose coefficientwise. -/
@[simp]
theorem restrict_comp (hAB : B ≤ A) (hBC : C ≤ B) :
    (restrict (R := R) hBC).comp (restrict hAB) = restrict (hBC.trans hAB) := by
  apply AlgHom.ext
  intro f
  exact Subtype.ext (by simp only [AlgHom.comp_apply, coe_restrict])

/-- Successive restrictions agree with restriction along the interval inclusion. -/
@[simp]
theorem restrict_restrict (hAB : B ≤ A) (hBC : C ≤ B) (f : compactAnnularCoeff R A) :
    restrict hBC (restrict hAB f) = restrict (hBC.trans hAB) f := by
  simpa only [AlgHom.comp_apply] using congrArg (fun g => g f) (restrict_comp hAB hBC)

/-- Restriction commutes with truncation to a finite set of degrees. -/
@[simp]
theorem restrict_truncate (h : B ≤ A) (s : Finset ℤ) (f : compactAnnularCoeff R A) :
    restrict h (truncate s f) = truncate s (restrict h f) := by
  ext n
  simp

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {A B : CompactAnnulus}

/-- Restriction is contractive for the endpoint maximum norms. -/
theorem norm_restrict_le (h : B ≤ A) (f : compactAnnularCoeff R A) :
    ‖restrict h f‖ ≤ ‖f‖ := by
  change ‖(restrict h).toLinearMap f‖ ≤ ‖f‖
  rw [toLinearMap_restrict]
  exact norm_inclusion_le h f

/-- Restriction is uniformly continuous for the annular norm uniformities. -/
theorem uniformContinuous_restrict (h : B ≤ A) :
    UniformContinuous (restrict (R := R) h) := by
  change UniformContinuous (restrict (R := R) h).toLinearMap
  rw [toLinearMap_restrict]
  exact uniformContinuous_inclusion h

end compactAnnularCoeff

namespace compactAnnularCoeff

variable [NormedField R] [IsUltrametricDist R] [CompleteSpace R] {A : CompactAnnulus}

/-- Compact annuli over a complete ultrametric field are normed algebras over that field. -/
noncomputable instance instNormedAlgebra : NormedAlgebra R (compactAnnularCoeff R A) where
  toAlgebra := inferInstance
  norm_smul_le := _root_.norm_smul_le

end compactAnnularCoeff

end TauCeti
