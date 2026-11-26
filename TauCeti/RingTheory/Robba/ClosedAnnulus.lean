/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Robba.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import TauCeti.Analysis.Normed.Group.Pi

/-!
# Laurent series on a closed annulus

For positive real endpoints `r ≤ s`, Laurent series converging at both endpoints converge at
all radii in `[r, s]`. Their Cauchy convolution and the norm `max (|f|ᵣ, |f|ₛ)` give the Banach
algebra of the closed annulus. Both endpoints are needed: when `[NormOneClass R]`, the norms
of `t` and `t⁻¹` are `s` and `r⁻¹`, respectively. The construction allows arbitrary real radii
and either characteristic.

`closedAnnulusCoeff` is the coefficient submodule, and `ClosedAnnulusRing` equips it with convergent
convolution. Restriction to a smaller annulus is the identity on coefficients and decreases the
norm. Finite Laurent polynomials are dense in the endpoint maximum norm.

The convolution estimates come from `TauCeti.RingTheory.Robba.Basic`. Completeness uses the
weighted uniform coefficient limit of `TauCeti.exists_weighted_uniform_limit`.

## References

* M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), §2, (2.1)–(2.6).
* K. S. Kedlaya, *Slope filtrations revisited*, Doc. Math. 10 (2005), Definition 2.4.2.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti

section Coeff

variable (R : Type*) [SeminormedRing R]

/-- Laurent coefficient families converging at the endpoints `r` and `s`. When `0 < r ≤ s`,
these are precisely the families converging at every radius in the closed annulus `[r, s]`. -/
def closedAnnulusCoeff (r s : ℝ) : Submodule R (ℤ → R) where
  carrier := {a | LaurentConvergesAt r a ∧ LaurentConvergesAt s a}
  zero_mem' := ⟨laurentConvergesAt_zero _, laurentConvergesAt_zero _⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  smul_mem' c _ ha := ⟨ha.1.smul c, ha.2.smul c⟩

variable {R}

/-- Membership in the coefficient module is convergence at both endpoints. -/
@[simp]
theorem mem_closedAnnulusCoeff {r s : ℝ} {a : ℤ → R} :
    a ∈ closedAnnulusCoeff R r s ↔ LaurentConvergesAt r a ∧ LaurentConvergesAt s a :=
  (Iff.rfl)

/-- Endpoint convergence is equivalent to convergence on the whole closed annulus. -/
theorem mem_closedAnnulusCoeff_iff {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) {a : ℤ → R} :
    a ∈ closedAnnulusCoeff R r s ↔ ∀ ρ ∈ Set.Icc r s, LaurentConvergesAt ρ a := by
  exact ⟨fun ha _ hρ ↦ ha.1.of_endpoints ha.2 hr hρ.1 hρ.2,
    fun ha ↦ ⟨ha r ⟨le_rfl, hrs⟩, ha s ⟨hrs, le_rfl⟩⟩⟩

/-- Restriction to a smaller closed annulus preserves convergence. -/
theorem closedAnnulusCoeff_le {r s r' s' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (hr's' : r' ≤ s') (hs's : s' ≤ s) :
    closedAnnulusCoeff R r s ≤ closedAnnulusCoeff R r' s' := fun _ ha ↦
  ⟨ha.1.of_endpoints ha.2 hr hrr' (hr's'.trans hs's),
    ha.1.of_endpoints ha.2 hr (hrr'.trans hr's') hs's⟩

variable (R) in
/-- Laurent series on a closed annulus, with Cauchy convolution as multiplication. The norm is
the maximum of the Gauss norms at the two endpoints. -/
abbrev ClosedAnnulusRing (r s : ℝ) : Type _ := closedAnnulusCoeff R r s

namespace ClosedAnnulusRing

variable {r s : ℝ} [Fact (0 < r)] [Fact (0 < s)]

/-- Endpoint convergence supplies convergent convolution and its associativity hypotheses. -/
instance [IsUltrametricDist R] [CompleteSpace R] :
    IsConvolutionRing (closedAnnulusCoeff R r s) where
  single_mem n c := ⟨laurentConvergesAt_single _ n c, laurentConvergesAt_single _ n c⟩
  addRingConvolution_mem ha hb :=
    ⟨ha.1.addRingConvolution (Fact.out) hb.1, ha.2.addRingConvolution (Fact.out) hb.2⟩
  addConvolutionExists ha hb := ha.1.addConvolutionExists (Fact.out) hb.1
  summable_sigma_addFiber_mul_mul ha hb hc :=
    ha.1.summable_sigma_addFiber_mul_mul (Fact.out) hb.1 hc.1

end ClosedAnnulusRing

end Coeff

namespace ClosedAnnulusRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r s : ℝ} [hr : Fact (0 < r)] [hs : Fact (0 < s)]

omit [CompleteSpace R] in
/-- The endpoint maximum satisfies the ultrametric triangle inequality. -/
private theorem max_gaussNorm_add_le (f g : ClosedAnnulusRing R r s) :
    max (laurentGaussNorm r ((f + g : ClosedAnnulusRing R r s) : ℤ → R))
      (laurentGaussNorm s ((f + g : ClosedAnnulusRing R r s) : ℤ → R)) ≤
      max (max (laurentGaussNorm r (f : ℤ → R)) (laurentGaussNorm s (f : ℤ → R)))
        (max (laurentGaussNorm r (g : ℤ → R)) (laurentGaussNorm s (g : ℤ → R))) := by
  exact max_le
    ((laurentGaussNorm_add_le hr.out.le f.property.1.bddAbove g.property.1.bddAbove).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _)))
    ((laurentGaussNorm_add_le hs.out.le f.property.2.bddAbove g.property.2.bddAbove).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _)))

/-- The maximum of the two endpoint Gauss norms is submultiplicative. -/
private theorem max_gaussNorm_mul_le (f g : ClosedAnnulusRing R r s) :
    max (laurentGaussNorm r ((f * g : ClosedAnnulusRing R r s) : ℤ → R))
      (laurentGaussNorm s ((f * g : ClosedAnnulusRing R r s) : ℤ → R)) ≤
      max (laurentGaussNorm r (f : ℤ → R)) (laurentGaussNorm s (f : ℤ → R)) *
        max (laurentGaussNorm r (g : ℤ → R)) (laurentGaussNorm s (g : ℤ → R)) := by
  refine max_le ?_ ?_
  · exact (laurentGaussNorm_addRingConvolution_le hr.out
      f.property.1.bddAbove g.property.1.bddAbove).trans
      (mul_le_mul (le_max_left _ _) (le_max_left _ _) (laurentGaussNorm_nonneg _ _)
        (le_max_of_le_left (laurentGaussNorm_nonneg _ _)))
  · exact (laurentGaussNorm_addRingConvolution_le hs.out
      f.property.2.bddAbove g.property.2.bddAbove).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (laurentGaussNorm_nonneg _ _)
        (le_max_of_le_left (laurentGaussNorm_nonneg _ _)))

/-- The closed-annulus norm is the maximum of its endpoint Gauss norms. -/
noncomputable instance instNormedRing : NormedRing (ClosedAnnulusRing R r s) :=
  RingNorm.toNormedRing
    { toFun f := max (laurentGaussNorm r (f : ℤ → R)) (laurentGaussNorm s (f : ℤ → R))
      map_zero' := by simp
      add_le' f g := by
        exact (max_gaussNorm_add_le f g).trans
          (max_le_add_of_nonneg (le_max_of_le_left (laurentGaussNorm_nonneg _ _))
            (le_max_of_le_left (laurentGaussNorm_nonneg _ _)))
      neg' f := by simp
      mul_le' f g := by exact max_gaussNorm_mul_le f g
      eq_zero_of_map_eq_zero' f hf := by
        apply Subtype.ext
        funext n
        have h := (le_laurentGaussNorm f.property.1.bddAbove n).trans
          ((le_max_left _ _).trans hf.le)
        simpa only [Submodule.coe_zero, Pi.zero_apply] using norm_eq_zero.mp
          ((nonpos_of_mul_nonpos_left h (zpow_pos hr.out n)).antisymm (norm_nonneg _)) }

/-- The uniformity of a closed annulus is induced by its endpoint maximum norm. -/
noncomputable instance instUniformSpace : UniformSpace (ClosedAnnulusRing R r s) :=
  instNormedRing.toMetricSpace.toUniformSpace

/-- The topology of a closed annulus is induced by its endpoint maximum norm, rather than
coefficientwise convergence. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (ClosedAnnulusRing R r s) :=
  instUniformSpace.toTopologicalSpace

/-- The norm is the maximum of the endpoint Gauss norms. -/
theorem norm_def (f : ClosedAnnulusRing R r s) :
    ‖f‖ = max (laurentGaussNorm r (f : ℤ → R)) (laurentGaussNorm s (f : ℤ → R)) := (rfl)

/-- Every coefficient is bounded in both endpoint weights by the norm. -/
theorem norm_coeff_mul_zpow_le (f : ClosedAnnulusRing R r s) (n : ℤ) :
    ‖(f : ℤ → R) n‖ * r ^ n ≤ ‖f‖ ∧ ‖(f : ℤ → R) n‖ * s ^ n ≤ ‖f‖ :=
  ⟨(le_laurentGaussNorm f.property.1.bddAbove n).trans (le_max_left _ _),
    (le_laurentGaussNorm f.property.2.bddAbove n).trans (le_max_right _ _)⟩

/-- A norm bound is equivalent to the two endpoint weighted coefficient bounds. -/
theorem norm_le_iff {f : ClosedAnnulusRing R r s} {C : ℝ} :
    ‖f‖ ≤ C ↔ ∀ n, ‖(f : ℤ → R) n‖ * r ^ n ≤ C ∧ ‖(f : ℤ → R) n‖ * s ^ n ≤ C := by
  exact ⟨fun h n ↦ ⟨(norm_coeff_mul_zpow_le f n).1.trans h,
    (norm_coeff_mul_zpow_le f n).2.trans h⟩,
    fun h ↦ max_le (laurentGaussNorm_le fun n ↦ (h n).1)
      (laurentGaussNorm_le fun n ↦ (h n).2)⟩

/-- The endpoint maximum norm is ultrametric. -/
instance : IsUltrametricDist (ClosedAnnulusRing R r s) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm max_gaussNorm_add_le

/-- The norm of a Laurent monomial uses both endpoint weights. -/
@[simp]
theorem norm_monomial (n : ℤ) (c : R) :
    ‖(IsConvolutionRing.monomial n c : ClosedAnnulusRing R r s)‖ =
      max (‖c‖ * r ^ n) (‖c‖ * s ^ n) := by
  simp [norm_def, laurentGaussNorm_single, hr.out.le, hs.out.le]

/-- The norm of one is one when this holds in the coefficient ring. -/
instance [NormOneClass R] : NormOneClass (ClosedAnnulusRing R r s) where
  norm_one := by
    rw [← IsConvolutionRing.monomial_zero_one, norm_monomial]
    simp

/-- Each coefficient map is uniformly continuous in the endpoint maximum norm. -/
theorem uniformContinuous_coeff (n : ℤ) :
    UniformContinuous fun f : ClosedAnnulusRing R r s ↦ (f : ℤ → R) n :=
  AddMonoidHomClass.uniformContinuous_of_bound
    ({ toFun := fun f : ClosedAnnulusRing R r s ↦ (f : ℤ → R) n
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : ClosedAnnulusRing R r s →+ R)
    (r ^ n)⁻¹ fun f ↦ by
      rw [inv_mul_eq_div, le_div_iff₀ (zpow_pos hr.out n)]
      exact (norm_coeff_mul_zpow_le f n).1

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- A uniform weighted limit of closed-annulus series still converges at both endpoints. -/
private theorem limit_mem (F : ℕ → ClosedAnnulusRing R r s) (a : ℤ → R)
    (hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ n,
      ‖(F k : ℤ → R) n - a n‖ * max (r ^ n) (s ^ n) ≤ ε) :
    a ∈ closedAnnulusCoeff R r s := by
  have hw (n : ℤ) : 0 ≤ max (r ^ n) (s ^ n) := le_max_of_le_left (zpow_pos hr.out n).le
  have ha : Tendsto (fun n ↦ ‖a n‖ * max (r ^ n) (s ^ n)) cofinite (𝓝 0) := by
    apply tendsto_zero_of_weighted_uniform_limit _ hw (fun k ↦ (F k : ℤ → R)) a _ hunif
    intro k
    simp_rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
    simpa only [max_self] using Tendsto.max
      (laurentConvergesAt_iff.1 (F k).property.1)
      (laurentConvergesAt_iff.1 (F k).property.2)
  exact ⟨laurentConvergesAt_iff.2 (squeeze_zero
    (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos hr.out n).le)
    (fun n ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)) ha),
    laurentConvergesAt_iff.2 (squeeze_zero
      (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos hs.out n).le)
      (fun n ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)) ha)⟩

/-- Closed annuli are complete for the endpoint maximum norm over a complete coefficient ring. -/
instance instCompleteSpace : CompleteSpace (ClosedAnnulusRing R r s) := by
  refine Metric.complete_of_cauchySeq_tendsto (α := ClosedAnnulusRing R r s) fun F hF ↦ ?_
  obtain ⟨a, hunif⟩ := exists_weighted_uniform_limit
    (fun n : ℤ ↦ max (r ^ n) (s ^ n)) (fun k ↦ (F k : ℤ → R)) (by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hF ε hε
      refine ⟨N, fun k hk l hl n ↦ ?_⟩
      have h := norm_coeff_mul_zpow_le (F k - F l) n
      simp only [Submodule.coe_sub, Pi.sub_apply] at h
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      exact (max_le h.1 h.2).trans_lt ((dist_eq_norm _ _).symm.trans_lt (hN k hk l hl)))
  refine ⟨⟨a, limit_mem F a hunif⟩, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [dist_eq_norm]
  refine (norm_le_iff.2 fun n ↦ ?_).trans_lt (half_lt_self hε)
  simp only [Submodule.coe_sub, Pi.sub_apply]
  exact ⟨(mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)).trans (hN k hk n),
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)).trans (hN k hk n)⟩

/-- Truncate a closed-annulus series to a finite set of Laurent degrees. -/
noncomputable def trunc (f : ClosedAnnulusRing R r s) (S : Finset ℤ) : ClosedAnnulusRing R r s :=
  ∑ n ∈ S, IsConvolutionRing.monomial n ((f : ℤ → R) n)

/-- Truncation retains exactly the coefficients in the chosen finite set. -/
@[simp]
theorem coe_trunc_apply (f : ClosedAnnulusRing R r s) (S : Finset ℤ) (n : ℤ) :
    (trunc f S : ℤ → R) n = if n ∈ S then (f : ℤ → R) n else 0 := by
  classical
  simp [trunc, Finset.sum_apply, IsConvolutionRing.coe_monomial, Pi.single_apply]

/-- A truncation has finite Laurent support. -/
theorem finite_support_trunc (f : ClosedAnnulusRing R r s) (S : Finset ℤ) :
    (Function.support (trunc f S : ℤ → R)).Finite := by
  refine S.finite_toSet.subset fun n hn ↦ ?_
  have h : n ∈ S ∧ (f : ℤ → R) n ≠ 0 := by
    simpa only [Function.mem_support, coe_trunc_apply, ne_eq, ite_eq_right_iff,
      Classical.not_imp, not_not] using hn
  exact h.1

/-- Truncating a Laurent series converges in the maximum of the two endpoint Gauss norms. -/
theorem tendsto_trunc (f : ClosedAnnulusRing R r s) : Tendsto (trunc f) atTop (𝓝 f) := by
  classical
  refine (Metric.tendsto_atTop (u := trunc f)).2 fun ε hε ↦ ?_
  have hF : Tendsto (fun n ↦ max (‖(f : ℤ → R) n‖ * r ^ n)
      (‖(f : ℤ → R) n‖ * s ^ n)) cofinite (𝓝 0) := by
    simpa only [max_self] using Tendsto.max
      (laurentConvergesAt_iff.1 f.property.1) (laurentConvergesAt_iff.1 f.property.2)
  have hbad := eventually_cofinite.1 (hF.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨hbad.toFinset, fun S hS ↦ ?_⟩
  rw [dist_eq_norm]
  refine (norm_le_iff.2 fun n ↦ ?_).trans_lt (half_lt_self hε)
  simp only [Submodule.coe_sub, Pi.sub_apply, coe_trunc_apply]
  by_cases hn : n ∈ S
  · simp [hn, (half_pos hε).le]
  · have hsmall : max (‖(f : ℤ → R) n‖ * r ^ n)
        (‖(f : ℤ → R) n‖ * s ^ n) < ε / 2 := by
      by_contra h
      exact hn (hS (hbad.mem_toFinset.2 h))
    simpa only [ite_eq_right hn, zero_sub, norm_neg] using
      ⟨(le_max_left _ _).trans hsmall.le, (le_max_right _ _).trans hsmall.le⟩

/-- Finite Laurent polynomials are dense in the Banach algebra of a closed annulus. -/
theorem dense_finite_support :
    Dense {f : ClosedAnnulusRing R r s | (Function.support (f : ℤ → R)).Finite} := by
  intro f
  exact mem_closure_of_tendsto (tendsto_trunc f)
    (Filter.Eventually.of_forall fun S ↦ finite_support_trunc f S)

end ClosedAnnulusRing

namespace ClosedAnnulusRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r s : ℝ} [hr : Fact (0 < r)] [hs : Fact (0 < s)]

/-- Convolution is commutative over commutative coefficients. -/
noncomputable instance instNormedCommRing : NormedCommRing (ClosedAnnulusRing R r s) :=
  { instNormedRing with mul_comm := mul_comm }

/-- The norm of a constant Laurent series is its coefficient norm. -/
@[simp]
theorem norm_algebraMap (c : R) : ‖algebraMap R (ClosedAnnulusRing R r s) c‖ = ‖c‖ := by
  rw [← IsConvolutionRing.monomial_zero_left, norm_monomial]
  simp

/-- Restrict a Laurent series to a smaller closed annulus, without changing coefficients. -/
noncomputable def restrict {r' s' : ℝ} (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    [Fact (0 < r')] [Fact (0 < s')] :
    ClosedAnnulusRing R r s →ₐ[R] ClosedAnnulusRing R r' s' where
  toFun f := ⟨f, closedAnnulusCoeff_le hr.out hrr' hr's' hs's f.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  commutes' _ := Subtype.ext (by simp)

/-- Restriction is the identity on Laurent coefficients. -/
@[simp]
theorem coe_restrict {r' s' : ℝ} (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    [Fact (0 < r')] [Fact (0 < s')] (f : ClosedAnnulusRing R r s) :
    (restrict hrr' hr's' hs's f : ℤ → R) = (f : ℤ → R) := (rfl)

/-- Restriction to a smaller annulus decreases the norm. -/
theorem norm_restrict_le {r' s' : ℝ} (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    [Fact (0 < r')] [Fact (0 < s')] (f : ClosedAnnulusRing R r s) :
    ‖restrict hrr' hr's' hs's f‖ ≤ ‖f‖ := by
  rw [norm_def, coe_restrict, norm_def]
  exact max_le
    (laurentGaussNorm_le_max_endpoints f.property.1.bddAbove f.property.2.bddAbove hr.out hrr'
      (hr's'.trans hs's))
    (laurentGaussNorm_le_max_endpoints f.property.1.bddAbove f.property.2.bddAbove hr.out
      (hrr'.trans hr's') hs's)

/-- Restriction is continuous for the Banach norms. -/
theorem continuous_restrict {r' s' : ℝ} (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    [Fact (0 < r')] [Fact (0 < s')] : Continuous (restrict (R := R) hrr' hr's' hs's) :=
  AddMonoidHomClass.continuous_of_bound (restrict (R := R) hrr' hr's' hs's) 1 fun f ↦ by
    simpa using norm_restrict_le hrr' hr's' hs's f

/-- Restriction is injective because it keeps all coefficients. -/
theorem restrict_injective {r' s' : ℝ} (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    [Fact (0 < r')] [Fact (0 < s')] :
    Function.Injective (restrict (R := R) hrr' hr's' hs's) := fun _ _ h ↦
  Subtype.ext (congrArg (fun f : ClosedAnnulusRing R r' s' ↦ (f : ℤ → R)) h)

/-- Restricting to the same annulus is the identity. -/
@[simp]
theorem restrict_refl (hrs : r ≤ s) :
    restrict (R := R) le_rfl hrs le_rfl = AlgHom.id R (ClosedAnnulusRing R r s) := by
  exact AlgHom.ext fun f ↦ Subtype.ext (coe_restrict le_rfl hrs le_rfl f)

/-- Successive restrictions agree with restriction to the final annulus. -/
@[simp]
theorem restrict_trans {r' s' r'' s'' : ℝ}
    [Fact (0 < r')] [Fact (0 < s')] [Fact (0 < r'')] [Fact (0 < s'')]
    (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s)
    (hr'r'' : r' ≤ r'') (hr''s'' : r'' ≤ s'') (hs''s' : s'' ≤ s') :
    (restrict (R := R) hr'r'' hr''s'' hs''s').comp (restrict hrr' hr's' hs's) =
      restrict (hrr'.trans hr'r'') hr''s'' (hs''s'.trans hs's) := by
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  simp only [AlgHom.coe_comp, Function.comp_apply, coe_restrict]

/-- Restriction preserves Laurent monomials. -/
@[simp]
theorem restrict_monomial {r' s' : ℝ} [Fact (0 < r')] [Fact (0 < s')]
    (hrr' : r ≤ r') (hr's' : r' ≤ s') (hs's : s' ≤ s) (n : ℤ) (c : R) :
    restrict hrr' hr's' hs's (IsConvolutionRing.monomial n c) =
      IsConvolutionRing.monomial n c := by
  apply Subtype.ext
  simp only [coe_restrict, IsConvolutionRing.coe_monomial]

end ClosedAnnulusRing

namespace ClosedAnnulusRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {r s : ℝ} [hr : Fact (0 < r)] [hs : Fact (0 < s)]

/-- Over a complete ultrametric field the closed annulus is a Banach algebra. -/
noncomputable instance instNormedAlgebra : NormedAlgebra K (ClosedAnnulusRing K r s) where
  norm_smul_le c f := by
    simp only [norm_def]
    rw [mul_max_of_nonneg _ _ (norm_nonneg c)]
    exact max_le_max
      (laurentGaussNorm_smul_le hr.out.le f.property.1.bddAbove c)
      (laurentGaussNorm_smul_le hs.out.le f.property.2.bddAbove c)

end ClosedAnnulusRing

namespace RobbaRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r α β : ℝ} [hα : Fact (0 < α)] [hβ : Fact (0 < β)]

/-- Restrict a series on the open annulus `r < |t| < 1` to a compact subannulus
`[α, β]` in its interior. These maps give the compact windows of an open annular chart. -/
noncomputable def annulusToClosedAnnulus (hrα : r < α) (hαβ : α ≤ β) (hβ₁ : β < 1) :
    annulus R r →ₐ[R] ClosedAnnulusRing R α β where
  toFun f := ⟨((f : RobbaRing R) : ℤ → R),
    (mem_annularCoeff.1 (mem_annulus.1 f.property) α hα.out hrα (hαβ.trans_lt hβ₁)),
    (mem_annularCoeff.1 (mem_annulus.1 f.property) β hβ.out (hrα.trans_le hαβ) hβ₁)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  commutes' _ := Subtype.ext (by simp)

/-- Compact-window restriction preserves the coefficient family of a Robba series. -/
@[simp]
theorem coe_annulusToClosedAnnulus (hrα : r < α) (hαβ : α ≤ β) (hβ₁ : β < 1)
    (f : annulus R r) :
    (annulusToClosedAnnulus hrα hαβ hβ₁ f : ℤ → R) = ((f : RobbaRing R) : ℤ → R) := (rfl)

/-- Restricting an open annular chart to a compact window is injective. -/
theorem annulusToClosedAnnulus_injective (hrα : r < α) (hαβ : α ≤ β) (hβ₁ : β < 1) :
    Function.Injective (annulusToClosedAnnulus (R := R) hrα hαβ hβ₁) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun F : ClosedAnnulusRing R α β ↦ (F : ℤ → R)) h

end RobbaRing

end TauCeti
