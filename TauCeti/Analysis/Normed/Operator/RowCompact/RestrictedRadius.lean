/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Topology.WithTopology
import TauCeti.Analysis.SpecificLimits.MonomialWeight

/-!
# Improvement of radius is compact

Let `R` be an ultrametric normed commutative ring and `σ` a finite set of variables. Restricting
a series converging on the closed polydisc of polyradii `s` to a strictly smaller polydisc of
polyradii `r` (so `rᵢ < sᵢ` for every `i`) is a completely continuous `R`-linear map
(`TauCeti.MvPowerSeries.isCompletelyContinuous_restrictedRadiusCLM`). Its approximants are
truncations to finitely many monomials: outside a finite set of exponents `t` the weight ratio
`∏ (rᵢ / sᵢ) ^ tᵢ` is small, and the coefficient `aₜ` of a series `f` satisfies
`‖aₜ‖ rᵗ = ‖aₜ‖ sᵗ ∏ (rᵢ / sᵢ) ^ tᵢ ≤ ‖f‖ₛ ∏ (rᵢ / sᵢ) ^ tᵢ`.
No completeness of `R`, no discreteness of its value group and no assumption that the radii are
norms of scalars is needed: the weights are real numbers throughout.

Strictness is essential. Over a complete nontrivial ring, the identity of a restricted-series
algebra in at least one variable is not completely continuous
(`TauCeti.MvPowerSeries.not_isCompletelyContinuous_id_isRestrictedSubring`), because the
monomials are linearly independent, so the algebra is not a finitely generated module
(`TauCeti.MvPowerSeries.not_finite_isRestrictedSubring`).

The matrix form of the same phenomenon is the row criterion for maps into the unit-radius
coefficient model `C₀(σ →₀ ℕ, R)`. If the image of `x` under `u : C₀(J, R) →L[R] C₀(σ →₀ ℕ, R)`
is the coefficient family of a series `v x` restricted at polyradii `c` with `‖v x‖ ≤ C ‖x‖`,
then row `t` of the matrix of `u` is bounded by `C ‖1‖ c⁻ᵗ`
(`TauCeti.MvPowerSeries.norm_matrixCoeff_le_of_apply_eq_coeff`). When every `cᵢ > 1` this row
majorant tends to zero, so `u` is row compact
(`TauCeti.MvPowerSeries.isRowCompact_of_apply_eq_coeff`). This applies to `u` the coefficient
isometry composed with restriction to unit radius and any bounded map into series restricted
at `c`.

## Main results

* `TauCeti.MvPowerSeries.isCompletelyContinuous_restrictedRadiusCLM`: strict radius restriction
  is completely continuous.
* `TauCeti.MvPowerSeries.not_isCompletelyContinuous_id_isRestrictedSubring`: equal radii give no
  compactness.
* `TauCeti.MvPowerSeries.isRowCompact_of_apply_eq_coeff`: maps into the unit-radius coefficient
  model that factor through a strictly larger radius are row compact.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

section Finiteness

/-- Over a complete nontrivial ring, the identity of a restricted-series algebra in at least one
variable is not completely continuous. Hence radius restriction is not completely continuous for
equal polyradii. -/
theorem not_isCompletelyContinuous_id_isRestrictedSubring [Nontrivial R] [CompleteSpace R]
    [Nonempty σ] (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    ¬(ContinuousLinearMap.id R (IsRestricted.subring (R := R) c)).IsCompletelyContinuous := by
  rw [ContinuousLinearMap.isCompletelyContinuous_id_iff]
  exact not_finite_isRestrictedSubring c

end Finiteness

section Truncation

variable {r : σ → ℝ}

/-- Truncation of a restricted series to the monomials with exponents in a finite set `S`, as a
linear map. -/
private noncomputable def truncLinearMap (S : Finset (σ →₀ ℕ)) :
    IsRestricted.subring (R := R) r →ₗ[R] IsRestricted.subring (R := R) r :=
  (polynomialToRestricted r).toLinearMap ∘ₗ truncFinset R S ∘ₗ
    { toFun f := (f : MvPowerSeries σ R)
      map_add' _ _ := rfl
      map_smul' a f := coe_smul_isRestrictedSubring a f }

private theorem coeff_truncLinearMap [DecidableEq σ] (S : Finset (σ →₀ ℕ))
    (f : IsRestricted.subring (R := R) r) (t : σ →₀ ℕ) :
    coeff t (truncLinearMap S f : MvPowerSeries σ R) =
      if t ∈ S then coeff t (f : MvPowerSeries σ R) else 0 := by
  simp [truncLinearMap, coeff_truncFinset]

variable [∀ i, Fact (0 < r i)]

/-- Truncation of a restricted series to the monomials with exponents in a finite set `S`, as a
contractive continuous linear map. -/
private noncomputable def truncCLM (S : Finset (σ →₀ ℕ)) :
    IsRestricted.subring (R := R) r →L[R] IsRestricted.subring (R := R) r where
  toLinearMap := truncLinearMap S
  cont := AddMonoidHomClass.continuous_of_bound (truncLinearMap S) 1 fun f ↦ by
    classical
    rw [one_mul, norm_le_iff (norm_nonneg f)]
    intro t
    rw [coeff_truncLinearMap]
    split_ifs
    · exact norm_coeff_mul_prod_le f t
    · simp

private theorem coeff_truncCLM [DecidableEq σ] (S : Finset (σ →₀ ℕ))
    (f : IsRestricted.subring (R := R) r) (t : σ →₀ ℕ) :
    coeff t (truncCLM S f : MvPowerSeries σ R) =
      if t ∈ S then coeff t (f : MvPowerSeries σ R) else 0 :=
  coeff_truncLinearMap S f t

/-- A truncation has finite rank: its values are combinations of the monomials indexed by `S`. -/
private theorem isFiniteRank_truncCLM (S : Finset (σ →₀ ℕ)) :
    ((truncCLM S : IsRestricted.subring (R := R) r →L[R] IsRestricted.subring (R := R) r) :
      IsRestricted.subring (R := R) r →ₗ[R] IsRestricted.subring (R := R) r).IsFiniteRank := by
  refine LinearMap.isFiniteRank_iff_forall_mem.2
    ⟨_, Submodule.fg_span (S.finite_toSet.image
      fun t ↦ polynomialToRestricted r (MvPolynomial.monomial t (1 : R))), fun f ↦ ?_⟩
  simp only [truncCLM, truncLinearMap, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, AlgHom.toLinearMap_apply,
    truncFinset_apply, map_sum]
  refine Submodule.sum_mem _ fun t ht ↦ ?_
  rw [← mul_one (coeff t _), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)

end Truncation

section RadiusRestriction

variable {r s : σ → ℝ} [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- **Improvement of radius is completely continuous.** Over finitely many variables, restricting
series from polyradii `s` to polyradii `r` with `rᵢ < sᵢ` for every `i` is a uniform limit of
continuous linear maps of finite rank, namely truncations to finitely many monomials. -/
theorem isCompletelyContinuous_restrictedRadiusCLM [Finite σ] (hrs : ∀ i, r i < s i) :
    (restrictedRadiusCLM (R := R) fun i ↦ (hrs i).le).IsCompletelyContinuous := by
  classical
  rw [ContinuousLinearMap.isCompletelyContinuous_iff]
  intro ε hε
  have hs (i : σ) : 0 < s i := Fact.out
  -- Outside a finite set `S` of exponents, the weight ratio `∏ (rᵢ / sᵢ) ^ tᵢ` is at most `ε`.
  have hS := eventually_cofinite.1 ((Finsupp.tendsto_prod_pow_cofinite_nhds_zero
    (w := fun i ↦ r i / s i) (fun i ↦ div_nonneg (Fact.out : 0 < r i).le (hs i).le)
    fun i ↦ (div_lt_one (hs i)).2 (hrs i)).eventually (ge_mem_nhds hε))
  refine ⟨(truncCLM hS.toFinset).comp (restrictedRadiusCLM fun i ↦ (hrs i).le),
    (isFiniteRank_truncCLM _).comp_right _, fun f ↦ ?_⟩
  rw [norm_le_iff (mul_nonneg hε.le (norm_nonneg f))]
  intro t
  simp only [AddSubgroupClass.coe_sub, map_sub, ContinuousLinearMap.comp_apply, coeff_truncCLM,
    restrictedRadiusCLM_apply, coe_restrictedRadiusHom, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  -- The truncation keeps exactly the coefficients whose weight ratio exceeds `ε`.
  split_ifs with ht
  · rw [sub_zero]
    have hrst : t.prod (r · ^ ·) = t.prod (s · ^ ·) * t.prod fun i n ↦ (r i / s i) ^ n := by
      rw [← Finsupp.prod_mul]
      exact Finsupp.prod_congr fun i _ ↦ by rw [← mul_pow, mul_div_cancel₀ _ (hs i).ne']
    rw [hrst, ← mul_assoc, mul_comm ε]
    exact mul_le_mul (norm_coeff_mul_prod_le f t) ht
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (div_nonneg (Fact.out : 0 < r i).le (hs i).le) _)
      (norm_nonneg f)
  · rw [sub_self, norm_zero, zero_mul]
    positivity

end RadiusRestriction

section RowCompact

variable {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- **Row bound from a larger radius.** Let `u : C₀(J, R) →L[R] C₀(σ →₀ ℕ, R)` send each `x` to
the coefficient family of a series `v x` restricted at polyradii `c`, with `‖v x‖ ≤ C ‖x‖`. Then
the entries of row `t` of the matrix of `u` are bounded by `C ‖1‖ c⁻ᵗ`. -/
theorem norm_matrixCoeff_le_of_apply_eq_coeff
    {u : C₀(J, R) →L[R] C₀(WithDiscreteTopology (σ →₀ ℕ), R)}
    (v : C₀(J, R) → IsRestricted.subring (R := R) c)
    (hu : ∀ x t, u x (.toTopology ⊥ t) = coeff t (v x : MvPowerSeries σ R))
    {C : ℝ} (hv : ∀ x, ‖v x‖ ≤ C * ‖x‖) (t : σ →₀ ℕ) (j : J) :
    ‖u.matrixCoeff (.toTopology ⊥ t) j‖ ≤ C * ‖(1 : R)‖ * (t.prod (c · ^ ·))⁻¹ := by
  rw [ContinuousLinearMap.matrixCoeff_apply, hu, le_mul_inv_iff₀ (prod_pow_pos t)]
  calc _ ≤ ‖v (ZeroAtInftyContinuousMap.single j 1)‖ := norm_coeff_mul_prod_le _ t
    _ ≤ _ := by
      simpa [ZeroAtInftyContinuousMap.norm_single] using hv (ZeroAtInftyContinuousMap.single j 1)

/-- **Maps factoring through a larger radius are row compact.** Over finitely many variables, let
`u : C₀(J, R) →L[R] C₀(σ →₀ ℕ, R)` send each `x` to the coefficient family of a series `v x`
restricted at polyradii `c` with every `cᵢ > 1`, where `‖v x‖ ≤ C ‖x‖`. Then `u` is row compact.
In other words, a bounded map into series restricted at `c`, followed by restriction to unit
radius and the coefficient isometry, is row compact. -/
theorem isRowCompact_of_apply_eq_coeff [Finite σ] (hc : ∀ i, 1 < c i)
    {u : C₀(J, R) →L[R] C₀(WithDiscreteTopology (σ →₀ ℕ), R)}
    (v : C₀(J, R) → IsRestricted.subring (R := R) c)
    (hu : ∀ x t, u x (.toTopology ⊥ t) = coeff t (v x : MvPowerSeries σ R))
    {C : ℝ} (hv : ∀ x, ‖v x‖ ≤ C * ‖x‖) : u.IsRowCompact := by
  have hc0 (i : σ) : 0 < c i := Fact.out
  have hw := Finsupp.tendsto_prod_pow_cofinite_nhds_zero (w := fun i ↦ (c i)⁻¹)
    (fun i ↦ (inv_pos.2 (hc0 i)).le) fun i ↦ inv_lt_one_of_one_lt₀ (hc i)
  refine ContinuousLinearMap.isRowCompact_of_norm_matrixCoeff_le
    (r := fun i ↦ C * ‖(1 : R)‖ * (i.ofTopology.prod (c · ^ ·))⁻¹) ?_ fun i j ↦ ?_
  · have h := (hw.comp (WithTopology.ofTopology_injective (t := ⊥)).tendsto_cofinite).const_mul
      (C * ‖(1 : R)‖)
    rw [mul_zero] at h
    refine h.congr fun i ↦ ?_
    simp only [Function.comp_apply, Finsupp.prod, inv_pow, Finset.prod_inv_distrib]
  · rcases i with ⟨t⟩
    exact norm_matrixCoeff_le_of_apply_eq_coeff v hu hv t j

end RowCompact

end TauCeti.MvPowerSeries
