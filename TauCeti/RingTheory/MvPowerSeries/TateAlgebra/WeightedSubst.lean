/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.FiniteRank
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Weighted substitution operators on Tate algebras

Let `R` be a complete ultrametric normed commutative ring. For a series `g` and series
`h₁, …, h_k` of Gauss norm `‖hᵢ‖ ≤ rᵢ` in variables `Y`, the *weighted substitution*
`f ↦ g · f(h)` is a continuous `R`-linear map from series in `X₁, …, X_k` restricted at
polyradii `r` to series in `Y` (`TauCeti.MvPowerSeries.restrictedWeightedSubstCLM`). It is
built from the analytic substitution `f ↦ f(h)` and multiplication by `g`. Such operators, for
instance `f ↦ g · f(Xᵖ)` and its variants, are the basic examples of operators on spaces of
analytic functions in nonarchimedean spectral theory, such as Dwork's operators and Hecke
operators on overconvergent forms.

At unit radius the coefficient isometry identifies the Tate algebra with the model space
`C₀(σ →₀ ℕ, R)`, and the weighted substitution becomes an operator
`TauCeti.MvPowerSeries.weightedSubstCLM` between model spaces. Its matrix has the entries

`aₑₜ = coeff e (g · h₁^t₁ ⋯ h_k^t_k)`

(`TauCeti.MvPowerSeries.matrixCoeff_weightedSubstCLM`): column `t` is the coefficient family of
the image `g hᵗ` of the monomial `Xᵗ`.

Weighted substitutions compose: substituting `h'` with weight `g'` and then `h` with weight `g`
is substituting `h'(h)` with weight `g · g'(h)`
(`TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_comp`). The weight `1` with `h = X` gives the
identity, while `h = 0` gives the map `f ↦ f(0) · g`, since `f(0)` is the constant coefficient
(`TauCeti.MvPowerSeries.restrictedAnalyticSubst_zero_apply`,
`TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_zero_apply`) of rank at most one
(`TauCeti.MvPowerSeries.isFiniteRank_weightedSubstCLM_zero`). Row compactness of weighted
substitutions converging on a larger polydisc is in
`TauCeti.Analysis.Normed.Operator.RowCompact.WeightedSubst`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM`: the operator `f ↦ g · f(h)` between
  restricted-series algebras.
* `TauCeti.MvPowerSeries.weightedSubstCLM`: the same operator at unit radius, between the
  coefficient model spaces.

## Main results

* `TauCeti.MvPowerSeries.matrixCoeff_weightedSubstCLM`: the matrix entries `coeff e (g hᵗ)`.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_comp`,
  `TauCeti.MvPowerSeries.weightedSubstCLM_comp`: the composition law.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_one_X`,
  `TauCeti.MvPowerSeries.weightedSubstCLM_one_X`: the identity.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_zero_apply`: substituting zero gives the
  constant coefficient, at all radii.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_zero_apply`,
  `TauCeti.MvPowerSeries.weightedSubstCLM_zero_apply`,
  `TauCeti.MvPowerSeries.isFiniteRank_weightedSubstCLM_zero`: substitution of zero has finite
  rank.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
* B. Dwork, *On the zeta function of a hypersurface*, Publ. Math. IHÉS **12** (1962), 5–68.
-/

public section

open scoped ZeroAtInfty

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {k m : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

section Restricted

variable {r : Fin k → ℝ} {s : τ → ℝ} [∀ j, Fact (0 < s j)]

/-- **Substituting zero** evaluates at the origin: `f(0)` is the constant coefficient of `f`. -/
theorem restrictedAnalyticSubst_zero_apply
    (hh : ∀ i, ‖(0 : Fin k → IsRestricted.subring (R := R) s) i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedAnalyticSubst 0 hh f =
      algebraMap R _ (constantCoeff (f : MvPowerSeries (Fin k) R)) := by
  -- Every monomial but the constant one vanishes at zero.
  refine (hasSum_restrictedAnalyticSubst _ _ _).unique ?_
  convert hasSum_ite_eq (0 : Fin k →₀ ℕ)
    (algebraMap R (IsRestricted.subring (R := R) s) (constantCoeff (f : MvPowerSeries (Fin k) R)))
    using 2 with t
  split_ifs with ht
  · simp [ht]
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 ht
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi]), mul_zero]

variable [∀ i, Fact (0 < r i)]

/-- **Weighted substitution.** For `g ∈ R{Y/s}` and `hᵢ ∈ R{Y/s}` with `‖hᵢ‖ ≤ rᵢ`, the continuous
`R`-linear map `R{X/r} → R{Y/s}` sending `f` to `g · f(h)`. -/
noncomputable def restrictedWeightedSubstCLM (g : IsRestricted.subring (R := R) s)
    (h : Fin k → IsRestricted.subring (R := R) s) (hh : ∀ i, ‖h i‖ ≤ r i) :
    IsRestricted.subring (R := R) r →L[R] IsRestricted.subring (R := R) s where
  toLinearMap := LinearMap.mulLeft R g ∘ₗ (restrictedAnalyticSubst h hh).toLinearMap
  cont := continuous_const.mul (continuous_restrictedAnalyticSubst h hh)

/-- The weighted substitution sends `f` to `g · f(h)`. -/
@[simp]
theorem restrictedWeightedSubstCLM_apply (g : IsRestricted.subring (R := R) s)
    (h : Fin k → IsRestricted.subring (R := R) s) (hh : ∀ i, ‖h i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedWeightedSubstCLM g h hh f = g * restrictedAnalyticSubst h hh f :=
  (rfl)

/-- The weighted substitution is bounded by the norm of its weight: `‖g · f(h)‖ ≤ ‖g‖ ‖f‖`. -/
theorem norm_restrictedWeightedSubstCLM_apply_le (g : IsRestricted.subring (R := R) s)
    (h : Fin k → IsRestricted.subring (R := R) s) (hh : ∀ i, ‖h i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedWeightedSubstCLM g h hh f‖ ≤ ‖g‖ * ‖f‖ := by
  rw [restrictedWeightedSubstCLM_apply]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_restrictedAnalyticSubst_le h hh f) (norm_nonneg g))

/-- **Composition of weighted substitutions**: substituting `h'` with weight `g'`, then `h` with
weight `g`, is substituting `h'(h)` with weight `g · g'(h)`. -/
theorem restrictedWeightedSubstCLM_comp {r' : Fin m → ℝ} [∀ j, Fact (0 < r' j)]
    (g : IsRestricted.subring (R := R) s) (h : Fin k → IsRestricted.subring (R := R) s)
    (hh : ∀ i, ‖h i‖ ≤ r i) (g' : IsRestricted.subring (R := R) r)
    (h' : Fin m → IsRestricted.subring (R := R) r) (hh' : ∀ j, ‖h' j‖ ≤ r' j) :
    (restrictedWeightedSubstCLM g h hh).comp (restrictedWeightedSubstCLM g' h' hh') =
      restrictedWeightedSubstCLM (g * restrictedAnalyticSubst h hh g')
        (fun j ↦ restrictedAnalyticSubst h hh (h' j))
        (fun j ↦ (norm_restrictedAnalyticSubst_le h hh (h' j)).trans (hh' j)) := by
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, restrictedWeightedSubstCLM_apply, map_mul,
    restrictedAnalyticSubst_restrictedAnalyticSubst, mul_assoc]

/-- **The identity is a weighted substitution**: weight `1` and `h = X`. -/
theorem restrictedWeightedSubstCLM_one_X [NormOneClass R] :
    restrictedWeightedSubstCLM (s := r) 1
        (fun i ↦ ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩)
        (fun i ↦ (norm_X i).le) = ContinuousLinearMap.id R _ := by
  ext1 f
  rw [restrictedWeightedSubstCLM_apply, restrictedAnalyticSubst_self, one_mul, AlgHom.id_apply,
    ContinuousLinearMap.id_apply]

/-- **Substituting zero**: the weighted substitution with `h = 0` sends `f` to `f(0) • g`. -/
theorem restrictedWeightedSubstCLM_zero_apply (g : IsRestricted.subring (R := R) s)
    (hh : ∀ i, ‖(0 : Fin k → IsRestricted.subring (R := R) s) i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedWeightedSubstCLM g 0 hh f = constantCoeff (f : MvPowerSeries (Fin k) R) • g := by
  rw [restrictedWeightedSubstCLM_apply, restrictedAnalyticSubst_zero_apply, mul_comm,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

end Restricted

section Coefficients

/-- **Weighted substitution on the coefficient model.** At unit radius, the weighted substitution
`f ↦ g · f(h)`, transported along the coefficient isometries to an operator between the model
spaces `C₀(Fin k →₀ ℕ, R)` and `C₀(τ →₀ ℕ, R)`. -/
noncomputable def weightedSubstCLM (g : IsRestricted.subring (R := R) fun _ : τ ↦ (1 : ℝ))
    (h : Fin k → IsRestricted.subring (R := R) fun _ : τ ↦ (1 : ℝ)) (hh : ∀ i, ‖h i‖ ≤ 1) :
    C₀(WithDiscreteTopology (Fin k →₀ ℕ), R) →L[R] C₀(WithDiscreteTopology (τ →₀ ℕ), R) :=
  restrictedCoeffLinearIsometryEquiv.toContinuousLinearEquiv.arrowCongrEquiv
    restrictedCoeffLinearIsometryEquiv.toContinuousLinearEquiv (restrictedWeightedSubstCLM g h hh)

variable (g : IsRestricted.subring (R := R) fun _ : τ ↦ (1 : ℝ))
  (h : Fin k → IsRestricted.subring (R := R) fun _ : τ ↦ (1 : ℝ)) (hh : ∀ i, ‖h i‖ ≤ 1)

/-- The coefficient-model weighted substitution is the Tate-algebra weighted substitution read
through the coefficient isometries. -/
theorem weightedSubstCLM_apply (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R)) :
    weightedSubstCLM g h hh x = restrictedCoeffLinearIsometryEquiv
      (restrictedWeightedSubstCLM g h hh (restrictedCoeffLinearIsometryEquiv.symm x)) := by
  simp [weightedSubstCLM]

/-- The coordinate `e` of the image of `x` is the coefficient of `Yᵉ` in `g · f(h)`, where `f` is
the series with coefficient family `x`. -/
@[simp]
theorem weightedSubstCLM_apply_toTopology (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R))
    (e : τ →₀ ℕ) :
    weightedSubstCLM g h hh x (.toTopology ⊥ e) =
      coeff e ((g : MvPowerSeries τ R) *
        (restrictedAnalyticSubst h hh (restrictedCoeffLinearIsometryEquiv.symm x) :
          MvPowerSeries τ R)) := by
  rw [weightedSubstCLM_apply, restrictedCoeffLinearIsometryEquiv_apply,
    restrictedWeightedSubstCLM_apply, Subring.coe_mul]

/-- **The matrix of a weighted substitution**: the entry in row `e` and column `t` is the
coefficient of `Yᵉ` in `g · h₁^t₁ ⋯ h_k^t_k`, the image of the monomial `Xᵗ`. -/
@[simp]
theorem matrixCoeff_weightedSubstCLM [DecidableEq (WithDiscreteTopology (Fin k →₀ ℕ))]
    (e : τ →₀ ℕ) (t : Fin k →₀ ℕ) :
    (weightedSubstCLM g h hh).matrixCoeff (.toTopology ⊥ e) (.toTopology ⊥ t) =
      coeff e ((g : MvPowerSeries τ R) * ∏ i, (h i : MvPowerSeries τ R) ^ t i) := by
  have hx : (restrictedCoeffLinearIsometryEquiv.symm
      (ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) (1 : R)) :
        IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) =
      ⟨monomial t 1, isRestricted_monomial _ t 1⟩ := by
    refine Subtype.ext <| MvPowerSeries.ext fun s ↦ ?_
    classical
    rw [restrictedCoeffLinearIsometryEquiv_symm_apply, ZeroAtInftyContinuousMap.single_apply,
      coeff_monomial]
    simp
  rw [ContinuousLinearMap.matrixCoeff_apply, weightedSubstCLM_apply_toTopology, hx,
    restrictedAnalyticSubst_apply, restrictedEval₂_monomial, map_one, one_mul]
  simp only [SubmonoidClass.coe_pow, SubmonoidClass.coe_finsetProd]

/-- **Composition of coefficient-model weighted substitutions**: substituting `h'` with weight
`g'`, then `h` with weight `g`, is substituting `h'(h)` with weight `g · g'(h)`. -/
theorem weightedSubstCLM_comp (g' : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
    (h' : Fin m → IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
    (hh' : ∀ j, ‖h' j‖ ≤ 1) :
    (weightedSubstCLM g h hh).comp (weightedSubstCLM g' h' hh') =
      weightedSubstCLM (g * restrictedAnalyticSubst h hh g')
        (fun j ↦ restrictedAnalyticSubst h hh (h' j))
        (fun j ↦ (norm_restrictedAnalyticSubst_le h hh (h' j)).trans (hh' j)) := by
  ext1 x
  rw [ContinuousLinearMap.comp_apply, weightedSubstCLM_apply, weightedSubstCLM_apply,
    LinearIsometryEquiv.symm_apply_apply, ← ContinuousLinearMap.comp_apply,
    restrictedWeightedSubstCLM_comp, weightedSubstCLM_apply]

/-- **The identity is a weighted substitution** on the coefficient model: weight `1` and
`h = X`. -/
theorem weightedSubstCLM_one_X [NormOneClass R] :
    weightedSubstCLM (τ := Fin k) 1
        (fun i ↦ ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩)
        (fun i ↦ (norm_X i).le) = ContinuousLinearMap.id R _ := by
  ext1 x
  rw [weightedSubstCLM_apply, restrictedWeightedSubstCLM_one_X, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.id_apply]

/-- **Substituting zero**: the weighted substitution with `h = 0` sends the coefficient family
`x` of `f` to `f(0) • g`. -/
theorem weightedSubstCLM_zero_apply (x : C₀(WithDiscreteTopology (Fin k →₀ ℕ), R)) :
    weightedSubstCLM g 0 (fun _ ↦ by simp) x =
      x (.toTopology ⊥ 0) • restrictedCoeffLinearIsometryEquiv g := by
  rw [weightedSubstCLM_apply, restrictedWeightedSubstCLM_zero_apply, map_smul,
    ← coeff_zero_eq_constantCoeff_apply, restrictedCoeffLinearIsometryEquiv_symm_apply]

/-- **Substituting zero has finite rank**: the weighted substitution with `h = 0` takes values in
the line spanned by the coefficient family of `g`. -/
theorem isFiniteRank_weightedSubstCLM_zero :
    LinearMap.IsFiniteRank (weightedSubstCLM g (0 : Fin k → _) (fun _ ↦ by simp) :
      C₀(WithDiscreteTopology (Fin k →₀ ℕ), R) →ₗ[R] C₀(WithDiscreteTopology (τ →₀ ℕ), R)) :=
  LinearMap.isFiniteRank_iff_forall_mem.2
    ⟨R ∙ restrictedCoeffLinearIsometryEquiv g, Submodule.fg_span_singleton _, fun x ↦ by
      rw [ContinuousLinearMap.coe_coe, weightedSubstCLM_zero_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩

end Coefficients

end TauCeti.MvPowerSeries
