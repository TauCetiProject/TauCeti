/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.FiniteRank
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst

/-!
# Weighted substitution operators on restricted power series

Let `R` be a complete ultrametric normed commutative ring. For series `g, h₁, …, h_k` restricted
at polyradii `s` in variables `Y`, with Gauss norms `‖hᵢ‖_s ≤ rᵢ`, the **weighted substitution
operator** is the continuous `R`-linear map

`R{X/r} → R{Y/s}, f ↦ g · f(h)`,

where `f(h)` is the analytic substitution `TauCeti.MvPowerSeries.restrictedAnalyticSubst`. It
does not increase norms by more than the factor `‖g‖`, and it sends the monomial `Xᵗ` to
`g hᵗ = g h₁^t₁ ⋯ h_k^t_k`; in coefficient coordinates, the column of index `t` of its matrix is
therefore the coefficient family of `g hᵗ`. Dwork's operators and the `U_p`-operators on
overconvergent functions are built from operators of this shape, the basic examples of compact
operators on Banach spaces of analytic functions.

Two degenerate cases bound the class. Substituting `h = 0` gives `f ↦ f(0) g`, whose range lies
in the line spanned by `g`, so it has finite rank. Substituting the variables themselves with
weight `g = 1` gives the identity, which is not completely continuous as soon as there is a
variable. Weighted substitutions compose: substituting `h₂` with weight `g₂` and then `h₁` with
weight `g₁` is the weighted substitution of `h₂(h₁)` with weight `g₁ · g₂(h₁)`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM`: the operator `f ↦ g · f(h)`.

## Main results

* `TauCeti.MvPowerSeries.norm_restrictedWeightedSubstCLM_apply_le`: `‖g · f(h)‖ ≤ ‖g‖ ‖f‖`.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_monomial`: the image of `Xᵗ` is `g hᵗ`.
* `TauCeti.MvPowerSeries.isFiniteRank_restrictedWeightedSubstCLM_zero`: substituting zero gives
  an operator of finite rank.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_one_X`: substituting the variables with
  weight one is the identity.
* `TauCeti.MvPowerSeries.restrictedWeightedSubstCLM_comp`: the composition law.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {k : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r : Fin k → ℝ} [∀ i, Fact (0 < r i)] {s : τ → ℝ} [∀ j, Fact (0 < s j)]

/-- The **weighted substitution operator** `f ↦ g · f(h)` from `R{X/r}` to `R{Y/s}`, for
series `g` and `hᵢ` restricted at `s` with `‖hᵢ‖ ≤ rᵢ`. Here `f(h)` is the analytic substitution
of the `hᵢ` for the variables `Xᵢ`. -/
noncomputable def restrictedWeightedSubstCLM (g : IsRestricted.subring (R := R) s)
    (h : Fin k → IsRestricted.subring (R := R) s) (hh : ∀ i, ‖h i‖ ≤ r i) :
    IsRestricted.subring (R := R) r →L[R] IsRestricted.subring (R := R) s where
  toLinearMap := LinearMap.mulLeft R g ∘ₗ (restrictedAnalyticSubst h hh).toLinearMap
  cont := continuous_const.mul (continuous_restrictedAnalyticSubst h hh)

variable (g : IsRestricted.subring (R := R) s) (h : Fin k → IsRestricted.subring (R := R) s)
  (hh : ∀ i, ‖h i‖ ≤ r i)

/-- A weighted substitution multiplies the analytic substitution by the weight. -/
@[simp]
theorem restrictedWeightedSubstCLM_apply (f : IsRestricted.subring (R := R) r) :
    restrictedWeightedSubstCLM g h hh f = g * restrictedAnalyticSubst h hh f :=
  (rfl)

/-- A weighted substitution increases norms at most by the norm of its weight. -/
theorem norm_restrictedWeightedSubstCLM_apply_le (f : IsRestricted.subring (R := R) r) :
    ‖restrictedWeightedSubstCLM g h hh f‖ ≤ ‖g‖ * ‖f‖ := by
  rw [restrictedWeightedSubstCLM_apply]
  exact (norm_mul_le _ _).trans <|
    mul_le_mul_of_nonneg_left (norm_restrictedAnalyticSubst_le h hh f) (norm_nonneg g)

/-- A weighted substitution sends the monomial `Xᵗ` to `g hᵗ`. -/
theorem restrictedWeightedSubstCLM_monomial (t : Fin k →₀ ℕ) :
    restrictedWeightedSubstCLM g h hh ⟨monomial t 1, isRestricted_monomial r t 1⟩ =
      g * ∏ i, h i ^ t i := by
  rw [restrictedWeightedSubstCLM_apply, restrictedAnalyticSubst_apply, restrictedEval₂_monomial,
    map_one, one_mul]

/-- Substituting zero with weight `g` sends `f` to `f(0) g`. -/
theorem restrictedWeightedSubstCLM_zero
    (hh₀ : ∀ i, ‖(0 : Fin k → IsRestricted.subring (R := R) s) i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedWeightedSubstCLM g 0 hh₀ f = constantCoeff (f : MvPowerSeries (Fin k) R) • g := by
  rw [restrictedWeightedSubstCLM_apply, restrictedAnalyticSubst_zero, Algebra.smul_def,
    mul_comm]

/-- Substituting zero gives an operator of finite rank: its range lies in the line spanned by the
weight. -/
theorem isFiniteRank_restrictedWeightedSubstCLM_zero
    (hh₀ : ∀ i, ‖(0 : Fin k → IsRestricted.subring (R := R) s) i‖ ≤ r i) :
    (restrictedWeightedSubstCLM g 0 hh₀ : IsRestricted.subring (R := R) r →ₗ[R]
      IsRestricted.subring (R := R) s).IsFiniteRank := by
  refine LinearMap.isFiniteRank_iff_forall_mem.2 ⟨_, Submodule.fg_span_singleton g, fun f ↦ ?_⟩
  rw [ContinuousLinearMap.coe_coe, restrictedWeightedSubstCLM_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)

/-- Substituting the variables themselves with weight one is the identity. -/
@[simp]
theorem restrictedWeightedSubstCLM_one_X [NormOneClass R] :
    restrictedWeightedSubstCLM (s := r) 1
        (fun i ↦ ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩)
        (fun i ↦ (norm_X i).le) = ContinuousLinearMap.id R _ := by
  ext1 f
  simp [restrictedAnalyticSubst_self]

/-- **Composition of weighted substitutions.** Substituting `h₂` with weight `g₂` and then `h₁`
with weight `g₁` is substituting `h₂(h₁)` with weight `g₁ · g₂(h₁)`. -/
theorem restrictedWeightedSubstCLM_comp {m : ℕ} {s' : Fin m → ℝ} [∀ j, Fact (0 < s' j)]
    (g₁ : IsRestricted.subring (R := R) s) (h₁ : Fin m → IsRestricted.subring (R := R) s)
    (hh₁ : ∀ j, ‖h₁ j‖ ≤ s' j) (g₂ : IsRestricted.subring (R := R) s')
    (h₂ : Fin k → IsRestricted.subring (R := R) s') (hh₂ : ∀ i, ‖h₂ i‖ ≤ r i) :
    (restrictedWeightedSubstCLM g₁ h₁ hh₁).comp (restrictedWeightedSubstCLM g₂ h₂ hh₂) =
      restrictedWeightedSubstCLM (g₁ * restrictedAnalyticSubst h₁ hh₁ g₂)
        (fun i ↦ restrictedAnalyticSubst h₁ hh₁ (h₂ i))
        (fun i ↦ (norm_restrictedAnalyticSubst_le h₁ hh₁ (h₂ i)).trans (hh₂ i)) := by
  ext1 f
  simp [restrictedAnalyticSubst_restrictedAnalyticSubst, mul_assoc]

end TauCeti.MvPowerSeries
