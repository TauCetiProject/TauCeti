/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPolynomial.NormCoeff

/-!
# Substituting polynomials into Tate algebras

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1`, and let `a s` be polynomials in
the variables `τ`, indexed by finitely many `s : σ`, without constant term and with all
coefficients of norm at most `1`. Mathlib's formal substitution `MvPowerSeries.subst`, which sends
`X s` to `a s`, then carries unit-radius restricted series in `σ` to unit-radius restricted series
in `τ` without increasing the Gauss norm. It therefore restricts to an `R`-algebra homomorphism of
Tate algebras, and two mutually inverse substitutions give an isometric `R`-algebra isomorphism.

Renamings of the variables are the simplest examples. The triangular substitutions
`Xᵢ ↦ Xᵢ + Yᵅⁱ` used to make a restricted series distinguished in one variable are the examples
this file is written for.

Vanishing constant terms ensure that the formal substitution is defined. Evaluating a Tate algebra
at arbitrary elements of norm at most `1` requires the completeness of the target and is not treated
here.

## Main results

* `MvPowerSeries.hasSubst_coe`: polynomials without constant term in finitely many variables
  form a substitutable family, and `MvPolynomial.coe_finsuppProd_pow`: the coercion to power
  series commutes with the products of powers that appear in the coefficients of a
  substitution.
* `MvPowerSeries.norm_coeff_subst_le`: each coefficient of a substitution is bounded by the
  supremum of the terms contributing to it, in any ultrametric seminormed commutative ring.
* `MvPowerSeries.norm_coeff_subst_coe_le` and `MvPowerSeries.norm_coeff_subst_coe_sub_le`: for a
  substitution of unit-ball polynomials, a coefficient is controlled by the coefficients of the
  substituted series at the exponents contributing to it, possibly after isolating one of them.
* `MvPowerSeries.IsRestricted.subst`: substitution of unit-ball polynomials without constant
  term preserves unit-radius restrictedness.
* `MvPowerSeries.restrictedSubst`: the resulting `R`-algebra homomorphism of Tate algebras, and
  `MvPowerSeries.norm_restrictedSubst_le`: it does not increase the Gauss norm.
* `MvPowerSeries.restrictedSubstEquiv`: two mutually inverse substitutions give an
  `R`-algebra isomorphism of Tate algebras, which is an isometry
  (`MvPowerSeries.norm_restrictedSubstEquiv`).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.3 and §5.2.4.
-/

public section

namespace MvPowerSeries

open Filter
open scoped Topology

section CommRing

variable {σ τ R : Type*} [CommRing R]

/-- The coercion of polynomials to power series commutes with products of powers. -/
theorem _root_.MvPolynomial.coe_finsuppProd_pow (a : σ → MvPolynomial τ R) (d : σ →₀ ℕ) :
    ((d.prod fun s n ↦ a s ^ n : MvPolynomial τ R) : MvPowerSeries τ R) =
      d.prod fun s n ↦ (a s : MvPowerSeries τ R) ^ n := by
  simp only [Finsupp.prod, ← MvPolynomial.coe_pow]
  exact map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)) _ _

/-- Polynomials without constant term form a substitutable family over finitely many
variables. -/
theorem hasSubst_coe [Finite σ] {a : σ → MvPolynomial τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) :
    HasSubst fun s ↦ (a s : MvPowerSeries τ R) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, ha]

end CommRing

section SeminormedCommRing

variable {σ τ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]

/-- **Ultrametric bound for the coefficients of a substitution.** The coefficient of a
substitution is a finite sum of the products `coeff d f * coeff e (∏ₛ (a s) ^ (d s))`, so it is
bounded by any common bound on these products. -/
theorem norm_coeff_subst_le {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (e : τ →₀ ℕ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ d, ‖coeff d f * coeff e (d.prod fun s n ↦ a s ^ n)‖ ≤ r) :
    ‖coeff e (subst a f)‖ ≤ r := by
  rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun d _ ↦ h d

variable [NormOneClass R]

/-- **Coefficients of a substitution of unit-ball polynomials.** A coefficient of the
substitution is bounded by any common bound on the coefficients of `f` at the exponents `d` whose
polynomial `∏ₛ (a s) ^ (d s)` contributes to it. -/
theorem norm_coeff_subst_coe_le [Finite σ] {a : σ → MvPolynomial τ R}
    (ha₀ : ∀ s, (a s).constantCoeff = 0) (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)
    (f : MvPowerSeries σ R) (e : τ →₀ ℕ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ d, (d.prod fun s n ↦ a s ^ n).coeff e ≠ 0 → ‖coeff d f‖ ≤ r) :
    ‖coeff e (subst (fun s ↦ (a s : MvPowerSeries τ R)) f)‖ ≤ r := by
  refine norm_coeff_subst_le (hasSubst_coe ha₀) f e hr fun d ↦ ?_
  rw [← MvPolynomial.coe_finsuppProd_pow, MvPolynomial.coeff_coe]
  by_cases hd : (d.prod fun s n ↦ a s ^ n).coeff e = 0
  · simp [hd, hr]
  · exact (norm_mul_le _ _).trans <| (mul_le_of_le_one_right (norm_nonneg _)
      (TauCeti.MvPolynomial.norm_coeff_prod_pow_le_one norm_one.le d
        (fun s _ ↦ ha₁ s) e)).trans (h d hd)

/-- **Isolating one term of a substitution.** Up to the contribution
`coeff ν f * coeff e (∏ₛ (a s) ^ (ν s))` of a single exponent `ν`, a coefficient of a substitution
of unit-ball polynomials is bounded by the coefficients of `f` at the other exponents whose
polynomials contribute to it. -/
theorem norm_coeff_subst_coe_sub_le [Finite σ] {a : σ → MvPolynomial τ R}
    (ha₀ : ∀ s, (a s).constantCoeff = 0) (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)
    (f : MvPowerSeries σ R) (ν : σ →₀ ℕ) (e : τ →₀ ℕ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ d ≠ ν, (d.prod fun s n ↦ a s ^ n).coeff e ≠ 0 → ‖coeff d f‖ ≤ r) :
    ‖coeff e (f.subst fun s ↦ (a s : MvPowerSeries τ R)) -
      coeff ν f * (ν.prod fun s n ↦ a s ^ n).coeff e‖ ≤ r := by
  have hsub : coeff e (f.subst fun s ↦ (a s : MvPowerSeries τ R)) -
      coeff ν f * (ν.prod fun s n ↦ a s ^ n).coeff e =
      coeff e ((f - monomial ν (coeff ν f)).subst fun s ↦ (a s : MvPowerSeries τ R)) := by
    rw [subst_sub (hasSubst_coe ha₀), subst_monomial (hasSubst_coe ha₀),
      ← MvPolynomial.coe_finsuppProd_pow, map_sub, ← MvPolynomial.coeff_coe, algebraMap_apply,
      coeff_C_mul]
    simp
  rw [hsub]
  refine norm_coeff_subst_coe_le ha₀ ha₁ _ e hr fun d hd ↦ ?_
  by_cases hdν : d = ν
  · subst hdν
    simp [hr]
  · simpa [coeff_monomial_ne hdν] using h d hdν hd

end SeminormedCommRing

variable {σ τ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

omit [IsUltrametricDist R] in
/-- Restrictedness at the unit radius is convergence of the coefficient norms to zero. -/
theorem isRestricted_one_iff {f : MvPowerSeries σ R} :
    IsRestricted (fun _ ↦ 1) f ↔ Tendsto (fun t ↦ ‖coeff t f‖) cofinite (𝓝 0) := by
  simp [IsRestricted]

variable [NormOneClass R]

/-- **Substitution of unit-ball polynomials preserves restrictedness.** If finitely many
polynomials without constant term have all coefficients of norm at most `1`, then substituting
them into a unit-radius restricted series gives a unit-radius restricted series. -/
theorem IsRestricted.subst [Finite σ] {a : σ → MvPolynomial τ R}
    (ha₀ : ∀ s, (a s).constantCoeff = 0) (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)
    {f : MvPowerSeries σ R} (hf : IsRestricted (fun _ ↦ 1) f) :
    IsRestricted (fun _ ↦ 1) (f.subst fun s ↦ (a s : MvPowerSeries τ R)) := by
  classical
  rw [isRestricted_one_iff] at hf ⊢
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun e ↦ hb.trans_le (norm_nonneg _),
    fun ε hε ↦ ?_⟩
  -- Only the finitely many large coefficients of `f` can produce a large coefficient, and each
  -- of them contributes through a polynomial with finite support.
  have hB : {d | ε / 2 ≤ ‖coeff d f‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using hf.eventually (gt_mem_nhds (half_pos hε))
  have hE : (⋃ d ∈ {d | ε / 2 ≤ ‖coeff d f‖},
      ((d.prod fun s n ↦ a s ^ n : MvPolynomial τ R).support : Set (τ →₀ ℕ))).Finite :=
    hB.biUnion fun d _ ↦ Finset.finite_toSet _
  filter_upwards [hE.compl_mem_cofinite] with e he
  refine (norm_coeff_subst_coe_le ha₀ ha₁ f e (half_pos hε).le fun d hd ↦ ?_).trans_lt
    (half_lt_self hε)
  by_contra hlt
  exact he (Set.mem_biUnion (le_of_not_ge hlt) (MvPolynomial.mem_support_iff.mpr hd))

variable [Finite σ] (a : σ → MvPolynomial τ R) (ha₀ : ∀ s, (a s).constantCoeff = 0)
  (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1)

/-- **Substitution of unit-ball polynomials as a map of Tate algebras.** Substituting
polynomials without constant term whose coefficients have norm at most `1` is an `R`-algebra
homomorphism between the unit-radius Tate algebras. -/
noncomputable def restrictedSubst :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →ₐ[R]
      IsRestricted.subring (R := R) (fun _ : τ ↦ 1) where
  toFun f := ⟨(f : MvPowerSeries σ R).subst fun s ↦ (a s : MvPowerSeries τ R),
    IsRestricted.subst ha₀ ha₁ f.2⟩
  map_one' := Subtype.ext <| by simpa using map_one (substAlgHom (hasSubst_coe ha₀))
  map_mul' f g := Subtype.ext <| by simp [subst_mul (hasSubst_coe ha₀)]
  map_zero' := Subtype.ext <| by simpa using map_zero (substAlgHom (hasSubst_coe ha₀))
  map_add' f g := Subtype.ext <| by simp [subst_add (hasSubst_coe ha₀)]
  commutes' r := Subtype.ext <| by simp

/-- The map of Tate algebras is Mathlib's formal substitution. -/
@[simp]
theorem coe_restrictedSubst (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (restrictedSubst a ha₀ ha₁ f : MvPowerSeries τ R) =
      (f : MvPowerSeries σ R).subst fun s ↦ (a s : MvPowerSeries τ R) := (rfl)

/-- Substitution of unit-ball polynomials does not increase the Gauss norm. -/
theorem norm_restrictedSubst_le (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    ‖restrictedSubst a ha₀ ha₁ f‖ ≤ ‖f‖ := by
  rw [norm_le_iff (norm_nonneg _)]
  intro e
  simp only [one_pow, Finsupp.prod_fun_one, mul_one, coe_restrictedSubst]
  refine norm_coeff_subst_coe_le ha₀ ha₁ _ e (norm_nonneg _) fun d _ ↦ ?_
  simpa using norm_coeff_mul_prod_le f d

variable [Finite τ] (b : τ → MvPolynomial σ R) (hb₀ : ∀ t, (b t).constantCoeff = 0)
  (hb₁ : ∀ t u, ‖(b t).coeff u‖ ≤ 1)

/-- Substituting `b` after `a` is substituting the polynomials `aeval b (a s)`. -/
private theorem restrictedSubst_restrictedSubst
    (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    restrictedSubst b hb₀ hb₁ (restrictedSubst a ha₀ ha₁ f) = f := by
  apply Subtype.ext
  rw [coe_restrictedSubst, coe_restrictedSubst,
    subst_comp_subst_apply (hasSubst_coe ha₀) (hasSubst_coe hb₀)]
  have h : (fun s ↦ ((a s : MvPowerSeries τ R)).subst fun t ↦ (b t : MvPowerSeries σ R)) =
      X := by
    funext s
    rw [← coe_substAlgHom (hasSubst_coe hb₀), substAlgHom_coe, ← MvPolynomial.coe_X,
      ← hab s]
    exact (MvPolynomial.comp_aeval_apply b (MvPolynomial.coeToMvPowerSeries.algHom R) (a s)).symm
  rw [h, subst_self, id]

/-- **Isomorphisms of Tate algebras from inverse substitutions.** If two families of unit-ball
polynomials without constant term are inverse to each other under substitution, the substitutions
are mutually inverse `R`-algebra isomorphisms of the unit-radius Tate algebras. -/
noncomputable def restrictedSubstEquiv
    (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t) :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) ≃ₐ[R]
      IsRestricted.subring (R := R) (fun _ : τ ↦ 1) :=
  AlgEquiv.ofAlgHom (restrictedSubst a ha₀ ha₁) (restrictedSubst b hb₀ hb₁)
    (AlgHom.ext <| restrictedSubst_restrictedSubst b hb₀ hb₁ a ha₀ ha₁ hba)
    (AlgHom.ext <| restrictedSubst_restrictedSubst a ha₀ ha₁ b hb₀ hb₁ hab)

/-- The isomorphism of Tate algebras is the substitution of `a`. -/
@[simp]
theorem coe_restrictedSubstEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t)
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f : MvPowerSeries τ R) =
      (f : MvPowerSeries σ R).subst fun s ↦ (a s : MvPowerSeries τ R) :=
  coe_restrictedSubst a ha₀ ha₁ f

/-- The inverse isomorphism of Tate algebras is the substitution of `b`. -/
@[simp]
theorem coe_restrictedSubstEquiv_symm
    (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t)
    (f : IsRestricted.subring (R := R) (fun _ : τ ↦ 1)) :
    ((restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba).symm f : MvPowerSeries σ R) =
      (f : MvPowerSeries τ R).subst fun t ↦ (b t : MvPowerSeries σ R) :=
  coe_restrictedSubst b hb₀ hb₁ f

/-- An isomorphism of Tate algebras given by inverse substitutions preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedSubstEquiv (hab : ∀ s, MvPolynomial.aeval b (a s) = MvPolynomial.X s)
    (hba : ∀ t, MvPolynomial.aeval a (b t) = MvPolynomial.X t)
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    ‖restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f‖ = ‖f‖ := by
  refine le_antisymm (norm_restrictedSubst_le a ha₀ ha₁ f) ?_
  calc ‖f‖ = ‖(restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba).symm
        (restrictedSubstEquiv a ha₀ ha₁ b hb₀ hb₁ hab hba f)‖ := by rw [AlgEquiv.symm_apply_apply]
    _ ≤ _ := norm_restrictedSubst_le b hb₀ hb₁ _

end MvPowerSeries
