/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Analytic substitution into restricted power series

Let `R` be a complete ultrametric normed commutative ring, let `r` be positive radii for the
variables `X₁, …, X_k`, and let `g₁, …, g_k` be series restricted at positive polyradii `s` in
variables `Y`, with Gauss norms `‖gᵢ‖_s ≤ rᵢ`. The target algebra `R{Y/s}` is a complete
ultrametric normed ring, so a series `f ∈ R{X/r}` can be evaluated at `g`:

```text
f(g) = ∑ₜ fₜ g₁^t₁ ⋯ g_k^t_k,
```

the convergent sum of `MvPowerSeries.restrictedEval₂`. This is the analytic substitution
`R{X/r} → R{Y/s}`. It is an `R`-algebra homomorphism that does not increase Gauss norms, and it
is the only continuous one sending `Xᵢ` to `gᵢ`. Unlike Mathlib's formal substitution
`MvPowerSeries.subst`, it allows the `gᵢ` to have nonzero, even non-nilpotent, constant terms,
paying for this with the norm bounds; where both are defined they agree.

The universal property gives the identity and composition laws and the compatibility with
evaluation. Translation `Xᵢ ↦ Xᵢ + aᵢ` by constants with `‖aᵢ‖ ≤ rᵢ` is an example in which the
constant terms do not vanish: it is an isometric `R`-algebra automorphism of `R{X/r}`, with
inverse the translation by `-a`. Such substitutions are the changes of disc coordinates on closed
polydiscs of arbitrary real radii. Translation of unit-radius topological restricted series by
power-bounded constants is `TauCeti.ValuationSpectrum.taylorHom`. The Gauss-normed construction
here allows radii that are not norms of elements of `R`, which no weight family can encode.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedAnalyticSubst`: the substitution `f ↦ f(g)` as an
  `R`-algebra homomorphism `R{X/r} →ₐ[R] R{Y/s}`.
* `TauCeti.MvPowerSeries.restrictedTranslate` and `TauCeti.MvPowerSeries.restrictedTranslateEquiv`:
  translation by `a`, as an algebra homomorphism and as an algebra automorphism.

## Main results

* `TauCeti.MvPowerSeries.coeff_restrictedAnalyticSubst`: the coefficients of `f(g)` are the
  convergent sums `∑' t, fₜ · coeff e (g₁^t₁ ⋯ g_k^t_k)`.
* `TauCeti.MvPowerSeries.norm_restrictedAnalyticSubst_le`: substitution is contractive.
* `TauCeti.MvPowerSeries.eq_restrictedAnalyticSubst`: uniqueness among continuous algebra
  homomorphisms.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_self` and
  `TauCeti.MvPowerSeries.restrictedAnalyticSubst_comp`: the identity and composition laws.
* `TauCeti.MvPowerSeries.restrictedEval₂_restrictedAnalyticSubst`: evaluating `f(g)` at `b` is
  evaluating `f` at `g(b)`.
* `TauCeti.MvPowerSeries.restrictedMap_restrictedAnalyticSubst`: compatibility with bounded
  coefficient maps.
* `TauCeti.MvPowerSeries.coe_restrictedAnalyticSubst_eq_subst`: agreement with Mathlib's formal
  substitution whenever the latter is defined.
* `TauCeti.MvPowerSeries.norm_restrictedTranslate`: translation preserves the Gauss norm.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1, for
  Tate algebras and their homomorphisms.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

variable {k : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r : Fin k → ℝ} {s : τ → ℝ} [∀ j, Fact (0 < s j)]

section AnalyticSubst

variable (g : Fin k → IsRestricted.subring (R := R) s) (hg : ∀ i, ‖g i‖ ≤ r i)

/-- **Analytic substitution.** For series `gᵢ ∈ R{Y/s}` with `‖gᵢ‖ ≤ rᵢ`, the `R`-algebra
homomorphism `R{X/r} → R{Y/s}` sending `f = ∑ₜ fₜ Xᵗ` to the convergent sum `∑ₜ fₜ gᵗ`. The `gᵢ`
may have nonzero constant terms. -/
noncomputable def restrictedAnalyticSubst :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s :=
  { restrictedEval₂ (algebraMap R _) g (fun a ↦ (norm_algebraMap_isRestrictedSubring a).le) hg with
    commutes' := restrictedEval₂_algebraMap _ _ _ _ }

/-- Analytic substitution is evaluation at `g` in the complete ring `R{Y/s}`. -/
theorem restrictedAnalyticSubst_apply (f : IsRestricted.subring (R := R) r) :
    restrictedAnalyticSubst g hg f =
      restrictedEval₂ (algebraMap R _) g (fun a ↦ (norm_algebraMap_isRestrictedSubring a).le) hg
        f := (rfl)

/-- The substitution `f(g)` is the sum of the substituted monomials `fₜ gᵗ`. -/
theorem hasSum_restrictedAnalyticSubst (f : IsRestricted.subring (R := R) r) :
    HasSum (fun t : Fin k →₀ ℕ ↦
        algebraMap R _ (coeff t (f : MvPowerSeries (Fin k) R)) * ∏ i, g i ^ t i)
      (restrictedAnalyticSubst g hg f) := by
  have h := hasSum_restrictedEval₂ (algebraMap R _) g
    (fun a ↦ (norm_algebraMap_isRestrictedSubring a).le) hg f
  simp only [funext (weightedEvalTerm_def _ g (f : MvPowerSeries (Fin k) R))] at h
  exact h

/-- The coefficient of `Yᵉ` in `f(g)` is the sum of the coefficients of `Yᵉ` in the substituted
monomials `fₜ gᵗ`. -/
theorem hasSum_coeff_restrictedAnalyticSubst (f : IsRestricted.subring (R := R) r)
    (e : τ →₀ ℕ) :
    HasSum (fun t : Fin k →₀ ℕ ↦ coeff t (f : MvPowerSeries (Fin k) R) *
        coeff e (∏ i, (g i : MvPowerSeries τ R) ^ t i))
      (coeff e (restrictedAnalyticSubst g hg f : MvPowerSeries τ R)) := by
  convert (hasSum_restrictedAnalyticSubst g hg f).map
    ((coeff e).toAddMonoidHom.comp (IsRestricted.subring (R := R) s).subtype.toAddMonoidHom)
    (continuous_coeff_isRestrictedSubring e) using 1
  · ext t
    simp [coeff_C_mul]
  · simp

/-- **The coefficient formula for analytic substitution**: the coefficient of `Yᵉ` in `f(g)` is
the convergent sum `∑' t, fₜ · coeff e (g₁^t₁ ⋯ g_k^t_k)`. -/
theorem coeff_restrictedAnalyticSubst (f : IsRestricted.subring (R := R) r) (e : τ →₀ ℕ) :
    coeff e (restrictedAnalyticSubst g hg f : MvPowerSeries τ R) =
      ∑' t : Fin k →₀ ℕ, coeff t (f : MvPowerSeries (Fin k) R) *
        coeff e (∏ i, (g i : MvPowerSeries τ R) ^ t i) :=
  (hasSum_coeff_restrictedAnalyticSubst g hg f e).tsum_eq.symm

/-- Substitution sends the variable `Xᵢ` to `gᵢ`. -/
@[simp]
theorem restrictedAnalyticSubst_X (i : Fin k) :
    restrictedAnalyticSubst g hg ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ = g i :=
  restrictedEval₂_X _ g _ hg i

/-- **Coefficient maps commute with analytic substitution.** For a bounded ring homomorphism
`φ : R →+* S` such that the mapped series `φ(gᵢ)` still satisfy `‖φ(gᵢ)‖ ≤ rᵢ`, mapping the
coefficients of `f(g)` gives `φ(f)(φ(g))`. -/
theorem restrictedMap_restrictedAnalyticSubst {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)
    (hφg : ∀ i, ‖restrictedMap φ hφ (g i)‖ ≤ r i) (f : IsRestricted.subring (R := R) r) :
    restrictedMap φ hφ (restrictedAnalyticSubst g hg f) =
      restrictedAnalyticSubst (fun i ↦ restrictedMap φ hφ (g i)) hφg (restrictedMap φ hφ f) := by
  -- compare coefficients: a bounded `φ` is continuous, so it commutes with the coefficient sums
  have hφc : Continuous φ := AddMonoidHomClass.continuous_of_bound φ C hφ
  refine Subtype.ext <| MvPowerSeries.ext fun e ↦ ?_
  rw [coeff_restrictedMap, ← ((hasSum_coeff_restrictedAnalyticSubst g hg f e).map φ hφc).tsum_eq,
    coeff_restrictedAnalyticSubst]
  refine tsum_congr fun t ↦ ?_
  simp [coe_restrictedMap, ← map_pow, ← map_prod, coeff_map]

/-- **Comparison with formal substitution.** When Mathlib's formal substitution of the `gᵢ` is
defined, for instance when their constant coefficients are nilpotent, it agrees with analytic
substitution. -/
theorem coe_restrictedAnalyticSubst_eq_subst
    (hsub : HasSubst fun i ↦ (g i : MvPowerSeries τ R)) (f : IsRestricted.subring (R := R) r) :
    (restrictedAnalyticSubst g hg f : MvPowerSeries τ R) =
      subst (fun i ↦ (g i : MvPowerSeries τ R)) (f : MvPowerSeries (Fin k) R) := by
  ext e
  rw [coeff_restrictedAnalyticSubst, coeff_subst hsub,
    ← tsum_eq_finsum (L := .unconditional _) (coeff_subst_finite hsub _ e)]
  refine tsum_congr fun t ↦ ?_
  rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, smul_eq_mul]

variable [∀ i, Fact (0 < r i)]

/-- **Analytic substitution does not increase the Gauss norm**: `‖f(g)‖_s ≤ ‖f‖_r`. -/
theorem norm_restrictedAnalyticSubst_le (f : IsRestricted.subring (R := R) r) :
    ‖restrictedAnalyticSubst g hg f‖ ≤ ‖f‖ :=
  norm_restrictedEval₂_le _ g _ hg f

/-- Analytic substitution is continuous for the Gauss norms. -/
theorem continuous_restrictedAnalyticSubst : Continuous (restrictedAnalyticSubst g hg) :=
  continuous_restrictedEval₂ _ g _ hg

/-- **Uniqueness of analytic substitution**: a continuous `R`-algebra homomorphism
`R{X/r} → R{Y/s}` sending each `Xᵢ` to `gᵢ` is the substitution `f ↦ f(g)`. -/
theorem eq_restrictedAnalyticSubst
    (ψ : IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s)
    (hψ : Continuous ψ)
    (hX : ∀ i, ψ ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ = g i) :
    ψ = restrictedAnalyticSubst g hg :=
  AlgHom.toRingHom_injective <| eq_restrictedEval₂ _ g _ hg ψ.toRingHom hψ ψ.commutes hX

/-- **Substituting the variables themselves is the identity.** -/
theorem restrictedAnalyticSubst_self [NormOneClass R] :
    restrictedAnalyticSubst (s := r)
        (fun i ↦ ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩)
        (fun i ↦ (norm_X i).le) = AlgHom.id R _ :=
  (eq_restrictedAnalyticSubst _ _ (AlgHom.id R _) continuous_id fun _ ↦ rfl).symm

/-- **Composition of analytic substitutions**: substituting `h` into `f(g)` is substituting the
series `g(h)` into `f`. -/
theorem restrictedAnalyticSubst_comp {m : ℕ} {s' : Fin m → ℝ} [∀ j, Fact (0 < s' j)]
    (g : Fin k → IsRestricted.subring (R := R) s') (hg : ∀ i, ‖g i‖ ≤ r i)
    (h : Fin m → IsRestricted.subring (R := R) s) (hh : ∀ j, ‖h j‖ ≤ s' j) :
    (restrictedAnalyticSubst h hh).comp (restrictedAnalyticSubst g hg) =
      restrictedAnalyticSubst (fun i ↦ restrictedAnalyticSubst h hh (g i))
        (fun i ↦ (norm_restrictedAnalyticSubst_le h hh (g i)).trans (hg i)) :=
  eq_restrictedAnalyticSubst _ _ _
    ((continuous_restrictedAnalyticSubst h hh).comp (continuous_restrictedAnalyticSubst g hg))
    fun i ↦ by simp

/-- Applying two analytic substitutions in turn is substituting the composite series. -/
theorem restrictedAnalyticSubst_restrictedAnalyticSubst {m : ℕ} {s' : Fin m → ℝ}
    [∀ j, Fact (0 < s' j)] (g : Fin k → IsRestricted.subring (R := R) s') (hg : ∀ i, ‖g i‖ ≤ r i)
    (h : Fin m → IsRestricted.subring (R := R) s) (hh : ∀ j, ‖h j‖ ≤ s' j)
    (f : IsRestricted.subring (R := R) r) :
    restrictedAnalyticSubst h hh (restrictedAnalyticSubst g hg f) =
      restrictedAnalyticSubst (fun i ↦ restrictedAnalyticSubst h hh (g i))
        (fun i ↦ (norm_restrictedAnalyticSubst_le h hh (g i)).trans (hg i)) f :=
  DFunLike.congr_fun (restrictedAnalyticSubst_comp g hg h hh) f

/-- **Evaluation of a substitution**: for `b` in a complete ultrametric ring with `‖bⱼ‖ ≤ s'ⱼ`,
evaluating `f(g)` at `b` is evaluating `f` at the values `gᵢ(b)`. -/
theorem restrictedEval₂_restrictedAnalyticSubst {m : ℕ} {s' : Fin m → ℝ} [∀ j, Fact (0 < s' j)]
    {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (b : Fin m → S) (hb : ∀ j, ‖b j‖ ≤ s' j)
    (g : Fin k → IsRestricted.subring (R := R) s') (hg : ∀ i, ‖g i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedEval₂ φ b hφ hb (restrictedAnalyticSubst g hg f) =
      restrictedEval₂ φ (fun i ↦ restrictedEval₂ φ b hφ hb (g i)) hφ
        (fun i ↦ (norm_restrictedEval₂_le φ b hφ hb (g i)).trans (hg i)) f := by
  have h := eq_restrictedEval₂ φ (fun i ↦ restrictedEval₂ φ b hφ hb (g i)) hφ
    (fun i ↦ (norm_restrictedEval₂_le φ b hφ hb (g i)).trans (hg i))
    ((restrictedEval₂ φ b hφ hb).comp (restrictedAnalyticSubst g hg).toRingHom)
    ((continuous_restrictedEval₂ φ b hφ hb).comp (continuous_restrictedAnalyticSubst g hg))
    (fun a ↦ by simp) fun i ↦ by simp
  exact DFunLike.congr_fun h f

end AnalyticSubst

section Translate

variable [NormOneClass R] [∀ i, Fact (0 < r i)]

omit [CompleteSpace R] in
/-- The translated variable `Xᵢ + aᵢ` has Gauss norm at most `rᵢ` when `‖aᵢ‖ ≤ rᵢ`. -/
theorem norm_X_add_algebraMap_le {i : Fin k} {a : R} (ha : ‖a‖ ≤ r i) :
    ‖(⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ + algebraMap R _ a :
      IsRestricted.subring (R := R) r)‖ ≤ r i :=
  (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (norm_X i).le (by rwa [norm_algebraMap_isRestrictedSubring]))

/-- **Translation** `Xᵢ ↦ Xᵢ + aᵢ` of the polydisc of radii `r`, for constants with
`‖aᵢ‖ ≤ rᵢ`. -/
noncomputable def restrictedTranslate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) r :=
  restrictedAnalyticSubst (s := r)
    (fun i ↦ (⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ :
      IsRestricted.subring (R := R) r) + algebraMap R _ (a i))
    fun i ↦ norm_X_add_algebraMap_le (ha i)

/-- Translation by `a` is the analytic substitution `Xᵢ ↦ Xᵢ + aᵢ`, so the substitution API
(coefficient formula, evaluation, coefficient maps) applies to it. -/
theorem restrictedTranslate_def (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    restrictedTranslate a ha = restrictedAnalyticSubst (s := r)
      (fun i ↦ (⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ :
        IsRestricted.subring (R := R) r) + algebraMap R _ (a i))
      (fun i ↦ norm_X_add_algebraMap_le (ha i)) := (rfl)

/-- Translation sends `Xᵢ` to `Xᵢ + aᵢ`. -/
@[simp]
theorem restrictedTranslate_X (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) (i : Fin k) :
    restrictedTranslate a ha ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ =
      ⟨X i, isRestricted_monomial r (Finsupp.single i 1) 1⟩ + algebraMap R _ (a i) :=
  restrictedAnalyticSubst_X _ _ i

/-- Translation is continuous for the Gauss norm. -/
theorem continuous_restrictedTranslate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    Continuous (restrictedTranslate a ha) :=
  continuous_restrictedAnalyticSubst _ _

/-- Translation by `0` is the identity. -/
@[simp]
theorem restrictedTranslate_zero :
    restrictedTranslate (r := r) 0 (fun i ↦ by simpa using (Fact.out : 0 < r i).le) =
      AlgHom.id R _ :=
  (eq_restrictedAnalyticSubst _ _ (AlgHom.id R _) continuous_id fun _ ↦ by simp).symm

/-- **Translations compose additively**: translating by `a` and then by `b` is translating by
`a + b`. -/
theorem restrictedTranslate_comp (a b : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i)
    (hb : ∀ i, ‖b i‖ ≤ r i) :
    (restrictedTranslate b hb).comp (restrictedTranslate a ha) =
      restrictedTranslate (a + b)
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))) :=
  eq_restrictedAnalyticSubst _ _ _
    ((continuous_restrictedTranslate b hb).comp (continuous_restrictedTranslate a ha))
    fun i ↦ by
      simp only [AlgHom.comp_apply, restrictedTranslate_X, map_add, AlgHom.commutes, Pi.add_apply]
      abel

/-- **Translation is an automorphism**: translation by `a`, with inverse the translation
by `-a`. -/
noncomputable def restrictedTranslateEquiv (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) r :=
  AlgEquiv.ofAlgHom (restrictedTranslate a ha)
    (restrictedTranslate (-a) fun i ↦ by simpa using ha i)
    (by rw [restrictedTranslate_comp]; simp)
    (by rw [restrictedTranslate_comp]; simp)

/-- The automorphism `restrictedTranslateEquiv a` is the translation by `a`. -/
@[simp]
theorem coe_restrictedTranslateEquiv (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    ⇑(restrictedTranslateEquiv a ha) = restrictedTranslate a ha := (rfl)

/-- The inverse of translation by `a` is translation by `-a`. -/
@[simp]
theorem restrictedTranslateEquiv_symm (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i) :
    ⇑(restrictedTranslateEquiv a ha).symm =
      restrictedTranslate (-a) fun i ↦ by simpa using ha i := (rfl)

/-- **Translation is an isometry** for the Gauss norm at the radii `r`. -/
@[simp]
theorem norm_restrictedTranslate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedTranslate a ha f‖ = ‖f‖ := by
  refine le_antisymm (norm_restrictedAnalyticSubst_le _ _ f) ?_
  calc ‖f‖ = ‖(restrictedTranslateEquiv a ha).symm (restrictedTranslateEquiv a ha f)‖ := by
        rw [AlgEquiv.symm_apply_apply]
    _ ≤ ‖restrictedTranslate a ha f‖ := by
        rw [restrictedTranslateEquiv_symm, coe_restrictedTranslateEquiv]
        exact norm_restrictedAnalyticSubst_le _ _ _

end Translate

end TauCeti.MvPowerSeries
