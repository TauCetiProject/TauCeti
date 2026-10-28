/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst

/-!
# Analytic substitution of overconvergent power series

Let `R` be a complete ultrametric normed commutative ring. Let `f ∈ R⟨X₁, …, X_k⟩†` be
overconvergent, and let `g₁, …, g_k ∈ R⟨Y⟩†` be overconvergent series of unit Gauss norm
`‖gᵢ‖₁ ≤ 1`. The analytic substitution `f(g) = ∑ₜ fₜ g₁^t₁ ⋯ g_k^t_k` of the unit-radius Tate
algebras (`TauCeti.MvPowerSeries.restrictedAnalyticSubst`) is then again overconvergent. This
makes analytic substitution an `R`-algebra homomorphism `R⟨X⟩† → R⟨Y⟩†`, the restriction of the
substitution between the Tate algebras.

The point is the choice of radii. If `f` is restricted at a radius `ρ_f > 1`, the substitution
converges at a radius `ρ > 1` on which `‖gᵢ‖_ρ ≤ ρ_f` for every `i`. Such a `ρ` exists because the
coefficients of the `gᵢ` have norm at most `1 < ρ_f`, and strict coefficient bounds on an
overconvergent series persist to all radii close enough to `1`
(`TauCeti.Dagger.eventually_isRestricted_forall_norm_coeff_mul_pow_lt`). Since `ρ_f` may be
arbitrarily close to `1`, the inner series are bounded at the unit radius itself.

Unlike the formal substitution `TauCeti.Dagger.washnitzerAlgebra.subst`, the `gᵢ` may be
arbitrary overconvergent series and may have nonzero constant terms. For instance, translation
`Xᵢ ↦ Xᵢ + aᵢ` by constants with `‖aᵢ‖ ≤ 1` is an automorphism of `R⟨X⟩†`. Where formal
substitution is defined the two substitutions agree.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.analyticSubst`: the substitution `f ↦ f(g)` as an `R`-algebra
  homomorphism `R⟨X⟩† →ₐ[R] R⟨Y⟩†`.
* `TauCeti.Dagger.washnitzerAlgebra.translate` and
  `TauCeti.Dagger.washnitzerAlgebra.translateEquiv`: translation `Xᵢ ↦ Xᵢ + aᵢ`, as an
  `R`-algebra homomorphism and as an `R`-algebra automorphism of `R⟨X⟩†`.

## Main results

* `TauCeti.Dagger.coe_restrictedAnalyticSubst_mem_washnitzerAlgebra`: analytic substitution of
  overconvergent series of unit Gauss norm at most `1` preserves overconvergence.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_analyticSubst`: compatibility with analytic
  substitution of the Tate algebras.
* `TauCeti.Dagger.washnitzerAlgebra.coeff_analyticSubst`: the coefficient formula.
* `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_X` and
  `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_ofMvPolynomial`: the values on variables and on
  polynomials.
* `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_self` and
  `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_comp`: the identity and composition laws.
* `TauCeti.Dagger.washnitzerAlgebra.coe_analyticSubst_eq_subst`: agreement with Mathlib's formal
  substitution whenever the latter is defined.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_translate` and
  `TauCeti.Dagger.washnitzerAlgebra.norm_toTate_translate`: translation is the restriction of
  translation of the Tate algebra, and preserves the unit Gauss norm.
* `TauCeti.Dagger.washnitzerAlgebra.translate_zero` and
  `TauCeti.Dagger.washnitzerAlgebra.translate_comp`: translations compose additively.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
-/

public section

namespace TauCeti.Dagger

open Filter Topology _root_.MvPowerSeries
open TauCeti.MvPowerSeries (restrictedAnalyticSubst coeff_restrictedAnalyticSubst)

variable {k m : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **Analytic substitution preserves overconvergence.** Substituting overconvergent series
`gᵢ` of unit Gauss norm at most `1` into an overconvergent series `f`, by the analytic
substitution of the unit-radius Tate algebras, gives an overconvergent series. -/
theorem coe_restrictedAnalyticSubst_mem_washnitzerAlgebra (g : Fin k → washnitzerAlgebra τ R)
    (hg : ∀ i, ‖washnitzerAlgebra.toTate τ R (g i)‖ ≤ 1) (f : washnitzerAlgebra (Fin k) R) :
    (restrictedAnalyticSubst (fun i ↦ washnitzerAlgebra.toTate τ R (g i)) hg
      (washnitzerAlgebra.toTate (Fin k) R f) : MvPowerSeries τ R) ∈ washnitzerAlgebra τ R := by
  obtain ⟨ρf, hρf, hf⟩ := mem_washnitzerAlgebra.mp f.2
  -- The coefficients of every `gᵢ` have norm at most `1 < ρf`, so at a common radius `ρ > 1`
  -- every `gᵢ` is restricted with all weighted coefficient norms below `ρf`.
  have hcoeff (i : Fin k) (t : τ →₀ ℕ) : ‖coeff t (g i : MvPowerSeries τ R)‖ < ρf := by
    simpa using ((norm_coeff_le_norm (washnitzerAlgebra.toTate τ R (g i)) t).trans
      (hg i)).trans_lt hρf
  obtain ⟨ρ, hρg, hρ⟩ := ((eventually_all.2 fun i ↦
    eventually_isRestricted_forall_norm_coeff_mul_pow_lt (g i).2 (hcoeff i)).and
      self_mem_nhdsWithin).exists
  have : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
  have : Fact (0 < ρf) := ⟨zero_lt_one.trans hρf⟩
  let g' (i : Fin k) : IsRestricted.subring (R := R) (fun _ : τ ↦ ρ) := ⟨g i, (hρg i).1⟩
  have hg' (i : Fin k) : ‖g' i‖ ≤ ρf :=
    (norm_le_iff (zero_lt_one.trans hρf).le).2 fun t ↦ by
      simpa [g', Finsupp.prod_pow_eq_pow_degree] using ((hρg i).2 t).le
  -- The substitution at the radii `ρf` and `ρ` has the same coefficients as at unit radii.
  have h : (restrictedAnalyticSubst (fun i ↦ washnitzerAlgebra.toTate τ R (g i)) hg
      (washnitzerAlgebra.toTate (Fin k) R f) : MvPowerSeries τ R) =
      restrictedAnalyticSubst (r := fun _ ↦ ρf) g' hg' ⟨f, hf⟩ := by
    ext e
    simp [coeff_restrictedAnalyticSubst, g']
  exact mem_washnitzerAlgebra.mpr ⟨ρ, hρ, h ▸ IsRestricted.mem_subring.mp (Subtype.prop _)⟩

namespace washnitzerAlgebra

section AnalyticSubst

variable (g : Fin k → washnitzerAlgebra τ R) (hg : ∀ i, ‖toTate τ R (g i)‖ ≤ 1)

/-- **Analytic substitution of overconvergent series.** For overconvergent series `gᵢ` of unit
Gauss norm at most `1`, the `R`-algebra homomorphism `R⟨X⟩† → R⟨Y⟩†` sending `f = ∑ₜ fₜ Xᵗ` to the
convergent sum `∑ₜ fₜ gᵗ`. The `gᵢ` may have nonzero constant terms. -/
noncomputable def analyticSubst : washnitzerAlgebra (Fin k) R →ₐ[R] washnitzerAlgebra τ R where
  __ := ((IsRestricted.subring (R := R) (fun _ : τ ↦ (1 : ℝ))).subtype.comp
      ((restrictedAnalyticSubst (fun i ↦ toTate τ R (g i)) hg).toRingHom.comp
        (toTate (Fin k) R).toRingHom)).codRestrict (washnitzerAlgebra τ R).toSubring
      (coe_restrictedAnalyticSubst_mem_washnitzerAlgebra g hg)
  commutes' a := Subtype.ext <| by
    simp [c_eq_algebraMap]

/-- Analytic substitution of overconvergent series is the restriction of analytic substitution
of the unit-radius Tate algebras. -/
@[simp]
theorem toTate_analyticSubst (f : washnitzerAlgebra (Fin k) R) :
    toTate τ R (analyticSubst g hg f) =
      restrictedAnalyticSubst (fun i ↦ toTate τ R (g i)) hg (toTate (Fin k) R f) :=
  Subtype.ext (by simp [analyticSubst])

/-- **The coefficient formula for analytic substitution**: the coefficient of `Yᵉ` in `f(g)` is
the convergent sum `∑' t, fₜ · coeff e (g₁^t₁ ⋯ g_k^t_k)`. -/
theorem coeff_analyticSubst (f : washnitzerAlgebra (Fin k) R) (e : τ →₀ ℕ) :
    coeff e (analyticSubst g hg f : MvPowerSeries τ R) =
      ∑' t : Fin k →₀ ℕ, coeff t (f : MvPowerSeries (Fin k) R) *
        coeff e (∏ i, (g i : MvPowerSeries τ R) ^ t i) := by
  rw [← coe_toTate, toTate_analyticSubst, coeff_restrictedAnalyticSubst]
  simp

/-- Analytic substitution sends the variable `Xᵢ` to `gᵢ`. -/
@[simp]
theorem analyticSubst_X (i : Fin k) : analyticSubst g hg (X (Fin k) R i) = g i :=
  toTate_injective <| by
    rw [toTate_analyticSubst, toTate_X, TauCeti.MvPowerSeries.restrictedAnalyticSubst_X]

/-- Analytic substitution sends a polynomial `p` to its value `p(g)`. -/
@[simp]
theorem analyticSubst_ofMvPolynomial (p : MvPolynomial (Fin k) R) :
    analyticSubst g hg (ofMvPolynomial (Fin k) R p) = MvPolynomial.aeval g p := by
  have h : (analyticSubst g hg).comp (ofMvPolynomial (Fin k) R) = MvPolynomial.aeval g :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h p

/-- **Analytic substitution does not increase the unit Gauss norm**: `‖f(g)‖₁ ≤ ‖f‖₁`. -/
theorem norm_toTate_analyticSubst_le (f : washnitzerAlgebra (Fin k) R) :
    ‖toTate τ R (analyticSubst g hg f)‖ ≤ ‖toTate (Fin k) R f‖ := by
  rw [toTate_analyticSubst]
  exact TauCeti.MvPowerSeries.norm_restrictedAnalyticSubst_le _ _ _

/-- **Comparison with formal substitution.** When Mathlib's formal substitution of the `gᵢ` is
defined, for instance when their constant coefficients are nilpotent, it agrees with analytic
substitution. -/
theorem coe_analyticSubst_eq_subst (hsub : HasSubst fun i ↦ (g i : MvPowerSeries τ R))
    (f : washnitzerAlgebra (Fin k) R) :
    (analyticSubst g hg f : MvPowerSeries τ R) =
      subst (fun i ↦ (g i : MvPowerSeries τ R)) (f : MvPowerSeries (Fin k) R) := by
  rw [← coe_toTate, toTate_analyticSubst,
    TauCeti.MvPowerSeries.coe_restrictedAnalyticSubst_eq_subst _ _ (by simpa using hsub)]
  simp

/-- **Substituting the variables themselves is the identity.** -/
theorem analyticSubst_self [NormOneClass R] :
    analyticSubst (X (Fin k) R) (fun i ↦ by
      rw [toTate_X, norm_X]) = AlgHom.id R _ :=
  AlgHom.ext fun f ↦ toTate_injective <| by
    rw [toTate_analyticSubst, AlgHom.id_apply]
    exact DFunLike.congr_fun ((TauCeti.MvPowerSeries.eq_restrictedAnalyticSubst _ _
      (AlgHom.id R _) continuous_id fun i ↦ (toTate_X i).symm).symm) _

/-- Analytic substitution of `h` into `g(h)` keeps the unit Gauss norm at most `1`. -/
theorem norm_toTate_analyticSubst_le_one (h : Fin m → washnitzerAlgebra τ R)
    (hh : ∀ j, ‖toTate τ R (h j)‖ ≤ 1) (g : Fin k → washnitzerAlgebra (Fin m) R)
    (hg : ∀ i, ‖toTate (Fin m) R (g i)‖ ≤ 1) (i : Fin k) :
    ‖toTate τ R (analyticSubst h hh (g i))‖ ≤ 1 :=
  (norm_toTate_analyticSubst_le h hh (g i)).trans (hg i)

/-- **Composition of analytic substitutions**: substituting `h` into `f(g)` is substituting the
series `g(h)` into `f`. -/
theorem analyticSubst_comp (g : Fin k → washnitzerAlgebra (Fin m) R)
    (hg : ∀ i, ‖toTate (Fin m) R (g i)‖ ≤ 1) (h : Fin m → washnitzerAlgebra τ R)
    (hh : ∀ j, ‖toTate τ R (h j)‖ ≤ 1) :
    (analyticSubst h hh).comp (analyticSubst g hg) =
      analyticSubst (fun i ↦ analyticSubst h hh (g i))
        (norm_toTate_analyticSubst_le_one h hh g hg) :=
  AlgHom.ext fun f ↦ toTate_injective <| by
    simp only [AlgHom.comp_apply, toTate_analyticSubst,
      TauCeti.MvPowerSeries.restrictedAnalyticSubst_restrictedAnalyticSubst]

end AnalyticSubst

section Translate

variable [NormOneClass R]

omit [CompleteSpace R] [NormOneClass R] in
/-- The inclusion into the Tate algebra sends `Xᵢ + a` to the translated variable `Xᵢ + a`. -/
private theorem toTate_X_add_algebraMap (a : R) (i : Fin k) :
    toTate (Fin k) R (X (Fin k) R i + algebraMap R _ a) =
      ⟨_root_.MvPowerSeries.X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ +
        algebraMap R _ a := by
  rw [map_add, AlgHom.commutes, toTate_X]

omit [CompleteSpace R] in
/-- The translated variable `Xᵢ + a` has unit Gauss norm at most `1` when `‖a‖ ≤ 1`. -/
theorem norm_toTate_X_add_algebraMap_le {a : R} (ha : ‖a‖ ≤ 1) (i : Fin k) :
    ‖toTate (Fin k) R (X (Fin k) R i + algebraMap R _ a)‖ ≤ 1 := by
  rw [toTate_X_add_algebraMap]
  exact TauCeti.MvPowerSeries.norm_X_add_algebraMap_le (r := fun _ ↦ 1) ha

/-- **Translation** `Xᵢ ↦ Xᵢ + aᵢ` of overconvergent series, for constants with `‖aᵢ‖ ≤ 1`. -/
noncomputable def translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    washnitzerAlgebra (Fin k) R →ₐ[R] washnitzerAlgebra (Fin k) R :=
  analyticSubst (fun i ↦ X (Fin k) R i + algebraMap R _ (a i))
    fun i ↦ norm_toTate_X_add_algebraMap_le (ha i) i

/-- Translation by `a` is the analytic substitution `Xᵢ ↦ Xᵢ + aᵢ`, so the substitution API
applies to it. -/
theorem translate_def (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    translate a ha = analyticSubst (fun i ↦ X (Fin k) R i + algebraMap R _ (a i))
      (fun i ↦ norm_toTate_X_add_algebraMap_le (ha i) i) := (rfl)

/-- Translation sends `Xᵢ` to `Xᵢ + aᵢ`. -/
@[simp]
theorem translate_X (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) (i : Fin k) :
    translate a ha (X (Fin k) R i) = X (Fin k) R i + algebraMap R _ (a i) :=
  analyticSubst_X _ _ i

/-- Translation of overconvergent series is the restriction of translation of the unit-radius
Tate algebra. -/
@[simp]
theorem toTate_translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : washnitzerAlgebra (Fin k) R) :
    toTate (Fin k) R (translate a ha f) =
      TauCeti.MvPowerSeries.restrictedTranslate a ha (toTate (Fin k) R f) := by
  simp only [translate_def, toTate_analyticSubst, toTate_X_add_algebraMap,
    TauCeti.MvPowerSeries.restrictedTranslate_def]

/-- Translation by `0` is the identity. -/
@[simp]
theorem translate_zero : translate (k := k) (R := R) 0 (fun _ ↦ by simp) = AlgHom.id R _ :=
  AlgHom.ext fun f ↦ toTate_injective <| by simp

/-- **Translations compose additively**: translating by `a` and then by `b` is translating by
`a + b`. -/
theorem translate_comp (a b : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) :
    (translate b hb).comp (translate a ha) =
      translate (a + b)
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))) :=
  AlgHom.ext fun f ↦ toTate_injective <| by
    simpa using DFunLike.congr_fun
      (TauCeti.MvPowerSeries.restrictedTranslate_comp a b ha hb) (toTate (Fin k) R f)

/-- **Translation is an automorphism** of the Monsky–Washnitzer algebra: translation by `a`,
with inverse the translation by `-a`. -/
noncomputable def translateEquiv (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    washnitzerAlgebra (Fin k) R ≃ₐ[R] washnitzerAlgebra (Fin k) R :=
  AlgEquiv.ofAlgHom (translate a ha) (translate (-a) fun i ↦ by simpa using ha i)
    (AlgHom.ext fun f ↦ toTate_injective <| by
      simpa using (TauCeti.MvPowerSeries.restrictedTranslateEquiv a ha).apply_symm_apply
        (toTate (Fin k) R f))
    (AlgHom.ext fun f ↦ toTate_injective <| by
      simpa using (TauCeti.MvPowerSeries.restrictedTranslateEquiv a ha).symm_apply_apply
        (toTate (Fin k) R f))

/-- The automorphism `translateEquiv a` is the translation by `a`. -/
@[simp]
theorem coe_translateEquiv (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ⇑(translateEquiv a ha) = translate a ha := (rfl)

/-- The inverse of translation by `a` is translation by `-a`. -/
@[simp]
theorem translateEquiv_symm (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ⇑(translateEquiv a ha).symm = translate (-a) fun i ↦ by simpa using ha i := (rfl)

/-- **Translation preserves the unit Gauss norm** of overconvergent series. -/
theorem norm_toTate_translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : washnitzerAlgebra (Fin k) R) :
    ‖toTate (Fin k) R (translate a ha f)‖ = ‖toTate (Fin k) R f‖ := by
  rw [toTate_translate, TauCeti.MvPowerSeries.norm_restrictedTranslate]

end Translate

end washnitzerAlgebra

end TauCeti.Dagger
