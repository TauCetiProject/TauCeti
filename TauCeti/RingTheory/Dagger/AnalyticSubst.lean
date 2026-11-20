/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Eval
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
* `TauCeti.Dagger.washnitzerAlgebra.toTate_analyticSubst`,
  `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_ofRestricted`, and
  `TauCeti.Dagger.washnitzerAlgebra.exists_ofRestricted_restrictedAnalyticSubst`: compatibility
  with Tate-algebra and polyradius substitutions and explicit common-radius factorization.
* `TauCeti.Dagger.washnitzerAlgebra.coeff_analyticSubst`: the coefficient formula.
* `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_X` and
  `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_ofMvPolynomial`: the values on variables and on
  polynomials.
* `TauCeti.Dagger.washnitzerAlgebra.norm_analyticSubst_le`,
  `TauCeti.Dagger.washnitzerAlgebra.continuous_analyticSubst`, and
  `TauCeti.Dagger.washnitzerAlgebra.eq_analyticSubst`: contractivity, continuity, and uniqueness
  among continuous algebra homomorphisms.
* `TauCeti.Dagger.washnitzerAlgebra.map_analyticSubst` and
  `TauCeti.Dagger.washnitzerAlgebra.eval₂_analyticSubst`: compatibility with bounded coefficient
  maps and evaluation on the closed unit polydisc.
* `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_self` and
  `TauCeti.Dagger.washnitzerAlgebra.analyticSubst_comp`: the identity and composition laws.
* `TauCeti.Dagger.washnitzerAlgebra.coe_analyticSubst_eq_subst`: agreement with Mathlib's formal
  substitution whenever the latter is defined.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_translate`,
  `TauCeti.Dagger.washnitzerAlgebra.translate_ofRestricted`, and
  `TauCeti.Dagger.washnitzerAlgebra.norm_translate`: translation restricts Tate-algebra and
  polyradius translations and preserves the unit Gauss norm.
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

/-- Common-radius witness for analytic substitution: given `f ∈ R⟨X₁, …, X_k⟩†` and
`g₁, …, g_k ∈ R⟨Y⟩†` with `‖gᵢ‖₁ ≤ 1`, there exist radii `ρf > 1` and `ρ > 1` such that `f` is
restricted at `ρf`, every `gᵢ` is restricted at `ρ` with `ρ`-Gauss norm at most `ρf`, and the
unit-radius Tate-algebra substitution agrees in `MvPowerSeries τ R` with the analytic substitution
at `(ρf, ρ)`. -/
private theorem exists_coe_restrictedAnalyticSubst_eq (g : Fin k → washnitzerAlgebra τ R)
    (hg : ∀ i, ‖washnitzerAlgebra.toTate τ R (g i)‖ ≤ 1) (f : washnitzerAlgebra (Fin k) R) :
    ∃ (ρf ρ : ℝ) (hρf : 1 < ρf) (hρ : 1 < ρ)
      (hf : IsRestricted (fun _ : Fin k ↦ ρf) (f : MvPowerSeries (Fin k) R))
      (hgρ : ∀ i, IsRestricted (fun _ : τ ↦ ρ) (g i : MvPowerSeries τ R)),
      letI : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
      ∃ hg' : ∀ i,
          ‖(⟨(g i : MvPowerSeries τ R), hgρ i⟩ : IsRestricted.subring (R := R) (fun _ ↦ ρ))‖ ≤ ρf,
        (restrictedAnalyticSubst (fun i ↦ washnitzerAlgebra.toTate τ R (g i)) hg
          (washnitzerAlgebra.toTate (Fin k) R f) : MvPowerSeries τ R) =
          restrictedAnalyticSubst (r := fun _ ↦ ρf)
            (fun i ↦ ⟨(g i : MvPowerSeries τ R), hgρ i⟩) hg'
            ⟨(f : MvPowerSeries (Fin k) R), hf⟩ := by
  obtain ⟨ρf, hρf, hf⟩ := mem_washnitzerAlgebra.mp f.property
  -- The coefficients of every `gᵢ` have norm at most `1 < ρf`, so at a common radius `ρ > 1`
  -- every `gᵢ` is restricted with all weighted coefficient norms below `ρf`.
  have hcoeff (i : Fin k) (t : τ →₀ ℕ) : ‖coeff t (g i : MvPowerSeries τ R)‖ < ρf := by
    simpa using ((norm_coeff_le_norm (washnitzerAlgebra.toTate τ R (g i)) t).trans
      (hg i)).trans_lt hρf
  obtain ⟨ρ, hρg, hρ⟩ := ((eventually_all.2 fun i ↦
    eventually_isRestricted_forall_norm_coeff_mul_pow_lt (g i).property (hcoeff i)).and
      self_mem_nhdsWithin).exists
  have : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
  have hg' (i : Fin k) :
      ‖(⟨(g i : MvPowerSeries τ R), (hρg i).1⟩ :
          IsRestricted.subring (R := R) (fun _ ↦ ρ))‖ ≤ ρf :=
    norm_le_iff.2 fun t ↦ by
      simpa [Finsupp.prod_pow_eq_pow_degree] using ((hρg i).2 t).le
  refine ⟨ρf, ρ, hρf, hρ, hf, fun i ↦ (hρg i).1, hg', ?_⟩
  ext e
  simp [coeff_restrictedAnalyticSubst]

/-- **Analytic substitution preserves overconvergence.** Substituting overconvergent series
`gᵢ` of unit Gauss norm at most `1` into an overconvergent series `f`, by the analytic
substitution of the unit-radius Tate algebras, gives an overconvergent series. -/
theorem coe_restrictedAnalyticSubst_mem_washnitzerAlgebra (g : Fin k → washnitzerAlgebra τ R)
    (hg : ∀ i, ‖washnitzerAlgebra.toTate τ R (g i)‖ ≤ 1) (f : washnitzerAlgebra (Fin k) R) :
    (restrictedAnalyticSubst (fun i ↦ washnitzerAlgebra.toTate τ R (g i)) hg
      (washnitzerAlgebra.toTate (Fin k) R f) : MvPowerSeries τ R) ∈ washnitzerAlgebra τ R := by
  obtain ⟨_, ρ, _, hρ, _, _, _, h⟩ := exists_coe_restrictedAnalyticSubst_eq g hg f
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
theorem norm_analyticSubst_le (f : washnitzerAlgebra (Fin k) R) :
    ‖analyticSubst g hg f‖ ≤ ‖f‖ := by
  rw [← norm_toTate, ← norm_toTate, toTate_analyticSubst]
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
    analyticSubst (X (Fin k) R) (fun _ ↦ by simp) = AlgHom.id R _ :=
  AlgHom.ext fun f ↦ toTate_injective <| by
    rw [toTate_analyticSubst, AlgHom.id_apply]
    simp only [toTate_X]
    exact DFunLike.congr_fun TauCeti.MvPowerSeries.restrictedAnalyticSubst_self _

/-- **Composition of analytic substitutions**: substituting `h` into `f(g)` is substituting the
series `g(h)` into `f`. -/
theorem analyticSubst_comp (g : Fin k → washnitzerAlgebra (Fin m) R)
    (hg : ∀ i, ‖toTate (Fin m) R (g i)‖ ≤ 1) (h : Fin m → washnitzerAlgebra τ R)
    (hh : ∀ j, ‖toTate τ R (h j)‖ ≤ 1) :
    (analyticSubst h hh).comp (analyticSubst g hg) =
      analyticSubst (fun i ↦ analyticSubst h hh (g i))
        (fun i ↦ (norm_analyticSubst_le h hh (g i)).trans (hg i)) :=
  AlgHom.ext fun f ↦ toTate_injective <| by
    simp only [AlgHom.comp_apply, toTate_analyticSubst,
      TauCeti.MvPowerSeries.restrictedAnalyticSubst_restrictedAnalyticSubst]

/-- Analytic substitution is continuous for the unit Gauss norm topology on `W`. -/
@[continuity]
theorem continuous_analyticSubst : Continuous (analyticSubst g hg) :=
  AddMonoidHomClass.continuous_of_bound (analyticSubst g hg) 1 fun f ↦ by
    simpa using norm_analyticSubst_le g hg f

/-- **Uniqueness of analytic substitution on `W`.** A continuous `R`-algebra homomorphism
`R⟨X⟩† →ₐ[R] R⟨Y⟩†` sending each `Xᵢ` to `gᵢ` equals `analyticSubst g hg`. -/
theorem eq_analyticSubst (ψ : washnitzerAlgebra (Fin k) R →ₐ[R] washnitzerAlgebra τ R)
    (hψ : Continuous ψ) (hX : ∀ i, ψ (X (Fin k) R i) = g i) :
    ψ = analyticSubst g hg := by
  have hp : ψ.comp (ofMvPolynomial (Fin k) R) =
      (analyticSubst g hg).comp (ofMvPolynomial (Fin k) R) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [hX]
  exact DFunLike.coe_injective (denseRange_ofMvPolynomial.equalizer hψ
    (continuous_analyticSubst g hg) (funext (DFunLike.congr_fun hp)))

/-- Analytic substitution on `W` agrees via `ofRestricted` with `restrictedAnalyticSubst` between
any polyradii `r : Fin k → ℝ` and `s : τ → ℝ` bounded below by `ρr, ρs > 1` on which
`‖g₀ i‖_s ≤ r i` and `‖g₀ i‖₁ ≤ 1`. -/
theorem analyticSubst_ofRestricted {r : Fin k → ℝ} {s : τ → ℝ} [∀ j, Fact (0 < s j)]
    {ρr ρs : ℝ} (hρr : 1 < ρr) (hr : ∀ i, ρr ≤ r i) (hρs : 1 < ρs) (hs : ∀ j, ρs ≤ s j)
    (g₀ : Fin k → IsRestricted.subring (R := R) s) (hg₀ : ∀ i, ‖g₀ i‖ ≤ r i)
    (hg₁ : ∀ i, ‖toTate τ R (ofRestricted hρs hs (g₀ i))‖ ≤ 1)
    (f : IsRestricted.subring (R := R) r) :
    analyticSubst (fun i ↦ ofRestricted hρs hs (g₀ i)) hg₁ (ofRestricted hρr hr f) =
      ofRestricted hρs hs (restrictedAnalyticSubst g₀ hg₀ f) := by
  refine Subtype.ext <| MvPowerSeries.ext fun e ↦ ?_
  rw [coe_ofRestricted, coeff_analyticSubst, coeff_restrictedAnalyticSubst]
  simp

/-- **Common-radius factorization of analytic substitution.** Given `f ∈ R⟨X₁, …, X_k⟩†` and
`g₁, …, g_k ∈ R⟨Y⟩†` with `‖gᵢ‖₁ ≤ 1`, there exist radii `ρf > 1` and `ρ > 1` such that `f` is
restricted at `ρf`, every `gᵢ` is restricted at `ρ` with `ρ`-Gauss norm at most `ρf`, and
`analyticSubst g hg f` comes via `ofRestricted` from `restrictedAnalyticSubst` at those radii. -/
theorem exists_ofRestricted_restrictedAnalyticSubst (f : washnitzerAlgebra (Fin k) R) :
    ∃ (ρf ρ : ℝ) (hρf : 1 < ρf) (hρ : 1 < ρ)
      (hf : IsRestricted (fun _ : Fin k ↦ ρf) (f : MvPowerSeries (Fin k) R))
      (hgρ : ∀ i, IsRestricted (fun _ : τ ↦ ρ) (g i : MvPowerSeries τ R)),
      letI : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
      ∃ hg' : ∀ i,
          ‖(⟨(g i : MvPowerSeries τ R), hgρ i⟩ : IsRestricted.subring (R := R) (fun _ ↦ ρ))‖ ≤ ρf,
        analyticSubst g hg f =
          ofRestricted hρ (fun _ ↦ le_rfl)
            (restrictedAnalyticSubst (fun i ↦ ⟨(g i : MvPowerSeries τ R), hgρ i⟩) hg'
              ⟨(f : MvPowerSeries (Fin k) R), hf⟩) := by
  obtain ⟨ρf, ρ, hρf, hρ, hf, hgρ, hg', h⟩ := exists_coe_restrictedAnalyticSubst_eq g hg f
  refine ⟨ρf, ρ, hρf, hρ, hf, hgρ, hg', Subtype.ext ?_⟩
  rw [coe_ofRestricted, ← coe_toTate, toTate_analyticSubst]
  exact h

/-- **Bounded coefficient maps commute with analytic substitution on `W`.** -/
theorem map_analyticSubst {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (hφg : ∀ i, ‖toTate τ S (map φ hφ (g i))‖ ≤ 1) (f : washnitzerAlgebra (Fin k) R) :
    map φ hφ (analyticSubst g hg f) =
      analyticSubst (fun i ↦ map φ hφ (g i)) hφg (map φ hφ f) := by
  apply toTate_injective
  simpa only [toTate_map, toTate_analyticSubst] using
    TauCeti.MvPowerSeries.restrictedMap_restrictedAnalyticSubst
      (fun i ↦ toTate τ R (g i)) hg φ hφ (by simpa only [toTate_map] using hφg)
      (toTate (Fin k) R f)

/-- **Evaluation of an analytic substitution**: evaluating `f(g)` at `b` in the closed unit
polydisc of `S` agrees with evaluating `f` at the values `gᵢ(b)`. -/
theorem eval₂_analyticSubst {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (b : Fin m → S) (hb : ∀ j, ‖b j‖ ≤ 1)
    (g' : Fin k → washnitzerAlgebra (Fin m) R)
    (hg' : ∀ i, ‖toTate (Fin m) R (g' i)‖ ≤ 1) (f : washnitzerAlgebra (Fin k) R) :
    eval₂ φ b hφ hb (analyticSubst g' hg' f) =
      eval₂ φ (fun i ↦ eval₂ φ b hφ hb (g' i)) hφ
        (fun i ↦ (norm_eval₂_le φ b hφ hb (g' i)).trans (hg' i)) f := by
  simpa only [eval₂_eq_restrictedEval₂_toTate, toTate_analyticSubst] using
    TauCeti.MvPowerSeries.restrictedEval₂_restrictedAnalyticSubst φ hφ b hb
      (fun i ↦ toTate (Fin m) R (g' i)) hg' (toTate (Fin k) R f)

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

/-- Translation on `W` agrees via `ofRestricted` with `restrictedTranslate` on any polyradius
`r` bounded below by some `ρ > 1`. -/
@[simp]
theorem translate_ofRestricted {r : Fin k → ℝ} [∀ i, Fact (0 < r i)] {ρ : ℝ}
    (hρ : 1 < ρ) (hr : ∀ i, ρ ≤ r i) (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : IsRestricted.subring (R := R) r) :
    translate a ha (ofRestricted hρ hr f) =
      ofRestricted hρ hr
        (TauCeti.MvPowerSeries.restrictedTranslate a
          (fun i ↦ (ha i).trans (hρ.le.trans (hr i))) f) := by
  refine Subtype.ext <| MvPowerSeries.ext fun e ↦ ?_
  rw [coe_ofRestricted, translate_def, coeff_analyticSubst,
    TauCeti.MvPowerSeries.restrictedTranslate_def, coeff_restrictedAnalyticSubst]
  simp [_root_.MvPowerSeries.algebraMap_apply]

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
@[simp]
theorem norm_translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : washnitzerAlgebra (Fin k) R) :
    ‖translate a ha f‖ = ‖f‖ := by
  rw [← norm_toTate, ← norm_toTate, toTate_translate,
    TauCeti.MvPowerSeries.norm_restrictedTranslate]

/-- Translation is an isometry for the Gauss norm on `W`. -/
theorem isometry_translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    Isometry (translate a ha) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_translate a ha)

/-- Translation is continuous for the Gauss norm topology on `W`. -/
@[continuity]
theorem continuous_translate (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) :
    Continuous (translate a ha) :=
  (isometry_translate a ha).continuous

/-- Evaluating a translated series `f(X + a)` at `b` in the closed unit polydisc equals evaluating
`f` at `b + φ(a)`. -/
theorem eval₂_translate {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (b : Fin k → S) (hb : ∀ i, ‖b i‖ ≤ 1) (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1)
    (f : washnitzerAlgebra (Fin k) R) :
    eval₂ φ b hφ hb (translate a ha f) =
      eval₂ φ (fun i ↦ b i + φ (a i)) hφ
        (fun i ↦ (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (hb i) ((hφ (a i)).trans (ha i)))) f := by
  have hval : (fun i ↦ eval₂ φ b hφ hb (X (Fin k) R i + algebraMap R _ (a i))) =
      fun i ↦ b i + φ (a i) := funext fun i ↦ by simp
  have h := eval₂_analyticSubst φ hφ b hb
    (fun i ↦ X (Fin k) R i + algebraMap R _ (a i))
    (fun i ↦ norm_toTate_X_add_algebraMap_le (ha i) i) f
  rw [← translate_def a ha] at h
  rw [h, eval₂_apply, eval₂_apply, hval]

end Translate

end washnitzerAlgebra

end TauCeti.Dagger
