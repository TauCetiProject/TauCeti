/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.IntegralWashnitzer
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.RingTheory.Dagger.Noetherian

/-!
# The integral Monsky–Washnitzer algebra is noetherian

Let `K` be a complete ultrametric normed field with closed unit ball `K°`. The integral
Monsky–Washnitzer algebra `K°⟨X⟩†` in finitely many variables is noetherian exactly when `K°`
is. In particular `O_K⟨X⟩†` is noetherian for a complete discretely valued field `K` with ring of
integers `O_K`, a discrete valuation ring. This is the ring of which the weak completions of
finitely generated `O_K`-algebras in Monsky–Washnitzer cohomology are quotients.

A constant coefficient map retracts `K°⟨X⟩†` onto `K°`, so noetherianity descends to `K°`. The
converse is an induction on the number of variables via Weierstrass division, as for the
Monsky–Washnitzer algebra `K⟨X⟩†` itself (`TauCeti.Dagger.washnitzerAlgebra.isNoetherianRing`),
with two changes.

* Division must be integral. Write `R = K°⟨X⟩†` and `R' = K°⟨X, Y⟩†`. If `g ∈ R'` has Gauss norm
  one and is distinguished of degree `s` in `Y`, the Weierstrass division `f = q g + r` of
  `f ∈ R'` in `K⟨X, Y⟩†` satisfies `‖f‖ = max (‖q‖ ‖g‖) ‖r‖`, so `q ∈ R'` and `r ∈ R[Y]`. Hence
  `R' ⧸ (g)` is spanned over `R` by `1, Y, …, Y ^ (s - 1)`, and every ideal containing `g` is
  finitely generated when `R` is noetherian.
* A nonzero ideal `I` of `R'` need not contain an element of Gauss norm one. If `K°` is
  noetherian, its maximal ideal is finitely generated, so there is `π ∈ K°` with `‖a‖ ≤ ‖π‖`
  whenever `‖a‖ < 1`. Then `I = πᵏ I'` for some `k` and an ideal `I'` which is not contained in
  `π R'`, and every element of `I'` outside `π R'` has Gauss norm one. A triangular change of
  variables, which preserves Gauss norms, makes it distinguished in `Y`.

## Main results

* `TauCeti.Dagger.intWashnitzerAlgebra.isNoetherianRing`: `K°⟨X⟩†` is noetherian for finitely many
  variables when `K°` is noetherian, for instance when `K°` is a discrete valuation ring.
* `TauCeti.Dagger.intWashnitzerAlgebra.isNoetherianRing_unitClosedBall`: conversely, `K°` is
  noetherian when some `K°⟨X⟩†` is.
* `TauCeti.Dagger.intWashnitzerAlgebra.isNoetherianRing_iff`: `K°⟨X⟩†` is noetherian iff `K°` is.

## References

* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.2).
* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3 and §1.4 (1), for the induction over `K⟨X⟩†`.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, for the norm identity
  of Weierstrass division.
-/

public section

namespace TauCeti.Dagger.intWashnitzerAlgebra

open _root_.MvPowerSeries
open washnitzerAlgebra (optionSeries toTate optionC polynomialToOption)

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The constant coefficient retracts `K°⟨X⟩†` onto `K°`, so `K°` is noetherian as soon as
`K°⟨X⟩†` is, for any set of variables. -/
theorem isNoetherianRing_unitClosedBall (σ : Type*)
    [IsNoetherianRing (intWashnitzerAlgebra σ K)] :
    IsNoetherianRing (Subring.unitClosedBall K) := by
  let ε : intWashnitzerAlgebra σ K →+* Subring.unitClosedBall K :=
    ((constantCoeff : MvPowerSeries σ K →+* K).comp (intWashnitzerAlgebra σ K).subtype).codRestrict
      _ fun f ↦ Subring.mem_unitClosedBall.2 (norm_constantCoeff_le_one f)
  refine isNoetherianRing_of_surjective _ _ ε fun a ↦
    ⟨algebraMap (Subring.unitClosedBall K) (intWashnitzerAlgebra σ K) a, Subtype.ext ?_⟩
  simp [ε]

variable {σ τ : Type*}

/-- A Gauss-norm-preserving ring isomorphism of Monsky–Washnitzer algebras restricts to their
integral subrings. -/
private noncomputable def restrictRingEquiv (e : washnitzerAlgebra σ K ≃+* washnitzerAlgebra τ K)
    (he : ∀ f, ‖e f‖ = ‖f‖) : intWashnitzerAlgebra σ K ≃+* intWashnitzerAlgebra τ K where
  toFun f := ⟨e (toWashnitzerAlgebra σ K f),
    mem_intWashnitzerAlgebra_iff_norm_le_one.2
      ((he _).trans_le (norm_toWashnitzerAlgebra_le_one f))⟩
  invFun f := ⟨e.symm (toWashnitzerAlgebra τ K f),
    mem_intWashnitzerAlgebra_iff_norm_le_one.2 <| by
      rw [← he, e.apply_symm_apply]
      exact norm_toWashnitzerAlgebra_le_one f⟩
  left_inv f := Subtype.ext (by simp [toWashnitzerAlgebra_mk])
  right_inv f := Subtype.ext (by simp [toWashnitzerAlgebra_mk])
  map_mul' f g := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

/-- The restricted isomorphism acts as the given one on the underlying overconvergent series. -/
private theorem toWashnitzerAlgebra_restrictRingEquiv
    (e : washnitzerAlgebra σ K ≃+* washnitzerAlgebra τ K) (he : ∀ f, ‖e f‖ = ‖f‖)
    (f : intWashnitzerAlgebra σ K) :
    toWashnitzerAlgebra τ K (restrictRingEquiv e he f) = e (toWashnitzerAlgebra σ K f) :=
  toWashnitzerAlgebra_mk _ _

/-- With no variables, `K°⟨⟩† = K°` is noetherian when `K°` is. -/
private theorem isNoetherianRing_of_isEmpty [IsEmpty σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (intWashnitzerAlgebra σ K) := by
  refine isNoetherianRing_of_surjective _ _
    (algebraMap (Subring.unitClosedBall K) (intWashnitzerAlgebra σ K)) fun f ↦
      ⟨⟨constantCoeff (f : MvPowerSeries σ K),
        Subring.mem_unitClosedBall.2 (norm_constantCoeff_le_one f)⟩, Subtype.ext ?_⟩
  ext t
  rw [Subsingleton.elim t 0, coe_algebraMap, coeff_zero_C, coeff_zero_eq_constantCoeff_apply]

/-- Renaming the variables along an equivalence preserves noetherianity of `K°⟨X⟩†`. -/
private theorem isNoetherianRing_of_equiv (e : σ ≃ τ)
    [IsNoetherianRing (intWashnitzerAlgebra σ K)] :
    IsNoetherianRing (intWashnitzerAlgebra τ K) := by
  refine isNoetherianRing_of_ringEquiv _ (restrictRingEquiv
    (washnitzerAlgebra.renameAlgEquiv (R := K) e).toRingEquiv fun f ↦ ?_)
  rw [← washnitzerAlgebra.norm_toTate, ← washnitzerAlgebra.norm_toTate]
  have h : toTate τ K (washnitzerAlgebra.renameAlgEquiv e f) =
      IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ K f) :=
    Subtype.ext (by simp)
  rw [AlgEquiv.coe_toRingEquiv, h, IsRestricted.norm_renameAlgEquiv]

section Division

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- The Gauss norm of a series in `K⟨X, Y⟩†` is the Gauss norm at unit radius of its separated
series in `Y`, with coefficients in the Tate algebra in the variables `X`. -/
private theorem norm_eq_gaussNorm_map_optionSeries (f : W') :
    ‖f‖ = (PowerSeries.map (toTate σ K : W →+* Tate) (optionSeries f)).gaussNorm norm 1 := by
  rw [washnitzerAlgebra.map_toTate_optionSeries, ← TauCeti.PowerSeries.norm_eq_gaussNorm,
    norm_restrictedOptionEquiv, washnitzerAlgebra.norm_toTate]

/-- Adjoining the variable `Y` preserves Gauss norms. -/
private theorem norm_optionC (f : W) : ‖optionC f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm_map_optionSeries, washnitzerAlgebra.optionSeries_optionC,
    PowerSeries.map_C, ← washnitzerAlgebra.norm_toTate]
  exact TauCeti.PowerSeries.norm_C (c := 1) _

local notation "Wint" => intWashnitzerAlgebra σ K
local notation "Wint'" => intWashnitzerAlgebra (Option σ) K

/-- Adjoining the variable `Y`, as a ring map `K°⟨X⟩† → K°⟨X, Y⟩†`. -/
private noncomputable def intOptionC : Wint →+* Wint' :=
  ((washnitzerAlgebra (Option σ) K).val.toRingHom.comp
    ((optionC (σ := σ) (R := K)).toRingHom.comp (toWashnitzerAlgebra σ K))).codRestrict _ fun f ↦
    mem_intWashnitzerAlgebra_iff_norm_le_one.2
      ((norm_optionC _).trans_le (norm_toWashnitzerAlgebra_le_one f))

/-- `intOptionC` adjoins `Y` to the underlying overconvergent series. -/
private theorem toWashnitzerAlgebra_intOptionC (f : Wint) :
    toWashnitzerAlgebra (Option σ) K (intOptionC f) = optionC (toWashnitzerAlgebra σ K f) :=
  toWashnitzerAlgebra_mk _ _

/-- The variable `Y` of `K°⟨X, Y⟩†`. -/
private noncomputable def intY : Wint' :=
  ⟨MvPowerSeries.X none, X_mem_intWashnitzerAlgebra none⟩

/-- Evaluating a polynomial over `K°⟨X⟩†` at `Y` is compatible with the inclusions into the
Monsky–Washnitzer algebras. -/
private theorem toWashnitzerAlgebra_eval₂ (p : Polynomial Wint) :
    toWashnitzerAlgebra (Option σ) K (p.eval₂ intOptionC intY) =
      polynomialToOption (p.map (toWashnitzerAlgebra σ K)) := by
  have h : (toWashnitzerAlgebra (Option σ) K).comp (Polynomial.eval₂RingHom intOptionC intY) =
      (polynomialToOption (σ := σ) (R := K) : Polynomial W →+* W').comp
        (Polynomial.mapRingHom (toWashnitzerAlgebra σ K)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) (Subtype.ext ?_)
    · simp [toWashnitzerAlgebra_intOptionC]
    · simp [intY]
  exact RingHom.congr_fun h p

variable [CompleteSpace K]

/-- **Integral Weierstrass division.** If `g ∈ K⟨X, Y⟩†` has Gauss norm one and is distinguished of
degree `s` in `Y` with a unit distinguished coefficient, then every series `f` of Gauss norm at
most one is `q * g + r` with `‖q‖ ≤ 1` and `r` a polynomial in `Y` of degree less than `s` whose
coefficients have Gauss norm at most one. -/
private theorem exists_mul_add_eq_of_norm_le_one {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate)))
    (hg1 : ‖g‖ = 1) {f : W'} (hf : ‖f‖ ≤ 1) :
    ∃ (q : W') (r : Polynomial W), ‖q‖ ≤ 1 ∧ (∀ i, ‖r.coeff i‖ ≤ 1) ∧
      r.degree < s ∧ f = q * g + polynomialToOption r := by
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  have hf' : f = q * g + polynomialToOption r :=
    washnitzerAlgebra.optionSeries_injective (by simpa using hqr.symm)
  -- Map the division into the Tate algebra and apply the norm identity there.
  set φ := (toTate σ K : W →+* Tate)
  have hrφ : ∀ m, s ≤ m → ((r.map φ : Polynomial Tate) : PowerSeries Tate).coeff m = 0 :=
    fun m hm ↦ by
      rw [Polynomial.coeff_coe, Polynomial.coeff_map,
        Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast hm)), map_zero]
  have hmap : PowerSeries.map φ (optionSeries f) =
      PowerSeries.map φ (optionSeries q) * PowerSeries.map φ (optionSeries g) + r.map φ := by
    rw [hf']
    simp [Polynomial.polynomial_map_coe]
  have hnorm := hg.gaussNorm_mul_add_eq_max one_pos (fun x ↦ norm_mul _ _)
    (restrictedOptionEquiv (toTate _ K q)).2 hrφ
  rw [← washnitzerAlgebra.map_toTate_optionSeries, ← washnitzerAlgebra.map_toTate_optionSeries,
    ← hmap, ← norm_eq_gaussNorm_map_optionSeries, ← norm_eq_gaussNorm_map_optionSeries,
    ← norm_eq_gaussNorm_map_optionSeries, hg1, mul_one] at hnorm
  refine ⟨q, r, ?_, fun i ↦ ?_, hr, hf'⟩
  · exact (le_max_left _ _).trans (hnorm ▸ hf)
  · have hle := PowerSeries.le_gaussNorm norm 1 _
      (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
        (TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero hrφ)) i
    rw [one_pow, mul_one, Polynomial.coeff_coe, Polynomial.coeff_map] at hle
    exact (washnitzerAlgebra.norm_toTate (r.coeff i)).symm.trans_le
      (hle.trans ((le_max_right _ _).trans (hnorm ▸ hf)))

/-- An ideal of `K°⟨X, Y⟩†` containing a series of Gauss norm one which is distinguished in `Y`,
with a unit distinguished coefficient, is finitely generated as soon as `K°⟨X⟩†` is noetherian:
by integral Weierstrass division, the quotient by that series is a finite `K°⟨X⟩†`-module. -/
private theorem fg_of_isDistinguished_mem [IsNoetherianRing Wint] {I : Ideal Wint'} {g : Wint'}
    (hgI : g ∈ I) {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K (toWashnitzerAlgebra _ K g)) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K (toWashnitzerAlgebra _ K g)) : PowerSeries Tate)))
    (hg1 : ‖toWashnitzerAlgebra _ K g‖ = 1) : I.FG := by
  let : Algebra Wint Wint' := (intOptionC (σ := σ) (K := K)).toAlgebra
  let J : Ideal Wint' := Ideal.span {g}
  let ev : Polynomial Wint →ₐ[Wint] Wint' ⧸ J := Polynomial.aeval (Ideal.Quotient.mk J intY)
  let φ : Polynomial.degreeLT Wint s →ₗ[Wint] Wint' ⧸ J :=
    ev.toLinearMap ∘ₗ (Polynomial.degreeLT Wint s).subtype
  have hev (p : Polynomial Wint) : Ideal.Quotient.mk J (p.eval₂ intOptionC intY) = ev p := by
    have h : (Ideal.Quotient.mk J).comp (Polynomial.eval₂RingHom intOptionC intY) =
        (ev : Polynomial Wint →+* Wint' ⧸ J) :=
      Polynomial.ringHom_ext (fun a ↦ by
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          AlgHom.coe_toRingHom, ev, Polynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply Wint Wint' (Wint' ⧸ J), Ideal.Quotient.algebraMap_eq,
          RingHom.algebraMap_toAlgebra])
        (by simp [ev])
    exact RingHom.congr_fun h p
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨q, r, hq, hr1, hr, hf⟩ :=
      exists_mul_add_eq_of_norm_le_one hg hu hg1 (norm_toWashnitzerAlgebra_le_one f)
    -- Lift the quotient and the remainder to the integral algebras.
    obtain ⟨p, hp⟩ : r ∈ Polynomial.lifts (toWashnitzerAlgebra σ K) :=
      Polynomial.lifts_iff_coeff_lifts _ |>.2 fun n ↦
        ⟨⟨r.coeff n, mem_intWashnitzerAlgebra_iff_norm_le_one.2 (hr1 n)⟩,
          toWashnitzerAlgebra_mk _ _⟩
    rw [Polynomial.coe_mapRingHom] at hp
    have hpdeg : p.degree < s := by
      rwa [← Polynomial.degree_map_eq_of_injective toWashnitzerAlgebra_injective, hp]
    let q' : Wint' := ⟨q, mem_intWashnitzerAlgebra_iff_norm_le_one.2 hq⟩
    have hf' : f = q' * g + p.eval₂ intOptionC intY := toWashnitzerAlgebra_injective (by
      rw [map_add, map_mul, toWashnitzerAlgebra_eval₂, hp, toWashnitzerAlgebra_mk]
      exact hf)
    refine ⟨⟨p, Polynomial.mem_degreeLT.2 hpdeg⟩, ?_⟩
    have hgJ : Ideal.Quotient.mk J (q' * g) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))
    simp [φ, hf', hgJ, hev]
  have : Module.Finite Wint (Polynomial.degreeLT Wint s) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv Wint s).symm
  have : Module.Finite Wint (Wint' ⧸ J) := Module.Finite.of_surjective φ hφ
  have : IsNoetherian Wint' (Wint' ⧸ J) :=
    isNoetherian_of_tower Wint (isNoetherian_of_isNoetherianRing_of_finite Wint (Wint' ⧸ J))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker J.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgI))]
  exact ⟨{g}, by simp [Ideal.span]⟩

/-- An ideal of `K°⟨X, Y⟩†` containing a series of Gauss norm one is finitely generated as soon as
`K°⟨X⟩†` is noetherian: a triangular change of variables makes that series distinguished in `Y`
without changing its Gauss norm. -/
private theorem fg_of_norm_eq_one_mem [Finite σ] [IsNoetherianRing Wint] {I : Ideal Wint'}
    {f : Wint'} (hfI : f ∈ I) (hf1 : ‖toWashnitzerAlgebra _ K f‖ = 1) : I.FG := by
  have hf0 : toWashnitzerAlgebra _ K f ≠ 0 := fun h ↦ by simp [h] at hf1
  obtain ⟨α, hα, s, hd, hu⟩ :=
    washnitzerAlgebra.exists_triangularEquiv_isDistinguished_isUnit _ hf0
  have he (h : W') : ‖washnitzerAlgebra.triangularEquiv α hα h‖ = ‖h‖ := by
    rw [← washnitzerAlgebra.norm_toTate, washnitzerAlgebra.toTate_triangularEquiv,
      MvPowerSeries.norm_restrictedTriangularEquiv, washnitzerAlgebra.norm_toTate]
  let e : Wint' ≃+* Wint' :=
    restrictRingEquiv (washnitzerAlgebra.triangularEquiv α hα).toRingEquiv he
  have hef : toWashnitzerAlgebra _ K ((e : Wint' →+* Wint') f) =
      washnitzerAlgebra.triangularEquiv α hα (toWashnitzerAlgebra _ K f) :=
    toWashnitzerAlgebra_restrictRingEquiv _ he f
  have h := fg_of_isDistinguished_mem (I := I.map (e : Wint' →+* Wint'))
    (Ideal.mem_map_of_mem (e : Wint' →+* Wint') hfI) (hef ▸ hd) (hef ▸ hu)
    (hef ▸ (he _).trans hf1)
  rw [← Ideal.map_of_equiv (I := I) e]
  exact h.map _

end Division

/-- In a noetherian closed unit ball, the norms less than one have a largest element. -/
private theorem exists_forall_norm_le [IsNoetherianRing (Subring.unitClosedBall K)] :
    ∃ π : K, ‖π‖ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖ := by
  classical
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (unitBallIdeal K)
  obtain ⟨π, hπ, hπS⟩ : ∃ π ∈ unitBallIdeal K, ∀ b ∈ S, ‖(b : K)‖ ≤ ‖(π : K)‖ := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, zero_mem _, by simp⟩
    · obtain ⟨π, hπ, hmax⟩ := S.exists_max_image (fun b ↦ ‖(b : K)‖) hne
      exact ⟨π, hS ▸ Ideal.subset_span hπ, hmax⟩
  refine ⟨π, mem_unitBallIdeal.1 hπ, fun a ha ↦ ?_⟩
  have haS : (⟨a, Subring.mem_unitClosedBall.2 ha.le⟩ : Subring.unitClosedBall K) ∈
      Submodule.span (Subring.unitClosedBall K) (S : Set (Subring.unitClosedBall K)) :=
    hS ▸ mem_unitBallIdeal.2 ha
  refine Submodule.span_induction
    (p := fun (x : Subring.unitClosedBall K) _ ↦ ‖(x : K)‖ ≤ ‖(π : K)‖) hπS (by simp)
    (fun x y _ _ hx hy ↦ ?_) (fun b x _ hx ↦ ?_) haS
  · simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  · simpa using (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (Subring.mem_unitClosedBall.1 b.2)).trans hx)

/-- If every ideal of `K°⟨X⟩†` containing a series of Gauss norm one is finitely generated, and
some `π` with `‖π‖ < 1` has the largest norm less than one, then `K°⟨X⟩†` is noetherian: a nonzero
ideal is `πᵏ I'` for an ideal `I'` containing a series of Gauss norm one. -/
private theorem isNoetherianRing_of_forall_fg {π : K} (hπ1 : ‖π‖ < 1)
    (hπ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖)
    (h : ∀ (I : Ideal (intWashnitzerAlgebra τ K)) (f : intWashnitzerAlgebra τ K), f ∈ I →
      ‖toWashnitzerAlgebra τ K f‖ = 1 → I.FG) :
    IsNoetherianRing (intWashnitzerAlgebra τ K) := by
  classical
  set ι := toWashnitzerAlgebra τ K
  let c : intWashnitzerAlgebra τ K :=
    algebraMap (Subring.unitClosedBall K) _ ⟨π, Subring.mem_unitClosedBall.2 hπ1.le⟩
  have hc : ι c = algebraMap K (washnitzerAlgebra τ K) π :=
    Subtype.ext (by simp [ι, c, MvPowerSeries.algebraMap_apply])
  -- Multiples of `cᵐ` have Gauss norm at most `‖π‖ ^ m`.
  have hmem (m : ℕ) {x} (hx : x ∈ Ideal.span {c ^ m}) : ‖ι x‖ ≤ ‖π‖ ^ m := by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_pow, hc, norm_mul, norm_pow, washnitzerAlgebra.norm_algebraMap]
    exact mul_le_of_le_one_left (by positivity) (norm_toWashnitzerAlgebra_le_one b)
  -- A series of Gauss norm less than one is a multiple of `c`.
  have hdvd {x} (hx : ‖ι x‖ < 1) : x ∈ Ideal.span {c} := by
    have hxπ : ‖ι x‖ ≤ ‖π‖ := (washnitzerAlgebra.norm_le_iff (norm_nonneg _)).2 fun t ↦
      hπ _ ((washnitzerAlgebra.norm_coeff_le _ t).trans_lt hx)
    rcases eq_or_ne π 0 with rfl | hπ0
    · have : ι x = 0 := norm_le_zero_iff.1 (by simpa using hxπ)
      rw [toWashnitzerAlgebra_injective (this.trans (map_zero ι).symm)]
      exact zero_mem _
    refine Ideal.mem_span_singleton'.2
      ⟨⟨((algebraMap K (washnitzerAlgebra τ K) π⁻¹ * ι x : washnitzerAlgebra τ K) :
        MvPowerSeries τ K), mem_intWashnitzerAlgebra_iff_norm_le_one.2 ?_⟩,
        toWashnitzerAlgebra_injective ?_⟩
    · rw [norm_mul, washnitzerAlgebra.norm_algebraMap, norm_inv]
      exact inv_mul_le_one_of_le₀ hxπ (norm_nonneg _)
    · rw [map_mul, toWashnitzerAlgebra_mk, hc, mul_comm, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hπ0, map_one, one_mul]
  refine (isNoetherianRing_iff_ideal_fg _).2 fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hx₀pos : 0 < ‖ι x₀‖ :=
    norm_pos_iff.2 fun h ↦ hx₀ (toWashnitzerAlgebra_injective (h.trans (map_zero ι).symm))
  -- Choose the least `k` such that `I` is not contained in `(cᵏ⁺¹)`.
  have hex : ∃ k, ¬ I ≤ Ideal.span {c ^ (k + 1)} := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx₀pos hπ1
    refine ⟨n, fun hle ↦ (hn.trans_le' ?_).not_ge (hmem (n + 1) (hle hx₀I))⟩
    exact pow_le_pow_of_le_one (norm_nonneg _) hπ1.le n.le_succ
  obtain ⟨k, hk, hmin⟩ : ∃ k, ¬ I ≤ Ideal.span {c ^ (k + 1)} ∧
      ∀ j < k, I ≤ Ideal.span {c ^ (j + 1)} :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ not_not.1 (Nat.find_min hex hj)⟩
  have hIk : I ≤ Ideal.span {c ^ k} := by
    cases k with
    | zero => simp
    | succ j => exact hmin j j.lt_succ_self
  let I' : Ideal (intWashnitzerAlgebra τ K) :=
    Submodule.comap (LinearMap.mulLeft (intWashnitzerAlgebra τ K) (c ^ k)) I
  have hII' : I = Submodule.map (LinearMap.mulLeft (intWashnitzerAlgebra τ K) (c ^ k)) I' := by
    rw [Submodule.map_comap_eq, eq_comm, inf_eq_right]
    intro x hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hIk hx)
    exact ⟨b, by rw [LinearMap.mulLeft_apply, mul_comm, hb]⟩
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.1 hk
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (hIk hxI)
  have hbI' : b ∈ I' := by
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_comm]
    exact hxI
  have hb1 : ‖ι b‖ = 1 := by
    refine (norm_toWashnitzerAlgebra_le_one b).antisymm (not_lt.1 fun hb ↦ hx ?_)
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 (hdvd hb)
    exact Ideal.mem_span_singleton'.2 ⟨d, by ring⟩
  rw [hII']
  exact Submodule.FG.map _ (h I' b hbI' hb1)

section Main

variable [CompleteSpace K]

/-- If `K°` and `K°⟨X⟩†` are noetherian, so is `K°⟨X, Y⟩†`. -/
private theorem isNoetherianRing_option [Finite σ] [IsNoetherianRing (Subring.unitClosedBall K)]
    [IsNoetherianRing (intWashnitzerAlgebra σ K)] :
    IsNoetherianRing (intWashnitzerAlgebra (Option σ) K) := by
  obtain ⟨π, hπ1, hπ⟩ := exists_forall_norm_le (K := K)
  exact isNoetherianRing_of_forall_fg hπ1 hπ fun _ _ hfI hf1 ↦ fg_of_norm_eq_one_mem hfI hf1

/-- **The integral Monsky–Washnitzer algebra is noetherian.** Over a complete ultrametric normed
field `K` whose closed unit ball `K°` is noetherian, for instance a complete discretely valued
field, the algebra `K°⟨X⟩†` of overconvergent series with integral coefficients in finitely many
variables is a noetherian ring. -/
instance isNoetherianRing [Finite σ] [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (intWashnitzerAlgebra σ K) :=
  Finite.induction_empty_option
    (P := fun σ ↦ ∀ [Finite σ], IsNoetherianRing (intWashnitzerAlgebra σ K))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      have := h
      isNoetherianRing_of_equiv e)
    isNoetherianRing_of_isEmpty
    (fun {_} _ h _ ↦
      have := h
      isNoetherianRing_option) σ

/-- For finitely many variables, `K°⟨X⟩†` is noetherian exactly when `K°` is. -/
theorem isNoetherianRing_iff [Finite σ] :
    IsNoetherianRing (intWashnitzerAlgebra σ K) ↔ IsNoetherianRing (Subring.unitClosedBall K) :=
  ⟨fun _ ↦ isNoetherianRing_unitClosedBall σ, fun _ ↦ inferInstance⟩

end Main

end TauCeti.Dagger.intWashnitzerAlgebra
