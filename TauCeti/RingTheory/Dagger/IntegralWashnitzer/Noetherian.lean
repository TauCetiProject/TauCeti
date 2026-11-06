/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.RingTheory.Ideal.Colon
import TauCeti.RingTheory.Ideal.Quotient.Finite

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
* `TauCeti.Dagger.intWashnitzerAlgebra.isNoetherianRing_of_norm_eq_zpow`: the same for a complete
  discretely valued field, whose nonzero norms are the integer powers of `‖π‖`.
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
open washnitzerAlgebra (toTate optionC polynomialToOption)

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
    IsNoetherianRing (intWashnitzerAlgebra τ K) :=
  isNoetherianRing_of_ringEquiv _ (restrictRingEquiv
    (washnitzerAlgebra.renameAlgEquiv (R := K) e).toRingEquiv
    (washnitzerAlgebra.norm_renameAlgEquiv e))

section Division

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

local notation "Wint" => intWashnitzerAlgebra σ K
local notation "Wint'" => intWashnitzerAlgebra (Option σ) K

/-- Adjoining the variable `Y`, as a ring map `K°⟨X⟩† → K°⟨X, Y⟩†`. -/
private noncomputable def intOptionC : Wint →+* Wint' :=
  ((washnitzerAlgebra (Option σ) K).val.toRingHom.comp
    ((optionC (σ := σ) (R := K)).toRingHom.comp (toWashnitzerAlgebra σ K))).codRestrict _ fun f ↦
    mem_intWashnitzerAlgebra_iff_norm_le_one.2
      ((washnitzerAlgebra.norm_optionC _).trans_le (norm_toWashnitzerAlgebra_le_one f))

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

/-- An ideal of `K°⟨X, Y⟩†` containing a series of Gauss norm one which is distinguished in `Y`,
with a unit distinguished coefficient, is finitely generated as soon as `K°⟨X⟩†` is noetherian:
by integral Weierstrass division, the quotient by that series is a finite `K°⟨X⟩†`-module. -/
private theorem fg_of_isDistinguished_mem [IsNoetherianRing Wint] {I : Ideal Wint'} {g : Wint'}
    (hgI : g ∈ I) {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (washnitzerAlgebra.toTate _ K (toWashnitzerAlgebra _ K g)) :
        PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (washnitzerAlgebra.toTate _ K (toWashnitzerAlgebra _ K g)) :
        PowerSeries Tate)))
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
        simp [ev, IsScalarTower.algebraMap_apply Wint Wint' (Wint' ⧸ J),
          RingHom.algebraMap_toAlgebra]) (by simp [ev])
    exact RingHom.congr_fun h p
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨q, r, hr, hf, hq, hr1⟩ :=
      exists_mul_add_eq_and_norm_le_of_isDistinguished hg hu (toWashnitzerAlgebra _ K f)
    have hf1 := norm_toWashnitzerAlgebra_le_one f
    rw [hg1, mul_one] at hq
    -- Lift the quotient and the remainder to the integral algebras.
    obtain ⟨p, hp⟩ : r ∈ Polynomial.lifts (toWashnitzerAlgebra σ K) :=
      Polynomial.lifts_iff_coeff_lifts _ |>.2 fun n ↦
        ⟨⟨r.coeff n, mem_intWashnitzerAlgebra_iff_norm_le_one.2 ((hr1 n).trans hf1)⟩,
          toWashnitzerAlgebra_mk _ _⟩
    rw [Polynomial.coe_mapRingHom] at hp
    have hpdeg : p.degree < s := by
      rwa [← Polynomial.degree_map_eq_of_injective toWashnitzerAlgebra_injective, hp]
    let q' : Wint' := ⟨q, mem_intWashnitzerAlgebra_iff_norm_le_one.2 (hq.trans hf1)⟩
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
  exact Ideal.fg_of_le_of_finite_quotient (A := Wint) (Submodule.fg_span_singleton g)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgI))

/-- An ideal of `K°⟨X, Y⟩†` containing a series of Gauss norm one is finitely generated as soon as
`K°⟨X⟩†` is noetherian: a triangular change of variables makes that series distinguished in `Y`
without changing its Gauss norm. -/
private theorem fg_of_norm_eq_one_mem [Finite σ] [IsNoetherianRing Wint] {I : Ideal Wint'}
    {f : Wint'} (hfI : f ∈ I) (hf1 : ‖toWashnitzerAlgebra _ K f‖ = 1) : I.FG := by
  have hf0 : toWashnitzerAlgebra _ K f ≠ 0 := fun h ↦ by simp [h] at hf1
  obtain ⟨α, hα, s, hd, hu⟩ :=
    washnitzerAlgebra.exists_triangularEquiv_isDistinguished_isUnit _ hf0
  have he := washnitzerAlgebra.norm_triangularEquiv (R := K) α hα
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

/-- If every ideal of `K°⟨X⟩†` containing a series of Gauss norm one is finitely generated, and
some `π` with `‖π‖ < 1` has the largest norm less than one, then `K°⟨X⟩†` is noetherian: a nonzero
ideal is `πᵏ I'` for an ideal `I'` containing a series of Gauss norm one. -/
private theorem isNoetherianRing_of_forall_fg {π : K} (hπ1 : ‖π‖ < 1)
    (hπ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖)
    (h : ∀ (I : Ideal (intWashnitzerAlgebra τ K)) (f : intWashnitzerAlgebra τ K), f ∈ I →
      ‖toWashnitzerAlgebra τ K f‖ = 1 → I.FG) :
    IsNoetherianRing (intWashnitzerAlgebra τ K) := by
  set ι := toWashnitzerAlgebra τ K
  let a : Subring.unitClosedBall K := ⟨π, Subring.mem_unitClosedBall.2 hπ1.le⟩
  let c : intWashnitzerAlgebra τ K := algebraMap (Subring.unitClosedBall K) _ a
  refine (isNoetherianRing_iff_ideal_fg _).2 fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hx₀pos : 0 < ‖ι x₀‖ :=
    norm_pos_iff.2 fun h ↦ hx₀ (toWashnitzerAlgebra_injective (h.trans (map_zero ι).symm))
  -- Since `‖π‖ ^ n < ‖x₀‖` for some `n`, `I = cᵏ I'` with `I'` not contained in `(c)`.
  have hex : ∃ n, ¬ I ≤ Ideal.span {c ^ n} := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx₀pos hπ1
    refine ⟨n, fun hle ↦ hn.not_ge ?_⟩
    have := norm_toWashnitzerAlgebra_le_of_mem_span (a := a ^ n) (f := x₀)
      (by rw [map_pow]; exact hle hx₀I)
    simpa [a] using this
  obtain ⟨k, hIk, hk⟩ := Ideal.exists_eq_span_pow_mul_colon_not_le hex
  -- An element of `I'` outside `(c)` has Gauss norm one.
  obtain ⟨b, hbI', hb⟩ := Set.not_subset.1 hk
  have hb1 : ‖ι b‖ = 1 := by
    refine (norm_toWashnitzerAlgebra_le_one b).antisymm (not_lt.1 fun hlt ↦ hb ?_)
    exact mem_span_algebraMap_iff_norm_le.2 ((washnitzerAlgebra.norm_le_iff (norm_nonneg _)).2
      fun t ↦ hπ _ ((washnitzerAlgebra.norm_coeff_le _ t).trans_lt hlt))
  rw [hIk]
  exact (Submodule.fg_span_singleton _).mul (h _ b hbI' hb1)

section Main

variable [CompleteSpace K]

/-- If `K°` and `K°⟨X⟩†` are noetherian, so is `K°⟨X, Y⟩†`. -/
private theorem isNoetherianRing_option [Finite σ] [IsNoetherianRing (Subring.unitClosedBall K)]
    [IsNoetherianRing (intWashnitzerAlgebra σ K)] :
    IsNoetherianRing (intWashnitzerAlgebra (Option σ) K) := by
  obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg
    (IsNoetherian.noetherian (unitBallIdeal K))
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

/-- **Discretely valued fields.** Over a complete field `K` whose nonzero norms are the integer
powers of `‖π‖` for some `0 < ‖π‖ < 1`, the integral Monsky–Washnitzer algebra `K°⟨X⟩†` in
finitely many variables is noetherian, since `K°` is then a principal ideal ring. -/
theorem isNoetherianRing_of_norm_eq_zpow [Finite σ] {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hdisc : ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) :
    IsNoetherianRing (intWashnitzerAlgebra σ K) :=
  have := isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow hπ0 hπ1 hdisc
  inferInstance

/-- For finitely many variables, `K°⟨X⟩†` is noetherian exactly when `K°` is. -/
theorem isNoetherianRing_iff [Finite σ] :
    IsNoetherianRing (intWashnitzerAlgebra σ K) ↔ IsNoetherianRing (Subring.unitClosedBall K) :=
  ⟨fun _ ↦ isNoetherianRing_unitClosedBall σ, fun _ ↦ inferInstance⟩

end Main

end TauCeti.Dagger.intWashnitzerAlgebra
