/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Weierstrass
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Monsky–Washnitzer algebras are noetherian

Over a complete ultrametric normed field `K`, the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely
many variables is a noetherian ring.

The proof is the classical induction on the number of variables via Weierstrass theory. Write
`W = K⟨X⟩†` and `W' = K⟨X, Y⟩†`, with `Y = X none`, and regard `W'` as a `W`-algebra through
`washnitzerAlgebra.optionC`. A nonzero ideal `I` of `W'` contains a nonzero series `f`, and a
triangular automorphism of `W'` makes `f` distinguished in `Y` of some degree `s`, with a unit
coefficient in degree `s`. Overconvergent Weierstrass division by `f` shows that `W' ⧸ (f)` is
spanned over `W` by `1, Y, …, Y ^ (s - 1)`, so it is a finite `W`-module. If `W` is noetherian,
`W' ⧸ (f)` is then a noetherian module, hence `I` is finitely generated.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.isNoetherianRing`: `K⟨X⟩†` is noetherian for finitely many
  variables.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4 (1).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, Theorem 1 (the same argument for
  Tate algebras).
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- An ideal of `K⟨X, Y⟩†` containing a series which is distinguished in `Y`, with a unit
coefficient in the distinguished degree, is finitely generated as soon as `K⟨X⟩†` is
noetherian: by Weierstrass division, the quotient by that series is a finite `K⟨X⟩†`-module. -/
private theorem fg_of_isDistinguished_mem [IsNoetherianRing W] {I : Ideal W'} {g : W'}
    (hgI : g ∈ I) {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) : I.FG := by
  let : Algebra W W' := (optionC (σ := σ) (R := K)).toRingHom.toAlgebra
  let Y : W' := X (Option σ) K none
  let J : Ideal W' := Ideal.span {g}
  have hev (r : Polynomial W) : optionSeries (Polynomial.aeval Y r) = (r : PowerSeries W) :=
    optionSeries_eval₂_optionC_X_none r
  -- Division by `g` makes the remainders of degree `< s` surject onto `W' ⧸ (g)`.
  let φ : Polynomial.degreeLT W s →ₗ[W] W' ⧸ J :=
    ((Ideal.Quotient.mkₐ W J).comp (Polynomial.aeval Y)).toLinearMap ∘ₗ
      (Polynomial.degreeLT W s).subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
    have hf : f = q * g + Polynomial.aeval Y r :=
      optionSeries_injective (by rw [map_add, map_mul, hev]; exact hqr.symm)
    refine ⟨⟨r, Polynomial.mem_degreeLT.mpr hr⟩, ?_⟩
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    refine (Ideal.Quotient.eq.mpr ?_).symm
    rw [hf, add_sub_cancel_right]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have : Module.Finite W (Polynomial.degreeLT W s) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv W s).symm
  have : Module.Finite W (W' ⧸ J) := Module.Finite.of_surjective φ hφ
  have : IsNoetherian W' (W' ⧸ J) :=
    isNoetherian_of_tower W (isNoetherian_of_isNoetherianRing_of_finite W (W' ⧸ J))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker J.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgI))]
  exact ⟨{g}, by simp [Ideal.span]⟩

/-- If `K⟨X⟩†` is noetherian, so is `K⟨X, Y⟩†`. -/
private theorem isNoetherianRing_option [Finite σ] [IsNoetherianRing W] : IsNoetherianRing W' := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  by_cases hI : I = ⊥
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨f, hfI, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf
  let e : W' ≃+* W' := (triangularEquiv α hα).toRingEquiv
  have h := fg_of_isDistinguished_mem (I := I.map (e : W' →+* W'))
    (Ideal.mem_map_of_mem (e : W' →+* W') hfI) hd hu
  rw [← Ideal.map_of_equiv (I := I) e]
  exact h.map _

omit [CompleteSpace K] in
/-- Renaming the variables along an equivalence preserves noetherianity of `K⟨X⟩†`. -/
private theorem isNoetherianRing_of_equiv {τ : Type*} [Finite σ] [Finite τ] (e : σ ≃ τ)
    [IsNoetherianRing W] : IsNoetherianRing (washnitzerAlgebra τ K) := by
  classical
  have hX₁ (i : σ) (t : τ →₀ ℕ) : ‖(MvPolynomial.X (R := K) (e i)).coeff t‖ ≤ 1 := by
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  have hX₁' (i : τ) (t : σ →₀ ℕ) : ‖(MvPolynomial.X (R := K) (e.symm i)).coeff t‖ ≤ 1 := by
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  exact isNoetherianRing_of_ringEquiv W
    (substEquiv (fun s ↦ MvPolynomial.X (e s)) (fun _ ↦ MvPolynomial.constantCoeff_X _ _) hX₁
      (fun t ↦ MvPolynomial.X (e.symm t)) (fun _ ↦ MvPolynomial.constantCoeff_X _ _) hX₁'
      (by simp) (by simp)).toRingEquiv

omit [CompleteSpace K] in
/-- With no variables, `K⟨X⟩† = K` is noetherian. -/
private theorem isNoetherianRing_of_isEmpty [IsEmpty σ] : IsNoetherianRing W := by
  refine isNoetherianRing_of_surjective K W (algebraMap K W) fun f ↦ ?_
  obtain ⟨c, hc⟩ := C_surjective (σ := σ) (f : MvPowerSeries σ K)
  exact ⟨c, Subtype.ext (by simpa [MvPowerSeries.algebraMap_apply] using hc)⟩

/-- **Monsky–Washnitzer algebras are noetherian.** Over a complete ultrametric normed field `K`,
the algebra `K⟨X⟩†` of overconvergent power series in finitely many variables is a noetherian
ring. No characteristic or nontrivial-norm assumption is needed. -/
instance isNoetherianRing [Finite σ] : IsNoetherianRing (washnitzerAlgebra σ K) :=
  Finite.induction_empty_option
    (P := fun σ ↦ ∀ [Finite σ], IsNoetherianRing (washnitzerAlgebra σ K))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      have := h
      isNoetherianRing_of_equiv e)
    isNoetherianRing_of_isEmpty
    (fun {_} _ h _ ↦
      have := h
      isNoetherianRing_option) σ

end TauCeti.Dagger.washnitzerAlgebra
