/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.MaximumModulus
import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Simultaneous attainment of polynomial Gauss norms

A finite family of polynomials over an algebraically closed ultrametric normed field admits one
point of the closed unit polydisc at which each polynomial attains its unit Gauss norm. The point
can be chosen in the coefficient field itself, even if it is not complete. In particular this
applies over the algebraic closure of `ℚ_[p]` without passing to the completed algebraic closure.

We use the unit-polydisc maximum principle (Bosch, Güntzer and Remmert, *Non-Archimedean
Analysis*, §5.1.4) in the form `MvPowerSeries.exists_norm_restrictedEval₂_eq_norm`:
apply it to the product of the nonzero polynomials in the completion, using roots of unity
already in the coefficient field. Multiplicativity then forces attainment in each factor.
-/

public section

open Finset UniformSpace MvPowerSeries

namespace MvPolynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {n : ℕ}

-- The restricted evaluation API uses `Fin n` as the variable type.
private theorem exists_forall_norm_coeff_le_norm_eval_fin {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin n) K) :
    ∃ x : Fin n → K, (∀ j, ‖x j‖ ≤ 1) ∧ ∀ i ∈ s, ∀ d, ‖(P i).coeff d‖ ≤ ‖eval x (P i)‖ := by
  classical
  -- Discard zero factors, for which the coefficient bound holds at every point.
  let t := s.filter (fun i ↦ P i ≠ 0)
  let Q := ∏ i ∈ t, P i
  have hQ : Q ≠ 0 := prod_ne_zero_iff.mpr (fun i hi ↦ (mem_filter.mp hi).2)
  let incl := TauCeti.MvPowerSeries.polynomialToRestricted (R := K) (fun _ : Fin n ↦ 1)
  have hQ' : incl Q ≠ 0 := fun h ↦ hQ <| MvPolynomial.coe_injective _ _ <| by
    simpa [incl] using congrArg Subtype.val h
  have hD : {d : Fin n →₀ ℕ | ‖MvPowerSeries.coeff d (incl Q : MvPowerSeries (Fin n) K)‖ =
      ‖incl Q‖}.Finite :=
    ((incl Q).property.finite_setOfPred_achievesGaussNorm (by simpa using hQ')).subset fun d hd ↦ by
      simpa [AchievesGaussNorm, norm_eq_gaussNorm] using hd
  obtain ⟨m, hdeg, hm⟩ := IsUltrametricDist.exists_lt_norm_natCast_eq_one K
    (hD.toFinset.sup Finsupp.degree)
  have : NeZero (m : K) := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K m
  let φ : K →+* Completion K := Completion.coeRingHom
  have hφ (a : K) : ‖φ a‖ = ‖a‖ := Completion.norm_coe a
  have hm' : ‖(m : Completion K)‖ = 1 := by rw [← map_natCast φ, hφ, hm]
  -- All coordinates of the maximizing point are in the image of `K`.
  obtain ⟨y, hy, hyζ, hmax⟩ := exists_norm_restrictedEval₂_eq_norm (S := Completion K) φ hφ
    (hζ.map_of_injective (f := φ) (Completion.coe_injective K)) hm' (incl Q) fun d hd j ↦
      (Finsupp.le_degree j d).trans_lt ((Finset.le_sup (hD.mem_toFinset.mpr hd)).trans_lt hdeg)
  choose a _ ha using hyζ
  let x : Fin n → K := fun j ↦ ζ ^ a j
  have hxy (j : Fin n) : φ (x j) = y j := by rw [ha j, ← map_pow]
  let e := restrictedEval₂ φ y (fun r ↦ (hφ r).le) hy
  have he (p : MvPolynomial (Fin n) K) : ‖e (incl p)‖ = ‖eval x p‖ := by
    dsimp only [e, incl]
    rw [TauCeti.MvPowerSeries.polynomialToRestricted_apply, restrictedEval₂_polynomial,
      ← hφ (eval x p)]
    have hcoord : (⇑φ ∘ x) = y := funext hxy
    simp only [MvPolynomial.eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id, hcoord]
  refine ⟨x, fun j ↦ by simpa only [← hxy, hφ] using hy j, fun i hi d ↦ ?_⟩
  by_cases hp : P i = 0
  · simp [hp]
  have hprod : ∏ j ∈ t, ‖e (incl (P j))‖ = ∏ j ∈ t, ‖incl (P j)‖ := by
    simpa only [Q, map_prod, norm_prod] using hmax
  have hn : (∏ j ∈ t, ‖e (incl (P j))‖) ≠ 0 := by
    simpa only [hprod, ← norm_prod, ← map_prod] using norm_ne_zero_iff.mpr hQ'
  have hge : ‖incl (P i)‖ ≤ ‖e (incl (P i))‖ := le_of_not_gt fun hlt ↦
    (prod_lt_prod₀ (fun j hj ↦ (norm_nonneg _).lt_of_ne (prod_ne_zero_iff.mp hn j hj).symm)
      (fun j _ ↦ norm_restrictedEval₂_le ..) ⟨i, mem_filter.mpr ⟨hi, hp⟩, hlt⟩).ne hprod
  rw [← he]
  simpa only [incl, TauCeti.MvPowerSeries.coe_polynomialToRestricted, MvPolynomial.coeff_coe] using
    (norm_coeff_le_norm (incl (P i)) d).trans hge

/-- A finite family of multivariate polynomials over an algebraically closed ultrametric field
has a common point on the closed unit polydisc at which every evaluation dominates all
coefficient norms of its polynomial. The coefficient field need not be complete. -/
theorem exists_forall_norm_coeff_le_norm_eval {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ K) :
    ∃ x : σ → K, (∀ j, ‖x j‖ ≤ 1) ∧ ∀ i ∈ s, ∀ d, ‖(P i).coeff d‖ ≤ ‖eval x (P i)‖ := by
  classical
  let v := s.biUnion fun i ↦ (P i).vars
  let e := Finite.equivFin (↥v)
  let f : Fin (Nat.card ↥v) → σ := Subtype.val ∘ e.symm
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  let Q (i : ι) := killCompl hf (P i)
  have hQ (i : ι) (hi : i ∈ s) : rename f (Q i) = P i := by
    obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range (P i) f hf (fun j hj ↦
      ⟨e ⟨j, mem_biUnion.mpr ⟨i, hi, hj⟩⟩, by simp [f]⟩)
    dsimp only [Q]
    rw [← hq, killCompl_rename_app]
  obtain ⟨y, hy, hyQ⟩ := exists_forall_norm_coeff_le_norm_eval_fin s Q
  let x (j : σ) : K := if hj : j ∈ v then y (e ⟨j, hj⟩) else 0
  have hxy : x ∘ f = y := by
    funext j
    simp [x, f, (e.symm j).property]
  refine ⟨x, fun j ↦ by dsimp only [x]; split <;> simp [hy], fun i hi d ↦ ?_⟩
  rw [← hQ i hi, eval_rename, hxy]
  by_cases hd : (rename f (Q i)).coeff d = 0
  · simp [hd]
  obtain ⟨a, rfl, -⟩ := coeff_rename_ne_zero f (Q i) d hd
  simpa only [coeff_rename_mapDomain f hf] using hyQ i hi a

end MvPolynomial
