/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
import TauCeti.Analysis.ExteriorPower.Overlap
import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.LinearAlgebra.Basis.Submodule
import TauCeti.LinearAlgebra.LinearIndependent.Fin
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

/-!
# Submodularity of Euclidean subspace heights

The Euclidean heights of an intersection and a sum satisfy
`H(U ∩ W) H(U + W) ≤ H(U) H(W)`, with constant one. We prove the
relative Arakelov and absolute Euclidean versions, and their logarithmic forms.
The zero and whole subspaces are included.

Choose bases of `U` and `W` with a common initial basis of their intersection.
The archimedean local inequality is Koteljanskii's inequality for Gram
determinants; at finite places it is the overlapping-family exterior maximum
norm inequality. Multiplication over all places and taking degree roots give
the global inequalities on the native Plücker heights.

## References

* T. Struppeck and J. D. Vaaler, *Inequalities for heights of algebraic subspaces
  and the Thue–Siegel principle* (1990).
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.12).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §2.8.
-/

public section

open scoped BigOperators
open Module Submodule Set NumberField

namespace NumberField.InfinitePlace

open TauCeti

variable {K ι : Type*} [Field K] [LinearOrder ι] [Fintype ι]

/-- The archimedean Euclidean local factors of overlapping Plücker families
satisfy the product inequality, with the real or complex place multiplicity. -/
theorem plucker_overlap_le (w : InfinitePlace K) {p q r : ℕ}
    (x : Fin p → ι → K) (y : Fin q → ι → K) (z : Fin r → ι → K) :
    (∑ s, ‖w.embedding (plucker x s)‖ ^ 2) ^ ((w.mult : ℝ) / 2) *
        (∑ s, ‖w.embedding (plucker (Fin.append x (Fin.append y z)) s)‖ ^ 2) ^
          ((w.mult : ℝ) / 2) ≤
      (∑ s, ‖w.embedding (plucker (Fin.append x y) s)‖ ^ 2) ^ ((w.mult : ℝ) / 2) *
        (∑ s, ‖w.embedding (plucker (Fin.append x z) s)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
  have hb := sum_norm_plucker_sq_overlap_le (fun i j ↦ w.embedding (x i j))
    (fun i j ↦ w.embedding (y i j)) (fun i j ↦ w.embedding (z i j))
  have happ {a b : ℕ} (u : Fin a → ι → K) (v : Fin b → ι → K) :
      Fin.append (fun i j ↦ w.embedding (u i j)) (fun i j ↦ w.embedding (v i j)) =
        fun i j ↦ w.embedding (Fin.append u v i j) := by
    ext i j
    induction i using Fin.addCases <;> simp
  simp_rw [happ, plucker_map] at hb
  have hn {a : ℕ} (u : Fin a → ι → K) :
      0 ≤ ∑ s, ‖w.embedding (plucker u s)‖ ^ 2 := by positivity
  simpa only [Real.mul_rpow (hn x) (hn (Fin.append x (Fin.append y z))),
    Real.mul_rpow (hn (Fin.append x y)) (hn (Fin.append x z))] using
    Real.rpow_le_rpow (by positivity) hb (by positivity : 0 ≤ (w.mult : ℝ) / 2)

end NumberField.InfinitePlace

namespace TauCeti

variable {K ι : Type*} [Field K] [NumberField K] [LinearOrder ι] [Finite ι]

/-- The relative Arakelov heights of the Plücker vectors of overlapping
independent families satisfy the constant-one product inequality. -/
theorem arakelovMulHeight_plucker_overlap_le {p q r : ℕ}
    {x : Fin p → ι → K} {y : Fin q → ι → K} {z : Fin r → ι → K}
    (h : LinearIndependent K (Fin.append x (Fin.append y z))) :
    arakelovMulHeight (plucker x) *
        arakelovMulHeight (plucker (Fin.append x (Fin.append y z))) ≤
      arakelovMulHeight (plucker (Fin.append x y)) *
        arakelovMulHeight (plucker (Fin.append x z)) := by
  classical
  let _ := Fintype.ofFinite ι
  have hx := (linearIndependent_fin_append.mp h).1
  have hxy := h.fin_append_left_append
  have hxz := h.fin_append_right_append
  have h0 := (plucker_ne_zero_iff _).mpr hx
  have h1 := (plucker_ne_zero_iff _).mpr h
  have h2 := (plucker_ne_zero_iff _).mpr hxy
  have h3 := (plucker_ne_zero_iff _).mpr hxz
  have hfin (v : FinitePlace K) :
      (⨆ s, v (plucker x s)) * (⨆ s, v (plucker (Fin.append x (Fin.append y z)) s)) ≤
        (⨆ s, v (plucker (Fin.append x y) s)) * (⨆ s, v (plucker (Fin.append x z) s)) :=
    v.val.iSup_plucker_overlap_le (FinitePlace.add_le v) x y z
  -- Pair the local factors before comparing the finite products and finprods.
  rw [arakelovMulHeight_eq h0, arakelovMulHeight_eq h1,
    arakelovMulHeight_eq h2, arakelovMulHeight_eq h3]
  conv_lhs => rw [mul_mul_mul_comm]
  conv_rhs => rw [mul_mul_mul_comm]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (FinitePlace.hasFiniteMulSupport_iSup h0)
      (FinitePlace.hasFiniteMulSupport_iSup h1),
    ← finprod_mul_distrib (FinitePlace.hasFiniteMulSupport_iSup h2)
      (FinitePlace.hasFiniteMulSupport_iSup h3)]
  apply mul_le_mul
  · -- The height factors use Fintype.ofFinite, whereas the local inequality uses
    -- the powersetCard instance induced by the chosen Fintype on ι. Align them.
    have hf (a : ℕ) : Fintype.ofFinite (powersetCard ι a) =
          powersetCard.instFintypeElemFinset ι a := Subsingleton.elim _ _
    exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦ by
      rw [hf p, hf (p + (q + r)), hf (p + q), hf (p + r)]
      exact w.plucker_overlap_le x y z
  · exact finprod_le_finprod₀
      ((FinitePlace.hasFiniteMulSupport_iSup h0).mul (FinitePlace.hasFiniteMulSupport_iSup h1))
      (fun v ↦ mul_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _)
        (Real.iSup_nonneg_of_nonnegHomClass v _))
      ((FinitePlace.hasFiniteMulSupport_iSup h2).mul (FinitePlace.hasFiniteMulSupport_iSup h3)) hfin
  · exact finprod_nonneg fun v ↦ mul_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _)
      (Real.iSup_nonneg_of_nonnegHomClass v _)
  · exact Finset.prod_nonneg fun _ _ ↦ by positivity

end TauCeti

namespace Submodule

open TauCeti

variable {K ι : Type*} [Field K] [NumberField K] [LinearOrder ι] [Finite ι]

/-- **Submodularity of the relative Euclidean subspace height.** The product
of the heights of an intersection and a sum is bounded by the original product. -/
theorem relativeSubspaceArakelovHeight_inf_mul_sup_le (U W : Submodule K (ι → K)) :
    relativeSubspaceArakelovHeight (U ⊓ W) * relativeSubspaceArakelovHeight (U ⊔ W) ≤
      relativeSubspaceArakelovHeight U * relativeSubspaceArakelovHeight W := by
  obtain ⟨p, q, r, x, y, z, h, hI, hU, hW, hS⟩ :=
    U.exists_linearIndependent_span_inf_sup W
  have hx := (linearIndependent_fin_append.mp h).1
  have hxy := h.fin_append_left_append
  have hxz := h.fin_append_right_append
  rw [← hI, ← hS, ← hU, ← hW, relativeSubspaceArakelovHeight_span_range hx,
    relativeSubspaceArakelovHeight_span_range h, relativeSubspaceArakelovHeight_span_range hxy,
    relativeSubspaceArakelovHeight_span_range hxz]
  exact arakelovMulHeight_plucker_overlap_le h

/-- **Struppeck–Vaaler submodularity of absolute Euclidean subspace heights.**
No disjointness, complementarity or positive-dimension hypothesis is required. -/
theorem subspaceHeight_inf_mul_sup_le (U W : Submodule K (ι → K)) :
    subspaceHeight (U ⊓ W) * subspaceHeight (U ⊔ W) ≤ subspaceHeight U * subspaceHeight W := by
  apply (pow_le_pow_iff_left₀
    (mul_nonneg (subspaceHeight_pos _).le (subspaceHeight_pos _).le)
    (mul_nonneg (subspaceHeight_pos _).le (subspaceHeight_pos _).le)
    (show finrank ℚ K ≠ 0 from finrank_pos.ne')).mp
  simpa only [mul_pow, subspaceHeight_pow_finrank] using
    relativeSubspaceArakelovHeight_inf_mul_sup_le U W

/-- The logarithmic relative Euclidean subspace height is submodular. -/
theorem relativeSubspaceArakelovLogHeight_inf_add_sup_le (U W : Submodule K (ι → K)) :
    relativeSubspaceArakelovLogHeight (U ⊓ W) + relativeSubspaceArakelovLogHeight (U ⊔ W) ≤
      relativeSubspaceArakelovLogHeight U + relativeSubspaceArakelovLogHeight W := by
  have h := Real.log_le_log
    (mul_pos (relativeSubspaceArakelovHeight_pos _) (relativeSubspaceArakelovHeight_pos _))
    (relativeSubspaceArakelovHeight_inf_mul_sup_le U W)
  simpa only [Real.log_mul (relativeSubspaceArakelovHeight_pos _).ne'
    (relativeSubspaceArakelovHeight_pos _).ne',
    relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight] using h

/-- The absolute logarithmic Euclidean subspace height is submodular. -/
theorem subspaceLogHeight_inf_add_sup_le (U W : Submodule K (ι → K)) :
    subspaceLogHeight (U ⊓ W) + subspaceLogHeight (U ⊔ W) ≤
      subspaceLogHeight U + subspaceLogHeight W := by
  have h := Real.log_le_log (mul_pos (subspaceHeight_pos _) (subspaceHeight_pos _))
    (subspaceHeight_inf_mul_sup_le U W)
  simpa only [Real.log_mul (subspaceHeight_pos _).ne' (subspaceHeight_pos _).ne',
    subspaceLogHeight_eq_log_subspaceHeight] using h

end Submodule
