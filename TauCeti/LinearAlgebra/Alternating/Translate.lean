/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Alternating maps on translated arguments

Subtracting a common vector `b` from every argument of an alternating map only produces the terms
in which `b` replaces a single argument, since every term containing `b` twice vanishes
(`AlternatingMap.map_sub_const`). Applied to the edge vectors `w i.succ - w 0` of a simplex with
vertices `w 0, …, w n`, this gives the alternating sum of the values on the faces
`Fin.removeNth j w` (`AlternatingMap.map_succ_sub_zero`). This is how a form evaluated on the edges
of the face opposite the origin of the standard simplex splits into its coordinate coefficients, in
the boundary term of Stokes' theorem for simplices.
-/

public section

open Function

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Subtracting a common vector `b` from every argument of an alternating map leaves the original
value minus the values in which `b` replaces one argument. -/
theorem map_sub_const {ι : Type*} [Fintype ι] [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N) (v : ι → M)
    (b : M) : f (fun i ↦ v i - b) = f v - ∑ i, f (update v i b) := by
  -- Index the arguments by `Fin n` along `Fintype.equivFin ι`, and induct on `n`.
  suffices H : ∀ (n : ℕ) (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M),
      f (fun i ↦ v i - b) = f v - ∑ i, f (update v i b) by
    set σ := Fintype.equivFin ι
    have h := H _ (f.domDomCongr σ) (v ∘ σ.symm)
    simp only [domDomCongr_apply, update_comp_equiv] at h
    simp only [comp_def, Equiv.symm_apply_apply] at h
    rw [h, Equiv.sum_comp σ.symm fun i ↦ f (update v i b)]
  intro n
  induction n with
  | zero => intro f v; simp [Subsingleton.elim (fun i ↦ v i - b) v]
  | succ n ih =>
    intro f v
    -- Split off the first argument and apply the induction hypothesis to the two curried maps.
    have hb := ih (f.curryLeft b) (Fin.tail v)
    have h0 := ih (f.curryLeft (v 0)) (Fin.tail v)
    simp only [curryLeft_apply_apply] at hb h0
    have hz : ∑ i : Fin n, f (Matrix.vecCons b (update (Fin.tail v) i b)) = 0 :=
      Finset.sum_eq_zero fun i _ ↦
        f.map_eq_zero_of_eq _ (i := 0) (j := i.succ) (by simp) (Fin.succ_ne_zero i).symm
    have hv : (fun i ↦ v i - b) = Matrix.vecCons (v 0 - b) fun i ↦ Fin.tail v i - b := by
      ext i
      cases i using Fin.cases <;> simp [Fin.tail]
    rw [hv, ← curryLeft_apply_apply, map_sub, sub_apply, curryLeft_apply_apply,
      curryLeft_apply_apply, h0, hb, hz, sub_zero, Fin.sum_univ_succ]
    -- `Matrix.vecCons` is `Fin.cons` by definition, so the remaining terms match once `v` is read
    -- as `Fin.cons (v 0) (Fin.tail v)`.
    simp only [Matrix.vecCons, Fin.cons_update, Fin.cons_self_tail]
    rw [← Fin.update_cons_zero (x := v 0), Fin.cons_self_tail]
    abel

/-- An alternating map evaluated on the edge vectors `w i.succ - w 0` of a simplex with vertices
`w 0, …, w n` is the alternating sum of its values on the faces `Fin.removeNth j w`. -/
theorem map_succ_sub_zero {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (w : Fin (n + 1) → M) :
    f (fun i ↦ w i.succ - w 0) = ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) • f (j.removeNth w) := by
  rw [map_sub_const, Fin.sum_univ_succ, Fin.removeNth_zero]
  have h (i : Fin n) : f (update (fun i ↦ w i.succ) i (w 0)) =
      (-1 : R) ^ (i : ℕ) • f (i.succ.removeNth w) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    rw [← Fin.insertNth_removeNth, map_insertNth, ← Int.cast_smul_eq_zsmul R]
    push_cast
    congr 2
    ext k
    cases k using Fin.cases <;> simp [Fin.removeNth, Fin.succ_succAbove_succ]
  simp only [h, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib,
    Fin.val_zero, pow_zero, one_smul]
  exact sub_eq_add_neg _ _

end AlternatingMap
