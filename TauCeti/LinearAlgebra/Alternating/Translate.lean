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

A vector `w` whose interior product with an alternating map `f` vanishes, `f.curryLeft w = 0`,
lies in the kernel of `f` in every argument: `f` vanishes as soon as `w` is one of its arguments
(`AlternatingMap.map_update_eq_zero_of_curryLeft_eq_zero`), so adding independent multiples of `w`
to the arguments does not change the value
(`AlternatingMap.map_add_smul_of_curryLeft_eq_zero`). For a differential form whose contraction with
a vector field vanishes, this says that its values only depend on tangent vectors modulo that
field.
-/

public section

open Function

namespace AlternatingMap

section Ring

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

end Ring

section Semiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- If the interior product of `f` with `w` vanishes, then `f` vanishes whenever one of its
arguments is `w`. -/
theorem map_update_eq_zero_of_curryLeft_eq_zero {n : ℕ} {f : M [⋀^Fin (n + 1)]→ₗ[R] N} {w : M}
    (hw : f.curryLeft w = 0) (v : Fin (n + 1) → M) (i : Fin (n + 1)) : f (update v i w) = 0 := by
  -- With `w` in the first argument, this is the hypothesis.
  have h₀ (u : Fin (n + 1) → M) : f (update u 0 w) = 0 := by
    have h := congrArg (fun g : M [⋀^Fin n]→ₗ[R] N ↦ g (Fin.tail u)) hw
    simp only [curryLeft_apply_apply, zero_apply] at h
    -- `Matrix.vecCons` is `Fin.cons` by definition.
    rwa [← Fin.cons_self_tail (update u 0 w), update_self, Fin.tail_update_zero]
  rcases eq_or_ne i 0 with rfl | hi
  · exact h₀ v
  -- Otherwise swapping the arguments `0` and `i` moves `w` to the first argument.
  have h := f.map_swap_add (update v i w) hi.symm
  rwa [update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right, h₀, zero_add] at h

/-- If the interior product of `f` with `w` vanishes, then adding multiples of `w` to the
arguments of `f` does not change its value. -/
theorem map_add_smul_of_curryLeft_eq_zero {n : ℕ} {f : M [⋀^Fin (n + 1)]→ₗ[R] N} {w : M}
    (hw : f.curryLeft w = 0) (v : Fin (n + 1) → M) (c : Fin (n + 1) → R) :
    f (fun i ↦ v i + c i • w) = f v := by
  classical
  -- Expand multilinearly: every term with some argument `c i • w` vanishes.
  have h := f.toMultilinearMap.map_add_univ v fun i ↦ c i • w
  simp only [coe_multilinearMap, Pi.add_def] at h
  rw [h, Finset.sum_eq_single Finset.univ]
  · simp
  · intro s _ hs
    obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
      by_contra! h
      exact hs (Finset.eq_univ_of_forall h)
    have hu : s.piecewise v (fun i ↦ c i • w) =
        update (s.piecewise v fun i ↦ c i • w) i (c i • w) := by
      rw [eq_comm, update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
    rw [hu, f.map_update_smul, map_update_eq_zero_of_curryLeft_eq_zero hw, smul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ _) h

end Semiring

end AlternatingMap
