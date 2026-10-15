/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.GroupTheory.Perm.Basic

/-!
# Norm estimates and interior products of paired wedges

The paired wedge is `ContinuousAlternatingMap.pairedWedge`. This file proves its binomial
operator-norm bound on real seminormed spaces and its interior-product antiderivation rule on
normed spaces, using Mathlib's `ContinuousAlternatingMap.curryLeft`.

The normalization is the signed-permutation sum divided by the two input factorials, so the
interior-product rule has unit constants.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 14.13.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

section Norm

variable {E F₁ F₂ F₃ : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]

private lemma norm_wedgeWithUnalternated_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    ‖ContinuousAlternatingMap.wedgeWithUnalternated mu phi psi v‖ ≤
      ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
  rw [ContinuousAlternatingMap.wedgeWithUnalternated_apply]
  calc
    _ ≤ ‖mu‖ * ‖phi (fun i => v (Fin.castAdd l i))‖ *
        ‖psi (fun j => v (Fin.natAdd k j))‖ := mu.le_opNorm₂ _ _
    _ ≤ ‖mu‖ * (‖phi‖ * ∏ i, ‖v (Fin.castAdd l i)‖) *
        (‖psi‖ * ∏ j, ‖v (Fin.natAdd k j)‖) := by
      gcongr
      · exact phi.le_opNorm _
      · exact psi.le_opNorm _
    _ = ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
      rw [Fin.prod_univ_add]
      ring

private lemma norm_pairedWedge_apply_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    ‖pairedWedge mu mu.continuous₂ phi psi v‖ ≤
      (k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
  rw [pairedWedge_apply, norm_smul]
  have hterm (sigma : Equiv.Perm (Fin (k + l))) :
      ‖Equiv.Perm.sign sigma •
        ContinuousAlternatingMap.wedgeWithUnalternated mu phi psi (v ∘ sigma)‖ ≤
        ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
    simpa [Equiv.Perm.prod_comp sigma Finset.univ (fun i => ‖v i‖) (by simp),
      Function.comp_def] using norm_wedgeWithUnalternated_le mu phi psi (v ∘ sigma)
  simp only [ContinuousAlternatingMap.wedgeWithUnalternated_apply, Function.comp_apply] at hterm
  calc
    _ ≤ ‖(((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹)‖ *
        ∑ _sigma : Equiv.Perm (Fin (k + l)),
          (‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun sigma _ => hterm sigma)
    _ = (k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      norm_num only [nsmul_eq_mul, norm_inv, norm_mul, Real.norm_natCast]
      have hfac : ((k.factorial : ℝ) * (l.factorial : ℝ)) ≠ 0 := by positivity
      field_simp [hfac]
      have hchoose : ((k + l).choose k : ℝ) * k.factorial * l.factorial =
          (k + l).factorial := by
        have h := Nat.add_choose_mul_factorial_mul_factorial l k
        norm_cast
        simpa [Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using h
      rw [← hchoose]
      ring

/-- The norm of the paired wedge is bounded by the number of `(k, l)`-shuffles times the norms of
the pairing and the two forms. -/
theorem norm_pairedWedge_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    ‖pairedWedge mu mu.continuous₂ phi psi‖ ≤ (k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖ := by
  exact (pairedWedge mu mu.continuous₂ phi psi).opNorm_le_bound (by positivity)
    (norm_pairedWedge_apply_le mu phi psi)

end Norm

section InteriorProduct

open Equiv

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ}

variable [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂] in
/-- In the interior-product expansion, inserting `v` into the `i`-th slot of `phi` contributes
the signed sum with `phi.curryLeft v`. -/
private lemma sum_sign_smul_insertNth_castAdd (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (k + 1)) :
    (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      ∑ sigma : Perm (Fin (k + (l + 1))), Perm.sign sigma •
        mu (phi.curryLeft v fun a =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.castAdd (l + 1) a)))
          (psi fun b =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.natAdd k b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    simp [← mul_pow]
  -- Locate the entries of the inserted tuple, then move `v` to the front of the block of `phi`.
  simp_rw [Fin.insertNth_castAdd_comp_castAdd, Fin.insertNth_castAdd_apply_natAdd,
    ContinuousAlternatingMap.map_insertNth, ← ContinuousAlternatingMap.curryLeft_apply_apply]
  -- Collect the two signs in front of the sum, where they cancel.
  simp only [map_zsmul, FunLike.coe_smul, Pi.smul_apply, smul_comm (Perm.sign _),
    ← Finset.smul_sum, smul_smul, hsign, one_smul]
  symm
  refine Fintype.sum_equiv (finCongr (show k + (l + 1) = k + 1 + l by omega)).permCongr _ _
    fun sigma => ?_
  simp [Perm.sign_permCongr]

variable [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] in
/-- In the interior-product expansion, inserting `v` into the `i`-th slot of `psi` contributes
`(-1) ^ (k + 1)` times the signed sum with `psi.curryLeft v`. -/
private lemma sum_sign_smul_insertNth_natAdd (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (l + 1)) :
    (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      (-1 : ℤ) ^ (k + 1) • ∑ sigma : Perm (Fin (k + 1 + l)), Perm.sign sigma •
        mu (phi fun a => w (sigma (Fin.castAdd l a)))
          (psi.curryLeft v fun b => w (sigma (Fin.natAdd (k + 1) b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) * (-1) ^ (i : ℕ) = (-1) ^ (k + 1) := by
    simp [pow_add, mul_assoc, ← mul_pow]
  -- Locate the entries of the inserted tuple, then move `v` to the front of the block of `psi`.
  simp_rw [Fin.insertNth_natAdd_apply_castAdd, Fin.insertNth_natAdd_comp_natAdd,
    ContinuousAlternatingMap.map_insertNth, ← ContinuousAlternatingMap.curryLeft_apply_apply]
  -- Collect the two signs in front of the sum, where they combine to `(-1) ^ (k + 1)`.
  simp only [map_zsmul, smul_comm (Perm.sign _), ← Finset.smul_sum, smul_smul, hsign,
    Function.comp_apply]

variable [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- The interior product is an antiderivation of degree `-1` for the paired wedge:
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (k + 1) φ ∧ ι_v ψ` for a `(k + 1)`-form `φ`, where the interior
product `ι_v` is `ContinuousAlternatingMap.curryLeft`. The degree `k + (l + 1)` of the first term
is identified with `k + 1 + l` by `Fin.cast`. The coefficient spaces are normed because Mathlib's
`curryLeft` requires a normed target, both for the input forms and for their paired wedge. -/
theorem curryLeft_pairedWedge (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) :
    (pairedWedge mu mu.continuous₂ phi psi).curryLeft v w =
      pairedWedge mu mu.continuous₂ (phi.curryLeft v) psi (w ∘ Fin.cast (show k + (l + 1) = k + 1
    + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • pairedWedge mu mu.continuous₂ phi (psi.curryLeft v) w := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, pairedWedge_apply, pairedWedge_apply,
    pairedWedge_apply, Matrix.vecCons]
  -- Expand the signed sum along the slot that receives `v`; the summand is the function
  -- `y ↦ mu (phi (y ∘ castAdd)) (psi (y ∘ natAdd))` evaluated at `Fin.cons v w ∘ sigma`.
  have hexp : (∑ sigma : Perm (Fin (k + 1 + (l + 1))), Perm.sign sigma •
      mu (phi fun i => Fin.cons (α := fun _ => E) v w (sigma (Fin.castAdd (l + 1) i)))
        (psi fun j => Fin.cons (α := fun _ => E) v w (sigma (Fin.natAdd (k + 1) j)))) = _ :=
    sum_sign_smul_cons_comp_eq_sum_insertNth
      (fun y : Fin (k + 1 + l + 1) → E =>
        mu (phi fun i => y (Fin.castAdd (l + 1) i)) (psi fun j => y (Fin.natAdd (k + 1) j))) v w
  -- The slot of `v` ranges over `Fin (k + 1 + l + 1)`, which is `Fin ((k + 1) + (l + 1))`;
  -- split it into the block of `phi` and the block of `psi`.
  have hsplit (f : Fin (k + 1 + l + 1) → F₃) :
      ∑ j, f j = ∑ i : Fin (k + 1), f (Fin.castAdd (l + 1) i) +
        ∑ i : Fin (l + 1), f (Fin.natAdd (k + 1) i) :=
    Fin.sum_univ_add (a := k + 1) (b := l + 1) f
  rw [hexp, hsplit]
  simp only [sum_sign_smul_insertNth_castAdd, sum_sign_smul_insertNth_natAdd, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.factorial_succ k, Nat.factorial_succ l]
  match_scalars <;> field_simp

end InteriorProduct

end ContinuousAlternatingMap

end
