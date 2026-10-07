/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# Wedge products of continuous alternating maps

This file defines the paired wedge product of continuous alternating maps. Given a continuous
bilinear pairing `μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃`, it combines a `k`-form with values in `F₁`
and an `l`-form with values in `F₂` into a `(k + l)`-form with values in `F₃`.

The normalization is the determinant convention: the signed sum over all permutations is divided
by `k! l!`. Equivalently, this is the unscaled sum over `(k, l)`-shuffles. In particular, the wedge
of two one-forms is the usual two-term determinant rather than half of it. The construction starts
with Mathlib's `MultilinearMap.domCoprod`, composes with the pairing, and then applies
`MultilinearMap.alternatization`.

The paired construction follows the design of Yury Kudryashov's
[`DeRhamCohomology`](https://github.com/urkud/DeRhamCohomology) project.

## Main declarations

* `TauCeti.wedgeWith`: the paired wedge product.
* `TauCeti.wedgeWith_apply`: the signed-permutation formula in every degree.
* `TauCeti.norm_wedgeWith_le`: the sharp binomial norm bound.
* `TauCeti.wedgeWith_compContinuousLinearMap`: compatibility with pullback by a continuous linear
  map.
-/

public section

open TensorProduct

namespace TauCeti

section

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

private noncomputable def pairingLinear (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    F₁ ⊗[ℝ] F₂ →ₗ[ℝ] F₃ :=
  TensorProduct.lift
    { toFun := fun x => (mu x).toLinearMap
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }

@[simp]
private lemma pairingLinear_tmul (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (x : F₁) (y : F₂) :
    pairingLinear mu (x ⊗ₜ[ℝ] y) = mu x y :=
  rfl

private noncomputable def wedgeUnalternated {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  (pairingLinear mu).compMultilinearMap <|
    (MultilinearMap.domCoprod phi.toContinuousMultilinearMap.toMultilinearMap
      psi.toContinuousMultilinearMap.toMultilinearMap).domDomCongr finSumFinEquiv

private lemma wedgeUnalternated_apply {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeUnalternated mu phi psi v =
      mu (phi (fun i => v (Fin.castAdd l i))) (psi (fun j => v (Fin.natAdd k j))) := by
  simp [wedgeUnalternated, pairingLinear]

private noncomputable def wedgeAlternating {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→ₗ[ℝ] F₃ :=
  (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
    (wedgeUnalternated mu phi psi).alternatization

private lemma wedgeAlternating_apply {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeAlternating mu phi psi v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
          mu (phi (fun i => v (sigma (Fin.castAdd l i))))
            (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
  simp [wedgeAlternating, MultilinearMap.alternatization_apply, wedgeUnalternated_apply]

private lemma norm_wedgeUnalternated_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    ‖wedgeUnalternated mu phi psi v‖ ≤ ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
  rw [wedgeUnalternated_apply]
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

private lemma norm_wedgeAlternating_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    ‖wedgeAlternating mu phi psi v‖ ≤
      (k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
  rw [wedgeAlternating, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    norm_smul]
  have hterm (sigma : Equiv.Perm (Fin (k + l))) :
      ‖Equiv.Perm.sign sigma • wedgeUnalternated mu phi psi (v ∘ sigma)‖ ≤
        ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
    simpa [Equiv.Perm.prod_comp sigma Finset.univ (fun i => ‖v i‖) (by simp),
      Function.comp_def] using norm_wedgeUnalternated_le mu phi psi (v ∘ sigma)
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

private lemma wedgeAlternating_apply_one_one (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin 1]→L[ℝ] F₁) (psi : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    wedgeAlternating mu phi psi ![v, w] =
      mu (phi ![v]) (psi ![w]) - mu (phi ![w]) (psi ![v]) := by
  rw [wedgeAlternating_apply]
  simp only [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, inv_one, Nat.succ_eq_add_one, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Equiv.Perm.default_eq,
    Function.Embedding.coeFn_mk, Equiv.Perm.decomposeFin.symm_sign, ↓reduceIte, ite_mul, one_mul,
    neg_mul, mul_ite, mul_neg, Fin.natAdd_eq_addNat, Fin.addNat_one,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, ite_smul, Units.neg_smul,
    Finset.sum_ite_irrel, Finset.sum_singleton, Equiv.Perm.sign_one,
    Equiv.Perm.decomposeFin_symm_of_one, one_smul, Finset.sum_neg_distrib,
    Equiv.Perm.decomposeFin_symm_of_refl, one_ne_zero, neg_neg, smul_add, smul_neg]
  have h₀ : (fun i : Fin 1 => ![v, w] (Fin.castAdd 1 i)) = ![v] := by
    funext i
    fin_cases i
    rfl
  have h₁ : (fun _j : Fin 1 => w) = ![w] := by
    funext j
    fin_cases j
    rfl
  have h₂ : (fun i : Fin 1 => ![v, w] ((Equiv.swap 0 1) (Fin.castAdd 1 i))) = ![w] := by
    funext i
    fin_cases i
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.reduceCastAdd,
      Equiv.swap_apply_left, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h₃ : (fun j : Fin 1 => ![v, w] ((Equiv.swap 0 1) j.succ)) = ![v] := by
    funext j
    fin_cases j
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
      Fin.succ_zero_eq_one, Equiv.swap_apply_right, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one]
  rw [h₀, h₁, h₂, h₃, sub_eq_add_neg]

/-- The paired wedge product of continuous alternating maps, normalized as the signed sum over all
permutations divided by `k! l!`. Equivalently, it is the unscaled sum over `(k, l)`-shuffles. -/
noncomputable def wedgeWith {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→L[ℝ] F₃ :=
  (wedgeAlternating mu phi psi).mkContinuous
    ((k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖) (norm_wedgeAlternating_le mu phi psi)

/-- The paired wedge is the signed permutation sum divided by `k! l!`. -/
theorem wedgeWith_apply {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWith mu phi psi v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
          mu (phi (fun i => v (sigma (Fin.castAdd l i))))
            (psi (fun j => v (sigma (Fin.natAdd k j)))) :=
  wedgeAlternating_apply mu phi psi v

/-- On two one-forms, the paired wedge is the usual two-term determinant, with no factor `1 / 2`. -/
theorem wedgeWith_apply_one_one (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin 1]→L[ℝ] F₁) (psi : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    wedgeWith mu phi psi ![v, w] =
      mu (phi ![v]) (psi ![w]) - mu (phi ![w]) (psi ![v]) :=
  wedgeAlternating_apply_one_one mu phi psi v w

/-- The paired wedge is additive in its first form. -/
theorem wedgeWith_add_left {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi phi' : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu (phi + phi') psi = wedgeWith mu phi psi + wedgeWith mu phi' psi := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.add_apply, map_add, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sigma _
  simp only [add_apply, smul_add]

/-- The paired wedge is additive in its second form. -/
theorem wedgeWith_add_right {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi psi' : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu phi (psi + psi') = wedgeWith mu phi psi + wedgeWith mu phi psi' := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.add_apply, map_add, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sigma _
  simp only [smul_add]

/-- The paired wedge respects scalar multiplication in its first form. -/
theorem wedgeWith_smul_left {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (c : ℝ)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu (c • phi) psi = c • wedgeWith mu phi psi := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.smul_apply, map_smul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [smul_apply, smul_comm (Equiv.Perm.sign sigma) c]
  simp only [smul_smul]
  ring_nf

/-- The paired wedge respects scalar multiplication in its second form. -/
theorem wedgeWith_smul_right {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (c : ℝ)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu phi (c • psi) = c • wedgeWith mu phi psi := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.smul_apply, map_smul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [smul_comm (Equiv.Perm.sign sigma) c]
  simp only [smul_smul]
  ring_nf

/-- Wedge with the zero form on the left is zero. -/
@[simp]
theorem wedgeWith_zero_left {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu (0 : E [⋀^Fin k]→L[ℝ] F₁) psi = 0 := by
  simpa only [zero_smul] using
    wedgeWith_smul_left mu (0 : ℝ) (0 : E [⋀^Fin k]→L[ℝ] F₁) psi

/-- Wedge with the zero form on the right is zero. -/
@[simp]
theorem wedgeWith_zero_right {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) :
    wedgeWith mu phi (0 : E [⋀^Fin l]→L[ℝ] F₂) = 0 := by
  simpa only [zero_smul] using
    wedgeWith_smul_right mu (0 : ℝ) phi (0 : E [⋀^Fin l]→L[ℝ] F₂)

/-- The norm of the paired wedge is bounded by the number of `(k, l)`-shuffles times the norms of
the pairing and the two forms. -/
theorem norm_wedgeWith_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    ‖wedgeWith mu phi psi‖ ≤ (k + l).choose k * ‖mu‖ * ‖phi‖ * ‖psi‖ := by
  apply AlternatingMap.mkContinuous_norm_le
  positivity

/-- Pulling both arguments of a paired wedge back by a continuous linear map is the same as pulling
back their wedge. -/
theorem wedgeWith_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (f : E' →L[ℝ] E)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith mu (phi.compContinuousLinearMap f) (psi.compContinuousLinearMap f) =
      (wedgeWith mu phi psi).compContinuousLinearMap f := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def]

end

end TauCeti

end
