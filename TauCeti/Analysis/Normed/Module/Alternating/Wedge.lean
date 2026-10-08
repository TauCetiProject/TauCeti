/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import TauCeti.Data.Fin.Basic

/-!
# Wedge products of continuous alternating maps

This file defines the paired wedge product of continuous alternating maps. Given a continuous
bilinear pairing `μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃`, it combines a `k`-form with values in `F₁`
and an `l`-form with values in `F₂` into a `(k + l)`-form with values in `F₃`.

The normalization is the determinant convention: the signed sum over all permutations is divided
by `k! l!`. Equivalently, this is the unscaled sum over `(k, l)`-shuffles. In particular, the wedge
of two one-forms is the usual two-term determinant rather than half of it. The construction starts
with Mathlib's `AlternatingMap.domCoprod`, transports its domain along `finSumFinEquiv`, and
postcomposes with the pairing.

The paired construction follows the design of Yury Kudryashov's
[`DeRhamCohomology`](https://github.com/urkud/DeRhamCohomology) project.

## Main declarations

* `TauCeti.wedgeWith`: the paired wedge product.
* `TauCeti.wedgeWith_toAlternatingMap`: its characterization by alternatization.
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

/-- The unalternated multilinear pairing underlying `wedgeWith`. -/
noncomputable def wedgeWithUnalternated {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  (pairingLinear mu).compMultilinearMap <|
    (MultilinearMap.domCoprod phi.toAlternatingMap.toMultilinearMap
      psi.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv

/-- The unalternated pairing evaluates `phi` on the first `k` vectors and `psi` on the last `l`. -/
@[simp]
theorem wedgeWithUnalternated_apply {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternated mu phi psi v =
      mu (phi (fun i => v (Fin.castAdd l i))) (psi (fun j => v (Fin.natAdd k j))) := by
  simp [wedgeWithUnalternated, pairingLinear]

private noncomputable def wedgeAlternating {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→ₗ[ℝ] F₃ :=
  (pairingLinear mu).compAlternatingMap <|
    (phi.toAlternatingMap.domCoprod psi.toAlternatingMap).domDomCongr finSumFinEquiv

private lemma wedgeAlternating_eq_alternatization {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeAlternating mu phi psi =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        (wedgeWithUnalternated mu phi psi).alternatization := by
  have htransport :
      MultilinearMap.alternatization
          ((MultilinearMap.domCoprod phi.toAlternatingMap.toMultilinearMap
            psi.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv) =
        (MultilinearMap.alternatization
          (MultilinearMap.domCoprod phi.toAlternatingMap.toMultilinearMap
            psi.toAlternatingMap.toMultilinearMap)).domDomCongr finSumFinEquiv := by
    apply AlternatingMap.ext
    intro v
    simp only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      AlternatingMap.domDomCongr_apply]
    symm
    exact Fintype.sum_equiv finSumFinEquiv.permCongr _ _ fun sigma => by
      simp
  unfold wedgeAlternating wedgeWithUnalternated
  rw [LinearMap.compMultilinearMap_alternatization,
    htransport,
    MultilinearMap.domCoprod_alternatization_eq]
  simp only [Fintype.card_fin, LinearMap.compAlternatingMap_smul,
    AlternatingMap.domDomCongr_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_mul]
  rw [inv_smul_smul₀ (by positivity)]

private lemma wedgeAlternating_apply {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeAlternating mu phi psi v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
          mu (phi (fun i => v (sigma (Fin.castAdd l i))))
            (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
  rw [wedgeAlternating_eq_alternatization]
  simp [MultilinearMap.alternatization_apply, wedgeWithUnalternated_apply]

private lemma norm_wedgeWithUnalternated_le {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    ‖wedgeWithUnalternated mu phi psi v‖ ≤ ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
  rw [wedgeWithUnalternated_apply]
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
  rw [wedgeAlternating_eq_alternatization, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply,
    norm_smul]
  have hterm (sigma : Equiv.Perm (Fin (k + l))) :
      ‖Equiv.Perm.sign sigma • wedgeWithUnalternated mu phi psi (v ∘ sigma)‖ ≤
        ‖mu‖ * ‖phi‖ * ‖psi‖ * ∏ i, ‖v i‖ := by
    simpa [Equiv.Perm.prod_comp sigma Finset.univ (fun i => ‖v i‖) (by simp),
      Function.comp_def] using norm_wedgeWithUnalternated_le mu phi psi (v ∘ sigma)
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
  classical
  rw [wedgeAlternating_apply]
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_fin_two_eq_one_or_swap e
  rw [hperm, Finset.sum_insert (by decide), Finset.sum_singleton,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [Fin.fin_one_eq_zero, Matrix.cons_fin_one, sub_eq_add_neg]

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
            (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
  simp only [wedgeWith, AlternatingMap.coe_mkContinuous]
  exact wedgeAlternating_apply mu phi psi v

/-- The underlying alternating map of the paired wedge is the alternatization of its unalternated
multilinear pairing, divided by `k! l!`. -/
theorem wedgeWith_toAlternatingMap {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    (wedgeWith mu phi psi).toAlternatingMap =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        (wedgeWithUnalternated mu phi psi).alternatization := by
  simp only [wedgeWith]
  exact wedgeAlternating_eq_alternatization mu phi psi

/-- On two one-forms, the paired wedge is the usual two-term determinant, with no factor `1 / 2`. -/
theorem wedgeWith_apply_one_one (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin 1]→L[ℝ] F₁) (psi : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    wedgeWith mu phi psi ![v, w] =
      mu (phi ![v]) (psi ![w]) - mu (phi ![w]) (psi ![v]) := by
  simp only [wedgeWith, AlternatingMap.coe_mkContinuous]
  exact wedgeAlternating_apply_one_one mu phi psi v w

/-- Postcomposing the pairing postcomposes the paired wedge. -/
@[simp]
theorem wedgeWith_postcomp {F₄ : Type*} [NormedAddCommGroup F₄] [NormedSpace ℝ F₄]
    {k l : ℕ} (nu : F₃ →L[ℝ] F₄) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith ((ContinuousLinearMap.compL ℝ F₂ F₃ F₄ nu).comp mu) phi psi =
      nu.compContinuousAlternatingMap (wedgeWith mu phi psi) := by
  ext v
  simp only [wedgeWith_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply, map_smul, map_sum]
  congr 2
  funext sigma
  exact (nu.map_smul_of_tower (Equiv.Perm.sign sigma) _).symm

/-- The paired wedge is additive in the pairing. -/
@[simp]
theorem wedgeWith_add_pairing {k l : ℕ} (mu nu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith (mu + nu) phi psi = wedgeWith mu phi psi + wedgeWith nu phi psi := by
  ext v
  simp only [wedgeWith_apply, add_apply, ContinuousAlternatingMap.add_apply, Finset.smul_sum,
    smul_add]
  rw [Finset.sum_add_distrib]

/-- The paired wedge respects scalar multiplication of the pairing. -/
@[simp]
theorem wedgeWith_smul_pairing {k l : ℕ} (c : ℝ) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith (c • mu) phi psi = c • wedgeWith mu phi psi := by
  ext v
  simp only [wedgeWith_apply, ContinuousAlternatingMap.smul_apply,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [smul_apply, smul_apply, smul_comm (Equiv.Perm.sign sigma) c]
  simp only [smul_smul]
  ring_nf

/-- The paired wedge for the zero pairing is zero. -/
@[simp]
theorem wedgeWith_zero_pairing {k l : ℕ} (phi : E [⋀^Fin k]→L[ℝ] F₁)
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWith (0 : F₁ →L[ℝ] F₂ →L[ℝ] F₃) phi psi = 0 := by
  ext v
  simp only [wedgeWith_apply, zero_apply, smul_zero, Finset.sum_const_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The paired wedge is additive in its first form. -/
@[simp]
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
@[simp]
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
@[simp]
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
@[simp]
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
  unfold wedgeWith
  apply AlternatingMap.mkContinuous_norm_le
  positivity

/-- Pulling both arguments of a paired wedge back by a continuous linear map is the same as pulling
back their wedge. -/
@[simp]
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
