/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import TauCeti.Data.Fin.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Inversion

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
* `TauCeti.wedgeWith_flip`: swapping the two forms flips the pairing and costs the sign
  `(-1) ^ (k * l)`; `TauCeti.wedgeWith_comm` is graded commutativity for a symmetric pairing.
* `TauCeti.wedgeWith_wedgeWith_left_apply`, `TauCeti.wedgeWith_wedgeWith_right_apply`: an iterated
  paired wedge as a single signed sum over all permutations, divided by `k! l! m!`.
* `TauCeti.wedgeWith_assoc`: associativity, for pairings whose two composites agree.
* `TauCeti.curryLeft_wedgeWith`: the interior product `ContinuousAlternatingMap.curryLeft` is an
  antiderivation of degree `-1` for the paired wedge.

Associativity and graded commutativity are not identities of the paired wedge in general: in degree
zero they reduce to associativity and commutativity of the pairing. They are proved here under
exactly those hypotheses on the pairings, which hold for the multiplication of a normed algebra
(graded commutativity only when it is commutative) but not for a Lie bracket in general.

The interior product of a vector `v` with a form is Mathlib's `ContinuousAlternatingMap.curryLeft`,
which inserts `v` as the first argument; `ι_v ∘ ι_v = 0` is Mathlib's
`ContinuousAlternatingMap.curryLeft_same`. The antiderivation rule
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (k + 1) φ ∧ ι_v ψ` for a `(k + 1)`-form `φ` holds for every
pairing, with the normalization of this file and no extra constant.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 14.13.
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

/-- The flip identity: swapping the two forms of a paired wedge flips the pairing and costs the
graded sign `(-1) ^ (k * l)`. This holds for every pairing. -/
theorem wedgeWith_flip {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (v : Fin (k + l) → E) :
    wedgeWith mu phi psi v =
      (-1 : ℝ) ^ (k * l) • wedgeWith mu.flip psi phi (v ∘ Fin.cast (Nat.add_comm l k)) := by
  -- Reindex the permutation sum on the right by composing with the block swap `B`, which
  -- exchanges the first `k` and the last `l` indices and has sign `(-1) ^ (k * l)`.
  set c : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  set B : Equiv.Perm (Fin (k + l)) := finAddFlip.trans c
  have hsum : ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
        mu.flip (psi (fun i => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.castAdd k i))))
          (phi (fun j => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.natAdd l j)))) =
      Equiv.Perm.sign B • ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
        mu (phi (fun i => v (sigma (Fin.castAdd l i))))
          (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (c.permCongr.trans (Equiv.mulRight B)) _ _ fun tau => ?_
    have hsign : Equiv.Perm.sign tau =
        Equiv.Perm.sign B * Equiv.Perm.sign (c.permCongr tau * B) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_permCongr, mul_comm, mul_assoc, ← sq]
      simp [Int.units_sq]
    have hleft : (fun i => v ((c.permCongr tau * B) (Fin.castAdd l i))) =
        fun j => v (Fin.cast (Nat.add_comm l k) (tau (Fin.natAdd l j))) := by
      funext i
      simp [B, c, finAddFlip_apply_castAdd]
    have hright : (fun j => v ((c.permCongr tau * B) (Fin.natAdd k j))) =
        fun i => v (Fin.cast (Nat.add_comm l k) (tau (Fin.castAdd k i))) := by
      funext j
      simp [B, c, finAddFlip_apply_natAdd]
    simp only [Equiv.trans_apply, Equiv.coe_mulRight, Function.comp_apply, hsign, mul_smul,
      ContinuousLinearMap.flip_apply]
    rw [hleft, hright]
  rw [wedgeWith_apply, wedgeWith_apply, hsum, sign_finAddFlip_trans_finCongr]
  generalize (∑ sigma : Equiv.Perm (Fin (k + l)), (_ : F₃)) = S
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  match_scalars
  ring_nf
  simp

/-- Graded commutativity of the paired wedge along a symmetric pairing. -/
theorem wedgeWith_comm {k l : ℕ} {mu : F₁ →L[ℝ] F₁ →L[ℝ] F₃} (hmu : ∀ a b, mu a b = mu b a)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₁) (v : Fin (k + l) → E) :
    wedgeWith mu phi psi v =
      (-1 : ℝ) ^ (k * l) • wedgeWith mu psi phi (v ∘ Fin.cast (Nat.add_comm l k)) := by
  have hflip : mu.flip = mu := by
    ext a b
    exact hmu b a
  rw [wedgeWith_flip, hflip]

end

section Assoc

open Equiv

variable {E F₁ F₂ F₃ F₁₂ F₂₃ G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [NormedAddCommGroup F₁₂] [NormedSpace ℝ F₁₂]
  [NormedAddCommGroup F₂₃] [NormedSpace ℝ F₂₃] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k l m : ℕ}

/-- A paired wedge whose left factor is itself a paired wedge is the signed sum over all
permutations of `k + l + m` slots, divided by `k! l! m!`. -/
theorem wedgeWith_wedgeWith_left_apply (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂)
    (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G) (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + l + m) → E) :
    wedgeWith mu₁₂₃ (wedgeWith mu₁₂ phi psi) chi v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + l + m)), Perm.sign sigma •
          mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
              (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
            (chi fun r => v (sigma (Fin.natAdd (k + l) r))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr tau (1 : Perm (Fin m))))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + l + m)) =>
      mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
          (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
        (chi fun r => v (sigma (Fin.natAdd (k + l) r))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [wedgeWith_apply, map_smul, map_sum, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    Units.smul_def, map_zsmul] at key ⊢
  simp_rw [smul_comm _ ((k.factorial : ℝ) * l.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((k + l).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- A paired wedge whose right factor is itself a paired wedge is the signed sum over all
permutations of `k + (l + m)` slots, divided by `k! l! m!`. -/
theorem wedgeWith_wedgeWith_right_apply (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃)
    (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G) (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + (l + m)) → E) :
    wedgeWith mu₁₂₃' phi (wedgeWith mu₂₃ psi chi) v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + (l + m))), Perm.sign sigma •
          mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
            (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
              (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr (1 : Perm (Fin k)) tau))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + (l + m))) =>
      mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
        (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
          (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [wedgeWith_apply, map_smul, map_sum, Units.smul_def, map_zsmul] at key ⊢
  simp_rw [smul_comm _ ((l.factorial : ℝ) * m.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((l + m).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Associativity of the paired wedge, for pairings whose two composites agree:
`mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c)`. For the multiplication of a normed algebra this
hypothesis is `mul_assoc`; for a Lie bracket it does not hold in general. -/
theorem wedgeWith_assoc (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h : ∀ a b c, mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (chi : E [⋀^Fin m]→L[ℝ] F₃)
    (v : Fin (k + l + m) → E) :
    wedgeWith mu₁₂₃ (wedgeWith mu₁₂ phi psi) chi v =
      wedgeWith mu₁₂₃' phi (wedgeWith mu₂₃ psi chi) (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [wedgeWith_wedgeWith_left_apply, wedgeWith_wedgeWith_right_apply]
  congr 1
  refine Fintype.sum_equiv (finCongr (Nat.add_assoc k l m)).permCongr _ _ fun sigma => ?_
  have h₁ (i : Fin k) : Fin.cast (Nat.add_assoc k l m).symm (Fin.castAdd (l + m) i) =
      Fin.castAdd m (Fin.castAdd l i) := Fin.ext rfl
  have h₂ (j : Fin l) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.castAdd m j)) =
      Fin.castAdd m (Fin.natAdd k j) := Fin.ext rfl
  have h₃ (r : Fin m) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.natAdd l r)) =
      Fin.natAdd (k + l) r := Fin.ext (Nat.add_assoc k l r).symm
  simp [h, h₁, h₂, h₃, Perm.sign_permCongr]

end Assoc

section InteriorProduct

open Equiv

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {α : Type*} {k l : ℕ}

/-! The next four lemmas locate the entries of `j.insertNth x y` in the two blocks of
`Fin ((k + 1) + (l + 1))`, according to whether the inserted slot `j` lies in the first block or
the second. -/

private lemma insertNth_castAdd_comp_castAdd (i : Fin (k + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) :
    (fun a : Fin (k + 1) => Fin.insertNth (α := fun _ => α)
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) x y (Fin.castAdd (l + 1) a)) =
      Fin.insertNth (α := fun _ => α) i x
        (fun b : Fin k => y (Fin.cast (show k + (l + 1) = k + 1 + l by omega)
          (Fin.castAdd (l + 1) b))) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨Fin.insertNth_apply_same _ _ _, funext fun b => ?_⟩
  have : (Fin.castAdd (l + 1) (i.succAbove b) : Fin (k + 1 + l + 1)) =
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)).succAbove
        (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.castAdd (l + 1) b)) := by
    ext
    simp only [Fin.val_castAdd, Fin.val_succAbove, Fin.val_cast]
  simp only [Fin.removeNth, this, Fin.insertNth_apply_succAbove]

private lemma insertNth_castAdd_apply_natAdd (i : Fin (k + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) (b : Fin (l + 1)) :
    Fin.insertNth (α := fun _ => α) (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) x y
      (Fin.natAdd (k + 1) b) =
      y (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.natAdd k b)) := by
  have : (Fin.natAdd (k + 1) b : Fin (k + 1 + l + 1)) =
      (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)).succAbove
        (Fin.cast (show k + (l + 1) = k + 1 + l by omega) (Fin.natAdd k b)) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_succAbove, Fin.val_cast]
    split_ifs <;> omega
  rw [this, Fin.insertNth_apply_succAbove]

private lemma insertNth_natAdd_apply_castAdd (i : Fin (l + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) (a : Fin (k + 1)) :
    Fin.insertNth (α := fun _ => α) (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) x y
      (Fin.castAdd (l + 1) a) = y (Fin.castAdd l a) := by
  have : (Fin.castAdd (l + 1) a : Fin (k + 1 + l + 1)) =
      (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)).succAbove (Fin.castAdd l a) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_succAbove]
    split_ifs <;> omega
  rw [this, Fin.insertNth_apply_succAbove]

private lemma insertNth_natAdd_comp_natAdd (i : Fin (l + 1)) (x : α)
    (y : Fin (k + 1 + l) → α) :
    (fun b : Fin (l + 1) => Fin.insertNth (α := fun _ => α)
      (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) x y (Fin.natAdd (k + 1) b)) =
      Fin.insertNth (α := fun _ => α) i x (fun c : Fin l => y (Fin.natAdd (k + 1) c)) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨Fin.insertNth_apply_same _ _ _, funext fun c => ?_⟩
  have : (Fin.natAdd (k + 1) (i.succAbove c) : Fin (k + 1 + l + 1)) =
      (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)).succAbove (Fin.natAdd (k + 1) c) := by
    ext
    simp only [Fin.val_natAdd, Fin.val_succAbove]
    split_ifs <;> omega
  simp only [Fin.removeNth, this, Fin.insertNth_apply_succAbove]

/-- The terms of the expansion of `(wedgeWith mu phi psi).curryLeft v` in which `v` lands in the
`i`-th slot of `phi`: each such slot contributes the signed sum of `wedgeWith mu (phi.curryLeft v)
psi`. -/
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
  simp_rw [insertNth_castAdd_comp_castAdd, insertNth_castAdd_apply_natAdd,
    ContinuousAlternatingMap.map_insertNth, ← ContinuousAlternatingMap.curryLeft_apply_apply,
    map_zsmul, FunLike.coe_smul, Pi.smul_apply, smul_comm (Perm.sign _),
    ← Finset.smul_sum, smul_smul, Fin.val_castAdd, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_smul]
  symm
  refine Fintype.sum_equiv (finCongr (show k + (l + 1) = k + 1 + l by omega)).permCongr _ _
    fun sigma => ?_
  simp [Perm.sign_permCongr]

/-- The terms of the expansion of `(wedgeWith mu phi psi).curryLeft v` in which `v` lands in the
`i`-th slot of `psi`: each such slot contributes `(-1) ^ (k + 1)` times the signed sum of
`wedgeWith mu phi (psi.curryLeft v)`. -/
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
  have hsign : (-1 : ℤ) ^ (k + 1 + (i : ℕ)) * (-1) ^ (i : ℕ) = (-1) ^ (k + 1) := by
    rw [pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
  simp_rw [insertNth_natAdd_apply_castAdd, insertNth_natAdd_comp_natAdd,
    ContinuousAlternatingMap.map_insertNth, ← ContinuousAlternatingMap.curryLeft_apply_apply,
    map_zsmul, smul_comm (Perm.sign _), ← Finset.smul_sum, smul_smul, Fin.val_natAdd, hsign,
    Function.comp_apply]

/-- The interior product is an antiderivation of degree `-1` for the paired wedge:
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (k + 1) φ ∧ ι_v ψ` for a `(k + 1)`-form `φ`, where the interior
product `ι_v` is `ContinuousAlternatingMap.curryLeft`. The degree `k + (l + 1)` of the first term
is identified with `k + 1 + l` by `Fin.cast`. -/
theorem curryLeft_wedgeWith (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) :
    (wedgeWith mu phi psi).curryLeft v w =
      wedgeWith mu (phi.curryLeft v) psi (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • wedgeWith mu phi (psi.curryLeft v) w := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, wedgeWith_apply, wedgeWith_apply,
    wedgeWith_apply, Matrix.vecCons]
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

end TauCeti

end
