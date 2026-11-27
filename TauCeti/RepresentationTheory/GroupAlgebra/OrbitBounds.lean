/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsAlgebraHom
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Orbit bounds for monoid algebra operators

A bound on the observations of the translates of a vector bounds the same observations
of its image under a monoid algebra operator. The loss in a weighted sum of squared
norms is at most the square of the sum of the norms of the coefficients. Semilinear
observations allow the coefficients to be measured after a field embedding, without
requiring the embedding to preserve their norms.

For a scaled projection this is the class-sum estimate used in
`New.Data.normSqAt_goodProjTranslate_le` in `grh/src/New/UpperBound/Size/ArchimedeanSize.lean`
of lsernau/grh-lean (revision `72fead1`).
-/

public section

open scoped BigOperators

namespace Representation

variable {k L G V E : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [SeminormedRing L] [SeminormedAddCommGroup E] [Module L E] [IsBoundedSMul L E] {σ : k →+* L}

/-- A semilinear observation of a monoid algebra operator applied to a vector is bounded by
summing the products of the coefficient norms and the observed norms of its translates. -/
theorem norm_map_asAlgebraHom_apply_le (ρ : Representation k G V) (a : MonoidAlgebra k G)
    (x : V) (f : V →ₛₗ[σ] E) :
    ‖f (ρ.asAlgebraHom a x)‖ ≤ ∑ g ∈ a.coeff.support, ‖σ (a.coeff g)‖ * ‖f (ρ g x)‖ := by
  classical
  simp only [ρ.asAlgebraHom_apply, Finsupp.sum, map_sum, map_smulₛₗ]
  exact norm_sum_le_of_le _ fun g _ ↦ norm_smul_le _ _

/-- Bounds on the squared norms of all observed translates give a weighted bound for the
image under the monoid algebra action. The weights must be nonnegative on the sum, and the
orbit bound can vary with the observation. -/
theorem sum_norm_sq_asAlgebraHom_le {ι : Type*} (ρ : Representation k G V)
    (a : MonoidAlgebra k G) (x : V) (s : Finset ι) (f : ι → V →ₛₗ[σ] E) {w B : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hB : ∀ i ∈ s, ∀ g, ‖f i (ρ g x)‖ ^ 2 ≤ B i) :
    ∑ i ∈ s, w i * ‖f i (ρ.asAlgebraHom a x)‖ ^ 2 ≤
      (∑ g ∈ a.coeff.support, ‖σ (a.coeff g)‖) ^ 2 * ∑ i ∈ s, w i * B i := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hB₀ : 0 ≤ B i := (sq_nonneg _).trans (hB i hi 1)
  have hn : ‖f i (ρ.asAlgebraHom a x)‖ ≤
      (∑ g ∈ a.coeff.support, ‖σ (a.coeff g)‖) * √(B i) := by
    refine (ρ.norm_map_asAlgebraHom_apply_le a x (f i)).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun g _ ↦ mul_le_mul_of_nonneg_left
      (Real.le_sqrt_of_sq_le (hB i hi g)) (norm_nonneg _)
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  simpa only [mul_pow, Real.sq_sqrt hB₀] using pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- For a finite monoid `G`, suppose the coefficient norms of `e` after applying the scalar
map are at most one. Applying `e` to a translate of `x` and scaling by `|G|` bounds the
weighted sum of squared observations by `|G|⁴` times the total weight times the orbit bound. -/
theorem sum_norm_sq_card_smul_asAlgebraHom_apply_le {ι : Type*} [Fintype G]
    (ρ : Representation k G V) (e : MonoidAlgebra k G) (x : V) (g : G) (s : Finset ι)
    (f : ι → V →ₛₗ[σ] E) {w : ι → ℝ} {B : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ t, ‖σ (e.coeff t)‖ ≤ 1) (hB : ∀ i ∈ s, ∀ t, ‖f i (ρ t x)‖ ^ 2 ≤ B) :
    ∑ i ∈ s, w i * ‖f i (Fintype.card G • ρ.asAlgebraHom e (ρ g x))‖ ^ 2 ≤
      (Fintype.card G : ℝ) ^ 4 * ((∑ i ∈ s, w i) * B) := by
  classical
  let N := Fintype.card G
  have hcoeff : (∑ t ∈ e.coeff.support, ‖σ (e.coeff t)‖) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ e.coeff.support, (1 : ℝ) := Finset.sum_le_sum fun t _ ↦ he t
      _ = e.coeff.support.card := by simp
      _ ≤ (N : ℝ) := by exact_mod_cast Finset.card_le_univ _
  have hsum := ρ.sum_norm_sq_asAlgebraHom_le e (ρ g x) s f hw (B := fun _ ↦ B)
    (fun i hi t ↦ by simpa only [← mul_apply_eq_comp, ← map_mul] using hB i hi (t * g))
  have hsum₀ : 0 ≤ ∑ i ∈ s, w i * B :=
    Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) ((sq_nonneg _).trans (hB i hi 1))
  calc
    _ ≤ ∑ i ∈ s, w i * ((N : ℝ) ^ 2 * ‖f i (ρ.asAlgebraHom e (ρ g x))‖ ^ 2) := by
      refine Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left ?_ (hw i hi)
      rw [map_nsmul, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) norm_nsmul_le 2
    _ = (N : ℝ) ^ 2 * ∑ i ∈ s, w i * ‖f i (ρ.asAlgebraHom e (ρ g x))‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ mul_left_comm ..
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * ∑ i ∈ s, w i * B) := by
      gcongr
      exact hsum.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hcoeff 2) hsum₀)
    _ = _ := by rw [Finset.sum_mul]; ring

end Representation
