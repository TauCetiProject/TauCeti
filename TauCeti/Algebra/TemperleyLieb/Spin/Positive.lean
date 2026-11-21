/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.LinearAlgebra.Matrix.Trace.Positive
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Positive spin models for Temperley–Lieb algebras

For a negative real spin parameter `q`, the spin generator matrices are Hermitian and the
configuration weights are strictly positive. Thus the weighted matrix trace is a faithful
positive functional; its pullback along `spinRep` is the Markov trace. It is tracial on the
represented algebra, not in general on the entire matrix algebra.

Every real loop parameter `δ ≥ 2`, including the boundary `δ = 2`, admits such a spin parameter.
This gives positive receiving matrix models for the continuous range of loop parameters,
without requiring a star structure on the presented Temperley–Lieb algebra. No injectivity of
the spin representation is asserted.

Use `open scoped ComplexOrder MatrixOrder` for the scalar and positive-semidefinite matrix
orders when applying the positive functional.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553 (weighted traces of vertex models).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The spin matrices and trace are those of `TauCeti.Algebra.TemperleyLieb.MarkovTrace`.
-/

public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TauCeti.TemperleyLieb

/-- At a self-adjoint spin parameter, every spin generator is Hermitian. Positivity of the
parameter is not required. -/
theorem isHermitian_spinGenerator {R : Type*} [CommRing R] [StarRing R] (q : Rˣ)
    (hq : IsSelfAdjoint (q : R)) {n : ℕ} (j k : Fin n) :
    (spinGenerator q j k).IsHermitian := by
  classical
  have hqu : star q = q := Units.ext hq.star_eq
  refine Matrix.IsHermitian.ext fun s t ↦ ?_
  have hrev : (∀ l ∉ ({j, k} : Finset (Fin n)), t l = s l) ↔
      (∀ l ∉ ({j, k} : Finset (Fin n)), s l = t l) := by
    constructor <;> intro h l hl <;> exact (h l hl).symm
  simp only [spinGenerator_apply, hrev]
  split_ifs
  · cases s j <;> cases s k <;> cases t j <;> cases t k <;>
      simp [← Units.coe_star, hqu]
  · simp

variable {𝕜 : Type*} [RCLike 𝕜] (q : 𝕜ˣ) {n : ℕ}

/-- A negative spin parameter gives a strictly positive weight to either spin. -/
theorem markovWeight_pos (hq : (q : 𝕜) < 0) (b : Bool) : 0 < markovWeight q b := by
  cases b with
  | false =>
    simpa [Units.val_inv_eq_inv_val] using RCLike.inv_pos_of_pos (neg_pos.mpr hq)
  | true => simpa using neg_pos.mpr hq

/-- Every configuration has strictly positive weight at a negative spin parameter. -/
theorem spinWeight_pos (hq : (q : 𝕜) < 0) (s : Fin n → Bool) : 0 < spinWeight q s := by
  rw [spinWeight_def]
  exact Finset.prod_pos fun i _ ↦ markovWeight_pos q hq (s i)

/-- The positive weighted matrix functional of the spin model at a negative spin parameter.
It is tracial on the image of `spinRep`, but need not be tracial on all matrices. -/
noncomputable def spinPositiveLinearMap (hq : (q : 𝕜) < 0) :
    Matrix (Fin n → Bool) (Fin n → Bool) 𝕜 →ₚ[𝕜] 𝕜 :=
  PositiveLinearMap.mk₀
    (traceLinearMap (Fin n → Bool) 𝕜 𝕜 ∘ₗ
      LinearMap.mulLeft 𝕜 (diagonal (spinWeight q)))
    fun _ hA ↦ hA.posSemidef.trace_diagonal_mul_nonneg fun s ↦ (spinWeight_pos q hq s).le

/-- The spin functional is the matrix trace weighted by the configuration weights. -/
@[simp]
theorem spinPositiveLinearMap_apply (hq : (q : 𝕜) < 0)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) 𝕜) :
    spinPositiveLinearMap q hq A = (diagonal (spinWeight q) * A).trace := (rfl)

/-- The positive spin functional pulls back to the existing Markov trace. -/
@[simp↓]
theorem spinPositiveLinearMap_spinRep (hq : (q : 𝕜) < 0) {δ : 𝕜}
    (hδ : δ = -((q : 𝕜) + ((q⁻¹ : 𝕜ˣ) : 𝕜))) (x : TemperleyLieb 𝕜 δ n) :
    spinPositiveLinearMap q hq (spinRep q hδ x) = markovTrace q hδ x := by
  simp only [spinPositiveLinearMap_apply, markovTrace_apply]

/-- The value of the positive spin functional on the identity is the loop parameter to the
number of strands. -/
@[simp↓]
theorem spinPositiveLinearMap_one (hq : (q : 𝕜) < 0) :
    spinPositiveLinearMap (n := n) q hq 1 = (-((q : 𝕜) + ((q⁻¹ : 𝕜ˣ) : 𝕜))) ^ n := by
  simpa only [map_one, spinPositiveLinearMap_apply, markovTrace_apply] using
    markovTrace_one (n := n) q rfl

/-- The spin functional is faithful on matrix squares. This is faithfulness of the receiving
functional, not of the Temperley–Lieb representation. -/
@[simp↓]
theorem spinPositiveLinearMap_conjTranspose_mul_self_eq_zero_iff (hq : (q : 𝕜) < 0)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) 𝕜) :
    spinPositiveLinearMap q hq (Aᴴ * A) = 0 ↔ A = 0 := by
  simp only [spinPositiveLinearMap_apply]
  exact trace_diagonal_mul_conjTranspose_mul_self_eq_zero_iff (spinWeight_pos q hq) A

/-- The weighted matrix functional is tracial on the represented Temperley–Lieb algebra. -/
theorem spinPositiveLinearMap_spinRep_mul_comm (hq : (q : 𝕜) < 0) {δ : 𝕜}
    (hδ : δ = -((q : 𝕜) + ((q⁻¹ : 𝕜ˣ) : 𝕜))) (x y : TemperleyLieb 𝕜 δ n) :
    spinPositiveLinearMap q hq (spinRep q hδ x * spinRep q hδ y) =
      spinPositiveLinearMap q hq (spinRep q hδ y * spinRep q hδ x) := by
  simp only [← map_mul, spinPositiveLinearMap_spinRep, markovTrace_mul_comm]

/-- Every real loop parameter `δ ≥ 2`, including `δ = 2`, has a negative spin parameter `q`
with `δ = -(q + q⁻¹)`. -/
theorem exists_neg_spinParameter {δ : ℝ} (hδ : 2 ≤ δ) :
    ∃ q : 𝕜ˣ, (q : 𝕜) < 0 ∧ (δ : 𝕜) = -((q : 𝕜) + ((q⁻¹ : 𝕜ˣ) : 𝕜)) := by
  let r := δ / 2 + Real.sqrt ((δ / 2) ^ 2 - 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrinv : r⁻¹ = δ / 2 - Real.sqrt ((δ / 2) ^ 2 - 1) :=
    Real.add_sqrt_self_sq_sub_one_inv (by linarith)
  have hrne : (-((r : ℝ) : 𝕜)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hr.ne')
  refine ⟨Units.mk0 (-((r : ℝ) : 𝕜)) hrne, ?_, ?_⟩
  · simpa using (neg_neg_iff_pos.mpr (RCLike.ofReal_pos.mpr hr) : -((r : ℝ) : 𝕜) < 0)
  · simp only [Units.val_mk0, Units.val_inv_eq_inv_val, inv_neg, ← RCLike.ofReal_inv]
    rw [hrinv]
    push_cast
    dsimp [r]
    push_cast
    ring

end TauCeti.TemperleyLieb
