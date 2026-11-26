/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Unitary
import TauCeti.MeasureTheory.Integral.ContinuousMap
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.MvPolynomial.Aeval
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Unitary Haar averaging of matrix polynomials

This file uses Zariski density of `Φ → U(n)` (`TauCeti.eq_smul_det_pow_of_unitary`) and normalized
Haar averaging (`TauCeti.haarProb`) on the compact group `Φ → U(n)` to extract
determinant-character components of linear forms on polynomials in tuples of complex square
matrices.

## Main results

* `MeasureTheory.Measure.exists_forall_map_eq_integral_unitary_translate`: averaging the unitary
  translates `q (uᵀ Z)` against any `μ`-integrable weight `w` on `Φ → unitaryGroup n ℂ` produces a
  polynomial `mean` such that `M mean = ∫ u, w u * M (q (uᵀ Z)) ∂μ` for every `ℂ`-linear functional
  `M`.
* `TauCeti.exists_forall_eq_mul_map_det_pow`: for any polynomial `q : MvPolynomial (Φ × n × n) ℂ`
  and exponents `c : Φ → ℕ`, there is `a : ℂ` such that every `ℂ`-linear functional `M`
  transforming by `M (q (uᵀ Z)) = t * ∏ τ, det (u τ) ^ c τ` on `Φ → unitaryGroup n ℂ` satisfies
  `t = a * M (∏ τ, det (Z τ) ^ c τ)`.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press, 1939, Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer, 2009, §2.4.
* Adapted from the averaging section of `src/Lib/GLn/SchurModule/Polarisation.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open Matrix MvPolynomial MeasureTheory

namespace MeasureTheory.Measure

variable {Φ n : Type*} [Fintype n] [DecidableEq n]

/-- Averaging the unitary translates `q (uᵀ Z)` of a polynomial `q` in square matrices against an
integrable weight `w` with respect to a measure `μ` on `Φ → unitaryGroup n ℂ` produces a
polynomial `mean` such that `M mean = ∫ u, w u * M (q (uᵀ Z)) ∂μ` for every `ℂ`-linear functional
`M`. -/
theorem exists_forall_map_eq_integral_unitary_translate
    [MeasurableSpace (Φ → Matrix.unitaryGroup n ℂ)]
    [OpensMeasurableSpace (Φ → Matrix.unitaryGroup n ℂ)]
    (μ : Measure (Φ → Matrix.unitaryGroup n ℂ))
    (q : MvPolynomial (Φ × n × n) ℂ)
    {w : (Φ → Matrix.unitaryGroup n ℂ) → ℂ} (hw : Integrable w μ) :
    ∃ mean : MvPolynomial (Φ × n × n) ℂ, ∀ M : MvPolynomial (Φ × n × n) ℂ →ₗ[ℂ] ℂ,
      M mean = ∫ u : Φ → Matrix.unitaryGroup n ℂ, w u *
        M (aeval (fun y : Φ × n × n ↦
          ∑ i : n, (u y.1 : Matrix n n ℂ) i y.2.1 • X (y.1, i, y.2.2)) q) ∂μ := by
  let Q : MvPolynomial (Φ × n × n) (MvPolynomial (Φ × n × n) ℂ) :=
    aeval (fun y : Φ × n × n ↦
      ∑ i : n, X (R := ℂ) (y.1, i, y.2.1) • X (y.1, i, y.2.2)) q
  let φ (u : Φ → Matrix.unitaryGroup n ℂ) : MvPolynomial (Φ × n × n) ℂ →ₐ[ℂ] ℂ :=
    aeval fun y : Φ × n × n ↦ (u y.1 : Matrix n n ℂ) y.2.1 y.2.2
  have h_expand (u : Φ → Matrix.unitaryGroup n ℂ) :
      aeval (fun y : Φ × n × n ↦
          ∑ i : n, (u y.1 : Matrix n n ℂ) i y.2.1 • X (R := ℂ) (y.1, i, y.2.2)) q =
        ∑ d ∈ Q.support, φ u (Q.coeff d) • monomial d 1 := by
    calc _ = mapAlgHom (φ u) Q := by simp [Q, φ, comp_aeval_apply, smul_eq_C_mul]
      _ = ∑ d ∈ Q.support, φ u (Q.coeff d) • monomial d 1 := by
        conv_lhs => rw [Q.as_sum, _root_.map_sum]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        have hmap : mapAlgHom (φ u) (monomial d (Q.coeff d)) =
            monomial d (φ u (Q.coeff d)) := by simp
        rw [hmap, smul_monomial, smul_eq_mul, mul_one]
  have hφ_cont (p : MvPolynomial (Φ × n × n) ℂ) : Continuous fun u ↦ φ u p := by
    have hval : Continuous fun U : Matrix.unitaryGroup n ℂ ↦ (U : Matrix n n ℂ) :=
      continuous_subtypeVal
    have h_coord : Continuous fun (u : Φ → Matrix.unitaryGroup n ℂ) (y : Φ × n × n) ↦
        (u y.1 : Matrix n n ℂ) y.2.1 y.2.2 :=
      continuous_pi fun y ↦ (continuous_apply y.2.2).comp ((continuous_apply y.2.1).comp
        (hval.comp (continuous_apply y.1)))
    exact (MvPolynomial.continuous_aeval p).comp h_coord
  refine ⟨∑ d ∈ Q.support, (∫ u, w u * φ u (Q.coeff d) ∂μ) • monomial d 1, fun M ↦ ?_⟩
  have h_int (d : Φ × n × n →₀ ℕ) :
      Integrable (fun u ↦ w u * φ u (Q.coeff d) * M (monomial d 1)) μ :=
    (hw.mul_continuous_of_compactSpace (hφ_cont (Q.coeff d))).mul_const (M (monomial d 1))
  simp only [h_expand, _root_.map_sum, _root_.map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc,
    ← integral_mul_const]
  exact (integral_finsetSum Q.support fun d _ ↦ h_int d).symm

end MeasureTheory.Measure

namespace TauCeti

variable {Φ n : Type*} [Fintype n] [DecidableEq n]

/-- **Unitary averaging for determinant characters.** Let `q : MvPolynomial (Φ × n × n) ℂ` and
`c : Φ → ℕ`. There exists `a : ℂ` such that every `ℂ`-linear functional `M` satisfying
`M (q (uᵀ Z)) = t * ∏ τ, det (u τ) ^ c τ` for all `u : Φ → unitaryGroup n ℂ` obeys
`t = a * M (∏ τ, det (Z τ) ^ c τ)`, where `Z τ` is the matrix of variables
`(i, j) ↦ X (τ, i, j)`. -/
theorem exists_forall_eq_mul_map_det_pow [Fintype Φ] (c : Φ → ℕ)
    (q : MvPolynomial (Φ × n × n) ℂ) :
    ∃ a : ℂ, ∀ (M : MvPolynomial (Φ × n × n) ℂ →ₗ[ℂ] ℂ) (t : ℂ),
      (∀ u : Φ → Matrix.unitaryGroup n ℂ,
        M (aeval (fun y : Φ × n × n ↦
          ∑ i : n, (u y.1 : Matrix n n ℂ) i y.2.1 • X (y.1, i, y.2.2)) q) =
          t * ∏ τ : Φ, (u τ : Matrix n n ℂ).det ^ c τ) →
      t = a * M (∏ τ : Φ, (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det ^ c τ) := by
  let : MeasurableSpace (Φ → Matrix.unitaryGroup n ℂ) := borel _
  have : BorelSpace (Φ → Matrix.unitaryGroup n ℂ) := ⟨rfl⟩
  let μ : Measure (Φ → Matrix.unitaryGroup n ℂ) := haarProb (Φ → Matrix.unitaryGroup n ℂ)
  let χ (u : Φ → Matrix.unitaryGroup n ℂ) : ℂ := ∏ τ : Φ, (u τ : Matrix n n ℂ).det ^ c τ
  have hχ_mul (u v : Φ → Matrix.unitaryGroup n ℂ) : χ (u * v) = χ u * χ v := by
    simp [χ, mul_pow, Finset.prod_mul_distrib]
  have hχ_inv (u : Φ → Matrix.unitaryGroup n ℂ) : χ u⁻¹ * χ u = 1 := by
    simpa [χ] using (hχ_mul u⁻¹ u).symm
  have hχ_cont : Continuous (fun u ↦ χ u⁻¹) := by
    have hχ : Continuous χ := by
      unfold χ
      fun_prop
    exact hχ.comp continuous_inv
  obtain ⟨mean, h_mean⟩ := μ.exists_forall_map_eq_integral_unitary_translate q
    (hχ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let value (x : Φ → Matrix.unitaryGroup n ℂ) : MvPolynomial (Φ × n × n) ℂ →ₐ[ℂ] ℂ :=
    aeval fun y : Φ × n × n ↦ (x y.1 : Matrix n n ℂ) y.2.2 y.2.1
  let a : ℂ := ∫ u, χ u⁻¹ * value u q ∂μ
  have h_point (x u : Φ → Matrix.unitaryGroup n ℂ) : value x (aeval
      (fun y : Φ × n × n ↦ ∑ i : n, (u y.1 : Matrix n n ℂ) i y.2.1 • X (y.1, i, y.2.2)) q) =
      value (x * u) q := by
    simp [value, comp_aeval_apply, Matrix.mul_apply, mul_comm]
  have h_value (x : Φ → Matrix.unitaryGroup n ℂ) : value x mean = a * χ x :=
    calc value x mean = ∫ u, χ u⁻¹ * value (x * u) q ∂μ := by
          simpa only [AlgHom.toLinearMap_apply, h_point] using h_mean (value x).toLinearMap
      _ = ∫ u, χ (x * u)⁻¹ * value (x * u) q * χ x ∂μ := by
          congr with u
          simp only [_root_.mul_inv_rev, hχ_mul]
          linear_combination -(χ u⁻¹ * value (x * u) q) * hχ_inv x
      _ = a * χ x := by
          rw [integral_mul_const, integral_mul_left_eq_self (fun u ↦ χ u⁻¹ * value u q) x]
  have h_eval (x : Φ → Matrix.unitaryGroup n ℂ) :
      mean.eval (fun y ↦ (x y.1 : Matrix n n ℂ) y.2.2 y.2.1) =
        a * ∏ τ : Φ, (x τ : Matrix n n ℂ).det ^ c τ := by
    have h_eq := congrArg (fun f : MvPolynomial (Φ × n × n) ℂ →+* ℂ ↦ f mean)
      (coe_aeval_eq_eval fun y : Φ × n × n ↦ (x y.1 : Matrix n n ℂ) y.2.2 y.2.1)
    exact h_eq.symm.trans (h_value x)
  refine ⟨a, fun M t hM ↦ ?_⟩
  calc t = ∫ u, χ u⁻¹ * (t * χ u) ∂μ := by simp [mul_left_comm _ t, hχ_inv]
    _ = M mean := by simp only [h_mean, hM, χ]
    _ = a * M (∏ τ : Φ, (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det ^ c τ) := by
        simp [eq_smul_det_pow_of_unitary c h_eval]

end TauCeti

end
