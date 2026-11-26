/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Separation.Connected
import TauCeti.Analysis.Matrix.SingularValues
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Unitary Zariski density and Haar averaging of matrix polynomials

This file extends Zariski density of the complex unitary group `U(n)` to arbitrary products
`Φ → U(n)` (`MvPolynomial.eq_of_eval_eq_on_pi_unitaryGroup`) and uses Haar averaging on the
compact group `Φ → U(n)` to extract determinant-character components of linear forms on
polynomials in tuples of complex square matrices.

## Main results

* `MvPolynomial.eq_of_eval_eq_on_pi_unitaryGroup`: two polynomials in `MvPolynomial (Φ × n × n) ℂ`
  that agree on every tuple of unitary matrices are equal (for any index type `Φ`).
* `TauCeti.eq_smul_det_pow_of_unitary`: a polynomial `f : MvPolynomial (Φ × n × n) ℂ` whose value
  at `xᵀ` equals `a * ∏ τ, det (x τ) ^ c τ` for all `x : Φ → unitaryGroup n ℂ` equals
  `a • ∏ τ, det (Z τ) ^ c τ`.
* `TauCeti.exists_forall_map_eq_integral_translate`: averaging the unitary translates `q (uᵀ z)`
  against a continuous weight `w` with respect to any finite measure `μ` on `Φ → unitaryGroup n ℂ`
  produces a polynomial `mean` commuting with every `ℂ`-linear functional `M`.
* `TauCeti.exists_forall_eq_mul_map_det_pow`: for any polynomial `q : MvPolynomial (Φ × n × n) ℂ`
  and exponents `c : Φ → ℕ`, there is `a : ℂ` such that every `ℂ`-linear functional `M`
  transforming by `M (q (uᵀ z)) = t * ∏ τ, det (u τ) ^ c τ` on `Φ → unitaryGroup n ℂ` satisfies
  `t = a * M (∏ τ, det (z τ) ^ c τ)`.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press, 1939, Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer, 2009, §2.4.
* Adapted from the averaging section of `src/Lib/GLn/SchurModule/Polarisation.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open Matrix MvPolynomial MeasureTheory

namespace MvPolynomial

/-- **Zariski density of `U(n)^Φ` in `M_n(ℂ)^Φ`.** Two polynomials in the entries of a family of
square complex matrices indexed by `Φ` that take the same value on every tuple of unitary matrices
are equal. -/
theorem eq_of_eval_eq_on_pi_unitaryGroup {Φ n : Type*} [Fintype n] [DecidableEq n]
    {p q : MvPolynomial (Φ × n × n) ℂ}
    (h : ∀ U : Φ → Matrix.unitaryGroup n ℂ,
      eval (fun x ↦ (U x.1 : Matrix n n ℂ) x.2.1 x.2.2) p =
        eval (fun x ↦ (U x.1 : Matrix n n ℂ) x.2.1 x.2.2) q) :
    p = q := by
  refine MvPolynomial.funext fun x ↦ ?_
  have hsvd (τ : Φ) : ∃ (d : n → ℂ) (U V : Matrix.unitaryGroup n ℂ),
      Matrix.of (fun i j ↦ x (τ, i, j)) = (U : Matrix n n ℂ) * Matrix.diagonal d * V := by
    let e := Fintype.equivFin n
    obtain ⟨d, U, V, hUV⟩ : ∃ (d : Fin (Fintype.card n) → ℂ)
        (U V : Matrix.unitaryGroup (Fin (Fintype.card n)) ℂ),
        (Matrix.of fun i j ↦ x (τ, i, j)).submatrix e.symm e.symm =
          (U : Matrix _ _ ℂ) * Matrix.diagonal d * (V : Matrix _ _ ℂ) :=
      ⟨_, Matrix.exists_unitary_mul_diagonal_mul_unitary _⟩
    refine ⟨d ∘ e, ⟨(U : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr
        U.property⟩,
      ⟨(V : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr V.property⟩, ?_⟩
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← hUV, Matrix.submatrix_submatrix]
    simp
  choose d U V hA using hsvd
  let F : Φ × n × n → MvPolynomial (Φ × n) ℂ := fun ⟨τ, i, j⟩ ↦
    ∑ k, C ((U τ : Matrix n n ℂ) i k * (V τ : Matrix n n ℂ) k j) * X (τ, k)
  have hF (z : Φ × n → ℂ) (r : MvPolynomial (Φ × n × n) ℂ) :
      eval z (aeval F r) =
        eval (fun y ↦ ((U y.1 : Matrix n n ℂ) * Matrix.diagonal (fun k ↦ z (y.1, k)) * V y.1)
          y.2.1 y.2.2) r := by
    have hcomp : (eval z).comp (algebraMap ℂ (MvPolynomial (Φ × n) ℂ)) = RingHom.id ℂ := by
      ext; simp
    rw [map_aeval, hcomp]
    refine congrArg (fun y ↦ eval y r) (_root_.funext fun ⟨τ, i, j⟩ ↦ ?_)
    rw [Matrix.mul_apply]
    simp only [F, map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hS : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0
        zero_le_one).isPreconnected ⟨1, by simp, -1, by simp, by norm_num⟩
  have hpq : aeval F p = aeval F q := by
    refine MvPolynomial.funext_set (fun _ ↦ Metric.sphere (0 : ℂ) 1) (fun _ ↦ hS)
      fun z hz ↦ ?_
    rw [hF, hF]
    let W : Φ → Matrix.unitaryGroup n ℂ := fun τ ↦
      ⟨(U τ : Matrix n n ℂ) * Matrix.diagonal (fun k ↦ z (τ, k)) * V τ,
        mul_mem (mul_mem (U τ).property (Matrix.diagonal_mem_unitary.mpr
          (Pi.mem_unitary_iff.mpr fun k ↦ by
            rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
              mem_sphere_zero_iff_norm.mp (hz (τ, k) trivial)]
            norm_num))) (V τ).property⟩
    exact h W
  have hx : x = fun y ↦ ((U y.1 : Matrix n n ℂ) * Matrix.diagonal (d y.1) * V y.1) y.2.1 y.2.2 :=
    _root_.funext fun ⟨τ, i, j⟩ ↦ congrFun (congrFun (hA τ) i) j
  rw [hx, ← hF (fun y ↦ d y.1 y.2) p, ← hF (fun y ↦ d y.1 y.2) q, hpq]

end MvPolynomial

namespace TauCeti

variable {Φ n : Type*} [Fintype n] [DecidableEq n]

/-- A polynomial `f` in square complex matrices indexed by `Φ` whose value at `xᵀ` is
`a * ∏ τ, det (x τ) ^ c τ` for all unitary `x : Φ → unitaryGroup n ℂ` equals
`a • ∏ τ, det (Z τ) ^ c τ`, where `Z τ` is the matrix of variables `(i, j) ↦ X (τ, i, j)`. -/
theorem eq_smul_det_pow_of_unitary [Fintype Φ] (c : Φ → ℕ) {f : MvPolynomial (Φ × n × n) ℂ}
    {a : ℂ} (hf : ∀ x : Φ → Matrix.unitaryGroup n ℂ,
      f.eval (fun y ↦ (x y.1 : Matrix n n ℂ) y.2.2 y.2.1) =
        a * ∏ τ : Φ, (x τ : Matrix n n ℂ).det ^ c τ) :
    f = a • ∏ τ : Φ, (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det ^ c τ := by
  let swap : Φ × n × n ≃ Φ × n × n :=
    { toFun := fun ⟨τ, i, j⟩ ↦ (τ, j, i)
      invFun := fun ⟨τ, i, j⟩ ↦ (τ, j, i)
      left_inv := fun ⟨_, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, _⟩ ↦ rfl }
  apply (MvPolynomial.renameEquiv ℂ swap).injective
  refine MvPolynomial.eq_of_eval_eq_on_pi_unitaryGroup fun U ↦ ?_
  have hdet (τ : Φ) :
      eval (fun y ↦ (U y.1 : Matrix n n ℂ) y.2.2 y.2.1)
        (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det =
      (U τ : Matrix n n ℂ).det := by
    rw [RingHom.map_det]
    have hmat : (RingHom.mapMatrix (eval (fun y ↦ (U y.1 : Matrix n n ℂ) y.2.2 y.2.1)))
        (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)) = (U τ : Matrix n n ℂ)ᵀ := by
      ext i j
      simp
    rw [hmat, det_transpose]
  simp only [renameEquiv_apply, smul_eq_C_mul, map_mul, eval_C, map_prod, map_pow, eval_rename,
    Function.comp_def, swap, Equiv.coe_fn_mk]
  rw [hf U]
  congr 1
  refine Finset.prod_congr rfl fun τ _ ↦ ?_
  rw [hdet τ]

/-- The integral over `Φ → unitaryGroup n ℂ`, against a finite measure `μ` and a continuous weight
`w`, of the unitary translates `q (uᵀ z)` of a polynomial `q` in square matrices is represented by
a polynomial `mean` commuting with every `ℂ`-linear functional `M`. -/
theorem exists_forall_map_eq_integral_translate
    [MeasurableSpace (Φ → Matrix.unitaryGroup n ℂ)]
    [OpensMeasurableSpace (Φ → Matrix.unitaryGroup n ℂ)]
    (μ : Measure (Φ → Matrix.unitaryGroup n ℂ)) [IsFiniteMeasure μ]
    (q : MvPolynomial (Φ × n × n) ℂ)
    {w : (Φ → Matrix.unitaryGroup n ℂ) → ℂ} (hw : Continuous w) :
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
        conv_lhs => rw [Q.as_sum, map_sum]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        have hmap : mapAlgHom (φ u) (monomial d (Q.coeff d)) =
            monomial d (φ u (Q.coeff d)) := map_monomial (φ u).toRingHom d (Q.coeff d)
        rw [hmap, smul_monomial, smul_eq_mul, mul_one]
  have hφ_cont (p : MvPolynomial (Φ × n × n) ℂ) : Continuous fun u ↦ φ u p := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      simp only [φ, aeval_C]
      exact continuous_const
    | add p₁ p₂ h₁ h₂ =>
      simp only [map_add]
      exact h₁.add h₂
    | mul_X p₁ y h₁ =>
      simp only [map_mul, φ, aeval_X]
      have hval : Continuous fun U : Matrix.unitaryGroup n ℂ ↦ (U : Matrix n n ℂ) :=
        continuous_subtypeVal
      exact h₁.mul ((continuous_apply y.2.2).comp ((continuous_apply y.2.1).comp
        (hval.comp (continuous_apply y.1))))
  refine ⟨∑ d ∈ Q.support, (∫ u, w u * φ u (Q.coeff d) ∂μ) • monomial d 1, fun M ↦ ?_⟩
  have h_cont (d : Φ × n × n →₀ ℕ) :
      Continuous fun u ↦ w u * φ u (Q.coeff d) * M (monomial d 1) :=
    (hw.mul (hφ_cont (Q.coeff d))).mul continuous_const
  simp only [h_expand, map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc,
    ← integral_mul_const]
  exact (integral_finsetSum Q.support fun d _ ↦
    (h_cont d).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).symm

/-- **Unitary averaging for determinant characters.** Let `q : MvPolynomial (Φ × n × n) ℂ` and
`c : Φ → ℕ`. There exists `a : ℂ` such that every `ℂ`-linear functional `M` satisfying
`M (q (uᵀ z)) = t * ∏ τ, det (u τ) ^ c τ` for all `u : Φ → unitaryGroup n ℂ` obeys
`t = a * M (∏ τ, det (Z τ) ^ c τ)`. -/
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
  let K : TopologicalSpace.PositiveCompacts (Φ → Matrix.unitaryGroup n ℂ) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ : Measure (Φ → Matrix.unitaryGroup n ℂ) := Measure.haarMeasure K
  have : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
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
  obtain ⟨mean, h_mean⟩ :=
    exists_forall_map_eq_integral_translate μ q (w := fun u ↦ χ u⁻¹) hχ_cont
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
  refine ⟨a, fun M t hM ↦ ?_⟩
  calc t = ∫ u, χ u⁻¹ * (t * χ u) ∂μ := by simp [mul_left_comm _ t, hχ_inv]
    _ = M mean := by simp only [h_mean, hM, χ]
    _ = a * M (∏ τ : Φ, (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det ^ c τ) := by
        simp [eq_smul_det_pow_of_unitary c h_value]

end TauCeti

end
