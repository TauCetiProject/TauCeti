/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic

/-!
# The unitary group is Zariski dense in the complex matrices

A polynomial in the entries of an `n × n` complex matrix is determined by its values on the
unitary matrices. The unitary group is cut out by the equations `star A * A = 1`, which involve
complex conjugation and so are not polynomial; it is a real form of `GL n ℂ`, not an algebraic
subgroup of it, and over `ℂ` it is Zariski dense.

The proof is the singular value decomposition `A = U * diagonal d * V` with `U`, `V` unitary
(`Matrix.exists_unitary_mul_diagonal_mul_unitary`). Substituting `U * diagonal z * V` into a
polynomial gives a polynomial in `z ∈ ℂⁿ`, and `U * diagonal z * V` is unitary whenever every
`zᵢ` lies on the unit circle. A polynomial in `n` variables vanishing on the torus `(S¹)ⁿ` is zero,
since the circle is infinite (`MvPolynomial.funext_set`), so evaluating at `z = d` recovers the
value at `A`.

The same holds for the rational functions on `GL n ℂ`, those of the form `P / det ^ m`: two of
them agreeing on the unitary group agree everywhere. This is the algebraic input to Weyl's
unitarian trick, which reduces questions about the rational representations of `GL n ℂ` to
questions about the continuous representations of the compact group `U(n)`.

Over `ℝ` the analogous statement fails: the orthogonal group is cut out by polynomial equations,
so it is a proper Zariski-closed subset of the real matrices.

## Main results

* `MvPolynomial.eq_of_eval_eq_on_unitaryGroup`: two polynomials in the entries of a complex
  matrix that agree on the unitary group are equal. This is the unitary counterpart of Mathlib's
  `MvPolynomial.eq_of_eval_eq_on_gl`.
* `TauCeti.Matrix.GeneralLinearGroup.eq_of_mem_rationalFunctions_of_forall_unitary`: two rational
  functions on `GL n ℂ` that agree on the unitary group are equal.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 2.4.
-/

public section

namespace MvPolynomial

variable {n : ℕ}

/-- **The unitary group is Zariski dense in the complex matrices.** Two polynomials in the entries
of an `n × n` complex matrix that take the same value at every unitary matrix are equal. -/
theorem eq_of_eval_eq_on_unitaryGroup {p q : MvPolynomial (Fin n × Fin n) ℂ}
    (h : ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      eval (fun ij => U ij.1 ij.2) p = eval (fun ij => U ij.1 ij.2) q) :
    p = q := by
  refine MvPolynomial.funext fun x => ?_
  -- Only the shape `U * diagonal d * V` of the singular value decomposition is used.
  obtain ⟨d, U, V, hA⟩ : ∃ (d : Fin n → ℂ) (U V : Matrix.unitaryGroup (Fin n) ℂ),
      Matrix.of (fun i j => x (i, j)) = (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal d * V :=
    ⟨_, Matrix.exists_unitary_mul_diagonal_mul_unitary _⟩
  -- Substituting `U * diagonal z * V` for the matrix of variables, as a polynomial in `z`.
  let F : Fin n × Fin n → MvPolynomial (Fin n) ℂ := fun ij =>
    ∑ k, C ((U : Matrix (Fin n) (Fin n) ℂ) ij.1 k * (V : Matrix (Fin n) (Fin n) ℂ)
      k ij.2) * X k
  have hF (z : Fin n → ℂ) (r : MvPolynomial (Fin n × Fin n) ℂ) :
      eval z (bind₁ F r) = eval (fun ij => ((U : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal z * V) ij.1 ij.2) r := by
    -- `eval z` is `eval₂Hom (RingHom.id ℂ) z` by definition.
    refine (eval₂Hom_bind₁ (RingHom.id ℂ) z F r).trans
      (congrArg (fun y => eval y r) (_root_.funext fun ij => ?_))
    rw [Matrix.mul_apply]
    simp only [F, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply,
      Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- The unit circle is infinite, being connected with more than one point.
  have hS : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0
        zero_le_one).isPreconnected ⟨1, by simp, -1, by simp, by norm_num⟩
  have hpq : bind₁ F p = bind₁ F q := by
    refine MvPolynomial.funext_set (fun _ => Metric.sphere (0 : ℂ) 1) (fun _ => hS)
      fun z hz => ?_
    rw [hF, hF]
    refine h _ (mul_mem (mul_mem U.2 ?_) V.2)
    refine Matrix.diagonal_mem_unitary.mpr (Pi.mem_unitary_iff.mpr fun i => ?_)
    -- A complex number of modulus one is unitary: `conj z * z = ‖z‖ ^ 2 = 1`.
    rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
      mem_sphere_zero_iff_norm.mp (hz i trivial)]
    norm_num
  have hx : x = fun ij => ((U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal d *
      V) ij.1 ij.2 :=
    _root_.funext fun ij => congrFun (congrFun hA ij.1) ij.2
  rw [hx, ← hF, ← hF, hpq]

end MvPolynomial

namespace TauCeti.Matrix.GeneralLinearGroup

open _root_.Matrix

variable {n : ℕ}

/-- **A rational function on `GL n ℂ` is determined by its values on the unitary group.** Two
rational functions, polynomials in the entries divided by a power of the determinant, that agree
at every unitary matrix are equal. -/
theorem eq_of_mem_rationalFunctions_of_forall_unitary {f g : GL (Fin n) ℂ → ℂ}
    (hf : f ∈ rationalFunctions ℂ n) (hg : g ∈ rationalFunctions ℂ n)
    (h : ∀ u : unitaryGroup (Fin n) ℂ, f (Unitary.toUnits u) = g (Unitary.toUnits u)) :
    f = g := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions.mp (sub_mem hf hg)
  have hP0 : P = 0 := by
    refine MvPolynomial.eq_of_eval_eq_on_unitaryGroup fun U hU => ?_
    have h1 := hP (Unitary.toUnits ⟨U, hU⟩)
    rw [Pi.sub_apply, h, sub_self, mul_zero] at h1
    simpa using h1.symm
  funext x
  have hx := hP x
  rw [hP0, map_zero, Pi.sub_apply, mul_eq_zero, sub_eq_zero] at hx
  exact hx.resolve_left (pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero x))

end TauCeti.Matrix.GeneralLinearGroup
