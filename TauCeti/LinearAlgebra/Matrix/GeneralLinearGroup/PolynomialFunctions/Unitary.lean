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

A polynomial in the entries of a square complex matrix is determined by its values on the
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

* `MvPolynomial.eq_of_eval_eq_on_pi_unitaryGroup`: two polynomials in the entries of a family of
  square complex matrices indexed by `Φ` that agree on every tuple of unitary matrices are equal.
* `MvPolynomial.eq_of_eval_eq_on_unitaryGroup`: two polynomials in the entries of a complex
  matrix that agree on the unitary group are equal. This is the unitary counterpart of Mathlib's
  `MvPolynomial.eq_of_eval_eq_on_gl`.
* `TauCeti.eq_smul_det_pow_of_unitary`: a polynomial in square complex matrices indexed by `Φ`
  whose value at `xᵀ` is `a * ∏ τ, det (x τ) ^ c τ` for all unitary `x` equals
  `a • ∏ τ, det (Z τ) ^ c τ`.
* `TauCeti.Matrix.GeneralLinearGroup.eq_of_mem_rationalFunctions_of_forall_unitary`: two rational
  functions on `GL n ℂ` that agree on the unitary group are equal.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 2.4.
* The product Zariski-density and determinant-character results are adapted from
  `src/Lib/GLn/SchurModule/Polarisation.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
  In particular, `TauCeti.eq_smul_det_pow_of_unitary` follows `New.eq_smul_det_pow_of_unitary`.
-/

public section

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Zariski density of `U(n)^Φ` in `M_n(ℂ)^Φ`.** Two polynomials in the entries of a family of
square complex matrices indexed by `Φ` that take the same value at every tuple of unitary matrices
are equal. -/
theorem eq_of_eval_eq_on_pi_unitaryGroup {Φ : Type*} {p q : MvPolynomial (Φ × ι × ι) ℂ}
    (h : ∀ U : Φ → Matrix ι ι ℂ, (∀ τ, U τ ∈ Matrix.unitaryGroup ι ℂ) →
      eval (fun x => U x.1 x.2.1 x.2.2) p = eval (fun x => U x.1 x.2.1 x.2.2) q) :
    p = q := by
  refine MvPolynomial.funext fun x => ?_
  -- Only the shape `U * diagonal d * V` of the singular value decomposition is used; it is
  -- transported from `Fin (Fintype.card ι)` along an enumeration of `ι`.
  have hsvd (τ : Φ) : ∃ (d : ι → ℂ) (U V : Matrix.unitaryGroup ι ℂ),
      Matrix.of (fun i j => x (τ, i, j)) = (U : Matrix ι ι ℂ) * Matrix.diagonal d * V := by
    let e := Fintype.equivFin ι
    obtain ⟨d, U, V, hUV⟩ : ∃ (d : Fin (Fintype.card ι) → ℂ)
        (U V : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ),
        (Matrix.of fun i j => x (τ, i, j)).submatrix e.symm e.symm =
          (U : Matrix _ _ ℂ) * Matrix.diagonal d * (V : Matrix _ _ ℂ) :=
      ⟨_, Matrix.exists_unitary_mul_diagonal_mul_unitary _⟩
    refine ⟨d ∘ e, ⟨(U : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr
        U.property⟩,
      ⟨(V : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr V.property⟩, ?_⟩
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← hUV, Matrix.submatrix_submatrix]
    simp
  choose d U V hA using hsvd
  -- Substituting `U τ * diagonal z_τ * V τ` for the matrix of variables, as a polynomial in `z`.
  let F : Φ × ι × ι → MvPolynomial (Φ × ι) ℂ := fun ⟨τ, i, j⟩ =>
    ∑ k, C ((U τ : Matrix ι ι ℂ) i k * (V τ : Matrix ι ι ℂ) k j) * X (τ, k)
  have hF (z : Φ × ι → ℂ) (r : MvPolynomial (Φ × ι × ι) ℂ) :
      eval z (aeval F r) =
        eval (fun y => ((U y.1 : Matrix ι ι ℂ) * Matrix.diagonal (fun k => z (y.1, k)) * V y.1)
          y.2.1 y.2.2) r := by
    have hcomp : (eval z).comp (algebraMap ℂ (MvPolynomial (Φ × ι) ℂ)) = RingHom.id ℂ := by
      ext; simp
    rw [map_aeval, hcomp]
    -- `eval y` is `eval₂Hom (RingHom.id ℂ) y` by definition.
    refine congrArg (fun y => eval y r) (_root_.funext fun ⟨τ, i, j⟩ => ?_)
    rw [Matrix.mul_apply]
    simp only [F, map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- The unit circle is infinite, being connected with more than one point.
  have hS : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0
        zero_le_one).isPreconnected ⟨1, by simp, -1, by simp, by norm_num⟩
  have hpq : aeval F p = aeval F q := by
    refine MvPolynomial.funext_set (fun _ => Metric.sphere (0 : ℂ) 1) (fun _ => hS)
      fun z hz => ?_
    rw [hF, hF]
    refine h (fun τ => (U τ : Matrix ι ι ℂ) * Matrix.diagonal (fun k => z (τ, k)) * V τ)
      fun τ => mul_mem (mul_mem (U τ).property ?_) (V τ).property
    refine Matrix.diagonal_mem_unitary.mpr (Pi.mem_unitary_iff.mpr fun k => ?_)
    -- A complex number of modulus one is unitary: `conj z * z = ‖z‖ ^ 2 = 1`.
    rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
      mem_sphere_zero_iff_norm.mp (hz (τ, k) trivial)]
    norm_num
  have hx : x = fun y => ((U y.1 : Matrix ι ι ℂ) * Matrix.diagonal (d y.1) * V y.1) y.2.1 y.2.2 :=
    _root_.funext fun ⟨τ, i, j⟩ => congrFun (congrFun (hA τ) i) j
  rw [hx, ← hF (fun y => d y.1 y.2) p, ← hF (fun y => d y.1 y.2) q, hpq]

/-- **The unitary group is Zariski dense in the complex matrices.** Two polynomials in the entries
of a square complex matrix that take the same value at every unitary matrix are equal. -/
theorem eq_of_eval_eq_on_unitaryGroup {p q : MvPolynomial (ι × ι) ℂ}
    (h : ∀ U ∈ Matrix.unitaryGroup ι ℂ,
      eval (fun ij => U ij.1 ij.2) p = eval (fun ij => U ij.1 ij.2) q) :
    p = q := by
  let e : ι × ι ≃ Unit × ι × ι := (Equiv.punitProd (ι × ι)).symm
  apply (renameEquiv ℂ e).injective
  refine eq_of_eval_eq_on_pi_unitaryGroup fun U hU => ?_
  simpa only [renameEquiv_apply, eval_rename, Function.comp_def, e, Equiv.punitProd_symm_apply]
    using h (U ()) (hU ())

end MvPolynomial

namespace TauCeti

open _root_.Matrix MvPolynomial

/-- A polynomial `f` in square complex matrices indexed by `Φ` whose value at `xᵀ` is
`a * ∏ τ, det (x τ) ^ c τ` for all unitary `x : Φ → unitaryGroup n ℂ` equals
`a • ∏ τ, det (Z τ) ^ c τ`, where `Z τ` is the matrix of variables `(i, j) ↦ X (τ, i, j)`. -/
theorem eq_smul_det_pow_of_unitary {Φ n : Type*} [Fintype n] [DecidableEq n] [Fintype Φ]
    (c : Φ → ℕ) {f : MvPolynomial (Φ × n × n) ℂ} {a : ℂ}
    (hf : ∀ x : Φ → Matrix.unitaryGroup n ℂ,
      f.eval (fun y ↦ (x y.1 : Matrix n n ℂ) y.2.2 y.2.1) =
        a * ∏ τ : Φ, (x τ : Matrix n n ℂ).det ^ c τ) :
    f = a • ∏ τ : Φ, (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det ^ c τ := by
  let swap : Φ × n × n ≃ Φ × n × n := Equiv.prodCongr (Equiv.refl Φ) (Equiv.prodComm n n)
  apply (MvPolynomial.renameEquiv ℂ swap).injective
  refine MvPolynomial.eq_of_eval_eq_on_pi_unitaryGroup fun U hU ↦ ?_
  let u : Φ → Matrix.unitaryGroup n ℂ := fun τ ↦ ⟨U τ, hU τ⟩
  have hdet (τ : Φ) :
      eval (fun y ↦ U y.1 y.2.2 y.2.1)
        (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)).det = (U τ).det := by
    rw [RingHom.map_det]
    have hmat : (RingHom.mapMatrix (eval (fun y ↦ U y.1 y.2.2 y.2.1)))
        (Matrix.of fun i j : n ↦ X (R := ℂ) (τ, i, j)) = (U τ)ᵀ := by
      ext i j
      simp
    rw [hmat, det_transpose]
  have hswap (x : Φ × n × n) : swap x = (x.1, x.2.2, x.2.1) := by
    simp [swap, Prod.map_apply', Prod.swap]
  simp only [renameEquiv_apply, smul_eq_C_mul, map_mul, eval_C, map_prod, map_pow, eval_rename,
    Function.comp_def, hswap]
  rw [hf u]
  congr 1
  refine Finset.prod_congr rfl fun τ _ ↦ ?_
  rw [hdet τ]

end TauCeti

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
