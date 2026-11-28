/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConleyZehnder
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Geometry.Symplectic.Complex.ImInner.Basis
import TauCeti.Geometry.Symplectic.ConleyZehnder

/-!
# The Conley–Zehnder index of a constant orbit in a Hermitian space

Let `F` be a finite-dimensional complex inner product space of complex dimension `n`, with the
symplectic form `ω = Im ⟪·, ·⟫_ℂ`, and let `H : F → ℝ` be a `C²` autonomous Hamiltonian. At a
point `p` where the Hessian of `H` is nondegenerate, for instance a nondegenerate critical point,
whose constant loop is then a one-periodic orbit of `H`, this file computes the Conley–Zehnder
index of the constant path at `p` (`TauCeti.SymplecticForm.orbitConleyZehnderIndex`) whenever the
linearized Hamiltonian vector field is small, `‖dX_H(p)‖ < 2π`:

`CZ(p) = ind_p(H) - n`

(`TauCeti.SymplecticForm.orbitConleyZehnderIndex_const_eq_morseIndex_sub_finrank`), where
`ind_p(H)` is the Morse index (`TauCeti.morseIndex`). The bound is on the operator norm of
`F`, and no small multiple of `H` is taken: for instance `a ‖z‖²` with `0 < a < π` has
`‖dX_H(0)‖ = 2a < 2π`, its minimum at the origin has Morse index `0`, and the index is `-n`, as
`TauCeti.orbitConleyZehnderIndex_mul_norm_sq_of_mem_Ioo` finds by a direct computation. The bound
cannot be dropped: for `a = π` the time-one map is the identity.

The proof reads the linearized flow `t ↦ exp (t dX_H(p))` in the real basis `(i e, e)` attached to
an orthonormal basis `e` of `F` (`OrthonormalBasis.imInnerSymplecticBasis`), which is both a
symplectic basis of `ω` and orthonormal for the real inner product `Re ⟪·, ·⟫_ℂ`. In it the matrix
of `dX_H(p)` has the operator norm of `dX_H(p)` (`ContinuousLinearMap.l2_opNorm_toMatrix`), and
`ω(dX_H(p) w, u)` is the Hessian of `H` at `p`, so the coordinate-free signature axiom
`TauCeti.SymplecticForm.conleyZehnderIndex_eq_sigNeg_sub` gives the negative index of inertia of
the Hessian, which is the Morse index, minus `n`.

In the grading `μ = CZ` of the coordinate-free index, read in symplectic bases in which `ω` has the
matrix `J`, this is the normalization `μ(p) = ind_p(H) - n` of the generators of the Floer complex
of a Hamiltonian with small linearized vector fields at its critical points.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the normalization of the Conley–Zehnder index and the
  grading of the Floer complex of a small Morse function).
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844.
-/

public section

open Function Matrix Module
open scoped Matrix.Norms.L2Operator

namespace TauCeti.SymplecticForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F}

/-- **The Conley–Zehnder index of a constant orbit of a Hamiltonian with small linearization.**
Let `F` be a finite-dimensional complex inner product space of complex dimension `n` whose
symplectic form `ω` is `Im ⟪·, ·⟫`, and let `H : F → ℝ` be `C²`. At a point `p` where the Hessian
of `H` is nondegenerate and `‖dX_H(p)‖ < 2π`, the constant path at `p` has Conley–Zehnder index
`ind_p(H) - n`, where `ind_p(H)` is the Morse index. -/
theorem orbitConleyZehnderIndex_const_eq_morseIndex_sub_finrank
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : F → ℝ}
    (hH : ContDiff ℝ 2 (uncurry fun (_ : ℝ) ↦ H)) {p : F}
    (hp : (hessianQuadraticForm H p).Nondegenerate)
    (h2π : ‖fderiv ℝ (ω.hamiltonianVectorField H) p‖ < 2 * Real.pi) :
    ω.orbitConleyZehnderIndex hH (continuous_const : Continuous fun _ : ℝ ↦ p) =
      morseIndex H p - finrank ℂ F := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hH₂ : ContDiffAt ℝ 2 H p :=
    (hH.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)).contDiffAt
  -- The real basis `(i e, e)` is orthonormal, and `ω` has the matrix `J` in it.
  set e := stdOrthonormalBasis ℂ F
  set b := e.imInnerSymplecticBasis
  have hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J _ ℝ := by
    rw [← e.toMatrix_imInnerSymplecticForm]
    congr 1
    ext v w
    simp [hω]
  -- `ω(dX_H(p) w, u)` is the Hessian of `H` at `p`.
  set L := fderiv ℝ (ω.hamiltonianVectorField H) p
  have hLQ (w u : F) :
      ω (L w) u = QuadraticMap.associated (R := ℝ) (hessianQuadraticForm H p) w u := by
    rw [associated_hessianQuadraticForm hH₂]
    exact ω.apply_fderiv_hamiltonianVectorField
      ((hH₂.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) w u
  have hL : ‖LinearMap.toMatrix b b L‖ < 2 * Real.pi := by
    rwa [← b.toBasis_toOrthonormalBasis e.orthonormal_imInnerSymplecticBasis,
      ContinuousLinearMap.l2_opNorm_toMatrix]
  -- Along the constant path the linearized flow is `t ↦ exp (t L)`.
  rw [orbitConleyZehnderIndex_def, ω.conleyZehnderIndex_eq_sigNeg_sub hLQ
      (LinearMap.BilinForm.isSymm_def.2 (QuadraticMap.associated_isSymm ℝ _))
      (QuadraticMap.nondegenerate_associated_iff.2 hp) hb hL _ _
      (fun t ↦ by simp [L, dysonSeriesLeft_const]),
    QuadraticMap.toQuadraticMap_associated, morseIndex_def, finrank_real_of_complex]
  push_cast
  ring

end TauCeti.SymplecticForm
