/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Fiberwise
public import TauCeti.Geometry.Symplectic.Hamiltonian.Transport
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Hamiltonian vector fields on the cotangent space and the two sign conventions

On the linear cotangent space `T*V = V × V'`, with tautological one-form `λ = p dq`
(`TauCeti.cotangentLiouvilleForm`), Tau Ceti uses the symplectic form `ω = -dλ`
(`TauCeti.strongDualCotangentSymplecticForm`) and Hamiltonian vector fields with
`ω(X_H, ·) = dH` (`TauCeti.SymplecticForm.hamiltonianVectorField`). Much of the literature on
cotangent bundles, for instance Barraud–Damian–Humilière–Oancea, uses instead the form
`ω_src = dλ` and the convention `ω_src(X, ·) = -dH`. This file compares the two.

* **Hamilton's equations.** If `dH(x)(δq, δp) = α(δq) + δp(b)`, so that `α = ∂H/∂q` and
  `b = ∂H/∂p`, then `X_H(x) = (b, -α)`: `q' = ∂H/∂p`, `p' = -∂H/∂q`
  (`TauCeti.strongDualCotangentSymplecticForm_hamiltonianVectorField`).
* **The other form.** The form `dλ` is the rescaling of `ω` by `-1`
  (`TauCeti.extDeriv_cotangentLiouvilleForm_apply_eq_rescale`). So the field `X` with
  `dλ(X, ·) = -dH` is the Hamiltonian vector field of `-H` for `dλ` in our convention, which by
  `TauCeti.SymplecticForm.hamiltonianVectorField_rescale_neg_one` is the Hamiltonian vector field
  of `H` for `ω`: the two sign changes cancel.
* **Transport along the fibrewise negation.** The fibrewise negation `ν(q, p) = (q, -p)`
  (`TauCeti.cotangentFiberNeg`) is a symplectomorphism from `(T*V, dλ)` to `(T*V, ω)`
  (`TauCeti.isSymplectomorphism_cotangentFiberNeg`). It carries the field `X` with
  `dλ(X, ·) = -dH` to the Hamiltonian vector field of `-H ∘ ν⁻¹` for `ω`
  (`TauCeti.cotangentFiberNeg_hamiltonianVectorField`). So data stated for `(T*V, dλ)` in the
  convention `ω_src(X, ·) = -dH` is read for `(T*V, ω)` in our convention by transporting along
  `ν` and replacing the Hamiltonian `H` by `-H ∘ ν⁻¹`.

On `T*ℝ`, with position `q = x.1` and momentum `p = x.2 1`, the canonical form satisfies
`ω(∂_q, ∂_p) = 1` (`TauCeti.strongDualCotangentSymplecticForm_real_dq_dp`), and the transport is
checked on two Hamiltonians.

* For the kinetic energy `H = p² / 2`, the field with `dλ(X, ·) = -dH` is `p ∂_q`
  (`TauCeti.hamiltonianVectorField_rescale_neg_one_neg_real_momentum_sq_div_two`). Its image under
  `ν` is the Hamiltonian vector field of `-H ∘ ν⁻¹ = -p² / 2` for `ω`
  (`TauCeti.cotangentFiberNeg_hamiltonianVectorField_real_momentum_sq_div_two`), which is `-p ∂_q`
  (`TauCeti.hamiltonianVectorField_neg_real_momentum_sq_div_two`).
* For the harmonic oscillator `H = (q² + p²) / 2`, the field is `p ∂_q - q ∂_p`
  (`TauCeti.hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two`), and its
  image under `ν`
  (`TauCeti.cotangentFiberNeg_hamiltonianVectorField_real_sq_add_momentum_sq_div_two`) is
  `-p ∂_q + q ∂_p`
  (`TauCeti.hamiltonianVectorField_neg_real_sq_add_momentum_sq_div_two`).

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Hamiltonian vector fields) and Section 3.2 (cotangent bundles).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2, for the convention
  `ω(X_H, ·) = -dH` with `ω = dλ`.
-/

public section

noncomputable section

namespace TauCeti

open SymplecticForm

/-! ### Hamilton's equations and the two conventions -/

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exterior derivative `dλ` of the Liouville form is the rescaling by `-1` of the canonical
symplectic form `ω = -dλ`. -/
theorem extDeriv_cotangentLiouvilleForm_apply_eq_rescale (x : V × StrongDual ℝ V)
    (v : Fin 2 → V × StrongDual ℝ V) :
    extDeriv cotangentLiouvilleForm x v =
      strongDualCotangentSymplecticForm.rescale (-1) (by norm_num) (v 0) (v 1) := by
  rw [rescale_apply, ← neg_extDeriv_cotangentLiouvilleForm_apply, neg_one_mul, neg_neg]

/-- The fibrewise negation `ν` is a symplectomorphism from the cotangent space with the form
`dλ`, the rescaling of `ω` by `-1`, to the cotangent space with the form `ω = -dλ`. -/
theorem isSymplectomorphism_cotangentFiberNeg :
    (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).IsSymplectomorphism
      strongDualCotangentSymplecticForm (cotangentFiberNeg (V := V)).toLinearEquiv := by
  rw [isSymplectomorphism_iff]
  intro v w
  rw [ContinuousLinearEquiv.coe_toLinearEquiv, strongDualCotangentSymplecticForm_cotangentFiberNeg,
    rescale_apply, neg_one_mul]

variable [FiniteDimensional ℝ V]

/-- **Hamilton's equations on the cotangent space.** If the derivative of `H` at `x` is
`(δq, δp) ↦ α(δq) + δp(b)`, so that `α = ∂H/∂q` and `b = ∂H/∂p`, then the Hamiltonian vector
field of `H` at `x` is `(b, -α)`. -/
theorem strongDualCotangentSymplecticForm_hamiltonianVectorField
    {H : V × StrongDual ℝ V → ℝ} {x : V × StrongDual ℝ V} {α : StrongDual ℝ V} {b : V}
    (hH : HasFDerivAt H (α.comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)) +
      (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))) x) :
    strongDualCotangentSymplecticForm.hamiltonianVectorField H x = (b, -α) := by
  rw [eq_comm, eq_hamiltonianVectorField_iff, hH.fderiv]
  intro v
  simp only [strongDualCotangentSymplecticForm_apply, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.apply_apply, neg_apply]
  ring

/-- **Transport along the fibrewise negation.** The fibrewise negation `ν` carries the field `X`
with `dλ(X, ·) = -dH` at `x` to the Hamiltonian vector field of `-H ∘ ν⁻¹ = -H ∘ ν` for
`ω = -dλ` at `ν x`. -/
theorem cotangentFiberNeg_hamiltonianVectorField (H : V × StrongDual ℝ V → ℝ)
    (x : V × StrongDual ℝ V) :
    cotangentFiberNeg
        ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
          (-H) x) =
      strongDualCotangentSymplecticForm.hamiltonianVectorField (-(H ∘ cotangentFiberNeg))
        (cotangentFiberNeg x) := by
  have h := isSymplectomorphism_cotangentFiberNeg.map_hamiltonianVectorField (-H) x
  rw [ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    cotangentFiberNeg_symm] at h
  rw [h, Pi.neg_comp]

end General

/-! ### Checks on `T*ℝ` -/

section Real

/-- On `T*ℝ`, the canonical symplectic form pairs the position direction `∂_q = (1, 0)` with the
momentum direction `∂_p = (0, 1)` to `1`: `ω(∂_q, ∂_p) = 1`. -/
theorem strongDualCotangentSymplecticForm_real_dq_dp :
    strongDualCotangentSymplecticForm ((1 : ℝ), (0 : StrongDual ℝ ℝ)) (0, 1) = 1 := by
  simp

/-- The momentum coordinate `p = x.2 1` of `T*ℝ` has derivative `(δq, δp) ↦ δp(1)`. -/
private theorem hasFDerivAt_momentum (x : ℝ × StrongDual ℝ ℝ) :
    HasFDerivAt (fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1)
      ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) x :=
  ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
    (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))).hasFDerivAt

/-- The derivative of a function of `(q, p)` with partial derivatives `a` in `q` and `c` in `p`
is `(δq, δp) ↦ a δq + δp(c)`, the form used in Hamilton's equations. -/
private theorem hasFDerivAt_real_of_partials {H : ℝ × StrongDual ℝ ℝ → ℝ}
    {x : ℝ × StrongDual ℝ ℝ} {a c : ℝ}
    (hH : HasFDerivAt H (a • ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ) +
      c • (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) x) :
    HasFDerivAt H ((a • ContinuousLinearMap.id ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)) +
      (ContinuousLinearMap.apply ℝ ℝ c).comp (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) x := by
  convert hH using 1
  ext v
  · simp
  · simpa [mul_comm] using (Dual.apply_one_mul_eq (v : Module.Dual ℝ ℝ) c).symm

/-- The kinetic energy `p² / 2` has partial derivatives `0` in `q` and `p` in `p`. -/
private theorem hasFDerivAt_momentum_sq_div_two (x : ℝ × StrongDual ℝ ℝ) :
    HasFDerivAt (fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1 ^ 2 / 2)
      (((0 : ℝ) • ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)) +
        (ContinuousLinearMap.apply ℝ ℝ (x.2 1)).comp
          (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) x := by
  refine hasFDerivAt_real_of_partials ?_
  have h := HasFDerivAt.mul_const (HasFDerivAt.pow (hasFDerivAt_momentum x) 2) (2⁻¹ : ℝ)
  convert h using 1
  · funext y
    simp [div_eq_mul_inv]
  · ext v
    · simp
    · simp
      ring

/-- **The kinetic energy in the convention of `dλ`.** For `H = p² / 2` on `T*ℝ`, the field `X`
with `dλ(X, ·) = -dH` is `p ∂_q`. -/
theorem hamiltonianVectorField_rescale_neg_one_neg_real_momentum_sq_div_two
    (x : ℝ × StrongDual ℝ ℝ) :
    (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1 ^ 2 / 2) x =
      (x.2 1, 0) := by
  rw [hamiltonianVectorField_rescale_neg_one, neg_neg,
    strongDualCotangentSymplecticForm_hamiltonianVectorField (hasFDerivAt_momentum_sq_div_two x)]
  simp

/-- **The negated kinetic energy in the convention of `ω`.** For `-p² / 2` on `T*ℝ`, the
Hamiltonian vector field for `ω = -dλ`, with `ω(X, ·) = dH`, is `-p ∂_q`. -/
theorem hamiltonianVectorField_neg_real_momentum_sq_div_two (x : ℝ × StrongDual ℝ ℝ) :
    strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1 ^ 2 / 2) x =
      (-x.2 1, 0) := by
  rw [hamiltonianVectorField_neg,
    strongDualCotangentSymplecticForm_hamiltonianVectorField (hasFDerivAt_momentum_sq_div_two x)]
  simp

/-- **The kinetic energy across the two conventions.** The fibrewise negation carries the field
`p ∂_q` of `H = p² / 2` for `dλ`, in the convention `dλ(X, ·) = -dH`, to the Hamiltonian vector
field of `-H ∘ ν⁻¹ = -p² / 2` for `ω`, in the convention `ω(X, ·) = dH`, which is `-p ∂_q`
(`TauCeti.hamiltonianVectorField_neg_real_momentum_sq_div_two`). -/
theorem cotangentFiberNeg_hamiltonianVectorField_real_momentum_sq_div_two (x : ℝ × StrongDual ℝ ℝ) :
    cotangentFiberNeg
        ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
          (-fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1 ^ 2 / 2) x) =
      strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ y.2 1 ^ 2 / 2) (cotangentFiberNeg x) := by
  rw [cotangentFiberNeg_hamiltonianVectorField]
  congr 2
  funext y
  simp

/-- The harmonic oscillator `(q² + p²) / 2` has partial derivatives `q` in `q` and `p` in `p`. -/
private theorem hasFDerivAt_sq_add_momentum_sq_div_two (x : ℝ × StrongDual ℝ ℝ) :
    HasFDerivAt (fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)
      ((x.1 • ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)) +
        (ContinuousLinearMap.apply ℝ ℝ (x.2 1)).comp
          (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))) x := by
  refine hasFDerivAt_real_of_partials ?_
  have h := HasFDerivAt.mul_const (HasFDerivAt.add (HasFDerivAt.pow (hasFDerivAt_fst (p := x)) 2)
    (HasFDerivAt.pow (hasFDerivAt_momentum x) 2)) (2⁻¹ : ℝ)
  convert h using 1
  · funext y
    simp [div_eq_mul_inv]
  · ext v
    · simp
    · simp
      ring

/-- **The harmonic oscillator in the convention of `dλ`.** For `H = (q² + p²) / 2` on `T*ℝ`, the
field `X` with `dλ(X, ·) = -dH` is `p ∂_q - q ∂_p`. -/
theorem hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two
    (x : ℝ × StrongDual ℝ ℝ) :
    (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) x =
      (x.2 1, -x.1 • ContinuousLinearMap.id ℝ ℝ) := by
  rw [hamiltonianVectorField_rescale_neg_one, neg_neg,
    strongDualCotangentSymplecticForm_hamiltonianVectorField
      (hasFDerivAt_sq_add_momentum_sq_div_two x),
    ← neg_smul]

/-- **The negated harmonic oscillator in the convention of `ω`.** For `-(q² + p²) / 2` on `T*ℝ`,
the Hamiltonian vector field for `ω = -dλ`, with `ω(X, ·) = dH`, is `-p ∂_q + q ∂_p`. -/
theorem hamiltonianVectorField_neg_real_sq_add_momentum_sq_div_two (x : ℝ × StrongDual ℝ ℝ) :
    strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) x =
      (-x.2 1, x.1 • ContinuousLinearMap.id ℝ ℝ) := by
  rw [hamiltonianVectorField_neg,
    strongDualCotangentSymplecticForm_hamiltonianVectorField
      (hasFDerivAt_sq_add_momentum_sq_div_two x)]
  simp

/-- **The harmonic oscillator across the two conventions.** The fibrewise negation carries the
field `p ∂_q - q ∂_p` of `H = (q² + p²) / 2` for `dλ`, in the convention `dλ(X, ·) = -dH`, to the
Hamiltonian vector field of `-H ∘ ν⁻¹ = -H` for `ω`, in the convention `ω(X, ·) = dH`, which is
`-p ∂_q + q ∂_p` (`TauCeti.hamiltonianVectorField_neg_real_sq_add_momentum_sq_div_two`). -/
theorem cotangentFiberNeg_hamiltonianVectorField_real_sq_add_momentum_sq_div_two
    (x : ℝ × StrongDual ℝ ℝ) :
    cotangentFiberNeg
        ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
          (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) x) =
      strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) (cotangentFiberNeg x) := by
  rw [cotangentFiberNeg_hamiltonianVectorField]
  congr 2
  funext y
  simp

end Real

end TauCeti
