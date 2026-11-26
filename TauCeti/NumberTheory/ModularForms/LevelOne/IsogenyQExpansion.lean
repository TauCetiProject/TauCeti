/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.QExpansion.Affine

/-!
# Width-`n` Laurent `q`-expansions of `j` along upper-triangular representatives

For a positive integer `n` and an upper-triangular integral matrix `A = !![a, b; 0, d] ∈ reps n`
(`a d = n`, `0 < a`, `0 ≤ b < d`), the function `τ ↦ j (A • τ) = j ((a τ + b) / d)` on the upper
half-plane has a meromorphic cusp function at period `n`, and its Laurent `q`-expansion in
`q_n = exp (2 π i τ / n)` is obtained from the width-one Laurent `q`-expansion of `j` by rescaling
by the root of unity `exp (2 π i b / d)` and substituting `X ↦ X ^ (a ^ 2)`.

These specializations of `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_comp_toGLReal_smul` and
`TauCeti.UpperHalfPlane.laurentQExpansion_comp_toGLReal_smul` to the modular invariant `j` provide
the shared `q`-expansion input for both the integrality of singular moduli and the construction of
the classical modular polynomial `Φ_n(X, Y)`.

## Main results

* `TauCeti.ModularForm.meromorphicAt_cuspFunction_j_toGLReal_smul`: `τ ↦ j (A • τ)` has a
  meromorphic cusp function at period `n` for `A ∈ reps n`.
* `TauCeti.ModularForm.laurentQExpansion_j_toGLReal_smul`: the width-`n` Laurent `q`-expansion of
  `τ ↦ j (A • τ)` for `A ∈ reps n`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C.
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §2.
-/

public section

open Function UpperHalfPlane
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

open FixedDetMatrices

variable {n : ℕ} [NeZero n] {A : FixedDetMatrix (Fin 2) ℤ n}

/-- Along an upper-triangular representative `A = !![a, b; 0, d] ∈ reps n`, the function
`τ ↦ j (A • τ)` has a meromorphic cusp function at period `n`. -/
theorem meromorphicAt_cuspFunction_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction n fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_comp_toGLReal_smul
    (Int.natCast_pos.2 (NeZero.pos n)) hA periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j

/-- **Width-`n` Laurent `q`-expansion of `j(A • τ)`.** For an upper-triangular representative
`A = !![a, b; 0, d] ∈ reps n`, the width-`n` Laurent `q`-expansion of `j(A • τ)` is the width-one
expansion of `j` rescaled by `exp (2 π i b / d)` and expanded by `X ↦ X ^ (a ^ 2)`. -/
theorem laurentQExpansion_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) :
    UpperHalfPlane.laurentQExpansion n
        (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ ((A.val 0 0).natAbs ^ 2).toPNat'
        (TauCeti.LaurentSeries.rescale
          (Units.mk0 (𝕢 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ)) (Periodic.qParam_ne_zero _))
          (UpperHalfPlane.laurentQExpansion 1 j)) :=
  TauCeti.UpperHalfPlane.laurentQExpansion_comp_toGLReal_smul
    (Int.natCast_pos.2 (NeZero.pos n)) hA periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j

end TauCeti.ModularForm
