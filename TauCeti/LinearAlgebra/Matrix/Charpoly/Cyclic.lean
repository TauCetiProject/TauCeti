/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import TauCeti.LinearAlgebra.Charpoly.Cyclic

/-!
# Characteristic polynomials via cyclic vectors

If a monic polynomial `p` of degree `n` annihilates an `n × n` matrix `M` over a commutative ring
and the first `n` powers of `M` carry `e₀` to `e₀, …, eₙ₋₁`, then `M.charpoly = p`, reduced via
`Matrix.charpoly_toLin'` to
`LinearMap.charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_linearIndependent_pow`.

## Main results

* `Matrix.charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single`: a monic
  annihilating polynomial of degree `n` with standard-basis orbit of `e₀` equals the
  characteristic polynomial.
-/

public section

open Polynomial

namespace Matrix

/-- **Cyclic-vector criterion for the characteristic polynomial.** If `p` is monic of degree `n`,
annihilates `M`, and the first `n` powers of `M` carry `e₀` to the standard basis vectors `eₘ`,
then `M.charpoly = p`. -/
theorem charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single {n : ℕ} {R : Type*}
    [CommRing R] (hn : 0 < n) {M : Matrix (Fin n) (Fin n) R} {p : R[X]}
    (hp : p.IsMonicOfDegree n) (hann : aeval M p = 0)
    (hcyc : ∀ m (hm : m < n), M ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1) :
    M.charpoly = p := by
  nontriviality R
  rw [← Matrix.charpoly_toLin']
  have hfin : Module.finrank R (Fin n → R) = n := Module.finrank_fin_fun R
  have hlin : M.toLin' = Matrix.toLinAlgEquiv' M :=
    LinearMap.ext fun v => by rw [Matrix.toLin'_apply, Matrix.toLinAlgEquiv'_apply]
  have hann' : aeval M.toLin' p = 0 := by
    rw [hlin, Polynomial.aeval_algHom_apply, hann, map_zero]
  have hli : LinearIndependent R fun i : Fin (Module.finrank R (Fin n → R)) ↦
      (M.toLin' ^ (i : ℕ)) (Pi.single ⟨0, hn⟩ 1) := by
    have hvec : (fun i : Fin (Module.finrank R (Fin n → R)) ↦
        (M.toLin' ^ (i : ℕ)) (Pi.single ⟨0, hn⟩ 1)) =
        fun i : Fin (Module.finrank R (Fin n → R)) ↦ Pi.single (Fin.cast hfin i) (1 : R) := by
      ext i j
      rw [← Matrix.toLin'_pow, Matrix.toLin'_apply, hcyc i (Nat.lt_of_lt_of_eq i.isLt hfin)]
      simp only [Fin.cast]
    rw [hvec]
    exact (Pi.linearIndependent_single_one (Fin n) R).comp (Fin.cast hfin) (Fin.cast_injective hfin)
  exact LinearMap.charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_linearIndependent_pow
    (by rwa [hfin]) hann' hli

end Matrix
