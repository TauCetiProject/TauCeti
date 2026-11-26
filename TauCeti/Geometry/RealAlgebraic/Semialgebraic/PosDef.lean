/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import TauCeti.LinearAlgebra.Matrix.MvPolynomial
import TauCeti.LinearAlgebra.Matrix.PosDef.Sylvester

/-!
# Semialgebraicity of the positive-definite cone

In matrix-entry coordinates `Fin n × Fin n → K` over a linearly ordered field `K` with trivial star,
Sylvester's criterion (`Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos`) expresses positive
definiteness by symmetry equations and strict positivity of the leading principal minor polynomials,
so the positive-definite cone is a quantifier-free semialgebraic set.

## Main results

* `TauCeti.isSemialgebraic_setOf_posDef`: the positive-definite matrices form a semialgebraic set
  in entry coordinates.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.2.5 (Sylvester's criterion).
-/

public section

namespace TauCeti

/-- In matrix-entry coordinates `Fin n × Fin n → K`, the set of positive-definite `n × n` matrices
over a linearly ordered field with trivial star is semialgebraic. -/
theorem isSemialgebraic_setOf_posDef {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [StarRing K] [TrivialStar K] (n : ℕ) :
    IsSemialgebraic {s : Fin n × Fin n → K | (Matrix.of (Function.curry s)).PosDef} := by
  let ev := MvPolynomial.eval (R := K) (σ := Fin n × Fin n)
  let M := Matrix.mvPolynomialX (Fin n) (Fin n) K
  have hdet {m : ℕ} (f : Fin m → Fin n) (s) :
      ((Matrix.of (Function.curry s)).submatrix f f).det = ev s ((M.submatrix f f).det) := by
    have hs : Function.uncurry (Matrix.of (Function.curry s)) = s := by
      ext ⟨i, j⟩; simp [Function.uncurry, Function.curry]
    simpa [ev, M, MvPolynomial.aeval_eq_eval, hs] using
      (Matrix.aeval_det_submatrix_mvPolynomialX (R := K) (Matrix.of (Function.curry s)) f f).symm
  have heq : {s : Fin n × Fin n → K | (Matrix.of (Function.curry s)).PosDef} =
      (⋂ p : Fin n × Fin n, {s | ev s (MvPolynomial.X p) = ev s (MvPolynomial.X p.swap)}) ∩
      (⋂ k : Fin n, {s | 0 < ev s ((M.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
        (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det)}) := by
    ext s
    simp only [ev, Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos, Matrix.IsSymm.ext_iff,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Prod.forall, MvPolynomial.eval_X,
      Prod.swap_prod_mk, Matrix.of_apply, Function.curry_apply, ← hdet]
    exact and_congr ⟨fun h i j ↦ (h i j).symm, fun h i j ↦ (h i j).symm⟩ Iff.rfl
  exact heq ▸ (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_pos _)

end TauCeti
