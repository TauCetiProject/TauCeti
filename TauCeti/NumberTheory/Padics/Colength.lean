/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.Algebra.Module.Submodule.ColengthDvd

/-!
# Prime-adic determinant bounds from colength

If a submodule has colength dividing `p ^ j` in a second submodule, every finite family in
that second submodule admits a matrix of row combinations in the first. Under any coefficient
map to an algebraic closure of `ℚ_[p]`, the determinant of this matrix has norm at least
`p ^ (-j)`. This turns a local colength bound into a determinant witness for comparing
covolumes at prime-adic embeddings.

The local implication is used in `New.TwistedLattice.indexLe_of_colengthDvd` in
`grh/src/New/Reduction/Lattices/TwistedLattice.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

namespace Submodule.ColengthDvd

/-- Colength dividing `p ^ j` supplies a matrix of row combinations with determinant of
prime-adic norm at least `p ^ (-d)` after a coefficient map, for any real budget `d ≥ j`.
For a nonempty family the determinant itself can be chosen to be exactly `p ^ j`. -/
theorem exists_matrix_rpow_le_norm_det {O V I : Type*} [CommRing O]
    [AddCommMonoid V] [Module O V] [Fintype I] [DecidableEq I]
    {M N : Submodule O V} {p : ℕ} [Fact p.Prime] {j : ℕ} {d : ℝ}
    (h : M.ColengthDvd N ((p : O) ^ j)) (f : O →+* PadicAlgCl p) (hj : (j : ℝ) ≤ d)
    {y : I → V} (hy : ∀ i, y i ∈ M) :
    ∃ A : Matrix I I O, (p : ℝ) ^ (-d) ≤ ‖f A.det‖ ∧
      ∀ i, (∑ k, A i k • y k) ∈ N := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  cases isEmpty_or_nonempty I with
  | inl hI =>
    refine ⟨1, ?_, hI.elim⟩
    simpa only [Matrix.det_one, map_one, norm_one] using
      Real.rpow_le_one_of_one_le_of_nonpos hp (by linarith : -d ≤ 0)
  | inr hI =>
    obtain ⟨A, hA, hAy⟩ := h.exists_matrix_det_eq y hy
    refine ⟨A, ?_, hAy⟩
    rw [hA]
    calc
      (p : ℝ) ^ (-d) ≤ (p : ℝ) ^ (-(j : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp (by linarith)
      _ = ‖f ((p : O) ^ j)‖ := by
        simp only [map_pow, map_natCast]
        rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← map_pow,
          PadicAlgCl.norm_extends, Padic.norm_p_pow]
        simp

end Submodule.ColengthDvd
