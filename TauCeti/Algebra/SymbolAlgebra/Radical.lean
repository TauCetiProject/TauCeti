/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.SymbolAlgebra.MatrixCorner
public import Mathlib.FieldTheory.Minpoly.Basic
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The matrix corner selected by a radical

For a specified root `α ^ n = a` in an arbitrary field extension, the degree `d` of its
minimal polynomial divides `n`. The scalar `c = α ^ d` defines the corresponding smaller
symbol algebra, and the degree `n` algebra is a matrix algebra over it. The equivalence
has the prescribed diagonal and forward-shift generator images, including when `d = 1`
or `n / d = 1`. The degree-one equivalence supplies the base-field convention for
the selected corner.

## References

* C. A. Weibel, *The K-book*, III.6.9 and Remark 6.10.4.
-/

public section

open IntermediateField Module

namespace TauCeti

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {n : ℕ} [NeZero n] {ζ a b : F} {α : E}

/-- The matrix corner selected by the specified radical `α`. The corner degree is its
minimal-polynomial degree, and its first parameter is the scalar represented by `α ^ d`.
The two generator equations fix the equivalence and the direction of the forward shift.
No irreducibility assumption on `X ^ n - C a` is required. -/
theorem symbolAlgebra_matrix_corner (hζ : IsPrimitiveRoot ζ n)
    (hα : α ^ n = algebraMap F E a) (ha : a ≠ 0) (hb : b ≠ 0) :
    let d := (minpoly F α).natDegree
    let s := n / d
    d ∣ n ∧ ∃ c : F, α ^ d = algebraMap F E c ∧ c ^ s = a ∧
      ∃ e : SymbolAlgebra n ζ a b ≃ₐ[F]
          Matrix (Fin s) (Fin s) (SymbolAlgebra d (ζ ^ s) c b),
        e SymbolAlgebra.x = SymbolAlgebra.matrixCornerX s ζ SymbolAlgebra.x ∧
        e SymbolAlgebra.y = Matrix.weightedShift s SymbolAlgebra.y := by
  have hgen := adjoin_adjoinSimple_gen_eq_top (F := F) α
  have hroot : AdjoinSimple.gen F α ^ n = algebraMap F F⟮α⟯ a :=
    AdjoinSimple.gen_pow_eq_algebraMap_iff.2 hα
  obtain ⟨_, _, hdvd, _⟩ := exists_forall_mem_zpowers_apply_eq hζ hroot hgen
  obtain ⟨c, hc, hca⟩ := exists_pow_finrank_eq_algebraMap hζ hroot hgen
  have hint : IsIntegral F α :=
    IsIntegral.of_pow (NeZero.pos n) (hα ▸ isIntegral_algebraMap)
  rw [IntermediateField.adjoin.finrank hint] at hdvd hc hca
  let d := (minpoly F α).natDegree
  let s := n / d
  have hd0 : d ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hs0 : s ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hdvd).2 ⟨NeZero.ne n, hd0⟩
  have : NeZero d := ⟨hd0⟩
  have : NeZero s := ⟨hs0⟩
  have hds : d * s = n := Nat.mul_div_cancel' hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hs0] at hca
    exact ha hca.symm
  have hζds : IsPrimitiveRoot ζ (d * s) := hds.symm ▸ hζ
  refine ⟨hdvd, c, AdjoinSimple.gen_pow_eq_algebraMap_iff.1 hc, hca, ?_⟩
  have he : ∃ e : SymbolAlgebra (d * s) ζ (c ^ s) b ≃ₐ[F]
        Matrix (Fin s) (Fin s) (SymbolAlgebra d (ζ ^ s) c b),
      e SymbolAlgebra.x = SymbolAlgebra.matrixCornerX s ζ SymbolAlgebra.x ∧
      e SymbolAlgebra.y = Matrix.weightedShift s SymbolAlgebra.y :=
    ⟨SymbolAlgebra.algEquivMatrixOfPow d s hζds hc0 hb,
      SymbolAlgebra.algEquivMatrixOfPow_x d s hζds hc0 hb,
      SymbolAlgebra.algEquivMatrixOfPow_y d s hζds hc0 hb⟩
  rw [hds, hca] at he
  exact he

end TauCeti
