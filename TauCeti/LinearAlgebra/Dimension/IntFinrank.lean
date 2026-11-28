/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Tactic.GCongr

/-!
# Finrank bounds for quotients and product extensions

This file proves elementary `Module.finrank` upper bounds for a module `B` receiving a surjection
from a finitely generated module `A` over a commutative integral domain `R`, together with the
`B × R` and `B × ℤ` specializations used in the equivariant `S`-unit theorem.

## Main results

* `TauCeti.finrank_le_of_surjective_of_finite`: if `f : A →ₗ[R] B` is surjective and `A` is
  finitely generated over `R`, then `Module.finrank R B ≤ Module.finrank R A`.
* `TauCeti.finrank_prod_self_le_of_surjective`: under the same hypotheses,
  `Module.finrank R (B × R) ≤ Module.finrank R A + 1`.
* `TauCeti.finrank_prod_int_le_of_surjective`: the `R = ℤ` specialization.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean (commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`), file
  `src/Lib/ClassField/GreenbergWiles/SelmerLevels.lean` (declaration
  `New.finrank_prod_int_le_of_surjective`); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

universe u

namespace TauCeti

/-- If `f : A →ₗ[R] B` is surjective and `A` is finitely generated over an integral domain `R`,
then `Module.finrank R B ≤ Module.finrank R A`. -/
theorem finrank_le_of_surjective_of_finite {R A B : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] [Module.Finite R A]
    {f : A →ₗ[R] B} (hf : Function.Surjective f) :
    Module.finrank R B ≤ Module.finrank R A := by
  refine Module.finrank_le_of_rank_le ?_
  calc Module.rank R B
      ≤ Module.rank R A := LinearMap.rank_le_of_surjective f hf
    _ = (Module.finrank R A : Cardinal) := (Module.finrank_eq_rank R A).symm

/-- If `f : A →ₗ[R] B` is surjective and `A` is finitely generated over an integral domain `R`,
then `Module.finrank R (B × R) ≤ Module.finrank R A + 1`. -/
theorem finrank_prod_self_le_of_surjective {R A B : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] [Module.Finite R A]
    {f : A →ₗ[R] B} (hf : Function.Surjective f) :
    Module.finrank R (B × R) ≤ Module.finrank R A + 1 := by
  refine Module.finrank_le_of_rank_le ?_
  calc Module.rank R (B × R)
      ≤ Module.rank R A + Module.rank R R := by
        grw [LinearMap.rank_eq_of_surjective LinearMap.fst_surjective, LinearMap.ker_fst,
          rank_range_le, LinearMap.rank_le_of_surjective f hf]
    _ = ((Module.finrank R A + 1 : ℕ) : Cardinal) := by
        simp [Module.finrank_eq_rank]

/-- If an abelian group `B` is a quotient of a finitely generated abelian group `A`, then
`Module.finrank ℤ (B × ℤ) ≤ Module.finrank ℤ A + 1`. -/
theorem finrank_prod_int_le_of_surjective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] {f : A →ₗ[ℤ] B} (hf : Function.Surjective f) :
    Module.finrank ℤ (B × ℤ) ≤ Module.finrank ℤ A + 1 :=
  finrank_prod_self_le_of_surjective hf

end TauCeti
