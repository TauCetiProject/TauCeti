/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star

/-!
# Star symmetry of the Ocneanu trace

For a star-fixed unit parameter `q : Rˣ` in a commutative star ring `R`, conjugating the Ocneanu
trace `ocneanuTrace R q z x` conjugates both the Markov parameter `z` and the element `x`
(`TauCeti.InfiniteTypeAHeckeAlgebra.star_ocneanuTrace`). In particular, when `z` is self-adjoint,
`ocneanuTrace R q z` commutes with `star` (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star`).
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

/-- Conjugating `ocneanuTrace R q z x` conjugates both `z` and `x`. -/
theorem star_ocneanuTrace {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] (z : R) (x : InfiniteTypeAHeckeAlgebra R q) :
    star (ocneanuTrace R q z x) = ocneanuTrace R q (star z) (star x) := by
  let φ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    { toFun y := star (ocneanuTrace R q z (star y))
      map_add' _ _ := by simp
      map_smul' _ _ := by simp [star_smul] }
  have hφ : IsMarkovTrace (star z) φ :=
    { map_one := by simp [φ]
      map_mul_comm _ _ := by simp [φ, star_mul, (isMarkovTrace_ocneanuTrace z).map_mul_comm]
      map_mul_T {n a} ha := by
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, star_mul, star_T]
        rw [(isMarkovTrace_ocneanuTrace (q := q) z).map_mul_comm (T q n) (star a),
          (isMarkovTrace_ocneanuTrace z).map_mul_T (star_mem_stage_iff.mpr ha),
          star_mul, mul_comm] }
  simpa [φ] using LinearMap.congr_fun hφ.eq_ocneanuTrace (star x)

/-- For a self-adjoint Markov parameter `z`, `ocneanuTrace R q z` commutes with `star`. -/
@[simp]
theorem ocneanuTrace_star {R : Type*} [CommRing R] [StarRing R] {q : Rˣ}
    [Fact (IsSelfAdjoint (q : R))] {z : R} (hz : IsSelfAdjoint z)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    ocneanuTrace R q z (star x) = star (ocneanuTrace R q z x) := by
  rw [star_ocneanuTrace, hz.star_eq]

end TauCeti.InfiniteTypeAHeckeAlgebra
