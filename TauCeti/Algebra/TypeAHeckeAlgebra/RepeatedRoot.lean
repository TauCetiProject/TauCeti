/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# Proper-star collapse at the repeated-root parameter `q + q⁻¹ = 0`

When `q + q⁻¹ = 0` (over `ℂ`, `q = ±i`), the quadratic relation of `InfiniteTypeAHeckeAlgebra R q`
degenerates to `(T q i - q) ^ 2 = 0` (`T_sub_algebraMap_sq_eq_zero`) and `signCharacter`
coincides with `indexCharacter` (`signCharacter_eq_indexCharacter`).

In any `R`-algebra `A` with a proper star (`IsProperStar A`), a nilpotent normal element vanishes
(`IsStarNormal.eq_zero_of_isNilpotent`). Consequently, every `R`-algebra homomorphism out of
`InfiniteTypeAHeckeAlgebra R q` sending the generators `T q i` to normal (in particular unitary)
elements sends every generator to `q` and factors through `indexCharacter R q`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.map_T_eq_algebraMap_of_isStarNormal`: normal generator images
  collapse to `q` when `q + q⁻¹ = 0`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.map_eq_algebraMap_indexCharacter_of_isStarNormal`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.map_eq_smul_one_indexCharacter_of_isStarNormal`:
  representations by normal generators factor through `indexCharacter`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.map_eq_algebraMap_indexCharacter_of_mem_unitary`:
  unitary representations at `q + q⁻¹ = 0` factor through `indexCharacter`.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

section RepeatedRoot

variable {R : Type*} [CommRing R] {q : Rˣ}
variable {A F : Type*} [Ring A] [StarRing A] [IsProperStar A] [Algebra R A]
  [FunLike F (InfiniteTypeAHeckeAlgebra R q) A]
  [AlgHomClass F R (InfiniteTypeAHeckeAlgebra R q) A]

/-- **Normal collapse at `q + q⁻¹ = 0`.** In any `R`-algebra `A` with a proper star, an algebra map
`φ` sending `T i` to a normal element sends `T i` to `q`: `φ (T i) - algebraMap R A q` is both
normal and square-zero. -/
theorem map_T_eq_algebraMap_of_isStarNormal (hq : (q : R) + ↑q⁻¹ = 0) (φ : F)
    (hφ : ∀ i, IsStarNormal (φ (T q i))) (i : ℕ) :
    φ (T q i) = algebraMap R A (q : R) := by
  have hd_sq : (φ (T q i) - algebraMap R A (q : R)) ^ 2 = 0 := by
    rw [← AlgHomClass.commutes φ, ← map_sub, ← map_pow, T_sub_algebraMap_sq_eq_zero hq i, map_zero]
  have hcomm_star (a : A) : Commute (star (algebraMap R A (q : R))) a := by
    rw [commute_iff_eq]
    simpa only [star_mul, star_star] using congrArg star (Algebra.commutes (q : R) (star a)).symm
  have hd_norm : IsStarNormal (φ (T q i) - algebraMap R A (q : R)) :=
    ⟨by
      rw [star_sub]
      exact ((hφ i).star_comm_self.sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
        ((hcomm_star _).sub_right (hcomm_star _))⟩
  exact sub_eq_zero.mp (hd_norm.eq_zero_of_isNilpotent ⟨2, hd_sq⟩)

/-- **Representations by normal generators at `q + q⁻¹ = 0` factor through `indexCharacter`.** -/
theorem map_eq_algebraMap_indexCharacter_of_isStarNormal (hq : (q : R) + ↑q⁻¹ = 0) (φ : F)
    (hφ : ∀ i, IsStarNormal (φ (T q i))) (x : InfiniteTypeAHeckeAlgebra R q) :
    φ x = algebraMap R A (indexCharacter R q x) :=
  DFunLike.congr_fun
    (hom_ext (F := AlgHom.ofClass φ) (G := (Algebra.ofId R A).comp (indexCharacter R q))
      fun i ↦ by simpa using map_T_eq_algebraMap_of_isStarNormal hq φ hφ i) x

/-- Scalar-action form of `map_eq_algebraMap_indexCharacter_of_isStarNormal`. -/
theorem map_eq_smul_one_indexCharacter_of_isStarNormal (hq : (q : R) + ↑q⁻¹ = 0) (φ : F)
    (hφ : ∀ i, IsStarNormal (φ (T q i))) (x : InfiniteTypeAHeckeAlgebra R q) :
    φ x = indexCharacter R q x • (1 : A) := by
  rw [map_eq_algebraMap_indexCharacter_of_isStarNormal hq φ hφ x, Algebra.algebraMap_eq_smul_one]

/-- **Unitary representations at `q + q⁻¹ = 0` factor through `indexCharacter`.** -/
theorem map_eq_algebraMap_indexCharacter_of_mem_unitary (hq : (q : R) + ↑q⁻¹ = 0) (φ : F)
    (hφ : ∀ i, φ (T q i) ∈ unitary A) (x : InfiniteTypeAHeckeAlgebra R q) :
    φ x = algebraMap R A (indexCharacter R q x) :=
  map_eq_algebraMap_indexCharacter_of_isStarNormal hq φ
    (fun i ↦ isStarNormal_of_mem_unitary (hφ i)) x

end RepeatedRoot

end TauCeti.InfiniteTypeAHeckeAlgebra
