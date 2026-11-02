/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.DegreeScaling
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The Hermitian metric of an exterior algebra

Let `M` be a module over a commutative star ring `R` with a finite ordered basis `b`, and let
`h = Matrix.toLinearMapₛₗ₂ (starRingEnd R) b b 1` be the Hermitian form for which `b` is
orthonormal, conjugate-linear in its first argument. The exterior algebra `⋀ M` has the
increasing wedge basis `b.ExteriorAlgebra`, indexed by finite sets of indices, and the
corresponding form

  `H = Matrix.toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra 1`

for which the wedge basis is orthonormal. Over `ℝ` and `ℂ` this is the exterior Gram metric of
`h`. It is Hermitian and, over a star-ordered ring without zero divisors, positive definite
(`Matrix.star_toLinearMapₛₗ₂_one_apply`, `Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff`).

This file proves that **exterior multiplication by `x` is adjoint to contraction by `h(x, ·)`**:
`H (x ∧ s) t = H s (h(x, ·) ⌋ t)`. Since `⋀ M` is generated from `1` by exterior multiplication,
the adjointness and the normalization `H 1 1 = 1` determine `H`, so `H` depends only on `h`
and not on the orthonormal basis used to build it.

These are the identities behind the creation and annihilation operators of a Fock space: in the
spinor module `⋀ W` of a complex structure, the Clifford action of a vector is a sum of a
creation and an annihilation operator, and their adjointness makes Clifford multiplication by a
real vector skew-Hermitian. The degree scaling `T_r`, which multiplies the `p`-th exterior power
by `r ^ p`, has adjoint `T_{star r}` for `H`, so pulling `H` back along `T_r` multiplies it by
`(star r * r) ^ p` on the `p`-th exterior power. This is how the metrics of differently
normalized Fock actions compare.

## Main results

* `ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_left`: `H (x ∧ s) t = H s (h(x, ·) ⌋ t)`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_ι_mul_right`: `H s (x ∧ t) = H (h(x, ·) ⌋ s) t`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_apply_one_one`: `H 1 1 = 1`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq`: two bases with the same
  Hermitian form on `M` give the same Hermitian form on `⋀ M`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_degreeScaling_left`: `H (T_r s) t = H s (T_{star r} t)`.
* `ExteriorAlgebra.toLinearMapₛₗ₂_degreeScaling_degreeScaling_of_mem_exteriorPower`:
  `H (T_r s) (T_r t) = (star r * r) ^ p * H s t` for `s` in the `p`-th exterior power.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra Matrix TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M I : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
  [Fintype I] [LinearOrder I] (b : Module.Basis I R M)

/-- **The vacuum is a unit vector**: `H 1 1 = 1` for the Hermitian form making the wedge basis
orthonormal.

Not `@[simp]`: `Matrix.toLinearMapₛₗ₂_apply` already expands the left-hand side. -/
theorem toLinearMapₛₗ₂_apply_one_one :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
      (1 : Matrix (Finset I) (Finset I) R) 1 1 = 1 := by
  have h : b.ExteriorAlgebra ∅ = 1 := by simp [b.exteriorAlgebra_eq_prod_map_sort]
  rw [← h, toLinearMapₛₗ₂_apply_basis, one_apply_eq]

/-- Exterior multiplication by a basis vector is adjoint to contraction by its coordinate. -/
private theorem toLinearMapₛₗ₂_ι_basis_mul (i : I) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R (b i) * s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) t) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  have key : H.comp (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R (b i))) =
      H.compl₂ (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)) := by
    refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply,
      ι_mul_basis, contractLeft_coord_basis]
    -- Both sides are the shuffle sign when `T = insert i S` with `i ∉ S`, and zero otherwise.
    split_ifs with hiS hiT hiT <;>
      simp only [H, Units.smul_def, map_zsmul, map_zero, LinearMap.zero_apply,
        LinearMap.smul_apply, toLinearMapₛₗ₂_apply_basis, one_apply]
    · simp [show S ≠ T.erase i by rintro rfl; simp at hiS]
    · by_cases hST : insert i S = T
      · subst hST
        simp [Finset.erase_insert hiS]
      · simp [hST, show S ≠ T.erase i by rintro rfl; exact hST (Finset.insert_erase hiT)]
    · simp [show insert i S ≠ T by rintro rfl; exact hiT (Finset.mem_insert_self i S)]
  exact LinearMap.congr_fun₂ key s t

/-- **Exterior multiplication is adjoint to contraction**: for the Hermitian form `h` making `b`
orthonormal and the form `H` making the wedge basis orthonormal,
`H (x ∧ s) t = H s (h(x, ·) ⌋ t)`. -/
theorem toLinearMapₛₗ₂_ι_mul_left (x : M) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (_root_.ExteriorAlgebra.ι R x * s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) x) t) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul, map_smulₛₗ, Finset.sum_mul, smul_mul_assoc,
    LinearMap.sum_apply, LinearMap.smul_apply, toLinearMapₛₗ₂_one_basis_eq_coord,
    toLinearMapₛₗ₂_ι_basis_mul]

/-- **Contraction is adjoint to exterior multiplication**: for the Hermitian form `h` making `b`
orthonormal and the form `H` making the wedge basis orthonormal,
`H s (x ∧ t) = H (h(x, ·) ⌋ s) t`. -/
theorem toLinearMapₛₗ₂_ι_mul_right (x : M) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (_root_.ExteriorAlgebra.ι R x * t) =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R)
        (contractLeft (Q := (0 : QuadraticForm R M))
          (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) x) s) t := by
  rw [← star_toLinearMapₛₗ₂_one_apply, toLinearMapₛₗ₂_ι_mul_left, star_toLinearMapₛₗ₂_one_apply]

/-- **The Hermitian form of `⋀ M` depends only on the Hermitian form of `M`**: if two finite
ordered bases `b` and `b'` of `M` are orthonormal for the same Hermitian form, then their wedge
bases are orthonormal for the same Hermitian form on `⋀ M`. -/
theorem toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq {I' : Type*} [Fintype I'] [LinearOrder I']
    (b' : Module.Basis I' R M)
    (h : toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix I I R) =
      toLinearMapₛₗ₂ (starRingEnd R) b' b' (1 : Matrix I' I' R)) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) =
      toLinearMapₛₗ₂ (starRingEnd R) b'.ExteriorAlgebra b'.ExteriorAlgebra
        (1 : Matrix (Finset I') (Finset I') R) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  set H' := toLinearMapₛₗ₂ (starRingEnd R) b'.ExteriorAlgebra b'.ExteriorAlgebra
    (1 : Matrix (Finset I') (Finset I') R)
  -- Both forms pair the vacuum with `t` by the scalar part of `t`.
  have hone (t : _root_.ExteriorAlgebra R M) : H 1 t = H' 1 t := by
    induction t using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [H, H', Algebra.algebraMap_eq_smul_one, map_smul, toLinearMapₛₗ₂_apply_one_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | ι_mul t m _ =>
      rw [toLinearMapₛₗ₂_ι_mul_right, toLinearMapₛₗ₂_ι_mul_right, contractLeft_one,
        contractLeft_one, map_zero, map_zero, LinearMap.zero_apply]
  refine LinearMap.ext fun s ↦ ?_
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r =>
    refine LinearMap.ext fun t ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.smul_apply, hone]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul s m hs =>
    refine LinearMap.ext fun t ↦ ?_
    rw [toLinearMapₛₗ₂_ι_mul_left, toLinearMapₛₗ₂_ι_mul_left, hs, h]

/-- **The adjoint of the degree scaling by `r` is the degree scaling by `star r`**: for the form `H`
making the wedge basis orthonormal, `H (T_r s) t = H s (T_{star r} t)`. -/
theorem toLinearMapₛₗ₂_degreeScaling_left (r : Rˣ) (s t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) t =
      toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s (degreeScaling (star r) t) := by
  set H := toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) R)
  have key : H.comp (degreeScaling r).toLinearMap =
      H.compl₂ (degreeScaling (star r)).toLinearMap := by
    refine LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra fun S T ↦ ?_
    simp only [H, LinearMap.comp_apply, LinearMap.compl₂_apply, AlgEquiv.toLinearMap_apply,
      degreeScaling_basis, map_smulₛₗ, LinearMap.smul_apply, toLinearMapₛₗ₂_apply_basis,
      one_apply, Units.coe_star, smul_eq_mul, starRingEnd_apply, star_pow, RingHom.id_apply]
    split_ifs with hST
    · rw [hST]
    · simp only [mul_zero]
  exact LinearMap.congr_fun₂ key s t

/-- **The degree scaling rescales the metric on each exterior power**: for the form `H` making the
wedge basis orthonormal and `s` in the `p`-th exterior power, `H (T_r s) (T_r t)` is
`(star r * r) ^ p` times `H s t`. -/
theorem toLinearMapₛₗ₂_degreeScaling_degreeScaling_of_mem_exteriorPower (r : Rˣ) {p : ℕ}
    {s : _root_.ExteriorAlgebra R M} (hs : s ∈ ⋀[R]^p M) (t : _root_.ExteriorAlgebra R M) :
    toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) (degreeScaling r s) (degreeScaling r t) =
      (star (r : R) * r) ^ p * toLinearMapₛₗ₂ (starRingEnd R) b.ExteriorAlgebra b.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) R) s t := by
  -- Move the right-hand scaling across as `T_{star r}`, which also acts on `s` by a scalar.
  have h := toLinearMapₛₗ₂_degreeScaling_left b (star r) s t
  rw [star_star] at h
  rw [degreeScaling_of_mem_exteriorPower r hs, map_smulₛₗ, LinearMap.smul_apply, ← h,
    degreeScaling_of_mem_exteriorPower _ hs, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul]
  simp only [Units.coe_star, starRingEnd_apply, star_pow, star_star]
  ring

end ExteriorAlgebra
