/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# The characteristic polynomial and the fixed submodule

For an endomorphism `f` of a finite-dimensional vector space `V`, the fixed submodule
`f.fixedSubmodule` is the eigenspace of `f` for the eigenvalue `1`
(`Module.End.eigenspace_one_eq_fixedSubmodule`). Its dimension is therefore at
most the multiplicity of `1` as a root of the characteristic polynomial, with equality when `f` is
semisimple (`Module.End.IsFinitelySemisimple.rootMultiplicity_charpoly`), for example when `f`
has finite order invertible in the field.

These multiplicities are read here on the reverse characteristic polynomial
`det(1 - t f) = f.charpoly.reverse`, the denominator in Molien's formula. If `f` is semisimple
with fixed space of dimension `m`, then `det(1 - t f) = (1 - t) ^ m * R(t)` with `R(1) ≠ 0`, which
is the order of the pole of `det(1 - t f)⁻¹` at `t = 1`. If the fixed space is a hyperplane, then
`det(1 - t f) = (1 - t) ^ (dim V - 1) * (1 - det(f) t)` exactly, whether or not `f` is semisimple.
Comparing the poles at `t = 1` of Molien's series is how the degrees of the basic invariants of a
pseudoreflection group are related to the order of the group and to its number of
pseudoreflections.

## Main results

* `Module.End.IsFinitelySemisimple.rootMultiplicity_one_charpoly`: for a semisimple endomorphism,
  the multiplicity of the root `1` of the characteristic polynomial is the dimension of the fixed
  submodule.
* `Module.End.IsFinitelySemisimple.exists_reverse_charpoly_eq_one_sub_X_pow_mul`: for a
  semisimple endomorphism, `det(1 - t f) = (1 - t) ^ m * R(t)` with `m = dim V^f` and `R(1) ≠ 0`.
* `Module.End.reverse_charpoly_of_finrank_fixedSubmodule_add_one`: if the fixed submodule is a
  hyperplane, then `det(1 - t f) = (1 - t) ^ (dim V - 1) * (1 - det(f) t)`.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, Cambridge University Press (1990), § 3.9.
-/

public section

open Polynomial Module

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The dimension of the fixed submodule of an endomorphism is at most the multiplicity of `1`
as a root of its characteristic polynomial. -/
theorem finrank_fixedSubmodule_le_rootMultiplicity_one_charpoly (f : End K V) :
    finrank K f.fixedSubmodule ≤ f.charpoly.rootMultiplicity 1 :=
  f.eigenspace_one_eq_fixedSubmodule ▸ LinearMap.finrank_eigenspace_le f 1

/-- For a semisimple endomorphism, the multiplicity of `1` as a root of the characteristic
polynomial is the dimension of the fixed submodule. -/
theorem IsFinitelySemisimple.rootMultiplicity_one_charpoly {f : End K V}
    (hf : f.IsFinitelySemisimple) :
    f.charpoly.rootMultiplicity 1 = finrank K f.fixedSubmodule := by
  rw [hf.rootMultiplicity_charpoly, eigenspace_one_eq_fixedSubmodule]

/-- For a semisimple endomorphism `f` whose fixed submodule has dimension `m`, the reverse
characteristic polynomial `det(1 - t f)` is `(1 - t) ^ m` times a polynomial that does not vanish
at `t = 1`. -/
theorem IsFinitelySemisimple.exists_reverse_charpoly_eq_one_sub_X_pow_mul {f : End K V}
    (hf : f.IsFinitelySemisimple) :
    ∃ R : K[X], f.charpoly.reverse = (1 - X) ^ finrank K f.fixedSubmodule * R ∧ R.eval 1 ≠ 0 := by
  obtain ⟨S, hS, hdvd⟩ :=
    f.charpoly.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly_monic.ne_zero 1
  refine ⟨S.reverse, ?_, ?_⟩
  · rw [hS, reverse_mul_of_domain, reverse_X_sub_C_pow, hf.rootMultiplicity_one_charpoly, map_one,
      one_mul]
  · rw [eval_reverse_of_ne_zero S one_ne_zero, one_pow, inv_one, one_mul]
    exact fun h ↦ hdvd (dvd_iff_isRoot.2 h)

/-- If the fixed submodule of `f` is a hyperplane, of dimension `m = dim V - 1`, then the reverse
characteristic polynomial is `det(1 - t f) = (1 - t) ^ m * (1 - det(f) t)`. No semisimplicity is
needed: a transvection, with `det f = 1`, gives `(1 - t) ^ dim V`. -/
theorem reverse_charpoly_of_finrank_fixedSubmodule_add_one (f : End K V)
    (h : finrank K f.fixedSubmodule + 1 = finrank K V) :
    f.charpoly.reverse =
      (1 - X) ^ finrank K f.fixedSubmodule * (1 - C (LinearMap.det f) * X) := by
  set m := finrank K f.fixedSubmodule
  -- The characteristic polynomial is `(X - 1) ^ m * S` with `S` monic of degree one.
  obtain ⟨S, hS⟩ : (X - C 1) ^ m ∣ f.charpoly :=
    (pow_dvd_pow _ f.finrank_fixedSubmodule_le_rootMultiplicity_one_charpoly).trans
      (pow_rootMultiplicity_dvd _ _)
  have hSm : S.Monic := (monic_X_sub_C (1 : K)).pow m |>.of_mul_monic_left (hS ▸ f.charpoly_monic)
  have hSdeg : S.natDegree = 1 := by
    have := congrArg natDegree hS
    rw [LinearMap.charpoly_natDegree, ((monic_X_sub_C (1 : K)).pow m).natDegree_mul hSm,
      natDegree_pow, natDegree_X_sub_C, mul_one, ← h] at this
    omega
  -- Its root is `det f`, read off from the constant coefficient of the characteristic polynomial.
  have hSX : S = X - C (LinearMap.det f) := by
    rw [hSm.eq_X_add_C hSdeg, sub_eq_add_neg, ← C_neg]
    congr 2
    have h0 := congrArg (eval 0) hS
    rw [← coeff_zero_eq_eval_zero, eval_mul, eval_pow, hSm.eq_X_add_C hSdeg] at h0
    rw [LinearMap.det_eq_sign_charpoly_coeff, h0, ← h]
    simp only [eval_sub, eval_X, eval_C, eval_add, eval_one, zero_sub, zero_add, map_one]
    have hsq : ((-1 : K) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-S.coeff 0) * hsq
  rw [hS, reverse_mul_of_domain, reverse_X_sub_C_pow, hSX, ← pow_one (X : K[X]),
    reverse_X_pow_sub_C, map_one, one_mul, pow_one]

end Module.End
