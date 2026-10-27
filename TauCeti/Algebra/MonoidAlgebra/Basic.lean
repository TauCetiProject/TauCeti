/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Basic facts about monoid algebras

General facts about the monoid algebra `R[G]` that use only its basis elements `single g r`, and
none of the further theory built on it.

## Main results

* `TauCeti.single_sub_one_ne_zero`: over a nontrivial ring, the difference `single g 1 - 1`
  between the basis element at `g` and the unit is nonzero when `g ≠ 1`.
* `MonoidAlgebra.coeff_one_mul_comm`: the coefficient at the identity of `xy` equals
  that of `yx` in a group algebra over a commutative semiring.
* `MonoidAlgebra.coeff_one_mul_of_coeff_mem`: the coefficient at the identity is multiplicative
  on elements whose other coefficients lie in a square-zero ideal, with additive version
  `AddMonoidAlgebra.coeff_zero_mul_of_coeff_mem`.
* The `IsMulCommutative (MonoidAlgebra R M)` instance: the monoid algebra of a commutative
  magma over a commutative semiring is commutative, as a mixin on the existing ring structure.
* `TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff`: an element of `R[M]` lies in `I • R[M]` exactly
  when its coefficients lie in `I`, and `TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff`: the kernel
  of the coefficientwise map along `f : R →+* S` is `ker f • R[M]`.

## References

Injectivity of `single` in its index is Mathlib's `MonoidAlgebra.single_left_injective`.
-/

public section

namespace TauCeti

section Commutative

variable {R : Type*} [CommSemiring R] {M : Type*} [Mul M]

/-- The monoid algebra of a commutative magma over a commutative semiring is commutative. This is
the mixin form of Mathlib's `MonoidAlgebra.nonUnitalCommSemiring`, for a multiplication that is
commutative without carrying a `CommSemigroup` instance. -/
instance instIsMulCommutativeMonoidAlgebra [IsMulCommutative M] :
    IsMulCommutative (MonoidAlgebra R M) where
  is_comm.comm f g := by
    have hM := isMulCommutative_iff.mp (inferInstance : IsMulCommutative M)
    simp [MonoidAlgebra.mul_def, Finsupp.sum, mul_comm, hM, f.coeff.support.sum_comm]

end Commutative

section Semiring

variable {R : Type*} [Semiring R] {M : Type*}

/-- An element of `R[M]` all of whose coefficients are divisible by `n` is `n` times an element. -/
theorem _root_.MonoidAlgebra.exists_eq_nsmul_of_dvd_coeff {n : ℕ} {x : MonoidAlgebra R M}
    (h : ∀ m, (n : R) ∣ x.coeff m) : ∃ y, x = n • y := by
  choose c hc using h
  refine ⟨∑ m ∈ x.coeff.support, MonoidAlgebra.single m (c m), ?_⟩
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [MonoidAlgebra.smul_single, hc m, nsmul_eq_mul]

end Semiring

variable {R : Type*} [Ring R] {G : Type*} [One G]

/-- Over a nontrivial ring, the difference `single g 1 - 1` between the basis element at `g` and the
unit is nonzero when `g ≠ 1`. -/
theorem single_sub_one_ne_zero [Nontrivial R] {g : G} (hg : g ≠ 1) :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def]
  intro h
  exact hg (MonoidAlgebra.single_left_injective one_ne_zero h)

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {M : Type*}

/-- An element of `R[M]` lies in `I • R[M]` exactly when all of its coefficients lie in `I`. -/
@[simp]
theorem mem_ideal_smul_top_iff {I : Ideal R} {x : MonoidAlgebra R M} :
    x ∈ I • (⊤ : Submodule R (MonoidAlgebra R M)) ↔ ∀ m, x.coeff m ∈ I := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun r hr n _ m ↦ ?_) fun x y hx hy m ↦ ?_
    · simpa using I.mul_mem_right (n.coeff m) hr
    · simpa using I.add_mem (hx m) (hy m)
  · rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    simpa [MonoidAlgebra.smul_single'] using
      Submodule.smul_mem_smul (hx m) (Submodule.mem_top (x := MonoidAlgebra.single m (1 : R)))

/-- Applying a ring homomorphism `f` to the coefficients kills exactly `ker f • R[M]`. -/
@[simp]
theorem mapRingHom_eq_zero_iff [Monoid M] {S : Type*} [Semiring S] (f : R →+* S)
    {x : MonoidAlgebra R M} :
    MonoidAlgebra.mapRingHom M f x = 0 ↔
      x ∈ RingHom.ker f • (⊤ : Submodule R (MonoidAlgebra R M)) := by
  rw [mem_ideal_smul_top_iff, ← MonoidAlgebra.coeff_inj]
  simp [Finsupp.ext_iff, MonoidAlgebra.coeff_mapRingHom]

end MonoidAlgebra

end TauCeti

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G]

/-- The coefficient at the identity is symmetric under swapping the factors in a group algebra
over a commutative semiring. -/
theorem coeff_one_mul_comm (x y : MonoidAlgebra R G) :
    (x * y).coeff 1 = (y * x).coeff 1 := by
  induction y using MonoidAlgebra.induction_on with
  | of g => simp [MonoidAlgebra.of_apply]
  | add y z hy hz =>
      simpa only [mul_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply] using
        congrArg₂ (· + ·) hy hz
  | smul r y hy =>
      simpa only [mul_smul_comm, smul_mul_assoc, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply] using congrArg (r • ·) hy

/-- If all coefficients away from the identity of two elements of `R[M]` lie in a square-zero
ideal, the coefficient at the identity of their product is the product of their coefficients at
the identity. Thus the identity coefficient is multiplicative on the elements of `R[M]` that are
constant modulo such an ideal. -/
@[to_additive (dont_translate := R) coeff_zero_mul_of_coeff_mem
/-- If all coefficients away from zero of two elements of `R[M]` lie in a square-zero ideal, the
coefficient at zero of their product is the product of their coefficients at zero. Thus the zero
coefficient is multiplicative on the elements of `R[M]` that are constant modulo such an ideal;
for Laurent polynomials this is the constant coefficient. -/]
theorem coeff_one_mul_of_coeff_mem {R M : Type*} [CommSemiring R] [Monoid M] {I : Ideal R}
    (hI : I ^ 2 = ⊥) {x y : MonoidAlgebra R M} (hx : ∀ m ≠ 1, x.coeff m ∈ I)
    (hy : ∀ m ≠ 1, y.coeff m ∈ I) :
    (x * y).coeff 1 = x.coeff 1 * y.coeff 1 := by
  classical
  have hzero {m n : M} (hm : m ≠ 1) (hn : n ≠ 1) : x.coeff m * y.coeff n = 0 := by
    have hmem : x.coeff m * y.coeff n ∈ I ^ 2 := pow_two I ▸ Ideal.mul_mem_mul (hx m hm) (hy n hn)
    simpa [hI] using hmem
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_eq_single 1, Finsupp.sum_eq_single 1]
  · simp
  · intro n _ hn
    simp [hn]
  · simp
  · intro m _ hm
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    dsimp only
    split_ifs with hmn
    · exact hzero hm fun hn ↦ hm (by simpa [hn] using hmn)
    · rfl
  · simp

end MonoidAlgebra
