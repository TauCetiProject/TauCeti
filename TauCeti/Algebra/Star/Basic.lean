/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module

/-!
# Involution-closed absorption, proper-star annihilators, scalar commutation, and star-linearity

In any magma `A` with an antimultiplicative involution (`StarMul A`), a subset closed under `star`
(`StarMemClass S A`) that absorbs multiplication by ambient elements on the left also absorbs
multiplication on the right via `x * a = star (star a * star x)`. Similarly, in a star module over
`R` with `StarMul A` and `IsScalarTower R A A`, applying `star` shows that scalars commute with
left multiplication (`x * (c • y) = c • (x * y)`), so `SMulCommClass R A A` is automatic.

In a star ring whose star is proper (`IsProperStar`: `star x * x = 0` forces `x = 0`), such as a
C⋆-algebra, an element killed by every two-sided multiplication `star d * X * c` vanishes. This is
how entrywise identities are read off from sesquilinear forms with coefficients in the ring, for
instance for matrices over a C⋆-algebra.

In particular, a ring with proper star has zero left and right annihilators. These are recorded
as the instances `FaithfulSMul Rᵐᵒᵖ R` and `FaithfulSMul R R` for the actions of `R` on itself by
right and left multiplication, which is how nondegeneracy enters the theory of double
centralizers.

A star-linear (conjugate-linear) equivalence `V ≃ₗ⋆[S] W` is linear over any scalars `R` acting on
`S` with trivial star (`LinearEquiv.restrictScalarsₛₗ`). For example, a conjugate-linear
equivalence of complex vector spaces is real-linear.

## Main results

* `StarMemClass.mul_mem_right_of_mul_mem_left`: left absorption implies right absorption on
  star-closed subsets.
* `TauCeti.eq_zero_of_forall_star_mul_mul_eq_zero`: if `star d * X * c = 0` for all `c` and
  `d`, then `X = 0`.
* `TauCeti.faithfulSMul_mulOpposite_of_isProperStar`: if `c * x = c * y` for all `c`, then
  `x = y`.
* `TauCeti.faithfulSMul_of_isProperStar`: if `x * c = y * c` for all `c`, then `x = y`.
* `TauCeti.mul_smul_comm_of_starModule`: in a star module with a multiplicative star and a scalar
  tower, scalars commute with left multiplication, so no `SMulCommClass` assumption is needed
  there.
* `LinearEquiv.restrictScalarsₛₗ`: a star-linear equivalence over `S` is `R`-linear when `R` acts
  on `S` with trivial star.
-/

public section

/-- A subset closed under the involution and under left multiplication by ambient elements is also
closed under right multiplication, via `x * a = star (star a * star x)`. -/
theorem StarMemClass.mul_mem_right_of_mul_mem_left {S A : Type*} [Mul A] [StarMul A]
    [SetLike S A] [StarMemClass S A] {s : S}
    (hmul : ∀ a : A, ∀ x ∈ s, a * x ∈ s) (a : A) {x : A} (hx : x ∈ s) : x * a ∈ s := by
  simpa only [star_mul, star_star] using star_mem (hmul (star a) (star x) (star_mem hx))

namespace TauCeti

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] [IsProperStar R]

/-- In a star ring with proper star, an element annihilated by every two-sided multiplication
vanishes. -/
theorem eq_zero_of_forall_star_mul_mul_eq_zero {X : R} (h : ∀ c d : R, star d * X * c = 0) :
    X = 0 := by
  have h' : star (X * star X) * (X * star X) = 0 := by
    simpa [star_mul, mul_assoc] using h (star X) (X * star X)
  exact mul_star_self_eq_zero.mp (star_mul_self_eq_zero.mp h')

section Ring

variable {R : Type*} [NonUnitalRing R]

/-- In a ring with proper star, an element `x` with `c * x = 0` for every `c` vanishes:
the action of `Rᵐᵒᵖ` on `R` by right multiplication is faithful. -/
instance faithfulSMul_mulOpposite_of_isProperStar [Star R] [IsProperStar R] :
    FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {x y} h := MulOpposite.unop_injective <| sub_eq_zero.mp <|
    star_mul_self_eq_zero.mp <| by
      simpa [mul_sub, sub_eq_zero, MulOpposite.smul_eq_mul_unop] using h (star (x.unop - y.unop))

/-- In a ring with proper involutive star, an element `x` with `x * c = 0` for every `c`
vanishes: the action of `R` on itself by left multiplication is faithful. -/
instance faithfulSMul_of_isProperStar [InvolutiveStar R] [IsProperStar R] :
    FaithfulSMul R R where
  eq_of_smul_eq_smul {x y} h := by
    have h' : star (star (x - y)) * star (x - y) = 0 := by
      simpa [sub_mul, sub_eq_zero] using h (star (x - y))
    have hs : star (x - y) = 0 := star_mul_self_eq_zero.mp h'
    exact sub_eq_zero.mp (star_mul_self_eq_zero.mp (by rw [hs, zero_mul]))

end Ring

end TauCeti

namespace TauCeti

variable {R A : Type*} [Star R] [Mul A] [StarMul A] [SMul R A] [StarModule R A]
  [IsScalarTower R A A]

/-- **Scalars commute with left multiplication in a star module.** If `A` has a multiplicative
star (`StarMul A`) and is a star module over `R` with `IsScalarTower R A A`, then
`x * (c • y) = c • (x * y)`. In particular `SMulCommClass R A A` is automatic. -/
theorem mul_smul_comm_of_starModule (c : R) (x y : A) : x * (c • y) = c • (x * y) := by
  -- apply `star`, which turns the goal into the identity `(star c • star y) * star x =
  -- star c • (star y * star x)`, an instance of `IsScalarTower R A A`
  apply star_injective
  rw [star_mul, star_smul, smul_mul_assoc, star_smul, star_mul]

end TauCeti

namespace LinearEquiv

variable (R : Type*) {S V W : Type*} [Semiring R] [Star R] [TrivialStar R] [CommSemiring S]
  [StarRing S] [SMul R S] [StarModule R S] [AddCommMonoid V] [Module R V] [Module S V]
  [IsScalarTower R S V] [AddCommMonoid W] [Module R W] [Module S W] [IsScalarTower R S W]

/-- A star-linear (conjugate-linear) equivalence over `S` is linear over any scalars `R` with
trivial star that act on `S`, `V` and `W` through scalar towers `R → S`: the star of `S` fixes the
images `r • 1` of these scalars. For example, a conjugate-linear equivalence of complex vector
spaces is real-linear. -/
def restrictScalarsₛₗ (f : V ≃ₗ⋆[S] W) : V ≃ₗ[R] W where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  -- `r • x = (r • 1 : S) • x`, and the star of `S` fixes `r • 1`.
  map_smul' r x := by simpa [starRingEnd_apply] using f.map_smulₛₗ (r • (1 : S)) x
  left_inv := f.left_inv
  right_inv := f.right_inv

@[simp]
theorem coe_restrictScalarsₛₗ (f : V ≃ₗ⋆[S] W) : ⇑(f.restrictScalarsₛₗ R) = f :=
  (rfl)

@[simp]
theorem restrictScalarsₛₗ_symm (f : V ≃ₗ⋆[S] W) :
    (f.restrictScalarsₛₗ R).symm = f.symm.restrictScalarsₛₗ R :=
  (rfl)

end LinearEquiv
