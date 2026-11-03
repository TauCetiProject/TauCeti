/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Basic identities for bilinear forms

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and cancelling the `2` leaves `B x y = 0`.

That cancellation is all the hypothesis on the ring there is: `2` has to be regular, and nothing
is asked of any other element, so the statement covers rings with zero divisors elsewhere.  Over a
field, or over any domain, `IsRegular.of_ne_zero` supplies the hypothesis from `(2 : R) ≠ 0`.

A bilinear map with additively torsion-free values, such as an integral intersection form,
vanishes on elements of finite additive order, so its values depend on each argument only modulo
torsion. In particular, for a hyperbolic pair `v, t` of a `ℤ`-valued form (`v · v = t · t = 0`,
`v · t = t · v = 1`), every class `a v + c t` modulo torsion has square `2ac`, so the form is even
when `v, t` span modulo torsion.

For a left-separating alternating bilinear map on a module with a two-element basis, its value
on that basis has trivial scalar annihilator. This holds over any commutative semiring and for
maps valued in an arbitrary module.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring in which
  `2` is regular is zero.
* `TauCeti.BilinForm.nondegenerate_smul_iff`: scalar multiplication by a regular element
  preserves nondegeneracy.
* `TauCeti.BilinForm.nondegenerate_neg_iff`: negating a bilinear form preserves nondegeneracy.
* `Module.Basis.dualBasis_smul_apply`: the dual basis of a scalar multiple of a form.
* `LinearMap.BilinForm.IsSymm.apply_add_self`: polarization of a symmetric bilinear form.
* `LinearMap.apply_eq_apply_of_isOfFinAddOrder_sub_left`,
  `LinearMap.apply_eq_apply_of_isOfFinAddOrder_sub_right`: a bilinear map with additively
  torsion-free values sees each argument only modulo elements of finite additive order.
* `LinearMap.BilinForm.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub`: `x · x = 2ac` for
  `x = a v + c t` modulo torsion, where `v, t` is a hyperbolic pair of a `ℤ`-valued form.
* `LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span`: a `ℤ`-valued form spanned modulo
  torsion by a hyperbolic pair is even.
* `LinearMap.IsAlt.eq_zero_of_smul_apply_basis_eq_zero`: the value of a left-separating
  alternating bilinear map on a two-element basis has trivial scalar annihilator.
-/

public section

namespace LinearMap.IsAlt

/-- The value of a left-separating alternating bilinear map on a two-element basis has trivial
scalar annihilator, over any commutative semiring. -/
theorem eq_zero_of_smul_apply_basis_eq_zero {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (b : Module.Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (hω : ω.SeparatingLeft) {r : R} (hr : r • ω (b 0) (b 1) = 0) : r = 0 := by
  have hb : r • b 0 = 0 := hω _ fun y ↦ by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.smul_apply, halt (b 0), hr, smul_zero,
      add_zero]
  simpa using congr(b.repr $hb 0)

end LinearMap.IsAlt

namespace LinearMap.BilinForm

/-- Restriction to a submodule commutes with scalar multiplication of a bilinear form. -/
@[simp]
theorem restrict_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (r : R) (B : LinearMap.BilinForm R M) (N : Submodule R M) :
    (r • B).restrict N = r • B.restrict N := by
  ext x y
  simp

end LinearMap.BilinForm

namespace LinearMap.BilinForm.IsSymm

/-- Polarization of a symmetric bilinear form over a commutative semiring. -/
theorem apply_add_self {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {B : LinearMap.BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B (x + y) (x + y) = B x x + B y y + 2 * B x y := by
  simp only [map_add, LinearMap.add_apply, hB.eq y x]
  ring

end LinearMap.BilinForm.IsSymm

namespace LinearMap

variable {R M N P : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [IsAddTorsionFree P] [Module R M] [Module R N] [Module R P] (B : M →ₗ[R] N →ₗ[R] P)

/-- A bilinear map with additively torsion-free values sees its left argument only modulo
elements of finite additive order. -/
theorem apply_eq_apply_of_isOfFinAddOrder_sub_left {x x' : M} (h : IsOfFinAddOrder (x - x'))
    (y : N) : B x y = B x' y := by
  have := ((B.flip y).toAddMonoidHom.isOfFinAddOrder h).eq_zero'
  simpa [sub_eq_zero] using this

/-- A bilinear map with additively torsion-free values sees its right argument only modulo
elements of finite additive order. -/
theorem apply_eq_apply_of_isOfFinAddOrder_sub_right {y y' : N} (h : IsOfFinAddOrder (y - y'))
    (x : M) : B x y = B x y' := by
  have := ((B x).toAddMonoidHom.isOfFinAddOrder h).eq_zero'
  simpa [sub_eq_zero] using this

end LinearMap

namespace LinearMap.BilinForm

variable {H : Type*} [AddCommGroup H] {B : LinearMap.BilinForm ℤ H} {v t x : H} {a c : ℤ}

/-- A class `x = a v + c t` modulo torsion, for a hyperbolic pair `v, t` of a `ℤ`-valued form,
has square `2ac`. -/
theorem apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub (hv : B v v = 0) (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1) (hx : IsOfFinAddOrder (x - (a • v + c • t))) :
    B x x = 2 * a * c := by
  rw [B.apply_eq_apply_of_isOfFinAddOrder_sub_left hx,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_right hx]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv, ht,
    hvt, htv]
  ring

/-- If every class is an integral combination of a hyperbolic pair `v, t` modulo torsion, the
`ℤ`-valued form is even. -/
theorem even_apply_self_of_isOfFinAddOrder_span (hv : B v v = 0) (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1)
    (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) (x : H) :
    Even (B x x) := by
  obtain ⟨a, c, hx⟩ := hspan x
  rw [apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub hv ht hvt htv hx, mul_assoc]
  exact even_two_mul _

end LinearMap.BilinForm

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

/-- **Away from characteristic two a symmetric alternating form is zero**: symmetry and alternation
force `2 * B x y = 0`, and a regular `2` cancels. -/
theorem eq_zero_of_isSymm_of_isAlt {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (h2 : IsLeftRegular (2 : R)) {B : BilinForm R M} (hsymm : B.IsSymm)
    (halt : B.IsAlt) : B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hzero : (2 : R) * B x y = 2 * 0 := by
    rw [mul_zero]
    linear_combination hsymm.eq x y - halt.neg_eq x y
  simpa using h2 hzero

/-- A scalar multiple of a bilinear form by a regular element is nondegenerate if and only if
the original form is nondegenerate. -/
@[simp]
theorem nondegenerate_smul_iff {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {B : BilinForm R M} {c : R} (hc : IsRegular c) :
    (c • B).Nondegenerate ↔ B.Nondegenerate := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hy, mul_zero]
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hx
      exact hx
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hy
      exact hy

/-- Negating a bilinear form preserves nondegeneracy. -/
@[simp]
theorem nondegenerate_neg_iff {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : BilinForm R M} :
    (-B).Nondegenerate ↔ B.Nondegenerate := by
  rw [← neg_one_smul R B]
  exact nondegenerate_smul_iff (isUnit_neg_one : IsUnit (-1 : R)).isRegular

end BilinForm

end TauCeti

namespace Module.Basis

/-- The basis dual to `b` for a nonzero scalar multiple `c • B` of a nondegenerate bilinear form
is `c⁻¹` times the basis dual to `b` for `B`. -/
@[simp]
theorem dualBasis_smul_apply {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (c : K) (hc : c ≠ 0) (i : ι) :
    LinearMap.BilinForm.dualBasis (c • B)
        ((TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB) b i =
      c⁻¹ • LinearMap.BilinForm.dualBasis B hB b i := by
  let hBc : (c • B).Nondegenerate :=
    (TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB
  apply LinearMap.ker_eq_bot.mp hBc.ker_eq_bot
  apply b.ext
  intro j
  simp only [map_smul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  split_ifs
  · simp only [mul_one, inv_mul_cancel₀ hc]
  · simp only [mul_zero]

end Module.Basis
