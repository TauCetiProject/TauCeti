/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Associator
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.CayleyDickson.Quaternion

/-!
# The imaginary octonions and their cross product

Let `A = CayleyDickson ℍ[R]` be the Cayley–Dickson double of the quaternions over a commutative
ring `R`; for `R = ℝ` this is the algebra of real (division) octonions
`TauCeti.DivisionOctonionReal`. This file sets up the seven-dimensional geometry of its imaginary
part: an inner product, a cross product and a trilinear form, all built from the multiplication
and the real part alone, so that they are preserved by every automorphism of the octonions. This
is the structure from which the compact real form of `G₂` is built.

* The **imaginary octonions** `Im A = ker T` are the kernel of the trace
  (`TauCeti.CayleyDickson.imaginary`); over a field in which `2` is invertible they have
  dimension `7`.
* The bilinear form `g x y = -Re (x * y)` (`TauCeti.CayleyDickson.imaginaryForm`) is symmetric,
  and on `Im A` it is the inner product: `g v v = N v`, so over a linearly ordered ring it is
  positive definite there.
* The **cross product** `x × y = (x * y - y * x) / 2` (`TauCeti.CayleyDickson.cross`), defined when
  `2` is invertible, is antisymmetric and takes values in `Im A`. On imaginary octonions the
  product splits into its real and imaginary parts as `v * w = -g v w • 1 + v × w`.
* The trilinear form `φ u v w = g (u × v) w` (`TauCeti.CayleyDickson.associativeForm`) is
  alternating: it changes sign under the exchange of its first two arguments and is invariant
  under cyclic permutations. In particular `u × v` is orthogonal to `u` and to `v`.

From these, two identities of the seven-dimensional cross product follow for imaginary `u`, `v`,
`w`:

* `u × (u × v) = g u v • u - g u u • v`, and the norm identity
  `N (u × v) = g u u * g v v - (g u v) ^ 2`;
* the **associator identity**
  `(u × v) × w - u × (v × w) = associator u v w + g u v • w - g v w • u`,
  where `associator u v w = (u * v) * w - u * (v * w)` is Mathlib's `associator`.

Since the octonions are not associative, even on imaginary elements
(`TauCeti.DivisionOctonionReal.exists_mul_mul_ne`), the familiar three-dimensional expansion of
`(u × v) × w` for three unrelated vectors does not hold in dimension seven; the associator identity
records the correction. In the special case `u × (u × v)` the associator vanishes by the
alternative law, and the three-dimensional form survives.

## Main definitions

* `TauCeti.CayleyDickson.imaginary`: the imaginary octonions, the kernel of the trace.
* `TauCeti.CayleyDickson.imaginaryForm`: the bilinear form `g x y = -Re (x * y)`.
* `TauCeti.CayleyDickson.cross`: the cross product `x × y = (x * y - y * x) / 2`.
* `TauCeti.CayleyDickson.associativeForm`: the trilinear form `φ u v w = g (u × v) w`.

## Main results

* `TauCeti.CayleyDickson.finrank_imaginary`: the imaginary octonions are `7`-dimensional.
* `TauCeti.CayleyDickson.imaginaryForm_self_of_mem` and
  `TauCeti.CayleyDickson.imaginaryForm_self_pos`: `g v v = N v` on imaginary octonions, so `g` is
  positive definite there; `TauCeti.CayleyDickson.normSq_add_of_mem` exhibits `g` as the polar
  form of the norm.
* `TauCeti.CayleyDickson.mul_eq_neg_smul_one_add_cross`: `v * w = -g v w • 1 + v × w`.
* `TauCeti.CayleyDickson.associativeForm_swap` and `TauCeti.CayleyDickson.associativeForm_rotate`:
  `φ` is alternating.
* `TauCeti.CayleyDickson.cross_cross_eq_smul_sub_smul`: `u × (u × v) = g u v • u - g u u • v`.
* `TauCeti.CayleyDickson.normSq_cross`: `N (u × v) = g u u * g v v - (g u v) ^ 2`.
* `TauCeti.CayleyDickson.cross_cross_sub_cross_cross`: the associator identity.

## Implementation notes

Only one identity is proved here in coordinates, by splitting an octonion into the eight
coordinates of its two quaternion components and closing the resulting polynomial identity with
`ring`: the anticommutator `v * w + w * v = -(2 * g v w) • 1` of imaginary octonions. Everything
else is derived from it, from the invariance of the real part of a product under exchanging and
reassociating factors (`TauCeti.CayleyDickson.re_mul_comm`, `TauCeti.CayleyDickson.re_mul_mul`),
from the rank-two equation `TauCeti.CayleyDickson.mul_self` and from the left alternative law.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §4.1.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Chapter IV.1: the cross product on the imaginary octonions and the associative calibration.
* D. A. Salamon and T. Walpuski, *Notes on the octonions*, Proceedings of the 23rd Gökova
  Geometry–Topology Conference (2017), 1–85, §2–§3.
-/

public section

namespace TauCeti

namespace CayleyDickson

open Module

open scoped Quaternion

section CommRing

variable {R : Type*} [CommRing R]

/-! ### The imaginary octonions -/

variable (R) in
/-- **The imaginary octonions**, the kernel of the trace of the double of the quaternions. Over a
field in which `2` is invertible they form a `7`-dimensional subspace
(`TauCeti.CayleyDickson.finrank_imaginary`), consisting of the elements with vanishing real part
(`TauCeti.CayleyDickson.mem_imaginary_iff_re`). -/
def imaginary : Submodule R (CayleyDickson ℍ[R]) := LinearMap.ker trace

@[simp]
theorem mem_imaginary {x : CayleyDickson ℍ[R]} : x ∈ imaginary R ↔ trace x = 0 :=
  LinearMap.mem_ker

/-- **Conjugation negates exactly the imaginary octonions**. Not a `simp` lemma, because
`TauCeti.CayleyDickson.mem_imaginary` already takes its left-hand side apart. -/
theorem mem_imaginary_iff_star_eq_neg {x : CayleyDickson ℍ[R]} :
    x ∈ imaginary R ↔ star x = -x := by
  rw [mem_imaginary]
  refine ⟨fun h => by rw [star_eq_trace_smul_one_sub, h, zero_smul, zero_sub], fun h => ?_⟩
  have h₁ := star_add_self x
  rw [h, neg_add_cancel] at h₁
  simpa using (congrArg (fun y : CayleyDickson ℍ[R] => y.fst.re) h₁).symm

/-! ### The form `g` -/

/-- The bilinear form `g x y = -Re (x * y)` on the double of the quaternions. It is symmetric
(`TauCeti.CayleyDickson.isSymm_imaginaryForm`), and on the imaginary octonions it is the inner
product: `g v v` is the norm of `v` (`TauCeti.CayleyDickson.imaginaryForm_self_of_mem`), positive
for `v ≠ 0` over a linearly ordered ring. -/
def imaginaryForm : LinearMap.BilinForm R (CayleyDickson ℍ[R]) :=
  LinearMap.mk₂ R (fun x y => -(x * y).fst.re)
    (fun x₁ x₂ y => by simp only [add_mul, add_fst, Quaternion.re_add]; ring)
    (fun r x y => by
      simp only [smul_mul_assoc, smul_fst, Quaternion.re_smul, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [mul_add, add_fst, Quaternion.re_add]; ring)
    (fun r x y => by
      simp only [mul_smul_comm, smul_fst, Quaternion.re_smul, smul_eq_mul]; ring)

@[simp]
theorem imaginaryForm_apply (x y : CayleyDickson ℍ[R]) :
    imaginaryForm x y = -(x * y).fst.re := (rfl)

theorem imaginaryForm_comm (x y : CayleyDickson ℍ[R]) : imaginaryForm x y = imaginaryForm y x := by
  rw [imaginaryForm_apply, imaginaryForm_apply, re_mul_comm]

/-- The form `g` is symmetric. -/
theorem isSymm_imaginaryForm :
    LinearMap.BilinForm.IsSymm (imaginaryForm : LinearMap.BilinForm R (CayleyDickson ℍ[R])) :=
  ⟨imaginaryForm_comm⟩

/-- On an imaginary octonion `v`, the form `g v v` is the norm of `v`: the rank-two equation
`v * v = T v • v - N v • 1` reads `v * v = -N v • 1` when `T v = 0`. -/
theorem imaginaryForm_self_of_mem {v : CayleyDickson ℍ[R]} (hv : v ∈ imaginary R) :
    imaginaryForm v v = normSq v := by
  rw [imaginaryForm_apply, mul_self, mem_imaginary.mp hv]
  simp

/-- On an imaginary octonion `w`, the form `g v w` is the real part of `v * star w`, the
polarization of the norm. -/
theorem imaginaryForm_eq_re_mul_star (v : CayleyDickson ℍ[R]) {w : CayleyDickson ℍ[R]}
    (hw : w ∈ imaginary R) :
    imaginaryForm v w = (v * star w).fst.re := by
  rw [mem_imaginary_iff_star_eq_neg.mp hw, mul_neg, imaginaryForm_apply, neg_fst,
    Quaternion.re_neg]

/-- **The norm identity for a sum with an imaginary octonion**: `g` is the polar form of the
norm, `N (v + w) = N v + N w + 2 g v w` when `w` is imaginary. -/
theorem normSq_add_of_mem (v : CayleyDickson ℍ[R]) {w : CayleyDickson ℍ[R]}
    (hw : w ∈ imaginary R) : normSq (v + w) = normSq v + normSq w + 2 * imaginaryForm v w := by
  rw [normSq_add, imaginaryForm_eq_re_mul_star v hw]

section LinearOrder

variable [LinearOrder R] [IsStrictOrderedRing R] {v : CayleyDickson ℍ[R]}

theorem imaginaryForm_self_nonneg (hv : v ∈ imaginary R) : 0 ≤ imaginaryForm v v := by
  rw [imaginaryForm_self_of_mem hv]
  exact normSq_nonneg

/-- **The form `g` is positive definite on the imaginary octonions** over a linearly ordered
ring. -/
theorem imaginaryForm_self_pos (hv : v ∈ imaginary R) (hv₀ : v ≠ 0) : 0 < imaginaryForm v v := by
  rwa [imaginaryForm_self_of_mem hv, normSq_pos]

theorem imaginaryForm_self_eq_zero_iff (hv : v ∈ imaginary R) : imaginaryForm v v = 0 ↔ v = 0 := by
  rw [imaginaryForm_self_of_mem hv, normSq_eq_zero]

end LinearOrder

/-! ### Imaginary octonions when `2` is invertible -/

section Invertible

variable [Invertible (2 : R)]

/-- When `2` is invertible, an octonion is imaginary exactly when its real part vanishes. -/
theorem mem_imaginary_iff_re {x : CayleyDickson ℍ[R]} : x ∈ imaginary R ↔ x.fst.re = 0 := by
  rw [mem_imaginary, trace_apply]
  refine ⟨fun h => ?_, fun h => by rw [h, mul_zero]⟩
  rw [← invOf_mul_cancel_left (2 : R) x.fst.re, h, mul_zero]

/-- When `2` is invertible, the trace is onto: `T (r • ⅟2 • 1) = r`. -/
theorem trace_surjective : Function.Surjective (trace : CayleyDickson ℍ[R] →ₗ[R] R) :=
  fun r => ⟨r • ⅟(2 : R) • (1 : CayleyDickson ℍ[R]), by
    rw [map_smul, map_smul, trace_one, smul_eq_mul, smul_eq_mul, invOf_mul_self, mul_one]⟩

/-- The anticommutator of two imaginary octonions is a scalar:
`v * w + w * v = -(2 * g v w) • 1`. -/
theorem mul_add_mul_swap_of_mem {v w : CayleyDickson ℍ[R]} (hv : v ∈ imaginary R)
    (hw : w ∈ imaginary R) :
    v * w + w * v = -(2 * imaginaryForm v w) • (1 : CayleyDickson ℍ[R]) := by
  have hv' := mem_imaginary_iff_re.mp hv
  have hw' := mem_imaginary_iff_re.mp hw
  ext <;> simp [hv', hw'] <;> ring

/-! ### The cross product -/

/-- **The cross product** `x × y = (x * y - y * x) / 2` of the double of the quaternions. It is
antisymmetric, takes values in the imaginary octonions
(`TauCeti.CayleyDickson.cross_mem_imaginary`), and on imaginary octonions it is the imaginary part
of the product
(`TauCeti.CayleyDickson.mul_eq_neg_smul_one_add_cross`). -/
def cross : CayleyDickson ℍ[R] →ₗ[R] CayleyDickson ℍ[R] →ₗ[R] CayleyDickson ℍ[R] :=
  ⅟(2 : R) • (LinearMap.mul R (CayleyDickson ℍ[R]) - (LinearMap.mul R (CayleyDickson ℍ[R])).flip)

theorem cross_apply (x y : CayleyDickson ℍ[R]) : cross x y = ⅟(2 : R) • (x * y - y * x) := by
  simp [cross]

theorem cross_swap (x y : CayleyDickson ℍ[R]) : cross y x = -cross x y := by
  rw [cross_apply, cross_apply, ← smul_neg, neg_sub]

@[simp]
theorem cross_self (x : CayleyDickson ℍ[R]) : cross x x = 0 := by
  simp [cross_apply]

/-- The cross product of any two octonions is imaginary. -/
theorem cross_mem_imaginary (x y : CayleyDickson ℍ[R]) : cross x y ∈ imaginary R := by
  rw [mem_imaginary_iff_re, cross_apply, smul_fst, Quaternion.re_smul, sub_fst,
    Quaternion.re_sub, re_mul_comm y x, sub_self, smul_zero]

/-- On imaginary octonions the cross product is the product corrected by its real part:
`v × w = v * w + g v w • 1`. -/
theorem cross_eq_mul_add_smul_one {v w : CayleyDickson ℍ[R]} (hv : v ∈ imaginary R)
    (hw : w ∈ imaginary R) : cross v w = v * w + imaginaryForm v w • 1 := by
  rw [cross_apply, eq_sub_of_add_eq' (mul_add_mul_swap_of_mem hv hw),
    show v * w - (-(2 * imaginaryForm v w) • (1 : CayleyDickson ℍ[R]) - v * w) =
      (2 : R) • (v * w + imaginaryForm v w • 1) by module,
    smul_smul, invOf_mul_self, one_smul]

/-- **The product of two imaginary octonions** splits into its real and imaginary parts as
`v * w = -g v w • 1 + v × w`. -/
theorem mul_eq_neg_smul_one_add_cross {v w : CayleyDickson ℍ[R]} (hv : v ∈ imaginary R)
    (hw : w ∈ imaginary R) : v * w = -imaginaryForm v w • 1 + cross v w := by
  rw [cross_eq_mul_add_smul_one hv hw, neg_smul]
  abel

/-! ### The associative form -/

/-- The trilinear form `φ u v w = g (u × v) w`. It is alternating
(`TauCeti.CayleyDickson.associativeForm_swap` and
`TauCeti.CayleyDickson.associativeForm_rotate`); restricted to the imaginary octonions it is the
associative `3`-form of Harvey and Lawson. -/
def associativeForm :
    CayleyDickson ℍ[R] →ₗ[R] CayleyDickson ℍ[R] →ₗ[R] CayleyDickson ℍ[R] →ₗ[R] R :=
  cross.compr₂ imaginaryForm

@[simp]
theorem associativeForm_apply (u v w : CayleyDickson ℍ[R]) :
    associativeForm u v w = imaginaryForm (cross u v) w := (rfl)

/-- The form `φ` changes sign when its first two arguments are exchanged. -/
theorem associativeForm_swap (u v w : CayleyDickson ℍ[R]) :
    associativeForm v u w = -associativeForm u v w := by
  rw [associativeForm_apply, associativeForm_apply, cross_swap u v, map_neg, LinearMap.neg_apply]

/-- The form `φ` is invariant under cyclic permutations of its arguments:
`g (v × w) u = g (u × v) w`. -/
theorem associativeForm_rotate (u v w : CayleyDickson ℍ[R]) :
    associativeForm v w u = associativeForm u v w := by
  simp only [associativeForm_apply, imaginaryForm_apply, cross_apply, smul_mul_assoc, sub_mul,
    smul_fst, sub_fst, Quaternion.re_smul, Quaternion.re_sub, smul_eq_mul, neg_inj]
  rw [re_mul_comm (v * w) u, ← re_mul_mul, re_mul_mul w v u, re_mul_comm w (v * u)]

theorem associativeForm_self_left (u w : CayleyDickson ℍ[R]) : associativeForm u u w = 0 := by
  simp

theorem associativeForm_self_right (u v : CayleyDickson ℍ[R]) : associativeForm u v v = 0 := by
  rw [← associativeForm_rotate, associativeForm_self_left]

/-- The cross product `u × v` is orthogonal to `u`. -/
theorem imaginaryForm_cross_self_left (u v : CayleyDickson ℍ[R]) :
    imaginaryForm (cross u v) u = 0 := by
  rw [← associativeForm_apply, ← associativeForm_rotate, associativeForm_self_right]

/-- The cross product `u × v` is orthogonal to `v`. -/
theorem imaginaryForm_cross_self_right (u v : CayleyDickson ℍ[R]) :
    imaginaryForm (cross u v) v = 0 := by
  rw [← associativeForm_apply, associativeForm_self_right]

/-! ### Identities of the seven-dimensional cross product -/

/-- **The double cross product with a repeated factor**: for imaginary `u` and `v`,
`u × (u × v) = g u v • u - g u u • v`. Here the associator `(u * u) * v - u * (u * v)` vanishes by
the alternative law, so the three-dimensional formula survives; for three unrelated factors it does
not (`TauCeti.CayleyDickson.cross_cross_sub_cross_cross`). -/
theorem cross_cross_eq_smul_sub_smul {u v : CayleyDickson ℍ[R]} (hu : u ∈ imaginary R)
    (hv : v ∈ imaginary R) :
    cross u (cross u v) = imaginaryForm u v • u - imaginaryForm u u • v := by
  have huu : u * u = -imaginaryForm u u • (1 : CayleyDickson ℍ[R]) := by
    rw [mul_self, mem_imaginary.mp hu, imaginaryForm_self_of_mem hu, zero_smul, zero_sub, neg_smul]
  rw [cross_eq_mul_add_smul_one hu (cross_mem_imaginary u v), imaginaryForm_comm u (cross u v),
    imaginaryForm_cross_self_left, zero_smul, add_zero, cross_eq_mul_add_smul_one hu hv, mul_add,
    mul_smul_comm, mul_one, ← left_alternative, huu, smul_mul_assoc, one_mul]
  module

/-- **The norm of a cross product**: for imaginary `u` and `v`,
`N (u × v) = g u u * g v v - (g u v) ^ 2`. -/
theorem normSq_cross {u v : CayleyDickson ℍ[R]} (hu : u ∈ imaginary R) (hv : v ∈ imaginary R) :
    normSq (cross u v) = imaginaryForm u u * imaginaryForm v v - imaginaryForm u v ^ 2 := by
  rw [← imaginaryForm_self_of_mem (cross_mem_imaginary u v), ← associativeForm_apply,
    associativeForm_rotate, associativeForm_apply, cross_swap u (cross u v), map_neg,
    LinearMap.neg_apply,
    cross_cross_eq_smul_sub_smul hu hv, map_sub, map_smul, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **The associator identity of the seven-dimensional cross product**: for imaginary `u`, `v`
and `w`,

`(u × v) × w - u × (v × w) = associator u v w + g u v • w - g v w • u`.

The cross product is therefore not associative, and its failure to satisfy the three-dimensional
double cross product formula is measured by the octonion associator. -/
theorem cross_cross_sub_cross_cross {u v w : CayleyDickson ℍ[R]} (hu : u ∈ imaginary R)
    (hv : v ∈ imaginary R) (hw : w ∈ imaginary R) :
    cross (cross u v) w - cross u (cross v w) =
      associator u v w + imaginaryForm u v • w - imaginaryForm v w • u := by
  rw [cross_eq_mul_add_smul_one (cross_mem_imaginary u v) hw,
    cross_eq_mul_add_smul_one hu (cross_mem_imaginary v w), imaginaryForm_comm u (cross v w),
    ← associativeForm_apply, ← associativeForm_apply, associativeForm_rotate u v w,
    cross_eq_mul_add_smul_one hu hv, cross_eq_mul_add_smul_one hv hw, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, associator_apply]
  abel

end Invertible

end CommRing

/-! ### Dimension -/

/-- **The imaginary octonions are `7`-dimensional** over a field in which `2` is invertible, such
as `ℝ`: the trace is a nonzero linear form on the `8`-dimensional double of the quaternions. -/
theorem finrank_imaginary (K : Type*) [Field K] [Invertible (2 : K)] :
    finrank K (imaginary K) = 7 := by
  have h := LinearMap.finrank_range_add_finrank_ker (trace : CayleyDickson ℍ[K] →ₗ[K] K)
  rw [LinearMap.range_eq_top.mpr trace_surjective, finrank_top, finrank_self, finrank_eq,
    Quaternion.finrank_eq_four] at h
  unfold imaginary
  omega

end CayleyDickson

end TauCeti
