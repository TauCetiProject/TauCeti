/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Discriminant

/-!
# Changes of generator and the comparison with discriminant zero

Mathlib's `QuadraticAlgebra.changeGenerator a b u k` is the `R`-algebra map
`QuadraticAlgebra R a' b' → QuadraticAlgebra R a b` sending `ω` to `u • ω + k`. This file proves
that every such map commutes with conjugation, preserves norms and traces, and commutes with the
coefficientwise maps `mapRingHom f`. None of these needs `u` to be regular.

It then specializes to `u = 2`, `k = -b`. For `B = QuadraticAlgebra R a b` of discriminant
`d = b² + 4a`, the element `2ω - b` of `B` squares to `d`, so `ω ↦ 2ω - b` defines an `R`-algebra
map `QuadraticAlgebra R d 0 → B` (`QuadraticAlgebra.algHomOfDiscrZero`). When `2` is invertible
it is the inverse of Mathlib's `algEquivDiscrZero`; in general it sends `x + yω` to
`(x - by) + 2yω`, so it is injective exactly when `2` is regular, bijective exactly when `2` is a
unit, and its image is `{x + yω | 2 ∣ y}`.

The source parameter `e` of `QuadraticAlgebra R d e` carries a hypothesis `e = 0` rather than
being the literal `0`, so that the map can be formed after a change of coefficients, where the
reduced parameter `f 0` is not syntactically `0`.

## Main definitions

* `QuadraticAlgebra.algHomOfDiscrZero`: the algebra map `QuadraticAlgebra R (discr a b) 0 → B`
  sending `ω` to `2ω - b`.

## Main results

* `QuadraticAlgebra.star_changeGenerator`, `norm_changeGenerator`, `trace_changeGenerator`,
  `mapRingHom_changeGenerator`: compatibility of every change of generator with conjugation,
  norm, trace and coefficients.
* `QuadraticAlgebra.mem_range_algHomOfDiscrZero_iff`: the image of `algHomOfDiscrZero` is
  `{z | 2 ∣ z.im}`.
* `QuadraticAlgebra.injective_algHomOfDiscrZero_iff`, `bijective_algHomOfDiscrZero_iff`:
  injectivity and bijectivity in terms of `2`.
-/

public section

namespace QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

section changeGenerator

variable {a b u k a' b' : R} (ha : a' = u ^ 2 * a - u * b * k - k ^ 2) (hb : b' = u * b + 2 * k)
include ha hb

/-- A change of generator commutes with conjugation. -/
theorem star_changeGenerator (z : QuadraticAlgebra R a' b') :
    changeGenerator a b u k ha hb (star z) = star (changeGenerator a b u k ha hb z) := by
  subst hb
  ext <;> simp
  ring

/-- A change of generator preserves norms. -/
theorem norm_changeGenerator (z : QuadraticAlgebra R a' b') :
    norm (changeGenerator a b u k ha hb z) = norm z := by
  subst ha hb
  simp [norm_def]
  ring

/-- A change of generator preserves traces. -/
theorem trace_changeGenerator (z : QuadraticAlgebra R a' b') :
    trace (changeGenerator a b u k ha hb z) = trace z := by
  subst hb
  simp [trace_def]
  ring

/-- **Compatibility with a change of coefficients.** For a ring map `f : R →+* S`, a change of
generator commutes with the coefficientwise maps `mapRingHom f`. -/
theorem mapRingHom_changeGenerator (f : R →+* S) (z : QuadraticAlgebra R a' b') :
    mapRingHom f a b (changeGenerator a b u k ha hb z) =
      changeGenerator (f a) (f b) (f u) (f k) (by simp [ha]) (by simp [hb, map_ofNat])
        (mapRingHom f a' b' z) := by
  ext <;> simp

end changeGenerator

section DiscrZero

variable {a b d e : R}

variable (a b) in
/-- **The comparison with discriminant zero.** For `d = discr a b = b² + 4a` and `e = 0`, the
`R`-algebra map `QuadraticAlgebra R d e → QuadraticAlgebra R a b` sending `ω` to `2ω - b`, the
change of generator with `u = 2` and `k = -b`. It runs opposite to Mathlib's
`algEquivDiscrZero`. -/
def algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) :
    QuadraticAlgebra R d e →ₐ[R] QuadraticAlgebra R a b :=
  changeGenerator a b 2 (-b) (by rw [hd, discr_def]; ring) (by rw [he]; ring)

@[simp]
theorem re_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    (algHomOfDiscrZero a b hd he z).re = z.re - b * z.im := by
  simp [algHomOfDiscrZero]
  ring

@[simp]
theorem im_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    (algHomOfDiscrZero a b hd he z).im = 2 * z.im := by
  simp [algHomOfDiscrZero, mul_comm]

/-- `algHomOfDiscrZero` sends `ω` to `2ω - b`, whose square is `discr a b`. -/
@[simp]
theorem algHomOfDiscrZero_omega (hd : d = discr a b) (he : e = 0) :
    algHomOfDiscrZero a b hd he ω = ⟨-b, 2⟩ := by
  ext <;> simp

/-- When `2` is invertible, `algHomOfDiscrZero` is the inverse of Mathlib's
`algEquivDiscrZero`. -/
theorem algHomOfDiscrZero_eq_algEquivDiscrZero_symm [Invertible (2 : R)] :
    algHomOfDiscrZero a b rfl rfl = ((algEquivDiscrZero a b).symm : _ →ₐ[R] _) :=
  algHom_ext (by ext <;> simp)

/-- `algHomOfDiscrZero` is injective exactly when `2` is regular in `R`. -/
theorem injective_algHomOfDiscrZero_iff (hd : d = discr a b) (he : e = 0) :
    Function.Injective (algHomOfDiscrZero a b hd he) ↔ IsRegular (2 : R) := by
  rw [← isRegular_im_omega_iff_injective, im_algHomOfDiscrZero, im_omega, mul_one]

/-- `algHomOfDiscrZero` is bijective exactly when `2` is a unit in `R`. -/
theorem bijective_algHomOfDiscrZero_iff (hd : d = discr a b) (he : e = 0) :
    Function.Bijective (algHomOfDiscrZero a b hd he) ↔ IsUnit (2 : R) := by
  rw [← isUnit_im_omega_iff_bijective, im_algHomOfDiscrZero, im_omega, mul_one]

/-- **The image of the comparison.** An element of `QuadraticAlgebra R a b` lies in the image
of `algHomOfDiscrZero` exactly when `2` divides its `ω`-coordinate. -/
theorem mem_range_algHomOfDiscrZero_iff (hd : d = discr a b) (he : e = 0)
    {z : QuadraticAlgebra R a b} :
    z ∈ (algHomOfDiscrZero a b hd he).range ↔ 2 ∣ z.im := by
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ⟨⟨z.re + b * y, y⟩, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.im, im_algHomOfDiscrZero hd he w⟩
  · ext <;> simp [hy]

/-- `algHomOfDiscrZero` commutes with conjugation. -/
theorem star_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    algHomOfDiscrZero a b hd he (star z) = star (algHomOfDiscrZero a b hd he z) :=
  star_changeGenerator _ _ z

/-- `algHomOfDiscrZero` preserves norms. -/
theorem norm_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    norm (algHomOfDiscrZero a b hd he z) = norm z :=
  norm_changeGenerator _ _ z

/-- `algHomOfDiscrZero` preserves traces. -/
theorem trace_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    trace (algHomOfDiscrZero a b hd he z) = trace z :=
  trace_changeGenerator _ _ z

/-- For a ring map `f : R →+* S`, `algHomOfDiscrZero` commutes with the coefficientwise maps
`mapRingHom f`. -/
theorem mapRingHom_algHomOfDiscrZero (f : R →+* S) (hd : d = discr a b) (he : e = 0)
    (z : QuadraticAlgebra R d e) :
    mapRingHom f a b (algHomOfDiscrZero a b hd he z) =
      algHomOfDiscrZero (f a) (f b) (by rw [hd, map_discr]) (by rw [he, map_zero])
        (mapRingHom f d e z) := by
  simp only [algHomOfDiscrZero, mapRingHom_changeGenerator, map_ofNat, map_neg]

end DiscrZero

end QuadraticAlgebra
