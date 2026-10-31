/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complex vector fields and involutive complex distributions

A *complex vector field* on a real manifold `M` is a section `Z` of the complexified tangent
bundle, assigning to every point `x` a vector `Z x` of `ℂ ⊗[ℝ] T_x M`. It is the combination
`Z = X + i Y` of its real and imaginary parts, the real vector fields
`X y = TauCeti.realPart _ (Z y)` and `Y y = TauCeti.imaginaryPart _ (Z y)`, and it is
differentiable when they are. The Lie bracket of real vector fields extends complex-bilinearly to
complex vector fields:
`[X + i Y, X' + i Y'] = ([X, X'] - [Y, Y']) + i ([X, Y'] + [Y, X'])`.

A *complex distribution* assigns to every point `x` a complex subspace `D x` of `ℂ ⊗[ℝ] T_x M`.
It is *involutive* when the complex Lie bracket of two complex vector fields tangent to `D` is again
tangent to `D`. The basic examples are the eigenbundles `T^(1,0) M` and `T^(0,1) M` of an almost
complex structure, whose involutivity is equivalent to the vanishing of its Nijenhuis tensor; this
is the integrability condition of the Newlander–Nirenberg theorem.

## Main definitions

* `TauCeti.complexMlieBracket`: the Lie bracket of complex vector fields.
* `TauCeti.IsInvolutiveComplexDistribution`: a complex distribution is involutive.

## Main results

* `TauCeti.complexMlieBracket_one_tmul_add_I_tmul`: the complex Lie bracket of `X + i Y` and
  `X' + i Y'` is `([X, X'] - [Y, Y']) + i ([X, Y'] + [Y, X'])`.
* `TauCeti.complexMlieBracket_one_tmul`: on real vector fields it is the Lie bracket.
* `TauCeti.complexMlieBracket_swap`: it is antisymmetric.
* `TauCeti.complexMlieBracket_congr`: its value at a point depends only on the germs of
  the complex vector fields there.

## Implementation notes

As for `TauCeti.IsInvolutiveDistribution`, involutivity quantifies over complex vector fields that
are only differentiable on the open set where they are tangent to `D`: one derivative is all the
Lie bracket uses.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Vol. II,
  Interscience, 1969, Chapter IX, Section 2.
-/

public section

noncomputable section

open Set VectorField
open scoped Manifold TensorProduct Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- The Lie bracket of complex vector fields on a real manifold, the complex-bilinear extension of
the Lie bracket of real vector fields: for `Z = X + i Y` and `W = X' + i Y'`, with `X, Y, X', Y'`
the real and imaginary parts, it is `([X, X'] - [Y, Y']) + i ([X, Y'] + [Y, X'])`
(`TauCeti.complexMlieBracket_one_tmul_add_I_tmul`). -/
def complexMlieBracket (Z W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x) (x : M) :
    ℂ ⊗[ℝ] TangentSpace I x :=
  (1 : ℂ) ⊗ₜ[ℝ]
      (mlieBracket I (fun y ↦ realPart (TangentSpace I y) (Z y))
          (fun y ↦ realPart (TangentSpace I y) (W y)) x -
        mlieBracket I (fun y ↦ imaginaryPart (TangentSpace I y) (Z y))
          (fun y ↦ imaginaryPart (TangentSpace I y) (W y)) x) +
    Complex.I ⊗ₜ[ℝ]
      (mlieBracket I (fun y ↦ realPart (TangentSpace I y) (Z y))
          (fun y ↦ imaginaryPart (TangentSpace I y) (W y)) x +
        mlieBracket I (fun y ↦ imaginaryPart (TangentSpace I y) (Z y))
          (fun y ↦ realPart (TangentSpace I y) (W y)) x)

/-- **The complex Lie bracket in real coordinates.** The complex Lie bracket of `X + i Y` and
`X' + i Y'` is `([X, X'] - [Y, Y']) + i ([X, Y'] + [Y, X'])`. -/
theorem complexMlieBracket_one_tmul_add_I_tmul (X Y X' Y' : Π x : M, TangentSpace I x) (x : M) :
    complexMlieBracket I (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] X y + Complex.I ⊗ₜ[ℝ] Y y)
        (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] X' y + Complex.I ⊗ₜ[ℝ] Y' y) x =
      (1 : ℂ) ⊗ₜ[ℝ] (mlieBracket I X X' x - mlieBracket I Y Y' x) +
        Complex.I ⊗ₜ[ℝ] (mlieBracket I X Y' x + mlieBracket I Y X' x) := by
  simp [complexMlieBracket]

/-- On real vector fields the complex Lie bracket is the Lie bracket. -/
@[simp]
theorem complexMlieBracket_one_tmul (X X' : Π x : M, TangentSpace I x) (x : M) :
    complexMlieBracket I (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] X y) (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] X' y) x =
      (1 : ℂ) ⊗ₜ[ℝ] mlieBracket I X X' x := by
  have h := complexMlieBracket_one_tmul_add_I_tmul (I := I) X 0 X' 0 x
  simp only [Pi.zero_apply, TensorProduct.tmul_zero, add_zero, mlieBracket_zero_left,
    mlieBracket_zero_right, sub_zero] at h
  exact h

/-- The complex Lie bracket is antisymmetric. -/
theorem complexMlieBracket_swap (Z W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x) (x : M) :
    complexMlieBracket I Z W x = -complexMlieBracket I W Z x := by
  simp only [complexMlieBracket]
  rw [mlieBracket_swap_apply (V := fun y ↦ realPart (TangentSpace I y) (Z y)),
    mlieBracket_swap_apply (V := fun y ↦ imaginaryPart (TangentSpace I y) (Z y))
      (W := fun y ↦ imaginaryPart (TangentSpace I y) (W y)),
    mlieBracket_swap_apply (V := fun y ↦ realPart (TangentSpace I y) (Z y))
      (W := fun y ↦ imaginaryPart (TangentSpace I y) (W y)),
    mlieBracket_swap_apply (V := fun y ↦ imaginaryPart (TangentSpace I y) (Z y))
      (W := fun y ↦ realPart (TangentSpace I y) (W y))]
  simp only [TensorProduct.tmul_sub, TensorProduct.tmul_add, TensorProduct.tmul_neg]
  abel

/-- The complex Lie bracket at `x` depends only on the germs at `x` of the complex vector
fields. -/
theorem complexMlieBracket_congr {Z₁ Z W₁ W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x} {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, Z₁ y = Z y) (hW : ∀ᶠ y in 𝓝 x, W₁ y = W y) :
    complexMlieBracket I Z₁ W₁ x = complexMlieBracket I Z W x := by
  have hre {V₁ V : Π x : M, ℂ ⊗[ℝ] TangentSpace I x} (h : ∀ᶠ y in 𝓝 x, V₁ y = V y) :
      (fun y ↦ realPart (TangentSpace I y) (V₁ y)) =ᶠ[𝓝 x]
        fun y ↦ realPart (TangentSpace I y) (V y) :=
    h.mono fun y hy ↦ congrArg (realPart (TangentSpace I y)) hy
  have him {V₁ V : Π x : M, ℂ ⊗[ℝ] TangentSpace I x} (h : ∀ᶠ y in 𝓝 x, V₁ y = V y) :
      (fun y ↦ imaginaryPart (TangentSpace I y) (V₁ y)) =ᶠ[𝓝 x]
        fun y ↦ imaginaryPart (TangentSpace I y) (V y) :=
    h.mono fun y hy ↦ congrArg (imaginaryPart (TangentSpace I y)) hy
  simp only [complexMlieBracket, (hre hZ).mlieBracket_vectorField_eq (hre hW),
    (him hZ).mlieBracket_vectorField_eq (him hW), (hre hZ).mlieBracket_vectorField_eq (him hW),
    (him hZ).mlieBracket_vectorField_eq (hre hW)]

variable [IsManifold I 1 M] {D : Π x : M, Submodule ℂ (ℂ ⊗[ℝ] TangentSpace I x)}

variable (I) in
/-- A complex distribution `D`, a complex subspace `D x` of `ℂ ⊗[ℝ] T_x M` at every point `x`, is
involutive: whenever two complex vector fields, with real and imaginary parts differentiable on an
open set `U`, are tangent to `D` on `U`, their complex Lie bracket is tangent to `D` on `U`. -/
def IsInvolutiveComplexDistribution (D : Π x : M, Submodule ℂ (ℂ ⊗[ℝ] TangentSpace I x)) :
    Prop :=
  ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Z W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x⦄,
    MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (Z y)) →
      MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (Z y)) →
        MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (W y)) →
          MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (W y)) →
            (∀ x ∈ U, Z x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
              ∀ x ∈ U, complexMlieBracket I Z W x ∈ D x

/-- The defining property of an involutive complex distribution. -/
theorem isInvolutiveComplexDistribution_iff :
    IsInvolutiveComplexDistribution I D ↔
      ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃Z W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x⦄,
        MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (Z y)) →
          MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (Z y)) →
            MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (W y)) →
              MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (W y)) →
                (∀ x ∈ U, Z x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
                  ∀ x ∈ U, complexMlieBracket I Z W x ∈ D x :=
  Iff.rfl

/-- The complex Lie bracket of two complex vector fields that are differentiable and tangent to an
involutive complex distribution on an open set is tangent to it there. -/
theorem IsInvolutiveComplexDistribution.complexMlieBracket_mem
    (hD : IsInvolutiveComplexDistribution I D) {U : Set M} (hU : IsOpen U)
    {Z W : Π x : M, ℂ ⊗[ℝ] TangentSpace I x}
    (hZre : MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (Z y)))
    (hZim : MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (Z y)))
    (hWre : MDiff[U] (T% fun y ↦ realPart (TangentSpace I y) (W y)))
    (hWim : MDiff[U] (T% fun y ↦ imaginaryPart (TangentSpace I y) (W y)))
    (hZD : ∀ x ∈ U, Z x ∈ D x) (hWD : ∀ x ∈ U, W x ∈ D x) {x : M} (hx : x ∈ U) :
    complexMlieBracket I Z W x ∈ D x :=
  hD hU hZre hZim hWre hWim hZD hWD x hx

end TauCeti
