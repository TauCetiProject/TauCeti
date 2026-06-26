/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic
public import TauCeti.Analysis.PositiveDefinite.Kernel

/-!
# The positive-definite function ↔ positive-definite kernel correspondence

A positive-definite function `F : M → ℂ` on an involutive additive monoid and a positive-definite
kernel `K : M → M → ℂ` are two views of the same data, linked by the assignment
`K(a, b) = F(a + b⋆)`. This file proves that `F` is positive definite (`TauCeti.IsPositiveDefinite`,
from `TauCeti.Analysis.PositiveDefinite.Basic`) **if and only if** the two-variable kernel
`fun a b => F (a + star b)` is positive definite (`TauCeti.IsPositiveDefiniteKernel`, from
`TauCeti.Analysis.PositiveDefinite.Kernel`).

Both predicates express nonnegativity of finite quadratic forms, with
`IsPositiveDefiniteKernel` using Mathlib's `Matrix.PosSemidef` convention for the two-variable
kernel.

Under the negation involution `a⋆ = -a` the kernel takes the familiar translation-invariant shape
`K(a, b) = F(a - b)`, the form in which positive definiteness is usually stated on groups such as
`ℝᵈ` or a real inner-product space. We record that specialization as a corollary parameterized by
the hypothesis `star a = -a` (Mathlib pins no such `StarAddMonoid` instance, since `star` is the
identity on a real vector space, so the negation involution is supplied as a side hypothesis rather
than an instance).

This advances the `OneParameterSemigroups` roadmap, Part C ("Positive-definite functions and
Bochner's theorem", `TauCetiRoadmap/OneParameterSemigroups/README.md`): the `API to develop` bullet
"the PD-function ↔ PD-kernel equivalence (`K(a, b) = F(a + b⋆)`; `F(a − b)` for a group)". The two
component predicates already live in TauCeti; this file is the equivalence connecting them, and the
group form. No Mathlib code is vendored.

## Main declarations

* `TauCeti.IsPositiveDefinite.isPositiveDefiniteKernel`: a positive-definite function gives the
  positive-definite kernel `fun a b => F (a + star b)`.
* `TauCeti.IsPositiveDefinite.of_isPositiveDefiniteKernel`: conversely, if the kernel
  `fun a b => F (a + star b)` is positive definite then `F` is positive definite.
* `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteKernel`: the equivalence of the two predicates.
* `TauCeti.IsPositiveDefinite.isPositiveDefiniteKernel_sub` and
  `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteKernel_sub`: the subtraction form
  `K(a, b) = F(a - b)` under the negation involution `star a = -a`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M] {F : M → ℂ}

/-- The Hermitian form of the kernel `K(a, b) = F(a + b⋆)` with coefficients `x` over a finite
family is `F`'s defining form with coefficients `conj x`, hence nonnegative. This is stated as its
own (universe-polymorphic in the index `ι`) lemma so that it can be fed to
`TauCeti.isPositiveDefiniteKernel_iff`. -/
private theorem kernel_form_nonneg (hF : IsPositiveDefinite F) {ι : Type*} [Fintype ι]
    (v : ι → M) (x : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, conj (x i) * x j * F (v i + star (v j)) := by
  have h := hF.sum_nonneg (fun i => conj (x i)) v
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj]

/-- A positive-definite function `F` induces the positive-definite kernel `K(a, b) = F(a + b⋆)`.
This is the forward half of the function ↔ kernel correspondence. -/
theorem isPositiveDefiniteKernel (hF : IsPositiveDefinite F) :
    IsPositiveDefiniteKernel (fun a b => F (a + star b)) :=
  isPositiveDefiniteKernel_iff.mpr
    ⟨fun a b => hF.conj_symm b a, fun {_ι : Type} _ v x => hF.kernel_form_nonneg v x⟩

/-- If the kernel `K(a, b) = F(a + b⋆)` is positive definite, then so is the function `F`. This is
the reverse half of the function ↔ kernel correspondence. -/
theorem of_isPositiveDefiniteKernel
    (hK : IsPositiveDefiniteKernel (fun a b => F (a + star b))) : IsPositiveDefinite F := by
  obtain ⟨_, hpos⟩ := isPositiveDefiniteKernel_iff.mp hK
  intro n c v
  have h := hpos v (fun i => conj (c i))
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj]

end IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M] {F : M → ℂ}

/-- A function `F` on an involutive additive monoid is positive definite if and only if the
two-variable kernel `K(a, b) = F(a + b⋆)` is positive definite. -/
theorem isPositiveDefinite_iff_isPositiveDefiniteKernel :
    IsPositiveDefinite F ↔ IsPositiveDefiniteKernel (fun a b => F (a + star b)) :=
  ⟨IsPositiveDefinite.isPositiveDefiniteKernel, IsPositiveDefinite.of_isPositiveDefiniteKernel⟩

namespace IsPositiveDefinite

variable {G : Type*} [SubNegMonoid G] [StarAddMonoid G] {F : G → ℂ}

/-- Under the negation involution `a⋆ = -a`, a positive-definite function `F` gives the
translation-invariant positive-definite kernel `K(a, b) = F(a - b)`. This is the form in which
positive definiteness is usually stated on groups such as `ℝᵈ` or a real inner-product space. -/
theorem isPositiveDefiniteKernel_sub (hstar : ∀ a : G, star a = -a) (hF : IsPositiveDefinite F) :
    IsPositiveDefiniteKernel (fun a b => F (a - b)) := by
  have hfun : (fun a b : G => F (a + star b)) = fun a b => F (a - b) := by
    funext a b
    rw [hstar, ← sub_eq_add_neg]
  rw [← hfun]
  exact hF.isPositiveDefiniteKernel

end IsPositiveDefinite

variable {G : Type*} [SubNegMonoid G] [StarAddMonoid G] {F : G → ℂ}

/-- Under the negation involution `a⋆ = -a`, `F` is positive definite if and only if the
translation-invariant kernel `K(a, b) = F(a - b)` is positive definite. -/
theorem isPositiveDefinite_iff_isPositiveDefiniteKernel_sub (hstar : ∀ a : G, star a = -a) :
    IsPositiveDefinite F ↔ IsPositiveDefiniteKernel (fun a b => F (a - b)) := by
  have hfun : (fun a b : G => F (a + star b)) = fun a b => F (a - b) := by
    funext a b
    rw [hstar, ← sub_eq_add_neg]
  rw [isPositiveDefinite_iff_isPositiveDefiniteKernel, hfun]

end TauCeti
