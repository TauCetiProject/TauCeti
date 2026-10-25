/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed
public import TauCeti.CategoryTheory.FiniteBijection
public import TauCeti.CategoryTheory.Monoidal.DayConvolution.Braided
public import TauCeti.CategoryTheory.Monoidal.DayConvolution.Closed
public import TauCeti.CategoryTheory.Monoidal.DayConvolution.Unit

/-!
# Symmetric sequences of pointed simplicial sets

A symmetric sequence of pointed simplicial sets is a functor `X` from the finite-bijection
groupoid to pointed simplicial sets: a sequence of pointed simplicial sets `X_n`, the value at
the standard finite set `Fin n`, with a based action of the symmetric group `Σ_n` on each.

Symmetric sequences carry the Day convolution product along the block sum of finite sets. Its
`n`-th level is the left Kan extension
`(X ⊗ Y)_n = colim_{Fin p ⊕ Fin q ≃ Fin n} X_p ∧ Y_q`,
which Hovey, Shipley and Smith write as the wedge `⋁_{p+q=n} (Σ_n)₊ ∧_{Σ_p × Σ_q} (X_p ∧ Y_q)`
of induced representations; that identification is not formalized here. We define
`SymmetricSequence` as Mathlib's type synonym `FiniteBijection ⊛⥤ PointedSSet` carrying the Day
convolution monoidal structure, and check that the hypotheses of Mathlib's construction hold:

* pointed simplicial sets have all small colimits, as an undercategory of simplicial sets, so
  the Day convolution and its unit exist as pointwise left Kan extensions;
* the smash product of pointed simplicial sets is closed and symmetric, so smashing with a fixed
  pointed simplicial set on either side preserves colimits.

As the block sum on finite sets and the smash product are symmetric, Day convolution makes
symmetric sequences a symmetric monoidal category. Its unit is the zero sphere `S⁰` in level
zero and the point in every positive level: the instance `DayFunctor.isIso_ν` identifies level
zero with `S⁰`, and `SymmetricSequence.isInitialUnitObj` shows that each positive level, which
receives no bijection from `Fin 0`, is initial, that is, isomorphic to the one-point pointed
simplicial set.

Pointed simplicial sets are complete and closed, so this symmetric monoidal structure is closed:
the internal hom of symmetric sequences has levels
`Hom(X, Y)_n = ∫_k Map_*(X_k, Y_(k+n))`, the end over the finite-bijection groupoid. Hovey, Shipley
and Smith write it as the product `∏_k Map_{Σ_k}(X_k, Y_(k+n))` of equivariant mapping spaces; that
identification is not formalized here.

Symmetric spectra are the modules over the commutative monoid of spheres in this symmetric
monoidal category.

## Main definitions

* `SymmetricSequence`: symmetric sequences of pointed simplicial sets, with the Day convolution
  product.
* The symmetric monoidal structure on `SymmetricSequence`, the instance
  `DayFunctor.symmetricCategory`, and its closed structure, the instance
  `DayFunctor.monoidalClosed`.

## Main statements

* `SymmetricSequence.isInitialUnitObj`: the unit symmetric sequence is initial in every positive
  level.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.1.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti

open scoped DayFunctor

/-- Symmetric sequences of pointed simplicial sets: functors from the finite-bijection groupoid
to pointed simplicial sets, with the Day convolution product along the block sum. -/
abbrev SymmetricSequence := FiniteBijection ⊛⥤ PointedSSet.{u}

/- Day convolution makes symmetric sequences of pointed simplicial sets a symmetric monoidal
category, through the instance `DayFunctor.symmetricCategory`. -/
noncomputable example : SymmetricCategory SymmetricSequence.{u} := inferInstance

/- The Day convolution of symmetric sequences is closed, through the instance
`DayFunctor.monoidalClosed`, with the internal hom `DayFunctor.internalHom`. -/
noncomputable example : MonoidalClosed SymmetricSequence.{u} := inferInstance

/-- The unit symmetric sequence is initial, the point, in every positive level `n + 1`: no
bijection reaches `Fin (n + 1)` from `Fin 0`. -/
noncomputable def SymmetricSequence.isInitialUnitObj (n : ℕ) :
    Limits.IsInitial ((𝟙_ SymmetricSequence.{u}).functor.obj (FiniteBijection.mk (n + 1))) :=
  DayFunctor.isInitialUnitObj

end TauCeti
