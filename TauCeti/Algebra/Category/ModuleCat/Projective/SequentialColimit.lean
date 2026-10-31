/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# The projective dimension of a sequential colimit of modules

Let `F₀ → F₁ → F₂ → ⋯` be a sequence of `R`-modules, a functor `F : ℕ ⥤ ModuleCat R`, with
colimit `M`. Dimension shifting along the telescope short exact sequence
`0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → M → 0` (`ModuleCat.shortExact_telescopeShortComplex`) shows that if every
`Fₙ` has projective dimension at most `d`, then `M` has projective dimension at most `d + 1`: the
direct sum `⨁ₙ Fₙ` has projective dimension at most `d`, as coproducts of modules are exact.

The bound is sharp: `ℚ` is the colimit of `ℤ →2 ℤ →3 ℤ →4 ⋯` (multiplication by `n + 2` at the
`n`-th step) of free `ℤ`-modules but is not projective. This is how a bound on the projective
dimension of modules over the stages of a sequential colimit of rings, such as the perfection of
a ring of characteristic `p`, leads to a bound over the colimit.

## Main declarations

* `ModuleCat.hasProjectiveDimensionLT_succ_of_isColimit`: the colimit of a sequence of modules of
  projective dimension `< n` has projective dimension `< n + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), proof of Proposition 11.31.
-/

public section

open CategoryTheory Limits DirectSum

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)

/-- The colimit of a sequence of modules of projective dimension `< n` has projective dimension
`< n + 1`. In terms of `HasProjectiveDimensionLE`, a sequential colimit of modules of projective
dimension at most `d` has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLT_succ_of_isColimit [Small.{v} R] {c : Cocone F} (hc : IsColimit c)
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (F.obj i) n) :
    HasProjectiveDimensionLT c.pt (n + 1) := by
  have : AB4OfSize.{0} (ModuleCat.{v} R) := AB4OfSize_shrink.{0, v} _
  have hsum (m : ℕ) (hm : n ≤ m) : HasProjectiveDimensionLT (of R (⨁ i, F.obj i)) m :=
    hasProjectiveDimensionLT_of_isColimit_cofan (coproductCoconeIsColimit fun i ↦ F.obj i) m
      fun i ↦ hasProjectiveDimensionLT_of_ge _ n m hm
  have hS := shortExact_telescopeShortComplex F hc
  rw [← telescopeShortComplex_X₃ F c]
  exact hS.hasProjectiveDimensionLT_X₃ n (telescopeShortComplex_X₁ F c ▸ hsum n le_rfl)
    (telescopeShortComplex_X₂ F c ▸ hsum (n + 1) n.le_succ)

end ModuleCat
