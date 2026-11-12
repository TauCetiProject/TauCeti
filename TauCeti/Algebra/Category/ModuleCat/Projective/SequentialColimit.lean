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
public import TauCeti.Algebra.Category.ModuleCat.DirectedUnion
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.RingTheory.Flat.ProjectiveDimension

/-!
# The projective dimension of a sequential colimit of modules

Let `F₀ → F₁ → F₂ → ⋯` be a sequence of `R`-modules, a functor `F : ℕ ⥤ ModuleCat R`, with
colimit `M`. Dimension shifting along the telescope short exact sequence
`0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → M → 0` (`ModuleCat.shortExact_telescopeShortComplex`) shows that if every
`Fₙ` has projective dimension at most `d`, then `M` has projective dimension at most `d + 1`: the
direct sum `⨁ₙ Fₙ` has projective dimension at most `d`, as coproducts of modules are exact.

The bound is sharp: `ℚ` is the colimit of `ℤ →2 ℤ →3 ℤ →4 ⋯` (multiplication by `n + 2` at the
`n`-th step) of free `ℤ`-modules but is not projective.

This is how a bound on the projective dimension of modules over the stages of a sequential
colimit of rings leads to a bound over the colimit. Let `R` be the union of an increasing
sequence of subrings `S₀ ⊆ S₁ ⊆ ⋯` and flat over each of them. Every `R`-module `M` is the colimit
of the base changes `R ⊗[Sₙ] M` (`TauCeti.ModuleCat.isColimitTensorSubringCocone`), and flat
base change does not increase projective dimension. So if `M` has projective dimension at most
`d` over every `Sₙ`, then it has projective dimension at most `d + 1` over `R`.
The perfection of a regular ring of characteristic `p` is the main example.

## Main declarations

* `ModuleCat.hasProjectiveDimensionLT_succ_of_isColimit`: the colimit of a sequence of modules of
  projective dimension `< n` has projective dimension `< n + 1`.
* `ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top`: if `R` is the union of an increasing
  sequence of subrings over each of which it is flat, and an `R`-module has projective dimension
  `< n` over each of these subrings, then it has projective dimension `< n + 1` over `R`.

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

namespace ModuleCat

open TauCeti.ModuleCat in
/-- If `R` is the union of an increasing sequence of subrings `S k` over each of which it is flat,
and an `R`-module `M` has projective dimension `< n` over every `S k`, then it has projective
dimension `< n + 1` over `R`. In terms of `HasProjectiveDimensionLE`, global dimension at most
`d` for all the `S k` gives global dimension at most `d + 1` for `R`. -/
theorem hasProjectiveDimensionLT_succ_of_iSup_eq_top {R : Type u} [CommRing R]
    {S : ℕ → Subring R} (hS : Monotone S) (htop : ⨆ k, S k = ⊤) [∀ k, Module.Flat (S k) R]
    {n : ℕ} (M : ModuleCat.{u} R) (h : ∀ k, HasProjectiveDimensionLT (of (S k) M) n) :
    HasProjectiveDimensionLT M (n + 1) := by
  have htop' (r : R) : ∃ k, r ∈ S k :=
    (Subring.mem_iSup_of_directed hS.directed_le).1 (htop ▸ Subring.mem_top r)
  have := hasProjectiveDimensionLT_succ_of_isColimit (tensorSubringFunctor M hS)
    (isColimitTensorSubringCocone htop') n fun k ↦
      tensorSubringFunctor_obj M hS k ▸ hasProjectiveDimensionLT_tensorProduct R M (h k)
  rwa [tensorSubringCocone_pt] at this

end ModuleCat
