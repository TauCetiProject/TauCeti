/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Algebra.Category.ModuleCat.RatAddCircle
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Short exact sequences of trivial representations

Equipping a module with the trivial action of a monoid `G` is a functor
`Rep.trivialFunctor k G : ModuleCat k ⥤ Rep k G`. It is additive, and it carries a short exact
sequence of `k`-modules to a short exact sequence of trivial representations, because exactness,
injectivity and surjectivity in `Rep k G` are tested on underlying modules.

The case of interest is the sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` with `ℚ/ℤ` realized as the rational
circle `AddCircle (1 : ℚ)`. With trivial action of a group `G`, its connecting maps in group
cohomology send a character `G → ℚ/ℤ` to a class in `H²(G, ℤ)`.

## Main definitions

* `Rep.ratAddCircleShortComplex`: the short complex `ℤ → ℚ → ℚ/ℤ` of trivial integral
  representations of `G`.

## Main results

* `Rep.shortExact_map_trivialFunctor`: the trivial-action functor preserves short exactness.
* `Rep.ratAddCircleShortComplex_shortExact`: `0 → ℤ → ℚ → ℚ/ℤ → 0` is short exact as a sequence of
  trivial representations.
* `Rep.ratAddCircleShortComplex_f_hom_apply`, `Rep.ratAddCircleShortComplex_g_hom_apply`: its maps
  are the inclusion of the integers and reduction modulo `1`.
-/

public noncomputable section

universe w u v

open CategoryTheory

namespace Rep

variable {k : Type u} [Ring k] {G : Type v} [Monoid G]

/-- The trivial-action functor is additive. -/
instance : (trivialFunctor.{w} k G).Additive where

/-- The trivial-action functor carries a short exact sequence of modules to a short exact sequence
of trivial representations. -/
theorem shortExact_map_trivialFunctor {S : ShortComplex (ModuleCat.{w} k)} (hS : S.ShortExact) :
    (S.map (trivialFunctor k G)).ShortExact :=
  -- the forgetful functor to `ModuleCat k` is faithful and sends the mapped complex back to `S`
  -- definitionally, so short exactness is reflected from `hS`
  ShortExact.reflects_shortExact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) hS

variable (G)

-- The objects are stated as `Rep.trivial` and the definition is reducible, so that the connecting
-- maps of this sequence are syntactically maps out of and into `Rep.trivial`, where Mathlib's
-- lemmas about trivial coefficients (`groupCohomology.H1IsoOfIsTrivial`, ...) apply. It is
-- definitionally the image of `ModuleCat.ratAddCircleShortComplex` under `trivialFunctor`.
/-- The short complex `ℤ → ℚ → ℚ/ℤ` of trivial integral representations of `G`, with `ℚ/ℤ` the
rational circle `AddCircle (1 : ℚ)`: the inclusion of the integers followed by reduction
modulo `1`. -/
abbrev ratAddCircleShortComplex : ShortComplex (Rep ℤ G) where
  X₁ := Rep.trivial ℤ G ℤ
  X₂ := Rep.trivial ℤ G ℚ
  X₃ := Rep.trivial ℤ G (AddCircle (1 : ℚ))
  f := (trivialFunctor ℤ G).map ModuleCat.ratAddCircleShortComplex.f
  g := (trivialFunctor ℤ G).map ModuleCat.ratAddCircleShortComplex.g
  zero := (ModuleCat.ratAddCircleShortComplex.map (trivialFunctor ℤ G)).zero

/-- The sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial integral representations is short exact. -/
theorem ratAddCircleShortComplex_shortExact : (ratAddCircleShortComplex G).ShortExact :=
  shortExact_map_trivialFunctor ModuleCat.ratAddCircleShortComplex_shortExact

-- Not `@[simp]`: `simp` already evaluates both maps through `Rep.trivialFunctor_map_hom` and
-- `ModuleCat.hom_ofHom`, so the `simpNF` linter rejects these as simp lemmas.
/-- The first map of `ℤ → ℚ → ℚ/ℤ` is the inclusion of the integers. -/
theorem ratAddCircleShortComplex_f_hom_apply (n : ℤ) :
    (ratAddCircleShortComplex G).f.hom n = (n : ℚ) :=
  rfl

/-- The second map of `ℤ → ℚ → ℚ/ℤ` is reduction modulo `1`. -/
theorem ratAddCircleShortComplex_g_hom_apply (q : ℚ) :
    (ratAddCircleShortComplex G).g.hom q = (q : AddCircle (1 : ℚ)) :=
  rfl

end Rep
