/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms on open subschemes

Smoothness of relative dimension `n` restricts to every open subscheme of the source. In
particular, an open subscheme of a scheme smooth of relative dimension `n` over a base is
smooth of the same relative dimension over that base, without a connectedness assumption.

## Main declarations

* `AlgebraicGeometry.Scheme.Opens.smoothOfRelativeDimension_ι_comp`: restricting the source of
  a smooth morphism to an open subscheme preserves its relative dimension.
* `AlgebraicGeometry.Scheme.Opens.smoothOfRelativeDimension_over`: an open subscheme of a
  scheme smooth of relative dimension `n` over a base is smooth of that relative dimension.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Opens

universe u

/-- Restriction to an arbitrary open subscheme preserves smoothness of relative dimension `n`. -/
instance smoothOfRelativeDimension_ι_comp {X S : Scheme.{u}} (U : X.Opens) (n : ℕ)
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (U.ι ≫ f) :=
  -- An open immersion has relative dimension zero, and dimensions add under composition.
  Nat.zero_add n ▸ inferInstanceAs (SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))

/-- An arbitrary open subscheme is smooth of the same relative dimension over the base. -/
instance smoothOfRelativeDimension_over {X S : Scheme.{u}} [X.Over S] (U : X.Opens) (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ S)] : SmoothOfRelativeDimension n (U.toScheme ↘ S) := by
  rw [← U.ι_comp_over]
  infer_instance

end AlgebraicGeometry.Scheme.Opens
