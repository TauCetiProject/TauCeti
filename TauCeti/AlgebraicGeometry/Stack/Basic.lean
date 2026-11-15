/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Pseudofunctors on schemes

Prestacks and stacks over the big category of schemes are phrased in terms of `Cat`-valued
pseudofunctors on `LocallyDiscrete Scheme.{u}ᵒᵖ`, in the sense of Mathlib's
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`. This file names their carrier type.

## Main declarations

* `TauCeti.AlgebraicGeometry.SchPseudofunctor`: `Cat`-valued pseudofunctors on schemes.
-/

public section

open CategoryTheory Bicategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- `Cat`-valued pseudofunctors on schemes, contravariant in the scheme. These are the carriers
of prestacks and stacks over the big category of schemes, in the sense of Mathlib's
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`. -/
abbrev SchPseudofunctor := Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}

end TauCeti.AlgebraicGeometry
