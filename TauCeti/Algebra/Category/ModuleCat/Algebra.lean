/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: the finiteness transfer for linear maps is used only inside the proof.
import TauCeti.Algebra.Module.LinearMap.Finite

/-!
# Finite-dimensional morphism spaces of modules over a finite-dimensional algebra

For an algebra `A` over a field `k`, Mathlib's `ModuleCat.linearOverField` makes `ModuleCat A`
a `k`-linear category. When `A` is finite-dimensional over `k`, the morphisms between two
finitely generated `A`-modules form a finite-dimensional `k`-vector space
(the instance `ModuleCat.finiteDimensional_hom_of_finite`). This is the Hom-finiteness that
dimension counts in the module category of a finite-dimensional algebra rest on.

The morphism space is identified with the `A`-linear maps by `ModuleCat.homLinearEquiv`, and
those embed in maps into a power of the target by `Module.Finite.linearMap_of_isNoetherian`.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace ModuleCat

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Morphisms between finitely generated modules over a finite-dimensional algebra form a
finite-dimensional space over the ground field. -/
instance finiteDimensional_hom_of_finite (M N : ModuleCat.{w} A) [Module.Finite A M]
    [Module.Finite A N] : FiniteDimensional k (M ⟶ N) := by
  have : Module.Finite k N := Module.Finite.trans A N
  have : Module.Finite k (M →ₗ[A] N) := Module.Finite.linearMap_of_isNoetherian
  exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm

end ModuleCat
