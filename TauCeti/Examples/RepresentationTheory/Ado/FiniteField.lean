/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Lie.Ado.ArbitraryField
public import Mathlib.Algebra.Field.ZMod

/-!
# Ado–Iwasawa over the field with two elements

This instantiates Ado–Iwasawa for an arbitrary finite-dimensional Lie algebra
in characteristic two. It checks that neither characteristic zero, algebraic closedness nor a
lower bound on the characteristic is required.
-/

public section

namespace TauCeti.Examples.Ado

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

/-- A finite-dimensional Lie algebra over `𝔽₂` admits a faithful finite-dimensional action. -/
example (L : Type u) [LieRing L]
    [LieAlgebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ZMod 2) V)
      (_ : FiniteDimensional (ZMod 2) V)
      (ρ : L →ₗ⁅ZMod 2⁆ Module.End (ZMod 2) V), Function.Injective ρ :=
  adoIwasawa (ZMod 2) L

end TauCeti.Examples.Ado
