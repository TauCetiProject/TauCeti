/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
public import TauCeti.RingTheory.Syntomic.StandardSyntomic

/-!
# Spectra of standard syntomic algebras

If `S` is a standard syntomic `R`-algebra of relative dimension `n`, then every fibre
`κ(p) ⊗[R] S` of `Spec S ⟶ Spec R` has Krull dimension at most `n`, so the morphism
`Spec S ⟶ Spec R` has relative dimension at most `n` in the sense of
`TauCeti.AlgebraicGeometry.RelativeDimensionLE`. This connects the algebraic local models of
syntomic morphisms to the scheme-level fibre-dimension API used to define families of curves.

## Main results

* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.relativeDimensionLE_SpecMap`: the
  spectrum of a standard syntomic algebra of relative dimension `n` has relative dimension at
  most `n`.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

namespace Algebra.IsStandardSyntomicOfRelativeDimension

universe u

/-- The morphism `Spec S ⟶ Spec R` of a standard syntomic `R`-algebra `S` of relative dimension
`n` has relative dimension at most `n`. -/
instance relativeDimensionLE_SpecMap (n : ℕ) (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [h : IsStandardSyntomicOfRelativeDimension n R S] :
    RelativeDimensionLE n (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (relativeDimensionLE_SpecMap_iff R S).mpr h.ringKrullDim_fiber_le

end Algebra.IsStandardSyntomicOfRelativeDimension

end TauCeti
