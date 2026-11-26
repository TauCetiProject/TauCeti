/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.RingTheory.DominantDimension
public import TauCeti.RingTheory.GlobalDimension

import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.CategoryTheory.Generator.GeneratorCogenerator
import TauCeti.RingTheory.GlobalDimension.AdditiveGenerator
import TauCeti.RingTheory.Morita.Tachikawa.Basic

/-!
# Auslander algebras

An **Auslander algebra** is an Artin algebra `Γ` with `gl.dim Γ ≤ 2 ≤ dom.dim Γ`
(`TauCeti.IsAuslanderAlgebra`). Like `TauCeti.dominantDimension`, the predicate is stated for any
ring, but it is the notion of the literature only for Artin algebras.

The Auslander correspondence says that `A ↦ Module.End A M`, for an additive generator `M` of
`mod A = FGModuleCat A`, induces a bijection from the Morita classes of representation-finite Artin
algebras onto the Morita classes of Auslander algebras. This file proves the forward direction
(`TauCeti.isAuslanderAlgebra_end`): the endomorphism ring `Γ = Module.End A M` of an additive
generator `M` of `mod A`, for an Artin algebra `A`, is an Auslander algebra. Its global dimension is
at most two (`TauCeti.IsAdditiveGenerator.globalDimension_moduleEnd_le_two`), and since an additive
generator is a generator-cogenerator (`TauCeti.IsAdditiveGenerator.isGeneratorCogenerator`), its
dominant dimension is at least two by the forward direction of the Morita-Tachikawa correspondence
(`TauCeti.two_le_dominantDimension_end`).

For nonsemisimple `A` both dimensions of `Γ` are exactly two. For semisimple `A` the ring `Γ` is
semisimple, of global dimension `0` (or `⊥` when `M = 0`) and of dominant dimension `⊤`.

## Main definitions

* `TauCeti.IsAuslanderAlgebra Γ`: `Γ` has global dimension at most two and dominant dimension at
  least two.

## Main results

* `TauCeti.isAuslanderAlgebra_end`: **the Auslander correspondence, forward direction**: the
  endomorphism ring of an additive generator of `mod A`, for an Artin algebra `A`, is an Auslander
  algebra.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, Proposition VI.5.4(a).
* M. Auslander, *Representation dimension of Artin algebras*, Queen Mary College Mathematics Notes,
  London (1971).
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- An **Auslander algebra**: a ring `Γ` with `gl.dim Γ ≤ 2 ≤ dom.dim Γ`. Like
`TauCeti.dominantDimension`, it is stated for any ring, but it is the notion of the literature only
for Artin algebras. -/
def IsAuslanderAlgebra (Γ : Type u) [Ring Γ] : Prop :=
  TauCeti.globalDimension.{u} Γ ≤ 2 ∧ 2 ≤ dominantDimension Γ

/-- The definition of an Auslander algebra: global dimension at most two and dominant dimension at
least two. -/
theorem isAuslanderAlgebra_iff {Γ : Type u} [Ring Γ] :
    IsAuslanderAlgebra Γ ↔ TauCeti.globalDimension.{u} Γ ≤ 2 ∧ 2 ≤ dominantDimension Γ :=
  Iff.rfl

/-- **The Auslander correspondence, forward direction.** For an additive generator `M` of `mod A`,
for an Artin algebra `A`, the endomorphism ring `Module.End A M` is an Auslander algebra. The base
ring `R` may live in any universe, and the modules in any universe in which `A` is small. -/
theorem isAuslanderAlgebra_end (R : Type u) [CommRing R] [IsArtinianRing R] {A : Type v} [Ring A]
    [Algebra R A] [Module.Finite R A] [Small.{w} A] (M : FGModuleCat.{w} A)
    (hM : IsAdditiveGenerator M) : IsAuslanderAlgebra (Module.End A M.obj) :=
  isAuslanderAlgebra_iff.2 ⟨hM.globalDimension_moduleEnd_le_two R,
    two_le_dominantDimension_end R M hM.isGeneratorCogenerator⟩

end TauCeti
