/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Cogenerator
public import TauCeti.RingTheory.DominantDimension

/-!
# The endomorphism ring of a generator-cogenerator has dominant dimension at least two

Let `A` be an Artin algebra and `M` a generator-cogenerator of `mod A`, with endomorphism ring
`Γ = Module.End A M` acting on `M` by evaluation. This file proves the forward direction of the
Morita-Tachikawa correspondence: `Γ` has dominant dimension at least two
(`TauCeti.two_le_dominantDimension_end`).

The proof follows Müller. As a generator, `M` is a finitely generated projective `Γ`-module
(`TauCeti.Module.IsGenerator.finite_end` and `TauCeti.Module.IsGenerator.projective_end`). As a
cogenerator, `M` is an injective `Γ`-module (`FGModuleCat.injective_end_of_isCoseparator`). A
presentation `Aᵐ → Aⁿ → M → 0` and the left exact functor `Hom_A(-, M)` then give an exact sequence
`0 → Γ → Mⁿ → Mᵐ` of `Γ`-modules whose last two terms are finitely generated, projective and
injective. This last step holds over any ring, for a finitely presented generator that is
injective over its endomorphism ring
(`TauCeti.two_le_dominantDimension_end_of_isGenerator`).

## Main results

* `TauCeti.two_le_dominantDimension_end`: **the Morita-Tachikawa correspondence, forward
  direction**: the endomorphism ring of a generator-cogenerator of `mod A`, for an Artin algebra
  `A`, has dominant dimension at least two.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Proposition VI.5.4(a).
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- **The Morita-Tachikawa correspondence, forward direction.** The endomorphism ring of a
generator-cogenerator `M` of `mod A`, for an Artin algebra `A`, has dominant dimension at least two.
The base ring `R` may live in any universe, and the modules in any universe in which `A` is
small. -/
theorem two_le_dominantDimension_end (R : Type u) [CommRing R] [IsArtinianRing R]
    {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A] [Small.{w} A]
    (M : FGModuleCat.{w} A) (hM : IsGeneratorCogenerator M) :
    2 ≤ dominantDimension (Module.End A M.obj) := by
  obtain ⟨hs, hc⟩ := isGeneratorCogenerator_iff.1 hM
  have := IsArtinianRing.of_finite R A
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hs
  have := Module.finitePresentation_of_finite A M.obj
  have := FGModuleCat.injective_end_of_isCoseparator R hc
  exact two_le_dominantDimension_end_of_isGenerator M.obj

end TauCeti
