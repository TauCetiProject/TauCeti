/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.Algebra.Homology.Ext.Presentation

/-!
# Extension classes and left almost-split maps

The first map of a short exact sequence is left almost split exactly when its extension
class is nonzero and is killed by pushforward along every map out of the first term
that is not a split monomorphism. This converts an extension class constructed by
Auslander–Reiten duality into the factorization property of an actual sequence.

The factorization test uses the kernel of `TauCeti.homBoundary`, computed from Mathlib's
contravariant long exact Ext sequence. No finiteness or linearity assumption is needed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory.Abelian TauCeti

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C}

/-- A short exact sequence starts with a left almost-split map exactly when its class
is nonzero and every pushforward along a map that is not a split monomorphism vanishes. -/
theorem isLeftAlmostSplit_f_iff_extClass (hS : S.ShortExact) :
    IsLeftAlmostSplit S.f ↔ hS.extClass ≠ 0 ∧
      ∀ (N : C) (g : S.X₁ ⟶ N), ¬ IsSplitMono g →
        hS.extClass.comp (Ext.mk₀ g) (add_zero 1) = 0 := by
  have hfactor (N : C) (g : S.X₁ ⟶ N) :
      hS.extClass.comp (Ext.mk₀ g) (add_zero 1) = 0 ↔
        ∃ h : S.X₂ ⟶ N, S.f ≫ h = g := by
    simpa only [LinearMap.mem_ker, homBoundary_apply, LinearMap.mem_range,
      Linear.leftComp_apply] using
      (SetLike.ext_iff.mp (ker_homBoundary ℤ hS N) g)
  constructor
  · intro hf
    refine ⟨?_, fun N g hg ↦ (hfactor N g).mpr (hf.factors N g hg)⟩
    intro hz
    obtain ⟨r, hr⟩ := (hfactor S.X₁ (𝟙 S.X₁)).mp (by simp [hz])
    exact hf.not_isSplitMono (IsSplitMono.mk' ⟨r, hr⟩)
  · rintro ⟨hne, hkill⟩
    refine isLeftAlmostSplit_iff.mpr ⟨?_, fun N g hg ↦ (hfactor N g).mp (hkill N g hg)⟩
    intro hs
    have hz := (hfactor S.X₁ (𝟙 S.X₁)).mpr
      ⟨retraction S.f, IsSplitMono.id S.f⟩
    exact hne (by simpa using hz)

end CategoryTheory.ShortComplex.ShortExact
