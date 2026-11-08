/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian
public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Split

/-!
# Gluing a pullback of a deflation with a pushout of an inflation

In a commutative diagram
```
A --f--> B --g--> C
|a       |b       |c
A' -f'-> B' -g'-> C'
```
whose left square is a pullback along a deflation `f'` and whose right square is a pushout along
an inflation `g`, both squares are bicartesian, so the outer rectangle is a pullback. Its biproduct
short complex `A ⟶ C ⊞ A' ⟶ C'` is a conflation: it is a kernel by the pullback property, and its
deflation `(c, -(f' ≫ g'))` is the composite of `(𝟙, -f')` with the deflation `(c, g')` of the
pushout square (Bühler, Corollary 3.6). This is the step that makes the mapping cone of a map of
acyclic complexes acyclic.

## Main results

* `TauCeti.ExactStructure.conflation_shortComplex'_of_isPullback_of_isPushout`: gluing a pullback
  along a deflation with a pushout along an inflation.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Corollary 3.6.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- **Gluing a pullback with a pushout** (Bühler, Corollary 3.6). In a commutative diagram
```
A --f--> B --g--> C
|a       |b       |c
A' -f'-> B' -g'-> C'
```
whose left square is a pullback, with `f'` a deflation, and whose right square is a pushout,
with `g` an inflation, the outer rectangle is a pullback and the short complex
`A ⟶ C ⊞ A' ⟶ C'`, with maps `(f ≫ g, a)` and `(c, -(f' ≫ g'))`, is a conflation. -/
theorem conflation_shortComplex'_of_isPullback_of_isPushout {A B C' A' B' C'' : C}
    {f : A ⟶ B} {g : B ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'} {c : C' ⟶ C''} {f' : A' ⟶ B'}
    {g' : B' ⟶ C''} (hl : IsPullback f a b f') (hr : IsPushout g b c g')
    (hf' : E.IsDeflation f') (hg : E.IsInflation g) :
    E.Conflation
      (hl.paste_horiz (E.isPullback_of_isPushout_of_isInflation hg hr)).toCommSq.shortComplex' := by
  have hrc := E.conflation_shortComplex_of_isPushout_of_isInflation hg hr
  have hneg : E.IsDeflation (-f') := by
    have h : (-𝟙 A') ≫ f' = -f' := by simp
    have : IsIso (-𝟙 A') := ⟨⟨-𝟙 A', by simp, by simp⟩⟩
    rw [← h]
    exact E.isDeflation_comp _ _ (E.deflations.of_isIso _) hf'
  have hfac : biprod.map (𝟙 C') (-f') ≫ biprod.desc c g' = biprod.desc c (-(f' ≫ g')) := by
    apply biprod.hom_ext' <;> simp
  have hdef : E.IsDeflation (biprod.desc c (-(f' ≫ g'))) := by
    -- Rewriting cannot key through the unexposed `IsDeflation` abbreviation.
    change E.deflations (biprod.desc c (-(f' ≫ g')))
    rw [← hfac]
    exact E.isDeflation_comp _ _ (E.isDeflation_id_biprod hneg C') (E.isDeflation_g hrc)
  exact E.conflation_of_isLimit_of_isDeflation
    (hl.paste_horiz (E.isPullback_of_isPushout_of_isInflation hg hr)).isLimitKernelFork hdef

end TauCeti.ExactStructure
