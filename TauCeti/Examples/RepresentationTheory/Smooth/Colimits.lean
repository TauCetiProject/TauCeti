/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.QuotientTower
public import TauCeti.RepresentationTheory.Smooth.Colimits

/-!
# Examples for colimits of smooth representations

Colimits in `SmoothRep A G` are computed in `Rep A G`: the inclusion carries a colimit, for
instance a coproduct of any family, to the colimit of the included diagram. A morphism of smooth
representations that is not surjective has a nonzero cokernel, and the kernel of any morphism maps
injectively to the source.

For `G = ℤ_p` (written multiplicatively) the direct sum `⊕_n ℤ[ℤ_p ⧸ p^n ℤ_p]` of the permutation
representations is smooth, while their product is not (see the smooth-representation examples):
sums and products of smooth representations differ.
-/

public section

open CategoryTheory Limits Representation

namespace TauCeti

section General

variable {A G : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Colimits of smooth representations are computed in `Rep A G`. -/
noncomputable example {J : Type} [SmallCategory J] (F : J ⥤ SmoothRep.{0} A G) :
    (SmoothRep.ι A G).obj (colimit F) ≅ colimit (F ⋙ SmoothRep.ι A G) :=
  preservesColimitIso _ _

/-- Every family of smooth representations has a coproduct, computed in `Rep A G`. -/
noncomputable example {κ : Type} (V : κ → SmoothRep.{0} A G) :
    (SmoothRep.ι A G).obj (∐ V) ≅ ∐ fun k ↦ (SmoothRep.ι A G).obj (V k) :=
  PreservesCoproduct.iso _ _

/-- A morphism of smooth representations that is not surjective has a nonzero cokernel. -/
example {V W : SmoothRep.{0} A G} (f : V ⟶ W) (hf : ¬ Function.Surjective f.hom.hom) :
    ¬ IsZero (cokernel f) := fun h ↦
  hf ((SmoothRep.epi_iff_surjective f).1 (Preadditive.epi_of_isZero_cokernel f h))

/-- The kernel of a morphism of smooth representations maps injectively to the source. -/
example {V W : SmoothRep.{0} A G} (f : V ⟶ W) : Function.Injective (kernel.ι f).hom.hom :=
  (SmoothRep.mono_iff_injective _).1 inferInstance

end General

section PadicGroup

variable (p : ℕ) [Fact p.Prime]

/-- The direct sum `⊕_n ℤ[ℤ_p ⧸ p^n ℤ_p]` of the permutation representations is smooth. -/
example :
    IsSmooth (directSum fun n ↦ ofMulAction ℤ (Multiplicative ℤ_[p])
      (Multiplicative ℤ_[p] ⧸ ((FiniteQuotientTower.padicTower p).ker n).toSubgroup)) :=
  inferInstance

end PadicGroup

end TauCeti
