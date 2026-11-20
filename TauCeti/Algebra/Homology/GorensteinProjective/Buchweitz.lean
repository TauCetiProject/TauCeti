/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.IwanagaGorenstein
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity

/-!
# Buchweitz's theorem: the stable category of Gorenstein-projective modules is `D_sg`

Let `A` be an Iwanaga–Gorenstein ring, with `injdim A ≤ d` as a left module. Chen's functor from
the stable category of finitely generated Gorenstein-projective modules to the singularity
category `D_sg(A) = Dᵇ(mod-A) / Kᵇ(proj-A)` is fully faithful
(`CategoryTheory.GorensteinProjective.fullyFaithfulToSingularityCategory`). It is also
essentially surjective, hence an equivalence of categories:

1. Chen's functor is essentially surjective as soon as every `d`-th syzygy is Gorenstein-projective
   (`CategoryTheory.GorensteinProjective.essSurj_toSingularityCategory_of_isSyzygy`).
2. Every `d`-th syzygy `M` in `FGModuleCat A` is Gorenstein-projective
   (`FGModuleCat.isGorensteinProjective_of_isSyzygy`): among all modules it is still a `d`-th
   syzygy, so `Ext^{>0}(M, A) = 0`, and `TauCeti.isGorensteinProjective_iff_ext_eq_zero` applies.

## Main results

* `TauCeti.IsIwanagaGorenstein.essSurj_toSingularityCategory`: **Buchweitz's theorem**, density:
  Chen's functor is essentially surjective, and hence an equivalence of categories
  (`TauCeti.IsIwanagaGorenstein.isEquivalence_toSingularityCategory`).
  Chen's functor is a triangle functor for any abelian category
  (`CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated`), so this is an
  equivalence of triangulated categories.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212, Theorem 3.8.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w u

namespace TauCeti

variable {A : Type u} [Ring A] [IsIwanagaGorenstein A]

variable [HasDerivedCategory.{w} (FGModuleCat.{u} A)]

/-- **Buchweitz's theorem**, density: over an Iwanaga–Gorenstein ring, every object of the
singularity category `D_sg(A)` is a finitely generated Gorenstein-projective module placed in
degree zero. -/
instance IsIwanagaGorenstein.essSurj_toSingularityCategory :
    (GorensteinProjective.toSingularityCategory (FGModuleCat.{u} A)).EssSurj := by
  obtain ⟨d, _⟩ := IsIwanagaGorenstein.exists_hasInjectiveDimensionLE (A := A)
  exact GorensteinProjective.essSurj_toSingularityCategory_of_isSyzygy d
    fun _ hM ↦ FGModuleCat.isGorensteinProjective_of_isSyzygy hM

/-- **Buchweitz's theorem**: over an Iwanaga–Gorenstein ring, Chen's functor from the stable
category of finitely generated Gorenstein-projective modules to the singularity category is an
equivalence of categories. -/
instance IsIwanagaGorenstein.isEquivalence_toSingularityCategory :
    (GorensteinProjective.toSingularityCategory (FGModuleCat.{u} A)).IsEquivalence where

end TauCeti
