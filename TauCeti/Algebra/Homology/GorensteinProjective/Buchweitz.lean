/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Singularity.Syzygy
public import TauCeti.Algebra.Homology.GorensteinProjective.IwanagaGorenstein
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity

/-!
# Buchweitz's theorem: the stable category of Gorenstein-projective modules is `D_sg`

Let `A` be an Iwanaga–Gorenstein ring, with `injdim A ≤ d` as a left module. Chen's functor from
the stable category of finitely generated Gorenstein-projective modules to the singularity
category `D_sg(A) = Dᵇ(mod-A) / Kᵇ(proj-A)` is fully faithful
(`CategoryTheory.GorensteinProjective.fullyFaithfulToSingularityCategory`). It is also
essentially surjective, hence an equivalence of categories:

1. Every object of `D_sg(A)` is a `d`-th syzygy `M` placed in some degree
   (`TauCeti.SingularityCategory.exists_iso_Q_obj_singleFunctor_obj_isSyzygy`).
2. `M` is Gorenstein-projective (`FGModuleCat.isGorensteinProjective_of_isSyzygy`): among all
   modules it is still a `d`-th syzygy, so `Ext^{>0}(M, A) = 0`, and
   `TauCeti.isGorensteinProjective_iff_ext_eq_zero` applies.
3. A Gorenstein-projective module placed in any degree lies in the essential image of Chen's
   functor (`CategoryTheory.GorensteinProjective.mem_essImage_toSingularityCategory`).

## Main results

* `TauCeti.IsIwanagaGorenstein.essSurj_toSingularityCategory`: **Buchweitz's theorem**, density:
  Chen's functor is essentially surjective, and hence an equivalence of categories
  (`TauCeti.IsIwanagaGorenstein.isEquivalence_toSingularityCategory`).

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
    (GorensteinProjective.toSingularityCategory (FGModuleCat.{u} A)).EssSurj where
  mem_essImage Y := by
    obtain ⟨d, _⟩ := IsIwanagaGorenstein.exists_hasInjectiveDimensionLE (A := A)
    have := Localization.essSurj (SingularityCategory.Q (FGModuleCat.{u} A))
      (DerivedCategory.Bounded.perfect (FGModuleCat.{u} A)).trW
    obtain ⟨M, n, hM, ⟨e⟩⟩ := SingularityCategory.exists_iso_Q_obj_singleFunctor_obj_isSyzygy
      ((SingularityCategory.Q (FGModuleCat.{u} A)).objPreimage Y) d
    exact (GorensteinProjective.mem_essImage_toSingularityCategory
      (FGModuleCat.isGorensteinProjective_of_isSyzygy hM) n).ofIso
        (e.symm ≪≫ (SingularityCategory.Q (FGModuleCat.{u} A)).objObjPreimageIso Y)

/-- **Buchweitz's theorem**: over an Iwanaga–Gorenstein ring, Chen's functor from the stable
category of finitely generated Gorenstein-projective modules to the singularity category is an
equivalence of categories. -/
instance IsIwanagaGorenstein.isEquivalence_toSingularityCategory :
    (GorensteinProjective.toSingularityCategory (FGModuleCat.{u} A)).IsEquivalence where

end TauCeti
