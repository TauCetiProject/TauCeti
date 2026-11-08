/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Singularity.Syzygy
public import TauCeti.Algebra.Homology.GorensteinProjective.IwanagaGorenstein
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat

/-!
# Buchweitz's theorem: the stable category of Gorenstein-projective modules is `D_sg`

Let `A` be an Iwanaga–Gorenstein ring, with `injdim A ≤ d` as a left module. Chen's functor from
the stable category of finitely generated Gorenstein-projective modules to the singularity
category `D_sg(A) = Dᵇ(mod-A) / Kᵇ(proj-A)` is fully faithful
(`CategoryTheory.GorensteinProjective.fullyFaithfulToSingularityCategory`). It is also
essentially surjective, hence an equivalence of categories:

1. Every object of `D_sg(A)` is a `d`-th syzygy `M` placed in some degree
   (`TauCeti.SingularityCategory.exists_iso_Q_obj_singleFunctor_obj_isSyzygy`).
2. Viewed among all modules, `M` is still a `d`-th syzygy, so `Ext^{>0}(M, A) = 0`, and `M` is
   Gorenstein-projective by `TauCeti.isGorensteinProjective_iff_ext_eq_zero`.
3. A Gorenstein-projective module placed in any degree lies in the essential image of Chen's
   functor (`CategoryTheory.GorensteinProjective.essImage_toSingularityCategory`).

## Main results

* `FGModuleCat.isGorensteinProjective_of_isSyzygy`: over an Iwanaga–Gorenstein ring with
  `injdim A ≤ d`, a `d`-th syzygy of finitely generated modules is Gorenstein-projective.
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

/-- **Syzygies over an Iwanaga–Gorenstein ring are Gorenstein-projective**: if `A` has injective
dimension at most `d` as a left module, every `d`-th syzygy of finitely generated modules is a
Gorenstein-projective object of `FGModuleCat A`. Among all modules it is still a `d`-th syzygy, so
it has no higher extensions by `A`. -/
theorem _root_.FGModuleCat.isGorensteinProjective_of_isSyzygy {d : ℕ}
    [HasInjectiveDimensionLE (ModuleCat.of A A) d] {M : FGModuleCat.{u} A}
    (hM : (isProjective (FGModuleCat.{u} A)).IsSyzygy d M) :
    isGorensteinProjective (FGModuleCat.{u} A) M := by
  let F := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  have hM' : (isProjective (ModuleCat.{u} A)).IsSyzygy d (F.obj M) :=
    hM.map F (fun S hS ↦ hS.map_of_exact F) fun Q (_ : Projective Q) ↦
      -- Instance search does not see the carrier of `Q` through `forget₂`.
      @ModuleCat.projective_of_categoryTheory_projective A _ (F.obj Q)
        (FGModuleCat.moduleProjective_of_projective Q)
  have : Module.Finite A (F.obj M) := inferInstanceAs (Module.Finite A M)
  exact (FGModuleCat.isGorensteinProjective_iff M).2
    ((isGorensteinProjective_iff_ext_eq_zero (F.obj M)).2 ⟨inferInstance, fun n e ↦
      hM'.ext_eq_zero_of_hasInjectiveDimensionLE (fun _ h ↦ h) (ModuleCat.of A A) n e⟩)

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
    exact (GorensteinProjective.essImage_toSingularityCategory
      (FGModuleCat.isGorensteinProjective_of_isSyzygy hM) n).ofIso
        (e.symm ≪≫ (SingularityCategory.Q (FGModuleCat.{u} A)).objObjPreimageIso Y)

/-- **Buchweitz's theorem**: over an Iwanaga–Gorenstein ring, Chen's functor from the stable
category of finitely generated Gorenstein-projective modules to the singularity category is an
equivalence of categories. -/
instance IsIwanagaGorenstein.isEquivalence_toSingularityCategory :
    (GorensteinProjective.toSingularityCategory (FGModuleCat.{u} A)).IsEquivalence where

end TauCeti
