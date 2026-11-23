/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.Separating
public import TauCeti.Algebra.Homology.InternalHomComplex.Unit
public import TauCeti.Algebra.Homology.LinearHomComplex.KInjective

/-!
# The internal Hom complex into a K-injective complex

Let `C` be a closed monoidal abelian category with countable products, and suppose that `C` has a
separating family `P` of objects `G` for which `- ⊗ G` preserves acyclic complexes; for the
category of `𝒪_X`-modules on a scheme `X` the extensions by zero `j_! 𝒪_U` of the structure
sheaves of opens `U` form such a family. Then for a K-injective complex `I`, the internal Hom
complex `𝓗om^•(-, I)` sends quasi-isomorphisms to quasi-isomorphisms
(`TauCeti.quasiIso_internalHomComplexPrecomp`).

Indeed, `Hom(G, 𝓗om^•(K, I))` is the Hom complex `Hom^•(K ⊗ G, I)`
(`CochainComplex.linearCoyonedaInternalHomComplexIso`). A quasi-isomorphism `s : K' ⟶ K` gives a
quasi-isomorphism `s ⊗ G`, as its mapping cone `cone(s) ⊗ G` is acyclic, and precomposition with
`s ⊗ G` is a quasi-isomorphism of Hom complexes into the K-injective complex `I`
(`TauCeti.quasiIso_linearHomComplexPrecomp`). The functors `Hom(G, -)` detect quasi-isomorphisms
(`CochainComplex.quasiIso_of_isSeparating`).

Without such a family the statement can fail: the functors `Hom(G, -)` need not detect
quasi-isomorphisms, and `- ⊗ G` need not preserve them.

## References

* [Stacks Project, Lemma 20.42.1 (08DI)](https://stacks.math.columbia.edu/tag/08DI): for
  `𝒪_X`-modules, `𝓗om^•(-, I)` sends quasi-isomorphisms to quasi-isomorphisms when `I` is
  K-injective.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex CochainComplex.HomComplex Opposite

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [HasCountableProducts C]

/-- Let `P` be a separating family of objects `G` of `C` for which `- ⊗ G` preserves acyclic
complexes. Precomposition with a quasi-isomorphism `s : K' ⟶ K` induces a quasi-isomorphism
`𝓗om^•(K, I) ⟶ 𝓗om^•(K', I)` of internal Hom complexes into a K-injective complex `I`. -/
theorem quasiIso_internalHomComplexPrecomp {P : ObjectProperty C} (hP : P.IsSeparating)
    (hPacyclic : ∀ G, P G → ∀ X : CochainComplex C ℤ, X.Acyclic →
      (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic)
    {K' K : CochainComplex C ℤ} (s : K' ⟶ K) [QuasiIso s] (I : CochainComplex C ℤ)
    [I.IsKInjective] : QuasiIso (internalHomComplexPrecomp s I) := by
  refine quasiIso_of_isSeparating hP _ fun G hG ↦ ?_
  have : QuasiIso (((tensorRight G).mapHomologicalComplex _).map s) := by
    rw [quasiIso_iff_acyclic_mappingCone]
    exact fun n ↦ (hPacyclic G hG _ ((quasiIso_iff_acyclic_mappingCone s).1 inferInstance) n).of_iso
      (mappingCone.mapHomologicalComplexIso s _)
  have := quasiIso_linearHomComplexPrecomp ℤ (((tensorRight G).mapHomologicalComplex _).map s) I
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (linearCoyonedaInternalHomComplexIso K I G)
    (linearCoyonedaInternalHomComplexIso K' I G) ?_)).2 this
  ext n φ
  exact (congrArg _ (linearCoyonedaInternalHomComplexIso_hom_f_apply K I G n φ)).trans
    ((linearHomComplexPrecomp_f_apply _ _ _ _).trans
      ((internalHomComplexHomEquiv_comp_precomp_f s φ).symm.trans
        (linearCoyonedaInternalHomComplexIso_hom_f_apply K' I G n _).symm))

end TauCeti
