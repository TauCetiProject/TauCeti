/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Cohomology
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import TauCeti.Algebra.Homology.Adjunction
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.Algebra.Homology.Homotopy

/-!
# K-injective cochain complexes: closure properties and Hom-complex criteria

A cochain complex `L` in an abelian category is K-injective (Mathlib's
`CochainComplex.IsKInjective`) if every morphism from an acyclic complex to `L` is null-homotopic.
This file proves that contractible complexes are K-injective
(`CochainComplex.isKInjective_of_homotopy_id_zero`), along with closure and characterization
properties of this class:

* a product of K-injective complexes is K-injective (`CochainComplex.isKInjective_of_isLimit_fan`);
* in a degreewise split short exact sequence `0 → X₁ → X₂ → X₃ → 0` of cochain complexes with
  `X₂` and `X₃` K-injective, the complex `X₁` is K-injective
  (`CochainComplex.isKInjective_X₁_of_degreewiseSplit`);
* a complex is both K-injective and acyclic if and only if it is contractible
  (`CochainComplex.isKInjective_and_acyclic_iff_nonempty_homotopy_id_zero`);
* the right adjoint of a homology-preserving functor between abelian categories sends K-injective
  complexes to K-injective complexes
  (`CategoryTheory.Adjunction.isKInjective_mapHomologicalComplex_obj`).

The degreewise-split property holds because K-injective complexes form the right orthogonal of the
acyclic complexes in the homotopy category, a triangulated subcategory, and a degreewise split
short exact sequence gives a distinguished triangle there. Together with closure under products it
shows that the limit of a tower of K-injective complexes with degreewise split surjective
transitions is K-injective, which is the step of Spaltenstein's construction of K-injective
replacements of unbounded complexes.

K-injectivity is also equivalent to acyclicity of the Hom complex from every acyclic complex,
for both the additive and linear Hom complexes. This identifies Mathlib's null-homotopy
definition with the condition on mapping complexes used to compute derived Hom. These criteria
assume no boundedness, injectivity of individual terms, or existence of resolutions. Their proofs
use Mathlib's cohomology-class description of Hom-complex cohomology and its all-degree
coboundary criterion for K-injective targets.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154,
  Definition 1.1.
* J. Lurie, *Higher Algebra*, Proposition 1.3.5.6.
* Stacks Project, *Derived Categories*, the section on K-injective complexes.
* Joël Riou's `CochainComplex.IsKInjective`, `IsKInjective.eq_δ_of_cocycle`, and
  `HomComplex.homologyAddEquiv` in Mathlib.
-/

public section

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- A contractible cochain complex, one whose identity is null-homotopic, is K-injective. -/
theorem isKInjective_of_homotopy_id_zero {L : CochainComplex C ℤ} (h : Homotopy (𝟙 L) 0) :
    L.IsKInjective where
  nonempty_homotopy_zero f _ :=
    ⟨(Homotopy.ofEq (Category.comp_id f).symm).trans ((h.compLeft f).trans (.ofEq (by simp)))⟩

/-- **Products of K-injective complexes are K-injective.** If `c` is a product of a family of
K-injective cochain complexes, then its cone point is K-injective. -/
theorem isKInjective_of_isLimit_fan {J : Type*}
    {X : J → CochainComplex C ℤ} {c : Fan X} (hc : IsLimit c) [∀ j, (X j).IsKInjective] :
    c.pt.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    -- Each component `f ≫ c.proj j` is null-homotopic, and the homotopies are assembled degreewise
    -- using that every term of `c.pt` is the product of the corresponding terms of the `X j`.
    let h (j : J) : Homotopy (f ≫ c.proj j) 0 := IsKInjective.homotopyZero _ hK
    -- the evaluation functors preserve the limit, as each `eval q ⋙ coyoneda.obj (op Y)` is
    -- corepresentable and the coyoneda functors preserve limits
    let hc' (q : ℤ) : IsLimit ((HomologicalComplex.eval C _ q).mapCone c) :=
      coyonedaJointlyReflectsLimits _ _ fun ⟨Y⟩ ↦
        isLimitOfPreserves (HomologicalComplex.eval C _ q ⋙ coyoneda.obj ⟨Y⟩) hc
    let hom (p q : ℤ) : K.X p ⟶ c.pt.X q :=
      (hc' q).lift ⟨K.X p, Discrete.natTrans fun j ↦ (h j.as).hom p q⟩
    have hom_proj (p q : ℤ) (j : J) : hom p q ≫ (c.π.app ⟨j⟩).f q = (h j).hom p q :=
      (hc' q).fac _ ⟨j⟩
    refine ⟨{ hom := hom, zero := fun p q hpq ↦ ?_, comm := fun p ↦ ?_ }⟩
    · refine (hc' q).hom_ext fun ⟨j⟩ ↦ ?_
      simpa [hom_proj] using (h j).zero p q hpq
    · refine (hc' p).hom_ext fun ⟨j⟩ ↦ ?_
      have hj := (h j).comm p
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, add_zero] at hj
      have hfun : (fun a b ↦ hom a b ≫ (c.π.app ⟨j⟩).f b) = (h j).hom := by
        funext a b
        exact hom_proj a b j
      simp only [Functor.mapCone_π_app, HomologicalComplex.eval_map, HomologicalComplex.zero_f,
        add_zero, Preadditive.add_comp]
      rw [← dNext_comp_right, ← prevD_comp_right, hfun]
      exact hj

/-- **K-injectivity of the first term of a degreewise split sequence.** In a short complex
`X₁ → X₂ → X₃` of cochain complexes that is split short exact in every degree, if `X₂` and `X₃`
are K-injective, then so is `X₁`. -/
theorem isKInjective_X₁_of_degreewiseSplit (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting)
    [S.X₂.IsKInjective] [S.X₃.IsKInjective] : S.X₁.IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal]
  exact ObjectProperty.ext_of_isTriangulatedClosed₁ _ _
    (trianglehOfDegreewiseSplit_distinguished S σ) (IsKInjective.rightOrthogonal S.X₂)
    (IsKInjective.rightOrthogonal S.X₃)

/-- A cochain complex is both K-injective and acyclic if and only if its identity map is
null-homotopic. -/
theorem isKInjective_and_acyclic_iff_nonempty_homotopy_id_zero (L : CochainComplex C ℤ) :
    L.IsKInjective ∧ L.Acyclic ↔ Nonempty (Homotopy (𝟙 L) 0) :=
  ⟨fun ⟨_, hL⟩ ↦ IsKInjective.nonempty_homotopy_zero (𝟙 L) hL,
    fun ⟨h⟩ ↦ ⟨isKInjective_of_homotopy_id_zero h, h.acyclic⟩⟩

end CochainComplex

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- **Right adjoints of homology-preserving functors preserve K-injectivity.** If `adj : F ⊣ G` is
an adjunction between abelian categories whose left adjoint `F` preserves homology (for instance, if
`F` preserves finite limits), then applying `G` degreewise sends K-injective cochain complexes to
K-injective cochain complexes. -/
theorem isKInjective_mapHomologicalComplex_obj (adj : F ⊣ G) [F.PreservesHomology]
    (L : CochainComplex D ℤ) [L.IsKInjective] :
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L) where
  nonempty_homotopy_zero {K} f hK := by
    have := adj.rightAdjoint_preservesLimits.{0, 0}
    have : G.Additive := G.additive_of_preserves_binary_products
    have : F.Additive := adj.left_adjoint_additive
    let adj' := adj.mapHomologicalComplex (.up ℤ)
    have hFK : ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic :=
      F.acyclic_mapHomologicalComplex_obj (.up ℤ) hK
    let h' := CochainComplex.IsKInjective.homotopyZero ((adj'.homEquiv K L).symm f) hFK
    refine ⟨(Homotopy.ofEq ?_).trans
      (((G.mapHomotopy h').compLeft (adj'.unit.app K)).trans (Homotopy.ofEq ?_))⟩
    · exact ((adj'.homEquiv K L).right_inv f).symm.trans (Adjunction.homEquiv_unit adj' K L _)
    · rw [(G.mapHomologicalComplex (.up ℤ)).map_zero, Limits.comp_zero]

end CategoryTheory.Adjunction

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ}

/-- The Hom complex from an acyclic complex to a K-injective complex is acyclic in every
integer degree. -/
theorem acyclic_homComplex_of_isKInjective [L.IsKInjective] (hK : K.Acyclic) :
    (HomComplex K L).Acyclic := by
  intro n
  rw [exactAt_homComplex_iff_subsingleton_cohomologyClass]
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff z (n - 1) (by simp)]
  exact IsKInjective.eq_δ_of_cocycle z hK (n - 1) (by simp)

/-- K-injectivity can be tested by acyclicity of Hom complexes, not only by homotopy classes
of degree-zero maps. -/
theorem isKInjective_iff_acyclic_homComplex :
    L.IsKInjective ↔ ∀ K : CochainComplex C ℤ, K.Acyclic → (HomComplex K L).Acyclic := by
  refine ⟨fun _ K hK ↦ acyclic_homComplex_of_isKInjective hK,
    fun hL ↦ ⟨fun {K} f hK ↦ ?_⟩⟩
  have : Subsingleton (CohomologyClass K L 0) :=
    (exactAt_homComplex_iff_subsingleton_cohomologyClass 0).mp (hL K hK 0)
  have hz : CohomologyClass.mk (Cocycle.ofHom f) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff (Cocycle.ofHom f) (-1) (by simp)] at hz
  obtain ⟨α, hα⟩ := hz
  exact ⟨(Cochain.equivHomotopy f 0).symm ⟨α, by simpa using hα.symm⟩⟩

variable (R : Type w) [Ring R] [Linear R C]

/-- The `R`-linear Hom complex from an acyclic complex to a K-injective complex is
acyclic, without any commutativity assumption on the scalar ring. -/
theorem acyclic_linearHomComplex_of_isKInjective [L.IsKInjective] (hK : K.Acyclic) :
    (CochainComplex.linearHomComplex R K L).Acyclic :=
  (acyclic_linearHomComplex_iff R).mpr (acyclic_homComplex_of_isKInjective hK)

/-- The linear Hom-complex criterion for K-injectivity agrees with Mathlib's
null-homotopy definition. -/
theorem isKInjective_iff_acyclic_linearHomComplex :
    L.IsKInjective ↔ ∀ K : CochainComplex C ℤ, K.Acyclic →
      (CochainComplex.linearHomComplex R K L).Acyclic := by
  simp only [acyclic_linearHomComplex_iff, isKInjective_iff_acyclic_homComplex]

end TauCeti
