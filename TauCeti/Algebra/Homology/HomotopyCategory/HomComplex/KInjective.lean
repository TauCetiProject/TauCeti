/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Cohomology

/-!
# K-injectivity and acyclic Hom complexes

A complex is K-injective exactly when its Hom complex from every acyclic complex is acyclic.
This identifies Mathlib's null-homotopy definition with the condition on mapping complexes
used to compute derived Hom. The linear version retains the scalar action needed for dg
categories of complexes, including complexes of module sheaves.

No boundedness, injectivity of individual terms, or existence of resolutions is assumed.
The proofs use Mathlib's cohomology-class description of Hom-complex cohomology and its
all-degree coboundary criterion for K-injective targets.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Definition 1.1.
* Joël Riou's `CochainComplex.IsKInjective`, `IsKInjective.eq_δ_of_cocycle`, and
  `HomComplex.homologyAddEquiv` in Mathlib.
-/

public section

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

/-- The scalar-valued Hom complex from an acyclic complex to a K-injective complex is
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
