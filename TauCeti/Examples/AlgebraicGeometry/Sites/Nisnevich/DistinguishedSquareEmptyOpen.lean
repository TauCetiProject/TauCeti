/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.EmptyOpen
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Examples: morphisms that are not the `p` of a square with empty open part

An elementary distinguished square `Q` over a reduced scheme with empty open part `U` has `p` an
isomorphism (`ElementaryDistinguishedSquare.isIso_p_of_isEmpty`). Hence:

* for a field extension `K → L` of degree two, for instance `ℝ → ℂ`, no such `Q` over `Spec K` has
  `p` isomorphic over `Spec K` to `Spec L ⟶ Spec K` (an étale morphism when the extension is
  separable);
* over `X = Spec ℝ`, no such `Q` has `p` isomorphic over `X` to the morphism
  `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`, which has two points over the single point of `X`: the structure
  rejects it, although it has exactly one point with residue field `ℝ` over that point
  (`existsUnique_realComplexToReal_isIso_residueFieldMap`): the point of `Spec ℂ` has residue
  field `ℂ` (`not_isIso_residueFieldMap_realComplexToReal_inr`). So the pointwise condition "one
  preimage with trivial residue field extension" holds while the uniqueness of the preimage
  fails (`not_existsUnique_realComplexToReal`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample

open TauCeti.AlgebraicGeometry.Scheme

universe u

/-- **An extension of degree other than one is not distinguished with empty `U`.** For an algebra
`K → L` over a nontrivial reduced commutative ring `K` with `finrank K L ≠ 1` (for instance a field
extension of degree two), no elementary distinguished square over `Spec K` with empty open part
has `p` isomorphic over `Spec K` to `Spec L ⟶ Spec K`, since that morphism is not an
isomorphism. -/
theorem isEmpty_iso_SpecMap_of_finrank_ne_one (K L : Type u) [CommRing K] [IsReduced K]
    [Nontrivial K] [CommRing L] [Algebra K L] (h : Module.finrank K L ≠ 1)
    (Q : ElementaryDistinguishedSquare (Spec (.of K))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap K L)) :=
  Q.isEmpty_iso_of_not_isIso _ fun hi ↦
    h (Module.finrank_of_bijective_algebraMap (isIso_SpecMap_iff.1 hi))

/-- The degree-two case. -/
example (K L : Type u) [Field K] [Field L] [Algebra K L] (h : Module.finrank K L = 2)
    (Q : ElementaryDistinguishedSquare (Spec (.of K))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap K L)) :=
  isEmpty_iso_SpecMap_of_finrank_ne_one K L (by omega) Q

/-- The case `ℝ → ℂ`. -/
example (Q : ElementaryDistinguishedSquare (Spec (.of ℝ))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap ℝ ℂ)) :=
  isEmpty_iso_SpecMap_of_finrank_ne_one ℝ ℂ (by rw [Complex.finrank_real_complex]; omega) Q

/-- The morphism `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`: the identity on `Spec ℝ` and `Spec ℂ ⟶ Spec ℝ`. -/
noncomputable abbrev realComplexToReal :
    Spec (.of ℝ) ⨿ Spec (.of ℂ) ⟶ Spec (.of ℝ) :=
  coprod.desc (𝟙 _) (Spec.algebraMap ℝ ℂ)

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` is not an isomorphism: it identifies the points of the two
components. -/
theorem not_isIso_realComplexToReal : ¬ IsIso realComplexToReal := by
  intro _
  obtain ⟨a⟩ : Nonempty (Spec (.of ℝ)) := inferInstance
  obtain ⟨b⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  exact inl_ne_inr _ _ a b (realComplexToReal.isOpenEmbedding.injective (Subsingleton.elim _ _))

/-- **`Spec ℝ ⨿ Spec ℂ` is rejected.** No elementary distinguished square over `Spec ℝ` with empty
open part has `p` isomorphic over `Spec ℝ` to `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`. -/
theorem isEmpty_iso_realComplexToReal (Q : ElementaryDistinguishedSquare (Spec (.of ℝ)))
    [IsEmpty Q.U] : IsEmpty (Over.mk Q.p ≅ Over.mk realComplexToReal) :=
  Q.isEmpty_iso_of_not_isIso _ not_isIso_realComplexToReal

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` restricts to the identity on `Spec ℝ`. -/
theorem realComplexToReal_inl (a : Spec (.of ℝ)) :
    realComplexToReal ((coprod.inl : Spec (.of ℝ) ⟶ _) a) = a := by
  rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
  rfl

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` induces an isomorphism of residue fields at the points of
`Spec ℝ`. -/
theorem isIso_residueFieldMap_realComplexToReal_inl (a : Spec (.of ℝ)) :
    IsIso (realComplexToReal.residueFieldMap ((coprod.inl : Spec (.of ℝ) ⟶ _) a)) := by
  have : IsIso ((coprod.inl ≫ realComplexToReal).residueFieldMap a) := by
    rw [coprod.inl_desc]
    infer_instance
  exact Scheme.Hom.isIso_residueFieldMap_of_comp coprod.inl realComplexToReal a

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` does not induce an isomorphism of residue fields at the point of
`Spec ℂ`. -/
theorem not_isIso_residueFieldMap_realComplexToReal_inr (b : Spec (.of ℂ)) :
    ¬ IsIso (realComplexToReal.residueFieldMap ((coprod.inr : Spec (.of ℂ) ⟶ _) b)) := by
  intro h
  have : IsIso ((coprod.inr ≫ realComplexToReal).residueFieldMap b) := by
    have : IsOpenImmersion (coprod.inr : Spec (.of ℂ) ⟶ Spec (.of ℝ) ⨿ Spec (.of ℂ)) :=
      inferInstance
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' h inferInstance
  rw [coprod.inr_desc, RingHom.isIso_SpecMap_residueFieldMap_iff_surjective] at this
  -- `i` is not real.
  obtain ⟨r, hr⟩ := this Complex.I
  simpa using congrArg Complex.im hr

/-- **The pointwise clause holds for `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`**: over the point of `Spec ℝ`
there is exactly one point with an isomorphism of residue fields, the point of `Spec ℝ`. -/
theorem existsUnique_realComplexToReal_isIso_residueFieldMap (x : Spec (.of ℝ)) :
    ∃! v, realComplexToReal v = x ∧ IsIso (realComplexToReal.residueFieldMap v) := by
  refine ⟨(coprod.inl : Spec (.of ℝ) ⟶ _) x,
    ⟨realComplexToReal_inl x, isIso_residueFieldMap_realComplexToReal_inl x⟩, ?_⟩
  rintro v ⟨-, hv⟩
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ : v ∈ Set.range (coprod.inl : Spec (.of ℝ) ⟶ _) ∪
      Set.range (coprod.inr : Spec (.of ℂ) ⟶ _) := by
    rw [(isCompl_range_inl_inr _ _).sup_eq_top]
    trivial
  · rw [Subsingleton.elim a x]
  · exact (not_isIso_residueFieldMap_realComplexToReal_inr b hv).elim

/-- **The uniqueness clause fails for `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`**: the points of `Spec ℝ` and of
`Spec ℂ` both lie over the point of `Spec ℝ`. -/
theorem not_existsUnique_realComplexToReal (x : Spec (.of ℝ)) :
    ¬ ∃! v, realComplexToReal v = x := by
  rintro ⟨v, -, hv⟩
  obtain ⟨b⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have h₁ := hv ((coprod.inl : Spec (.of ℝ) ⟶ _) x) (realComplexToReal_inl x)
  have h₂ := hv ((coprod.inr : Spec (.of ℂ) ⟶ _) b) (Subsingleton.elim _ _)
  exact inl_ne_inr _ _ x b (h₁.trans h₂.symm)

end TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample
