/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.EssentialSubspace

/-!
# Essential subspaces of Hilbert-space representations

Let `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` be a (not necessarily nondegenerate) Hilbert-space representation
of a possibly nonunital C⋆-algebra `A`. Its *essential subspace* `π.essentialSubspace` is the
essential subspace of its range (`NonUnitalStarSubalgebra.essentialSubspace`), equivalently the
closed linear span of the ranges `Set.range (π a)`. Every operator `π a` maps `H` into
`π.essentialSubspace` and annihilates its orthogonal complement `π.essentialSubspaceᗮ`, so
compressing `π` to `π.essentialSubspace` yields a nondegenerate representation
`π.restrictEssentialSubspace : A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace)` whose
extension by zero via `Submodule.extendByZero` recovers `π`.

## Main definitions and results

* `NonUnitalStarAlgHom.essentialSubspace`: the essential subspace of `NonUnitalStarAlgHom.range π`
  (`essentialSubspace_def`), shown equal to the closed span of all ranges `Set.range (π a)` by
  `essentialSubspace_eq_topologicalClosure_span`, with `mem_orthogonal_essentialSubspace_iff`
  characterizing its orthogonal complement as the common kernel `⋂ a, ker (π a)` and
  `isNondegenerate_iff_essentialSubspace_eq_top` relating it to
  `NonUnitalStarAlgHom.IsNondegenerate`.
* `NonUnitalStarAlgHom.ext_of_orthogonal_essentialSubspace`: bounded operators agreeing after
  right multiplication by `π a` and on `π.essentialSubspaceᗮ` are equal on `H`.
* `NonUnitalStarAlgHom.restrictEssentialSubspace`,
  `NonUnitalStarAlgHom.range_restrictEssentialSubspace`, and
  `NonUnitalStarAlgHom.isNondegenerate_restrictEssentialSubspace`: the nondegenerate compression of
  `π` to its essential subspace, with `extendByZero_restrictEssentialSubspace`.

## References

* Jacques Dixmier, *C*-Algebras*, Section 2.2 and Proposition 2.10.4.
* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The *essential subspace* of a Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`: the
essential subspace of its range, i.e., the closed linear span of all vectors `π a ξ`. -/
def essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (NonUnitalStarAlgHom.range π).essentialSubspace

/-- Unfolding formula identifying `π.essentialSubspace` with the essential subspace of the range of
`π`. -/
theorem essentialSubspace_def (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    π.essentialSubspace = (NonUnitalStarAlgHom.range π).essentialSubspace :=
  (rfl)

/-- `π.essentialSubspace` is the closed linear span of all ranges `Set.range (π a)`. -/
theorem essentialSubspace_eq_topologicalClosure_span (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    π.essentialSubspace = (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure := by
  rw [essentialSubspace_def, NonUnitalStarSubalgebra.essentialSubspace_def]
  congr 2
  simpa only [← SetLike.mem_coe, NonUnitalStarAlgHom.coe_range] using
    Set.biUnion_range (f := ⇑π) (g := fun T : H →L[ℂ] H => Set.range T)

/-- The essential subspace of a representation is closed. -/
theorem isClosed_essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (π.essentialSubspace : Set H) :=
  (NonUnitalStarAlgHom.range π).isClosed_essentialSubspace

instance (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : CompleteSpace π.essentialSubspace :=
  (NonUnitalStarAlgHom.range π).instCompleteSpaceEssentialSubspace

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- Every vector in the range of `π a` belongs to `π.essentialSubspace`. -/
theorem apply_mem_essentialSubspace (a : A) (ξ : H) : π a ξ ∈ π.essentialSubspace :=
  (NonUnitalStarAlgHom.range π).apply_mem_essentialSubspace (π.mem_range_self a) ξ

/-- A closed submodule contains `π.essentialSubspace` if and only if it contains every vector
`π a ξ`. -/
theorem essentialSubspace_le_iff {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) :
    π.essentialSubspace ≤ K ↔ ∀ a ξ, π a ξ ∈ K :=
  ((NonUnitalStarAlgHom.range π).essentialSubspace_le_iff hK).trans (by simp)

/-- A vector lies in the orthogonal complement of `π.essentialSubspace` if and only if it is
annihilated by every operator `π a`. -/
theorem mem_orthogonal_essentialSubspace_iff {ξ : H} :
    ξ ∈ π.essentialSubspaceᗮ ↔ ∀ a, π a ξ = 0 :=
  (NonUnitalStarAlgHom.range π).mem_orthogonal_essentialSubspace_iff.trans (by simp)

/-- Every operator `π a` vanishes on `π.essentialSubspaceᗮ`. -/
theorem apply_eq_zero_of_mem_orthogonal_essentialSubspace {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) (a : A) : π a ξ = 0 :=
  π.mem_orthogonal_essentialSubspace_iff.1 hξ a

/-- A representation is nondegenerate if and only if its essential subspace is `⊤`. -/
theorem isNondegenerate_iff_essentialSubspace_eq_top :
    π.IsNondegenerate ↔ π.essentialSubspace = ⊤ := by
  rw [π.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    π.essentialSubspace_eq_topologicalClosure_span]

/-- The orthogonal complement of the essential subspace of a nondegenerate representation is `⊥`. -/
theorem orthogonal_essentialSubspace_eq_bot_of_isNondegenerate (hπ : π.IsNondegenerate) :
    π.essentialSubspaceᗮ = ⊥ := by
  rw [π.isNondegenerate_iff_essentialSubspace_eq_top.1 hπ, Submodule.top_orthogonal_eq_bot]

/-- Continuous linear operators on `H` that agree after right multiplication by every `π a` and
agree on `π.essentialSubspaceᗮ` are equal everywhere on `H`. -/
theorem ext_of_orthogonal_essentialSubspace {S T : H →L[ℂ] H}
    (hmul : ∀ a, S * π a = T * π a) (horth : ∀ ξ ∈ π.essentialSubspaceᗮ, S ξ = T ξ) :
    S = T :=
  (NonUnitalStarAlgHom.range π).ext_of_orthogonal_essentialSubspace
    (by rintro _ ⟨a, rfl⟩; exact hmul a) horth

variable (π) in
/-- Compression of a representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to its closed essential subspace.
Because `π.essentialSubspace` contains all ranges of `π` and its orthogonal complement is killed by
`π`, this compression is a nondegenerate nonunital star-algebra homomorphism. -/
def restrictEssentialSubspace :
    A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace) :=
  let toRestrict (B : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
      B →⋆ₙₐ[ℂ] (B.essentialSubspace →L[ℂ] B.essentialSubspace) :=
    (NonUnitalStarSubalgebraClass.subtype B.restrictEssentialSubspace).comp
      B.restrictEssentialSubspaceEquiv.symm.toNonUnitalStarAlgHom
  (toRestrict (NonUnitalStarAlgHom.range π)).comp π.rangeRestrict

/-- Operator-composition unfolding of `restrictEssentialSubspace`. -/
theorem restrictEssentialSubspace_def (a : A) :
    π.restrictEssentialSubspace a =
      π.essentialSubspace.orthogonalProjectionOnto ∘L π a ∘L π.essentialSubspace.subtypeL :=
  (NonUnitalStarAlgHom.range π).coe_restrictEssentialSubspaceEquiv_symm_apply (π.rangeRestrict a)

/-- Coercing `π.restrictEssentialSubspace a ξ` back to `H` gives `π a ξ`. -/
@[simp]
theorem coe_restrictEssentialSubspace_apply (a : A) (ξ : π.essentialSubspace) :
    (π.restrictEssentialSubspace a ξ : H) = π a ξ := by
  rw [restrictEssentialSubspace_def]
  exact π.essentialSubspace.starProjection_eq_self_iff.2 (π.apply_mem_essentialSubspace a ξ)

/-- Extending `π.restrictEssentialSubspace a` by zero on `π.essentialSubspaceᗮ` recovers `π a`. -/
@[simp]
theorem extendByZero_restrictEssentialSubspace (a : A) :
    π.essentialSubspace.extendByZero (π.restrictEssentialSubspace a) = π a := by
  rw [π.restrictEssentialSubspace_def]
  have h := congrArg Subtype.val
    ((NonUnitalStarAlgHom.range π).restrictEssentialSubspaceEquiv.apply_symm_apply
      (π.rangeRestrict a))
  rw [NonUnitalStarSubalgebra.coe_restrictEssentialSubspaceEquiv_apply,
    NonUnitalStarSubalgebra.coe_restrictEssentialSubspaceEquiv_symm_apply,
    NonUnitalStarAlgHom.coe_codRestrict] at h
  exact h

/-- Composing `π.restrictEssentialSubspace` with `extendByZero` recovers `π`. -/
@[simp]
theorem extendByZero_comp_restrictEssentialSubspace :
    π.essentialSubspace.extendByZero.comp π.restrictEssentialSubspace = π :=
  NonUnitalStarAlgHom.ext π.extendByZero_restrictEssentialSubspace

/-- Compressing `π` to its essential subspace preserves operator norms. -/
@[simp]
theorem norm_restrictEssentialSubspace (a : A) : ‖π.restrictEssentialSubspace a‖ = ‖π a‖ := by
  rw [← π.essentialSubspace.norm_extendByZero, π.extendByZero_restrictEssentialSubspace]

/-- The range of `π.restrictEssentialSubspace` consists of the operators on `π.essentialSubspace`
whose zero extension belongs to `NonUnitalStarAlgHom.range π`. -/
theorem range_restrictEssentialSubspace :
    NonUnitalStarAlgHom.range π.restrictEssentialSubspace =
      (NonUnitalStarAlgHom.range π).comap π.essentialSubspace.extendByZero := by
  ext S
  simp [NonUnitalStarAlgHom.mem_range, ← π.essentialSubspace.extendByZero_injective.eq_iff]

/-- The compression of any representation to its essential subspace is nondegenerate. -/
theorem isNondegenerate_restrictEssentialSubspace :
    π.restrictEssentialSubspace.IsNondegenerate := by
  rw [isNondegenerate_iff_essentialSubspace_eq_top,
    π.restrictEssentialSubspace.essentialSubspace_def, range_restrictEssentialSubspace]
  -- Locally `π.essentialSubspace` is defeq to `(NonUnitalStarAlgHom.range π).essentialSubspace`.
  change ((NonUnitalStarAlgHom.range π).comap
    (NonUnitalStarAlgHom.range π).essentialSubspace.extendByZero).essentialSubspace = ⊤
  rw [← (NonUnitalStarAlgHom.range π).restrictEssentialSubspace_def]
  exact (NonUnitalStarAlgHom.range π).essentialSubspace_restrictEssentialSubspace

end NonUnitalStarAlgHom
