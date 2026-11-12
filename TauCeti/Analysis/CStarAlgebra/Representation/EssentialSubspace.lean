/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.Projection.ExtendByZero

/-!
# Essential subspaces of Hilbert-space representations

Let `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` be a (not necessarily nondegenerate) Hilbert-space representation
of a possibly nonunital C⋆-algebra `A`. Its *essential subspace* `π.essentialSubspace` is the
closed linear span of the ranges `Set.range (π a)`. Every operator `π a` maps `H` into
`π.essentialSubspace` and annihilates its orthogonal complement `π.essentialSubspaceᗮ`, so
compressing `π` to `π.essentialSubspace` yields a nondegenerate representation
`π.restrictEssentialSubspace : A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace)` whose
extension by zero via `Submodule.extendByZero` recovers `π`.

## Main definitions and results

* `NonUnitalStarAlgHom.essentialSubspace`: the closed span of all ranges `Set.range (π a)`, with
  `mem_orthogonal_essentialSubspace_iff` characterizing its orthogonal complement as the common
  kernel `⋂ a, ker (π a)` and `isNondegenerate_iff_essentialSubspace_eq_top` relating it to
  `NonUnitalStarAlgHom.IsNondegenerate`.
* `NonUnitalStarAlgHom.ext_of_orthogonal_essentialSubspace`: bounded operators agreeing after
  right multiplication by `π a` and on `π.essentialSubspaceᗮ` are equal on `H`.
* `NonUnitalStarAlgHom.restrictEssentialSubspace` and
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
closed linear span of all vectors `π a ξ`. -/
def essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure

/-- The essential subspace of a representation is closed. -/
theorem isClosed_essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (π.essentialSubspace : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : CompleteSpace π.essentialSubspace :=
  π.isClosed_essentialSubspace.completeSpace_coe

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- Every vector in the range of `π a` belongs to `π.essentialSubspace`. -/
theorem apply_mem_essentialSubspace (a : A) (ξ : H) : π a ξ ∈ π.essentialSubspace :=
  Submodule.le_topologicalClosure _ <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨a, ξ, rfl⟩

/-- A closed submodule contains `π.essentialSubspace` if and only if it contains every vector
`π a ξ`. -/
theorem essentialSubspace_le_iff {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) :
    π.essentialSubspace ≤ K ↔ ∀ a ξ, π a ξ ∈ K := by
  refine ⟨fun h a ξ => h (π.apply_mem_essentialSubspace a ξ), fun h => ?_⟩
  exact hK.closure_subset_iff.2 <| Submodule.span_le.2 <|
    Set.iUnion_subset fun a => Set.range_subset_iff.2 (h a)

/-- A vector lies in the orthogonal complement of `π.essentialSubspace` if and only if it is
annihilated by every operator `π a`. -/
theorem mem_orthogonal_essentialSubspace_iff {ξ : H} :
    ξ ∈ π.essentialSubspaceᗮ ↔ ∀ a, π a ξ = 0 := by
  refine ⟨fun hξ a => ext_inner_left ℂ fun v => ?_, fun hξ => ?_⟩
  · rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ (π.apply_mem_essentialSubspace (star a) v)
  · rw [Submodule.mem_orthogonal']
    refine (innerSL ℂ ξ).isClosed_ker.closure_subset_iff.2 <|
      (Submodule.span_le (p := (innerSL ℂ ξ).ker)).2 fun y hy => ?_
    obtain ⟨a, v, rfl⟩ := Set.mem_iUnion.1 hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, hξ (star a), inner_zero_left]

/-- Every operator `π a` vanishes on `π.essentialSubspaceᗮ`. -/
theorem apply_eq_zero_of_mem_orthogonal_essentialSubspace {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) (a : A) : π a ξ = 0 :=
  π.mem_orthogonal_essentialSubspace_iff.1 hξ a

/-- A representation is nondegenerate if and only if its essential subspace is `⊤`. -/
theorem isNondegenerate_iff_essentialSubspace_eq_top :
    π.IsNondegenerate ↔ π.essentialSubspace = ⊤ :=
  π.isNondegenerate_iff_dense.trans Submodule.dense_iff_topologicalClosure_eq_top

/-- The orthogonal complement of the essential subspace of a nondegenerate representation is `⊥`. -/
theorem orthogonal_essentialSubspace_eq_bot_of_isNondegenerate (hπ : π.IsNondegenerate) :
    π.essentialSubspaceᗮ = ⊥ := by
  rw [π.isNondegenerate_iff_essentialSubspace_eq_top.1 hπ, Submodule.top_orthogonal_eq_bot]

/-- Continuous linear operators on `H` that agree after right multiplication by every `π a` and
agree on `π.essentialSubspaceᗮ` are equal everywhere on `H`. -/
theorem ext_of_orthogonal_essentialSubspace {S T : H →L[ℂ] H}
    (hmul : ∀ a, S * π a = T * π a) (horth : ∀ ξ ∈ π.essentialSubspaceᗮ, S ξ = T ξ) :
    S = T := by
  have hess : ∀ η ∈ π.essentialSubspace, S η = T η := fun η hη =>
    ContinuousLinearMap.eqOn_closure_span (R₁ := ℂ) (s := ⋃ a, Set.range (π a))
      (fun _ hx => by obtain ⟨a, v, rfl⟩ := Set.mem_iUnion.1 hx; exact congr($(hmul a) v))
      (by
        simpa only [essentialSubspace, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
          using hη)
  ext ξ
  have hdecomp : ξ = π.essentialSubspace.starProjection ξ +
      (ξ - π.essentialSubspace.starProjection ξ) := (add_sub_cancel _ _).symm
  rw [hdecomp, map_add, map_add,
    hess _ (π.essentialSubspace.starProjection_apply_mem ξ),
    horth _ (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ)]

variable (π) in
/-- Compression of a representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to its closed essential subspace.
Because `π.essentialSubspace` contains all ranges of `π` and its orthogonal complement is killed by
`π`, this compression is a nondegenerate nonunital star-algebra homomorphism. -/
def restrictEssentialSubspace :
    A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace) where
  toFun a := π.essentialSubspace.orthogonalProjectionOnto ∘L π a ∘L π.essentialSubspace.subtypeL
  map_smul' c a := by
    ext ξ
    simp
  map_zero' := by
    ext ξ
    simp
  map_add' a b := by
    ext ξ
    simp
  map_mul' a b := by
    ext ξ
    simp [π.essentialSubspace.starProjection_eq_self_iff.2 (π.apply_mem_essentialSubspace b ξ)]
  map_star' a := by
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      π.essentialSubspace.adjoint_subtypeL, π.essentialSubspace.adjoint_orthogonalProjectionOnto,
      ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]

/-- Operator-composition unfolding of `restrictEssentialSubspace`. -/
theorem restrictEssentialSubspace_def (a : A) :
    π.restrictEssentialSubspace a =
      π.essentialSubspace.orthogonalProjectionOnto ∘L π a ∘L π.essentialSubspace.subtypeL :=
  (rfl)

/-- Coercing `π.restrictEssentialSubspace a ξ` back to `H` gives `π a ξ`. -/
@[simp]
theorem coe_restrictEssentialSubspace_apply (a : A) (ξ : π.essentialSubspace) :
    (π.restrictEssentialSubspace a ξ : H) = π a ξ :=
  π.essentialSubspace.starProjection_eq_self_iff.2 (π.apply_mem_essentialSubspace a ξ)

/-- Extending `π.restrictEssentialSubspace a` by zero on `π.essentialSubspaceᗮ` recovers `π a`. -/
@[simp]
theorem extendByZero_restrictEssentialSubspace (a : A) :
    π.essentialSubspace.extendByZero (π.restrictEssentialSubspace a) = π a :=
  π.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
    (π.apply_mem_essentialSubspace a) fun _ hξ =>
      π.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ a

/-- Composing `π.restrictEssentialSubspace` with `extendByZero` recovers `π`. -/
@[simp]
theorem extendByZero_comp_restrictEssentialSubspace :
    π.essentialSubspace.extendByZero.comp π.restrictEssentialSubspace = π :=
  NonUnitalStarAlgHom.ext π.extendByZero_restrictEssentialSubspace

/-- Compressing `π` to its essential subspace preserves operator norms. -/
@[simp]
theorem norm_restrictEssentialSubspace (a : A) : ‖π.restrictEssentialSubspace a‖ = ‖π a‖ := by
  rw [← π.essentialSubspace.norm_extendByZero, π.extendByZero_restrictEssentialSubspace]

/-- The compression of any representation to its essential subspace is nondegenerate. -/
theorem isNondegenerate_restrictEssentialSubspace :
    π.restrictEssentialSubspace.IsNondegenerate := by
  refine isNondegenerate_iff_forall_apply_eq_zero.2 fun ξ hξ => ?_
  have horth : (ξ : H) ∈ π.essentialSubspaceᗮ :=
    π.mem_orthogonal_essentialSubspace_iff.2 fun a => by
      simpa using congrArg Subtype.val (hξ a)
  exact Subtype.ext <| Submodule.mem_bot ℂ |>.1 <|
    π.essentialSubspace.inf_orthogonal_eq_bot ▸ ⟨ξ.2, horth⟩

end NonUnitalStarAlgHom
