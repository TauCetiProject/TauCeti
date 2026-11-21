/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import TauCeti.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.InnerProductSpace.Projection.ExtendByZero
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Essential subspaces of nonunital star subalgebras of operators

Let `A` be a nonunital star subalgebra of bounded operators on a Hilbert space `H` over `𝕜`
(`ℝ` or `ℂ`). Its *essential subspace* `A.essentialSubspace` is the closed linear span of all
image vectors `a ξ` for `a ∈ A` and `ξ : H`.

Because `A` is closed under adjoints, the orthogonal complement `A.essentialSubspaceᗮ` is the
common annihilator `⨅ a ∈ A, LinearMap.ker a.toLinearMap`
(`NonUnitalStarSubalgebra.orthogonal_essentialSubspace_eq_iInf_ker`). Every operator in `A` maps
`H` into `A.essentialSubspace` and vanishes on `A.essentialSubspaceᗮ`, so compressing `A` to
`A.essentialSubspace` yields a nondegenerate nonunital star subalgebra
`A.restrictEssentialSubspace` isometrically star-isomorphic to `A` via
`A.restrictEssentialSubspaceEquiv`.

## Main definitions and results

* `NonUnitalStarSubalgebra.essentialSubspace`: the closed linear span of all ranges `Set.range a`
  for `a ∈ A`, with `mem_orthogonal_essentialSubspace_iff` and
  `orthogonal_essentialSubspace_eq_iInf_ker` identifying its orthogonal complement with the common
  annihilator, `essentialSubspace_toNonUnitalStarSubalgebra` showing unital star subalgebras have
  essential subspace `⊤`, and `essentialSubspace_topologicalClosure` showing operator-norm closure
  preserves the essential subspace.
* `NonUnitalStarSubalgebra.ext_of_orthogonal_essentialSubspace`: bounded operators agreeing after
  right multiplication by every `a ∈ A` and on `A.essentialSubspaceᗮ` are equal.
* `NonUnitalStarSubalgebra.starProjection_essentialSubspace_mul` and
  `NonUnitalStarSubalgebra.mul_starProjection_essentialSubspace`:
  `A.essentialSubspace.starProjection` acts as a two-sided identity on `A`.
* `NonUnitalStarSubalgebra.restrictEssentialSubspace` and
  `NonUnitalStarSubalgebra.restrictEssentialSubspaceEquiv`: the nondegenerate compression of `A` to
  `A.essentialSubspace` and its isometric star-algebra isomorphism with `A`, with
  `essentialSubspace_restrictEssentialSubspace`.

## References

* Jacques Dixmier, *C*-Algebras*, Section 2.2.
* Jacques Dixmier, *Von Neumann Algebras*, Part I, Chapter I, Section 3.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace NonUnitalStarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The *essential subspace* of a nonunital star subalgebra `A` of bounded operators on `H`: the
closed linear span of all image vectors `a ξ` for `a ∈ A` and `ξ : H`. -/
def essentialSubspace (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) : Submodule 𝕜 H :=
  (Submodule.span 𝕜 (⋃ a ∈ A, Set.range a)).topologicalClosure

/-- Unfolding formula for `NonUnitalStarSubalgebra.essentialSubspace`. -/
theorem essentialSubspace_def (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace = (Submodule.span 𝕜 (⋃ a ∈ A, Set.range a)).topologicalClosure :=
  (rfl)

/-- The essential subspace of `A` is closed in `H`. -/
theorem isClosed_essentialSubspace (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (A.essentialSubspace : Set H) :=
  Submodule.isClosed_topologicalClosure _

/-- Being a closed subspace of the complete space `H`, `A.essentialSubspace` is complete. -/
instance instCompleteSpaceEssentialSubspace (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    CompleteSpace A.essentialSubspace :=
  A.isClosed_essentialSubspace.completeSpace_coe

variable {A B : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}

/-- Every operator in `A` maps `H` into `A.essentialSubspace`. -/
theorem apply_mem_essentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) (ξ : H) :
    a ξ ∈ A.essentialSubspace :=
  Submodule.le_topologicalClosure _ <| Submodule.subset_span <| Set.mem_iUnion₂.2 ⟨a, ha, ξ, rfl⟩

/-- A closed submodule contains `A.essentialSubspace` if and only if it contains `a ξ` for every
`a ∈ A` and `ξ : H`. -/
theorem essentialSubspace_le_iff {K : Submodule 𝕜 H} (hK : IsClosed (K : Set H)) :
    A.essentialSubspace ≤ K ↔ ∀ a ∈ A, ∀ ξ, a ξ ∈ K := by
  refine ⟨fun h a ha ξ => h (A.apply_mem_essentialSubspace ha ξ), fun h => ?_⟩
  exact hK.closure_subset_iff.2 <| Submodule.span_le.2 <|
    Set.iUnion₂_subset fun a ha => Set.range_subset_iff.2 (h a ha)

/-- `essentialSubspace` is monotone with respect to inclusion of nonunital star subalgebras. -/
theorem essentialSubspace_mono (h : A ≤ B) : A.essentialSubspace ≤ B.essentialSubspace :=
  (A.essentialSubspace_le_iff B.isClosed_essentialSubspace).2 fun _ ha ξ =>
    B.apply_mem_essentialSubspace (h ha) ξ

/-- The zero nonunital star subalgebra has trivial essential subspace. -/
@[simp]
theorem essentialSubspace_bot :
    (⊥ : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)).essentialSubspace = ⊥ :=
  le_antisymm
    ((essentialSubspace_le_iff
      (⊥ : Submodule 𝕜 H).isClosed_of_finiteDimensional).2 fun a ha ξ => by
      rw [NonUnitalStarAlgebra.mem_bot.1 ha, zero_apply]
      exact Submodule.zero_mem _)
    bot_le

/-- The full operator algebra has essential subspace `⊤`. -/
@[simp]
theorem essentialSubspace_top :
    (⊤ : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)).essentialSubspace = ⊤ :=
  eq_top_iff.2 fun ξ _ => by
    simpa using (⊤ : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)).apply_mem_essentialSubspace
      (a := (1 : H →L[𝕜] H)) trivial ξ

/-- A vector belongs to `A.essentialSubspaceᗮ` if and only if every operator in `A` annihilates
it. -/
theorem mem_orthogonal_essentialSubspace_iff {ξ : H} :
    ξ ∈ A.essentialSubspaceᗮ ↔ ∀ a ∈ A, a ξ = 0 := by
  refine ⟨fun hξ a ha => ext_inner_left 𝕜 fun v => ?_, fun hξ => ?_⟩
  · rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ (A.apply_mem_essentialSubspace (star_mem ha) v)
  · rw [Submodule.mem_orthogonal']
    exact (A.essentialSubspace_le_iff (innerSL 𝕜 ξ).isClosed_ker).2 fun a ha v => by
      simp [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hξ (star a) (star_mem ha)]

/-- Every operator in `A` vanishes on `A.essentialSubspaceᗮ`. -/
theorem apply_eq_zero_of_mem_orthogonal_essentialSubspace {ξ : H}
    (hξ : ξ ∈ A.essentialSubspaceᗮ) {a : H →L[𝕜] H} (ha : a ∈ A) : a ξ = 0 :=
  A.mem_orthogonal_essentialSubspace_iff.1 hξ a ha

/-- The orthogonal complement of `A.essentialSubspace` is the common annihilator
`⨅ a ∈ A, ker a`. -/
theorem orthogonal_essentialSubspace_eq_iInf_ker (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspaceᗮ = ⨅ a ∈ A, LinearMap.ker (a : H →ₗ[𝕜] H) := by
  ext ξ
  simp [A.mem_orthogonal_essentialSubspace_iff]

/-- The essential subspace is the orthogonal complement of the common annihilator of `A`. -/
theorem essentialSubspace_eq_orthogonal_iInf_ker (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace = (⨅ a ∈ A, LinearMap.ker (a : H →ₗ[𝕜] H))ᗮ := by
  rw [← A.orthogonal_essentialSubspace_eq_iInf_ker, A.essentialSubspace.orthogonal_orthogonal]

/-- `A.essentialSubspace` is all of `H` if and only if the common annihilator of `A` is `{0}`. -/
theorem essentialSubspace_eq_top_iff :
    A.essentialSubspace = ⊤ ↔ ∀ ξ : H, (∀ a ∈ A, a ξ = 0) → ξ = 0 := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  simp only [A.mem_orthogonal_essentialSubspace_iff]

/-- `A.essentialSubspace` is `⊥` if and only if `A = ⊥`. -/
@[simp]
theorem essentialSubspace_eq_bot_iff : A.essentialSubspace = ⊥ ↔ A = ⊥ := by
  refine ⟨fun h => SetLike.ext fun a => ?_, fun h => h ▸ essentialSubspace_bot⟩
  rw [NonUnitalStarAlgebra.mem_bot]
  refine ⟨fun ha => ?_, fun ha => ha ▸ zero_mem A⟩
  ext ξ
  have hξ : ξ ∈ A.essentialSubspaceᗮ := by
    rw [h, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  simpa using A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha

/-- Any unital star subalgebra viewed as a nonunital star subalgebra has essential subspace `⊤`. -/
@[simp]
theorem essentialSubspace_toNonUnitalStarSubalgebra (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    S.toNonUnitalStarSubalgebra.essentialSubspace = ⊤ :=
  eq_top_iff.2 fun ξ _ => by
    simpa using S.toNonUnitalStarSubalgebra.apply_mem_essentialSubspace S.one_mem ξ

/-- Taking the operator-norm closure of `A` does not change its essential subspace. -/
@[simp]
theorem essentialSubspace_topologicalClosure (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.topologicalClosure.essentialSubspace = A.essentialSubspace := by
  refine le_antisymm ((A.topologicalClosure.essentialSubspace_le_iff
      A.isClosed_essentialSubspace).2 fun a ha ξ => ?_)
    (essentialSubspace_mono A.le_topologicalClosure)
  have ha' : a ∈ _root_.closure (A : Set (H →L[𝕜] H)) := by
    rwa [← NonUnitalStarSubalgebra.topologicalClosure_coe]
  have hmem : a ξ ∈ _root_.closure ((fun b : H →L[𝕜] H => b ξ) '' (A : Set (H →L[𝕜] H))) :=
    mem_closure_image (ContinuousLinearMap.apply 𝕜 H ξ).continuous.continuousAt ha'
  refine A.isClosed_essentialSubspace.closure_subset_iff.2 ?_ hmem
  rintro _ ⟨b, hb, rfl⟩
  exact A.apply_mem_essentialSubspace hb ξ

/-- Bounded operators on `H` that agree after right multiplication by every `a ∈ A` and agree on
`A.essentialSubspaceᗮ` are equal everywhere on `H`. -/
theorem ext_of_orthogonal_essentialSubspace {S T : H →L[𝕜] H}
    (hmul : ∀ a ∈ A, S * a = T * a) (horth : ∀ ξ ∈ A.essentialSubspaceᗮ, S ξ = T ξ) :
    S = T := by
  have hker : A.essentialSubspace ≤ LinearMap.ker (S - T).toLinearMap :=
    (A.essentialSubspace_le_iff (S - T).isClosed_ker).2 fun a ha v => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, _root_.sub_apply,
        ← _root_.mul_apply_eq_comp, ← _root_.mul_apply_eq_comp, hmul a ha, sub_self]
  ext ξ
  have hsub : (S - T) ξ = 0 := by
    rw [← A.essentialSubspace.apply_starProjection_eq_of_forall_mem_orthogonal
      (fun η hη => by simp [horth η hη])]
    exact LinearMap.mem_ker.1 (hker (A.essentialSubspace.starProjection_apply_mem ξ))
  exact sub_eq_zero.1 hsub

/-- Left multiplication by `A.essentialSubspace.starProjection` fixes every element of `A`. -/
theorem starProjection_essentialSubspace_mul {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspace.starProjection * a = a := by
  ext ξ
  exact A.essentialSubspace.starProjection_eq_self_iff.2 (A.apply_mem_essentialSubspace ha ξ)

/-- Right multiplication by `A.essentialSubspace.starProjection` fixes every element of `A`. -/
theorem mul_starProjection_essentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    a * A.essentialSubspace.starProjection = a :=
  A.essentialSubspace.mul_starProjection_eq_self fun _ hξ =>
    A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha

/-- Left multiplication by `A.essentialSubspaceᗮ.starProjection` annihilates every element of
`A`. -/
theorem starProjection_orthogonal_essentialSubspace_mul {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspaceᗮ.starProjection * a = 0 := by
  rw [Submodule.starProjection_orthogonal', sub_mul, one_mul,
    A.starProjection_essentialSubspace_mul ha, sub_self]

/-- Right multiplication by `A.essentialSubspaceᗮ.starProjection` annihilates every element of
`A`. -/
theorem mul_starProjection_orthogonal_essentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    a * A.essentialSubspaceᗮ.starProjection = 0 := by
  rw [Submodule.starProjection_orthogonal', mul_sub, mul_one,
    A.mul_starProjection_essentialSubspace ha, sub_self]

variable (A) in
/-- Compression of a nonunital star subalgebra `A` of bounded operators on `H` to its essential
subspace `A.essentialSubspace`, defined as the preimage of `A` along
`A.essentialSubspace.extendByZero`. -/
def restrictEssentialSubspace :
    NonUnitalStarSubalgebra 𝕜 (A.essentialSubspace →L[𝕜] A.essentialSubspace) :=
  A.comap A.essentialSubspace.extendByZero

/-- Unfolding formula for `NonUnitalStarSubalgebra.restrictEssentialSubspace`. -/
theorem restrictEssentialSubspace_def (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.restrictEssentialSubspace = A.comap A.essentialSubspace.extendByZero :=
  (rfl)

/-- An operator on `A.essentialSubspace` belongs to `A.restrictEssentialSubspace` if and only if
its extension by zero on `A.essentialSubspaceᗮ` belongs to `A`. -/
@[simp]
theorem mem_restrictEssentialSubspace
    {S : A.essentialSubspace →L[𝕜] A.essentialSubspace} :
    S ∈ A.restrictEssentialSubspace ↔ A.essentialSubspace.extendByZero S ∈ A :=
  Iff.rfl

/-- Every operator in `A` is recovered by compressing to `A.essentialSubspace` and extending by
zero on `A.essentialSubspaceᗮ`. -/
theorem extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspace.extendByZero
        (A.essentialSubspace.orthogonalProjectionOnto ∘L a ∘L A.essentialSubspace.subtypeL) =
      a :=
  A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
    (A.apply_mem_essentialSubspace ha) fun _ hξ =>
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha

/-- Compressing any operator `a ∈ A` to `A.essentialSubspace` produces an element of
`A.restrictEssentialSubspace`. -/
theorem orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L a ∘L A.essentialSubspace.subtypeL ∈
      A.restrictEssentialSubspace := by
  rw [mem_restrictEssentialSubspace, A.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL ha]
  exact ha

/-- The canonical star-algebra isomorphism `A.restrictEssentialSubspace ≃⋆ₐ[𝕜] A` extending
operators on `A.essentialSubspace` by zero on `A.essentialSubspaceᗮ`, with inverse given by
compression to `A.essentialSubspace`. -/
def restrictEssentialSubspaceEquiv (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.restrictEssentialSubspace ≃⋆ₐ[𝕜] A :=
  { (A.essentialSubspace.extendByZero.comp
      (NonUnitalStarSubalgebraClass.subtype A.restrictEssentialSubspace)).codRestrict A
      (fun S => S.property) with
    invFun := fun a =>
      ⟨A.essentialSubspace.orthogonalProjectionOnto ∘L a.val ∘L A.essentialSubspace.subtypeL,
        A.orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace a.property⟩
    left_inv := fun S => Subtype.ext <|
      A.essentialSubspace.orthogonalProjectionOnto_comp_extendByZero_comp_subtypeL S.val
    right_inv := fun a => Subtype.ext <|
      A.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL a.property }

/-- `A.restrictEssentialSubspaceEquiv` acts by `A.essentialSubspace.extendByZero`. -/
@[simp]
theorem coe_restrictEssentialSubspaceEquiv_apply (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (S : A.restrictEssentialSubspace) :
    (A.restrictEssentialSubspaceEquiv S : H →L[𝕜] H) = A.essentialSubspace.extendByZero S.val :=
  (rfl)

/-- The inverse of `A.restrictEssentialSubspaceEquiv` compresses operators in `A` to
`A.essentialSubspace`. -/
@[simp]
theorem coe_restrictEssentialSubspaceEquiv_symm_apply (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (a : A) :
    (A.restrictEssentialSubspaceEquiv.symm a : A.essentialSubspace →L[𝕜] A.essentialSubspace) =
      A.essentialSubspace.orthogonalProjectionOnto ∘L a.val ∘L A.essentialSubspace.subtypeL :=
  (rfl)

/-- `A.restrictEssentialSubspaceEquiv` preserves operator norms. -/
theorem norm_restrictEssentialSubspaceEquiv (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (S : A.restrictEssentialSubspace) :
    ‖A.restrictEssentialSubspaceEquiv S‖ = ‖S‖ :=
  A.essentialSubspace.norm_extendByZero S.val

/-- `A.restrictEssentialSubspaceEquiv` is an isometry for the operator norms. -/
theorem isometry_restrictEssentialSubspaceEquiv (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    Isometry A.restrictEssentialSubspaceEquiv :=
  AddMonoidHomClass.isometry_of_norm A.restrictEssentialSubspaceEquiv
    A.norm_restrictEssentialSubspaceEquiv

/-- Mapping `A.restrictEssentialSubspace` back to `H` along `extendByZero` recovers `A`. -/
@[simp]
theorem map_extendByZero_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.restrictEssentialSubspace.map A.essentialSubspace.extendByZero = A := by
  ext a
  simp only [mem_map, mem_restrictEssentialSubspace]
  exact ⟨by rintro ⟨S, hS, rfl⟩; exact hS, fun ha =>
    ⟨(A.restrictEssentialSubspaceEquiv.symm ⟨a, ha⟩).val,
      (A.restrictEssentialSubspaceEquiv.symm ⟨a, ha⟩).property,
      by simpa only [coe_restrictEssentialSubspaceEquiv_apply] using
        congrArg Subtype.val (A.restrictEssentialSubspaceEquiv.apply_symm_apply ⟨a, ha⟩)⟩⟩

/-- The image of `A.restrictEssentialSubspace` under `A.essentialSubspace.extendByZero` is `A`. -/
@[simp]
theorem image_extendByZero_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.extendByZero ''
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[𝕜] A.essentialSubspace)) =
      (A : Set (H →L[𝕜] H)) := by
  rw [← coe_map, map_extendByZero_restrictEssentialSubspace]

/-- `A.restrictEssentialSubspace` is nondegenerate on `A.essentialSubspace`: its essential
subspace is `⊤`. -/
@[simp]
theorem essentialSubspace_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.restrictEssentialSubspace.essentialSubspace = ⊤ := by
  refine A.restrictEssentialSubspace.essentialSubspace_eq_top_iff.2 fun u hu => ?_
  have horth : (u : H) ∈ A.essentialSubspaceᗮ := by
    refine A.mem_orthogonal_essentialSubspace_iff.2 fun a ha => ?_
    have hmem := A.orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace ha
    have hzero := congrArg (Subtype.val : A.essentialSubspace → H) (hu _ hmem)
    simpa [A.essentialSubspace.starProjection_eq_self_iff.2
      (A.apply_mem_essentialSubspace ha u)] using hzero
  exact Subtype.ext <| (Submodule.mem_bot 𝕜).1 <|
    A.essentialSubspace.inf_orthogonal_eq_bot ▸ ⟨u.property, horth⟩

/-- For any complete subspace `U` of `H`, the range of `U.extendByZero` has essential subspace
`U`. -/
@[simp]
theorem essentialSubspace_range_extendByZero (U : Submodule 𝕜 H) [CompleteSpace U] :
    (NonUnitalStarAlgHom.range U.extendByZero).essentialSubspace = U := by
  refine le_antisymm
    (((NonUnitalStarAlgHom.range U.extendByZero).essentialSubspace_le_iff
      (completeSpace_coe_iff_isComplete.1 ‹CompleteSpace U›).isClosed).2 ?_)
    fun ξ hξ => ?_
  · rintro _ ⟨S, rfl⟩ x
    exact U.extendByZero_apply_mem S x
  · have hproj : U.starProjection ∈ NonUnitalStarAlgHom.range U.extendByZero :=
      ⟨1, U.extendByZero_one⟩
    simpa [U.starProjection_eq_self_iff.2 hξ] using
      (NonUnitalStarAlgHom.range U.extendByZero).apply_mem_essentialSubspace hproj ξ

end NonUnitalStarSubalgebra
