/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.ExtendByZero
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.InnerProductSpace.Amplification

/-!
# Nonunital star subalgebras of operators, essential subspaces, and operator closures

A nonunital star subalgebra `A` of bounded operators on a Hilbert space `H` need not contain the
identity operator on `H`, and its raw double commutant `A''` always contains `1` even when every
operator in `A` vanishes on a nontrivial subspace. Separating the common annihilator from the
essential subspace resolves this discrepancy.

The *essential subspace* `A.essentialSubspace` is the closed linear span of all ranges `range a`
for `a ∈ A`. Because `A` is closed under adjoints, the orthogonal complement
`A.essentialSubspaceᗮ` is the common annihilator `⨅ a ∈ A, ker a`
(`NonUnitalStarSubalgebra.orthogonal_essentialSubspace_eq_iInf_ker`). Every operator in `A` has
range in `A.essentialSubspace` and vanishes on `A.essentialSubspaceᗮ`, so compressing `A` to
`A.essentialSubspace` produces a nondegenerate nonunital star subalgebra
`A.restrictEssentialSubspace` isomorphic to `A` via `A.restrictEssentialSubspaceEquiv`.

Without assuming an operator-norm closure or approximate unit,
`A.essentialSubspace.starProjection v` lies in the closure of the orbit `A v` for every `v : H`
(`NonUnitalStarSubalgebra.starProjection_essentialSubspace_apply_mem_closure`), and diagonal
amplification approximates `A.essentialSubspace.starProjection` simultaneously on finitely many
vectors (`exists_forall_norm_starProjection_essentialSubspace_sub_apply_lt`).
Combining this projection approximation with the unital von Neumann density theorem on
`StarAlgebra.adjoin 𝕜 A` yields the nonunital density theorem
(`NonUnitalStarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`):
every operator in `A''` that vanishes on `A.essentialSubspaceᗮ` is a strong-operator limit of
elements of `A`.

Consequently:

* On `A.essentialSubspace`, both the strong and weak operator closures of
  `A.restrictEssentialSubspace` equal its unital double commutant `(A.restrictEssentialSubspace)''`
  (`closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace`,
  `closure_image_ofCLM_restrictEssentialSubspace`), packaging over `ℂ` into a concrete
  `VonNeumannAlgebra A.essentialSubspace` (`NonUnitalStarSubalgebra.essentialVonNeumannAlgebra`).
* On `H`, both the strong and weak operator closures of `A` equal the supported algebra
  `{x ∈ A'' | ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} =
  A.essentialSubspace.extendByZero '' (A.restrictEssentialSubspace)''`, with two-sided identity
  `A.essentialSubspace.starProjection` (`closure_image_toPointwiseConvergenceCLM`,
  `closure_image_ofCLM`).
* By contrast, the full double commutant `A''` splits as
  `A.essentialSubspace.extendByZero '' (A.restrictEssentialSubspace)'' +
  𝕜 • A.essentialSubspaceᗮ.starProjection` (`mem_centralizer_centralizer_iff`), adjoining scalar
  multiples of the identity on the annihilator; thus `1` belongs to the strong or weak operator
  closure of `A` (and those closures equal `A''`) if and only if `A.essentialSubspace = ⊤`.

## References

* Jacques Dixmier, *Von Neumann Algebras*, Part I, Chapter I, Section 3, Corollary 1.
* Richard V. Kadison and John R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Section 5.3, Remark 5.3.2.
-/

public section

noncomputable section

open scoped InnerProductSpace Topology

namespace NonUnitalStarSubalgebra

section EssentialSubspace

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

/-- Any unital star subalgebra viewed as a nonunital star subalgebra has essential subspace `⊤`. -/
@[simp]
theorem essentialSubspace_toNonUnitalStarSubalgebra (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    S.toNonUnitalStarSubalgebra.essentialSubspace = ⊤ :=
  eq_top_iff.2 fun ξ _ => by
    simpa using S.toNonUnitalStarSubalgebra.apply_mem_essentialSubspace S.one_mem ξ

/-- The full operator algebra has essential subspace `⊤`. -/
@[simp]
theorem essentialSubspace_top :
    (⊤ : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)).essentialSubspace = ⊤ :=
  essentialSubspace_toNonUnitalStarSubalgebra ⊤

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

end EssentialSubspace

section AnnihilatorAndCompression

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}

/-- A vector belongs to `A.essentialSubspaceᗮ` if and only if every operator in `A` annihilates
it. -/
theorem mem_orthogonal_essentialSubspace_iff {ξ : H} :
    ξ ∈ A.essentialSubspaceᗮ ↔ ∀ a ∈ A, a ξ = 0 := by
  refine ⟨fun hξ a ha => ext_inner_left 𝕜 fun v => ?_, fun hξ => ?_⟩
  · rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ (A.apply_mem_essentialSubspace (star_mem ha) v)
  · rw [Submodule.mem_orthogonal']
    refine (innerSL 𝕜 ξ).isClosed_ker.closure_subset_iff.2 <|
      (Submodule.span_le (p := (innerSL 𝕜 ξ).ker)).2 fun y hy => ?_
    obtain ⟨a, ha, v, rfl⟩ := Set.mem_iUnion₂.1 hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, hξ (star a) (star_mem ha), inner_zero_left]

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

/-- Left multiplication by `A.essentialSubspace.starProjection` fixes every element of `A`. -/
theorem starProjection_essentialSubspace_mul {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspace.starProjection * a = a := by
  ext ξ
  exact A.essentialSubspace.starProjection_eq_self_iff.2 (A.apply_mem_essentialSubspace ha ξ)

/-- Right multiplication by `A.essentialSubspace.starProjection` fixes every element of `A`. -/
theorem mul_starProjection_essentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    a * A.essentialSubspace.starProjection = a := by
  ext ξ
  have hdecomp : ξ = A.essentialSubspace.starProjection ξ +
      (ξ - A.essentialSubspace.starProjection ξ) := (add_sub_cancel _ _).symm
  conv_rhs => rw [hdecomp, map_add,
    A.apply_eq_zero_of_mem_orthogonal_essentialSubspace
      (A.essentialSubspace.sub_starProjection_mem_orthogonal ξ) ha, add_zero]
  rfl

/-- Left multiplication by `A.essentialSubspaceᗮ.starProjection` annihilates every element of
`A`. -/
theorem starProjection_orthogonal_essentialSubspace_mul {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspaceᗮ.starProjection * a = 0 := by
  rw [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def, sub_mul, one_mul,
    A.starProjection_essentialSubspace_mul ha, sub_self]

/-- Right multiplication by `A.essentialSubspaceᗮ.starProjection` annihilates every element of
`A`. -/
theorem mul_starProjection_orthogonal_essentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    a * A.essentialSubspaceᗮ.starProjection = 0 := by
  rw [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def, mul_sub, mul_one,
    A.mul_starProjection_essentialSubspace ha, sub_self]

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the commutant of `A`. -/
theorem starProjection_essentialSubspace_mem_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer :=
  fun _ ha => (A.mul_starProjection_essentialSubspace ha).trans
    (A.starProjection_essentialSubspace_mul ha).symm

/-- Every operator on `A.essentialSubspaceᗮ` extended by zero on `A.essentialSubspace` belongs to
the commutant of `A`. -/
theorem orthogonal_extendByZero_mem_centralizer (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (Q : A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ) :
    A.essentialSubspaceᗮ.extendByZero Q ∈ (A : Set (H →L[𝕜] H)).centralizer := by
  intro a ha
  have ha_eq : a = A.essentialSubspace.extendByZero
      (A.essentialSubspace.orthogonalProjectionOnto ∘L a ∘L A.essentialSubspace.subtypeL) :=
    (A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
      (A.apply_mem_essentialSubspace ha) fun _ hξ =>
        A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha).symm
  rw [ha_eq]
  exact A.essentialSubspace.commute_extendByZero_orthogonal_extendByZero _ Q

/-- `A.essentialSubspace` reduces every operator in the commutant of `A`. -/
theorem isReducing_essentialSubspace_of_mem_centralizer {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    A.essentialSubspace.IsReducing (y : Module.End 𝕜 H) := by
  refine (A.essentialSubspace.isReducing_iff _).2 ⟨?_, ?_⟩
  · rw [Module.End.mem_invtSubmodule]
    refine (A.essentialSubspace_le_iff
      (A.isClosed_essentialSubspace.preimage y.continuous)).2 fun a ha ξ => ?_
    have hcomm : a (y ξ) = y (a ξ) := by
      simpa only [_root_.mul_apply_eq_comp] using congrArg (fun T : H →L[𝕜] H => T ξ) (hy a ha)
    simpa only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ← hcomm] using
      A.apply_mem_essentialSubspace ha (y ξ)
  · intro ξ hξ
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, A.mem_orthogonal_essentialSubspace_iff]
    intro a ha
    have hcomm := congrArg (fun T : H →L[𝕜] H => T ξ) (hy a ha)
    simpa only [_root_.mul_apply_eq_comp,
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha, map_zero] using hcomm

/-- Every operator in the commutant of `A` commutes with `A.essentialSubspace.starProjection`. -/
theorem commute_starProjection_essentialSubspace_of_mem_centralizer {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    Commute A.essentialSubspace.starProjection y :=
  Submodule.isReducing_coe_iff_commute_starProjection.1
    (A.isReducing_essentialSubspace_of_mem_centralizer hy)

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the double commutant `A''`. -/
theorem starProjection_essentialSubspace_mem_centralizer_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
  fun _ hy => (A.commute_starProjection_essentialSubspace_of_mem_centralizer hy).symm.eq

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

/-- Compressing any operator `a ∈ A` to `A.essentialSubspace` produces an element of
`A.restrictEssentialSubspace`. -/
theorem orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace {a : H →L[𝕜] H} (ha : a ∈ A) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L a ∘L A.essentialSubspace.subtypeL ∈
      A.restrictEssentialSubspace := by
  rw [mem_restrictEssentialSubspace,
    A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
      (A.apply_mem_essentialSubspace ha) fun _ hξ =>
        A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha]
  exact ha

/-- The canonical star-algebra isomorphism `A.restrictEssentialSubspace ≃⋆ₐ[𝕜] A` extending
operators on `A.essentialSubspace` by zero on `A.essentialSubspaceᗮ`, with inverse given by
compression to `A.essentialSubspace`. -/
def restrictEssentialSubspaceEquiv (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.restrictEssentialSubspace ≃⋆ₐ[𝕜] A where
  toFun S := ⟨A.essentialSubspace.extendByZero S.1, S.2⟩
  invFun a :=
    ⟨A.essentialSubspace.orthogonalProjectionOnto ∘L a.1 ∘L A.essentialSubspace.subtypeL,
      A.orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace a.2⟩
  left_inv S := Subtype.ext <|
    A.essentialSubspace.orthogonalProjectionOnto_comp_extendByZero_comp_subtypeL S.1
  right_inv a := Subtype.ext <|
    A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
      (A.apply_mem_essentialSubspace a.2) fun _ hξ =>
        A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ a.2
  map_mul' S T := Subtype.ext (map_mul A.essentialSubspace.extendByZero S.1 T.1)
  map_add' S T := Subtype.ext (map_add A.essentialSubspace.extendByZero S.1 T.1)
  map_smul' c S := Subtype.ext (map_smul A.essentialSubspace.extendByZero c S.1)
  map_star' S := Subtype.ext (map_star A.essentialSubspace.extendByZero S.1)

/-- `A.restrictEssentialSubspaceEquiv` acts by `A.essentialSubspace.extendByZero`. -/
@[simp]
theorem coe_restrictEssentialSubspaceEquiv_apply (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (S : A.restrictEssentialSubspace) :
    (A.restrictEssentialSubspaceEquiv S : H →L[𝕜] H) = A.essentialSubspace.extendByZero S.1 :=
  (rfl)

/-- The inverse of `A.restrictEssentialSubspaceEquiv` compresses operators in `A` to
`A.essentialSubspace`. -/
@[simp]
theorem coe_restrictEssentialSubspaceEquiv_symm_apply (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (a : A) :
    (A.restrictEssentialSubspaceEquiv.symm a : A.essentialSubspace →L[𝕜] A.essentialSubspace) =
      A.essentialSubspace.orthogonalProjectionOnto ∘L a.1 ∘L A.essentialSubspace.subtypeL :=
  (rfl)

/-- `A.restrictEssentialSubspaceEquiv` preserves operator norms. -/
theorem norm_restrictEssentialSubspaceEquiv (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (S : A.restrictEssentialSubspace) :
    ‖A.restrictEssentialSubspaceEquiv S‖ = ‖S‖ :=
  A.essentialSubspace.norm_extendByZero S.1

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
    ⟨_, A.orthogonalProjectionOnto_comp_mem_restrictEssentialSubspace ha,
      A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
        (A.apply_mem_essentialSubspace ha) fun _ hξ =>
          A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha⟩⟩

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
    A.essentialSubspace.inf_orthogonal_eq_bot ▸ ⟨u.2, horth⟩

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

end AnnihilatorAndCompression

section DoubleCommutant

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}

/-- `A.essentialSubspace.extendByZero R` commutes with `A` on `H` if and only if `R` commutes with
`A.restrictEssentialSubspace` on `A.essentialSubspace`. -/
theorem extendByZero_mem_centralizer_iff
    {R : A.essentialSubspace →L[𝕜] A.essentialSubspace} :
    A.essentialSubspace.extendByZero R ∈ (A : Set (H →L[𝕜] H)).centralizer ↔
      R ∈ (A.restrictEssentialSubspace : Set _).centralizer := by
  rw [← A.image_extendByZero_restrictEssentialSubspace]
  simp only [Set.mem_centralizer_iff, Set.forall_mem_image, ← map_mul,
    A.essentialSubspace.extendByZero_injective.eq_iff]

/-- Compressing an element of `A'` to `A.essentialSubspace` yields an element of
`(A.restrictEssentialSubspace)'`. -/
theorem compression_mem_centralizer_restrictEssentialSubspace {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L y ∘L A.essentialSubspace.subtypeL ∈
      (A.restrictEssentialSubspace : Set _).centralizer := by
  intro S hS
  have hcomm : Commute (A.essentialSubspace.extendByZero S) y := hy _ hS
  exact (A.essentialSubspace.commute_extendByZero_iff_of_commute
    (A.commute_starProjection_essentialSubspace_of_mem_centralizer hy) S).1 hcomm

/-- `A.essentialSubspace.extendByZero S` belongs to `A''` on `H` if and only if `S` belongs to
`(A.restrictEssentialSubspace)''` on `A.essentialSubspace`. -/
theorem extendByZero_mem_centralizer_centralizer_iff
    {S : A.essentialSubspace →L[𝕜] A.essentialSubspace} :
    A.essentialSubspace.extendByZero S ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      S ∈ (A.restrictEssentialSubspace : Set _).centralizer.centralizer := by
  refine ⟨fun hS R hR => ?_, fun hS y hy => ?_⟩
  · have hcomm : Commute (A.essentialSubspace.extendByZero R)
        (A.essentialSubspace.extendByZero S) :=
      hS _ (A.extendByZero_mem_centralizer_iff.2 hR)
    exact A.essentialSubspace.extendByZero_injective (by simpa only [map_mul] using hcomm.eq)
  · have hy_comm := A.commute_starProjection_essentialSubspace_of_mem_centralizer hy
    have hSR : Commute S
        (A.essentialSubspace.orthogonalProjectionOnto ∘L y ∘L A.essentialSubspace.subtypeL) :=
      (hS _ (A.compression_mem_centralizer_restrictEssentialSubspace hy)).symm
    exact ((A.essentialSubspace.commute_extendByZero_iff_of_commute hy_comm S).2 hSR).symm.eq

/-- Compressing an element of `A''` to `A.essentialSubspace` yields an element of
`(A.restrictEssentialSubspace)''`. -/
theorem compression_mem_centralizer_centralizer_restrictEssentialSubspace {x : H →L[𝕜] H}
    (hx : x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L x ∘L A.essentialSubspace.subtypeL ∈
      (A.restrictEssentialSubspace : Set _).centralizer.centralizer := by
  have hx_comm : Commute A.essentialSubspace.starProjection x :=
    hx _ A.starProjection_essentialSubspace_mem_centralizer
  intro R hR
  have hRx : Commute (A.essentialSubspace.extendByZero R) x :=
    hx _ (A.extendByZero_mem_centralizer_iff.2 hR)
  exact (A.essentialSubspace.commute_extendByZero_iff_of_commute hx_comm R).1 hRx

/-- **Decomposition of the double commutant of a nonunital star subalgebra.** Every operator in
`A''` decomposes into an element of `(A.restrictEssentialSubspace)''` extended by zero on
`A.essentialSubspaceᗮ` plus a scalar multiple of the orthogonal projection onto the common
annihilator `A.essentialSubspaceᗮ`. -/
theorem mem_centralizer_centralizer_iff {x : H →L[𝕜] H} :
    x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      ∃ S ∈ (A.restrictEssentialSubspace : Set _).centralizer.centralizer,
        ∃ c : 𝕜, x = A.essentialSubspace.extendByZero S +
          c • A.essentialSubspaceᗮ.starProjection := by
  refine ⟨fun hx => ?_, ?_⟩
  · have hx_comm : Commute A.essentialSubspace.starProjection x :=
      hx _ A.starProjection_essentialSubspace_mem_centralizer
    have hx_orth_comm : Commute A.essentialSubspaceᗮ.starProjection x := by
      rw [Submodule.starProjection_orthogonal]
      exact (Commute.one_left x).sub_left hx_comm
    set x_orth : A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ :=
      A.essentialSubspaceᗮ.orthogonalProjectionOnto ∘L x ∘L A.essentialSubspaceᗮ.subtypeL with
      hx_orth_def
    -- `x_orth` commutes with every bounded operator on `A.essentialSubspaceᗮ`, so it lies in the
    -- center of `B(A.essentialSubspaceᗮ)` and is therefore a scalar multiple of `1`.
    have hx_center : x_orth ∈ Subalgebra.center 𝕜
        (A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ) := by
      rw [Subalgebra.mem_center_iff]
      intro Q
      have hQx : Commute (A.essentialSubspaceᗮ.extendByZero Q) x :=
        hx _ (A.orthogonal_extendByZero_mem_centralizer Q)
      exact (A.essentialSubspaceᗮ.commute_extendByZero_iff_of_commute hx_orth_comm Q).1 hQx
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff (K := 𝕜)).1 hx_center
    have hx_orth_eq : x_orth = c • 1 := by
      rw [hc, Algebra.algebraMap_eq_smul_one]
    refine ⟨_, A.compression_mem_centralizer_centralizer_restrictEssentialSubspace hx, c, ?_⟩
    conv_lhs =>
      rw [A.essentialSubspace.eq_extendByZero_add_orthogonal_extendByZero_of_commute hx_comm]
    rw [← hx_orth_def, hx_orth_eq, map_smul, Submodule.extendByZero_one]
  · rintro ⟨S, hS, c, rfl⟩
    have hS' : A.essentialSubspace.extendByZero S ∈
        (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
      A.extendByZero_mem_centralizer_centralizer_iff.2 hS
    have hp_orth : A.essentialSubspaceᗮ.starProjection ∈
        (A : Set (H →L[𝕜] H)).centralizer.centralizer := by
      rw [Submodule.starProjection_orthogonal]
      exact (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).sub_mem
        (Subalgebra.one_mem _) A.starProjection_essentialSubspace_mem_centralizer_centralizer
    exact (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).add_mem hS'
      (Subalgebra.smul_mem _ hp_orth c)

/-- Extending `(A.restrictEssentialSubspace)''` by zero on `A.essentialSubspaceᗮ` cuts out
precisely the operators in `A''` that vanish on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem image_extendByZero_centralizer_centralizer (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.extendByZero ''
      (A.restrictEssentialSubspace : Set _).centralizer.centralizer =
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  ext x
  refine ⟨?_, fun ⟨hx, hker⟩ => ?_⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨A.extendByZero_mem_centralizer_centralizer_iff.2 hS, fun _ hξ =>
      A.essentialSubspace.extendByZero_apply_of_mem_orthogonal S hξ⟩
  · have hx_comm : Commute A.essentialSubspace.starProjection x :=
      hx _ A.starProjection_essentialSubspace_mem_centralizer
    refine ⟨A.essentialSubspace.orthogonalProjectionOnto ∘L x ∘L A.essentialSubspace.subtypeL,
      A.compression_mem_centralizer_centralizer_restrictEssentialSubspace hx, ?_⟩
    rw [A.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_of_commute
      hx_comm]
    ext ξ
    have hdecomp : ξ = A.essentialSubspace.starProjection ξ +
        (ξ - A.essentialSubspace.starProjection ξ) := (add_sub_cancel _ _).symm
    conv_rhs => rw [hdecomp, map_add,
      hker _ (A.essentialSubspace.sub_starProjection_mem_orthogonal ξ), add_zero]
    rfl

end DoubleCommutant

section Density

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- For every vector `v : H`, `A.essentialSubspace.starProjection v` lies in the closure of the
orbit `A v`. -/
theorem starProjection_essentialSubspace_apply_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) (v : H) :
    A.essentialSubspace.starProjection v ∈ closure ((fun a : H →L[𝕜] H => a v) '' A) := by
  set K : Submodule 𝕜 H :=
    (A.toNonUnitalSubalgebra.toSubmodule.map
      (ContinuousLinearMap.apply 𝕜 H v).toLinearMap).topologicalClosure with hK
  have hKcoe : (K : Set H) = closure ((fun a : H →L[𝕜] H => a v) '' A) := by
    rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
    rfl
  have hKc : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure _
  have hKle : K ≤ A.essentialSubspace := by
    refine Submodule.topologicalClosure_minimal _ ?_ A.isClosed_essentialSubspace
    rintro _ ⟨a, ha, rfl⟩
    exact A.apply_mem_essentialSubspace ha v
  -- `K` is invariant under `A` and hence reducing, so `K.starProjection` commutes with `A`.
  have hinv : ∀ t ∈ A, K ∈ Module.End.invtSubmodule (t : Module.End 𝕜 H) := by
    intro t ht
    rw [Module.End.mem_invtSubmodule]
    refine Submodule.topologicalClosure_minimal _ ?_ (hKc.preimage t.continuous)
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨t * a, A.mul_mem ht ha, rfl⟩
  have hp : K.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer := by
    intro t ht
    have hadj : K ∈ Module.End.invtSubmodule (t.adjoint : Module.End 𝕜 H) := by
      simpa [← ContinuousLinearMap.star_eq_adjoint] using hinv (star t) (star_mem ht)
    have hred : K.IsReducing (t : Module.End 𝕜 H) :=
      ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr ⟨hinv t ht, hadj⟩
    exact (Submodule.isReducing_coe_iff_commute_starProjection.mp hred).eq.symm
  -- `A.essentialSubspace.starProjection v - K.starProjection v` lies in both `A.essentialSubspace`
  -- and `A.essentialSubspaceᗮ`, so it vanishes.
  have hdiff_orth :
      A.essentialSubspace.starProjection v - K.starProjection v ∈ A.essentialSubspaceᗮ := by
    refine A.mem_orthogonal_essentialSubspace_iff.2 fun a ha => ?_
    have haK : K.starProjection (a v) = a v :=
      K.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ ⟨a, ha, rfl⟩)
    calc a (A.essentialSubspace.starProjection v - K.starProjection v)
        = (a * A.essentialSubspace.starProjection) v - (a * K.starProjection) v := by
          rw [map_sub]; rfl
      _ = a v - K.starProjection (a v) := by
          rw [A.mul_starProjection_essentialSubspace ha, hp a ha]; rfl
      _ = 0 := by rw [haK, sub_self]
  have hdiff_mem :
      A.essentialSubspace.starProjection v - K.starProjection v ∈ A.essentialSubspace :=
    A.essentialSubspace.sub_mem (A.essentialSubspace.starProjection_apply_mem v)
      (hKle (K.starProjection_apply_mem v))
  have hpv_eq : A.essentialSubspace.starProjection v = K.starProjection v :=
    sub_eq_zero.1 <| (Submodule.mem_bot 𝕜).1 <|
      A.essentialSubspace.inf_orthogonal_eq_bot ▸ ⟨hdiff_mem, hdiff_orth⟩
  rw [← hKcoe, SetLike.mem_coe, hpv_eq]
  exact K.starProjection_apply_mem v

/-- The orthogonal projection onto `A.essentialSubspace` can be approximated simultaneously on any
finite family of vectors in `H` by elements of `A`. -/
theorem exists_forall_norm_starProjection_essentialSubspace_sub_apply_lt
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖A.essentialSubspace.starProjection (v i) - a (v i)‖ < ε := by
  classical
  have := Fintype.ofFinite ι
  let φ := (PiLp.diagStarAlgHom 𝕜 H ι).toNonUnitalStarAlgHom
  let w : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 v
  let u : PiLp 2 (fun _ : ι => H) :=
    WithLp.toLp 2 (fun i => A.essentialSubspace.starProjection (v i))
  have horth_iff : ∀ z : PiLp 2 (fun _ : ι => H),
      z ∈ (A.map φ).essentialSubspaceᗮ ↔ ∀ i, z i ∈ A.essentialSubspaceᗮ := by
    intro z
    simp only [mem_orthogonal_essentialSubspace_iff, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    refine ⟨fun hz i a ha => ?_, fun hz a ha => ?_⟩
    · simpa [φ] using congrArg (fun y : PiLp 2 (fun _ : ι => H) => y i) (hz a ha)
    · ext i
      simpa [φ] using hz i a ha
  have hu_mem : u ∈ (A.map φ).essentialSubspace := by
    rw [← (A.map φ).essentialSubspace.orthogonal_orthogonal]
    refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (A.essentialSubspace.mem_orthogonal' (z i)).1 ((horth_iff z).1 hz i) _
      (A.essentialSubspace.starProjection_apply_mem (v i))
  have hsub_orth : w - u ∈ (A.map φ).essentialSubspaceᗮ :=
    (horth_iff _).2 fun i => A.essentialSubspace.sub_starProjection_mem_orthogonal (v i)
  have hproj_w : (A.map φ).essentialSubspace.starProjection w = u := by
    have hw_eq : w = u + (w - u) := (add_sub_cancel _ _).symm
    rw [hw_eq, map_add, (A.map φ).essentialSubspace.starProjection_eq_self_iff.2 hu_mem,
      (A.map φ).essentialSubspace.starProjection_apply_eq_zero_iff.2 hsub_orth, add_zero]
  obtain ⟨_, ⟨T, hT, rfl⟩, hlt⟩ := Metric.mem_closure_iff.1
    (hproj_w ▸ (A.map φ).starProjection_essentialSubspace_apply_mem_closure w) ε hε
  obtain ⟨a, ha, rfl⟩ := mem_map.1 hT
  refine ⟨a, ha, fun i => ?_⟩
  have hlt' : ‖u - PiLp.diagStarAlgHom 𝕜 H ι a w‖ < ε := by
    simpa only [φ, StarAlgHom.coe_toNonUnitalStarAlgHom, dist_eq_norm] using hlt
  calc ‖A.essentialSubspace.starProjection (v i) - a (v i)‖
      = ‖(u - PiLp.diagStarAlgHom 𝕜 H ι a w) i‖ := by simp [u, w]
    _ ≤ ‖u - PiLp.diagStarAlgHom 𝕜 H ι a w‖ := PiLp.norm_apply_le _ _
    _ < ε := hlt'

/-- **The nonunital von Neumann density theorem.** Every operator `x` in `A''` that vanishes on the
common annihilator `A.essentialSubspaceᗮ` is a strong-operator limit of elements of `A`: for every
finite family of vectors `v : ι → H` and every `ε > 0`, some `a ∈ A` satisfies
`‖x (v i) - a (v i)‖ < ε` for all `i`. -/
theorem exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer)
    (hker : ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) : ∃ a ∈ A, ∀ i, ‖x (v i) - a (v i)‖ < ε := by
  have hxS : x ∈ (StarAlgebra.adjoin 𝕜 (A : Set (H →L[𝕜] H)) :
      Set (H →L[𝕜] H)).centralizer.centralizer :=
    Set.centralizer_subset
      (Set.centralizer_subset (StarAlgebra.subset_adjoin 𝕜 (A : Set (H →L[𝕜] H)))) hx
  let u : ι → H := fun i => A.essentialSubspace.starProjection (v i)
  obtain ⟨s, hs, happrox_s⟩ := (StarAlgebra.adjoin 𝕜
      (A : Set (H →L[𝕜] H))).exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    hxS u (half_pos hε)
  have hs_mem : s ∈ Submodule.span 𝕜 {(1 : H →L[𝕜] H)} ⊔ A.toSubmodule := by
    rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]
    exact hs
  obtain ⟨_, h₁, a₁, ha₁, rfl⟩ := Submodule.mem_sup.1 hs_mem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h₁
  have hc_pos : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨a₂, ha₂, happrox_p⟩ :=
    A.exists_forall_norm_starProjection_essentialSubspace_sub_apply_lt v
      (div_pos (half_pos hε) hc_pos)
  refine ⟨c • a₂ + a₁, add_mem (SMulMemClass.smul_mem _ ha₂) ha₁, fun i => ?_⟩
  have hxu : x (v i) = x (u i) := by
    have hdecomp : v i = u i + (v i - u i) := (add_sub_cancel _ _).symm
    conv_lhs => rw [hdecomp, map_add,
      hker _ (A.essentialSubspace.sub_starProjection_mem_orthogonal (v i)), add_zero]
  have ha₁u : a₁ (u i) = a₁ (v i) :=
    congrArg (fun T : H →L[𝕜] H => T (v i)) (A.mul_starProjection_essentialSubspace ha₁)
  have hsplit : x (v i) - (c • a₂ + a₁) (v i) =
      (x (u i) - (c • (1 : H →L[𝕜] H) + a₁) (u i)) + c • (u i - a₂ (v i)) := by
    simp only [hxu, add_apply, smul_apply, one_apply_eq_self, ha₁u, smul_sub]
    abel
  calc ‖x (v i) - (c • a₂ + a₁) (v i)‖
      ≤ ‖x (u i) - (c • (1 : H →L[𝕜] H) + a₁) (u i)‖ + ‖c • (u i - a₂ (v i))‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ < ε / 2 + ‖c‖ * (ε / 2 / (‖c‖ + 1)) := by
        rw [norm_smul]
        exact add_lt_add_of_lt_of_le (happrox_s i)
          (mul_le_mul_of_nonneg_left (happrox_p i).le (norm_nonneg c))
    _ ≤ ε / 2 + (‖c‖ + 1) * (ε / 2 / (‖c‖ + 1)) := by
        gcongr
        linarith
    _ = ε := by
        rw [mul_div_cancel₀ _ hc_pos.ne', add_halves]

/-- **Nonunital von Neumann density for one vector.** If `x ∈ A''` vanishes on the common
annihilator `A.essentialSubspaceᗮ`, then `x v` lies in the closure of the orbit `A v` for every
`v : H`. -/
theorem apply_mem_closure_of_mem_centralizer_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer)
    (hker : ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0) (v : H) :
    x v ∈ closure ((fun a : H →L[𝕜] H => a v) '' A) := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨a, ha, hlt⟩ := A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer hx hker
    (fun _ : Unit => v) hε
  exact ⟨a v, ⟨a, ha, rfl⟩, by simpa only [dist_eq_norm] using hlt ()⟩

/-- When `A.essentialSubspace = ⊤`, every operator in `A''` (including `1`) is a strong-operator
limit of elements of `A`. -/
theorem exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer_of_essentialSubspace_eq_top
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)} (hA : A.essentialSubspace = ⊤) {x : H →L[𝕜] H}
    (hx : x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) : ∃ a ∈ A, ∀ i, ‖x (v i) - a (v i)‖ < ε :=
  A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer hx
    (fun ξ hξ => by
      rw [hA, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hξ
      rw [hξ, map_zero]) v hε

end Density

section Closures

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The set of operators in `A''` vanishing on `A.essentialSubspaceᗮ` is weak-operator closed. -/
private theorem isClosed_image_ofCLM_supported
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0}) := by
  have himg : ContinuousLinearMapWOT.ofCLM ''
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} =
      (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer) ∩
        ⋂ ξ ∈ (A.essentialSubspaceᗮ : Set H), ⋂ ψ : StrongDual 𝕜 H,
          {T : H →WOT[𝕜] H | ψ (T ξ) = 0} := by
    ext T
    obtain ⟨x, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    simp only [Set.mem_inter_iff, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
      Set.mem_iInter, SetLike.mem_coe, Set.mem_ofPred, ContinuousLinearMapWOT.ofCLM_apply]
    exact and_congr_right fun _ => forall₂_congr fun ξ _ =>
      ⟨fun h ψ => by rw [h, map_zero],
        fun h => ext_inner_left 𝕜 fun v => by simpa using h (innerSL 𝕜 v)⟩
  rw [himg]
  exact ((A : Set (H →L[𝕜] H)).centralizer.isClosed_image_ofCLM_centralizer).inter <|
    isClosed_biInter fun ξ _ => isClosed_iInter fun ψ =>
      isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply ξ ψ) continuous_const

/-- **Supported strong-operator closure of a nonunital star subalgebra.** The strong operator
closure of `A` consists of those operators in `A''` that vanish on the common annihilator
`A.essentialSubspaceᗮ`. -/
theorem closure_image_toPointwiseConvergenceCLM (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  let q := ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H
  have hclosed : IsClosed (q '' {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
      ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0}) := by
    convert (isClosed_image_ofCLM_supported A).preimage
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM using 1
    ext T
    simp only [q, Set.mem_image, Set.mem_preimage,
      ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, congrArg ContinuousLinearMapWOT.ofCLM h⟩,
      fun ⟨a, ha, h⟩ => ⟨a, ha, ContinuousLinearMapWOT.ofCLM_injective h⟩⟩
  have hsub : (A : Set (H →L[𝕜] H)) ⊆
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} :=
    fun a ha => ⟨Set.subset_centralizer_centralizer ha, fun _ hξ =>
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha⟩
  refine subset_antisymm (closure_minimal (Set.image_mono hsub) hclosed) ?_
  rintro _ ⟨x, ⟨hx, hker⟩, rfl⟩
  rw [mem_closure_iff_nhds_basis
    ((PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
      (σ := RingHom.id 𝕜) (E := H) Metric.nhds_basis_ball).nhds_of_zero (q x))]
  rintro ⟨F, ε⟩ ⟨hF, hε⟩
  obtain ⟨a, ha, happrox⟩ := A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    hx hker (fun v : F => (v : H)) hε
  refine ⟨q a, ⟨a, ha, rfl⟩, fun v hv => ?_⟩
  rw [Metric.mem_ball, dist_zero_right, _root_.sub_apply, norm_sub_rev]
  exact happrox ⟨v, hv⟩

/-- **Supported weak-operator closure of a nonunital star subalgebra.** The weak operator closure
of `A` consists of those operators in `A''` that vanish on the common annihilator
`A.essentialSubspaceᗮ`. -/
theorem closure_image_ofCLM (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  have hsub : (A : Set (H →L[𝕜] H)) ⊆
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} :=
    fun a ha => ⟨Set.subset_centralizer_centralizer ha, fun _ hξ =>
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono hsub) (isClosed_image_ofCLM_supported A)) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) := by
    rw [A.closure_image_toPointwiseConvergenceCLM]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hx'

/-- The strong operator closure of `A` on `H` is the zero extension from `A.essentialSubspace` of
the unital double commutant `(A.restrictEssentialSubspace)''`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A.essentialSubspace.extendByZero ''
          (A.restrictEssentialSubspace : Set _).centralizer.centralizer) := by
  rw [A.closure_image_toPointwiseConvergenceCLM, A.image_extendByZero_centralizer_centralizer]

/-- The weak operator closure of `A` on `H` is the zero extension from `A.essentialSubspace` of
the unital double commutant `(A.restrictEssentialSubspace)''`. -/
theorem closure_image_ofCLM_eq_image_extendByZero (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.essentialSubspace.extendByZero ''
          (A.restrictEssentialSubspace : Set _).centralizer.centralizer) := by
  rw [A.closure_image_ofCLM, A.image_extendByZero_centralizer_centralizer]

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the strong operator closure of
`A`. -/
theorem toPointwiseConvergenceCLM_starProjection_essentialSubspace_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H
        A.essentialSubspace.starProjection ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) := by
  rw [A.closure_image_toPointwiseConvergenceCLM]
  exact ⟨A.essentialSubspace.starProjection,
    ⟨A.starProjection_essentialSubspace_mem_centralizer_centralizer, fun _ hξ =>
      A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ⟩, rfl⟩

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the weak operator closure of
`A`. -/
theorem ofCLM_starProjection_essentialSubspace_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMapWOT.ofCLM A.essentialSubspace.starProjection ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) := by
  rw [A.closure_image_ofCLM]
  exact ⟨A.essentialSubspace.starProjection,
    ⟨A.starProjection_essentialSubspace_mem_centralizer_centralizer, fun _ hξ =>
      A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ⟩, rfl⟩

/-- For a nondegenerate nonunital star subalgebra (`A.essentialSubspace = ⊤`), its strong operator
closure is its unital double commutant `A''`. -/
theorem closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)} (hA : A.essentialSubspace = ⊤) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H)).centralizer.centralizer := by
  rw [A.closure_image_toPointwiseConvergenceCLM, hA, Submodule.top_orthogonal_eq_bot]
  congr 1
  ext x
  simp

/-- For a nondegenerate nonunital star subalgebra (`A.essentialSubspace = ⊤`), its weak operator
closure is its unital double commutant `A''`. -/
theorem closure_image_ofCLM_of_essentialSubspace_eq_top
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)} (hA : A.essentialSubspace = ⊤) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer := by
  rw [A.closure_image_ofCLM, hA, Submodule.top_orthogonal_eq_bot]
  congr 1
  ext x
  simp

/-- **Unitality on the essential subspace (strong operator topology).** The strong operator closure
of `A.restrictEssentialSubspace` on `A.essentialSubspace` is its unital double commutant
`(A.restrictEssentialSubspace)''`, which contains `1 : A.essentialSubspace →L[𝕜]
A.essentialSubspace`. -/
theorem closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜)
      A.essentialSubspace A.essentialSubspace ''
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[𝕜] A.essentialSubspace))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜)
        A.essentialSubspace A.essentialSubspace ''
        (A.restrictEssentialSubspace :
          Set (A.essentialSubspace →L[𝕜] A.essentialSubspace)).centralizer.centralizer :=
  closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top
    A.essentialSubspace_restrictEssentialSubspace

/-- **Unitality on the essential subspace (weak operator topology).** The weak operator closure of
`A.restrictEssentialSubspace` on `A.essentialSubspace` is its unital double commutant
`(A.restrictEssentialSubspace)''`, which contains `1 : A.essentialSubspace →L[𝕜]
A.essentialSubspace`. -/
theorem closure_image_ofCLM_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM ''
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[𝕜] A.essentialSubspace))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.restrictEssentialSubspace :
          Set (A.essentialSubspace →L[𝕜] A.essentialSubspace)).centralizer.centralizer :=
  closure_image_ofCLM_of_essentialSubspace_eq_top A.essentialSubspace_restrictEssentialSubspace

/-- The ambient identity operator `1 : H →L[𝕜] H` lies in the weak operator closure of `A` if and
only if `A.essentialSubspace = ⊤`. -/
theorem one_mem_closure_image_ofCLM_iff (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMapWOT.ofCLM (1 : H →L[𝕜] H) ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      A.essentialSubspace = ⊤ := by
  rw [A.closure_image_ofCLM, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image, Set.mem_sep_iff]
  have h1 : (1 : H →L[𝕜] H) ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
    (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).one_mem
  simp only [h1, true_and, one_apply_eq_self, ← Submodule.eq_bot_iff,
    Submodule.orthogonal_eq_bot_iff]

/-- The ambient identity operator `1 : H →L[𝕜] H` lies in the strong operator closure of `A` if and
only if `A.essentialSubspace = ⊤`. -/
theorem one_mem_closure_image_toPointwiseConvergenceCLM_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H (1 : H →L[𝕜] H) ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) ↔
      A.essentialSubspace = ⊤ := by
  rw [A.closure_image_toPointwiseConvergenceCLM,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image, Set.mem_sep_iff]
  have h1 : (1 : H →L[𝕜] H) ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
    (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).one_mem
  simp only [h1, true_and, one_apply_eq_self, ← Submodule.eq_bot_iff,
    Submodule.orthogonal_eq_bot_iff]

/-- The weak operator closure of `A` equals the full double commutant `A''` on `H` if and only if
`A.essentialSubspace = ⊤`; otherwise `A''` strictly enlarges the closure by adjoining scalars on
the common annihilator. -/
theorem closure_image_ofCLM_eq_centralizer_centralizer_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      A.essentialSubspace = ⊤ := by
  refine ⟨fun h => A.one_mem_closure_image_ofCLM_iff.1 ?_,
    A.closure_image_ofCLM_of_essentialSubspace_eq_top⟩
  rw [h]
  exact ⟨1, (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).one_mem, rfl⟩

/-- The strong operator closure of `A` equals the full double commutant `A''` on `H` if and only if
`A.essentialSubspace = ⊤`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_centralizer_centralizer_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      A.essentialSubspace = ⊤ := by
  refine ⟨fun h => A.one_mem_closure_image_toPointwiseConvergenceCLM_iff.1 ?_,
    A.closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top⟩
  rw [h]
  exact ⟨1, (Subalgebra.centralizer 𝕜 (A : Set (H →L[𝕜] H)).centralizer).one_mem, rfl⟩

/-- **Supported bicommutant criterion (weak operator topology).** A nonunital star subalgebra `A`
is weak operator closed if and only if it equals the set of operators in `A''` vanishing on
`A.essentialSubspaceᗮ`. -/
theorem isClosed_image_ofCLM_iff (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      (A : Set (H →L[𝕜] H)) =
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  rw [← closure_eq_iff_isClosed, A.closure_image_ofCLM,
    (Set.image_injective.2 ContinuousLinearMapWOT.ofCLM_injective).eq_iff, eq_comm]

/-- **Supported bicommutant criterion (strong operator topology).** A nonunital star subalgebra `A`
is strong operator closed if and only if it equals the set of operators in `A''` vanishing on
`A.essentialSubspaceᗮ`. -/
theorem isClosed_image_toPointwiseConvergenceCLM_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) ↔
      (A : Set (H →L[𝕜] H)) =
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  rw [← closure_eq_iff_isClosed, A.closure_image_toPointwiseConvergenceCLM,
    (Set.image_injective.2 ContinuousLinearMap.toPointwiseConvergenceCLM_injective).eq_iff,
    eq_comm]

/-- A nonunital star subalgebra of bounded operators on `H` is weak operator closed if and only if
it is strong operator closed. -/
theorem isClosed_image_ofCLM_iff_isClosed_image_toPointwiseConvergenceCLM
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) :=
  A.isClosed_image_ofCLM_iff.trans A.isClosed_image_toPointwiseConvergenceCLM_iff.symm

/-- Any weak-operator closed nonunital star subalgebra contains the orthogonal projection onto its
essential subspace. -/
theorem starProjection_essentialSubspace_mem_of_isClosed_image_ofCLM
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}
    (hA : IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)))) :
    A.essentialSubspace.starProjection ∈ A := by
  have hmem := hA.closure_eq ▸ A.ofCLM_starProjection_essentialSubspace_mem_closure
  exact ContinuousLinearMapWOT.ofCLM_injective.mem_set_image.1 hmem

/-- Any strong-operator closed nonunital star subalgebra contains the orthogonal projection onto
its essential subspace. -/
theorem starProjection_essentialSubspace_mem_of_isClosed_image_toPointwiseConvergenceCLM
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}
    (hA : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H)))) :
    A.essentialSubspace.starProjection ∈ A := by
  have hmem := hA.closure_eq ▸
    A.toPointwiseConvergenceCLM_starProjection_essentialSubspace_mem_closure
  exact ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image.1 hmem

/-- For any complete subspace `U` of `H`, the full supported algebra
`NonUnitalStarAlgHom.range U.extendByZero` is weak operator closed on `H`. -/
theorem isClosed_image_ofCLM_range_extendByZero (U : Submodule 𝕜 H) [CompleteSpace U] :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      (NonUnitalStarAlgHom.range U.extendByZero : Set (H →L[𝕜] H))) := by
  let A := NonUnitalStarAlgHom.range U.extendByZero
  refine A.isClosed_image_ofCLM_iff.2 (subset_antisymm ?_ ?_)
  · intro a ha
    refine ⟨Set.subset_centralizer_centralizer ha, fun _ hξ =>
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha⟩
  · rintro x ⟨hx, hker⟩
    rw [essentialSubspace_range_extendByZero] at hker
    have hx_comm : Commute U.starProjection x := by
      have hp_cent : U.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer := by
        simpa [A, essentialSubspace_range_extendByZero] using
          A.starProjection_essentialSubspace_mem_centralizer
      exact hx _ hp_cent
    have hrange : ∀ ξ, x ξ ∈ U := fun ξ => by
      have hcomm := congrArg (fun T : H →L[𝕜] H => T ξ) hx_comm.eq
      rw [_root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp] at hcomm
      have hdecomp : ξ = U.starProjection ξ + (ξ - U.starProjection ξ) := (add_sub_cancel _ _).symm
      have hxproj : x (U.starProjection ξ) = x ξ := by
        conv_rhs => rw [hdecomp, map_add, hker _ (U.sub_starProjection_mem_orthogonal ξ), add_zero]
      rw [hxproj] at hcomm
      exact hcomm ▸ U.starProjection_apply_mem (x ξ)
    exact U.mem_range_extendByZero_iff.2 ⟨hrange, hker⟩

/-- For any complete subspace `U` of `H`, the full supported algebra
`NonUnitalStarAlgHom.range U.extendByZero` is strong operator closed on `H`. -/
theorem isClosed_image_toPointwiseConvergenceCLM_range_extendByZero
    (U : Submodule 𝕜 H) [CompleteSpace U] :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (NonUnitalStarAlgHom.range U.extendByZero : Set (H →L[𝕜] H))) :=
  (NonUnitalStarAlgHom.range
    U.extendByZero).isClosed_image_ofCLM_iff_isClosed_image_toPointwiseConvergenceCLM.1
    (isClosed_image_ofCLM_range_extendByZero U)

end Closures

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **essential von Neumann algebra** of a nonunital star subalgebra `A` on a complex Hilbert
space `H`: the von Neumann algebra on `A.essentialSubspace` generated by
`A.restrictEssentialSubspace`, whose underlying operators are the strong and weak operator closures
of `A.restrictEssentialSubspace`. -/
def essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    VonNeumannAlgebra A.essentialSubspace :=
  VonNeumannAlgebra.adjoin
    (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))

/-- Unfolding formula for `NonUnitalStarSubalgebra.essentialVonNeumannAlgebra`. -/
theorem essentialVonNeumannAlgebra_def (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    A.essentialVonNeumannAlgebra =
      VonNeumannAlgebra.adjoin
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) :=
  (rfl)

/-- The underlying set of `A.essentialVonNeumannAlgebra` is `(A.restrictEssentialSubspace)''`. -/
@[simp]
theorem coe_essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      (A.restrictEssentialSubspace :
        Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)).centralizer.centralizer :=
  VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset

/-- An operator on `A.essentialSubspace` belongs to `A.essentialVonNeumannAlgebra` if and only if
its extension by zero on `A.essentialSubspaceᗮ` belongs to `VonNeumannAlgebra.adjoin A`. -/
theorem mem_essentialVonNeumannAlgebra {A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {S : A.essentialSubspace →L[ℂ] A.essentialSubspace} :
    S ∈ A.essentialVonNeumannAlgebra ↔
      A.essentialSubspace.extendByZero S ∈ VonNeumannAlgebra.adjoin (A : Set (H →L[ℂ] H)) := by
  rw [← SetLike.mem_coe, coe_essentialVonNeumannAlgebra, ← SetLike.mem_coe,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset,
    A.extendByZero_mem_centralizer_centralizer_iff]

/-- `A.essentialVonNeumannAlgebra` is the weak operator closure of `A.restrictEssentialSubspace` on
`A.essentialSubspace`. -/
theorem image_ofCLM_essentialVonNeumannAlgebra_eq_closure
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    ContinuousLinearMapWOT.ofCLM ''
      (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      closure (ContinuousLinearMapWOT.ofCLM ''
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [coe_essentialVonNeumannAlgebra, A.closure_image_ofCLM_restrictEssentialSubspace]

/-- `A.essentialVonNeumannAlgebra` is the strong operator closure of `A.restrictEssentialSubspace`
on `A.essentialSubspace`. -/
theorem image_toPointwiseConvergenceCLM_essentialVonNeumannAlgebra_eq_closure
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        A.essentialSubspace A.essentialSubspace ''
      (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        A.essentialSubspace A.essentialSubspace ''
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [coe_essentialVonNeumannAlgebra,
    A.closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace]

/-- On `H`, the weak operator closure of `A` is `A.essentialVonNeumannAlgebra` extended by zero on
the common annihilator `A.essentialSubspaceᗮ`. -/
theorem closure_image_ofCLM_eq_image_extendByZero_essentialVonNeumannAlgebra
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[ℂ] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.essentialSubspace.extendByZero ''
          (A.essentialVonNeumannAlgebra :
            Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [A.closure_image_ofCLM_eq_image_extendByZero, coe_essentialVonNeumannAlgebra]

/-- On `H`, the strong operator closure of `A` is `A.essentialVonNeumannAlgebra` extended by zero
on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero_essentialVonNeumannAlgebra
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (A : Set (H →L[ℂ] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (A.essentialSubspace.extendByZero ''
          (A.essentialVonNeumannAlgebra :
            Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [A.closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero,
    coe_essentialVonNeumannAlgebra]

/-- The unital von Neumann algebra `VonNeumannAlgebra.adjoin A` on `H` splits as the supported
closure `A.essentialSubspace.extendByZero '' A.essentialVonNeumannAlgebra` plus complex scalar
multiples of the identity on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem coe_adjoin_eq (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (VonNeumannAlgebra.adjoin (A : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      {x | ∃ S ∈ A.essentialVonNeumannAlgebra, ∃ c : ℂ,
        x = A.essentialSubspace.extendByZero S + c • A.essentialSubspaceᗮ.starProjection} := by
  rw [VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]
  ext x
  simp only [A.mem_centralizer_centralizer_iff, ← SetLike.mem_coe, coe_essentialVonNeumannAlgebra,
    Set.mem_ofPred]

end Complex

end NonUnitalStarSubalgebra
