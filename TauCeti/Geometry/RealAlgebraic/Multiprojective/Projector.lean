/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic
public import TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding

/-!
# The product projector embedding of multiprojective space

Factorwise application of the rank-one projector map `Projectivization.projector` embeds a product
of projective spaces `∀ i : ι, ℙ K (α i → K)` into the space of matrix tuples
`∀ i : ι, Matrix (α i) (α i) K`, and—after flattening matrix entries via
`TauCeti.multiprojectiveMatrixCoordEquiv`—into the affine coordinate space
`(Σ i : ι, α i × α i) → K`. Over an ordered field its image is the *product projector locus*
`TauCeti.multiprojectiveProjectorLocus α K` (`TauCeti.multiprojectiveProjectorCoordLocus α K` in
flattened coordinates), where each factor is symmetric, idempotent, and of trace one.

This file develops the algebraic, topological, semialgebraic, and Nash properties of the product
projector embedding and connects them to the multiprojective and mixed semialgebraic theory in
`TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic`, `Map`, and `Nash`:

* Over `ℝ`, `TauCeti.multiprojectiveProjector` and `TauCeti.multiprojectiveProjectorCoord` are
  closed embeddings onto compact real algebraic loci, yielding the homeomorphisms
  `TauCeti.multiprojectiveProjectorHomeomorph` and
  `TauCeti.multiprojectiveProjectorCoordHomeomorph`. Relative complements in multiprojective space
  transport to relative complements inside the product projector locus
  (`TauCeti.image_multiprojectiveProjector_compl`,
  `TauCeti.image_multiprojectiveProjectorCoord_compl`).
* Over any strict ordered field and finite factor index `ι`, the relation
  `{(a, p) | multiprojectiveProjectorCoord p = a}` is mixed semialgebraic without assuming
  projection closure (`TauCeti.isMixedSemialgebraic_multiprojectiveProjectorCoord_rel`), and the
  standard product affine charts and their inverses are semialgebraic in the matrix-entry model.
* Over an ordered field with semialgebraic projections (such as `ℝ`), a subset `S` of
  multiprojective space is multiprojective semialgebraic if and only if its embedded image
  `multiprojectiveProjectorCoord '' S` is semialgebraic in affine matrix coordinates
  (`TauCeti.isSemialgebraic_image_multiprojectiveProjectorCoord_iff`), and a map
  `τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)` from an affine space has mixed semialgebraic graph
  over `s` if and only if `multiprojectiveProjectorCoord ∘ τ` is `TauCeti.IsSemialgebraicOn` on `s`
  (`TauCeti.isMixedSemialgebraic_graphOn_iff_isSemialgebraicOn_multiprojectiveProjectorCoord_comp`).
* Over `ℝ`, both the chart-to-projector entries and the projector-to-chart ratio coordinates are
  Nash germs (`TauCeti.isNashAt_multiprojectiveProjectorCoord_affineChart_symm`,
  `TauCeti.isNashAt_multiprojectiveAffineChart_projectorCoord`).

## Main definitions

* `TauCeti.multiprojectiveMatrixCoordEquiv`, `TauCeti.multiprojectiveMatrixCoordLinearEquiv`,
  `TauCeti.multiprojectiveMatrixCoordHomeomorph`: flattening `∀ i, Matrix (α i) (α i) K` to the
  entry coordinate space `(Σ i, α i × α i) → K`.
* `TauCeti.multiprojectiveProjector`, `TauCeti.multiprojectiveProjectorCoord`: the product
  rank-one projector map and its flattened coordinate form.
* `TauCeti.multiprojectiveProjectorLocus`, `TauCeti.multiprojectiveProjectorCoordLocus`: the
  product projector locus in matrix tuples and in flattened matrix coordinates.
* `TauCeti.multiprojectiveProjectorHomeomorph`, `TauCeti.multiprojectiveProjectorCoordHomeomorph`:
  over `ℝ`, the homeomorphisms from multiprojective space onto the product projector locus.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix MvPolynomial Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Flattened matrix-entry coordinates -/

section MatrixCoord

variable {ι : Type*} {α : ι → Type*} {K : Type*}

/-- Equivalence flattening a tuple of square matrices `∀ i, Matrix (α i) (α i) K` to the single
entry-coordinate function space `(Σ i, α i × α i) → K`. -/
def multiprojectiveMatrixCoordEquiv (α : ι → Type*) (K : Type*) :
    (∀ i, Matrix (α i) (α i) K) ≃ ((Σ i, α i × α i) → K) where
  toFun A q := A q.1 q.2.1 q.2.2
  invFun a i := Matrix.of fun j k ↦ a ⟨i, j, k⟩
  left_inv _ := funext fun _ ↦ Matrix.ext fun _ _ ↦ rfl
  right_inv _ := funext fun ⟨_, _, _⟩ ↦ rfl

@[simp]
theorem multiprojectiveMatrixCoordEquiv_apply (A : ∀ i, Matrix (α i) (α i) K)
    (q : Σ i, α i × α i) :
    multiprojectiveMatrixCoordEquiv α K A q = A q.1 q.2.1 q.2.2 :=
  (rfl)

@[simp]
theorem multiprojectiveMatrixCoordEquiv_symm_apply (a : (Σ i, α i × α i) → K)
    (i : ι) (j k : α i) :
    (multiprojectiveMatrixCoordEquiv α K).symm a i j k = a ⟨i, j, k⟩ :=
  (rfl)

/-- Linear equivalence refinement of `TauCeti.multiprojectiveMatrixCoordEquiv`. -/
def multiprojectiveMatrixCoordLinearEquiv (α : ι → Type*) (K : Type*) [Semiring K] :
    (∀ i, Matrix (α i) (α i) K) ≃ₗ[K] ((Σ i, α i × α i) → K) where
  toEquiv := multiprojectiveMatrixCoordEquiv α K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem multiprojectiveMatrixCoordLinearEquiv_toEquiv [Semiring K] :
    (multiprojectiveMatrixCoordLinearEquiv α K).toEquiv = multiprojectiveMatrixCoordEquiv α K :=
  (rfl)

@[simp]
theorem multiprojectiveMatrixCoordLinearEquiv_apply [Semiring K]
    (A : ∀ i, Matrix (α i) (α i) K) (q : Σ i, α i × α i) :
    multiprojectiveMatrixCoordLinearEquiv α K A q = A q.1 q.2.1 q.2.2 :=
  (rfl)

@[simp]
theorem multiprojectiveMatrixCoordLinearEquiv_symm_apply [Semiring K]
    (a : (Σ i, α i × α i) → K) (i : ι) (j k : α i) :
    (multiprojectiveMatrixCoordLinearEquiv α K).symm a i j k = a ⟨i, j, k⟩ :=
  (rfl)

/-- Homeomorphism refinement of `TauCeti.multiprojectiveMatrixCoordEquiv`. -/
def multiprojectiveMatrixCoordHomeomorph (α : ι → Type*) (K : Type*) [TopologicalSpace K] :
    (∀ i, Matrix (α i) (α i) K) ≃ₜ ((Σ i, α i × α i) → K) where
  toEquiv := multiprojectiveMatrixCoordEquiv α K
  continuous_toFun := continuous_pi fun q ↦ (continuous_apply q.1).matrix_elem q.2.1 q.2.2
  continuous_invFun := continuous_pi fun i ↦ continuous_matrix fun j k ↦
    continuous_apply (⟨i, j, k⟩ : Σ i, α i × α i)

@[simp]
theorem multiprojectiveMatrixCoordHomeomorph_toEquiv [TopologicalSpace K] :
    (multiprojectiveMatrixCoordHomeomorph α K).toEquiv = multiprojectiveMatrixCoordEquiv α K :=
  (rfl)

@[simp]
theorem coe_multiprojectiveMatrixCoordHomeomorph [TopologicalSpace K] :
    ⇑(multiprojectiveMatrixCoordHomeomorph α K) = multiprojectiveMatrixCoordEquiv α K :=
  (rfl)

@[simp]
theorem coe_multiprojectiveMatrixCoordHomeomorph_symm [TopologicalSpace K] :
    ⇑(multiprojectiveMatrixCoordHomeomorph α K).symm =
      (multiprojectiveMatrixCoordEquiv α K).symm :=
  (rfl)

end MatrixCoord

/-! ### Product projector map and product projector locus -/

section Projector

variable {ι : Type*} {α : ι → Type*} {K : Type*} [∀ i, Fintype (α i)] [Field K]

/-- Factorwise rank-one projector map on a product of projective spaces
`∀ i, ℙ K (α i → K) → ∀ i, Matrix (α i) (α i) K`. -/
def multiprojectiveProjector (p : ∀ i, ℙ K (α i → K)) : ∀ i, Matrix (α i) (α i) K :=
  fun i ↦ Projectivization.projector (p i)

@[simp]
theorem multiprojectiveProjector_apply (p : ∀ i, ℙ K (α i → K)) (i : ι) :
    multiprojectiveProjector p i = Projectivization.projector (p i) :=
  (rfl)

/-- The product rank-one projector map read in flattened matrix-entry coordinates
`(Σ i, α i × α i) → K`. -/
def multiprojectiveProjectorCoord (p : ∀ i, ℙ K (α i → K)) : (Σ i, α i × α i) → K :=
  multiprojectiveMatrixCoordEquiv α K (multiprojectiveProjector p)

theorem multiprojectiveProjectorCoord_def (p : ∀ i, ℙ K (α i → K)) :
    multiprojectiveProjectorCoord p =
      multiprojectiveMatrixCoordEquiv α K (multiprojectiveProjector p) :=
  (rfl)

@[simp]
theorem multiprojectiveProjectorCoord_apply (p : ∀ i, ℙ K (α i → K)) (q : Σ i, α i × α i) :
    multiprojectiveProjectorCoord p q = Projectivization.projector (p q.1) q.2.1 q.2.2 :=
  (rfl)

/-- The *product projector locus*: tuples of matrices each of which is symmetric, idempotent, and
of trace one (`TauCeti.projectorLocus`). -/
def multiprojectiveProjectorLocus (α : ι → Type*) (K : Type*) [∀ i, Fintype (α i)] [Field K] :
    Set (∀ i, Matrix (α i) (α i) K) :=
  {A | ∀ i, A i ∈ projectorLocus (α i) K}

@[simp]
theorem mem_multiprojectiveProjectorLocus {A : ∀ i, Matrix (α i) (α i) K} :
    A ∈ multiprojectiveProjectorLocus α K ↔ ∀ i, A i ∈ projectorLocus (α i) K :=
  Iff.rfl

/-- `TauCeti.multiprojectiveProjectorLocus` as `Set.pi` over `Set.univ`. -/
theorem multiprojectiveProjectorLocus_eq_univ_pi :
    multiprojectiveProjectorLocus α K = univ.pi fun i ↦ projectorLocus (α i) K := by
  ext A
  simp

/-- The product projector locus in flattened matrix-entry coordinates `(Σ i, α i × α i) → K`. -/
def multiprojectiveProjectorCoordLocus (α : ι → Type*) (K : Type*) [∀ i, Fintype (α i)]
    [Field K] : Set ((Σ i, α i × α i) → K) :=
  multiprojectiveMatrixCoordEquiv α K '' multiprojectiveProjectorLocus α K

@[simp]
theorem mem_multiprojectiveProjectorCoordLocus {a : (Σ i, α i × α i) → K} :
    a ∈ multiprojectiveProjectorCoordLocus α K ↔
      ∀ i, Matrix.of (fun j k ↦ a ⟨i, j, k⟩) ∈ projectorLocus (α i) K := by
  constructor
  · rintro ⟨A, hA, rfl⟩ i
    exact hA i
  · intro ha
    exact ⟨(multiprojectiveMatrixCoordEquiv α K).symm a, ha,
      (multiprojectiveMatrixCoordEquiv α K).apply_symm_apply a⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field, the product projector of every point lies in the product projector
locus. -/
theorem multiprojectiveProjector_mem_locus (p : ∀ i, ℙ K (α i → K)) :
    multiprojectiveProjector p ∈ multiprojectiveProjectorLocus α K :=
  fun i ↦ Projectivization.projector_mem_projectorLocus (p i)

/-- Over an ordered field, the flattened product projector of every point lies in
`TauCeti.multiprojectiveProjectorCoordLocus`. -/
theorem multiprojectiveProjectorCoord_mem_locus (p : ∀ i, ℙ K (α i → K)) :
    multiprojectiveProjectorCoord p ∈ multiprojectiveProjectorCoordLocus α K :=
  ⟨multiprojectiveProjector p, multiprojectiveProjector_mem_locus p, rfl⟩

/-- Over an ordered field, the product projector map is injective. -/
theorem multiprojectiveProjector_injective :
    Function.Injective
      (multiprojectiveProjector : (∀ i, ℙ K (α i → K)) → ∀ i, Matrix (α i) (α i) K) :=
  fun _ _ h ↦ funext fun i ↦ Projectivization.projector_injective (congrFun h i)

/-- Over an ordered field, the flattened product projector map is injective. -/
theorem multiprojectiveProjectorCoord_injective :
    Function.Injective
      (multiprojectiveProjectorCoord : (∀ i, ℙ K (α i → K)) → (Σ i, α i × α i) → K) :=
  (multiprojectiveMatrixCoordEquiv α K).injective.comp multiprojectiveProjector_injective

/-- Over an ordered field, the range of `TauCeti.multiprojectiveProjector` is the product projector
locus. -/
theorem range_multiprojectiveProjector :
    range (multiprojectiveProjector : (∀ i, ℙ K (α i → K)) → ∀ i, Matrix (α i) (α i) K) =
      multiprojectiveProjectorLocus α K := by
  refine Subset.antisymm (range_subset_iff.2 multiprojectiveProjector_mem_locus) fun A hA ↦ ?_
  choose p hp using fun i ↦ Projectivization.range_projector.symm.subset (hA i)
  exact ⟨p, funext hp⟩

/-- Over an ordered field, the range of `TauCeti.multiprojectiveProjectorCoord` is
`TauCeti.multiprojectiveProjectorCoordLocus`. -/
theorem range_multiprojectiveProjectorCoord :
    range (multiprojectiveProjectorCoord : (∀ i, ℙ K (α i → K)) → (Σ i, α i × α i) → K) =
      multiprojectiveProjectorCoordLocus α K := by
  have hcomp : (multiprojectiveProjectorCoord : (∀ i, ℙ K (α i → K)) → (Σ i, α i × α i) → K) =
      multiprojectiveMatrixCoordEquiv α K ∘ multiprojectiveProjector := rfl
  rw [hcomp, range_comp, range_multiprojectiveProjector]
  rfl

/-- Relative complements in multiprojective space transport under `TauCeti.multiprojectiveProjector`
to relative complements inside `TauCeti.multiprojectiveProjectorLocus`. -/
theorem image_multiprojectiveProjector_compl (S : Set (∀ i, ℙ K (α i → K))) :
    multiprojectiveProjector '' Sᶜ =
      multiprojectiveProjectorLocus α K \ (multiprojectiveProjector '' S) := by
  rw [← range_multiprojectiveProjector, ← image_univ,
    ← image_sdiff multiprojectiveProjector_injective, compl_eq_univ_sdiff]

/-- Relative complements in multiprojective space transport under
`TauCeti.multiprojectiveProjectorCoord` to relative complements inside
`TauCeti.multiprojectiveProjectorCoordLocus`. -/
theorem image_multiprojectiveProjectorCoord_compl (S : Set (∀ i, ℙ K (α i → K))) :
    multiprojectiveProjectorCoord '' Sᶜ =
      multiprojectiveProjectorCoordLocus α K \ (multiprojectiveProjectorCoord '' S) := by
  rw [← range_multiprojectiveProjectorCoord, ← image_univ,
    ← image_sdiff multiprojectiveProjectorCoord_injective, compl_eq_univ_sdiff]

/-- Over an ordered field, `TauCeti.multiprojectiveProjector` maps a standard product affine open
`multiprojectiveAffineOpen I` onto the matrices of the product projector locus whose `(I i, I i)`
diagonal entry is nonzero for every `i`. -/
theorem image_multiprojectiveProjector_affineOpen {n : ι → ℕ} (I : ∀ i, Fin (n i + 1)) :
    multiprojectiveProjector '' multiprojectiveAffineOpen (K := K) I =
      multiprojectiveProjectorLocus (fun i ↦ Fin (n i + 1)) K ∩
        {A | ∀ i, A i (I i) (I i) ≠ 0} := by
  ext A
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨multiprojectiveProjector_mem_locus p, fun i h0 ↦
      Projectivization.projector_apply_self_eq_zero_iff.1 h0
        (mem_multiprojectiveAffineOpen.1 hp i)⟩
  · rintro ⟨hA, hAI⟩
    obtain ⟨p, rfl⟩ := range_multiprojectiveProjector.symm.subset hA
    exact ⟨p, mem_multiprojectiveAffineOpen.2 fun i ↦
      not_not.1 (mt Projectivization.projector_apply_self_eq_zero_iff.2 (hAI i)), rfl⟩

/-- Flattened coordinate form of `TauCeti.image_multiprojectiveProjector_affineOpen`. -/
theorem image_multiprojectiveProjectorCoord_affineOpen {n : ι → ℕ} (I : ∀ i, Fin (n i + 1)) :
    multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I =
      multiprojectiveProjectorCoordLocus (fun i ↦ Fin (n i + 1)) K ∩
        {a | ∀ i, a ⟨i, I i, I i⟩ ≠ 0} := by
  have hcomp : (multiprojectiveProjectorCoord :
      (∀ i, ℙ K (Fin (n i + 1) → K)) → (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K) =
      multiprojectiveMatrixCoordEquiv (fun i ↦ Fin (n i + 1)) K ∘ multiprojectiveProjector := rfl
  rw [hcomp, image_comp, image_multiprojectiveProjector_affineOpen]
  ext a
  constructor
  · rintro ⟨A, ⟨hA, hAI⟩, rfl⟩
    exact ⟨⟨A, hA, rfl⟩, hAI⟩
  · rintro ⟨⟨A, hA, rfl⟩, hAI⟩
    exact ⟨A, ⟨hA, hAI⟩, rfl⟩

/-- Over an ordered field, the standard product affine chart at `I` reads the coordinates of `p`
off its product projector as column ratios `A i ((I i).succAbove k) (I i) / A i (I i) (I i)`. -/
theorem multiprojectiveAffineChart_eq_multiprojectiveProjector_div {n : ι → ℕ}
    (I : ∀ i, Fin (n i + 1)) (p : ∀ i, ℙ K (Fin (n i + 1) → K)) :
    multiprojectiveAffineChart I p = fun q ↦
      multiprojectiveProjector p q.1 ((I q.1).succAbove q.2) (I q.1) /
        multiprojectiveProjector p q.1 (I q.1) (I q.1) := by
  funext q
  rw [multiprojectiveAffineChart_apply, Projectivization.affineChart_eq_projector_div]
  rfl

end Projector

/-! ### Topological and compactness properties -/

section Topology

variable {ι : Type*} {α : ι → Type*} {K : Type*} [∀ i, Fintype (α i)] [Field K]

/-- The product projector map is continuous for the product of quotient topologies. -/
theorem continuous_multiprojectiveProjector [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] :
    Continuous (multiprojectiveProjector : (∀ i, ℙ K (α i → K)) → ∀ i, Matrix (α i) (α i) K) :=
  continuous_pi fun i ↦ Projectivization.continuous_projector.comp (continuous_apply i)

/-- The flattened product projector map is continuous. -/
theorem continuous_multiprojectiveProjectorCoord [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] :
    Continuous (multiprojectiveProjectorCoord : (∀ i, ℙ K (α i → K)) → (Σ i, α i × α i) → K) :=
  (multiprojectiveMatrixCoordHomeomorph α K).continuous.comp continuous_multiprojectiveProjector

/-- The product projector locus is closed in `∀ i, Matrix (α i) (α i) K`. -/
theorem isClosed_multiprojectiveProjectorLocus [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] :
    IsClosed (multiprojectiveProjectorLocus α K) := by
  rw [multiprojectiveProjectorLocus_eq_univ_pi]
  exact isClosed_set_pi fun _ _ ↦ isClosed_projectorLocus

/-- The flattened product projector locus is closed in `(Σ i, α i × α i) → K`. -/
theorem isClosed_multiprojectiveProjectorCoordLocus [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] :
    IsClosed (multiprojectiveProjectorCoordLocus α K) :=
  (multiprojectiveMatrixCoordHomeomorph α K).isClosed_image.2 isClosed_multiprojectiveProjectorLocus

/-- Over `ℝ`, `TauCeti.multiprojectiveProjector` is a closed embedding. -/
theorem isClosedEmbedding_multiprojectiveProjector :
    IsClosedEmbedding
      (multiprojectiveProjector : (∀ i, ℙ ℝ (α i → ℝ)) → ∀ i, Matrix (α i) (α i) ℝ) :=
  continuous_multiprojectiveProjector.isClosedEmbedding multiprojectiveProjector_injective

/-- Over `ℝ`, `TauCeti.multiprojectiveProjectorCoord` is a closed embedding. -/
theorem isClosedEmbedding_multiprojectiveProjectorCoord :
    IsClosedEmbedding
      (multiprojectiveProjectorCoord : (∀ i, ℙ ℝ (α i → ℝ)) → (Σ i, α i × α i) → ℝ) :=
  (multiprojectiveMatrixCoordHomeomorph α ℝ).isClosedEmbedding.comp
    isClosedEmbedding_multiprojectiveProjector

/-- Over `ℝ`, the product projector locus is compact. -/
theorem isCompact_multiprojectiveProjectorLocus :
    IsCompact (multiprojectiveProjectorLocus α ℝ) :=
  range_multiprojectiveProjector (α := α) (K := ℝ) ▸
    isCompact_range continuous_multiprojectiveProjector

/-- Over `ℝ`, the flattened product projector locus is compact. -/
theorem isCompact_multiprojectiveProjectorCoordLocus :
    IsCompact (multiprojectiveProjectorCoordLocus α ℝ) :=
  range_multiprojectiveProjectorCoord (α := α) (K := ℝ) ▸
    isCompact_range continuous_multiprojectiveProjectorCoord

/-- Over `ℝ`, the product projector map as a homeomorphism onto
`TauCeti.multiprojectiveProjectorLocus α ℝ`. -/
noncomputable def multiprojectiveProjectorHomeomorph (α : ι → Type*) [∀ i, Fintype (α i)] :
    (∀ i, ℙ ℝ (α i → ℝ)) ≃ₜ multiprojectiveProjectorLocus α ℝ :=
  (isHomeomorph_iff_continuous_bijective.2
    ⟨continuous_multiprojectiveProjector.subtype_mk multiprojectiveProjector_mem_locus,
      fun _ _ h ↦ multiprojectiveProjector_injective (congrArg Subtype.val h),
      fun ⟨A, hA⟩ ↦ by
        obtain ⟨p, hp⟩ := range_multiprojectiveProjector.symm.subset hA
        exact ⟨p, Subtype.ext hp⟩⟩).homeomorph _

@[simp]
theorem coe_multiprojectiveProjectorHomeomorph (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorHomeomorph α p : ∀ i, Matrix (α i) (α i) ℝ) =
      multiprojectiveProjector p :=
  (rfl)

@[simp]
theorem multiprojectiveProjectorHomeomorph_symm_apply_projector (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorHomeomorph α).symm
        ⟨multiprojectiveProjector p, multiprojectiveProjector_mem_locus p⟩ = p :=
  (multiprojectiveProjectorHomeomorph α).symm_apply_apply p

/-- Over `ℝ`, the flattened product projector map as a homeomorphism onto
`TauCeti.multiprojectiveProjectorCoordLocus α ℝ`. -/
noncomputable def multiprojectiveProjectorCoordHomeomorph (α : ι → Type*) [∀ i, Fintype (α i)] :
    (∀ i, ℙ ℝ (α i → ℝ)) ≃ₜ multiprojectiveProjectorCoordLocus α ℝ :=
  (isHomeomorph_iff_continuous_bijective.2
    ⟨continuous_multiprojectiveProjectorCoord.subtype_mk multiprojectiveProjectorCoord_mem_locus,
      fun _ _ h ↦ multiprojectiveProjectorCoord_injective (congrArg Subtype.val h),
      fun ⟨a, ha⟩ ↦ by
        obtain ⟨p, hp⟩ := range_multiprojectiveProjectorCoord.symm.subset ha
        exact ⟨p, Subtype.ext hp⟩⟩).homeomorph _

@[simp]
theorem coe_multiprojectiveProjectorCoordHomeomorph (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorCoordHomeomorph α p : (Σ i, α i × α i) → ℝ) =
      multiprojectiveProjectorCoord p :=
  (rfl)

@[simp]
theorem multiprojectiveProjectorCoordHomeomorph_symm_apply_projector (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorCoordHomeomorph α).symm
        ⟨multiprojectiveProjectorCoord p, multiprojectiveProjectorCoord_mem_locus p⟩ = p :=
  (multiprojectiveProjectorCoordHomeomorph α).symm_apply_apply p

end Topology

/-! ### Semialgebraic and Nash properties -/

section Semialgebraic

variable {ι σ K : Type*} [Field K] [LinearOrder K]

/-- For a finite factor index `ι`, the flattened product projector locus is semialgebraic in the
matrix-entry coordinates `(Σ i, α i × α i) → K`. -/
theorem isSemialgebraic_multiprojectiveProjectorCoordLocus {α : ι → Type*} [Finite ι]
    [∀ i, Fintype (α i)] :
    IsSemialgebraic (multiprojectiveProjectorCoordLocus α K) := by
  have h : multiprojectiveProjectorCoordLocus α K =
      ⋂ i : ι, (fun a : (Σ i, α i × α i) → K ↦ fun q : α i × α i ↦ a ⟨i, q⟩) ⁻¹'
        {b : α i × α i → K | Matrix.of (Function.curry b) ∈ projectorLocus (α i) K} := by
    ext a
    simp only [mem_multiprojectiveProjectorCoordLocus, mem_iInter, mem_preimage, mem_ofPred_eq]
    rfl
  rw [h]
  exact .iInter fun i ↦ (isSemialgebraic_projectorLocus (ι := α i) (K := K)).preimage_comp
    (fun q : α i × α i ↦ (⟨i, q⟩ : Σ i, α i × α i))

section OrderedProjector

variable [IsStrictOrderedRing K] {n : ι → ℕ}

/-- Over a strict ordered field and finite factor index `ι`, the graph relation
`{(a, p) | multiprojectiveProjectorCoord p = a}` is mixed semialgebraic without assuming projection
closure: in homogeneous coordinates `v_i` it is cut out inside `mixedPuncturedCone` by the
polynomial equations `(v_iᵀ v_i) * a ⟨i, j, k⟩ = v_i j * v_i k`. -/
theorem isMixedSemialgebraic_multiprojectiveProjectorCoord_rel [Finite ι] :
    IsMixedSemialgebraic
      {ap : (((Σ i, Fin (n i + 1) × Fin (n i + 1)) → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) |
        multiprojectiveProjectorCoord ap.2 = ap.1} := by
  rw [isMixedSemialgebraic_def]
  let P : (Σ i, Fin (n i + 1) × Fin (n i + 1)) →
      MvPolynomial ((Σ i, Fin (n i + 1) × Fin (n i + 1)) ⊕ Σ i, Fin (n i + 1)) K :=
    fun q ↦ (∑ r : Fin (n q.1 + 1), X (.inr ⟨q.1, r⟩) * X (.inr ⟨q.1, r⟩)) * X (.inl q) -
      X (.inr ⟨q.1, q.2.1⟩) * X (.inr ⟨q.1, q.2.2⟩)
  convert isSemialgebraic_mixedPuncturedCone.inter
    (.iInter fun q ↦ isSemialgebraic_eval_eq_zero (P q)) using 1
  ext w
  rw [mem_mixedCone, mem_inter_iff, mem_mixedPuncturedCone, mem_iInter]
  refine ⟨fun ⟨hw, heq⟩ ↦ ⟨hw, fun q ↦ ?_⟩, fun ⟨hw, hP⟩ ↦ ⟨hw, funext fun q ↦ ?_⟩⟩
  · have hs : (fun r ↦ w (.inr ⟨q.1, r⟩)) ⬝ᵥ (fun r ↦ w (.inr ⟨q.1, r⟩)) ≠ 0 :=
      dotProduct_self_eq_zero.not.mpr (hw q.1)
    have hq := congrFun heq q
    simp only [multiprojectiveProjectorCoord_apply, Projectivization.projector_mk,
      rankOneProjector_apply, Function.comp_apply] at hq
    rw [div_eq_iff hs] at hq
    simp only [mem_ofPred_eq, P, map_sub, map_mul, map_sum, eval_X, sub_eq_zero]
    simpa [dotProduct, mul_comm] using hq.symm
  · have hs : (fun r ↦ w (.inr ⟨q.1, r⟩)) ⬝ᵥ (fun r ↦ w (.inr ⟨q.1, r⟩)) ≠ 0 :=
      dotProduct_self_eq_zero.not.mpr (hw q.1)
    have hq := hP q
    simp only [mem_ofPred_eq, P, map_sub, map_mul, map_sum, eval_X, sub_eq_zero] at hq
    simp only [multiprojectiveProjectorCoord_apply, Projectivization.projector_mk,
      rankOneProjector_apply, Function.comp_apply, div_eq_iff hs]
    simpa [dotProduct, mul_comm] using hq.symm

/-- For a finite factor index `ι`, the inverse of a standard product affine chart followed by
`TauCeti.multiprojectiveProjectorCoord` is a semialgebraic map. -/
theorem isSemialgebraicMap_multiprojectiveProjectorCoord_affineChart_symm [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicMap
      (multiprojectiveProjectorCoord ∘ ⇑(multiprojectiveAffineChart (K := K) I).symm) := by
  rw [← isSemialgebraicOn_univ]
  let V : ∀ i, Fin (n i + 1) →
      MvPolynomial ((Σ i, Fin (n i)) ⊕ Σ i, Fin (n i + 1) × Fin (n i + 1)) K :=
    fun i ↦ Fin.insertNth (α := fun _ ↦ MvPolynomial _ K) (I i) 1 fun k ↦ X (.inl ⟨i, k⟩)
  have hV (z : (Σ i, Fin (n i)) → K) (a : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K)
      (i : ι) (r : Fin (n i + 1)) :
      eval (Sum.elim z a) (V i r) =
        Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) r := by
    induction r using (I i).succAboveCases with
    | x => simp [V]
    | p k => simp [V]
  refine isSemialgebraicOn_of_forall_eq_iff isSemialgebraic_univ
    (fun q ↦ (∑ r, V q.1 r * V q.1 r) * X (.inr q) - V q.1 q.2.1 * V q.1 q.2.2) fun z _ a ↦ ?_
  simp only [map_sub, map_mul, map_sum, hV, eval_X, Sum.elim_inr, Function.comp_apply, funext_iff]
  refine forall_congr' fun q ↦ ?_
  set v : Fin (n q.1 + 1) → K := Fin.insertNth (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩)
  have hs : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero (I q.1) _)
  rw [multiprojectiveProjectorCoord_apply, multiprojectiveAffineChart_symm_apply,
    Projectivization.affineChart_symm_apply, Projectivization.projector_mk, rankOneProjector_apply,
    div_eq_iff hs, sub_eq_zero, eq_comm]
  simp [v, dotProduct, mul_comm]

/-- For a finite factor index `ι`, the image of a standard product affine open under
`TauCeti.multiprojectiveProjectorCoord` is semialgebraic. -/
theorem isSemialgebraic_image_multiprojectiveProjectorCoord_affineOpen [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I) := by
  rw [image_multiprojectiveProjectorCoord_affineOpen]
  convert isSemialgebraic_multiprojectiveProjectorCoordLocus.inter
    (.iInter fun i ↦ isSemialgebraic_eval_ne_zero
      (X ⟨i, I i, I i⟩ : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K)) using 1
  ext a
  simp

/-- For a finite factor index `ι`, the standard product affine chart at `I` read in the flattened
product projector model is semialgebraic on the image of `multiprojectiveAffineOpen I`. -/
theorem isSemialgebraicOn_multiprojectiveProjectorCoord_affineChart [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicOn
      (fun a : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K ↦ fun q : Σ i, Fin (n i) ↦
        a ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ / a ⟨q.1, I q.1, I q.1⟩)
      (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I) := by
  refine isSemialgebraicOn_of_forall_eq_iff
    (isSemialgebraic_image_multiprojectiveProjectorCoord_affineOpen I)
    (fun q ↦ X (.inl ⟨q.1, I q.1, I q.1⟩) * X (.inr q) -
      X (.inl ⟨q.1, (I q.1).succAbove q.2, I q.1⟩))
    fun a ha z ↦ ?_
  rw [mem_ofPred_eq, image_multiprojectiveProjectorCoord_affineOpen] at ha
  simp only [funext_iff, map_sub, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr]
  refine forall_congr' fun q ↦ ?_
  have hne : a ⟨q.1, I q.1, I q.1⟩ ≠ 0 := ha.2 q.1
  rw [div_eq_iff hne, eq_comm, ← sub_eq_zero, mul_comm]

/-- **Semialgebraic subsets in the product projector model.** Over an ordered field with
semialgebraic projections (such as `ℝ`) and finitely many projective factors, a subset `S` of
`∀ i, ℙ K (Fin (n i + 1) → K)` has semialgebraic image under `TauCeti.multiprojectiveProjectorCoord`
if and only if `S` is multiprojective semialgebraic. -/
theorem isSemialgebraic_image_multiprojectiveProjectorCoord_iff [HasSemialgebraicProjections K]
    [Finite ι] {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsSemialgebraic (multiprojectiveProjectorCoord '' S) ↔ IsMultiprojectiveSemialgebraic S := by
  let μ := Σ i, Fin (n i + 1) × Fin (n i + 1)
  let R : Set ((μ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :=
    {ap | multiprojectiveProjectorCoord ap.2 = ap.1}
  have hR : IsSemialgebraic (mixedCone R) :=
    isMixedSemialgebraic_def.1 isMixedSemialgebraic_multiprojectiveProjectorCoord_rel
  rw [isMultiprojectiveSemialgebraic_def]
  constructor
  · intro hS
    convert (hR.inter (hS.preimage_comp Sum.inl)).image_comp_inr using 1
    ext v
    rw [mem_multiprojectiveCone, mem_image]
    constructor
    · rintro ⟨hv, hvS⟩
      let p : ∀ i, ℙ K (Fin (n i + 1) → K) :=
        fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)
      refine ⟨Sum.elim (multiprojectiveProjectorCoord p) v, ⟨?_, ⟨p, hvS, rfl⟩⟩,
        funext fun _ ↦ Sum.elim_inr _ _ _⟩
      rw [mem_mixedCone]
      exact ⟨hv, rfl⟩
    · rintro ⟨w, ⟨hwR, p, hpS, hp_eq⟩, rfl⟩
      rw [mem_mixedCone] at hwR
      obtain ⟨hw, hwp⟩ := hwR
      have hp' : (fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw i)) = p :=
        multiprojectiveProjectorCoord_injective (hwp.trans hp_eq.symm)
      exact ⟨hw, hp'.symm ▸ hpS⟩
  · intro hS
    convert (hR.inter (hS.preimage_comp Sum.inr)).image_comp_inl using 1
    ext a
    rw [mem_image, mem_image]
    constructor
    · rintro ⟨p, hpS, rfl⟩
      let v : (Σ i, Fin (n i + 1)) → K := fun q ↦ (p q.1).rep q.2
      have hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0 := fun i ↦ (p i).rep_ne_zero
      have hmk : (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) = p :=
        funext fun i ↦ (p i).mk_rep
      refine ⟨Sum.elim (multiprojectiveProjectorCoord p) v, ⟨?_, ?_⟩,
        funext fun _ ↦ Sum.elim_inl _ _ _⟩
      · exact mem_mixedCone.2 ⟨hv, show multiprojectiveProjectorCoord
          (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) =
          multiprojectiveProjectorCoord p by rw [hmk]⟩
      · exact mem_multiprojectiveCone.2 ⟨hv, hmk ▸ hpS⟩
    · rintro ⟨w, ⟨hwR, hwS⟩, rfl⟩
      exact ⟨_, (mem_multiprojectiveCone.1 hwS).2, (mem_mixedCone.1 hwR).2⟩

private theorem isSemialgebraicOn_multiprojectiveProjectorCoord_comp_of_graphOn
    [HasSemialgebraicProjections K] [Finite ι]
    {τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)}
    (hG : IsMixedSemialgebraic (s.graphOn τ)) :
    IsSemialgebraicOn (multiprojectiveProjectorCoord ∘ τ) s := by
  let μ := Σ i, Fin (n i + 1) × Fin (n i + 1)
  let R : Set ((μ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :=
    {ap | multiprojectiveProjectorCoord ap.2 = ap.1}
  have hR : IsSemialgebraic (mixedCone R) :=
    isMixedSemialgebraic_def.1 isMixedSemialgebraic_multiprojectiveProjectorCoord_rel
  rw [isSemialgebraicOn_iff_graph]
  let f₁ : (σ ⊕ Σ i, Fin (n i + 1)) → (σ ⊕ μ) ⊕ Σ i, Fin (n i + 1) :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let f₂ : (μ ⊕ Σ i, Fin (n i + 1)) → (σ ⊕ μ) ⊕ Σ i, Fin (n i + 1) :=
    Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  convert (((isMixedSemialgebraic_def.1 hG).preimage_comp f₁).inter
      (hR.preimage_comp f₂)).image_comp_inl using 1
  ext za
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  constructor
  · rintro ⟨hzas, hza⟩
    let p := τ (za ∘ Sum.inl)
    let v : (Σ i, Fin (n i + 1)) → K := fun q ↦ (p q.1).rep q.2
    have hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0 := fun i ↦ (p i).rep_ne_zero
    have hmk : (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) = p :=
      funext fun i ↦ (p i).mk_rep
    refine ⟨Sum.elim za v, ⟨?_, ?_⟩, funext fun _ ↦ Sum.elim_inl _ _ _⟩
    · rw [mem_preimage, mem_mixedCone]
      exact ⟨hv, mem_graphOn.2 ⟨hzas, hmk.symm⟩⟩
    · rw [mem_preimage, mem_mixedCone]
      exact ⟨hv, show multiprojectiveProjectorCoord
        (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) = za ∘ Sum.inr by
        rw [hmk]; exact hza⟩
  · rintro ⟨u, ⟨hu₁, hu₂⟩, rfl⟩
    rw [mem_preimage, mem_mixedCone] at hu₁ hu₂
    obtain ⟨hu, huG⟩ := hu₁
    obtain ⟨_, huR⟩ := hu₂
    obtain ⟨hus, hτu⟩ := mem_graphOn.1 huG
    have hτu' : τ ((u ∘ Sum.inl) ∘ Sum.inl) =
        fun i ↦ Projectivization.mk K (fun j ↦ u (.inr ⟨i, j⟩)) (hu i) := hτu
    have huR' : multiprojectiveProjectorCoord
        (fun i ↦ Projectivization.mk K (fun j ↦ u (.inr ⟨i, j⟩)) (hu i)) =
        (u ∘ Sum.inl) ∘ Sum.inr := huR
    exact ⟨hus, by rw [Function.comp_apply, hτu', huR']⟩

private theorem isMixedSemialgebraic_graphOn_of_isSemialgebraicOn_multiprojectiveProjectorCoord_comp
    [HasSemialgebraicProjections K] [Finite ι]
    {τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)}
    (hφ : IsSemialgebraicOn (multiprojectiveProjectorCoord ∘ τ) s) :
    IsMixedSemialgebraic (s.graphOn τ) := by
  let μ := Σ i, Fin (n i + 1) × Fin (n i + 1)
  let R : Set ((μ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :=
    {ap | multiprojectiveProjectorCoord ap.2 = ap.1}
  have hR : IsSemialgebraic (mixedCone R) :=
    isMixedSemialgebraic_def.1 isMixedSemialgebraic_multiprojectiveProjectorCoord_rel
  rw [isMixedSemialgebraic_def]
  let g₁ : σ ⊕ μ → μ ⊕ (σ ⊕ Σ i, Fin (n i + 1)) := Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl
  let g₂ : (μ ⊕ Σ i, Fin (n i + 1)) → μ ⊕ (σ ⊕ Σ i, Fin (n i + 1)) :=
    Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  convert (((isSemialgebraicOn_iff_graph.1 hφ).preimage_comp g₁).inter
      (hR.preimage_comp g₂)).image_comp_inr using 1
  ext w
  rw [mem_mixedCone, mem_image]
  constructor
  · rintro ⟨hw, hwG⟩
    obtain ⟨hws, hτw⟩ := mem_graphOn.1 hwG
    let p : ∀ i, ℙ K (Fin (n i + 1) → K) :=
      fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw i)
    refine ⟨Sum.elim (multiprojectiveProjectorCoord p) w, ⟨?_, ?_⟩,
      funext fun _ ↦ Sum.elim_inr _ _ _⟩
    · rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
      refine ⟨hws, ?_⟩
      rw [Function.comp_apply]
      have h₁ : (Sum.elim (multiprojectiveProjectorCoord p) w ∘ g₁) ∘ Sum.inl = w ∘ Sum.inl := rfl
      have h₂ : (Sum.elim (multiprojectiveProjectorCoord p) w ∘ g₁) ∘ Sum.inr =
          multiprojectiveProjectorCoord p := rfl
      rw [h₁, h₂, hτw]
    · rw [mem_preimage, mem_mixedCone]
      exact ⟨hw, rfl⟩
  · rintro ⟨u, ⟨hu₁, hu₂⟩, rfl⟩
    rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn] at hu₁
    rw [mem_preimage, mem_mixedCone] at hu₂
    obtain ⟨hws, hτu⟩ := hu₁
    obtain ⟨hw, hpu⟩ := hu₂
    have hw' : ∀ i, (fun j ↦ u (.inr (.inr ⟨i, j⟩))) ≠ 0 := hw
    refine ⟨hw', mem_graphOn.2 ⟨hws, ?_⟩⟩
    exact multiprojectiveProjectorCoord_injective (hτu.trans hpu.symm)

/-- **Semialgebraic maps from affine space via the product projector model.** Over an ordered field
with semialgebraic projections and finitely many projective factors, a map
`τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)` from an arbitrary affine space has mixed semialgebraic
graph over `s ⊆ σ → K` if and only if `multiprojectiveProjectorCoord ∘ τ` is
`TauCeti.IsSemialgebraicOn` on `s`. -/
theorem isMixedSemialgebraic_graphOn_iff_isSemialgebraicOn_multiprojectiveProjectorCoord_comp
    [HasSemialgebraicProjections K] [Finite ι]
    {τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)} :
    IsMixedSemialgebraic (s.graphOn τ) ↔
      IsSemialgebraicOn (multiprojectiveProjectorCoord ∘ τ) s :=
  ⟨isSemialgebraicOn_multiprojectiveProjectorCoord_comp_of_graphOn,
    isMixedSemialgebraic_graphOn_of_isSemialgebraicOn_multiprojectiveProjectorCoord_comp⟩

end OrderedProjector

/-! ### Nash chart coordinates over `ℝ` -/

section Nash

/-- Over `ℝ`, every matrix-entry coordinate of `TauCeti.multiprojectiveProjectorCoord` read in the
standard product affine chart at `I` is a Nash germ. -/
theorem isNashAt_multiprojectiveProjectorCoord_affineChart_symm {ι : Type*} [Fintype ι]
    {n : ι → ℕ} (I : ∀ i, Fin (n i + 1)) (q : Σ i, Fin (n i + 1) × Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → ℝ) :
    IsNashAt
      (fun z ↦ multiprojectiveProjectorCoord
        ((multiprojectiveAffineChart (K := ℝ) I).symm z) q) z := by
  have hw (l : Fin (n q.1 + 1)) :
      IsNashAt
        (fun z : (Σ i, Fin (n i)) → ℝ ↦
          Fin.insertNth (α := fun _ ↦ ℝ) (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩) l) z := by
    induction l using (I q.1).succAboveCases with
    | x => simpa using isNashAt_const 1
    | p k => simpa using isNashAt_apply (⟨q.1, k⟩ : Σ i, Fin (n i))
  simp only [multiprojectiveProjectorCoord_apply, multiprojectiveAffineChart_symm_apply,
    Projectivization.affineChart_symm_apply, Projectivization.projector_mk, rankOneProjector_apply]
  exact ((hw q.2.1).fun_mul (hw q.2.2)).fun_div
    (Finset.fun_isNashAt_sum _ fun k _ ↦ (hw k).fun_mul (hw k))
    (dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero (I q.1) _))

/-- Over `ℝ`, each ratio coordinate `a ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ / a ⟨q.1, I q.1, I q.1⟩`
recovering `TauCeti.multiprojectiveAffineChart I` from the flattened product projector model is a
Nash germ at every point `a` with `a ⟨q.1, I q.1, I q.1⟩ ≠ 0`. -/
theorem isNashAt_multiprojectiveAffineChart_projectorCoord {ι : Type*} [Fintype ι]
    {n : ι → ℕ} (I : ∀ i, Fin (n i + 1)) (q : Σ i, Fin (n i))
    {a : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → ℝ} (ha : a ⟨q.1, I q.1, I q.1⟩ ≠ 0) :
    IsNashAt
      (fun b : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → ℝ ↦
        b ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ / b ⟨q.1, I q.1, I q.1⟩) a :=
  (isNashAt_apply (⟨q.1, (I q.1).succAbove q.2, I q.1⟩ :
    Σ i, Fin (n i + 1) × Fin (n i + 1))).fun_div
    (isNashAt_apply (⟨q.1, I q.1, I q.1⟩ : Σ i, Fin (n i + 1) × Fin (n i + 1))) ha

end Nash

end Semialgebraic

end TauCeti
