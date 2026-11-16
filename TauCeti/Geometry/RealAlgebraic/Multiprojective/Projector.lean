/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic
public import TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding

import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Rational

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
`TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic`,
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function` (`TauCeti.IsSemialgebraicOn`), and
`TauCeti.Geometry.RealAlgebraic.Nash.Basic` (`TauCeti.IsNashAt`):

* Over `ℝ`, `TauCeti.multiprojectiveProjector` and `TauCeti.multiprojectiveProjectorCoord` are
  closed embeddings onto compact real algebraic loci, yielding the homeomorphisms
  `TauCeti.multiprojectiveProjectorHomeomorph` and
  `TauCeti.multiprojectiveProjectorCoordHomeomorph`. Relative complements in multiprojective space
  transport to relative complements inside the product projector locus
  (`TauCeti.image_multiprojectiveProjector_compl`,
  `TauCeti.image_multiprojectiveProjectorCoord_compl`).
* Over any strict ordered field and finite factor index `ι` (without assuming projection closure),
  the equality locus `{(a, p) | multiprojectiveProjectorCoord p = a}` is mixed semialgebraic
  (`TauCeti.isMixedSemialgebraic_setOf_multiprojectiveProjectorCoord_eq`), the standard product
  affine charts and their inverses are semialgebraic in the matrix-entry model, a subset `S` of a
  mixed space is mixed semialgebraic if and only if its image under
  `Prod.map id multiprojectiveProjectorCoord` is semialgebraic
  (`TauCeti.isSemialgebraic_preimage_prodMap_multiprojectiveProjectorCoord_iff`),
  a subset `S` of multiprojective space is multiprojective semialgebraic if and only if
  `multiprojectiveProjectorCoord '' S` is semialgebraic
  (`TauCeti.isSemialgebraic_image_multiprojectiveProjectorCoord_iff`), and an affine-domain map
  `τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)` has mixed semialgebraic graph over `s` if and only
  if `multiprojectiveProjectorCoord ∘ τ` has semialgebraic graph over `s`
  (`TauCeti.isMixedSemialgebraic_graphOn_iff_graph_multiprojectiveProjectorCoord_comp`).
* Over an ordered field with semialgebraic projections (such as `ℝ`), `τ` has mixed semialgebraic
  graph over `s` if and only if `multiprojectiveProjectorCoord ∘ τ` is `TauCeti.IsSemialgebraicOn`
  on `s`
  (`TauCeti.isMixedSemialgebraic_graphOn_iff_isSemialgebraicOn_multiprojectiveProjectorCoord_comp`).
* Over `ℝ`, both the chart-to-projector entries and the projector-to-chart ratio coordinates are
  Nash germs (`TauCeti.isNashAt_multiprojectiveProjectorCoord_affineChart_symm`,
  `TauCeti.isNashAt_multiprojectiveProjectorCoord_affineChart`).

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

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete (3) 36, Springer (1998), §3.4.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.

The product projector locus, closed-embedding, and affine-chart arguments adapt the single-factor
constructions and proofs in `TauCeti.LinearAlgebra.Projectivization.Projector` and
`TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`.
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

theorem multiprojectiveProjectorCoord_eq_comp :
    (multiprojectiveProjectorCoord : (∀ i, ℙ K (α i → K)) → (Σ i, α i × α i) → K) =
      multiprojectiveMatrixCoordEquiv α K ∘ multiprojectiveProjector :=
  funext multiprojectiveProjectorCoord_def

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

theorem multiprojectiveProjectorCoordLocus_def :
    multiprojectiveProjectorCoordLocus α K =
      multiprojectiveMatrixCoordEquiv α K '' multiprojectiveProjectorLocus α K :=
  (rfl)

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
  rw [multiprojectiveProjectorCoord_eq_comp, range_comp, range_multiprojectiveProjector,
    multiprojectiveProjectorCoordLocus_def]

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
theorem image_multiprojectiveProjector_affineOpen (I : ∀ i, α i) :
    multiprojectiveProjector '' multiprojectiveAffineOpen (K := K) I =
      multiprojectiveProjectorLocus α K ∩ {A | ∀ i, A i (I i) (I i) ≠ 0} := by
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
theorem image_multiprojectiveProjectorCoord_affineOpen (I : ∀ i, α i) :
    multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I =
      multiprojectiveProjectorCoordLocus α K ∩ {a | ∀ i, a ⟨i, I i, I i⟩ ≠ 0} := by
  rw [multiprojectiveProjectorCoord_eq_comp, image_comp,
    image_multiprojectiveProjector_affineOpen, multiprojectiveProjectorCoordLocus_def]
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
  rw [multiprojectiveAffineChart_apply, Projectivization.affineChart_eq_projector_div,
    multiprojectiveProjector_apply]

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
  isClosedEmbedding_multiprojectiveProjector.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_multiprojectiveProjector)

@[simp]
theorem coe_multiprojectiveProjectorHomeomorph_apply (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorHomeomorph α p : ∀ i, Matrix (α i) (α i) ℝ) =
      multiprojectiveProjector p := by
  simp [multiprojectiveProjectorHomeomorph, Homeomorph.setCongr]

@[simp]
theorem multiprojectiveProjectorHomeomorph_symm_apply_projector (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorHomeomorph α).symm
        ⟨multiprojectiveProjector p, multiprojectiveProjector_mem_locus p⟩ = p := by
  apply (multiprojectiveProjectorHomeomorph α).injective
  ext1
  simp

/-- Over `ℝ`, the flattened product projector map as a homeomorphism onto
`TauCeti.multiprojectiveProjectorCoordLocus α ℝ`. -/
noncomputable def multiprojectiveProjectorCoordHomeomorph (α : ι → Type*) [∀ i, Fintype (α i)] :
    (∀ i, ℙ ℝ (α i → ℝ)) ≃ₜ multiprojectiveProjectorCoordLocus α ℝ :=
  (multiprojectiveProjectorHomeomorph α).trans
    ((multiprojectiveMatrixCoordHomeomorph α ℝ).image (multiprojectiveProjectorLocus α ℝ))

@[simp]
theorem coe_multiprojectiveProjectorCoordHomeomorph_apply (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorCoordHomeomorph α p : (Σ i, α i × α i) → ℝ) =
      multiprojectiveProjectorCoord p :=
  (congrArg Subtype.val
    (Homeomorph.trans_apply (multiprojectiveProjectorHomeomorph α)
      ((multiprojectiveMatrixCoordHomeomorph α ℝ).image
        (multiprojectiveProjectorLocus α ℝ)) p)).trans <| by
    simp [multiprojectiveProjectorCoord_def]

@[simp]
theorem multiprojectiveProjectorCoordHomeomorph_symm_apply_projector (p : ∀ i, ℙ ℝ (α i → ℝ)) :
    (multiprojectiveProjectorCoordHomeomorph α).symm
        ⟨multiprojectiveProjectorCoord p, multiprojectiveProjectorCoord_mem_locus p⟩ = p := by
  apply (multiprojectiveProjectorCoordHomeomorph α).injective
  ext1
  simp

end Topology

/-! ### Semialgebraic and Nash properties -/

section Semialgebraic

variable {ι σ K : Type*} [Field K] [LinearOrder K]

/-- For a finite factor index `ι`, the flattened product projector locus is semialgebraic in the
matrix-entry coordinates `(Σ i, α i × α i) → K`. -/
theorem isSemialgebraic_multiprojectiveProjectorCoordLocus {α : ι → Type*} [Finite ι]
    [∀ i, Fintype (α i)] :
    IsSemialgebraic (multiprojectiveProjectorCoordLocus α K) := by
  have hcurry (i : ι) (a : (Σ i, α i × α i) → K) :
      Function.curry (fun q : α i × α i ↦ a ⟨i, q⟩) = fun j k ↦ a ⟨i, j, k⟩ :=
    funext₂ fun _ _ ↦ Function.curry_apply _ _ _
  have h : multiprojectiveProjectorCoordLocus α K =
      ⋂ i : ι, (fun a : (Σ i, α i × α i) → K ↦ fun q : α i × α i ↦ a ⟨i, q⟩) ⁻¹'
        {b : α i × α i → K | Matrix.of (Function.curry b) ∈ projectorLocus (α i) K} := by
    ext a
    simp only [mem_multiprojectiveProjectorCoordLocus, mem_iInter, mem_preimage, mem_ofPred_eq,
      hcurry]
  rw [h]
  exact .iInter fun i ↦ (isSemialgebraic_projectorLocus (ι := α i) (K := K)).preimage_comp
    (fun q : α i × α i ↦ (⟨i, q⟩ : Σ i, α i × α i))

section OrderedProjector

variable [IsStrictOrderedRing K] {n : ι → ℕ}

/-- Over a strict ordered field and finite factor index `ι`, the equality locus
`{(a, p) | multiprojectiveProjectorCoord p = a}` is mixed semialgebraic without assuming projection
closure: in homogeneous coordinates `v_i` it is cut out inside `mixedPuncturedCone` by the
polynomial equations `(v_iᵀ v_i) * a ⟨i, j, k⟩ = v_i j * v_i k`. -/
theorem isMixedSemialgebraic_setOf_multiprojectiveProjectorCoord_eq [Finite ι] :
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
  let V : ∀ i, Fin (n i + 1) → MvPolynomial (Σ i, Fin (n i)) K :=
    fun i r ↦ multiprojectiveInsertNthPoly I ⟨i, r⟩
  have hfn :
      (multiprojectiveProjectorCoord ∘ ⇑(multiprojectiveAffineChart (K := K) I).symm) =
        fun z q ↦
          eval z (V q.1 q.2.1 * V q.1 q.2.2) /
            eval z (∑ r : Fin (n q.1 + 1), V q.1 r * V q.1 r) := by
    ext z q
    simp [V, multiprojectiveAffineChart_symm_apply, Projectivization.affineChart_symm_apply,
      rankOneProjector_apply, dotProduct]
  rw [hfn]
  refine isSemialgebraicMap_eval_div
    (fun q : Σ i, Fin (n i + 1) × Fin (n i + 1) ↦ V q.1 q.2.1 * V q.1 q.2.2)
    (fun q : Σ i, Fin (n i + 1) × Fin (n i + 1) ↦ ∑ r : Fin (n q.1 + 1), V q.1 r * V q.1 r)
    fun z q ↦ ?_
  have hsum : eval z (∑ r : Fin (n q.1 + 1), V q.1 r * V q.1 r) =
      Fin.insertNth (α := fun _ ↦ K) (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩) ⬝ᵥ
        Fin.insertNth (α := fun _ ↦ K) (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩) := by
    simp [V, dotProduct]
  rw [hsum]
  exact dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero (I q.1) _)

/-- For a finite factor index `ι`, the image of a standard product affine open under
`TauCeti.multiprojectiveProjectorCoord` is semialgebraic. -/
theorem isSemialgebraic_image_multiprojectiveProjectorCoord_affineOpen {α : ι → Type*}
    [∀ i, Fintype (α i)] [Finite ι] (I : ∀ i, α i) :
    IsSemialgebraic (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I) := by
  rw [image_multiprojectiveProjectorCoord_affineOpen]
  convert isSemialgebraic_multiprojectiveProjectorCoordLocus.inter
    (.iInter fun i ↦ isSemialgebraic_eval_ne_zero
      (X ⟨i, I i, I i⟩ : MvPolynomial (Σ i, α i × α i) K)) using 1
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
  refine (isSemialgebraicOn_eval_div
    (fun q : Σ i, Fin (n i) ↦ X ⟨q.1, (I q.1).succAbove q.2, I q.1⟩)
    (fun q : Σ i, Fin (n i) ↦ X ⟨q.1, I q.1, I q.1⟩)
    (isSemialgebraic_image_multiprojectiveProjectorCoord_affineOpen I) fun a ha q ↦ ?_).congr
    fun a _ ↦ funext fun q ↦ by simp
  rw [image_multiprojectiveProjectorCoord_affineOpen] at ha
  simpa using ha.2 q.1

private theorem isMixedSemialgebraic_of_isSemialgebraic_preimage_prodMap
    [Finite ι] {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hE : IsSemialgebraic
      (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i + 1) × Fin (n i + 1)) K ⁻¹'
        (Prod.map id multiprojectiveProjectorCoord '' S))) :
    IsMixedSemialgebraic S := by
  let μ := Σ i, Fin (n i + 1) × Fin (n i + 1)
  let f : σ ⊕ μ → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun a ↦ X (.inl a))
      fun q ↦ X (.inr ⟨q.1, q.2.1⟩) * X (.inr ⟨q.1, q.2.2⟩)
  let g : σ ⊕ μ → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun _ ↦ 1)
      fun q ↦ ∑ r : Fin (n q.1 + 1), X (.inr ⟨q.1, r⟩) * X (.inr ⟨q.1, r⟩)
  have hg (w : (σ ⊕ Σ i, Fin (n i + 1)) → K)
      (hw : w ∈ mixedPuncturedCone σ n K) (c : σ ⊕ μ) : eval w (g c) ≠ 0 := by
    cases c with
    | inl _ => simp [g]
    | inr q =>
      have hsum : eval w (g (.inr q)) =
          (fun r ↦ w (.inr ⟨q.1, r⟩)) ⬝ᵥ (fun r ↦ w (.inr ⟨q.1, r⟩)) := by
        simp [g, dotProduct]
      rw [hsum]
      exact dotProduct_self_eq_zero.not.mpr (mem_mixedPuncturedCone.1 hw q.1)
  have heval (w : (σ ⊕ Σ i, Fin (n i + 1)) → K) (hw : w ∈ mixedPuncturedCone σ n K) :
      Equiv.sumArrowEquivProdArrow σ μ K (fun c ↦ eval w (f c) / eval w (g c)) =
        Prod.map id multiprojectiveProjectorCoord
          (w ∘ Sum.inl,
            fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩))
              (mem_mixedPuncturedCone.1 hw i)) := by
    refine Prod.ext (funext fun a ↦ by simp [f, g]) (funext fun q ↦ ?_)
    simp [f, g, rankOneProjector_apply, dotProduct]
  rw [isMixedSemialgebraic_def]
  convert hE.inter_preimage_eval_div isSemialgebraic_mixedPuncturedCone f g hg using 1
  ext w
  rw [mem_mixedCone, mem_inter_iff, mem_preimage, mem_preimage]
  refine ⟨fun ⟨hw, hwS⟩ ↦ ⟨mem_mixedPuncturedCone.2 hw, ?_⟩,
    fun ⟨hw, hfw⟩ ↦ ⟨mem_mixedPuncturedCone.1 hw, ?_⟩⟩
  · rw [heval w (mem_mixedPuncturedCone.2 hw)]
    exact mem_image_of_mem _ hwS
  · rwa [heval w hw,
      (Function.Injective.prodMap Function.injective_id
        multiprojectiveProjectorCoord_injective).mem_set_image] at hfw

private theorem isSemialgebraic_preimage_prodMap_inter_affineOpen
    [Finite ι] {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic
      (((fun z : (σ ⊕ Σ i, Fin (n i + 1) × Fin (n i + 1)) → K ↦ z ∘ Sum.inr) ⁻¹'
          (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I)) ∩
        Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i + 1) × Fin (n i + 1)) K ⁻¹'
          (Prod.map id multiprojectiveProjectorCoord '' S)) := by
  let μ := Σ i, Fin (n i + 1) × Fin (n i + 1)
  let UI : Set ((σ ⊕ μ) → K) :=
    (fun z ↦ z ∘ Sum.inr) ⁻¹'
      (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I)
  have hUI : IsSemialgebraic UI :=
    (isSemialgebraic_image_multiprojectiveProjectorCoord_affineOpen I).preimage_comp Sum.inr
  have hchartS : IsSemialgebraic ((mixedAffineChart σ I).symm ⁻¹' S) := by
    rw [← mixedAffineChart_image_inter_affineOpen]
    exact hS.isSemialgebraic_chart I
  let f : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ μ) K :=
    Sum.elim (fun a ↦ X (.inl a)) fun q ↦ X (.inr ⟨q.1, (I q.1).succAbove q.2, I q.1⟩)
  let g : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ μ) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ X (.inr ⟨q.1, I q.1, I q.1⟩)
  have hg (z : (σ ⊕ μ) → K) (hz : z ∈ UI) (c : σ ⊕ Σ i, Fin (n i)) : eval z (g c) ≠ 0 := by
    cases c with
    | inl _ => simp [g]
    | inr q =>
      rw [mem_preimage, image_multiprojectiveProjectorCoord_affineOpen] at hz
      simpa [g] using hz.2 q.1
  convert hchartS.inter_preimage_eval_div hUI f g hg using 1
  ext z
  simp only [mem_inter_iff, mem_preimage]
  refine and_congr_right fun hz ↦ ?_
  obtain ⟨p, hpI, hp_eq⟩ := hz
  have hfg : (fun c ↦ eval z (f c) / eval z (g c)) = mixedAffineChart σ I (z ∘ Sum.inl, p) := by
    ext (a | q)
    · simp [f, g]
    · rw [mixedAffineChart_apply_inr, multiprojectiveAffineChart_eq_multiprojectiveProjector_div]
      have hp_at (r : μ) : z (.inr r) = multiprojectiveProjector p r.1 r.2.1 r.2.2 := by
        simpa using (congrFun hp_eq r).symm
      simp [f, g, hp_at]
  have hprod : Equiv.sumArrowEquivProdArrow σ μ K z =
      Prod.map id multiprojectiveProjectorCoord (z ∘ Sum.inl, p) :=
    Prod.ext (funext fun _ ↦ by simp)
      (funext fun q ↦ by
        rw [Equiv.sumArrowEquivProdArrow_apply_snd, Prod.map_snd]
        exact (congrFun hp_eq q).symm)
  have hmemI : (z ∘ Sum.inl, p) ∈ (mixedAffineChart σ I).source := by
    rw [mixedAffineChart_source]
    exact mem_mixedAffineOpen.2 hpI
  rw [hprod, (Function.Injective.prodMap Function.injective_id
      multiprojectiveProjectorCoord_injective).mem_set_image, hfg,
    (mixedAffineChart σ I).left_inv hmemI]

/-- **Mixed semialgebraic subsets in the product projector model.** Over a strict ordered field and
finitely many projective factors, a subset `S ⊆ (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` is mixed
semialgebraic if and only if its embedded image under `Prod.map id multiprojectiveProjectorCoord`
is semialgebraic. No projection-closure hypothesis is required. -/
theorem isSemialgebraic_preimage_prodMap_multiprojectiveProjectorCoord_iff
    [Finite ι] {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsSemialgebraic
        (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i + 1) × Fin (n i + 1)) K ⁻¹'
          (Prod.map id multiprojectiveProjectorCoord '' S)) ↔
      IsMixedSemialgebraic S := by
  refine ⟨isMixedSemialgebraic_of_isSemialgebraic_preimage_prodMap, fun hS ↦ ?_⟩
  set E := Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i + 1) × Fin (n i + 1)) K ⁻¹'
    (Prod.map id multiprojectiveProjectorCoord '' S)
  have hcover : E =
      ⋃ I : ∀ i, Fin (n i + 1),
        ((fun z : (σ ⊕ Σ i, Fin (n i + 1) × Fin (n i + 1)) → K ↦ z ∘ Sum.inr) ⁻¹'
            (multiprojectiveProjectorCoord '' multiprojectiveAffineOpen (K := K) I)) ∩ E := by
    ext z
    simp only [mem_iUnion, mem_inter_iff]
    refine ⟨fun hz ↦ ?_, fun ⟨_, _, hz⟩ ↦ hz⟩
    rcases hz with ⟨⟨x, p⟩, hpS, hp_eq⟩
    obtain ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen p
    refine ⟨I, ?_, ⟨(x, p), hpS, hp_eq⟩⟩
    have hz_inr : z ∘ Sum.inr = multiprojectiveProjectorCoord p :=
      funext fun q ↦ (congrFun (congrArg Prod.snd hp_eq) q).symm
    rw [mem_preimage, hz_inr]
    exact mem_image_of_mem _ hpI
  rw [hcover]
  exact .iUnion fun I ↦ isSemialgebraic_preimage_prodMap_inter_affineOpen hS I

/-- **Semialgebraic subsets in the product projector model.** Over a strict ordered field and
finitely many projective factors, a subset `S` of `∀ i, ℙ K (Fin (n i + 1) → K)` has semialgebraic
image under `TauCeti.multiprojectiveProjectorCoord` if and only if `S` is multiprojective
semialgebraic. No projection-closure hypothesis is required. -/
theorem isSemialgebraic_image_multiprojectiveProjectorCoord_iff [Finite ι]
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsSemialgebraic (multiprojectiveProjectorCoord '' S) ↔ IsMultiprojectiveSemialgebraic S := by
  let e := (Equiv.emptySum Empty (Σ i, Fin (n i + 1) × Fin (n i + 1))).symm
  rw [← isSemialgebraic_preimage_comp_equiv e,
    ← isMixedSemialgebraic_univ_prod_iff (σ := Empty),
    ← isSemialgebraic_preimage_prodMap_multiprojectiveProjectorCoord_iff]
  convert Iff.rfl using 2
  ext z
  simp only [mem_preimage, mem_image, mem_prod, mem_univ, true_and, Prod.exists,
    Prod.map_apply, id_eq, Prod.ext_iff]
  exact ⟨fun ⟨_, p, hp, _, hp_eq⟩ ↦ ⟨p, hp, hp_eq⟩,
    fun ⟨p, hp, hp_eq⟩ ↦ ⟨z ∘ Sum.inl, p, hp, rfl, hp_eq⟩⟩

/-- **Graphs of maps from affine space via the product projector model.** Over a strict ordered
field and finitely many projective factors, a map
`τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)` from an arbitrary affine space has mixed semialgebraic
graph over `s ⊆ σ → K` if and only if `multiprojectiveProjectorCoord ∘ τ` has semialgebraic graph
over `s`. No projection-closure hypothesis is required. -/
theorem isMixedSemialgebraic_graphOn_iff_graph_multiprojectiveProjectorCoord_comp
    [Finite ι] {τ : (σ → K) → ∀ i, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)} :
    IsMixedSemialgebraic (s.graphOn τ) ↔
      IsSemialgebraic
        (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i + 1) × Fin (n i + 1)) K ⁻¹'
          s.graphOn (multiprojectiveProjectorCoord ∘ τ)) := by
  have hgraph :
      Prod.map id multiprojectiveProjectorCoord '' s.graphOn τ =
        s.graphOn (multiprojectiveProjectorCoord ∘ τ) := by
    ext ⟨x, a⟩
    simp only [mem_image, mem_graphOn, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq,
      Function.comp_apply]
    exact ⟨fun ⟨_, _, ⟨hx', hτx'⟩, hx'_eq, ha⟩ ↦ ⟨hx'_eq ▸ hx', hx'_eq ▸ hτx' ▸ ha⟩,
      fun ⟨hx, ha⟩ ↦ ⟨x, τ x, ⟨hx, rfl⟩, rfl, ha⟩⟩
  rw [← isSemialgebraic_preimage_prodMap_multiprojectiveProjectorCoord_iff, hgraph]

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
  isMixedSemialgebraic_graphOn_iff_graph_multiprojectiveProjectorCoord_comp.trans
    isSemialgebraicOn_iff_graph.symm

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
theorem isNashAt_multiprojectiveProjectorCoord_affineChart {ι : Type*} [Fintype ι]
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
