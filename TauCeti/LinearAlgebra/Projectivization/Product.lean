/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.Projector

/-!
# Finite products of projective spaces

A multiprojective space `(i : ι) → ℙ K (κ i → K)` is a product of projective spaces over a field
(or division ring) `K`. To apply affine coordinate methods—such as multivariate polynomials,
semialgebraic sets and affine charts—to such a product, we flatten both its homogeneous
representatives `(i : ι) → κ i → K` to `(Σ i, κ i) → K` (`LinearEquiv.piCurry`) and its families of
matrices `(i : ι) → Matrix (κ i) (μ i) K` to `(Σ i, κ i × μ i) → K`
(`TauCeti.piMatrixLinearEquiv`).

For `κ i = Fin (n i + 1)`, each choice of coordinate indices `I : ∀ i, Fin (n i + 1)` picks out the
standard product affine open `Projectivization.piAffineOpen I = {p | ∀ i, p i ∈ affineOpen (I i)}`
and the standard product affine chart `Projectivization.piAffineChart I`, a partial equivalence onto
the flattened affine coordinate space `(Σ i, Fin (n i)) → K`. These opens cover the product,
including in the empty product case (`IsEmpty ι`).

Factorwise application of `Projectivization.projector` gives the product projector map
`Projectivization.piProjector` into `(i : ι) → Matrix (κ i) (κ i) K` and its flattened entry form
`Projectivization.piProjectorCoords` into `(Σ i, κ i × κ i) → K`. Over an ordered field it is a
bijection onto the product projector locus `TauCeti.piProjectorLocus`, transports complements as
relative complements inside that locus, and expresses every standard product affine chart in terms
of ratios of matrix entries.

## Main declarations

* `TauCeti.piMatrixLinearEquiv`: the `R`-linear equivalence flattening a family of matrices
  `(i : ι) → Matrix (κ i) (μ i) α` to `(Σ i, κ i × μ i) → α`.
* `Projectivization.piAffineOpen` and `Projectivization.piAffineChart`: the standard product affine
  opens and flattened standard product affine charts of `(i : ι) → ℙ K (Fin (n i + 1) → K)`.
* `TauCeti.piProjectorLocus`, `Projectivization.piProjector` and
  `Projectivization.piProjectorCoords`: the product projector locus and the factorwise and
  flattened product projector maps.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix Set
open scoped LinearAlgebra.Projectivization

namespace TauCeti

section MatrixCoordinates

variable (R : Type*) [Semiring R] {ι : Type*} (κ μ : ι → Type*) (α : Type*)
  [AddCommMonoid α] [Module R α]

/-- Flatten a family of matrices `(i : ι) → Matrix (κ i) (μ i) α` to a single coordinate tuple
indexed by `Σ i, κ i × μ i`, as an `R`-linear equivalence. -/
def piMatrixLinearEquiv :
    ((i : ι) → Matrix (κ i) (μ i) α) ≃ₗ[R] ((p : Σ i, κ i × μ i) → α) where
  toFun A p := A p.1 p.2.1 p.2.2
  invFun a i := Matrix.of fun j k ↦ a ⟨i, j, k⟩
  left_inv A := by
    ext i j k
    rfl
  right_inv a := by
    ext ⟨i, j, k⟩
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem piMatrixLinearEquiv_apply (A : (i : ι) → Matrix (κ i) (μ i) α)
    (p : Σ i, κ i × μ i) :
    piMatrixLinearEquiv R κ μ α A p = A p.1 p.2.1 p.2.2 :=
  (rfl)

@[simp]
theorem piMatrixLinearEquiv_symm_apply (a : (p : Σ i, κ i × μ i) → α)
    (i : ι) (j : κ i) (k : μ i) :
    (piMatrixLinearEquiv R κ μ α).symm a i j k = a ⟨i, j, k⟩ :=
  (rfl)

end MatrixCoordinates

/-- The *product projector locus*: families of matrices `(A i)` in which every factor `A i` is a
symmetric idempotent matrix of trace one. Over an ordered field this is the exact range of
`Projectivization.piProjector`. -/
def piProjectorLocus {ι : Type*} (κ : ι → Type*) (K : Type*) [∀ i, Fintype (κ i)] [Field K] :
    Set ((i : ι) → Matrix (κ i) (κ i) K) :=
  univ.pi fun i ↦ projectorLocus (κ i) K

theorem piProjectorLocus_def {ι : Type*} (κ : ι → Type*) (K : Type*) [∀ i, Fintype (κ i)]
    [Field K] :
    piProjectorLocus κ K = univ.pi fun i ↦ projectorLocus (κ i) K :=
  (rfl)

@[simp]
theorem mem_piProjectorLocus {ι : Type*} {κ : ι → Type*} {K : Type*} [∀ i, Fintype (κ i)]
    [Field K] {A : (i : ι) → Matrix (κ i) (κ i) K} :
    A ∈ piProjectorLocus κ K ↔ ∀ i, A i ∈ projectorLocus (κ i) K := by
  simp [piProjectorLocus]

end TauCeti

namespace Projectivization

open TauCeti

/-! ### Standard product affine opens and charts -/

section PiAffineOpen

variable {K : Type*} [DivisionRing K] {ι : Type*} {κ : ι → Type*}

/-- The standard product affine open of `(i : ι) → ℙ K (κ i → K)` determined by a choice of
coordinate index `I i : κ i` in each factor: the points `p` whose `i`-th factor lies in
`affineOpen (I i)` for every `i`. -/
def piAffineOpen (I : ∀ i, κ i) : Set ((i : ι) → ℙ K (κ i → K)) :=
  univ.pi fun i ↦ affineOpen (I i)

theorem piAffineOpen_def (I : ∀ i, κ i) :
    piAffineOpen (K := K) I = univ.pi fun i ↦ affineOpen (I i) :=
  (rfl)

@[simp]
theorem mem_piAffineOpen_iff {I : ∀ i, κ i} {p : (i : ι) → ℙ K (κ i → K)} :
    p ∈ piAffineOpen I ↔ ∀ i, p i ∈ affineOpen (I i) := by
  simp [piAffineOpen]

theorem mk_mem_piAffineOpen_iff (I : ∀ i, κ i) (v : ∀ i, κ i → K) (hv : ∀ i, v i ≠ 0) :
    (fun i ↦ mk K (v i) (hv i)) ∈ piAffineOpen I ↔ ∀ i, v i (I i) ≠ 0 := by
  simp

/-- Every point of a product of projective spaces lies in some standard product affine open. -/
theorem exists_mem_piAffineOpen (p : (i : ι) → ℙ K (κ i → K)) :
    ∃ I : ∀ i, κ i, p ∈ piAffineOpen I :=
  ⟨fun i ↦ (exists_mem_affineOpen (p i)).choose,
    mem_piAffineOpen_iff.2 fun i ↦ (exists_mem_affineOpen (p i)).choose_spec⟩

/-- The standard product affine opens cover `(i : ι) → ℙ K (κ i → K)`, including when `ι` is
empty. -/
theorem iUnion_piAffineOpen :
    ⋃ I : ∀ i, κ i, piAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.2 (exists_mem_piAffineOpen p)

@[simp]
theorem piAffineOpen_of_isEmpty [IsEmpty ι] (I : ∀ i, κ i) :
    piAffineOpen (K := K) I = univ := by
  ext p
  simp

end PiAffineOpen

section PiAffineChart

variable {K : Type*} [Field K] {ι : Type*} {n : ι → ℕ}

/-- The standard product affine chart of `(i : ι) → ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, flattened to a partial equivalence onto `(Σ i, Fin (n i)) → K`. On
`piAffineOpen I` it sends `p` to `⟨i, k⟩ ↦ affineChart (I i) (p i) k`, and its inverse sends `z` to
`i ↦ (affineChart (I i)).symm (fun k ↦ z ⟨i, k⟩)`. -/
noncomputable def piAffineChart (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv ((i : ι) → ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (PartialEquiv.pi fun i ↦ affineChart (I i)).trans
    (Equiv.piCurry fun (_ : ι) (_ : Fin _) ↦ K).symm.toPartialEquiv

@[simp]
theorem piAffineChart_source (I : ∀ i, Fin (n i + 1)) :
    (piAffineChart (K := K) I).source = piAffineOpen I := by
  ext p
  simp [piAffineChart, PartialEquiv.pi]

@[simp]
theorem piAffineChart_target (I : ∀ i, Fin (n i + 1)) :
    (piAffineChart (K := K) I).target = univ := by
  ext z
  simp [piAffineChart, PartialEquiv.pi]

theorem piAffineChart_apply (I : ∀ i, Fin (n i + 1))
    (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) (q : Σ i, Fin (n i)) :
    piAffineChart I p q = affineChart (I q.1) (p q.1) q.2 :=
  (rfl)

@[simp]
theorem piAffineChart_mk (I : ∀ i, Fin (n i + 1))
    (v : ∀ i, Fin (n i + 1) → K) (hv : ∀ i, v i ≠ 0) (q : Σ i, Fin (n i)) :
    piAffineChart I (fun i ↦ mk K (v i) (hv i)) q =
      v q.1 ((I q.1).succAbove q.2) / v q.1 (I q.1) := by
  rw [piAffineChart_apply, affineChart_mk]

@[simp]
theorem piAffineChart_symm_apply (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (i : ι) :
    (piAffineChart I).symm z i = (affineChart (I i)).symm fun k ↦ z ⟨i, k⟩ :=
  (rfl)

end PiAffineChart

/-! ### The product projector map -/

section PiProjector

variable {ι : Type*} {κ : ι → Type*} {K : Type*} [∀ i, Fintype (κ i)] [Field K]

/-- The factorwise projector map on a product of projective spaces, sending `p` to the family of
rank-one projectors `i ↦ projector (p i)`. -/
def piProjector (p : (i : ι) → ℙ K (κ i → K)) : (i : ι) → Matrix (κ i) (κ i) K :=
  fun i ↦ projector (p i)

theorem piProjector_def :
    (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) =
      fun p i ↦ projector (p i) :=
  (rfl)

@[simp]
theorem piProjector_apply (p : (i : ι) → ℙ K (κ i → K)) (i : ι) :
    piProjector p i = projector (p i) :=
  (rfl)

@[simp]
theorem piProjector_mk (v : ∀ i, κ i → K) (hv : ∀ i, v i ≠ 0) :
    piProjector (fun i ↦ mk K (v i) (hv i)) = fun i ↦ rankOneProjector (v i) := by
  ext i j k
  simp [piProjector]

/-- The product projector map read in flattened matrix coordinates `(Σ i, κ i × κ i) → K`. -/
def piProjectorCoords (p : (i : ι) → ℙ K (κ i → K)) : (Σ i, κ i × κ i) → K :=
  piMatrixLinearEquiv K κ κ K (piProjector p)

theorem piProjectorCoords_def :
    (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) =
      piMatrixLinearEquiv K κ κ K ∘ piProjector :=
  (rfl)

@[simp]
theorem piProjectorCoords_apply (p : (i : ι) → ℙ K (κ i → K)) (q : Σ i, κ i × κ i) :
    piProjectorCoords p q = projector (p q.1) q.2.1 q.2.2 :=
  (rfl)

@[simp]
theorem piMatrixLinearEquiv_symm_piProjectorCoords (p : (i : ι) → ℙ K (κ i → K)) :
    (piMatrixLinearEquiv K κ κ K).symm (piProjectorCoords p) = piProjector p :=
  (piMatrixLinearEquiv K κ κ K).symm_apply_apply (piProjector p)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field, the product projector of every point lies in the product projector
locus. -/
theorem piProjector_mem_piProjectorLocus (p : (i : ι) → ℙ K (κ i → K)) :
    piProjector p ∈ piProjectorLocus κ K :=
  mem_piProjectorLocus.2 fun i ↦ projector_mem_projectorLocus (p i)

/-- Over an ordered field, the product projector map is injective. -/
theorem piProjector_injective :
    Function.Injective
      (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) :=
  fun _ _ h ↦ funext fun i ↦ projector_injective (congr_fun h i)

/-- Over an ordered field, the flattened product projector map is injective. -/
theorem piProjectorCoords_injective :
    Function.Injective (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) :=
  (piMatrixLinearEquiv K κ κ K).injective.comp piProjector_injective

/-- Over an ordered field, the range of `piProjector` is `piProjectorLocus`. -/
@[simp]
theorem range_piProjector :
    range (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) =
      piProjectorLocus κ K := by
  refine Subset.antisymm (range_subset_iff.2 piProjector_mem_piProjectorLocus) fun A hA ↦ ?_
  have hmem := mem_piProjectorLocus.1 hA
  choose p hp using
    fun i ↦ (range_projector (ι := κ i) (K := K) ▸ hmem i : A i ∈ range projector)
  exact ⟨p, funext hp⟩

/-- Over an ordered field, the range of `piProjectorCoords` is the flattened product projector
locus. -/
theorem range_piProjectorCoords :
    range (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) =
      piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K := by
  change range (piMatrixLinearEquiv K κ κ K ∘ piProjector) = _
  rw [range_comp, range_piProjector]

/-- **Complement transport in the product projector locus.** Because `piProjector` is a bijection
onto `piProjectorLocus`, the image of `Sᶜ` is the relative complement of `piProjector '' S` inside
`piProjectorLocus`. -/
theorem image_piProjector_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjector '' Sᶜ = piProjectorLocus κ K \ (piProjector '' S) := by
  rw [← range_piProjector, ← image_univ, ← image_sdiff piProjector_injective, compl_eq_univ_sdiff]

/-- **Complement transport in flattened matrix coordinates.** The image of `Sᶜ` under
`piProjectorCoords` is the relative complement of `piProjectorCoords '' S` inside the flattened
product projector locus. -/
theorem image_piProjectorCoords_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjectorCoords '' Sᶜ =
      (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) \ (piProjectorCoords '' S) := by
  rw [← range_piProjectorCoords, ← image_univ, ← image_sdiff piProjectorCoords_injective,
    compl_eq_univ_sdiff]

/-- The image of a standard product affine open `piAffineOpen I` under `piProjector` consists of
the matrices in `piProjectorLocus` whose `(I i, I i)`-diagonal entry is nonzero for every `i`. -/
theorem image_piProjector_piAffineOpen (I : ∀ i, κ i) :
    piProjector '' piAffineOpen (K := K) I =
      {A ∈ piProjectorLocus κ K | ∀ i, A i (I i) (I i) ≠ 0} := by
  ext A
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨piProjector_mem_piProjectorLocus p, fun i ↦ ?_⟩
    exact projector_apply_self_eq_zero_iff.not.2 (not_not.2 (mem_piAffineOpen_iff.1 hp i))
  · rintro ⟨hA, hdiag⟩
    obtain ⟨p, rfl⟩ := range_piProjector (κ := κ) (K := K) ▸ hA
    refine ⟨p, mem_piAffineOpen_iff.2 fun i ↦ ?_, rfl⟩
    exact not_not.1 (projector_apply_self_eq_zero_iff.not.1 (hdiag i))

omit [∀ i, Fintype (κ i)] in
/-- The standard product affine chart `piAffineChart I` reads off the coordinates of `p` from its
product projector entries as the ratios `A ⟨i, (I i).succAbove k, I i⟩ / A ⟨i, I i, I i⟩`. -/
theorem piAffineChart_eq_piProjectorCoords_div {n : ι → ℕ} (I : ∀ i, Fin (n i + 1))
    (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) :
    piAffineChart I p = fun q ↦
      piProjectorCoords p ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ /
        piProjectorCoords p ⟨q.1, I q.1, I q.1⟩ := by
  funext ⟨i, k⟩
  exact congr_fun (affineChart_eq_projector_div (I i) (p i)) k

end PiProjector

end Projectivization
