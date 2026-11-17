/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.Projectivization.Projector

/-!
# Products of projective spaces

A multiprojective space `(i : ι) → ℙ K (κ i → K)` is a product of projective spaces over a field
(or division ring) `K`. To apply affine coordinate methods—such as multivariate polynomials,
semialgebraic sets and affine charts—to such a product, we work with the flattened punctured
multicone `TauCeti.piConeDomain` and `TauCeti.piConePreimage` in `(Σ i, κ i) → K`, flatten
standard product affine chart coordinates via `(Equiv.piCurry _).symm`, and flatten families of
projectors `(i : ι) → Matrix (κ i) (κ i) K` to `(Σ i, κ i × κ i) → K` via
`TauCeti.piMatrixLinearEquiv`.

For `κ i = Fin (n i + 1)`, each choice of coordinate indices `I : ∀ i, Fin (n i + 1)` picks out the
standard product affine open `Projectivization.piAffineOpen I = {p | ∀ i, p i ∈ affineOpen (I i)}`
and the standard product affine chart `Projectivization.piAffineChart I`, a partial equivalence onto
the flattened affine coordinate space `(Σ i, Fin (n i)) → K`. These opens cover the product,
including in the empty product case (`IsEmpty ι`).

Factorwise application of `Projectivization.projector` gives the product projector map
`Projectivization.piProjector` into `(i : ι) → Matrix (κ i) (κ i) K` and its flattened entry form
`Projectivization.piProjectorCoords` into `(Σ i, κ i × κ i) → K`. Over an ordered field it is a
bijection onto the product projector locus `TauCeti.piProjectorLocus`, recovers each factor from any
row with nonzero diagonal entry (`Projectivization.mk_piProjectorCoords_row_eq`), transports
complements as relative complements inside that locus, and expresses every standard product affine
chart in terms of ratios of matrix entries.

## Main declarations

* `Projectivization.piAffineOpen` and `Projectivization.piAffineChart`: the standard product affine
  opens and flattened standard product affine charts of `(i : ι) → ℙ K (Fin (n i + 1) → K)`.
* `TauCeti.piConeDomain` and `TauCeti.piConePreimage`: the flattened punctured multicone and
  preimage of a multiprojective subset in `(Σ i, κ i) → K`.
* `TauCeti.piProjectorLocus`, `Projectivization.piProjector` and
  `Projectivization.piProjectorCoords`: the product projector locus and the factorwise and
  flattened product projector maps.
* `Projectivization.mk_piProjectorCoords_row_eq`: factor recovery from a nonzero-diagonal row of
  `piProjectorCoords`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-! ### Standard product affine opens and charts -/

section PiAffineOpen

variable {K : Type*} [DivisionRing K] {ι : Type*} {κ : ι → Type*}

/-- The standard product affine open of `(i : ι) → ℙ K (κ i → K)` determined by a choice of
coordinate index `I i : κ i` in each factor: the points `p` whose `i`-th factor lies in
`affineOpen (I i)` for every `i`. -/
def piAffineOpen (I : ∀ i, κ i) : Set ((i : ι) → ℙ K (κ i → K)) :=
  univ.pi fun i ↦ affineOpen (I i)

theorem piAffineOpen_def (I : ∀ i, κ i) :
    piAffineOpen (K := K) I = univ.pi fun i ↦ affineOpen (I i) := (rfl)

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
theorem iUnion_piAffineOpen : ⋃ I : ∀ i, κ i, piAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.2 (exists_mem_piAffineOpen p)

@[simp]
theorem piAffineOpen_of_isEmpty [IsEmpty ι] (I : ∀ i, κ i) :
    piAffineOpen (K := K) I = univ := by
  ext p; simp

end PiAffineOpen

section PiAffineChart

variable {K : Type*} [Field K] {ι : Type*} {n : ι → ℕ}

/-- The standard product affine chart of `(i : ι) → ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, flattened to a partial equivalence onto `(Σ i, Fin (n i)) → K`. On
`piAffineOpen I` it sends `p` to `⟨i, k⟩ ↦ affineChart (I i) (p i) k`, and its inverse sends `z` to
`i ↦ (affineChart (I i)).symm (fun k ↦ z ⟨i, k⟩)`. -/
noncomputable def piAffineChart (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv ((i : ι) → ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (PartialEquiv.pi fun i ↦ affineChart (I i)).transEquiv
    (Equiv.piCurry fun (_ : ι) (_ : Fin _) ↦ K).symm

@[simp]
theorem piAffineChart_source (I : ∀ i, Fin (n i + 1)) :
    (piAffineChart (K := K) I).source = piAffineOpen I := by
  ext p; simp [piAffineChart, PartialEquiv.pi]

@[simp]
theorem piAffineChart_target (I : ∀ i, Fin (n i + 1)) :
    (piAffineChart (K := K) I).target = univ := by
  ext z; simp [piAffineChart, PartialEquiv.pi]

@[simp]
theorem piAffineChart_apply (I : ∀ i, Fin (n i + 1))
    (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) (q : Σ i, Fin (n i)) :
    piAffineChart I p q = affineChart (I q.1) (p q.1) q.2 := by
  simp [piAffineChart, Sigma.uncurry]

@[simp]
theorem piAffineChart_mk (I : ∀ i, Fin (n i + 1))
    (v : ∀ i, Fin (n i + 1) → K) (hv : ∀ i, v i ≠ 0) :
    piAffineChart I (fun i ↦ mk K (v i) (hv i)) =
      fun q ↦ v q.1 ((I q.1).succAbove q.2) / v q.1 (I q.1) := by
  ext q; simp [affineChart_mk]

@[simp]
theorem piAffineChart_symm_apply (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (i : ι) :
    (piAffineChart I).symm z i = (affineChart (I i)).symm fun k ↦ z ⟨i, k⟩ := by
  simp only [piAffineChart, PartialEquiv.transEquiv, PartialEquiv.coe_trans_symm,
    Equiv.toPartialEquiv_symm_apply, Equiv.symm_symm, PartialEquiv.pi_symm, PartialEquiv.pi_apply]
  exact congrArg _ (funext fun k ↦ by simp [Sigma.curry])

end PiAffineChart

end Projectivization

namespace TauCeti

/-! ### Punctured multicone and cone preimages -/

section Cone

open Projectivization

variable {ι : Type*} {κ : ι → Type*}

/-- The flattened punctured-cone domain of `(i : ι) → ℙ K (κ i → K)`: tuples
`v : (Σ i, κ i) → K` whose `i`-th block `j ↦ v ⟨i, j⟩` is nonzero for every `i`. -/
def piConeDomain (κ : ι → Type*) (K : Type*) [Zero K] : Set ((Σ i, κ i) → K) :=
  {v | ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0}

theorem piConeDomain_def (κ : ι → Type*) (K : Type*) [Zero K] :
    piConeDomain κ K = {v | ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0} := (rfl)

@[simp]
theorem mem_piConeDomain_iff {K : Type*} [Zero K] {v : (Σ i, κ i) → K} :
    v ∈ piConeDomain κ K ↔ ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0 := Iff.rfl

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- The preimage of a subset `S` of `(i : ι) → ℙ K (κ i → K)` under the product of punctured-vector
quotient maps, viewed in the flattened coordinate space `(Σ i, κ i) → K`. -/
def piConePreimage (S : Set ((i : ι) → ℙ K (κ i → K))) : Set ((Σ i, κ i) → K) :=
  {v | ∃ hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0, (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S}

theorem piConePreimage_def (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage S =
      {v | ∃ hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0, (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S} :=
  (rfl)

@[simp]
theorem mem_piConePreimage_iff {S : Set ((i : ι) → ℙ K (κ i → K))} {v : (Σ i, κ i) → K} :
    v ∈ piConePreimage S ↔
      ∃ hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0, (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S :=
  Iff.rfl

theorem mk_mem_iff_mem_piConePreimage {S : Set ((i : ι) → ℙ K (κ i → K))}
    {v : (Σ i, κ i) → K} (hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0) :
    (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S ↔ v ∈ piConePreimage S :=
  ⟨fun h ↦ ⟨hv, h⟩, fun ⟨_, h⟩ ↦ h⟩

theorem piConePreimage_subset_piConeDomain (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage S ⊆ piConeDomain κ K :=
  fun _ ⟨hv, _⟩ ↦ hv

@[simp]
theorem piConePreimage_empty :
    piConePreimage (∅ : Set ((i : ι) → ℙ K (κ i → K))) = ∅ := by
  ext v; simp

@[simp]
theorem piConePreimage_univ :
    piConePreimage (univ : Set ((i : ι) → ℙ K (κ i → K))) = piConeDomain κ K := by
  ext v; simp

@[simp]
theorem piConePreimage_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage Sᶜ = piConeDomain κ K \ piConePreimage S := by
  ext v; simp only [mem_piConePreimage_iff, mem_compl_iff, mem_sdiff, mem_piConeDomain_iff]
  exact ⟨fun ⟨hv, hS⟩ ↦ ⟨hv, fun ⟨_, h⟩ ↦ hS h⟩, fun ⟨hv, hS⟩ ↦ ⟨hv, fun h ↦ hS ⟨hv, h⟩⟩⟩

@[simp]
theorem piConePreimage_union (S T : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (S ∪ T) = piConePreimage S ∪ piConePreimage T := by
  ext v; simp only [mem_piConePreimage_iff, mem_union]
  exact ⟨fun ⟨hv, h⟩ ↦ h.imp (fun hS ↦ ⟨hv, hS⟩) (fun hT ↦ ⟨hv, hT⟩),
    fun h ↦ h.elim (fun ⟨hv, hS⟩ ↦ ⟨hv, Or.inl hS⟩) (fun ⟨hv, hT⟩ ↦ ⟨hv, Or.inr hT⟩)⟩

@[simp]
theorem piConePreimage_inter (S T : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (S ∩ T) = piConePreimage S ∩ piConePreimage T := by
  ext v; simp only [mem_piConePreimage_iff, mem_inter_iff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, ⟨hv, hT⟩⟩, fun ⟨⟨hv, hS⟩, ⟨_, hT⟩⟩ ↦ ⟨hv, hS, hT⟩⟩

@[simp]
theorem piConePreimage_sdiff (S T : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (S \ T) = piConePreimage S \ piConePreimage T := by
  ext v; simp only [mem_piConePreimage_iff, mem_sdiff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, fun ⟨_, h⟩ ↦ hT h⟩,
    fun ⟨⟨hv, hS⟩, hT⟩ ↦ ⟨hv, hS, fun h ↦ hT ⟨hv, h⟩⟩⟩

@[simp]
theorem piConePreimage_iUnion {α : Type*} (S : α → Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (⋃ a, S a) = ⋃ a, piConePreimage (S a) := by
  ext v; simp only [mem_piConePreimage_iff, mem_iUnion]
  exact ⟨fun ⟨hv, a, ha⟩ ↦ ⟨a, hv, ha⟩, fun ⟨a, hv, ha⟩ ↦ ⟨hv, a, ha⟩⟩

theorem piConePreimage_mono {S T : Set ((i : ι) → ℙ K (κ i → K))} (h : S ⊆ T) :
    piConePreimage S ⊆ piConePreimage T := fun _ ⟨hv, hS⟩ ↦ ⟨hv, h hS⟩

@[simp]
theorem piConePreimage_subset_piConePreimage_iff {S T : Set ((i : ι) → ℙ K (κ i → K))} :
    piConePreimage S ⊆ piConePreimage T ↔ S ⊆ T := by
  refine ⟨fun h p hpS ↦ ?_, piConePreimage_mono⟩
  have hv : ∀ i, (fun j ↦ (p i).rep j) ≠ 0 := fun i ↦ (p i).rep_ne_zero
  have hpv : (fun i ↦ mk K (fun j ↦ (p i).rep j) (hv i)) = p := funext fun i ↦ (p i).mk_rep
  obtain ⟨_, hT⟩ := h (a := fun q ↦ (p q.1).rep q.2) ⟨hv, hpv.symm ▸ hpS⟩
  rwa [hpv] at hT

theorem piConePreimage_injective :
    Function.Injective (piConePreimage (K := K) (κ := κ)) :=
  fun _ _ h ↦ Subset.antisymm (piConePreimage_subset_piConePreimage_iff.1 h.subset)
    (piConePreimage_subset_piConePreimage_iff.1 h.symm.subset)

@[simp]
theorem piConePreimage_inj {S T : Set ((i : ι) → ℙ K (κ i → K))} :
    piConePreimage S = piConePreimage T ↔ S = T :=
  piConePreimage_injective.eq_iff

@[simp]
theorem piConePreimage_piAffineOpen (I : ∀ i, κ i) :
    piConePreimage (piAffineOpen (K := K) I) = {v | ∀ i, v ⟨i, I i⟩ ≠ 0} := by
  ext v
  simp only [mem_piConePreimage_iff, mem_piAffineOpen_iff, mk_mem_affineOpen_iff, mem_ofPred_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨fun i h0 ↦ h i (congr_fun h0 (I i)), h⟩⟩

end DivisionRing

end Cone

/-! ### Product projector locus -/

/-- The *product projector locus*: families of matrices `(A i)` in which every factor `A i` is a
symmetric idempotent matrix of trace one. Over an ordered field this is the exact range of
`Projectivization.piProjector`. -/
def piProjectorLocus {ι : Type*} (κ : ι → Type*) (K : Type*) [∀ i, Fintype (κ i)] [Field K] :
    Set ((i : ι) → Matrix (κ i) (κ i) K) :=
  univ.pi fun i ↦ projectorLocus (κ i) K

theorem piProjectorLocus_def {ι : Type*} (κ : ι → Type*) (K : Type*) [∀ i, Fintype (κ i)]
    [Field K] : piProjectorLocus κ K = univ.pi fun i ↦ projectorLocus (κ i) K := (rfl)

@[simp]
theorem mem_piProjectorLocus {ι : Type*} {κ : ι → Type*} {K : Type*} [∀ i, Fintype (κ i)]
    [Field K] {A : (i : ι) → Matrix (κ i) (κ i) K} :
    A ∈ piProjectorLocus κ K ↔ ∀ i, A i ∈ projectorLocus (κ i) K := by
  simp [piProjectorLocus]

end TauCeti

namespace Projectivization

open TauCeti

/-! ### The product projector map -/

section PiProjector

variable {ι : Type*} {κ : ι → Type*} {K : Type*} [∀ i, Fintype (κ i)] [Field K]

/-- The factorwise projector map on a product of projective spaces, sending `p` to the family of
rank-one projectors `i ↦ projector (p i)`. -/
def piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K :=
  Pi.map fun _ ↦ projector

theorem piProjector_def :
    (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) =
      Pi.map fun _ ↦ projector := (rfl)

@[simp]
theorem piProjector_apply (p : (i : ι) → ℙ K (κ i → K)) (i : ι) :
    piProjector p i = projector (p i) := by
  simp [piProjector]

@[simp]
theorem piProjector_mk (v : ∀ i, κ i → K) (hv : ∀ i, v i ≠ 0) :
    piProjector (fun i ↦ mk K (v i) (hv i)) = fun i ↦ rankOneProjector (v i) := by
  ext i j k; simp [piProjector]

/-- The product projector map read in flattened matrix coordinates `(Σ i, κ i × κ i) → K`. -/
def piProjectorCoords (p : (i : ι) → ℙ K (κ i → K)) : (Σ i, κ i × κ i) → K :=
  piMatrixLinearEquiv K κ κ K (piProjector p)

theorem piProjectorCoords_def :
    (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) =
      piMatrixLinearEquiv K κ κ K ∘ piProjector := (rfl)

@[simp]
theorem piProjectorCoords_apply (p : (i : ι) → ℙ K (κ i → K)) (q : Σ i, κ i × κ i) :
    piProjectorCoords p q = projector (p q.1) q.2.1 q.2.2 := by
  simp [piProjectorCoords]

@[simp]
theorem piMatrixLinearEquiv_piProjector (p : (i : ι) → ℙ K (κ i → K)) :
    piMatrixLinearEquiv K κ κ K (piProjector p) = piProjectorCoords p := (rfl)

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

/-- Over an ordered field, the flattened product projector of every point lies in the flattened
product projector locus. -/
theorem piProjectorCoords_mem_image_piProjectorLocus (p : (i : ι) → ℙ K (κ i → K)) :
    piProjectorCoords p ∈ piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K :=
  ⟨piProjector p, piProjector_mem_piProjectorLocus p, rfl⟩

/-- Over an ordered field, the product projector map is injective. -/
theorem piProjector_injective :
    Function.Injective
      (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) :=
  Function.Injective.piMap fun _ ↦ projector_injective

/-- Over an ordered field, the flattened product projector map is injective. -/
theorem piProjectorCoords_injective :
    Function.Injective (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) :=
  (piMatrixLinearEquiv K κ κ K).injective.comp piProjector_injective

/-- Over an ordered field, the range of `piProjector` is `piProjectorLocus`. -/
@[simp]
theorem range_piProjector :
    range (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) =
      piProjectorLocus κ K := by
  rw [piProjector_def, Set.range_piMap]; simp [piProjectorLocus, range_projector]

/-- Over an ordered field, the range of `piProjectorCoords` is the flattened product projector
locus. -/
@[simp]
theorem range_piProjectorCoords :
    range (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) =
      piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K := by
  rw [piProjectorCoords_def, range_comp, range_piProjector]

/-- **Complement transport in the product projector locus.** Because `piProjector` is a bijection
onto `piProjectorLocus`, the image of `Sᶜ` is the relative complement of `piProjector '' S` inside
`piProjectorLocus`. -/
theorem image_piProjector_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjector '' Sᶜ = piProjectorLocus κ K \ (piProjector '' S) := by
  rw [Set.image_compl_eq_range_sdiff_image piProjector_injective, range_piProjector]

/-- **Complement transport in flattened matrix coordinates.** The image of `Sᶜ` under
`piProjectorCoords` is the relative complement of `piProjectorCoords '' S` inside the flattened
product projector locus. -/
theorem image_piProjectorCoords_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjectorCoords '' Sᶜ =
      (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) \ (piProjectorCoords '' S) := by
  rw [Set.image_compl_eq_range_sdiff_image piProjectorCoords_injective, range_piProjectorCoords]

/-- The image of a standard product affine open `piAffineOpen I` under `piProjector` consists of
the matrices in `piProjectorLocus` whose `(I i, I i)`-diagonal entry is nonzero for every `i`. -/
theorem image_piProjector_piAffineOpen (I : ∀ i, κ i) :
    piProjector '' piAffineOpen (K := K) I =
      {A ∈ piProjectorLocus κ K | ∀ i, A i (I i) (I i) ≠ 0} := by
  rw [piProjector_def, piAffineOpen_def, Set.piMap_image_univ_pi]
  ext A; simp [image_projector_affineOpen, mem_piProjectorLocus, forall_and]

/-- The image of a standard product affine open `piAffineOpen I` under `piProjectorCoords` consists
of the points of the flattened product projector locus whose `(i, I i, I i)`-entry is nonzero for
every `i`. -/
theorem image_piProjectorCoords_piAffineOpen (I : ∀ i, κ i) :
    piProjectorCoords '' piAffineOpen (K := K) I =
      {a ∈ piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K | ∀ i, a ⟨i, I i, I i⟩ ≠ 0} := by
  rw [piProjectorCoords_def, image_comp, image_piProjector_piAffineOpen]
  ext a
  constructor
  · rintro ⟨A, ⟨hA, hdiag⟩, rfl⟩; exact ⟨⟨A, hA, rfl⟩, fun i ↦ by simpa using hdiag i⟩
  · rintro ⟨⟨A, hA, rfl⟩, hdiag⟩; exact ⟨A, ⟨hA, fun i ↦ by simpa using hdiag i⟩, rfl⟩

/-- Recovering the `i`-th projective factor from a row of `piProjectorCoords p` whose diagonal
entry is nonzero. -/
theorem mk_piProjectorCoords_row_eq {i : ι} (p : (i : ι) → ℙ K (κ i → K)) {r : κ i}
    (hr : projector (p i) r r ≠ 0) (hv : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) ≠ 0) :
    mk K (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) hv = p i := by
  have hrow : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) = projector (p i) r :=
    funext fun j ↦ piProjectorCoords_apply p ⟨i, r, j⟩
  simpa only [hrow] using mk_projector_row (p i) hr (hrow ▸ hv)

omit [∀ i, Fintype (κ i)] in
/-- The standard product affine chart `piAffineChart I` reads off the coordinates of `p` from its
product projector entries as the ratios `A ⟨i, (I i).succAbove k, I i⟩ / A ⟨i, I i, I i⟩`. -/
theorem piAffineChart_eq_piProjectorCoords_div {n : ι → ℕ} (I : ∀ i, Fin (n i + 1))
    (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) :
    piAffineChart I p = fun q ↦
      piProjectorCoords p ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ /
        piProjectorCoords p ⟨q.1, I q.1, I q.1⟩ := by
  funext ⟨i, k⟩
  simp only [piAffineChart_apply, piProjectorCoords_apply]
  exact congr_fun (affineChart_eq_projector_div (I i) (p i)) k

end PiProjector

end Projectivization
