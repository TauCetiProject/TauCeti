/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.PiCurry
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Rational

/-!
# Semialgebraic sets in multiprojective and mixed affine–multiprojective spaces

Let `K` be a linearly ordered field and `M = ∀ i : ι, ℙ K (Fin (n i + 1) → K)` be a finite product
of projective spaces, or more generally `(σ → K) × M` its product with an affine coordinate space.
This file develops the standard product affine charts of `M` and `(σ → K) × M` and the basic
theory of semialgebraic subsets of these spaces.

Homogeneous representatives `(i : ι) → Fin (n i + 1) → K` flatten via `Equiv.piCurry` to the
single coordinate space `(Σ i, Fin (n i + 1)) → K` (and for `ι = Fin m`, further to
`Fin (∑ i, (n i + 1)) → K` via `finSigmaFinEquiv`). A subset `S ⊆ M` is *multiprojective
semialgebraic* (`TauCeti.IsMultiprojectiveSemialgebraic`) when its punctured-cone preimage
`TauCeti.multiprojectiveCone S` in `(Σ i, Fin (n i + 1)) → K` is semialgebraic; likewise a subset
`S ⊆ (σ → K) × M` is *mixed semialgebraic* (`TauCeti.IsMixedSemialgebraic`) when its cone preimage
`TauCeti.mixedCone S` in `(σ ⊕ Σ i, Fin (n i + 1)) → K` is semialgebraic. Both definitions
include the empty product `[IsEmpty ι]` (such as `ι = Fin 0`).

Over any strict ordered field (`[IsStrictOrderedRing K]`) and finite factor index `[Finite ι]`,
cone semialgebraicity is equivalent to global semialgebraicity in every standard product affine
chart (`TauCeti.isMixedSemialgebraic_iff_forall_chart`,
`TauCeti.isMultiprojectiveSemialgebraic_iff_forall_chart`), without assuming projection closure:
inverse charts are polynomial in homogeneous coordinates, while the standard charts are rational
with nonvanishing denominators on the corresponding coordinate opens. Local-to-global criteria
over `ℝ` (`TauCeti.SemialgebraicAt`) are proved in
`TauCeti.Geometry.RealAlgebraic.Multiprojective.Local`.

## Main declarations

* `TauCeti.multiprojectiveAffineOpen`, `TauCeti.multiprojectiveAffineChart`,
  `TauCeti.multiprojectiveAffineOpenPartialHomeomorph`: standard product affine opens and charts of
  `∀ i : ι, ℙ K (Fin (n i + 1) → K)`, flattened to `(Σ i, Fin (n i)) → K`.
* `TauCeti.mixedAffineOpen`, `TauCeti.mixedAffineChart`,
  `TauCeti.mixedAffineOpenPartialHomeomorph`: standard product affine opens and charts of
  `(σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K)`, flattened to `(σ ⊕ Σ i, Fin (n i)) → K`.
* `TauCeti.multiprojectiveCone`, `TauCeti.mixedCone`: punctured-cone preimages in flattened
  homogeneous coordinates.
* `TauCeti.IsMultiprojectiveSemialgebraic`, `TauCeti.IsMixedSemialgebraic`: semialgebraic subsets
  of multiprojective and mixed affine–multiprojective spaces, with `MeasureTheory.IsSetAlgebra`,
  Boolean closure, and singletons (`TauCeti.isMultiprojectiveSemialgebraic_singleton`,
  `TauCeti.isMixedSemialgebraic_singleton`).
* `TauCeti.multiprojectiveInsertNthPoly`: flattened homogeneous coordinate polynomials representing
  `(TauCeti.multiprojectiveAffineChart I).symm`.
* `TauCeti.isMixedSemialgebraic_iff_forall_chart`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_chart`: equivalence of cone and chart
  semialgebraicity over any strict ordered field.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Chapter 2 and Section 3.4.
-/

public section

open MeasureTheory MvPolynomial Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Standard product affine opens and charts -/

section AffineOpen

variable {ι σ K : Type*} [DivisionRing K] {α : ι → Type*}

/-- The standard product affine open of a multiprojective space associated to homogeneous
coordinate indices `I : ∀ i, α i`: the locus where the `I i`-th homogeneous coordinate of the
`i`-th factor is nonzero for every `i`. -/
def multiprojectiveAffineOpen (I : ∀ i, α i) :
    Set (∀ i, ℙ K (α i → K)) :=
  {p | ∀ i, p i ∈ Projectivization.affineOpen (I i)}

@[simp]
theorem mem_multiprojectiveAffineOpen {I : ∀ i, α i}
    {p : ∀ i, ℙ K (α i → K)} :
    p ∈ multiprojectiveAffineOpen I ↔ ∀ i, p i ∈ Projectivization.affineOpen (I i) :=
  Iff.rfl

/-- `TauCeti.multiprojectiveAffineOpen` as `Set.pi` over `Set.univ`. -/
theorem multiprojectiveAffineOpen_eq_univ_pi (I : ∀ i, α i) :
    multiprojectiveAffineOpen (K := K) I = univ.pi fun i ↦ Projectivization.affineOpen (I i) := by
  ext p
  simp

/-- Every point of a multiprojective space lies in some standard product affine open. -/
theorem exists_mem_multiprojectiveAffineOpen (p : ∀ i, ℙ K (α i → K)) :
    ∃ I, p ∈ multiprojectiveAffineOpen I := by
  choose I hI using fun i ↦ Projectivization.exists_mem_affineOpen (p i)
  exact ⟨I, hI⟩

/-- The standard product affine opens cover multiprojective space. -/
theorem iUnion_multiprojectiveAffineOpen :
    ⋃ I : ∀ i, α i, multiprojectiveAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.2 (exists_mem_multiprojectiveAffineOpen p)

/-- On an empty product of projective spaces, every standard product affine open is the whole
space. -/
@[simp]
theorem multiprojectiveAffineOpen_eq_univ [IsEmpty ι] (I : ∀ i, α i) :
    multiprojectiveAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun _ i ↦ isEmptyElim i

/-- The standard product affine open of a mixed affine–multiprojective space
`(σ → K) × ∀ i, ℙ K (α i → K)` at `I : ∀ i, α i`. -/
def mixedAffineOpen (σ : Type*) (I : ∀ i, α i) :
    Set ((σ → K) × ∀ i, ℙ K (α i → K)) :=
  univ ×ˢ multiprojectiveAffineOpen I

@[simp]
theorem mem_mixedAffineOpen {I : ∀ i, α i}
    {x : (σ → K) × ∀ i, ℙ K (α i → K)} :
    x ∈ mixedAffineOpen σ I ↔ x.2 ∈ multiprojectiveAffineOpen I := by
  simp [mixedAffineOpen]

/-- Every point of a mixed affine–multiprojective space lies in some standard product affine
open. -/
theorem exists_mem_mixedAffineOpen (x : (σ → K) × ∀ i, ℙ K (α i → K)) :
    ∃ I, x ∈ mixedAffineOpen σ I := by
  obtain ⟨I, hI⟩ := exists_mem_multiprojectiveAffineOpen x.2
  exact ⟨I, mem_mixedAffineOpen.2 hI⟩

section Open

variable [TopologicalSpace K] [T1Space K] [Finite ι]

/-- In a finite product of projective spaces, each standard product affine open is open. -/
theorem isOpen_multiprojectiveAffineOpen (I : ∀ i, α i) :
    IsOpen (multiprojectiveAffineOpen (K := K) I) := by
  rw [multiprojectiveAffineOpen_eq_univ_pi]
  exact isOpen_set_pi finite_univ fun i _ ↦ Projectivization.isOpen_affineOpen (I i)

/-- In a mixed affine–multiprojective space with finitely many projective factors, each standard
product affine open is open. -/
theorem isOpen_mixedAffineOpen (I : ∀ i, α i) :
    IsOpen (mixedAffineOpen (K := K) σ I) :=
  isOpen_univ.prod (isOpen_multiprojectiveAffineOpen I)

end Open

end AffineOpen

section Charts

variable {ι σ K : Type*} [Field K] {n : ι → ℕ}

/-- The standard product affine chart of `∀ i, ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, with coordinates flattened to `(Σ i, Fin (n i)) → K` via
`Equiv.piCurry`. -/
noncomputable def multiprojectiveAffineChart (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv (∀ i, ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (PartialEquiv.pi fun i ↦ Projectivization.affineChart (K := K) (I i)).transEquiv
    (Equiv.piCurry fun i (_ : Fin (n i)) ↦ K).symm

@[simp]
theorem multiprojectiveAffineChart_source (I : ∀ i, Fin (n i + 1)) :
    (multiprojectiveAffineChart (K := K) I).source = multiprojectiveAffineOpen I := by
  ext p
  simp [multiprojectiveAffineChart]

@[simp]
theorem multiprojectiveAffineChart_target (I : ∀ i, Fin (n i + 1)) :
    (multiprojectiveAffineChart (K := K) I).target = univ := by
  ext z
  simp [multiprojectiveAffineChart]

@[simp]
theorem multiprojectiveAffineChart_apply (I : ∀ i, Fin (n i + 1))
    (p : ∀ i, ℙ K (Fin (n i + 1) → K)) (q : Σ i, Fin (n i)) :
    multiprojectiveAffineChart I p q = Projectivization.affineChart (I q.1) (p q.1) q.2 :=
  (rfl)

@[simp]
theorem multiprojectiveAffineChart_symm_apply (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (i : ι) :
    (multiprojectiveAffineChart I).symm z i =
      (Projectivization.affineChart (I i)).symm (fun k ↦ z ⟨i, k⟩) :=
  (rfl)

/-- The inverse of a standard product affine chart takes values in its affine open. -/
theorem multiprojectiveAffineChart_symm_mem_affineOpen (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) :
    (multiprojectiveAffineChart I).symm z ∈ multiprojectiveAffineOpen I := by
  intro i
  simp [multiprojectiveAffineChart_symm_apply]

/-- The standard product affine chart image of `S ∩ multiprojectiveAffineOpen I` is the
inverse-chart preimage of `S`. -/
theorem multiprojectiveAffineChart_image_inter_affineOpen
    (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) (I : ∀ i, Fin (n i + 1)) :
    multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I) =
      (multiprojectiveAffineChart I).symm ⁻¹' S := by
  rw [inter_comm, ← multiprojectiveAffineChart_source,
    (multiprojectiveAffineChart I).image_source_inter_eq', multiprojectiveAffineChart_target,
    univ_inter]

/-- The source of the transition map from chart `I` to chart `J` consists of the flattened
coordinates `z` for which `Fin.insertNth (I i) 1 (fun k ↦ z ⟨i, k⟩) (J i) ≠ 0` for every `i`. -/
theorem multiprojectiveAffineChart_symm_trans_source (I J : ∀ i, Fin (n i + 1)) :
    ((multiprojectiveAffineChart (K := K) I).symm.trans (multiprojectiveAffineChart J)).source =
      {z | ∀ i, Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) (J i) ≠ 0} := by
  ext z
  simp

/-- Formula for the transition map between two standard product affine charts. -/
theorem multiprojectiveAffineChart_symm_trans_apply (I J : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (q : Σ i, Fin (n i)) :
    (multiprojectiveAffineChart I).symm.trans (multiprojectiveAffineChart J) z q =
      Fin.insertNth (α := fun _ ↦ K) (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩) ((J q.1).succAbove q.2) /
        Fin.insertNth (α := fun _ ↦ K) (I q.1) 1 (fun k ↦ z ⟨q.1, k⟩) (J q.1) := by
  simp [PartialEquiv.trans_apply]

/-- The standard product affine chart of `(σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, flattened to `(σ ⊕ Σ i, Fin (n i)) → K`. -/
noncomputable def mixedAffineChart (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) ((σ ⊕ Σ i, Fin (n i)) → K) :=
  ((PartialEquiv.refl (σ → K)).prod (multiprojectiveAffineChart I)).transEquiv
    (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i)) K).symm

@[simp]
theorem mixedAffineChart_source (I : ∀ i, Fin (n i + 1)) :
    (mixedAffineChart (K := K) σ I).source = mixedAffineOpen σ I := by
  ext x
  simp [mixedAffineChart, mixedAffineOpen]

@[simp]
theorem mixedAffineChart_target (I : ∀ i, Fin (n i + 1)) :
    (mixedAffineChart (K := K) σ I).target = univ := by
  ext z
  simp [mixedAffineChart]

theorem mixedAffineChart_apply (I : ∀ i, Fin (n i + 1))
    (x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :
    mixedAffineChart σ I x = Sum.elim x.1 (multiprojectiveAffineChart I x.2) :=
  (rfl)

@[simp]
theorem mixedAffineChart_apply_inl (I : ∀ i, Fin (n i + 1))
    (x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) (a : σ) :
    mixedAffineChart σ I x (.inl a) = x.1 a :=
  (rfl)

@[simp]
theorem mixedAffineChart_apply_inr (I : ∀ i, Fin (n i + 1))
    (x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) (q : Σ i, Fin (n i)) :
    mixedAffineChart σ I x (.inr q) = multiprojectiveAffineChart I x.2 q :=
  (rfl)

@[simp]
theorem mixedAffineChart_symm_apply (I : ∀ i, Fin (n i + 1))
    (z : (σ ⊕ Σ i, Fin (n i)) → K) :
    (mixedAffineChart σ I).symm z =
      (z ∘ Sum.inl, (multiprojectiveAffineChart I).symm (z ∘ Sum.inr)) :=
  (rfl)

/-- The inverse of a mixed product affine chart takes values in its affine open. -/
theorem mixedAffineChart_symm_mem_affineOpen (I : ∀ i, Fin (n i + 1))
    (z : (σ ⊕ Σ i, Fin (n i)) → K) :
    (mixedAffineChart σ I).symm z ∈ mixedAffineOpen σ I := by
  simp

/-- The mixed product affine chart image of `S ∩ mixedAffineOpen σ I` is the inverse-chart preimage
of `S`. -/
theorem mixedAffineChart_image_inter_affineOpen
    (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) (I : ∀ i, Fin (n i + 1)) :
    mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I) =
      (mixedAffineChart σ I).symm ⁻¹' S := by
  rw [inter_comm, ← mixedAffineChart_source, (mixedAffineChart σ I).image_source_inter_eq',
    mixedAffineChart_target, univ_inter]

/-- The mixed product affine chart image of `(univ ×ˢ S) ∩ mixedAffineOpen σ I` is the preimage
under `w ↦ w ∘ Sum.inr` of the multiprojective chart image of `S ∩ multiprojectiveAffineOpen I`. -/
theorem mixedAffineChart_image_univ_prod_inter_affineOpen
    (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) (I : ∀ i, Fin (n i + 1)) :
    mixedAffineChart σ I '' ((univ : Set (σ → K)) ×ˢ S ∩ mixedAffineOpen σ I) =
      (fun w : (σ ⊕ Σ i, Fin (n i)) → K ↦ w ∘ Sum.inr) ⁻¹'
        (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I)) := by
  rw [mixedAffineChart_image_inter_affineOpen, multiprojectiveAffineChart_image_inter_affineOpen]
  ext w
  simp

section Topology

variable [TopologicalSpace K]

/-- The inverse of a standard product affine chart is continuous. -/
theorem continuous_multiprojectiveAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    Continuous (multiprojectiveAffineChart (K := K) I).symm :=
  continuous_pi fun i ↦ (Projectivization.continuous_affineChart_symm (I i)).comp
    (continuous_pi fun k ↦ continuous_apply (⟨i, k⟩ : Σ i, Fin (n i)))

/-- The inverse of a mixed product affine chart is continuous. -/
theorem continuous_mixedAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    Continuous (mixedAffineChart (K := K) σ I).symm :=
  (continuous_pi fun a ↦ continuous_apply (Sum.inl a : σ ⊕ Σ i, Fin (n i))).prodMk
    ((continuous_multiprojectiveAffineChart_symm I).comp
      (continuous_pi fun q ↦ continuous_apply (Sum.inr q : σ ⊕ Σ i, Fin (n i))))

variable [ContinuousMul K] [ContinuousInv₀ K]

/-- A standard product affine chart is continuous on its open domain. -/
theorem continuousOn_multiprojectiveAffineChart (I : ∀ i, Fin (n i + 1)) :
    ContinuousOn (multiprojectiveAffineChart (K := K) I) (multiprojectiveAffineOpen I) :=
  continuousOn_pi.2 fun q ↦ (continuous_apply q.2).comp_continuousOn <|
    (Projectivization.continuousOn_affineChart (I q.1)).comp
      (continuous_apply q.1).continuousOn fun _ hp ↦ hp q.1

/-- A mixed product affine chart is continuous on its open domain. -/
theorem continuousOn_mixedAffineChart (I : ∀ i, Fin (n i + 1)) :
    ContinuousOn (mixedAffineChart (K := K) σ I) (mixedAffineOpen σ I) := by
  refine continuousOn_pi.2 fun c ↦ ?_
  cases c with
  | inl a => exact ((continuous_apply a).comp continuous_fst).continuousOn
  | inr q =>
    exact (continuous_apply q).comp_continuousOn <|
      (continuousOn_multiprojectiveAffineChart I).comp continuous_snd.continuousOn
        fun _ hx ↦ mem_mixedAffineOpen.1 hx

variable [T1Space K] [Finite ι]

/-- The standard product affine chart of a finite product of projective spaces, as an open partial
homeomorphism onto `(Σ i, Fin (n i)) → K`. -/
noncomputable def multiprojectiveAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    OpenPartialHomeomorph (∀ i, ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (OpenPartialHomeomorph.pi fun i ↦
    Projectivization.affineOpenPartialHomeomorph (K := K) (I i)).transHomeomorph
    (piCurryHomeomorph fun i (_ : Fin (n i)) ↦ K).symm

@[simp]
theorem multiprojectiveAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (multiprojectiveAffineOpenPartialHomeomorph (K := K) I).toPartialEquiv =
      multiprojectiveAffineChart I := by
  refine PartialEquiv.ext (fun p ↦ ?_) (fun z ↦ ?_) ?_
  · ext q
    simp [multiprojectiveAffineOpenPartialHomeomorph]
  · ext i
    have h : (piCurryHomeomorph fun i (_ : Fin (n i)) ↦ K) z i = fun k ↦ z ⟨i, k⟩ :=
      funext fun k ↦ by simp
    simp [multiprojectiveAffineOpenPartialHomeomorph, h]
  · ext p
    simp [multiprojectiveAffineOpenPartialHomeomorph, multiprojectiveAffineChart]

@[simp]
theorem coe_multiprojectiveAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(multiprojectiveAffineOpenPartialHomeomorph (K := K) I) = multiprojectiveAffineChart I :=
  congrArg (fun e : PartialEquiv _ _ ↦ ⇑e)
    (multiprojectiveAffineOpenPartialHomeomorph_toPartialEquiv I)

@[simp]
theorem coe_multiprojectiveAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(multiprojectiveAffineOpenPartialHomeomorph (K := K) I).symm =
      (multiprojectiveAffineChart I).symm :=
  congrArg (fun e : PartialEquiv _ _ ↦ ⇑e.symm)
    (multiprojectiveAffineOpenPartialHomeomorph_toPartialEquiv I)

/-- The inverse of a standard product affine chart is an open embedding onto
`TauCeti.multiprojectiveAffineOpen I`. -/
theorem isOpenEmbedding_multiprojectiveAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    IsOpenEmbedding (multiprojectiveAffineChart (K := K) I).symm :=
  coe_multiprojectiveAffineOpenPartialHomeomorph_symm (K := K) I ▸
    (multiprojectiveAffineOpenPartialHomeomorph (K := K) I).symm.isOpenEmbedding (by simp)

/-- The standard product affine chart of a mixed affine–multiprojective space, as an open partial
homeomorphism onto `(σ ⊕ Σ i, Fin (n i)) → K`. -/
noncomputable def mixedAffineOpenPartialHomeomorph (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    OpenPartialHomeomorph ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))
      ((σ ⊕ Σ i, Fin (n i)) → K) :=
  ((OpenPartialHomeomorph.refl (σ → K)).prod
    (multiprojectiveAffineOpenPartialHomeomorph I)).transHomeomorph
    Homeomorph.sumArrowHomeomorphProdArrow.symm

@[simp]
theorem mixedAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (mixedAffineOpenPartialHomeomorph (K := K) σ I).toPartialEquiv = mixedAffineChart σ I := by
  refine PartialEquiv.ext (fun x ↦ ?_) (fun z ↦ ?_) ?_
  · ext c
    rw [mixedAffineChart_apply]
    simp [mixedAffineOpenPartialHomeomorph]
  · simp [mixedAffineOpenPartialHomeomorph]
  · ext x
    simp [mixedAffineOpenPartialHomeomorph, mixedAffineChart]

@[simp]
theorem coe_mixedAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(mixedAffineOpenPartialHomeomorph (K := K) σ I) = mixedAffineChart σ I :=
  congrArg (fun e : PartialEquiv _ _ ↦ ⇑e) (mixedAffineOpenPartialHomeomorph_toPartialEquiv I)

@[simp]
theorem coe_mixedAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(mixedAffineOpenPartialHomeomorph (K := K) σ I).symm = (mixedAffineChart σ I).symm :=
  congrArg (fun e : PartialEquiv _ _ ↦ ⇑e.symm)
    (mixedAffineOpenPartialHomeomorph_toPartialEquiv I)

end Topology

end Charts

/-! ### Punctured-cone preimages and Boolean algebra of semialgebraic sets -/

section Cone

variable {ι σ K : Type*} {n : ι → ℕ}

/-- The punctured-cone locus in flattened homogeneous coordinates `(Σ i, Fin (n i + 1)) → K`,
consisting of the vectors whose `i`-th homogeneous block is nonzero for every `i`. -/
def multiprojectivePuncturedCone (n : ι → ℕ) (K : Type*) [Zero K] :
    Set ((Σ i, Fin (n i + 1)) → K) :=
  {v | ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0}

@[simp]
theorem mem_multiprojectivePuncturedCone [Zero K] {v : (Σ i, Fin (n i + 1)) → K} :
    v ∈ multiprojectivePuncturedCone n K ↔ ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0 :=
  Iff.rfl

/-- The punctured-cone locus in flattened mixed coordinates `(σ ⊕ Σ i, Fin (n i + 1)) → K`. -/
def mixedPuncturedCone (σ : Type*) (n : ι → ℕ) (K : Type*) [Zero K] :
    Set ((σ ⊕ Σ i, Fin (n i + 1)) → K) :=
  {w | ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0}

@[simp]
theorem mem_mixedPuncturedCone [Zero K] {w : (σ ⊕ Σ i, Fin (n i + 1)) → K} :
    w ∈ mixedPuncturedCone σ n K ↔ ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0 :=
  Iff.rfl

variable [Field K]

/-- The punctured-cone preimage in `(Σ i, Fin (n i + 1)) → K` of a subset `S` of a
multiprojective space under the product of projective quotient maps. -/
def multiprojectiveCone (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    Set ((Σ i, Fin (n i + 1)) → K) :=
  {v | ∃ hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0,
    (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S}

theorem mem_multiprojectiveCone {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    {v : (Σ i, Fin (n i + 1)) → K} :
    v ∈ multiprojectiveCone S ↔ ∃ hv : ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0,
      (fun i ↦ Projectivization.mk K (fun j ↦ v ⟨i, j⟩) (hv i)) ∈ S :=
  Iff.rfl

/-- Flattening a tuple of nonzero vectors `u : ∀ i, {x : Fin (n i + 1) → K // x ≠ 0}` via
`Equiv.piCurry` identifies `TauCeti.multiprojectiveCone S` with the preimage of `S` under the
product quotient map `fun u i ↦ Projectivization.mk' K (u i)`. -/
theorem piCurry_symm_mem_multiprojectiveCone_iff
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (u : ∀ i, {x : Fin (n i + 1) → K // x ≠ 0}) :
    (Equiv.piCurry fun i (_ : Fin (n i + 1)) ↦ K).symm (fun i ↦ (u i).1) ∈
      multiprojectiveCone S ↔
      (fun i ↦ Projectivization.mk' K (u i)) ∈ S :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨fun i ↦ (u i).2, h⟩⟩

/-- The punctured-cone preimage in `(σ ⊕ Σ i, Fin (n i + 1)) → K` of a subset `S` of a mixed
affine–multiprojective space. -/
def mixedCone (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :
    Set ((σ ⊕ Σ i, Fin (n i + 1)) → K) :=
  {w | ∃ hw : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0,
    (w ∘ Sum.inl, fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw i)) ∈ S}

theorem mem_mixedCone {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    {w : (σ ⊕ Σ i, Fin (n i + 1)) → K} :
    w ∈ mixedCone S ↔ ∃ hw : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0,
      (w ∘ Sum.inl, fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw i)) ∈ S :=
  Iff.rfl

@[simp]
theorem mixedCone_empty :
    mixedCone (∅ : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) = ∅ := by
  ext w
  simp [mem_mixedCone]

@[simp]
theorem mixedCone_univ :
    mixedCone (univ : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) =
      mixedPuncturedCone σ n K := by
  ext w
  simp [mem_mixedCone]

@[simp]
theorem mixedCone_union (S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :
    mixedCone (S ∪ T) = mixedCone S ∪ mixedCone T := by
  ext w
  simp only [mem_mixedCone, mem_union]
  exact ⟨fun ⟨hw, h⟩ ↦ h.imp (fun hS ↦ ⟨hw, hS⟩) fun hT ↦ ⟨hw, hT⟩,
    fun h ↦ h.elim (fun ⟨hw, hS⟩ ↦ ⟨hw, Or.inl hS⟩) fun ⟨hw, hT⟩ ↦ ⟨hw, Or.inr hT⟩⟩

@[simp]
theorem mixedCone_inter (S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :
    mixedCone (S ∩ T) = mixedCone S ∩ mixedCone T := by
  ext w
  simp only [mem_mixedCone, mem_inter_iff]
  exact ⟨fun ⟨hw, hS, hT⟩ ↦ ⟨⟨hw, hS⟩, ⟨hw, hT⟩⟩, fun ⟨⟨hw, hS⟩, _, hT⟩ ↦ ⟨hw, hS, hT⟩⟩

@[simp]
theorem mixedCone_sdiff (S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :
    mixedCone (S \ T) = mixedCone S \ mixedCone T := by
  ext w
  simp only [mem_mixedCone, mem_sdiff]
  exact ⟨fun ⟨hw, hS, hT⟩ ↦ ⟨⟨hw, hS⟩, fun ⟨_, hT'⟩ ↦ hT hT'⟩,
    fun ⟨⟨hw, hS⟩, hT⟩ ↦ ⟨hw, hS, fun hT' ↦ hT ⟨hw, hT'⟩⟩⟩

theorem mixedCone_compl (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :
    mixedCone Sᶜ = mixedPuncturedCone σ n K \ mixedCone S := by
  ext w
  simp only [mem_mixedCone, mem_compl_iff, mem_sdiff, mem_mixedPuncturedCone]
  exact ⟨fun ⟨hw, hS⟩ ↦ ⟨hw, fun ⟨_, hS'⟩ ↦ hS hS'⟩,
    fun ⟨hw, hS⟩ ↦ ⟨hw, fun hS' ↦ hS ⟨hw, hS'⟩⟩⟩

@[simp]
theorem mixedCone_prod (A : Set (σ → K)) (B : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    mixedCone (A ×ˢ B) =
      (fun w : (σ ⊕ Σ i, Fin (n i + 1)) → K ↦ w ∘ Sum.inl) ⁻¹' A ∩
        (fun w : (σ ⊕ Σ i, Fin (n i + 1)) → K ↦ w ∘ Sum.inr) ⁻¹' multiprojectiveCone B := by
  ext w
  simp only [mem_mixedCone, mem_prod, mem_inter_iff, mem_preimage, mem_multiprojectiveCone,
    Function.comp_apply]
  exact ⟨fun ⟨hw, hA, hB⟩ ↦ ⟨hA, hw, hB⟩, fun ⟨hA, hw, hB⟩ ↦ ⟨hw, hA, hB⟩⟩

@[simp]
theorem multiprojectiveCone_empty :
    multiprojectiveCone (∅ : Set (∀ i, ℙ K (Fin (n i + 1) → K))) = ∅ := by
  ext v
  simp [mem_multiprojectiveCone]

@[simp]
theorem multiprojectiveCone_univ :
    multiprojectiveCone (univ : Set (∀ i, ℙ K (Fin (n i + 1) → K))) =
      multiprojectivePuncturedCone n K := by
  ext v
  simp [mem_multiprojectiveCone]

@[simp]
theorem multiprojectiveCone_union (S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    multiprojectiveCone (S ∪ T) = multiprojectiveCone S ∪ multiprojectiveCone T := by
  ext v
  simp only [mem_multiprojectiveCone, mem_union]
  exact ⟨fun ⟨hv, h⟩ ↦ h.imp (fun hS ↦ ⟨hv, hS⟩) fun hT ↦ ⟨hv, hT⟩,
    fun h ↦ h.elim (fun ⟨hv, hS⟩ ↦ ⟨hv, Or.inl hS⟩) fun ⟨hv, hT⟩ ↦ ⟨hv, Or.inr hT⟩⟩

@[simp]
theorem multiprojectiveCone_inter (S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    multiprojectiveCone (S ∩ T) = multiprojectiveCone S ∩ multiprojectiveCone T := by
  ext v
  simp only [mem_multiprojectiveCone, mem_inter_iff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, ⟨hv, hT⟩⟩, fun ⟨⟨hv, hS⟩, _, hT⟩ ↦ ⟨hv, hS, hT⟩⟩

@[simp]
theorem multiprojectiveCone_sdiff (S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    multiprojectiveCone (S \ T) = multiprojectiveCone S \ multiprojectiveCone T := by
  ext v
  simp only [mem_multiprojectiveCone, mem_sdiff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, fun ⟨_, hT'⟩ ↦ hT hT'⟩,
    fun ⟨⟨hv, hS⟩, hT⟩ ↦ ⟨hv, hS, fun hT' ↦ hT ⟨hv, hT'⟩⟩⟩

@[simp]
theorem multiprojectiveCone_compl (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :
    multiprojectiveCone Sᶜ = multiprojectivePuncturedCone n K \ multiprojectiveCone S := by
  ext v
  simp only [mem_multiprojectiveCone, mem_compl_iff, mem_sdiff, mem_multiprojectivePuncturedCone]
  exact ⟨fun ⟨hv, hS⟩ ↦ ⟨hv, fun ⟨_, hS'⟩ ↦ hS hS'⟩,
    fun ⟨hv, hS⟩ ↦ ⟨hv, fun hS' ↦ hS ⟨hv, hS'⟩⟩⟩

variable [LinearOrder K]

/-- A subset `S` of a mixed affine–multiprojective space
`(σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` is *mixed semialgebraic* if its punctured-cone preimage
`TauCeti.mixedCone S` in `(σ ⊕ Σ i, Fin (n i + 1)) → K` is semialgebraic. -/
def IsMixedSemialgebraic (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) : Prop :=
  IsSemialgebraic (mixedCone S)

theorem isMixedSemialgebraic_def {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMixedSemialgebraic S ↔ IsSemialgebraic (mixedCone S) :=
  Iff.rfl

/-- A subset `S` of a multiprojective space `∀ i, ℙ K (Fin (n i + 1) → K)` is *multiprojective
semialgebraic* if its punctured-cone preimage `TauCeti.multiprojectiveCone S` in
`(Σ i, Fin (n i + 1)) → K` is semialgebraic. -/
def IsMultiprojectiveSemialgebraic (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) : Prop :=
  IsSemialgebraic (multiprojectiveCone S)

theorem isMultiprojectiveSemialgebraic_def {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔ IsSemialgebraic (multiprojectiveCone S) :=
  Iff.rfl

/-- For `ι = Fin m`, multiprojective semialgebraicity is equivalent to semialgebraicity of the
punctured-cone preimage in the single finite coordinate space `Fin (∑ i, (n i + 1)) → K` via
`finSigmaFinEquiv`. -/
theorem isMultiprojectiveSemialgebraic_iff_fin {m : ℕ} {n : Fin m → ℕ}
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔
      IsSemialgebraic
        ((fun x : Fin (∑ i, (n i + 1)) → K ↦ x ∘ finSigmaFinEquiv) ⁻¹'
          multiprojectiveCone S) :=
  (isSemialgebraic_preimage_comp_equiv finSigmaFinEquiv).symm

/-- A cylinder `univ ×ˢ T` in `(σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` is mixed semialgebraic if
and only if `T` is multiprojective semialgebraic. -/
@[simp]
theorem isMixedSemialgebraic_univ_prod_iff {T : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMixedSemialgebraic ((univ : Set (σ → K)) ×ˢ T) ↔ IsMultiprojectiveSemialgebraic T := by
  rw [IsMixedSemialgebraic, IsMultiprojectiveSemialgebraic, mixedCone_prod, preimage_univ,
    univ_inter]
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage_comp Sum.inr⟩
  convert h.preimage_eval (Sum.elim (fun _ ↦ 0) X) using 1
  ext v
  simp only [mem_preimage]
  congr! 1
  ext q
  simp

/-- The product of an affine semialgebraic set and a multiprojective semialgebraic set is mixed
semialgebraic. -/
theorem IsSemialgebraic.isMixedSemialgebraic_prod {A : Set (σ → K)}
    {B : Set (∀ i, ℙ K (Fin (n i + 1) → K))} (hA : IsSemialgebraic A)
    (hB : IsMultiprojectiveSemialgebraic B) : IsMixedSemialgebraic (A ×ˢ B) := by
  rw [IsMixedSemialgebraic, mixedCone_prod]
  exact (hA.preimage_comp Sum.inl).inter (hB.preimage_comp Sum.inr)

/-- On an empty product of projective spaces, every subset is multiprojective semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_of_isEmpty [IsEmpty ι]
    (S : Set (∀ i, ℙ K (Fin (n i + 1) → K))) : IsMultiprojectiveSemialgebraic S := by
  rcases (multiprojectiveCone S).eq_empty_or_nonempty with h | ⟨v, hv⟩
  · rw [IsMultiprojectiveSemialgebraic, h]
    exact isSemialgebraic_empty
  · have huniv : multiprojectiveCone S = univ :=
      eq_univ_of_forall fun w ↦ Subsingleton.elim w v ▸ hv
    rw [IsMultiprojectiveSemialgebraic, huniv]
    exact isSemialgebraic_univ

/-- When the projective factor index `ι` is empty, `TauCeti.IsMixedSemialgebraic` on
`(σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K)` reduces to `TauCeti.IsSemialgebraic` on `σ → K`. -/
@[simp]
theorem isMixedSemialgebraic_of_isEmpty_iff [IsEmpty ι]
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMixedSemialgebraic S ↔ IsSemialgebraic ((fun x : σ → K ↦ (x, isEmptyElim)) ⁻¹' S) := by
  have heq : mixedCone S =
      (fun w : (σ ⊕ Σ i, Fin (n i + 1)) → K ↦ w ∘ Sum.inl) ⁻¹'
        ((fun x : σ → K ↦ (x, isEmptyElim)) ⁻¹' S) := by
    ext w
    simp only [mem_mixedCone, IsEmpty.forall_iff, exists_true_left, mem_preimage]
    congr! 1
    exact Prod.ext rfl (funext isEmptyElim)
  rw [IsMixedSemialgebraic, heq]
  exact isSemialgebraic_preimage_comp_equiv (Equiv.sumEmpty σ (Σ i, Fin (n i + 1))).symm

/-- For finitely many projective factors, the punctured-cone locus in
`(Σ i, Fin (n i + 1)) → K` is semialgebraic. -/
theorem isSemialgebraic_multiprojectivePuncturedCone [Finite ι] :
    IsSemialgebraic (multiprojectivePuncturedCone n K) := by
  have h : multiprojectivePuncturedCone n K =
      ⋂ i : ι, ⋃ j : Fin (n i + 1), {v | eval v (X ⟨i, j⟩) ≠ 0} := by
    ext v
    simp [funext_iff, not_forall]
  rw [h]
  exact .iInter fun i ↦ .iUnion fun j ↦ isSemialgebraic_eval_ne_zero _

/-- For finitely many projective factors, the punctured-cone locus in
`(σ ⊕ Σ i, Fin (n i + 1)) → K` is semialgebraic. -/
theorem isSemialgebraic_mixedPuncturedCone [Finite ι] :
    IsSemialgebraic (mixedPuncturedCone σ n K) :=
  isSemialgebraic_multiprojectivePuncturedCone.preimage_comp Sum.inr

/-- Every singleton in a finite product of projective spaces is multiprojective semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_singleton [Finite ι]
    (p : ∀ i : ι, ℙ K (Fin (n i + 1) → K)) :
    IsMultiprojectiveSemialgebraic ({p} : Set (∀ i : ι, ℙ K (Fin (n i + 1) → K))) := by
  rw [isMultiprojectiveSemialgebraic_def]
  have hminors : IsSemialgebraic
      (⋂ (i : ι) (j : Fin (n i + 1)) (k : Fin (n i + 1)),
        {v : (Σ i, Fin (n i + 1)) → K |
          eval v (C ((p i).rep k) * X ⟨i, j⟩ - C ((p i).rep j) * X ⟨i, k⟩) = 0}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ isSemialgebraic_eval_eq_zero _
  convert isSemialgebraic_multiprojectivePuncturedCone.inter hminors using 1
  ext v
  simp only [mem_multiprojectiveCone, mem_singleton_iff, funext_iff, mem_inter_iff,
    mem_multiprojectivePuncturedCone, mem_iInter, mem_ofPred_eq, map_sub, map_mul, eval_C, eval_X,
    sub_eq_zero]
  refine ⟨fun ⟨hv, hp⟩ ↦ ⟨hv, fun i j k ↦ ?_⟩, fun ⟨hv, hp⟩ ↦ ⟨hv, fun i ↦ ?_⟩⟩
  · have hi := (hp i).trans (p i).mk_rep.symm
    have hmul := (Projectivization.mk_eq_mk_iff_forall_mul_eq (hv i) (p i).rep_ne_zero).1 hi j k
    rw [mul_comm, hmul, mul_comm]
  · rw [← (p i).mk_rep, Projectivization.mk_eq_mk_iff_forall_mul_eq (hv i) (p i).rep_ne_zero]
    intro j k
    rw [mul_comm, hp i j k, mul_comm]

/-- Every singleton in a finite-dimensional mixed space is mixed semialgebraic. -/
theorem isMixedSemialgebraic_singleton [Finite σ] [Finite ι]
    (c : (σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K)) :
    IsMixedSemialgebraic ({c} : Set ((σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K))) := by
  rw [← Prod.eta c, ← singleton_prod_singleton]
  exact (isSemialgebraic_singleton c.1).isMixedSemialgebraic_prod
    (isMultiprojectiveSemialgebraic_singleton c.2)

@[simp]
theorem isMixedSemialgebraic_empty :
    IsMixedSemialgebraic (∅ : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) := by
  simp [IsMixedSemialgebraic]

@[simp]
theorem isMultiprojectiveSemialgebraic_empty :
    IsMultiprojectiveSemialgebraic (∅ : Set (∀ i, ℙ K (Fin (n i + 1) → K))) := by
  simp [IsMultiprojectiveSemialgebraic]

theorem IsMixedSemialgebraic.union {S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) (hT : IsMixedSemialgebraic T) :
    IsMixedSemialgebraic (S ∪ T) := by
  rw [IsMixedSemialgebraic] at hS hT ⊢
  rw [mixedCone_union]
  exact hS.union hT

theorem IsMixedSemialgebraic.inter {S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) (hT : IsMixedSemialgebraic T) :
    IsMixedSemialgebraic (S ∩ T) := by
  rw [IsMixedSemialgebraic] at hS hT ⊢
  rw [mixedCone_inter]
  exact hS.inter hT

theorem IsMixedSemialgebraic.sdiff {S T : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) (hT : IsMixedSemialgebraic T) :
    IsMixedSemialgebraic (S \ T) := by
  rw [IsMixedSemialgebraic] at hS hT ⊢
  rw [mixedCone_sdiff]
  exact hS.sdiff hT

theorem IsMixedSemialgebraic.biUnion {α : Type*} {A : Set α} (hA : A.Finite)
    {S : α → Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a ∈ A, IsMixedSemialgebraic (S a)) : IsMixedSemialgebraic (⋃ a ∈ A, S a) := by
  rw [IsMixedSemialgebraic]
  have h : mixedCone (⋃ a ∈ A, S a) = ⋃ a ∈ A, mixedCone (S a) := by
    ext w
    simp only [mem_mixedCone, mem_iUnion]
    exact ⟨fun ⟨hw, a, ha, hSa⟩ ↦ ⟨a, ha, hw, hSa⟩, fun ⟨a, ha, hw, hSa⟩ ↦ ⟨hw, a, ha, hSa⟩⟩
  rw [h]
  exact IsSemialgebraic.biUnion hA hS

theorem IsMixedSemialgebraic.iUnion {α : Type*} [Finite α]
    {S : α → Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a, IsMixedSemialgebraic (S a)) : IsMixedSemialgebraic (⋃ a, S a) := by
  simpa using IsMixedSemialgebraic.biUnion finite_univ fun a _ ↦ hS a

theorem IsMultiprojectiveSemialgebraic.union {S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∪ T) := by
  rw [IsMultiprojectiveSemialgebraic] at hS hT ⊢
  rw [multiprojectiveCone_union]
  exact hS.union hT

theorem IsMultiprojectiveSemialgebraic.inter {S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∩ T) := by
  rw [IsMultiprojectiveSemialgebraic] at hS hT ⊢
  rw [multiprojectiveCone_inter]
  exact hS.inter hT

theorem IsMultiprojectiveSemialgebraic.sdiff {S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S \ T) := by
  rw [IsMultiprojectiveSemialgebraic] at hS hT ⊢
  rw [multiprojectiveCone_sdiff]
  exact hS.sdiff hT

theorem IsMultiprojectiveSemialgebraic.biUnion {α : Type*} {A : Set α} (hA : A.Finite)
    {S : α → Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a ∈ A, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a ∈ A, S a) := by
  rw [IsMultiprojectiveSemialgebraic]
  have h : multiprojectiveCone (⋃ a ∈ A, S a) = ⋃ a ∈ A, multiprojectiveCone (S a) := by
    ext v
    simp only [mem_multiprojectiveCone, mem_iUnion]
    exact ⟨fun ⟨hv, a, ha, hSa⟩ ↦ ⟨a, ha, hv, hSa⟩, fun ⟨a, ha, hv, hSa⟩ ↦ ⟨hv, a, ha, hSa⟩⟩
  rw [h]
  exact IsSemialgebraic.biUnion hA hS

theorem IsMultiprojectiveSemialgebraic.iUnion {α : Type*} [Finite α]
    {S : α → Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a, S a) := by
  simpa using IsMultiprojectiveSemialgebraic.biUnion finite_univ fun a _ ↦ hS a

section BooleanAlgebra

variable [Finite ι]

/-- In a mixed affine–multiprojective space with finitely many projective factors, the mixed
semialgebraic sets form an algebra of sets. -/
theorem isSetAlgebra_setOf_isMixedSemialgebraic :
    IsSetAlgebra {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) | IsMixedSemialgebraic S} where
  empty_mem := isMixedSemialgebraic_empty
  compl_mem S hS := by
    rw [mem_ofPred_eq, IsMixedSemialgebraic, mixedCone_compl]
    exact isSemialgebraic_mixedPuncturedCone.sdiff hS
  union_mem _ _ hS hT := hS.union hT

/-- In a multiprojective space with finitely many factors, the multiprojective semialgebraic sets
form an algebra of sets. -/
theorem isSetAlgebra_setOf_isMultiprojectiveSemialgebraic :
    IsSetAlgebra {S : Set (∀ i, ℙ K (Fin (n i + 1) → K)) | IsMultiprojectiveSemialgebraic S} where
  empty_mem := isMultiprojectiveSemialgebraic_empty
  compl_mem S hS := by
    rw [mem_ofPred_eq, IsMultiprojectiveSemialgebraic, multiprojectiveCone_compl]
    exact isSemialgebraic_multiprojectivePuncturedCone.sdiff hS
  union_mem _ _ hS hT := hS.union hT

@[simp]
theorem isMixedSemialgebraic_univ :
    IsMixedSemialgebraic (univ : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) :=
  isSetAlgebra_setOf_isMixedSemialgebraic.univ_mem

@[simp]
theorem isMultiprojectiveSemialgebraic_univ :
    IsMultiprojectiveSemialgebraic (univ : Set (∀ i, ℙ K (Fin (n i + 1) → K))) :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.univ_mem

theorem IsMixedSemialgebraic.compl {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) : IsMixedSemialgebraic Sᶜ :=
  isSetAlgebra_setOf_isMixedSemialgebraic.compl_mem hS

@[simp]
theorem isMixedSemialgebraic_compl_iff {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMixedSemialgebraic Sᶜ ↔ IsMixedSemialgebraic S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, IsMixedSemialgebraic.compl⟩

theorem IsMixedSemialgebraic.biInter {α : Type*} {A : Set α} (hA : A.Finite)
    {S : α → Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a ∈ A, IsMixedSemialgebraic (S a)) : IsMixedSemialgebraic (⋂ a ∈ A, S a) := by
  simpa using isSetAlgebra_setOf_isMixedSemialgebraic.biInter_mem hA.toFinset (by simpa using hS)

theorem IsMixedSemialgebraic.iInter {α : Type*} [Finite α]
    {S : α → Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a, IsMixedSemialgebraic (S a)) : IsMixedSemialgebraic (⋂ a, S a) := by
  simpa using IsMixedSemialgebraic.biInter finite_univ fun a _ ↦ hS a

theorem IsMultiprojectiveSemialgebraic.compl {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) : IsMultiprojectiveSemialgebraic Sᶜ :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.compl_mem hS

@[simp]
theorem isMultiprojectiveSemialgebraic_compl_iff {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic Sᶜ ↔ IsMultiprojectiveSemialgebraic S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, IsMultiprojectiveSemialgebraic.compl⟩

theorem IsMultiprojectiveSemialgebraic.biInter {α : Type*} {A : Set α} (hA : A.Finite)
    {S : α → Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a ∈ A, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a ∈ A, S a) := by
  simpa using isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.biInter_mem hA.toFinset
    (by simpa using hS)

theorem IsMultiprojectiveSemialgebraic.iInter {α : Type*} [Finite α]
    {S : α → Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a, S a) := by
  simpa using IsMultiprojectiveSemialgebraic.biInter finite_univ fun a _ ↦ hS a

end BooleanAlgebra

end Cone

/-! ### Global chart characterization and semialgebraicity of transition maps -/

section GlobalCharts

variable {ι σ K : Type*} [Field K] {n : ι → ℕ}

/-- Flattened homogeneous coordinate polynomials inserting `1` in position `I i` of the `i`-th
factor, representing `(TauCeti.multiprojectiveAffineChart I).symm` in homogeneous coordinates. -/
noncomputable def multiprojectiveInsertNthPoly (I : ∀ i, Fin (n i + 1)) :
    (Σ i, Fin (n i + 1)) → MvPolynomial (Σ i, Fin (n i)) K :=
  fun q ↦ Fin.insertNth (α := fun _ ↦ MvPolynomial (Σ i, Fin (n i)) K) (I q.1) 1
    (fun k ↦ X ⟨q.1, k⟩) q.2

@[simp]
theorem eval_multiprojectiveInsertNthPoly (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
    eval z (multiprojectiveInsertNthPoly I ⟨i, j⟩) =
      Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) j := by
  induction j using (I i).succAboveCases with
  | x => simp [multiprojectiveInsertNthPoly]
  | p k => simp [multiprojectiveInsertNthPoly]

/-- Mixed polynomial coordinates acting as the identity on `σ` and inserting `1` in position `I i`
of the `i`-th homogeneous block. -/
private noncomputable def mixedInsertNthPoly (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    (σ ⊕ Σ i, Fin (n i + 1)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
  Sum.elim (fun a ↦ X (.inl a)) (fun q ↦ rename Sum.inr (multiprojectiveInsertNthPoly I q))

private theorem eval_mixedInsertNthPoly_inr (I : ∀ i, Fin (n i + 1))
    (z : (σ ⊕ Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
    eval z (mixedInsertNthPoly σ I (.inr ⟨i, j⟩)) =
      Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z (.inr ⟨i, k⟩)) j := by
  simp [mixedInsertNthPoly, eval_rename]

private theorem mixedInsertNthPoly_preimage_mixedCone
    (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) (I : ∀ i, Fin (n i + 1)) :
    (fun z c ↦ eval z (mixedInsertNthPoly σ I c)) ⁻¹' mixedCone S =
      mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I) := by
  rw [mixedAffineChart_image_inter_affineOpen]
  ext z
  simp only [mem_preimage, mem_mixedCone]
  have heval_inl : (fun a ↦ eval z (mixedInsertNthPoly σ I (.inl a))) = z ∘ Sum.inl :=
    funext fun _ ↦ by simp [mixedInsertNthPoly]
  have heval_inr (i : ι) :
      (fun j ↦ eval z (mixedInsertNthPoly σ I (.inr ⟨i, j⟩))) =
        Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z (.inr ⟨i, k⟩)) :=
    funext (eval_mixedInsertNthPoly_inr I z i)
  have hne : ∀ i, (fun j ↦ eval z (mixedInsertNthPoly σ I (.inr ⟨i, j⟩))) ≠ 0 := by
    intro i
    rw [heval_inr i]
    exact Fin.insertNth_one_ne_zero (I i) _
  have hsymm_eq : (mixedAffineChart σ I).symm z =
      ((fun c ↦ eval z (mixedInsertNthPoly σ I c)) ∘ Sum.inl,
        fun i ↦ Projectivization.mk K (fun j ↦ eval z (mixedInsertNthPoly σ I (.inr ⟨i, j⟩)))
          (hne i)) := by
    rw [mixedAffineChart_symm_apply, ← heval_inl]
    refine Prod.ext rfl (funext fun i ↦ ?_)
    simp only [multiprojectiveAffineChart_symm_apply, Projectivization.affineChart_symm_apply]
    congr 1
    exact (heval_inr i).symm
  exact ⟨fun ⟨_, hzS⟩ ↦ hsymm_eq ▸ hzS, fun hzS ↦ ⟨hne, hsymm_eq ▸ hzS⟩⟩

variable [LinearOrder K]

/-- A mixed semialgebraic set has semialgebraic image in every standard product affine chart. -/
theorem IsMixedSemialgebraic.isSemialgebraic_chart
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMixedSemialgebraic S) (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I)) := by
  rw [← mixedInsertNthPoly_preimage_mixedCone]
  exact hS.preimage_eval (mixedInsertNthPoly σ I)

/-- A multiprojective semialgebraic set has semialgebraic image in every standard product affine
chart. -/
theorem IsMultiprojectiveSemialgebraic.isSemialgebraic_chart
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} (hS : IsMultiprojectiveSemialgebraic S)
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I)) := by
  have h := ((isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 hS).isSemialgebraic_chart I
  rw [mixedAffineChart_image_univ_prod_inter_affineOpen] at h
  convert h.preimage_comp (Sum.elim Empty.elim id) using 1
  ext z
  simp [Function.comp_def]

/-- In a finite product of projective spaces, each standard product affine open is
multiprojective semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_affineOpen [Finite ι] (I : ∀ i, Fin (n i + 1)) :
    IsMultiprojectiveSemialgebraic (multiprojectiveAffineOpen (K := K) I) := by
  have h : multiprojectiveCone (multiprojectiveAffineOpen (K := K) I) =
      multiprojectivePuncturedCone n K ∩ ⋂ i : ι, {v | eval v (X ⟨i, I i⟩) ≠ 0} := by
    ext v
    simp only [mem_multiprojectiveCone, mem_multiprojectiveAffineOpen,
      Projectivization.mk_mem_affineOpen_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq, eval_X,
      mem_multiprojectivePuncturedCone]
    exact ⟨fun ⟨hv, hI⟩ ↦ ⟨hv, hI⟩, fun ⟨hv, hI⟩ ↦ ⟨hv, hI⟩⟩
  rw [IsMultiprojectiveSemialgebraic, h]
  exact isSemialgebraic_multiprojectivePuncturedCone.inter
    (.iInter fun _ ↦ isSemialgebraic_eval_ne_zero _)

/-- In a mixed affine–multiprojective space with finitely many projective factors, each standard
product affine open is mixed semialgebraic. -/
theorem isMixedSemialgebraic_affineOpen [Finite ι] (I : ∀ i, Fin (n i + 1)) :
    IsMixedSemialgebraic (mixedAffineOpen (K := K) σ I) :=
  (isMixedSemialgebraic_univ_prod_iff (σ := σ)).2 (isMultiprojectiveSemialgebraic_affineOpen I)

/-- The source of the transition map between two standard product affine charts is semialgebraic,
and the transition map itself is semialgebraic on its source. -/
theorem isSemialgebraicOn_multiprojectiveAffineChart_symm_trans [Finite ι]
    (I J : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicOn ((multiprojectiveAffineChart (K := K) I).symm.trans
      (multiprojectiveAffineChart J))
      ((multiprojectiveAffineChart (K := K) I).symm.trans
        (multiprojectiveAffineChart J)).source := by
  have hsrc_eq : ((multiprojectiveAffineChart (K := K) I).symm.trans
      (multiprojectiveAffineChart J)).source =
        ⋂ i : ι, {z | eval z (multiprojectiveInsertNthPoly I ⟨i, J i⟩) ≠ 0} := by
    rw [multiprojectiveAffineChart_symm_trans_source]
    ext z
    simp
  have hsrc : IsSemialgebraic
      ((multiprojectiveAffineChart (K := K) I).symm.trans
        (multiprojectiveAffineChart J)).source := by
    rw [hsrc_eq]
    exact .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  refine (isSemialgebraicOn_eval_div
    (fun q : Σ i, Fin (n i) ↦ multiprojectiveInsertNthPoly I ⟨q.1, (J q.1).succAbove q.2⟩)
    (fun q : Σ i, Fin (n i) ↦ multiprojectiveInsertNthPoly I ⟨q.1, J q.1⟩) hsrc ?_).congr
    fun z _ ↦ ?_
  · intro z hz q
    rw [hsrc_eq, mem_iInter] at hz
    exact hz q.1
  · ext q
    simp [multiprojectiveAffineChart_symm_trans_apply]

variable [IsStrictOrderedRing K] [Finite ι]

/-- If the intersection of the `I`-chart image of `S` with `B` is semialgebraic, then transporting
`S ∩ (mixedAffineOpen σ I ∩ mixedAffineChart σ I ⁻¹' B)` to chart `J` yields a semialgebraic set,
without assuming projection closure. -/
theorem isSemialgebraic_mixedAffineChart_image_inter
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    {I J : ∀ i, Fin (n i + 1)} {B : Set ((σ ⊕ Σ i, Fin (n i)) → K)}
    (hSB : IsSemialgebraic ((mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I)) ∩ B)) :
    IsSemialgebraic
      (mixedAffineChart σ J ''
        ((S ∩ (mixedAffineOpen σ I ∩ mixedAffineChart σ I ⁻¹' B)) ∩ mixedAffineOpen σ J)) := by
  rw [mixedAffineChart_image_inter_affineOpen] at hSB ⊢
  let UJ : Set ((σ ⊕ Σ i, Fin (n i)) → K) :=
    ⋂ i : ι, {w | eval w (mixedInsertNthPoly σ J (.inr ⟨i, I i⟩)) ≠ 0}
  have hUJ : IsSemialgebraic UJ := .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  let f : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
    Sum.elim (fun a ↦ X (.inl a))
      fun q ↦ mixedInsertNthPoly σ J (.inr ⟨q.1, (I q.1).succAbove q.2⟩)
  let g : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ mixedInsertNthPoly σ J (.inr ⟨q.1, I q.1⟩)
  convert hSB.inter_preimage_eval_div hUJ f g
    (fun w hw c ↦ by
      cases c with
      | inl _ => simp [g]
      | inr q =>
        simp only [UJ, mem_iInter, mem_ofPred_eq] at hw
        simpa [g] using hw q.1) using 1
  ext w
  have hTw : (fun c ↦ eval w (f c) / eval w (g c)) =
      mixedAffineChart σ I ((mixedAffineChart σ J).symm w) := by
    ext (a | q)
    · simp [f, g]
    · simp [f, g, eval_mixedInsertNthPoly_inr, multiprojectiveAffineChart_symm_apply]
  have hUJ_mem : w ∈ UJ ↔ (mixedAffineChart σ J).symm w ∈ mixedAffineOpen σ I := by
    simp [UJ, eval_mixedInsertNthPoly_inr, multiprojectiveAffineChart_symm_apply]
  simp only [mem_preimage, mem_inter_iff]
  rw [hTw, hUJ_mem]
  refine ⟨fun ⟨hS, hI, hB⟩ ↦ ⟨hI, ?_, hB⟩, fun ⟨hI, hS, hB⟩ ↦ ⟨?_, hI, hB⟩⟩
  · rwa [(mixedAffineChart σ I).left_inv (by rw [mixedAffineChart_source]; exact hI)]
  · rwa [(mixedAffineChart σ I).left_inv (by rw [mixedAffineChart_source]; exact hI)] at hS

private theorem isSemialgebraic_mixedCone_inter_eval_ne_zero
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} (I : ∀ i, Fin (n i + 1))
    (hI : IsSemialgebraic (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I))) :
    IsSemialgebraic (mixedCone S ∩ ⋂ i : ι, {w | eval w (X (.inr ⟨i, I i⟩)) ≠ 0}) := by
  rw [mixedAffineChart_image_inter_affineOpen] at hI
  let W : Set ((σ ⊕ Σ i, Fin (n i + 1)) → K) := ⋂ i : ι, {w | eval w (X (.inr ⟨i, I i⟩)) ≠ 0}
  have hW : IsSemialgebraic W := .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  let f : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun a ↦ X (.inl a)) fun q ↦ X (.inr ⟨q.1, (I q.1).succAbove q.2⟩)
  let g : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ X (.inr ⟨q.1, I q.1⟩)
  convert hI.inter_preimage_eval_div hW f g (fun w hw c ↦ by
      cases c with
      | inl _ => simp [g]
      | inr q =>
        simp only [W, mem_iInter, mem_ofPred_eq] at hw
        simpa [g] using hw q.1) using 1
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_mixedCone]
  refine ⟨fun ⟨⟨hw, hwS⟩, hwI⟩ ↦ ⟨hwI, ?_⟩, fun ⟨hwI, hfw⟩ ↦ ⟨?_, hwI⟩⟩
  · have hwI' : ∀ i, w (.inr ⟨i, I i⟩) ≠ 0 := by simpa [W] using hwI
    convert hwS using 1
    rw [mixedAffineChart_symm_apply]
    refine Prod.ext (funext fun a ↦ by simp [f, g]) (funext fun i ↦ ?_)
    simp only [multiprojectiveAffineChart_symm_apply, Projectivization.affineChart_symm_apply,
      Function.comp_def, f, g, Sum.elim_inr, eval_X]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ (hw i)).2 ⟨(w (.inr ⟨i, I i⟩))⁻¹,
      (Fin.insertNth_one_div_eq_inv_smul (I i) (fun j ↦ w (.inr ⟨i, j⟩)) (hwI' i)).symm⟩
  · have hwI' : ∀ i, w (.inr ⟨i, I i⟩) ≠ 0 := by simpa [W] using hwI
    have hw0 : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0 := fun i h0 ↦ hwI' i (congrFun h0 (I i))
    refine ⟨hw0, ?_⟩
    convert hfw using 1
    rw [mixedAffineChart_symm_apply]
    refine Prod.ext (funext fun a ↦ by simp [f, g]) (funext fun i ↦ ?_)
    simp only [multiprojectiveAffineChart_symm_apply, Projectivization.affineChart_symm_apply,
      Function.comp_def, f, g, Sum.elim_inr, eval_X]
    exact ((Projectivization.mk_eq_mk_iff' K _ _ _ (hw0 i)).2 ⟨(w (.inr ⟨i, I i⟩))⁻¹,
      (Fin.insertNth_one_div_eq_inv_smul (I i) (fun j ↦ w (.inr ⟨i, j⟩)) (hwI' i)).symm⟩).symm

/-- **Cone-versus-chart equivalence for mixed spaces.** Over a strict ordered field and finitely
many projective factors, a subset `S ⊆ (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` is mixed
semialgebraic if and only if its image in every standard product affine chart is semialgebraic.
No projection-closure hypothesis is required. -/
theorem isMixedSemialgebraic_iff_forall_chart
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMixedSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1),
        IsSemialgebraic (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I)) := by
  refine ⟨fun hS I ↦ hS.isSemialgebraic_chart I, fun hchart ↦ ?_⟩
  have hcover : mixedCone S =
      ⋃ I : ∀ i, Fin (n i + 1), mixedCone S ∩ ⋂ i : ι, {w | eval w (X (.inr ⟨i, I i⟩)) ≠ 0} := by
    ext w
    simp only [mem_iUnion, mem_inter_iff]
    refine ⟨fun hw ↦ ?_, fun ⟨_, hw, _⟩ ↦ hw⟩
    choose I hI using fun i ↦ Function.ne_iff.1 (hw.1 i)
    exact ⟨I, hw, by simpa using hI⟩
  rw [IsMixedSemialgebraic, hcover]
  exact .iUnion fun I ↦ isSemialgebraic_mixedCone_inter_eval_ne_zero I (hchart I)

/-- **Cone-versus-chart equivalence for multiprojective spaces.** Over a strict ordered field and
finitely many factors, a subset `S ⊆ ∀ i, ℙ K (Fin (n i + 1) → K)` is multiprojective
semialgebraic if and only if its image in every standard product affine chart is semialgebraic.
No projection-closure hypothesis is required. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_chart
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1),
        IsSemialgebraic (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I)) := by
  refine ⟨fun hS I ↦ hS.isSemialgebraic_chart I, fun hchart ↦ ?_⟩
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty), isMixedSemialgebraic_iff_forall_chart]
  intro I
  rw [mixedAffineChart_image_univ_prod_inter_affineOpen]
  exact (hchart I).preimage_comp Sum.inr

/-- For `ι = Fin m`, multiprojective semialgebraicity is equivalent to semialgebraicity of every
standard product chart image in `Fin (∑ i, n i) → K` via `finSigmaFinEquiv`. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_fin_chart {m : ℕ} {n : Fin m → ℕ}
    {S : Set (∀ i, ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1),
        IsSemialgebraic
          ((fun x : Fin (∑ i, n i) → K ↦ x ∘ finSigmaFinEquiv) ⁻¹'
            (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I))) := by
  rw [isMultiprojectiveSemialgebraic_iff_forall_chart]
  exact forall_congr' fun _ ↦ (isSemialgebraic_preimage_comp_equiv finSigmaFinEquiv).symm

end GlobalCharts

end TauCeti
