/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local
public import TauCeti.Topology.Algebra.Projectivization
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
with nonvanishing denominators on the corresponding coordinate opens.

Over `ℝ`, compactness of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` upgrades local chartwise
semialgebraicity (`TauCeti.SemialgebraicAt`) at every point of `M` to global semialgebraicity
(`TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`,
`TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`), derived as the empty-affine
case of `TauCeti.isMixedSemialgebraic_of_isBounded_fst`: every point is covered by the chart
preimage of a bounded open semialgebraic ball, finitely many such patches cover the compact closure,
and rational transition pullbacks assemble them in any target chart.

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
  of multiprojective and mixed affine–multiprojective spaces, with `MeasureTheory.IsSetAlgebra`
  and Boolean closure.
* `TauCeti.isMixedSemialgebraic_iff_forall_chart`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_chart`: equivalence of cone and chart
  semialgebraicity over any strict ordered field.
* `TauCeti.isMixedSemialgebraic_of_isBounded_fst`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`: local-to-global chartwise
  criteria over `ℝ`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Chapter 2 and Section 3.4.
-/

public section

open MeasureTheory Metric MvPolynomial Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Standard product affine opens and charts -/

section Charts

variable {ι σ K : Type*} [Field K] {n : ι → ℕ}

/-- The standard product affine open of a multiprojective space associated to homogeneous
coordinate indices `I : ∀ i, Fin (n i + 1)`: the locus where the `I i`-th homogeneous coordinate
of the `i`-th factor is nonzero for every `i`. -/
def multiprojectiveAffineOpen (I : ∀ i, Fin (n i + 1)) :
    Set (∀ i, ℙ K (Fin (n i + 1) → K)) :=
  {p | ∀ i, p i ∈ Projectivization.affineOpen (I i)}

@[simp]
theorem mem_multiprojectiveAffineOpen {I : ∀ i, Fin (n i + 1)}
    {p : ∀ i, ℙ K (Fin (n i + 1) → K)} :
    p ∈ multiprojectiveAffineOpen I ↔ ∀ i, p i ∈ Projectivization.affineOpen (I i) :=
  Iff.rfl

/-- `TauCeti.multiprojectiveAffineOpen` as `Set.pi` over `Set.univ`. -/
theorem multiprojectiveAffineOpen_eq_univ_pi (I : ∀ i, Fin (n i + 1)) :
    multiprojectiveAffineOpen (K := K) I = univ.pi fun i ↦ Projectivization.affineOpen (I i) := by
  ext p
  simp

/-- Every point of a multiprojective space lies in some standard product affine open. -/
theorem exists_mem_multiprojectiveAffineOpen (p : ∀ i, ℙ K (Fin (n i + 1) → K)) :
    ∃ I, p ∈ multiprojectiveAffineOpen I := by
  choose I hI using fun i ↦ Projectivization.exists_mem_affineOpen (p i)
  exact ⟨I, hI⟩

/-- The standard product affine opens cover multiprojective space. -/
theorem iUnion_multiprojectiveAffineOpen :
    ⋃ I : ∀ i, Fin (n i + 1), multiprojectiveAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.2 (exists_mem_multiprojectiveAffineOpen p)

/-- On an empty product of projective spaces, every standard product affine open is the whole
space. -/
@[simp]
theorem multiprojectiveAffineOpen_eq_univ [IsEmpty ι] (I : ∀ i, Fin (n i + 1)) :
    multiprojectiveAffineOpen (K := K) I = univ :=
  eq_univ_of_forall fun _ i ↦ isEmptyElim i

/-- The standard product affine chart of `∀ i, ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, with coordinates flattened to `(Σ i, Fin (n i)) → K` via
`Equiv.piCurry`. -/
noncomputable def multiprojectiveAffineChart (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv (∀ i, ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (PartialEquiv.pi fun i ↦ Projectivization.affineChart (K := K) (I i)).trans
    (Equiv.piCurry fun i (_ : Fin (n i)) ↦ K).symm.toPartialEquiv

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

/-- The standard product affine open of a mixed affine–multiprojective space
`(σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` at `I : ∀ i, Fin (n i + 1)`. -/
def mixedAffineOpen (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :=
  univ ×ˢ multiprojectiveAffineOpen I

@[simp]
theorem mem_mixedAffineOpen {I : ∀ i, Fin (n i + 1)}
    {x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)} :
    x ∈ mixedAffineOpen σ I ↔ x.2 ∈ multiprojectiveAffineOpen I := by
  simp [mixedAffineOpen]

/-- Every point of a mixed affine–multiprojective space lies in some standard product affine
open. -/
theorem exists_mem_mixedAffineOpen (x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) :
    ∃ I, x ∈ mixedAffineOpen σ I := by
  obtain ⟨I, hI⟩ := exists_mem_multiprojectiveAffineOpen x.2
  exact ⟨I, mem_mixedAffineOpen.2 hI⟩

/-- The standard product affine chart of `(σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)` at
`I : ∀ i, Fin (n i + 1)`, flattened to `(σ ⊕ Σ i, Fin (n i)) → K`. -/
noncomputable def mixedAffineChart (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K)) ((σ ⊕ Σ i, Fin (n i)) → K) :=
  ((PartialEquiv.refl (σ → K)).prod (multiprojectiveAffineChart I)).trans
    (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i)) K).symm.toPartialEquiv

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

section Open

variable [T1Space K] [Finite ι]

/-- In a finite product of projective spaces, each standard product affine open is open. -/
theorem isOpen_multiprojectiveAffineOpen (I : ∀ i, Fin (n i + 1)) :
    IsOpen (multiprojectiveAffineOpen (K := K) I) := by
  rw [multiprojectiveAffineOpen_eq_univ_pi]
  exact isOpen_set_pi finite_univ fun i _ ↦ Projectivization.isOpen_affineOpen (I i)

/-- In a mixed affine–multiprojective space with finitely many projective factors, each standard
product affine open is open. -/
theorem isOpen_mixedAffineOpen (I : ∀ i, Fin (n i + 1)) :
    IsOpen (mixedAffineOpen (K := K) σ I) :=
  isOpen_univ.prod (isOpen_multiprojectiveAffineOpen I)

end Open

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
    OpenPartialHomeomorph (∀ i, ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) where
  toPartialEquiv := multiprojectiveAffineChart I
  open_source := by simpa using isOpen_multiprojectiveAffineOpen I
  open_target := by simp
  continuousOn_toFun := by simpa using continuousOn_multiprojectiveAffineChart I
  continuousOn_invFun := (continuous_multiprojectiveAffineChart_symm I).continuousOn

@[simp]
theorem multiprojectiveAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (multiprojectiveAffineOpenPartialHomeomorph (K := K) I).toPartialEquiv =
      multiprojectiveAffineChart I :=
  (rfl)

@[simp]
theorem coe_multiprojectiveAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(multiprojectiveAffineOpenPartialHomeomorph (K := K) I) = multiprojectiveAffineChart I :=
  (rfl)

@[simp]
theorem coe_multiprojectiveAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(multiprojectiveAffineOpenPartialHomeomorph (K := K) I).symm =
      (multiprojectiveAffineChart I).symm :=
  (rfl)

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
      ((σ ⊕ Σ i, Fin (n i)) → K) where
  toPartialEquiv := mixedAffineChart σ I
  open_source := by simpa using isOpen_mixedAffineOpen I
  open_target := by simp
  continuousOn_toFun := by simpa using continuousOn_mixedAffineChart I
  continuousOn_invFun := (continuous_mixedAffineChart_symm I).continuousOn

@[simp]
theorem mixedAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (mixedAffineOpenPartialHomeomorph (K := K) σ I).toPartialEquiv = mixedAffineChart σ I :=
  (rfl)

@[simp]
theorem coe_mixedAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(mixedAffineOpenPartialHomeomorph (K := K) σ I) = mixedAffineChart σ I :=
  (rfl)

@[simp]
theorem coe_mixedAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(mixedAffineOpenPartialHomeomorph (K := K) σ I).symm = (mixedAffineChart σ I).symm :=
  (rfl)

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
theorem IsSemialgebraic.prod_isMultiprojectiveSemialgebraic {A : Set (σ → K)}
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
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)] at hS hT ⊢
  rw [prod_union]
  exact hS.union hT

theorem IsMultiprojectiveSemialgebraic.inter {S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∩ T) := by
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)] at hS hT ⊢
  rw [← univ_inter univ, ← prod_inter_prod]
  exact hS.inter hT

theorem IsMultiprojectiveSemialgebraic.sdiff {S T : Set (∀ i, ℙ K (Fin (n i + 1) → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S \ T) := by
  rw [IsMultiprojectiveSemialgebraic] at hS hT ⊢
  have h : multiprojectiveCone (S \ T) = multiprojectiveCone S \ multiprojectiveCone T := by
    ext v
    simp only [mem_multiprojectiveCone, mem_sdiff]
    exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, fun ⟨_, hT'⟩ ↦ hT hT'⟩,
      fun ⟨⟨hv, hS⟩, hT⟩ ↦ ⟨hv, hS, fun hT' ↦ hT ⟨hv, hT'⟩⟩⟩
  rw [h]
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
    rw [mem_ofPred_eq, ← isMixedSemialgebraic_univ_prod_iff (σ := Empty)] at hS ⊢
    have hc : (univ : Set (Empty → K)) ×ˢ Sᶜ = ((univ : Set (Empty → K)) ×ˢ S)ᶜ := by
      ext ⟨_, p⟩
      simp
    rw [hc]
    exact isSetAlgebra_setOf_isMixedSemialgebraic.compl_mem hS
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

/-- Polynomial coordinates inserting `1` in position `I i` of the `i`-th homogeneous block. -/
private noncomputable def mixedInsertNthPoly (σ : Type*) (I : ∀ i, Fin (n i + 1)) :
    (σ ⊕ Σ i, Fin (n i + 1)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
  Sum.elim (fun a ↦ X (.inl a))
    fun q ↦ Fin.insertNth (α := fun _ ↦ MvPolynomial (σ ⊕ Σ i, Fin (n i)) K) (I q.1) 1
      (fun k ↦ X (.inr ⟨q.1, k⟩)) q.2

private theorem eval_mixedInsertNthPoly_inr (I : ∀ i, Fin (n i + 1))
    (z : (σ ⊕ Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
    eval z (mixedInsertNthPoly σ I (.inr ⟨i, j⟩)) =
      Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z (.inr ⟨i, k⟩)) j := by
  induction j using (I i).succAboveCases with
  | x => simp [mixedInsertNthPoly]
  | p k => simp [mixedInsertNthPoly]

private theorem mixedInsertNthPoly_preimage_mixedCone
    (S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))) (I : ∀ i, Fin (n i + 1)) :
    (fun z c ↦ eval z (mixedInsertNthPoly σ I c)) ⁻¹' mixedCone S =
      mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I) := by
  ext z
  simp only [mem_preimage, mem_mixedCone, mem_image, mem_inter_iff]
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
  constructor
  · rintro ⟨_, hzS⟩
    exact ⟨(mixedAffineChart σ I).symm z,
      ⟨hsymm_eq ▸ hzS, mixedAffineChart_symm_mem_affineOpen I z⟩,
      (mixedAffineChart σ I).right_inv (by simp)⟩
  · rintro ⟨x, ⟨hxS, hxI⟩, rfl⟩
    refine ⟨hne, ?_⟩
    rw [← hsymm_eq, (mixedAffineChart σ I).left_inv (by simpa using hxI)]
    exact hxS

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
  convert h.preimage_comp (Sum.elim Empty.elim id) using 1
  ext z
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and,
    mem_mixedAffineOpen, Prod.exists]
  constructor
  · rintro ⟨p, ⟨hpS, hpI⟩, rfl⟩
    refine ⟨Empty.elim, p, ⟨hpS, hpI⟩, ?_⟩
    ext (e | q)
    · exact e.elim
    · rfl
  · rintro ⟨_, p, ⟨hpS, hpI⟩, hpz⟩
    exact ⟨p, ⟨hpS, hpI⟩, funext fun q ↦ congrFun hpz (.inr q)⟩

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
  let P : ∀ i, Fin (n i + 1) → MvPolynomial (Σ i, Fin (n i)) K :=
    fun i ↦ Fin.insertNth (α := fun _ ↦ MvPolynomial (Σ i, Fin (n i)) K) (I i) 1
      fun k ↦ X ⟨i, k⟩
  have hP (z : (Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
      eval z (P i j) = Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) j := by
    induction j using (I i).succAboveCases with
    | x => simp [P]
    | p k => simp [P]
  have hsrc_eq : ((multiprojectiveAffineChart (K := K) I).symm.trans
      (multiprojectiveAffineChart J)).source = ⋂ i : ι, {z | eval z (P i (J i)) ≠ 0} := by
    rw [multiprojectiveAffineChart_symm_trans_source]
    ext z
    simp [hP]
  have hsrc : IsSemialgebraic
      ((multiprojectiveAffineChart (K := K) I).symm.trans
        (multiprojectiveAffineChart J)).source := by
    rw [hsrc_eq]
    exact .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  refine (isSemialgebraicOn_eval_div (fun q : Σ i, Fin (n i) ↦ P q.1 ((J q.1).succAbove q.2))
    (fun q : Σ i, Fin (n i) ↦ P q.1 (J q.1)) hsrc ?_).congr fun z _ ↦ ?_
  · intro z hz q
    rw [hsrc_eq, mem_iInter] at hz
    exact hz q.1
  · ext q
    simp [multiprojectiveAffineChart_symm_trans_apply, hP]

variable [IsStrictOrderedRing K] [Finite ι]

/-- Transporting a semialgebraic subset `B` of the `I`-chart image of `S` to chart `J` preserves
semialgebraicity, without assuming projection closure. -/
theorem isSemialgebraic_mixedAffineChart_image_inter
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))}
    {I J : ∀ i, Fin (n i + 1)} {B : Set ((σ ⊕ Σ i, Fin (n i)) → K)}
    (hSB : IsSemialgebraic ((mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I)) ∩ B)) :
    IsSemialgebraic
      (mixedAffineChart σ J ''
        ((S ∩ (mixedAffineOpen σ I ∩ mixedAffineChart σ I ⁻¹' B)) ∩ mixedAffineOpen σ J)) := by
  let P : ∀ i, Fin (n i + 1) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
    fun i ↦ Fin.insertNth (α := fun _ ↦ MvPolynomial (σ ⊕ Σ i, Fin (n i)) K) (J i) 1
      fun k ↦ X (.inr ⟨i, k⟩)
  have hP (w : (σ ⊕ Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
      eval w (P i j) = Fin.insertNth (α := fun _ ↦ K) (J i) 1 (fun k ↦ w (.inr ⟨i, k⟩)) j := by
    induction j using (J i).succAboveCases with
    | x => simp [P]
    | p k => simp [P]
  let UJ : Set ((σ ⊕ Σ i, Fin (n i)) → K) := ⋂ i : ι, {w | eval w (P i (I i)) ≠ 0}
  have hUJ : IsSemialgebraic UJ := .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  let f : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
    Sum.elim (fun a ↦ X (.inl a)) fun q ↦ P q.1 ((I q.1).succAbove q.2)
  let g : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i)) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ P q.1 (I q.1)
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
    · simp [f, g, hP, multiprojectiveAffineChart_symm_apply]
  have hUJ_mem : w ∈ UJ ↔ (mixedAffineChart σ J).symm w ∈ mixedAffineOpen σ I := by
    simp [UJ, hP, multiprojectiveAffineChart_symm_apply]
  rw [mem_inter_iff, mem_preimage, hTw, hUJ_mem]
  constructor
  · rintro ⟨y, ⟨⟨hyS, hyI, hyB⟩, hyJ⟩, rfl⟩
    have hsymm : (mixedAffineChart σ J).symm (mixedAffineChart σ J y) = y :=
      (mixedAffineChart σ J).left_inv (by rw [mixedAffineChart_source]; exact hyJ)
    rw [hsymm]
    exact ⟨hyI, ⟨y, ⟨hyS, hyI⟩, rfl⟩, hyB⟩
  · rintro ⟨hyI, ⟨y', ⟨hy'S, hy'I⟩, hchart_eq⟩, hyB⟩
    let y := (mixedAffineChart σ J).symm w
    have hyJ : y ∈ mixedAffineOpen σ J := mixedAffineChart_symm_mem_affineOpen J w
    have hyy' : y = y' := by
      have hly : (mixedAffineChart σ I).symm (mixedAffineChart σ I y) = y :=
        (mixedAffineChart σ I).left_inv (by rw [mixedAffineChart_source]; exact hyI)
      have hly' : (mixedAffineChart σ I).symm (mixedAffineChart σ I y') = y' :=
        (mixedAffineChart σ I).left_inv (by rw [mixedAffineChart_source]; exact hy'I)
      rw [← hly, ← hchart_eq, hly']
    exact ⟨y, ⟨⟨hyy' ▸ hy'S, hyI, hyB⟩, hyJ⟩, (mixedAffineChart σ J).right_inv (by simp)⟩

private theorem isSemialgebraic_mixedCone_inter_eval_ne_zero
    {S : Set ((σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K))} (I : ∀ i, Fin (n i + 1))
    (hI : IsSemialgebraic (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I))) :
    IsSemialgebraic (mixedCone S ∩ ⋂ i : ι, {w | eval w (X (.inr ⟨i, I i⟩)) ≠ 0}) := by
  let W : Set ((σ ⊕ Σ i, Fin (n i + 1)) → K) := ⋂ i : ι, {w | eval w (X (.inr ⟨i, I i⟩)) ≠ 0}
  have hW : IsSemialgebraic W := .iInter fun _ ↦ isSemialgebraic_eval_ne_zero _
  let f : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun a ↦ X (.inl a)) fun q ↦ X (.inr ⟨q.1, (I q.1).succAbove q.2⟩)
  let g : (σ ⊕ Σ i, Fin (n i)) → MvPolynomial (σ ⊕ Σ i, Fin (n i + 1)) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ X (.inr ⟨q.1, I q.1⟩)
  convert hI.inter_preimage_eval_div hW f g (fun w hw c ↦ ?_) using 1
  · ext w
    simp only [mem_inter_iff, mem_preimage]
    refine ⟨fun ⟨⟨hw, hwS⟩, hwI⟩ ↦ ⟨hwI, ?_⟩, fun ⟨hwI, hfw⟩ ↦ ?_⟩
    · have hwI' : ∀ i, w (.inr ⟨i, I i⟩) ≠ 0 := by simpa [W] using hwI
      let x : (σ → K) × ∀ i, ℙ K (Fin (n i + 1) → K) :=
        (w ∘ Sum.inl, fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw i))
      have hxI : x ∈ mixedAffineOpen σ I := by
        simp [x, Projectivization.mk_mem_affineOpen_iff, hwI']
      refine ⟨x, ⟨hwS, hxI⟩, ?_⟩
      ext (a | q) <;> simp [x, f, g]
    · have hwI' : ∀ i, w (.inr ⟨i, I i⟩) ≠ 0 := by simpa [W] using hwI
      have hw0 : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0 := fun i h0 ↦ hwI' i (congrFun h0 (I i))
      obtain ⟨x, ⟨hxS, hxI⟩, hxw⟩ := hfw
      refine ⟨⟨hw0, ?_⟩, hwI⟩
      have hx_eq : x = (w ∘ Sum.inl,
          fun i ↦ Projectivization.mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hw0 i)) := by
        have hlx : (mixedAffineChart σ I).symm (mixedAffineChart σ I x) = x :=
          (mixedAffineChart σ I).left_inv (by rw [mixedAffineChart_source]; exact hxI)
        rw [← hlx, hxw, mixedAffineChart_symm_apply]
        refine Prod.ext (funext fun a ↦ by simp [f, g]) (funext fun i ↦ ?_)
        simp only [multiprojectiveAffineChart_symm_apply, Projectivization.affineChart_symm_apply]
        have hcoord : (fun k ↦ eval w (f (.inr ⟨i, k⟩)) / eval w (g (.inr ⟨i, k⟩))) =
            fun k ↦ w (.inr ⟨i, (I i).succAbove k⟩) / w (.inr ⟨i, I i⟩) :=
          funext fun k ↦ by simp [f, g]
        rw [Function.comp_def]
        simp only [hcoord]
        exact (Projectivization.mk_eq_mk_iff' K _ _ _ (hw0 i)).2 ⟨(w (.inr ⟨i, I i⟩))⁻¹,
          (Fin.insertNth_one_div_eq_inv_smul (I i) (fun j ↦ w (.inr ⟨i, j⟩)) (hwI' i)).symm⟩
      rwa [← hx_eq]
  · cases c with
    | inl _ => simp [g]
    | inr q =>
      simp only [W, mem_iInter, mem_ofPred_eq] at hw
      simpa [g] using hw q.1

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
  convert (hchart I).preimage_comp Sum.inr using 1
  ext z
  simp only [mem_image, mem_inter_iff, mem_prod, mem_univ, true_and, mem_mixedAffineOpen,
    mem_preimage, Prod.exists]
  constructor
  · rintro ⟨_, p, ⟨hpS, hpI⟩, rfl⟩
    refine ⟨p, ⟨hpS, hpI⟩, ?_⟩
    ext q
    simp
  · rintro ⟨p, ⟨hpS, hpI⟩, hpz⟩
    refine ⟨Empty.elim, p, ⟨hpS, hpI⟩, ?_⟩
    ext (e | q)
    · exact e.elim
    · rw [mixedAffineChart_apply_inr]
      exact congrFun hpz q

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

/-! ### Local-to-global chart characterization over `ℝ` -/

section RealLocalToGlobal

variable {ι σ : Type*} {n : ι → ℕ}

/-- **Local-to-global chart criterion on mixed spaces with bounded affine projection.**
If `S ⊆ (σ → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` has bounded projection to `σ → ℝ` and is
locally semialgebraic at every point of `closure (Prod.fst '' S) ×ˢ univ` in some standard product
affine chart containing that point, then `S` is mixed semialgebraic. -/
theorem isMixedSemialgebraic_of_isBounded_fst [Finite ι] [Finite σ]
    {S : Set ((σ → ℝ) × ∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))}
    (hb : Bornology.IsBounded (Prod.fst '' S))
    (hloc : ∀ x ∈ closure (Prod.fst '' S) ×ˢ (univ : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))),
      ∃ I, x ∈ mixedAffineOpen σ I ∧
        SemialgebraicAt (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I))
          (mixedAffineChart σ I x)) :
    IsMixedSemialgebraic S := by
  cases nonempty_fintype ι
  cases nonempty_fintype σ
  let Kset := closure (Prod.fst '' S) ×ˢ (univ : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ)))
  have hK : IsCompact Kset := hb.isCompact_closure.prod isCompact_univ
  have hSK : S ⊆ Kset := fun x hx ↦ ⟨subset_closure ⟨x, hx, rfl⟩, mem_univ x.2⟩
  choose I hxI hsemi using fun x : Kset ↦ hloc x.1 x.2
  have hball (x : Kset) :
      ∃ ε > 0, IsSemialgebraic
        ((mixedAffineChart σ (I x) '' (S ∩ mixedAffineOpen σ (I x))) ∩
          ball (mixedAffineChart σ (I x) x.1) ε) :=
    semialgebraicAt_iff_exists_ball.1 (hsemi x)
  choose ε hε hSball using hball
  let B : Kset → Set ((σ ⊕ Σ i, Fin (n i)) → ℝ) :=
    fun x ↦ ball (mixedAffineChart σ (I x) x.1) (ε x)
  let V : Kset → Set ((σ → ℝ) × ∀ i, ℙ ℝ (Fin (n i + 1) → ℝ)) :=
    fun x ↦ mixedAffineOpen σ (I x) ∩ mixedAffineChart σ (I x) ⁻¹' B x
  have hV_open (x : Kset) : IsOpen (V x) := by
    simpa [V] using (mixedAffineOpenPartialHomeomorph (K := ℝ) σ (I x)).isOpen_inter_preimage
      isOpen_ball
  have hxV (x : Kset) : x.1 ∈ V x := ⟨hxI x, mem_ball_self (hε x)⟩
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ V ⟨x, hx⟩)
    fun x hx ↦ (hV_open ⟨x, hx⟩).mem_nhds (hxV ⟨x, hx⟩)
  rw [isMixedSemialgebraic_iff_forall_chart]
  intro J
  have hcover : mixedAffineChart σ J '' (S ∩ mixedAffineOpen σ J) =
      ⋃ x ∈ t, mixedAffineChart σ J '' ((S ∩ V x) ∩ mixedAffineOpen σ J) := by
    ext w
    simp only [mem_iUnion, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hyS, hyJ⟩, hyw⟩
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (hSK hyS))
      exact ⟨x, hxt, y, ⟨⟨hyS, hyx⟩, hyJ⟩, hyw⟩
    · rintro ⟨_, _, y, ⟨⟨hyS, _⟩, hyJ⟩, hyw⟩
      exact ⟨y, ⟨hyS, hyJ⟩, hyw⟩
  rw [hcover]
  exact .biUnion t.finite_toSet fun x _ ↦
    isSemialgebraic_mixedAffineChart_image_inter (hSball x)

/-- **Local-to-global chart criterion on real multiprojective space (existential chart form).**
A subset `S` of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` is multiprojective semialgebraic if and
only if at every point `p : M` there is a standard product affine chart `I` around `p` in which
`S` is locally semialgebraic (`TauCeti.SemialgebraicAt`) at `multiprojectiveAffineChart I p`. -/
theorem isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt [Finite ι]
    {S : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p, ∃ I : ∀ i, Fin (n i + 1), p ∈ multiprojectiveAffineOpen I ∧
        SemialgebraicAt (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I))
          (multiprojectiveAffineChart I p) := by
  refine ⟨fun hS p ↦ ?_, fun hloc ↦ ?_⟩
  · obtain ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen p
    exact ⟨I, hpI, (hS.isSemialgebraic_chart I).semialgebraicAt _⟩
  · rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)]
    refine isMixedSemialgebraic_of_isBounded_fst
      (isCompact_univ.isBounded.subset (subset_univ _)) fun ⟨x₀, p⟩ _ ↦ ?_
    obtain ⟨I, hpI, hSp⟩ := hloc p
    obtain ⟨U, hUo, hpU, hU, hsU⟩ := semialgebraicAt_def.1 hSp
    refine ⟨I, mem_mixedAffineOpen.2 hpI, ?_⟩
    have hchart : mixedAffineChart Empty I ''
        ((univ : Set (Empty → ℝ)) ×ˢ S ∩ mixedAffineOpen Empty I) =
        (fun w : (Empty ⊕ Σ i, Fin (n i)) → ℝ ↦ w ∘ Sum.inr) ⁻¹'
          (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I)) := by
      ext w
      simp only [mem_image, mem_inter_iff, mem_prod, mem_univ, true_and, mem_mixedAffineOpen,
        mem_preimage, Prod.exists]
      constructor
      · rintro ⟨_, q, ⟨hqS, hqI⟩, rfl⟩
        exact ⟨q, ⟨hqS, hqI⟩, rfl⟩
      · rintro ⟨q, ⟨hqS, hqI⟩, hqw⟩
        refine ⟨Empty.elim, q, ⟨hqS, hqI⟩, ?_⟩
        ext (e | c)
        · exact e.elim
        · rw [mixedAffineChart_apply_inr]
          exact congrFun hqw c
    have hpt : mixedAffineChart Empty I (x₀, p) ∘ Sum.inr = multiprojectiveAffineChart I p :=
      funext fun q ↦ mixedAffineChart_apply_inr I (x₀, p) q
    rw [hchart, semialgebraicAt_def]
    exact ⟨(fun w ↦ w ∘ Sum.inr) ⁻¹' U,
      hUo.preimage (continuous_pi fun q ↦ continuous_apply (Sum.inr q : Empty ⊕ Σ i, Fin (n i))),
      by rw [mem_preimage, hpt]; exact hpU,
      hU.preimage_comp Sum.inr, hsU.preimage_comp Sum.inr⟩

/-- **Local-to-global chart criterion on real multiprojective space (universal chart form).**
A subset `S` of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` is multiprojective semialgebraic if and
only if at every point `p : M` and in every standard product affine chart `I` containing `p`, the
chart image of `S` is locally semialgebraic at `multiprojectiveAffineChart I p`. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt [Finite ι]
    {S : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p (I : ∀ i, Fin (n i + 1)), p ∈ multiprojectiveAffineOpen I →
        SemialgebraicAt (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I))
          (multiprojectiveAffineChart I p) := by
  refine ⟨fun hS p I _ ↦ (hS.isSemialgebraic_chart I).semialgebraicAt _, fun h ↦ ?_⟩
  rw [isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt]
  intro p
  obtain ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen p
  exact ⟨I, hpI, h p I hpI⟩

end RealLocalToGlobal

end TauCeti
