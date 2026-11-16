/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Sum
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local
public import TauCeti.Topology.Algebra.Projectivization.Product

/-!
# Semialgebraic subsets of multiprojective spaces

Let `M = (i : ι) → ℙ K (κ i → K)` be a finite product of projective spaces over an ordered field
`K`, including the empty product (`IsEmpty ι`). Flattening homogeneous representatives of its
factors to `(Σ i, κ i) → K` defines the punctured-cone domain `TauCeti.piConeDomain κ K` of tuples
whose blocks are all nonzero, together with the quotient-preimage operator `TauCeti.piConePreimage`.
A subset `S ⊆ M` is *multiprojective semialgebraic* (`TauCeti.IsMultiprojectiveSemialgebraic S`)
when `piConePreimage S` is semialgebraic in `(Σ i, κ i) → K`.

Because `piConeDomain κ K` is itself semialgebraic when `ι` and every `κ i` are finite, the
multiprojective semialgebraic subsets form an algebra of sets closed under complements, finite
unions and intersections, products, and diagonals, without needing projection closure.

Because `rankOneProjector`, `piAffineChart`, and matrix row extraction
(`rankOneProjector_row_eq_self`) are explicit rational or coordinate maps with strictly positive
denominators on their domains, the first three characterizations below are equivalent over **any**
ordered field (without needing `HasSemialgebraicProjections K`), and over `ℝ` they are also
equivalent to local chart semialgebraicity at every point:

1. **Cone preimage**: `piConePreimage S` is semialgebraic in `(Σ i, κ i) → K`.
2. **Embedded projector image**: `piProjectorCoords '' S` is semialgebraic inside the flattened
   matrix space `(Σ i, κ i × κ i) → K`, where `piProjector` embeds `M` onto the product projector
   locus `TauCeti.piProjectorLocus κ K` and transports complements to relative complements inside
   that locus.
3. **Global standard product affine charts** (for `κ i = Fin (n i + 1)`): for every `I`, the chart
   image `piAffineChart I '' (S ∩ piAffineOpen I)` is semialgebraic in `(Σ i, Fin (n i)) → K`.
4. **Local chart semialgebraicity at every point of `M`** (over `ℝ`): every point `p ∈ M` admits a
   standard product affine chart `piAffineChart I` around `p` in which the image of
   `S ∩ piAffineOpen I` is semialgebraic at `piAffineChart I p`. The local-to-global implication
   uses compactness of `M` to cover `M` by finitely many bounded semialgebraic chart balls and
   pushes those patches into the product projector model.

## Main declarations

* `TauCeti.piConeDomain` and `TauCeti.piConePreimage`: the flattened punctured-cone domain and
  quotient preimage in `(Σ i, κ i) → K`.
* `TauCeti.IsSemialgebraic.inter_preimage_div_of_pos`: preimage of a semialgebraic set under a
  rational map whose denominators are strictly positive on a semialgebraic domain.
* `TauCeti.IsMultiprojectiveSemialgebraic`: semialgebraic subsets of `(i : ι) → ℙ K (κ i → K)`.
* `TauCeti.isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords`: equivalence
  with semialgebraicity of the embedded projector image.
* `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_piAffineChart`: equivalence with global
  semialgebraicity in every standard product affine chart.
* `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_exists_semialgebraicAt` and
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`: over `ℝ`, equivalence with
  local semialgebraicity at every point in the standard product affine charts.
* `TauCeti.IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image`,
  `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_preimage_multiprojective`, and
  `TauCeti.isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn`: image, preimage, and
  right-inverse projector transport between affine coordinate spaces and multiprojective spaces.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete (3) 36, Springer, 1998, §3.4.

The product projector and standard product affine-chart equivalences generalize the single-factor
real projector arguments in `TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`.
-/

public section

universe v

open Matrix MeasureTheory MvPolynomial Projectivization Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

section Topology

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

/-- The factorwise product projector map is continuous for the product topologies. -/
theorem continuous_piProjector :
    Continuous (piProjector : ((i : ι) → ℙ K (κ i → K)) → (i : ι) → Matrix (κ i) (κ i) K) := by
  rw [piProjector_def]
  exact continuous_pi fun i ↦ continuous_projector.comp (continuous_apply i)

/-- The flattened product projector map into `(Σ i, κ i × κ i) → K` is continuous. -/
theorem continuous_piProjectorCoords :
    Continuous (piProjectorCoords : ((i : ι) → ℙ K (κ i → K)) → (Σ i, κ i × κ i) → K) := by
  refine continuous_pi fun q ↦ ?_
  have h : (fun p : (i : ι) → ℙ K (κ i → K) ↦ piProjectorCoords p q) =
      fun p ↦ projector (p q.1) q.2.1 q.2.2 := funext fun p ↦ piProjectorCoords_apply p q
  rw [h]
  exact (continuous_projector.comp (continuous_apply q.1)).matrix_elem q.2.1 q.2.2

end Topology

section RealEmbedding

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Over `ℝ`, the factorwise product projector map is a closed embedding onto
`TauCeti.piProjectorLocus κ ℝ`. -/
theorem isClosedEmbedding_piProjector :
    IsClosedEmbedding
      (piProjector : ((i : ι) → ℙ ℝ (κ i → ℝ)) → (i : ι) → Matrix (κ i) (κ i) ℝ) :=
  continuous_piProjector.isClosedEmbedding piProjector_injective

/-- Over `ℝ`, the flattened product projector map is a closed embedding into
`(Σ i, κ i × κ i) → ℝ`. -/
theorem isClosedEmbedding_piProjectorCoords :
    IsClosedEmbedding
      (piProjectorCoords : ((i : ι) → ℙ ℝ (κ i → ℝ)) → (Σ i, κ i × κ i) → ℝ) :=
  continuous_piProjectorCoords.isClosedEmbedding piProjectorCoords_injective

end RealEmbedding

end Projectivization

namespace TauCeti

/-! ### Punctured-cone preimage and multiprojective semialgebraic sets -/

section Cone

variable {ι : Type*} {κ : ι → Type*}

/-- The flattened punctured-cone domain of `(i : ι) → ℙ K (κ i → K)`: tuples
`v : (Σ i, κ i) → K` whose `i`-th block `j ↦ v ⟨i, j⟩` is nonzero for every `i`. -/
def piConeDomain (κ : ι → Type*) (K : Type*) [Zero K] : Set ((Σ i, κ i) → K) :=
  {v | ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0}

theorem piConeDomain_def (κ : ι → Type*) (K : Type*) [Zero K] :
    piConeDomain κ K = {v | ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0} :=
  (rfl)

@[simp]
theorem mem_piConeDomain_iff {K : Type*} [Zero K] {v : (Σ i, κ i) → K} :
    v ∈ piConeDomain κ K ↔ ∀ i, (fun j ↦ v ⟨i, j⟩) ≠ 0 :=
  Iff.rfl

/-- For finite `ι` and finite blocks `κ i`, the flattened punctured-cone domain is semialgebraic:
each block is nonzero precisely when at least one of its coordinates is nonzero. -/
theorem isSemialgebraic_piConeDomain {R : Type*} [CommRing R] [LinearOrder R]
    [Finite ι] [∀ i, Finite (κ i)] :
    IsSemialgebraic (piConeDomain κ R) := by
  let xij (i : ι) (j : κ i) : MvPolynomial (Σ i, κ i) R := X ⟨i, j⟩
  have h : piConeDomain κ R =
      ⋂ i : ι, ⋃ j : κ i, {v : (Σ i, κ i) → R | eval v (xij i j) ≠ 0} := by
    ext v
    simp only [mem_piConeDomain_iff, Function.ne_iff, Pi.zero_apply, mem_iInter, mem_iUnion,
      Set.mem_ofPred_eq, xij, eval_X, ne_eq]
  rw [h]
  exact IsSemialgebraic.iInter fun i ↦
    IsSemialgebraic.iUnion fun j ↦ isSemialgebraic_eval_ne_zero (xij i j)

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
  ext v
  simp

@[simp]
theorem piConePreimage_univ :
    piConePreimage (univ : Set ((i : ι) → ℙ K (κ i → K))) = piConeDomain κ K := by
  ext v
  simp

theorem piConePreimage_compl (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage Sᶜ = piConeDomain κ K \ piConePreimage S := by
  ext v
  simp only [mem_piConePreimage_iff, mem_compl_iff, mem_sdiff, mem_piConeDomain_iff]
  exact ⟨fun ⟨hv, hS⟩ ↦ ⟨hv, fun ⟨_, h⟩ ↦ hS h⟩, fun ⟨hv, hS⟩ ↦ ⟨hv, fun h ↦ hS ⟨hv, h⟩⟩⟩

theorem piConePreimage_union (S T : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (S ∪ T) = piConePreimage S ∪ piConePreimage T := by
  ext v
  simp only [mem_piConePreimage_iff, mem_union]
  exact ⟨fun ⟨hv, h⟩ ↦ h.imp (fun hS ↦ ⟨hv, hS⟩) (fun hT ↦ ⟨hv, hT⟩),
    fun h ↦ h.elim (fun ⟨hv, hS⟩ ↦ ⟨hv, Or.inl hS⟩) (fun ⟨hv, hT⟩ ↦ ⟨hv, Or.inr hT⟩)⟩

theorem piConePreimage_inter (S T : Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (S ∩ T) = piConePreimage S ∩ piConePreimage T := by
  ext v
  simp only [mem_piConePreimage_iff, mem_inter_iff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, ⟨hv, hT⟩⟩, fun ⟨⟨hv, hS⟩, ⟨_, hT⟩⟩ ↦ ⟨hv, hS, hT⟩⟩

theorem piConePreimage_iUnion {α : Type*} (S : α → Set ((i : ι) → ℙ K (κ i → K))) :
    piConePreimage (⋃ a, S a) = ⋃ a, piConePreimage (S a) := by
  ext v
  simp only [mem_piConePreimage_iff, mem_iUnion]
  exact ⟨fun ⟨hv, a, ha⟩ ↦ ⟨a, hv, ha⟩, fun ⟨a, hv, ha⟩ ↦ ⟨hv, a, ha⟩⟩

end DivisionRing

end Cone

section RationalPreimage

variable {α β K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem exists_pos_eval_eq_mul_eval_div {u : Set (β → K)}
    {N D : α → MvPolynomial β K} (hD : ∀ x ∈ u, ∀ a, 0 < eval x (D a))
    (p : MvPolynomial α K) :
    ∃ A B : MvPolynomial β K, ∀ x ∈ u,
      0 < eval x B ∧ eval x A = eval x B * eval (fun a ↦ eval x (N a) / eval x (D a)) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨C c, 1, fun x _ ↦ ⟨by simp, by simp⟩⟩
  | add p q ihp ihq =>
    obtain ⟨A₁, B₁, h₁⟩ := ihp
    obtain ⟨A₂, B₂, h₂⟩ := ihq
    refine ⟨A₁ * B₂ + A₂ * B₁, B₁ * B₂, fun x hx ↦ ?_⟩
    obtain ⟨hB₁, hA₁⟩ := h₁ x hx
    obtain ⟨hB₂, hA₂⟩ := h₂ x hx
    refine ⟨by simp [mul_pos hB₁ hB₂], ?_⟩
    simp only [map_add, map_mul, hA₁, hA₂]
    ring
  | mul_X p a ihp =>
    obtain ⟨A₁, B₁, h₁⟩ := ihp
    refine ⟨A₁ * N a, B₁ * D a, fun x hx ↦ ?_⟩
    obtain ⟨hB₁, hA₁⟩ := h₁ x hx
    have hDa : 0 < eval x (D a) := hD x hx a
    refine ⟨by simp [mul_pos hB₁ hDa], ?_⟩
    simp only [map_mul, eval_X, hA₁]
    calc
      eval x B₁ * eval (fun b ↦ eval x (N b) / eval x (D b)) p * eval x (N a)
        = eval x B₁ * eval (fun b ↦ eval x (N b) / eval x (D b)) p *
            (eval x (D a) * (eval x (N a) / eval x (D a))) := by
          rw [mul_div_cancel₀ _ hDa.ne']
      _ = eval x B₁ * eval x (D a) *
            (eval (fun b ↦ eval x (N b) / eval x (D b)) p *
              (eval x (N a) / eval x (D a))) := by
          ring

/-- Over an ordered field, pulling a semialgebraic subset of `α → K` back along a coordinatewise
rational map `x ↦ (a ↦ N_a(x) / D_a(x))` whose denominators are strictly positive on a
semialgebraic domain `u` preserves semialgebraicity inside `u` (without needing projection
closure). -/
theorem IsSemialgebraic.inter_preimage_div_of_pos {u : Set (β → K)} (hu : IsSemialgebraic u)
    {s : Set (α → K)} (hs : IsSemialgebraic s) (N D : α → MvPolynomial β K)
    (hD : ∀ x ∈ u, ∀ a, 0 < eval x (D a)) :
    IsSemialgebraic (u ∩ (fun x a ↦ eval x (N a) / eval x (D a)) ⁻¹' s) := by
  refine hs.induction (fun p ↦ ?_) (fun p ↦ ?_) (fun t _ iht ↦ ?_) (fun t₁ t₂ _ _ ih₁ ih₂ ↦ ?_)
  · obtain ⟨A, B, hAB⟩ := exists_pos_eval_eq_mul_eval_div hD p
    have hset : u ∩ (fun x a ↦ eval x (N a) / eval x (D a)) ⁻¹' {y | eval y p = 0} =
        u ∩ {x | eval x A = 0} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_ofPred_eq]
      refine and_congr_right fun hx ↦ ?_
      obtain ⟨hB, hEq⟩ := hAB x hx
      rw [hEq, mul_eq_zero, or_iff_right hB.ne']
    rw [hset]
    exact hu.inter (isSemialgebraic_eval_eq_zero A)
  · obtain ⟨A, B, hAB⟩ := exists_pos_eval_eq_mul_eval_div hD p
    have hset : u ∩ (fun x a ↦ eval x (N a) / eval x (D a)) ⁻¹' {y | 0 < eval y p} =
        u ∩ {x | 0 < eval x A} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_ofPred_eq]
      refine and_congr_right fun hx ↦ ?_
      obtain ⟨hB, hEq⟩ := hAB x hx
      rw [hEq, mul_pos_iff_of_pos_left hB]
    rw [hset]
    exact hu.inter (isSemialgebraic_eval_pos A)
  · have hset : u ∩ (fun x a ↦ eval x (N a) / eval x (D a)) ⁻¹' tᶜ =
        u \ (u ∩ (fun x a ↦ eval x (N a) / eval x (D a)) ⁻¹' t) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
      tauto
    rw [hset]
    exact hu.sdiff iht
  · rw [preimage_union, inter_union_distrib_left]
    exact ih₁.union ih₂

end RationalPreimage

section MultiprojectiveSemialgebraic

variable {ι : Type*} {κ : ι → Type v} {K : Type*} [Field K] [LinearOrder K]

/-- A subset `S` of a multiprojective space `(i : ι) → ℙ K (κ i → K)` is *multiprojective
semialgebraic* if its preimage `piConePreimage S` in the flattened coordinate space `(Σ i, κ i) → K`
is semialgebraic. -/
def IsMultiprojectiveSemialgebraic (S : Set ((i : ι) → ℙ K (κ i → K))) : Prop :=
  IsSemialgebraic (piConePreimage S)

theorem isMultiprojectiveSemialgebraic_def {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic S ↔ IsSemialgebraic (piConePreimage S) :=
  Iff.rfl

@[simp]
theorem isMultiprojectiveSemialgebraic_empty :
    IsMultiprojectiveSemialgebraic (∅ : Set ((i : ι) → ℙ K (κ i → K))) := by
  simp [IsMultiprojectiveSemialgebraic]

theorem IsMultiprojectiveSemialgebraic.union {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∪ T) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_union]
  exact IsSemialgebraic.union hS hT

theorem IsMultiprojectiveSemialgebraic.inter {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∩ T) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_inter]
  exact IsSemialgebraic.inter hS hT

theorem IsMultiprojectiveSemialgebraic.iUnion {α : Type*} [Finite α]
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a, S a) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_iUnion]
  exact IsSemialgebraic.iUnion hS

theorem IsMultiprojectiveSemialgebraic.biUnion {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a ∈ t, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a ∈ t, S a) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]
  exact IsMultiprojectiveSemialgebraic.iUnion fun x ↦ hS x.1 x.2

section Finite

variable [Finite ι] [∀ i, Finite (κ i)]

/-- For finite `ι` and finite blocks `κ i`, the multiprojective semialgebraic subsets form an
algebra of sets. -/
theorem isSetAlgebra_setOf_isMultiprojectiveSemialgebraic :
    IsSetAlgebra {S : Set ((i : ι) → ℙ K (κ i → K)) | IsMultiprojectiveSemialgebraic S} where
  empty_mem := isMultiprojectiveSemialgebraic_empty
  compl_mem S hS := by
    rw [Set.mem_ofPred_eq, isMultiprojectiveSemialgebraic_def, piConePreimage_compl]
    exact isSemialgebraic_piConeDomain.sdiff hS
  union_mem _ _ hS hT := hS.union hT

@[simp]
theorem isMultiprojectiveSemialgebraic_univ :
    IsMultiprojectiveSemialgebraic (univ : Set ((i : ι) → ℙ K (κ i → K))) :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.univ_mem

theorem IsMultiprojectiveSemialgebraic.compl {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) :
    IsMultiprojectiveSemialgebraic Sᶜ :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.compl_mem hS

@[simp]
theorem isMultiprojectiveSemialgebraic_compl_iff {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic Sᶜ ↔ IsMultiprojectiveSemialgebraic S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, IsMultiprojectiveSemialgebraic.compl⟩

theorem IsMultiprojectiveSemialgebraic.sdiff {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S \ T) :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.sdiff_mem hS hT

theorem IsMultiprojectiveSemialgebraic.biInter {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a ∈ t, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a ∈ t, S a) := by
  simpa using isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.biInter_mem ht.toFinset
    (by simpa using hS)

theorem IsMultiprojectiveSemialgebraic.iInter {α : Type*} [Finite α]
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a, S a) := by
  simpa using IsMultiprojectiveSemialgebraic.biInter finite_univ fun a _ ↦ hS a

end Finite

/-! ### Products and diagonals of multiprojective spaces -/

/-- The product of two multiprojective semialgebraic sets is multiprojective semialgebraic. -/
theorem IsMultiprojectiveSemialgebraic.prod {ι' : Type*} {κ' : ι' → Type v}
    {S : Set ((i : ι) → ℙ K (κ i → K))} {T : Set ((j : ι') → ℙ K (κ' j → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' (S ×ˢ T)) := by
  rw [isMultiprojectiveSemialgebraic_def]
  convert (IsSemialgebraic.preimage_sumArrowEquivProdArrow_prod hS hT).preimage_comp
    (Equiv.sumSigmaDistrib (Sum.elim κ κ')).symm using 1
  ext w
  simp only [mem_piConePreimage_iff, mem_preimage, mem_prod, Sum.forall]
  exact ⟨fun ⟨⟨h1, h2⟩, hSw, hTw⟩ ↦ ⟨⟨h1, hSw⟩, ⟨h2, hTw⟩⟩,
    fun ⟨⟨h1, hSw⟩, ⟨h2, hTw⟩⟩ ↦ ⟨⟨h1, h2⟩, hSw, hTw⟩⟩

omit [LinearOrder K] in
/-- Two nonzero coordinate vectors over a field span the same line if and only if all their
`2 × 2` homogeneous minors vanish. -/
private theorem mk_eq_mk_iff_forall_mul_eq {α : Type*} {x y : α → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    mk K x hx = mk K y hy ↔ ∀ a b : α, x a * y b = x b * y a := by
  rw [mk_eq_mk_iff']
  constructor
  · rintro ⟨c, rfl⟩ a b
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨b₀, hb₀⟩ := Function.ne_iff.1 hy
    refine ⟨x b₀ / y b₀, funext fun a ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hb₀]
    exact (h a b₀).symm

/-- For finite `ι` and finite blocks `κ i`, the diagonal of `(i : ι) → ℙ K (κ i → K)` is
multiprojective semialgebraic: inside the punctured cone it is cut out by the `2 × 2` homogeneous
minor equations in each factor. -/
theorem isMultiprojectiveSemialgebraic_diagonal [Finite ι] [hκ : ∀ i, Finite (κ i)] :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ k → K)) ⁻¹'
        diagonal ((i : ι) → ℙ K (κ i → K))) := by
  have : ∀ k, Finite (Sum.elim κ κ k) := Sum.rec hκ hκ
  rw [isMultiprojectiveSemialgebraic_def]
  let minorPoly (i : ι) (a b : κ i) : MvPolynomial (Σ k : ι ⊕ ι, Sum.elim κ κ k) K :=
    X ⟨.inl i, a⟩ * X ⟨.inr i, b⟩
  have h : piConePreimage
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ k → K)) ⁻¹'
        diagonal ((i : ι) → ℙ K (κ i → K))) =
      piConeDomain (Sum.elim κ κ) K ∩
        ⋂ (i : ι) (a : κ i) (b : κ i),
          {w : (Σ k : ι ⊕ ι, Sum.elim κ κ k) → K |
            eval w (minorPoly i a b) = eval w (minorPoly i b a)} := by
    ext w
    simp only [mem_piConePreimage_iff, mem_inter_iff, mem_piConeDomain_iff, mem_iInter,
      Set.mem_ofPred_eq, minorPoly, map_mul, eval_X]
    constructor
    · rintro ⟨hw, heq⟩
      have hdiag : (fun i ↦ mk K (fun j ↦ w ⟨.inl i, j⟩) (hw (.inl i))) =
          fun i ↦ mk K (fun j ↦ w ⟨.inr i, j⟩) (hw (.inr i)) :=
        mem_diagonal_iff.1 (mem_preimage.1 heq)
      exact ⟨hw, fun i a b ↦
        (mk_eq_mk_iff_forall_mul_eq (hw (.inl i)) (hw (.inr i))).1 (congr_fun hdiag i) a b⟩
    · rintro ⟨hw, hmin⟩
      refine ⟨hw, mem_preimage.2 (mem_diagonal_iff.2 (funext fun i ↦ ?_))⟩
      exact (mk_eq_mk_iff_forall_mul_eq (hw (.inl i)) (hw (.inr i))).2 (hmin i)
  rw [h]
  exact isSemialgebraic_piConeDomain.inter <|
    IsSemialgebraic.iInter fun i ↦ IsSemialgebraic.iInter fun a ↦
      IsSemialgebraic.iInter fun b ↦ isSemialgebraic_eval_eq (minorPoly i a b) (minorPoly i b a)

/-- For finite `ι` and finite blocks `κ i`, every singleton in `(i : ι) → ℙ K (κ i → K)` is
multiprojective semialgebraic. -/
@[simp]
theorem isMultiprojectiveSemialgebraic_singleton [Finite ι] [∀ i, Finite (κ i)]
    (p : (i : ι) → ℙ K (κ i → K)) :
    IsMultiprojectiveSemialgebraic ({p} : Set ((i : ι) → ℙ K (κ i → K))) := by
  rw [isMultiprojectiveSemialgebraic_def]
  let m₁ (i : ι) (a b : κ i) : MvPolynomial (Σ i, κ i) K := C ((p i).rep b) * X ⟨i, a⟩
  let m₂ (i : ι) (a b : κ i) : MvPolynomial (Σ i, κ i) K := C ((p i).rep a) * X ⟨i, b⟩
  have h : piConePreimage ({p} : Set ((i : ι) → ℙ K (κ i → K))) =
      piConeDomain κ K ∩
        ⋂ (i : ι) (a : κ i) (b : κ i), {v | eval v (m₁ i a b) = eval v (m₂ i a b)} := by
    ext v
    simp only [mem_piConePreimage_iff, mem_singleton_iff, funext_iff, mem_inter_iff,
      mem_piConeDomain_iff, mem_iInter, Set.mem_ofPred_eq, m₁, m₂, map_mul, eval_C, eval_X]
    refine ⟨fun ⟨hv, heq⟩ ↦ ⟨hv, fun i a b ↦ ?_⟩, fun ⟨hv, hmin⟩ ↦ ⟨hv, fun i ↦ ?_⟩⟩
    · have hi : mk K (fun j ↦ v ⟨i, j⟩) (hv i) = mk K (p i).rep (p i).rep_ne_zero := by
        rw [heq i, (p i).mk_rep]
      simpa [mul_comm] using (mk_eq_mk_iff_forall_mul_eq (hv i) (p i).rep_ne_zero).1 hi a b
    · rw [← (p i).mk_rep]
      exact (mk_eq_mk_iff_forall_mul_eq (hv i) (p i).rep_ne_zero).2 fun a b ↦ by
        simpa [mul_comm] using hmin i a b
  rw [h]
  exact isSemialgebraic_piConeDomain.inter <|
    IsSemialgebraic.iInter fun i ↦ IsSemialgebraic.iInter fun a ↦
      IsSemialgebraic.iInter fun b ↦ isSemialgebraic_eval_eq (m₁ i a b) (m₂ i a b)

end MultiprojectiveSemialgebraic

/-! ### The product projector locus and embedded semialgebraicity -/

section ProductProjector

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Over `ℝ`, the product projector locus is compact. -/
theorem isCompact_piProjectorLocus : IsCompact (piProjectorLocus κ ℝ) := by
  rw [piProjectorLocus_def]
  exact isCompact_univ_pi fun i ↦ isCompact_projectorLocus

variable {K : Type*} [Field K]

/-- The product projector locus is closed over a Hausdorff topological ring. -/
theorem isClosed_piProjectorLocus [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] :
    IsClosed (piProjectorLocus κ K) := by
  rw [piProjectorLocus_def]
  exact isClosed_set_pi fun i _ ↦ isClosed_projectorLocus

/-- For finite `ι`, the flattened product projector locus is semialgebraic in
`(Σ i, κ i × κ i) → K`. -/
theorem isSemialgebraic_piProjectorLocus [LinearOrder K] [Finite ι] :
    IsSemialgebraic (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) := by
  let emb (i : ι) : κ i × κ i → Σ i, κ i × κ i := fun p ↦ ⟨i, p⟩
  have h : piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K =
      ⋂ i : ι, (fun (a : (Σ i, κ i × κ i) → K) ↦ a ∘ emb i) ⁻¹'
        {b : κ i × κ i → K | Matrix.of (Function.curry b) ∈ projectorLocus (κ i) K} := by
    ext a
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine mem_iInter.2 fun i ↦ ?_
      have hmat : Matrix.of (Function.curry (piMatrixLinearEquiv K κ κ K A ∘ emb i)) = A i := by
        ext j k
        simp [Function.curry, emb]
      exact mem_preimage.2
        (by simpa only [Set.mem_ofPred_eq, hmat] using mem_piProjectorLocus.1 hA i)
    · intro ha
      refine ⟨(piMatrixLinearEquiv K κ κ K).symm a, mem_piProjectorLocus.2 fun i ↦ ?_,
        (piMatrixLinearEquiv K κ κ K).apply_symm_apply a⟩
      have hi : Matrix.of (Function.curry (a ∘ emb i)) ∈ projectorLocus (κ i) K :=
        mem_preimage.1 (mem_iInter.1 ha i)
      have hmat : (piMatrixLinearEquiv K κ κ K).symm a i =
          Matrix.of (Function.curry (a ∘ emb i)) := by
        ext j k
        simp [Function.curry, emb]
      rwa [hmat]
  rw [h]
  exact IsSemialgebraic.iInter fun i ↦
    (isSemialgebraic_projectorLocus (ι := κ i) (K := K)).preimage_comp (emb i)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- **Complement transport in flattened matrix coordinates.** For finite `ι`, the embedded image of
`Sᶜ` under `piProjectorCoords` is semialgebraic if and only if `piProjectorCoords '' S` is, since
the two are relative complements inside the semialgebraic flattened product projector locus. -/
theorem isSemialgebraic_image_piProjectorCoords_compl_iff [Finite ι]
    {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsSemialgebraic (piProjectorCoords '' Sᶜ) ↔ IsSemialgebraic (piProjectorCoords '' S) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc : piProjectorCoords '' S =
        (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) \ (piProjectorCoords '' Sᶜ) := by
      simpa only [compl_compl] using image_piProjectorCoords_compl Sᶜ
    rw [hc]
    exact isSemialgebraic_piProjectorLocus.sdiff h
  · rw [image_piProjectorCoords_compl]
    exact isSemialgebraic_piProjectorLocus.sdiff h

/-- On the flattened punctured cone `piConeDomain κ K`, the factorwise rank-one projector map into
flattened matrix entries is semialgebraic: its graph is cut out by the polynomial equations
`(vᵢᵀ vᵢ) Aᵢ = vᵢ vᵢᵀ`. -/
theorem isSemialgebraicOn_rankOneProjector_piConeDomain [Finite ι] :
    IsSemialgebraicOn
      (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
        rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2)
      (piConeDomain κ K) := by
  refine isSemialgebraicOn_of_forall_eq_iff isSemialgebraic_piConeDomain
    (fun q : Σ i, κ i × κ i ↦
      (∑ r : κ q.1, X (.inl ⟨q.1, r⟩) * X (.inl ⟨q.1, r⟩)) * X (.inr q) -
        X (.inl ⟨q.1, q.2.1⟩) * X (.inl ⟨q.1, q.2.2⟩))
    fun v hv A ↦ ?_
  simp only [funext_iff, map_sub, map_mul, map_sum, eval_X, Sum.elim_inl, Sum.elim_inr]
  refine forall_congr' fun ⟨i, a, b⟩ ↦ ?_
  have hs : (fun j ↦ v ⟨i, j⟩) ⬝ᵥ (fun j ↦ v ⟨i, j⟩) ≠ 0 :=
    dotProduct_self_eq_zero.not.mpr (hv i)
  rw [rankOneProjector_apply, div_eq_iff hs, sub_eq_zero, eq_comm]
  simp [dotProduct, mul_comm]

private theorem mk_piProjectorCoords_row_eq {i : ι} (p : (i : ι) → ℙ K (κ i → K)) {r : κ i}
    (hr : projector (p i) r r ≠ 0) (hv : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) ≠ 0) :
    mk K (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) hv = p i :=
  projector_injective <| by
    have hrow : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) = projector (p i) r :=
      funext fun j ↦ piProjectorCoords_apply p ⟨i, r, j⟩
    rw [projector_mk, hrow]
    exact rankOneProjector_row_eq_self (projector_mem_projectorLocus (p i)) hr

private theorem image_piProjectorCoords_eq_inter_iUnion (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjectorCoords '' S =
      (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) ∩
        ⋃ R : ∀ i, κ i,
          (⋂ i : ι, {a | eval a (X ⟨i, R i, R i⟩ : MvPolynomial (Σ i, κ i × κ i) K) ≠ 0}) ∩
            (fun a : (Σ i, κ i × κ i) → K ↦ a ∘ fun q : Σ i, κ i ↦ ⟨q.1, R q.1, q.2⟩) ⁻¹'
              piConePreimage S := by
  ext a
  constructor
  · rintro ⟨p, hpS, rfl⟩
    obtain ⟨R, hpR⟩ := exists_mem_piAffineOpen p
    have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 :=
      (projector_apply_self_pos_iff.2 (mem_piAffineOpen_iff.1 hpR i)).ne'
    have hv (i : ι) : (fun j ↦ piProjectorCoords p ⟨i, R i, j⟩) ≠ 0 :=
      fun h0 ↦ hR i (by simpa using congr_fun h0 (R i))
    refine ⟨(range_piProjectorCoords (κ := κ) (K := K)) ▸ mem_range_self p,
      mem_iUnion.2 ⟨R, ?_, hv, ?_⟩⟩
    · exact mem_iInter.2 fun i ↦ by simpa using hR i
    · convert hpS using 1
      exact funext fun i ↦ mk_piProjectorCoords_row_eq p (hR i) (hv i)
  · rintro ⟨haL, haU⟩
    obtain ⟨p, rfl⟩ := (range_piProjectorCoords (κ := κ) (K := K)).symm ▸ haL
    obtain ⟨R, hdiag, hv, hpS⟩ := mem_iUnion.1 haU
    have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 := by
      simpa using mem_iInter.1 hdiag i
    refine ⟨p, ?_, rfl⟩
    convert hpS using 1
    exact (funext fun i ↦ mk_piProjectorCoords_row_eq p (hR i) (hv i)).symm

private theorem inter_preimage_rankOneProjector_piProjectorCoords
    (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConeDomain κ K ∩
        (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
          rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2) ⁻¹' (piProjectorCoords '' S) =
      piConePreimage S := by
  ext v
  constructor
  · rintro ⟨hv, q, hqS, hq⟩
    refine ⟨hv, ?_⟩
    have heq : piProjectorCoords (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) =
        piProjectorCoords q := by
      ext ⟨i, j, k⟩
      simpa using (congr_fun hq ⟨i, j, k⟩).symm
    rwa [piProjectorCoords_injective heq]
  · rintro ⟨hv, hp⟩
    refine ⟨hv, fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i), hp, ?_⟩
    ext ⟨i, j, k⟩
    simp

/-- **Equivalence of cone and embedded-projector semialgebraicity.** Over any ordered field, a
subset `S` of a finite multiprojective space `(i : ι) → ℙ K (κ i → K)` is multiprojective
semialgebraic if and only if its image `piProjectorCoords '' S` in the flattened matrix space
`(Σ i, κ i × κ i) → K` is semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords
    [Finite ι] {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic S ↔ IsSemialgebraic (piProjectorCoords '' S) := by
  constructor
  · intro hS
    rw [image_piProjectorCoords_eq_inter_iUnion]
    exact (isSemialgebraic_piProjectorLocus (κ := κ) (K := K)).inter <|
      IsSemialgebraic.iUnion fun R ↦
        (IsSemialgebraic.iInter fun i ↦
          isSemialgebraic_eval_ne_zero
            (X ⟨i, R i, R i⟩ : MvPolynomial (Σ i, κ i × κ i) K)).inter
          (hS.preimage_comp fun q ↦ (⟨q.1, R q.1, q.2⟩ : Σ i, κ i × κ i))
  · intro himg
    rw [isMultiprojectiveSemialgebraic_def, ← inter_preimage_rankOneProjector_piProjectorCoords]
    let N (q : Σ i, κ i × κ i) : MvPolynomial (Σ i, κ i) K :=
      X ⟨q.1, q.2.1⟩ * X ⟨q.1, q.2.2⟩
    let D (q : Σ i, κ i × κ i) : MvPolynomial (Σ i, κ i) K :=
      ∑ r : κ q.1, X ⟨q.1, r⟩ * X ⟨q.1, r⟩
    have hfun : (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
        rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2) =
        fun v q ↦ eval v (N q) / eval v (D q) := by
      ext v q
      simp [N, D, rankOneProjector_apply, dotProduct]
    rw [hfun]
    exact isSemialgebraic_piConeDomain.inter_preimage_div_of_pos himg N D fun v hv q ↦ by
      simpa [D, dotProduct] using lt_of_le_of_ne (dotProduct_self_nonneg fun r ↦ v ⟨q.1, r⟩)
        (Ne.symm (dotProduct_self_eq_zero.not.mpr (hv q.1)))

/-- If `piProjectorCoords ∘ f` is semialgebraic on a finite-coordinate affine set `s`, then
`f '' s` is multiprojective semialgebraic. -/
theorem IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image {σ : Type*}
    [Finite ι] [HasSemialgebraicProjections K] [Finite σ]
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s) :
    IsMultiprojectiveSemialgebraic (f '' s) := by
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords, ← image_comp]
  exact hf.isSemialgebraic_image

/-- If `piProjectorCoords ∘ f` is semialgebraic on `s`, then the preimage in `s` of every
multiprojective semialgebraic subset `T` is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage_multiprojective {σ : Type*}
    [Finite ι] [HasSemialgebraicProjections K]
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s)
    {T : Set ((i : ι) → ℙ K (κ i → K))} (hT : IsMultiprojectiveSemialgebraic T) :
    IsSemialgebraic (s ∩ f ⁻¹' T) := by
  cases nonempty_fintype ι
  have hT' := isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords.1 hT
  have hpre : s ∩ f ⁻¹' T = s ∩ (piProjectorCoords ∘ f) ⁻¹' (piProjectorCoords '' T) := by
    ext x
    simp [piProjectorCoords_injective.mem_set_image]
  rw [hpre]
  exact hf.isSemialgebraic_inter_preimage hT'

end ProductProjector

section RightInverse

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {K : Type*} [Field K] [LinearOrder K]

omit [LinearOrder K] in
private theorem projector_apply_eq_one_of_forall_eq {α : Type*} [Fintype α]
    (q : ℙ K (α → K)) {a₀ : α} (ha₀ : ∀ b : α, b = a₀) :
    projector q a₀ a₀ = 1 := by
  induction q using ind with
  | h w hw =>
    have hw₀ : w a₀ ≠ 0 := by
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hw
      rwa [ha₀ b] at hb
    have hsum : (∑ r : α, w r * w r) = w a₀ * w a₀ :=
      Finset.sum_eq_single a₀ (fun b _ hb ↦ (hb (ha₀ b)).elim)
        (fun h ↦ (h (Finset.mem_univ a₀)).elim)
    rw [projector_mk, rankOneProjector_apply, dotProduct, hsum,
      div_self (mul_ne_zero hw₀ hw₀)]

private theorem eq_empty_of_infinite_of_rightInvOn [Infinite ι]
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) :
    s = ∅ := by
  classical
  obtain ⟨F, hF⟩ := hs.exists_finset_mem_iff_of_eqOn
  obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset (F.image Sigma.fst)
  have hnotMem (a b : κ i₀) : (⟨i₀, a, b⟩ : Σ i, κ i × κ i) ∉ F :=
    fun h ↦ hi₀ (Finset.mem_image.2 ⟨⟨i₀, a, b⟩, h, rfl⟩)
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨a₀, _⟩ := Function.ne_iff.1 (τ x i₀).rep_ne_zero
  by_cases hsub : ∃ b₀ : κ i₀, b₀ ≠ a₀
  · obtain ⟨b₀, hb₀⟩ := hsub
    let y := Function.update (Function.update x ⟨i₀, a₀, b₀⟩ 1) ⟨i₀, b₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      have h1 : q ≠ ⟨i₀, b₀, a₀⟩ := fun h ↦ hnotMem b₀ a₀ (h ▸ hq)
      have h2 : q ≠ ⟨i₀, a₀, b₀⟩ := fun h ↦ hnotMem a₀ b₀ (h ▸ hq)
      simp [y, h1, h2]).1 hx
    have hne : (⟨i₀, a₀, b₀⟩ : Σ i, κ i × κ i) ≠ ⟨i₀, b₀, a₀⟩ := by
      simp [hb₀.symm]
    have hsymm : projector (τ y i₀) a₀ b₀ = projector (τ y i₀) b₀ a₀ := by
      induction (τ y i₀) using ind with
      | h w hw => rw [projector_mk, rankOneProjector_apply, rankOneProjector_apply, mul_comm]
    have hya : projector (τ y i₀) a₀ b₀ = 1 := by
      simpa [y, hne] using congr_fun (hτ y hy) ⟨i₀, a₀, b₀⟩
    have hyb : projector (τ y i₀) b₀ a₀ = 0 := by
      simpa [y] using congr_fun (hτ y hy) ⟨i₀, b₀, a₀⟩
    exact one_ne_zero (hya.symm.trans (hsymm.trans hyb))
  · push Not at hsub
    let y := Function.update x ⟨i₀, a₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      have h1 : q ≠ ⟨i₀, a₀, a₀⟩ := fun h ↦ hnotMem a₀ a₀ (h ▸ hq)
      simp [y, h1]).1 hx
    have hy0 : projector (τ y i₀) a₀ a₀ = 0 := by
      simpa [y] using congr_fun (hτ y hy) ⟨i₀, a₀, a₀⟩
    exact one_ne_zero ((projector_apply_eq_one_of_forall_eq (τ y i₀) hsub).symm.trans hy0)

/-- **Inverse projector transport on semialgebraic subsets of the flattened product projector
locus.** Any map `τ : ((Σ i, κ i × κ i) → K) → (i : ι) → ℙ K (κ i → K)` that is a right inverse of
`piProjectorCoords` on a semialgebraic set `s` satisfies
`IsSemialgebraicOn (piProjectorCoords ∘ τ) s`, so `τ` pushes semialgebraic subsets of `s` forward to
multiprojective semialgebraic sets and pulls multiprojective semialgebraic sets back to
semialgebraic subsets of `s`. -/
theorem isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) :
    IsSemialgebraicOn (piProjectorCoords ∘ τ) s := by
  by_cases hι : Finite ι
  · exact (isSemialgebraicMap_id.isSemialgebraicOn hs).congr fun x hx ↦ (hτ x hx).symm
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    rw [eq_empty_of_infinite_of_rightInvOn hs hτ]
    exact isSemialgebraicOn_empty _

end RightInverse

/-! ### Standard product affine charts and local-to-global semialgebraicity -/

section ProductAffineCharts

variable {ι : Type*} {n : ι → ℕ} {K : Type*} [Field K] [LinearOrder K]

/-- Every multiprojective semialgebraic set is semialgebraic in every standard product affine chart
(requiring neither finiteness of `ι` nor projection closure). -/
theorem IsMultiprojectiveSemialgebraic.isSemialgebraic_image_piAffineChart
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} (hS : IsMultiprojectiveSemialgebraic S)
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I)) := by
  let L : (Σ i, Fin (n i + 1)) → MvPolynomial (Σ i, Fin (n i)) K := fun ⟨i, j⟩ ↦
    Fin.insertNth (α := fun _ ↦ MvPolynomial (Σ i, Fin (n i)) K) (I i) 1 (fun k ↦ X ⟨i, k⟩) j
  have hL (z : (Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
      eval z (L ⟨i, j⟩) = Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) j := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove (I i) j <;> simp [L]
  have hv (z : (Σ i, Fin (n i)) → K) (i : ι) : (fun j ↦ eval z (L ⟨i, j⟩)) ≠ 0 := by
    simpa only [funext (hL z i)] using Fin.insertNth_one_ne_zero (I i) fun k ↦ z ⟨i, k⟩
  have hmk (z : (Σ i, Fin (n i)) → K) (hvz : ∀ i, (fun j ↦ eval z (L ⟨i, j⟩)) ≠ 0) :
      (fun i ↦ mk K (fun j ↦ eval z (L ⟨i, j⟩)) (hvz i)) = (piAffineChart I).symm z := by
    ext i
    simp [funext (hL z i)]
  convert IsSemialgebraic.preimage_eval hS L using 1
  ext z
  constructor
  · rintro ⟨p, ⟨hpS, hpI⟩, rfl⟩
    refine ⟨hv _, ?_⟩
    rw [hmk, (piAffineChart I).left_inv (by simpa using hpI)]
    exact hpS
  · rintro ⟨hvz, hpS⟩
    rw [hmk] at hpS
    exact ⟨(piAffineChart I).symm z, ⟨hpS, by simp⟩, (piAffineChart I).right_inv (by simp)⟩

variable [IsStrictOrderedRing K]

/-- For finite `ι`, the inverse of a standard product affine chart followed by `piProjectorCoords`
is a semialgebraic map. -/
theorem isSemialgebraicMap_piProjectorCoords_piAffineChart_symm [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicMap
      (piProjectorCoords ∘ (piAffineChart (K := K) I).symm) := by
  rw [← isSemialgebraicOn_univ]
  let V : ∀ i, Fin (n i + 1) →
      MvPolynomial ((Σ i, Fin (n i)) ⊕ (Σ i, Fin (n i + 1) × Fin (n i + 1))) K :=
    fun i ↦ Fin.insertNth (I i) 1 fun k ↦ X (.inl ⟨i, k⟩)
  refine isSemialgebraicOn_of_forall_eq_iff isSemialgebraic_univ
    (fun q ↦ (∑ r, V q.1 r * V q.1 r) * X (.inr q) - V q.1 q.2.1 * V q.1 q.2.2)
    fun z _ A ↦ ?_
  have hV (i : ι) (r : Fin (n i + 1)) :
      eval (Sum.elim z A) (V i r) =
        Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) r := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove (I i) r <;> simp [V]
  simp only [Function.comp_apply, funext_iff, map_sub, map_mul, map_sum, hV, eval_X, Sum.elim_inr]
  refine forall_congr' fun ⟨i, a, b⟩ ↦ ?_
  set v : Fin (n i + 1) → K := Fin.insertNth (I i) 1 fun k ↦ z ⟨i, k⟩
  have hs : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero (I i) _)
  rw [piProjectorCoords_apply, piAffineChart_symm_apply, affineChart_symm_apply, projector_mk,
    rankOneProjector_apply, div_eq_iff hs, sub_eq_zero, eq_comm]
  simp [v, dotProduct, mul_comm]

/-- For finite `ι`, the image of `piAffineOpen I` under `piProjectorCoords` is semialgebraic. -/
theorem isSemialgebraic_image_piProjectorCoords_piAffineOpen [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (piProjectorCoords '' piAffineOpen (K := K) I) := by
  let xI (i : ι) : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K := X ⟨i, I i, I i⟩
  have hcoords (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) :
      piProjectorCoords p =
        piMatrixLinearEquiv K (fun i ↦ Fin (n i + 1)) (fun i ↦ Fin (n i + 1)) K
          (piProjector p) :=
    congr_fun piProjectorCoords_def p
  have h : piProjectorCoords '' piAffineOpen (K := K) I =
      (piMatrixLinearEquiv K (fun i ↦ Fin (n i + 1)) (fun i ↦ Fin (n i + 1)) K ''
        piProjectorLocus (fun i ↦ Fin (n i + 1)) K) ∩
        ⋂ i : ι, {a | eval a (xI i) ≠ 0} := by
    ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨piProjector p, piProjector_mem_piProjectorLocus p, (hcoords p).symm⟩,
        mem_iInter.2 fun i ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, xI, eval_X, piProjectorCoords_apply, ne_eq]
      exact projector_apply_self_eq_zero_iff.not.2 (not_not.2 (mem_piAffineOpen_iff.1 hp i))
    · rintro ⟨⟨A, hA, rfl⟩, hdiag⟩
      have hmem : A ∈ piProjector '' piAffineOpen I := by
        rw [image_piProjector_piAffineOpen]
        refine ⟨hA, fun i ↦ ?_⟩
        simpa only [Set.mem_ofPred_eq, xI, eval_X, piMatrixLinearEquiv_apply] using
          mem_iInter.1 hdiag i
      obtain ⟨p, hp, hAp⟩ := hmem
      exact ⟨p, hp, by rw [hcoords, hAp]⟩
  rw [h]
  exact (isSemialgebraic_piProjectorLocus (κ := fun i ↦ Fin (n i + 1)) (K := K)).inter <|
    IsSemialgebraic.iInter fun i ↦ isSemialgebraic_eval_ne_zero (xI i)

/-- For finite `ι`, the standard product affine chart `piAffineChart I` read in the flattened
product projector model is semialgebraic on `piProjectorCoords '' piAffineOpen I`. -/
theorem isSemialgebraicOn_piProjectorCoords_piAffineChart [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicOn
      (fun (a : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K) (q : Σ i, Fin (n i)) ↦
        a ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ / a ⟨q.1, I q.1, I q.1⟩)
      (piProjectorCoords '' piAffineOpen (K := K) I) := by
  refine isSemialgebraicOn_of_forall_eq_iff (isSemialgebraic_image_piProjectorCoords_piAffineOpen I)
    (fun q ↦ X (.inl ⟨q.1, I q.1, I q.1⟩) * X (.inr q) -
      X (.inl ⟨q.1, (I q.1).succAbove q.2, I q.1⟩))
    fun a ha w ↦ ?_
  obtain ⟨p, hp, rfl⟩ := ha
  simp only [funext_iff, map_sub, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr]
  refine forall_congr' fun ⟨i, k⟩ ↦ ?_
  have hii : piProjectorCoords p ⟨i, I i, I i⟩ ≠ 0 := by
    rw [piProjectorCoords_apply]
    exact projector_apply_self_eq_zero_iff.not.2 (not_not.2 (mem_piAffineOpen_iff.1 hp i))
  rw [div_eq_iff hii, eq_comm, ← sub_eq_zero]
  simp [mul_comm]

private theorem isSemialgebraic_image_piProjectorCoords_inter_piAffineOpen [Finite ι]
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    (hSI : IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I))) :
    IsSemialgebraic (piProjectorCoords '' (S ∩ piAffineOpen I)) := by
  let N (q : Σ i, Fin (n i)) : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K :=
    X ⟨q.1, (I q.1).succAbove q.2, I q.1⟩
  let D (q : Σ i, Fin (n i)) : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K :=
    X ⟨q.1, I q.1, I q.1⟩
  have hpos : ∀ a ∈ piProjectorCoords '' piAffineOpen (K := K) I, ∀ q, 0 < eval a (D q) := by
    rintro _ ⟨p, hp, rfl⟩ ⟨i, _⟩
    simpa [D] using projector_apply_self_pos_iff.2 (mem_piAffineOpen_iff.1 hp i)
  convert (isSemialgebraic_image_piProjectorCoords_piAffineOpen I).inter_preimage_div_of_pos
    hSI N D hpos using 1
  ext a
  constructor
  · rintro ⟨p, ⟨hpS, hpI⟩, rfl⟩
    refine ⟨⟨p, hpI, rfl⟩, ?_⟩
    have hdiv : (fun q ↦ eval (piProjectorCoords p) (N q) / eval (piProjectorCoords p) (D q)) =
        piAffineChart I p := by
      simpa [N, D] using (piAffineChart_eq_piProjectorCoords_div I p).symm
    exact mem_preimage.2 (hdiv ▸ ⟨p, ⟨hpS, hpI⟩, rfl⟩)
  · rintro ⟨⟨p, hpI, rfl⟩, hmem⟩
    have hdiv : (fun q ↦ eval (piProjectorCoords p) (N q) / eval (piProjectorCoords p) (D q)) =
        piAffineChart I p := by
      simpa [N, D] using (piAffineChart_eq_piProjectorCoords_div I p).symm
    obtain ⟨q, ⟨hqS, hqI⟩, hqp⟩ := hdiv ▸ mem_preimage.1 hmem
    have hpq : q = p := (piAffineChart I).injOn (by simpa using hqI) (by simpa using hpI) hqp
    exact ⟨p, ⟨hpq ▸ hqS, hpI⟩, rfl⟩

/-- **Chart characterization of multiprojective semialgebraic sets.** Over any ordered field, a
subset `S` of a finite multiprojective space `(i : ι) → ℙ K (Fin (n i + 1) → K)` is
multiprojective semialgebraic if and only if its image in every standard product affine chart is
semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_piAffineChart [Finite ι]
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1), IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I)) := by
  refine ⟨fun hS I ↦ hS.isSemialgebraic_image_piAffineChart I, fun hS ↦ ?_⟩
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords]
  convert IsSemialgebraic.iUnion
    (fun I ↦ isSemialgebraic_image_piProjectorCoords_inter_piAffineOpen (hS I)) using 1
  ext a
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨p, hpS, rfl⟩
    obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
    exact ⟨I, p, ⟨hpS, hpI⟩, rfl⟩
  · rintro ⟨I, p, ⟨hpS, _⟩, rfl⟩
    exact ⟨p, hpS, rfl⟩

end ProductAffineCharts

section RealProductAffineCharts

variable {ι : Type*} {n : ι → ℕ} [Finite ι]

/-- **Local-to-global semialgebraicity on real multiprojective space.** If at every point `p` of
`M = (i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ)` there is a standard product affine chart `I` containing
`p` in which `S` is semialgebraic at `piAffineChart I p`, then `S` is globally multiprojective
semialgebraic. Compactness of `M` covers it by finitely many bounded semialgebraic chart balls,
whose images under `piProjectorCoords` cover `piProjectorCoords '' S`. -/
theorem isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))}
    (hS : ∀ p, ∃ I : ∀ i, Fin (n i + 1), p ∈ piAffineOpen I ∧
      SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p)) :
    IsMultiprojectiveSemialgebraic S := by
  cases nonempty_fintype ι
  choose I hpI hloc using hS
  choose ε hε hball using fun p ↦ (semialgebraicAt_iff_exists_ball.1 (hloc p))
  let W : ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ)) → Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ)) :=
    fun p ↦ piAffineOpen (I p) ∩ piAffineChart (I p) ⁻¹' Metric.ball (piAffineChart (I p) p) (ε p)
  have hWo (p) : IsOpen (W p) :=
    (continuousOn_piAffineChart (I p)).isOpen_inter_preimage
      (isOpen_piAffineOpen (I p)) Metric.isOpen_ball
  have hpW (p) : p ∈ W p := ⟨hpI p, Metric.mem_ball_self (hε p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover W fun p _ ↦ (hWo p).mem_nhds (hpW p)
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords]
  convert IsSemialgebraic.biUnion t.finite_toSet fun p _ ↦
    (isSemialgebraicMap_piProjectorCoords_piAffineChart_symm (I p)).isSemialgebraic_image (hball p)
    using 1
  ext a
  simp only [mem_image, mem_iUnion, exists_prop, Function.comp_apply]
  constructor
  · rintro ⟨q, hqS, rfl⟩
    obtain ⟨p, hpt, hqW⟩ := mem_iUnion₂.1 (ht.2 (mem_univ q))
    refine ⟨p, hpt, piAffineChart (I p) q, ⟨⟨q, ⟨hqS, hqW.1⟩, rfl⟩, hqW.2⟩, ?_⟩
    rw [(piAffineChart (I p)).left_inv (by simpa using hqW.1)]
  · rintro ⟨p, _, _, ⟨⟨q, ⟨hqS, hqI⟩, rfl⟩, _⟩, rfl⟩
    refine ⟨q, hqS, ?_⟩
    rw [(piAffineChart (I p)).left_inv (by simpa using hqI)]

/-- Over `ℝ`, a subset of a finite multiprojective space is multiprojective semialgebraic if and
only if every ambient point admits a standard product affine chart in which the set is locally
semialgebraic at that point. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_exists_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p, ∃ I : ∀ i, Fin (n i + 1), p ∈ piAffineOpen I ∧
        SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p) := by
  refine ⟨fun hS p ↦ ?_, isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt⟩
  obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
  exact ⟨I, hpI, (hS.isSemialgebraic_image_piAffineChart I).semialgebraicAt _⟩

/-- Over `ℝ`, a subset of a finite multiprojective space is multiprojective semialgebraic if and
only if it is locally semialgebraic at every ambient point in every standard product affine chart
containing that point. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p (I : ∀ i, Fin (n i + 1)), p ∈ piAffineOpen I →
        SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p) := by
  refine ⟨fun hS p I _ ↦ (hS.isSemialgebraic_image_piAffineChart I).semialgebraicAt _, fun hS ↦ ?_⟩
  refine isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt fun p ↦ ?_
  obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
  exact ⟨I, hpI, hS p I hpI⟩

end RealProductAffineCharts

end TauCeti
