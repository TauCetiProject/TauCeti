/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Projectivization.Basic

/-!
# Mixed affine-multiprojective semialgebraic sets

Let `K` be an ordered field, `σ` an affine coordinate index type, and
`M = (i : ι) → ℙ K (κ i → K)` a product of projective spaces over `K`. A subset `S` of the mixed
ambient space `(σ → K) × M` is *affine-multiprojective semialgebraic*
(`TauCeti.IsAffineMultiprojectiveSemialgebraic S`) when its preimage
`TauCeti.affineMultiprojectiveConePreimage S` in `σ ⊕ (Σ i, κ i) → K`—obtained by keeping the
affine coordinates on `σ` and lifting the multiprojective coordinates to the flattened punctured
cone `TauCeti.piConeDomain κ K`—is semialgebraic.

When `ι` and each `κ i` are finite, these subsets form an algebra of sets for arbitrary `σ`, closed
under products, factor swaps, diagonals, and singletons, and compatible with pure affine
semialgebraic sets (`s ×ˢ univ`) and pure multiprojective semialgebraic sets (`Prod.snd ⁻¹' T`).
Over **any** ordered field (without needing `HasSemialgebraicProjections K`), semialgebraicity of
`S` is equivalent both to semialgebraicity of its image under the injective coordinate-and-projector
embedding `Projectivization.affinePiProjectorCoords` into `σ ⊕ (Σ i, κ i × κ i) → K`, and (for
`κ i = Fin (n i + 1)`) to semialgebraicity in every standard product affine chart
`Projectivization.affinePiAffineChart σ I`, again with no finiteness hypothesis on `σ`.

## Main declarations

* `Projectivization.affinePiProjectorCoords` and `Projectivization.affinePiAffineChart`: the
  flattened coordinate-and-projector embedding and standard product affine charts on mixed spaces.
* `TauCeti.affineMultiprojectiveConeDomain`, `TauCeti.affineMultiprojectiveConePreimage`, and
  `TauCeti.IsAffineMultiprojectiveSemialgebraic`: cone preimages and semialgebraic subsets of
  `(σ → K) × ((i : ι) → ℙ K (κ i → K))`.
* `TauCeti.prodAffineMultiprojectiveEquiv`: identification of a mixed space over `σ ⊕ τ` and
  `ι ⊕ ι'` with the Cartesian product of two mixed spaces.
* `TauCeti.isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords`:
  equivalence with semialgebraicity of the embedded projector image.
* `TauCeti.isAffineMultiprojectiveSemialgebraic_iff_forall_affinePiAffineChart`: equivalence with
  semialgebraicity in every standard product affine chart.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete (3) 36, Springer, 1998, §§2.2, 3.4.
-/

public section

universe v

open Matrix MeasureTheory MvPolynomial Projectivization Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

section AffinePiProjectorCoords

variable {σ ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)] {K : Type*} [Field K]

/-- Embed `(σ → K) × ((i : ι) → ℙ K (κ i → K))` into `σ ⊕ (Σ i, κ i × κ i) → K` by pairing the
affine coordinates with the flattened product projector coordinates `piProjectorCoords`. -/
def affinePiProjectorCoords (x : (σ → K) × ((i : ι) → ℙ K (κ i → K))) :
    σ ⊕ (Σ i, κ i × κ i) → K :=
  Sum.elim x.1 (piProjectorCoords x.2)

theorem affinePiProjectorCoords_def :
    (affinePiProjectorCoords :
        (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ ⊕ (Σ i, κ i × κ i) → K)) =
      fun x ↦ Sum.elim x.1 (piProjectorCoords x.2) :=
  (rfl)

@[simp]
theorem affinePiProjectorCoords_comp_inl (x : (σ → K) × ((i : ι) → ℙ K (κ i → K))) :
    affinePiProjectorCoords x ∘ Sum.inl = x.1 :=
  (rfl)

@[simp]
theorem affinePiProjectorCoords_comp_inr (x : (σ → K) × ((i : ι) → ℙ K (κ i → K))) :
    affinePiProjectorCoords x ∘ Sum.inr = piProjectorCoords x.2 :=
  (rfl)

@[simp]
theorem affinePiProjectorCoords_inl (x : (σ → K) × ((i : ι) → ℙ K (κ i → K))) (s : σ) :
    affinePiProjectorCoords x (.inl s) = x.1 s :=
  (rfl)

@[simp]
theorem affinePiProjectorCoords_inr (x : (σ → K) × ((i : ι) → ℙ K (κ i → K)))
    (q : Σ i, κ i × κ i) :
    affinePiProjectorCoords x (.inr q) = piProjectorCoords x.2 q :=
  (rfl)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field, `affinePiProjectorCoords` is injective. -/
theorem affinePiProjectorCoords_injective :
    Function.Injective
      (affinePiProjectorCoords :
        (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ ⊕ (Σ i, κ i × κ i) → K)) := by
  rintro ⟨x₁, p₁⟩ ⟨x₂, p₂⟩ h
  have hx : x₁ = x₂ := funext fun s ↦ congr_fun h (.inl s)
  have hp : p₁ = p₂ := piProjectorCoords_injective (funext fun q ↦ congr_fun h (.inr q))
  exact Prod.ext hx hp

/-- Over an ordered field, the range of `affinePiProjectorCoords` consists of tuples whose right
block lies in the flattened product projector locus. -/
theorem range_affinePiProjectorCoords :
    range (affinePiProjectorCoords :
        (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ ⊕ (Σ i, κ i × κ i) → K)) =
      (fun z : σ ⊕ (Σ i, κ i × κ i) → K ↦ z ∘ Sum.inr) ⁻¹'
        (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) := by
  ext z
  simp only [mem_range, mem_preimage, ← range_piProjectorCoords]
  constructor
  · rintro ⟨⟨x, p⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, hp⟩
    refine ⟨⟨z ∘ Sum.inl, p⟩, ?_⟩
    ext (s | q)
    · rfl
    · exact congr_fun hp q

/-- `affinePiProjectorCoords` is continuous for the product topologies. -/
theorem continuous_affinePiProjectorCoords
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] :
    Continuous
      (affinePiProjectorCoords :
        (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ ⊕ (Σ i, κ i × κ i) → K)) := by
  refine continuous_pi fun u ↦ ?_
  cases u with
  | inl s => exact (continuous_apply s).comp continuous_fst
  | inr q => exact ((continuous_apply q).comp continuous_piProjectorCoords).comp continuous_snd

end AffinePiProjectorCoords

section AffinePiAffineChart

variable (σ : Type*) {ι : Type*} {n : ι → ℕ} {K : Type*} [Field K]

/-- The standard product affine chart on `(σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K))`, keeping
the affine coordinates on `σ` and applying `piAffineChart I` on the multiprojective factor. -/
noncomputable def affinePiAffineChart (I : ∀ i, Fin (n i + 1)) :
    PartialEquiv ((σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K)))
      (σ ⊕ (Σ i, Fin (n i)) → K) :=
  ((PartialEquiv.refl (σ → K)).prod (piAffineChart I)).trans
    (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i)) K).symm.toPartialEquiv

@[simp]
theorem affinePiAffineChart_source (I : ∀ i, Fin (n i + 1)) :
    (affinePiAffineChart σ (K := K) I).source = univ ×ˢ piAffineOpen I := by
  ext ⟨x, p⟩
  simp [affinePiAffineChart]

@[simp]
theorem affinePiAffineChart_target (I : ∀ i, Fin (n i + 1)) :
    (affinePiAffineChart σ (K := K) I).target = univ := by
  ext z
  simp [affinePiAffineChart]

@[simp]
theorem affinePiAffineChart_apply (I : ∀ i, Fin (n i + 1)) (x : σ → K)
    (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) :
    affinePiAffineChart σ I (x, p) = Sum.elim x (piAffineChart I p) :=
  (rfl)

@[simp]
theorem affinePiAffineChart_symm_apply (I : ∀ i, Fin (n i + 1))
    (z : σ ⊕ (Σ i, Fin (n i)) → K) :
    (affinePiAffineChart σ I).symm z =
      (z ∘ Sum.inl, (piAffineChart I).symm (z ∘ Sum.inr)) :=
  (rfl)

end AffinePiAffineChart

end Projectivization

namespace TauCeti

/-! ### Mixed affine-multiprojective cone preimages and equivalences -/

section MixedCone

variable {σ ι : Type*} {κ : ι → Type v}

/-- The domain of flattened coordinates `w : σ ⊕ (Σ i, κ i) → K` whose multiprojective block lies
in `piConeDomain κ K`. -/
def affineMultiprojectiveConeDomain (σ : Type*) (κ : ι → Type v) (K : Type*) [Zero K] :
    Set (σ ⊕ (Σ i, κ i) → K) :=
  {w | w ∘ Sum.inr ∈ piConeDomain κ K}

@[simp]
theorem mem_affineMultiprojectiveConeDomain_iff {K : Type*} [Zero K]
    {w : σ ⊕ (Σ i, κ i) → K} :
    w ∈ affineMultiprojectiveConeDomain σ κ K ↔ ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0 := by
  simp [affineMultiprojectiveConeDomain]

/-- For finite `ι` and finite blocks `κ i`, `affineMultiprojectiveConeDomain σ κ R` is
semialgebraic for arbitrary `σ`. -/
theorem isSemialgebraic_affineMultiprojectiveConeDomain {R : Type*} [CommRing R] [LinearOrder R]
    [Finite ι] [∀ i, Finite (κ i)] :
    IsSemialgebraic (affineMultiprojectiveConeDomain σ κ R) :=
  isSemialgebraic_piConeDomain.preimage_comp Sum.inr

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- The cone preimage in `σ ⊕ (Σ i, κ i) → K` of a subset `S` of
`(σ → K) × ((i : ι) → ℙ K (κ i → K))`. -/
def affineMultiprojectiveConePreimage
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    Set (σ ⊕ (Σ i, κ i) → K) :=
  {w | ∃ hv : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0,
    (w ∘ Sum.inl, fun i ↦ mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hv i)) ∈ S}

@[simp]
theorem mem_affineMultiprojectiveConePreimage_iff
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} {w : σ ⊕ (Σ i, κ i) → K} :
    w ∈ affineMultiprojectiveConePreimage S ↔
      ∃ hv : ∀ i, (fun j ↦ w (.inr ⟨i, j⟩)) ≠ 0,
        (w ∘ Sum.inl, fun i ↦ mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hv i)) ∈ S :=
  Iff.rfl

@[simp]
theorem affineMultiprojectiveConePreimage_empty :
    affineMultiprojectiveConePreimage
      (∅ : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) = ∅ := by
  ext w
  simp

@[simp]
theorem affineMultiprojectiveConePreimage_univ :
    affineMultiprojectiveConePreimage
      (univ : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) =
      affineMultiprojectiveConeDomain σ κ K := by
  ext w
  simp

theorem affineMultiprojectiveConePreimage_compl
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    affineMultiprojectiveConePreimage Sᶜ =
      affineMultiprojectiveConeDomain σ κ K \ affineMultiprojectiveConePreimage S := by
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_compl_iff, mem_sdiff,
    mem_affineMultiprojectiveConeDomain_iff]
  exact ⟨fun ⟨hv, hS⟩ ↦ ⟨hv, fun ⟨_, h⟩ ↦ hS h⟩, fun ⟨hv, hS⟩ ↦ ⟨hv, fun h ↦ hS ⟨hv, h⟩⟩⟩

theorem affineMultiprojectiveConePreimage_union
    (S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    affineMultiprojectiveConePreimage (S ∪ T) =
      affineMultiprojectiveConePreimage S ∪ affineMultiprojectiveConePreimage T := by
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_union]
  exact ⟨fun ⟨hv, h⟩ ↦ h.imp (fun hS ↦ ⟨hv, hS⟩) (fun hT ↦ ⟨hv, hT⟩),
    fun h ↦ h.elim (fun ⟨hv, hS⟩ ↦ ⟨hv, Or.inl hS⟩) (fun ⟨hv, hT⟩ ↦ ⟨hv, Or.inr hT⟩)⟩

theorem affineMultiprojectiveConePreimage_inter
    (S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    affineMultiprojectiveConePreimage (S ∩ T) =
      affineMultiprojectiveConePreimage S ∩ affineMultiprojectiveConePreimage T := by
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_inter_iff]
  exact ⟨fun ⟨hv, hS, hT⟩ ↦ ⟨⟨hv, hS⟩, ⟨hv, hT⟩⟩, fun ⟨⟨hv, hS⟩, ⟨_, hT⟩⟩ ↦ ⟨hv, hS, hT⟩⟩

theorem affineMultiprojectiveConePreimage_iUnion {α : Type*}
    (S : α → Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    affineMultiprojectiveConePreimage (⋃ a, S a) =
      ⋃ a, affineMultiprojectiveConePreimage (S a) := by
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_iUnion]
  exact ⟨fun ⟨hv, a, ha⟩ ↦ ⟨a, hv, ha⟩, fun ⟨a, hv, ha⟩ ↦ ⟨hv, a, ha⟩⟩

theorem affineMultiprojectiveConePreimage_prod (s : Set (σ → K))
    (T : Set ((i : ι) → ℙ K (κ i → K))) :
    affineMultiprojectiveConePreimage (s ×ˢ T) =
      Equiv.sumArrowEquivProdArrow σ (Σ i, κ i) K ⁻¹' (s ×ˢ piConePreimage T) := by
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_prod, mem_preimage,
    Equiv.sumArrowEquivProdArrow_apply_snd, mem_piConePreimage_iff]
  exact ⟨fun ⟨hv, hs, hT⟩ ↦ ⟨hs, hv, hT⟩, fun ⟨hs, hv, hT⟩ ↦ ⟨hv, hs, hT⟩⟩

end DivisionRing

end MixedCone

section MixedEquiv

variable (σ τ : Type*) {ι ι' : Type*} (κ : ι → Type v) (κ' : ι' → Type v)

private def graphConeIndexEquiv :
    ((σ ⊕ τ) ⊕ (Σ k : ι ⊕ ι', Sum.elim κ κ' k)) ≃
      ((σ ⊕ (Σ i, κ i)) ⊕ (τ ⊕ (Σ j, κ' j))) :=
  ((Equiv.refl (σ ⊕ τ)).sumCongr (Equiv.sumSigmaDistrib (Sum.elim κ κ'))).trans
    (Equiv.sumSumSumComm σ τ (Σ i, κ i) (Σ j, κ' j))

/-- Index equivalence matching the flattened projector coordinates of a product mixed space with
the disjoint union of the two factor projector coordinate spaces. -/
def graphProjectorIndexEquiv :
    ((σ ⊕ τ) ⊕ (Σ k : ι ⊕ ι', Sum.elim κ κ' k × Sum.elim κ κ' k)) ≃
      ((σ ⊕ (Σ i, κ i × κ i)) ⊕ (τ ⊕ (Σ j, κ' j × κ' j))) :=
  ((Equiv.refl (σ ⊕ τ)).sumCongr
    (Equiv.sumSigmaDistrib fun k ↦ Sum.elim κ κ' k × Sum.elim κ κ' k)).trans
    (Equiv.sumSumSumComm σ τ (Σ i, κ i × κ i) (Σ j, κ' j × κ' j))

@[simp]
theorem graphProjectorIndexEquiv_symm_inl_inl (s : σ) :
    (graphProjectorIndexEquiv σ τ κ κ').symm (.inl (.inl s)) = .inl (.inl s) :=
  (rfl)

@[simp]
theorem graphProjectorIndexEquiv_symm_inr_inl (t : τ) :
    (graphProjectorIndexEquiv σ τ κ κ').symm (.inr (.inl t)) = .inl (.inr t) :=
  (rfl)

@[simp]
theorem graphProjectorIndexEquiv_symm_inl_inr (i : ι) (a b : κ i) :
    (graphProjectorIndexEquiv σ τ κ κ').symm (.inl (.inr ⟨i, a, b⟩)) = .inr ⟨.inl i, a, b⟩ :=
  (rfl)

@[simp]
theorem graphProjectorIndexEquiv_symm_inr_inr (j : ι') (c d : κ' j) :
    (graphProjectorIndexEquiv σ τ κ κ').symm (.inr (.inr ⟨j, c, d⟩)) = .inr ⟨.inr j, c, d⟩ :=
  (rfl)

variable (K : Type*) [DivisionRing K]

/-- Rearrange a single mixed affine-multiprojective space over `σ ⊕ τ` and `ι ⊕ ι'` into the
Cartesian product of the two mixed spaces. -/
def prodAffineMultiprojectiveEquiv :
    ((σ ⊕ τ → K) × ((k : ι ⊕ ι') → ℙ K (Sum.elim κ κ' k → K))) ≃
      (((σ → K) × ((i : ι) → ℙ K (κ i → K))) ×
       ((τ → K) × ((j : ι') → ℙ K (κ' j → K)))) :=
  ((Equiv.sumArrowEquivProdArrow σ τ K).prodCongr
    (Equiv.sumPiEquivProdPi fun k ↦ ℙ K (Sum.elim κ κ' k → K))).trans
    (Equiv.prodProdProdComm (σ → K) (τ → K)
      ((i : ι) → ℙ K (κ i → K)) ((j : ι') → ℙ K (κ' j → K)))

@[simp]
theorem prodAffineMultiprojectiveEquiv_apply
    (z : (σ ⊕ τ → K) × ((k : ι ⊕ ι') → ℙ K (Sum.elim κ κ' k → K))) :
    prodAffineMultiprojectiveEquiv σ τ κ κ' K z =
      ((z.1 ∘ Sum.inl, fun i ↦ z.2 (.inl i)), (z.1 ∘ Sum.inr, fun j ↦ z.2 (.inr j))) :=
  (rfl)

@[simp]
theorem prodAffineMultiprojectiveEquiv_symm_fst
    (x : (σ → K) × ((i : ι) → ℙ K (κ i → K)))
    (y : (τ → K) × ((j : ι') → ℙ K (κ' j → K))) :
    ((prodAffineMultiprojectiveEquiv σ τ κ κ' K).symm (x, y)).1 = Sum.elim x.1 y.1 :=
  (rfl)

@[simp]
theorem prodAffineMultiprojectiveEquiv_symm_snd
    (x : (σ → K) × ((i : ι) → ℙ K (κ i → K)))
    (y : (τ → K) × ((j : ι') → ℙ K (κ' j → K))) :
    ((prodAffineMultiprojectiveEquiv σ τ κ κ' K).symm (x, y)).2 =
      (Equiv.sumPiEquivProdPi fun k ↦ ℙ K (Sum.elim κ κ' k → K)).symm (x.2, y.2) :=
  (rfl)

end MixedEquiv

/-! ### Mixed affine-multiprojective semialgebraic sets -/

section AffineMultiprojectiveSemialgebraic

variable {σ ι : Type*} {κ : ι → Type v} {K : Type*} [Field K] [LinearOrder K]

/-- A subset `S` of `(σ → K) × ((i : ι) → ℙ K (κ i → K))` is *affine-multiprojective
semialgebraic* if its cone preimage in `σ ⊕ (Σ i, κ i) → K` is semialgebraic. -/
def IsAffineMultiprojectiveSemialgebraic
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) : Prop :=
  IsSemialgebraic (affineMultiprojectiveConePreimage S)

theorem isAffineMultiprojectiveSemialgebraic_def
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraic S ↔
      IsSemialgebraic (affineMultiprojectiveConePreimage S) :=
  Iff.rfl

@[simp]
theorem isAffineMultiprojectiveSemialgebraic_empty :
    IsAffineMultiprojectiveSemialgebraic
      (∅ : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) := by
  simp [IsAffineMultiprojectiveSemialgebraic]

theorem IsAffineMultiprojectiveSemialgebraic.union
    {S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S)
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (S ∪ T) := by
  rw [isAffineMultiprojectiveSemialgebraic_def, affineMultiprojectiveConePreimage_union]
  exact IsSemialgebraic.union hS hT

theorem IsAffineMultiprojectiveSemialgebraic.inter
    {S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S)
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (S ∩ T) := by
  rw [isAffineMultiprojectiveSemialgebraic_def, affineMultiprojectiveConePreimage_inter]
  exact IsSemialgebraic.inter hS hT

theorem IsAffineMultiprojectiveSemialgebraic.iUnion {α : Type*} [Finite α]
    {S : α → Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : ∀ a, IsAffineMultiprojectiveSemialgebraic (S a)) :
    IsAffineMultiprojectiveSemialgebraic (⋃ a, S a) := by
  rw [isAffineMultiprojectiveSemialgebraic_def, affineMultiprojectiveConePreimage_iUnion]
  exact IsSemialgebraic.iUnion hS

theorem IsAffineMultiprojectiveSemialgebraic.biUnion {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : ∀ a ∈ t, IsAffineMultiprojectiveSemialgebraic (S a)) :
    IsAffineMultiprojectiveSemialgebraic (⋃ a ∈ t, S a) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]
  exact IsAffineMultiprojectiveSemialgebraic.iUnion fun x ↦ hS x.1 x.2

/-- The Cartesian product of an affine semialgebraic set and a multiprojective semialgebraic set
is affine-multiprojective semialgebraic. -/
theorem IsSemialgebraic.prod_multiprojective {s : Set (σ → K)}
    {T : Set ((i : ι) → ℙ K (κ i → K))}
    (hs : IsSemialgebraic s) (hT : IsMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (s ×ˢ T) := by
  rw [isAffineMultiprojectiveSemialgebraic_def, affineMultiprojectiveConePreimage_prod]
  exact hs.preimage_sumArrowEquivProdArrow_prod (isMultiprojectiveSemialgebraic_def.1 hT)

/-- Pulling a subset of `(i : ι) → ℙ K (κ i → K)` back along `Prod.snd` gives an
affine-multiprojective semialgebraic set if and only if the subset is multiprojective
semialgebraic (requiring neither finiteness nor projection closure). -/
@[simp]
theorem isAffineMultiprojectiveSemialgebraic_preimage_snd_iff
    {T : Set ((i : ι) → ℙ K (κ i → K))} :
    IsAffineMultiprojectiveSemialgebraic
        ((Prod.snd : (σ → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' T) ↔
      IsMultiprojectiveSemialgebraic T := by
  have heq : (Prod.snd : (σ → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' T = univ ×ˢ T := by
    ext ⟨x, p⟩
    simp
  rw [heq]
  refine ⟨fun h ↦ ?_, fun hT ↦ isSemialgebraic_univ.prod_multiprojective hT⟩
  rw [isMultiprojectiveSemialgebraic_def]
  let L : σ ⊕ (Σ i, κ i) → MvPolynomial (Σ i, κ i) K :=
    Sum.elim (fun _ ↦ 0) (fun q ↦ X q)
  convert IsSemialgebraic.preimage_eval h L using 1
  ext v
  simp [L]

section Finite

variable [Finite ι] [∀ i, Finite (κ i)]

/-- For finite `ι` and finite blocks `κ i`, the affine-multiprojective semialgebraic subsets form
an algebra of sets for arbitrary `σ`. -/
theorem isSetAlgebra_setOf_isAffineMultiprojectiveSemialgebraic :
    IsSetAlgebra
      {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K))) |
        IsAffineMultiprojectiveSemialgebraic S} where
  empty_mem := isAffineMultiprojectiveSemialgebraic_empty
  compl_mem S hS := by
    rw [Set.mem_ofPred_eq, isAffineMultiprojectiveSemialgebraic_def,
      affineMultiprojectiveConePreimage_compl]
    exact isSemialgebraic_affineMultiprojectiveConeDomain.sdiff hS
  union_mem _ _ hS hT := hS.union hT

@[simp]
theorem isAffineMultiprojectiveSemialgebraic_univ :
    IsAffineMultiprojectiveSemialgebraic
      (univ : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :=
  isSetAlgebra_setOf_isAffineMultiprojectiveSemialgebraic.univ_mem

theorem IsAffineMultiprojectiveSemialgebraic.compl
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) :
    IsAffineMultiprojectiveSemialgebraic Sᶜ :=
  isSetAlgebra_setOf_isAffineMultiprojectiveSemialgebraic.compl_mem hS

@[simp]
theorem isAffineMultiprojectiveSemialgebraic_compl_iff
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraic Sᶜ ↔ IsAffineMultiprojectiveSemialgebraic S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, IsAffineMultiprojectiveSemialgebraic.compl⟩

theorem IsAffineMultiprojectiveSemialgebraic.sdiff
    {S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S)
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (S \ T) :=
  isSetAlgebra_setOf_isAffineMultiprojectiveSemialgebraic.sdiff_mem hS hT

theorem IsAffineMultiprojectiveSemialgebraic.biInter {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : ∀ a ∈ t, IsAffineMultiprojectiveSemialgebraic (S a)) :
    IsAffineMultiprojectiveSemialgebraic (⋂ a ∈ t, S a) := by
  simpa using isSetAlgebra_setOf_isAffineMultiprojectiveSemialgebraic.biInter_mem ht.toFinset
    (by simpa using hS)

theorem IsAffineMultiprojectiveSemialgebraic.iInter {α : Type*} [Finite α]
    {S : α → Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : ∀ a, IsAffineMultiprojectiveSemialgebraic (S a)) :
    IsAffineMultiprojectiveSemialgebraic (⋂ a, S a) := by
  simpa using IsAffineMultiprojectiveSemialgebraic.biInter finite_univ fun a _ ↦ hS a

end Finite

/-- The product of two affine-multiprojective semialgebraic sets is affine-multiprojective
semialgebraic. -/
theorem IsAffineMultiprojectiveSemialgebraic.prod {τ ι' : Type*} {κ' : ι' → Type v}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    {T : Set ((τ → K) × ((j : ι') → ℙ K (κ' j → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S)
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' (S ×ˢ T)) := by
  rw [isAffineMultiprojectiveSemialgebraic_def]
  convert (IsSemialgebraic.preimage_sumArrowEquivProdArrow_prod hS hT).preimage_comp
    (graphConeIndexEquiv σ τ κ κ').symm using 1
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_preimage,
    prodAffineMultiprojectiveEquiv_apply, mem_prod, Sum.forall, graphConeIndexEquiv]
  exact ⟨fun ⟨⟨h1, h2⟩, hSw, hTw⟩ ↦ ⟨⟨h1, hSw⟩, ⟨h2, hTw⟩⟩,
    fun ⟨⟨h1, hSw⟩, ⟨h2, hTw⟩⟩ ↦ ⟨⟨h1, h2⟩, hSw, hTw⟩⟩

/-- Swapping the two factors of a product mixed space preserves affine-multiprojective
semialgebraicity. -/
theorem IsAffineMultiprojectiveSemialgebraic.prod_swap {τ ι' : Type*} {κ' : ι' → Type v}
    {U : Set (((σ → K) × ((i : ι) → ℙ K (κ i → K))) ×
              ((τ → K) × ((j : ι') → ℙ K (κ' j → K))))}
    (hU : IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' U)) :
    IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv τ σ κ' κ K ⁻¹' (Prod.swap ⁻¹' U)) := by
  rw [isAffineMultiprojectiveSemialgebraic_def]
  let swapIdx : (σ ⊕ τ) ⊕ (Σ k : ι ⊕ ι', Sum.elim κ κ' k) →
      (τ ⊕ σ) ⊕ (Σ k : ι' ⊕ ι, Sum.elim κ' κ k) :=
    Sum.map (Equiv.sumComm σ τ) fun
      | ⟨.inl i, a⟩ => ⟨.inr i, a⟩
      | ⟨.inr j, b⟩ => ⟨.inl j, b⟩
  convert IsSemialgebraic.preimage_comp hU swapIdx using 1
  ext w
  simp only [mem_affineMultiprojectiveConePreimage_iff, mem_preimage,
    prodAffineMultiprojectiveEquiv_apply, Sum.forall]
  exact ⟨fun ⟨⟨h1, h2⟩, hw⟩ ↦ ⟨⟨h2, h1⟩, hw⟩, fun ⟨⟨h2, h1⟩, hw⟩ ↦ ⟨⟨h1, h2⟩, hw⟩⟩

/-- For finite `σ`, `ι`, and `κ i`, the diagonal of `(σ → K) × ((i : ι) → ℙ K (κ i → K))` is
affine-multiprojective semialgebraic. -/
theorem isAffineMultiprojectiveSemialgebraic_diagonal
    [Finite σ] [Finite ι] [∀ i, Finite (κ i)] :
    IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv σ σ κ κ K ⁻¹'
        diagonal ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) := by
  rw [isAffineMultiprojectiveSemialgebraic_def]
  let xInl (s : σ) : MvPolynomial ((σ ⊕ σ) ⊕ (Σ k : ι ⊕ ι, Sum.elim κ κ k)) K :=
    X (.inl (.inl s))
  let xInr (s : σ) : MvPolynomial ((σ ⊕ σ) ⊕ (Σ k : ι ⊕ ι, Sum.elim κ κ k)) K :=
    X (.inl (.inr s))
  have h : affineMultiprojectiveConePreimage
      (prodAffineMultiprojectiveEquiv σ σ κ κ K ⁻¹'
        diagonal ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) =
      (⋂ s : σ, {w | eval w (xInl s) = eval w (xInr s)}) ∩
        (fun w : (σ ⊕ σ) ⊕ (Σ k : ι ⊕ ι, Sum.elim κ κ k) → K ↦ w ∘ Sum.inr) ⁻¹'
          piConePreimage
            (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ k → K)) ⁻¹'
              diagonal ((i : ι) → ℙ K (κ i → K))) := by
    ext w
    simp only [mem_affineMultiprojectiveConePreimage_iff, mem_inter_iff, mem_iInter,
      Set.mem_ofPred_eq, xInl, xInr, eval_X, mem_preimage, mem_piConePreimage_iff]
    constructor
    · rintro ⟨hv, hdiag⟩
      have heq := mem_diagonal_iff.1 hdiag
      rw [prodAffineMultiprojectiveEquiv_apply] at heq
      exact ⟨fun s ↦ congr_fun (congrArg Prod.fst heq) s, hv,
        mem_preimage.2 (mem_diagonal_iff.2 (congrArg Prod.snd heq))⟩
    · rintro ⟨hs, hv, hp⟩
      have hp' := mem_diagonal_iff.1 (mem_preimage.1 hp)
      refine ⟨hv, ?_⟩
      rw [mem_diagonal_iff, prodAffineMultiprojectiveEquiv_apply]
      exact Prod.ext (funext hs) hp'
  rw [h]
  exact (IsSemialgebraic.iInter fun s ↦ isSemialgebraic_eval_eq (xInl s) (xInr s)).inter
    ((isMultiprojectiveSemialgebraic_def.1 isMultiprojectiveSemialgebraic_diagonal).preimage_comp
      Sum.inr)

/-- For finite `σ`, `ι`, and `κ i`, every singleton in `(σ → K) × ((i : ι) → ℙ K (κ i → K))` is
affine-multiprojective semialgebraic. -/
@[simp]
theorem isAffineMultiprojectiveSemialgebraic_singleton
    [Finite σ] [Finite ι] [∀ i, Finite (κ i)]
    (c : (σ → K) × ((i : ι) → ℙ K (κ i → K))) :
    IsAffineMultiprojectiveSemialgebraic
      ({c} : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) := by
  have h : ({c} : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) = {c.1} ×ˢ {c.2} := by
    ext ⟨x, p⟩
    simp [Prod.ext_iff]
  rw [h]
  exact (isSemialgebraic_singleton c.1).prod_multiprojective
    (isMultiprojectiveSemialgebraic_singleton c.2)

end AffineMultiprojectiveSemialgebraic

/-! ### Embedded projector and chart characterizations for mixed sets -/

section MixedProjectorAndCharts

section Projector

variable {σ ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For finite `ι`, the range of `affinePiProjectorCoords` is semialgebraic for arbitrary `σ`. -/
theorem isSemialgebraic_range_affinePiProjectorCoords [Finite ι] :
    IsSemialgebraic
      (range (affinePiProjectorCoords :
        (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ ⊕ (Σ i, κ i × κ i) → K))) := by
  rw [range_affinePiProjectorCoords]
  exact (isSemialgebraic_piProjectorLocus (κ := κ) (K := K)).preimage_comp Sum.inr

/-- **Complement transport for `affinePiProjectorCoords`.** Because `affinePiProjectorCoords` is
injective, the image of `Sᶜ` is the relative complement of `affinePiProjectorCoords '' S` inside
`range affinePiProjectorCoords`. -/
theorem image_affinePiProjectorCoords_compl
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    affinePiProjectorCoords '' Sᶜ =
      range affinePiProjectorCoords \ (affinePiProjectorCoords '' S) := by
  rw [← image_univ, ← image_sdiff affinePiProjectorCoords_injective, compl_eq_univ_sdiff]

private theorem mk_piProjectorCoords_row_eq_mixed {i : ι} (p : (i : ι) → ℙ K (κ i → K)) {r : κ i}
    (hr : projector (p i) r r ≠ 0) (hv : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) ≠ 0) :
    mk K (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) hv = p i :=
  projector_injective <| by
    have hrow : (fun j ↦ piProjectorCoords p ⟨i, r, j⟩) = projector (p i) r :=
      funext fun j ↦ piProjectorCoords_apply p ⟨i, r, j⟩
    rw [projector_mk, hrow]
    exact rankOneProjector_row_eq_self (projector_mem_projectorLocus (p i)) hr

/-- Pushing an affine-multiprojective semialgebraic set forward along `affinePiProjectorCoords`
yields a semialgebraic subset of `σ ⊕ (Σ i, κ i × κ i) → K` (over any ordered field, for
arbitrary `σ`). -/
theorem IsAffineMultiprojectiveSemialgebraic.isSemialgebraic_image_affinePiProjectorCoords
    [Finite ι] {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) :
    IsSemialgebraic (affinePiProjectorCoords '' S) := by
  let rowIdx (R : ∀ i, κ i) : σ ⊕ (Σ i, κ i) → σ ⊕ (Σ i, κ i × κ i) :=
    Sum.map id fun q ↦ ⟨q.1, R q.1, q.2⟩
  let xR (R : ∀ i, κ i) (i : ι) : MvPolynomial (σ ⊕ (Σ i, κ i × κ i)) K :=
    X (.inr ⟨i, R i, R i⟩)
  have h : affinePiProjectorCoords '' S =
      range affinePiProjectorCoords ∩
        ⋃ R : ∀ i, κ i,
          (⋂ i : ι, {z | eval z (xR R i) ≠ 0}) ∩
            (fun z ↦ z ∘ rowIdx R) ⁻¹' affineMultiprojectiveConePreimage S := by
    ext z
    constructor
    · rintro ⟨⟨x, p⟩, hxpS, rfl⟩
      obtain ⟨R, hpR⟩ := exists_mem_piAffineOpen p
      have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 :=
        (projector_apply_self_pos_iff.2 (mem_piAffineOpen_iff.1 hpR i)).ne'
      have hv (i : ι) : (fun j ↦ piProjectorCoords p ⟨i, R i, j⟩) ≠ 0 :=
        fun h0 ↦ hR i (by simpa using congr_fun h0 (R i))
      refine ⟨mem_range_self (x, p), mem_iUnion.2 ⟨R, ?_, hv, ?_⟩⟩
      · exact mem_iInter.2 fun i ↦ by simpa [xR] using hR i
      · have heq : ((affinePiProjectorCoords (x, p) ∘ rowIdx R) ∘ Sum.inl,
            fun i ↦ mk K (fun j ↦ piProjectorCoords p ⟨i, R i, j⟩) (hv i)) = (x, p) :=
          Prod.ext (funext fun _ ↦ rfl)
            (funext fun i ↦ mk_piProjectorCoords_row_eq_mixed p (hR i) (hv i))
        exact heq.symm ▸ hxpS
    · rintro ⟨⟨⟨x, p⟩, rfl⟩, hzU⟩
      obtain ⟨R, hdiag, hv, hxpS⟩ := mem_iUnion.1 hzU
      have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 := by
        simpa [xR] using mem_iInter.1 hdiag i
      refine ⟨(x, p), ?_, rfl⟩
      have heq : ((affinePiProjectorCoords (x, p) ∘ rowIdx R) ∘ Sum.inl,
          fun i ↦ mk K (fun j ↦ piProjectorCoords p ⟨i, R i, j⟩) (hv i)) = (x, p) :=
        Prod.ext (funext fun _ ↦ rfl)
          (funext fun i ↦ mk_piProjectorCoords_row_eq_mixed p (hR i) (hv i))
      exact heq ▸ hxpS
  rw [h]
  exact isSemialgebraic_range_affinePiProjectorCoords.inter <|
    IsSemialgebraic.iUnion fun R ↦
      (IsSemialgebraic.iInter fun i ↦ isSemialgebraic_eval_ne_zero (xR R i)).inter
        (hS.preimage_comp (rowIdx R))

/-- Conversely, if `affinePiProjectorCoords '' S` is semialgebraic, then `S` is
affine-multiprojective semialgebraic (over any ordered field, for arbitrary `σ`). -/
theorem isAffineMultiprojectiveSemialgebraic_of_isSemialgebraic_image_affinePiProjectorCoords
    [Finite ι] {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (himg : IsSemialgebraic (affinePiProjectorCoords '' S)) :
    IsAffineMultiprojectiveSemialgebraic S := by
  let N : σ ⊕ (Σ i, κ i × κ i) → MvPolynomial (σ ⊕ (Σ i, κ i)) K :=
    Sum.elim (fun s ↦ X (.inl s)) fun q ↦ X (.inr ⟨q.1, q.2.1⟩) * X (.inr ⟨q.1, q.2.2⟩)
  let D : σ ⊕ (Σ i, κ i × κ i) → MvPolynomial (σ ⊕ (Σ i, κ i)) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ ∑ r : κ q.1, X (.inr ⟨q.1, r⟩) * X (.inr ⟨q.1, r⟩)
  have hpos : ∀ w ∈ affineMultiprojectiveConeDomain σ κ K, ∀ u, 0 < eval w (D u) := by
    rintro w hw (s | ⟨i, _, _⟩)
    · simp [D]
    · have hwi := mem_affineMultiprojectiveConeDomain_iff.1 hw i
      simpa [D, dotProduct] using lt_of_le_of_ne (dotProduct_self_nonneg fun r ↦ w (.inr ⟨i, r⟩))
        (Ne.symm (dotProduct_self_eq_zero.not.mpr hwi))
  have heq : affineMultiprojectiveConePreimage S =
      affineMultiprojectiveConeDomain σ κ K ∩
        (fun w u ↦ eval w (N u) / eval w (D u)) ⁻¹' (affinePiProjectorCoords '' S) := by
    ext w
    constructor
    · rintro ⟨hv, hwS⟩
      refine ⟨mem_affineMultiprojectiveConeDomain_iff.2 hv,
        mem_preimage.2 ⟨(w ∘ Sum.inl, fun i ↦ mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hv i)),
          hwS, ?_⟩⟩
      ext (s | ⟨i, j, k⟩)
      · simp [N, D]
      · simp [N, D, rankOneProjector_apply, dotProduct]
    · rintro ⟨hw, hmem⟩
      have hv := mem_affineMultiprojectiveConeDomain_iff.1 hw
      obtain ⟨⟨x, q⟩, hxqS, hxq⟩ := mem_preimage.1 hmem
      have hx : x = w ∘ Sum.inl := funext fun s ↦ by simpa [N, D] using congr_fun hxq (.inl s)
      have hq : q = fun i ↦ mk K (fun j ↦ w (.inr ⟨i, j⟩)) (hv i) :=
        piProjectorCoords_injective <| funext fun ⟨i, j, k⟩ ↦ by
          simpa [N, D, rankOneProjector_apply, dotProduct] using congr_fun hxq (.inr ⟨i, j, k⟩)
      exact ⟨hv, by rwa [← hx, ← hq]⟩
  rw [isAffineMultiprojectiveSemialgebraic_def, heq]
  exact isSemialgebraic_affineMultiprojectiveConeDomain.inter_preimage_div_of_pos himg N D hpos

/-- **Embedded projector characterization of mixed semialgebraic sets.** Over any ordered field, a
subset `S` of `(σ → K) × ((i : ι) → ℙ K (κ i → K))` (with `ι` and each `κ i` finite, and `σ`
arbitrary) is affine-multiprojective semialgebraic if and only if its image
`affinePiProjectorCoords '' S` in `σ ⊕ (Σ i, κ i × κ i) → K` is semialgebraic. -/
theorem isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords
    [Finite ι] {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraic S ↔
      IsSemialgebraic (affinePiProjectorCoords '' S) :=
  ⟨IsAffineMultiprojectiveSemialgebraic.isSemialgebraic_image_affinePiProjectorCoords,
    isAffineMultiprojectiveSemialgebraic_of_isSemialgebraic_image_affinePiProjectorCoords⟩

end Projector

section Charts

variable {σ ι : Type*} {n : ι → ℕ} {K : Type*} [Field K] [LinearOrder K]

/-- Every affine-multiprojective semialgebraic set is semialgebraic in every standard product
affine chart `affinePiAffineChart σ I` (requiring neither finiteness of `σ` or `ι` nor projection
closure). -/
theorem IsAffineMultiprojectiveSemialgebraic.isSemialgebraic_image_affinePiAffineChart
    {S : Set ((σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (affinePiAffineChart σ I '' (S ∩ (univ ×ˢ piAffineOpen I))) := by
  let L : σ ⊕ (Σ i, Fin (n i + 1)) → MvPolynomial (σ ⊕ (Σ i, Fin (n i))) K :=
    Sum.elim (fun s ↦ X (.inl s)) fun ⟨i, j⟩ ↦
      Fin.insertNth (α := fun _ ↦ MvPolynomial (σ ⊕ (Σ i, Fin (n i))) K)
        (I i) 1 (fun k ↦ X (.inr ⟨i, k⟩)) j
  have hL (z : σ ⊕ (Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
      eval z (L (.inr ⟨i, j⟩)) =
        Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z (.inr ⟨i, k⟩)) j := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove (I i) j <;> simp [L]
  have hv (z : σ ⊕ (Σ i, Fin (n i)) → K) (i : ι) :
      (fun j ↦ eval z (L (.inr ⟨i, j⟩))) ≠ 0 := by
    simpa only [funext (hL z i)] using Fin.insertNth_one_ne_zero (I i) fun k ↦ z (.inr ⟨i, k⟩)
  have hmk (z : σ ⊕ (Σ i, Fin (n i)) → K)
      (hvz : ∀ i, (fun j ↦ eval z (L (.inr ⟨i, j⟩))) ≠ 0) :
      ((fun u ↦ eval z (L u)) ∘ Sum.inl,
        fun i ↦ mk K (fun j ↦ eval z (L (.inr ⟨i, j⟩))) (hvz i)) =
        (affinePiAffineChart σ I).symm z := by
    refine Prod.ext (funext fun s ↦ by simp [L]) ?_
    ext i
    simp [funext (hL z i)]
  convert IsSemialgebraic.preimage_eval hS L using 1
  ext z
  constructor
  · rintro ⟨⟨x, p⟩, ⟨hxpS, _, hpI⟩, rfl⟩
    refine ⟨hv _, ?_⟩
    rw [hmk, (affinePiAffineChart σ I).left_inv (by simpa using hpI)]
    exact hxpS
  · rintro ⟨hvz, hxpS⟩
    rw [hmk] at hxpS
    exact ⟨(affinePiAffineChart σ I).symm z, ⟨hxpS, by simp⟩,
      (affinePiAffineChart σ I).right_inv (by simp)⟩

private theorem isSemialgebraic_image_affinePiProjectorCoords_of_affinePiAffineChart
    [IsStrictOrderedRing K] [Finite ι]
    {S : Set ((σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K)))}
    {I : ∀ i, Fin (n i + 1)}
    (hSI : IsSemialgebraic (affinePiAffineChart σ I '' (S ∩ (univ ×ˢ piAffineOpen I)))) :
    IsSemialgebraic (affinePiProjectorCoords '' (S ∩ (univ ×ˢ piAffineOpen I))) := by
  let xI (i : ι) : MvPolynomial (σ ⊕ (Σ i, Fin (n i + 1) × Fin (n i + 1))) K :=
    X (.inr ⟨i, I i, I i⟩)
  let U : Set (σ ⊕ (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K) :=
    range affinePiProjectorCoords ∩ ⋂ i : ι, {z | 0 < eval z (xI i)}
  have hU : IsSemialgebraic U :=
    isSemialgebraic_range_affinePiProjectorCoords.inter <|
      IsSemialgebraic.iInter fun i ↦ isSemialgebraic_eval_pos (xI i)
  let N : σ ⊕ (Σ i, Fin (n i)) →
      MvPolynomial (σ ⊕ (Σ i, Fin (n i + 1) × Fin (n i + 1))) K :=
    Sum.elim (fun s ↦ X (.inl s)) fun q ↦ X (.inr ⟨q.1, (I q.1).succAbove q.2, I q.1⟩)
  let D : σ ⊕ (Σ i, Fin (n i)) →
      MvPolynomial (σ ⊕ (Σ i, Fin (n i + 1) × Fin (n i + 1))) K :=
    Sum.elim (fun _ ↦ 1) fun q ↦ X (.inr ⟨q.1, I q.1, I q.1⟩)
  have hpos : ∀ z ∈ U, ∀ u, 0 < eval z (D u) := by
    rintro z ⟨_, hz⟩ (s | ⟨i, _⟩)
    · simp [D]
    · simpa [D, xI] using mem_iInter.1 hz i
  have hdiv (x : σ → K) (p : (i : ι) → ℙ K (Fin (n i + 1) → K)) :
      (fun u ↦ eval (affinePiProjectorCoords (x, p)) (N u) /
          eval (affinePiProjectorCoords (x, p)) (D u)) =
        affinePiAffineChart σ I (x, p) := by
    ext (s | q)
    · simp [N, D]
    · simpa [N, D] using (congr_fun (piAffineChart_eq_piProjectorCoords_div I p) q).symm
  convert hU.inter_preimage_div_of_pos hSI N D hpos using 1
  ext z
  constructor
  · rintro ⟨⟨x, p⟩, ⟨hxpS, _, hpI⟩, rfl⟩
    refine ⟨⟨mem_range_self (x, p), mem_iInter.2 fun i ↦ ?_⟩, ?_⟩
    · simpa [xI] using projector_apply_self_pos_iff.2 (mem_piAffineOpen_iff.1 hpI i)
    · exact mem_preimage.2 (hdiv x p ▸ ⟨(x, p), ⟨hxpS, mem_univ x, hpI⟩, rfl⟩)
  · rintro ⟨⟨⟨⟨x, p⟩, rfl⟩, hz⟩, hmem⟩
    have hpI : p ∈ piAffineOpen I := mem_piAffineOpen_iff.2 fun i ↦
      projector_apply_self_pos_iff.1 (by simpa [xI] using mem_iInter.1 hz i)
    obtain ⟨⟨x', p'⟩, ⟨hx'p'S, hsrc'⟩, heq⟩ := hdiv x p ▸ mem_preimage.1 hmem
    have hxp : (x', p') = (x, p) := (affinePiAffineChart σ I).injOn
      (by simpa using hsrc') (by simpa using hpI) heq
    exact ⟨(x, p), ⟨(hxp ▸ hx'p'S), mem_univ x, hpI⟩, rfl⟩

/-- **Chart characterization of mixed semialgebraic sets.** Over any ordered field, a subset `S` of
`(σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K))` (with finite `ι` and arbitrary `σ`) is
affine-multiprojective semialgebraic if and only if its image in every standard product affine chart
`affinePiAffineChart σ I` is semialgebraic. -/
theorem isAffineMultiprojectiveSemialgebraic_iff_forall_affinePiAffineChart
    [IsStrictOrderedRing K] [Finite ι]
    {S : Set ((σ → K) × ((i : ι) → ℙ K (Fin (n i + 1) → K)))} :
    IsAffineMultiprojectiveSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1),
        IsSemialgebraic (affinePiAffineChart σ I '' (S ∩ (univ ×ˢ piAffineOpen I))) := by
  refine ⟨fun hS I ↦ hS.isSemialgebraic_image_affinePiAffineChart I, fun hS ↦ ?_⟩
  rw [isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords]
  convert IsSemialgebraic.iUnion
    (fun I ↦ isSemialgebraic_image_affinePiProjectorCoords_of_affinePiAffineChart (hS I)) using 1
  ext z
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨⟨x, p⟩, hxpS, rfl⟩
    obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
    exact ⟨I, (x, p), ⟨hxpS, mem_univ x, hpI⟩, rfl⟩
  · rintro ⟨I, ⟨x, p⟩, ⟨hxpS, _⟩, rfl⟩
    exact ⟨(x, p), hxpS, rfl⟩

end Charts

end MixedProjectorAndCharts

end TauCeti
