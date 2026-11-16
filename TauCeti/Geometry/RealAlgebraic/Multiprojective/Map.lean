/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Semialgebraic maps between multiprojective and mixed spaces

For mixed affine–multiprojective spaces `X₁ = (σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)` and
`X₂ = (σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)`, the product `X₁ × X₂` is canonically
identified with `((σ₁ ⊕ σ₂) → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)` via
`TauCeti.mixedProdEquiv`. Under this identification, a map `f : X₁ → X₂` is *mixed semialgebraic*
on `s ⊆ X₁` (`TauCeti.IsMixedSemialgebraicOn f s`) if `s` and the graph `s.graphOn f` are mixed
semialgebraic. Specializing `σ₁, σ₂` to empty index types yields semialgebraic maps between pure
multiprojective spaces (`TauCeti.IsMultiprojectiveSemialgebraicOn`, using Mathlib's
`Equiv.sumPiEquivProdPi` on the product of multiprojective spaces), and specializing `X₁` to an
affine space `σ → K` and `X₂` to a multiprojective space `M` recovers graphs `s.graphOn τ ⊆
(σ → K) × M` of maps from an affine subset (such as the carrier of a simplicial complex) into `M`.

Graph semialgebraicity alone does not assert continuity; real Nash maps combining mixed graph
semialgebraicity, continuity, and chartwise real analyticity are developed in
`TauCeti.Geometry.RealAlgebraic.Multiprojective.Nash`.

## Main declarations

* `TauCeti.mixedProdEquiv`, `TauCeti.mixedProdHomeomorph`, `TauCeti.mixedProdChartIndexEquiv`:
  canonical identifications of products of mixed spaces and their chart coordinate index types
  with a single mixed space over sum index types.
* `TauCeti.IsMixedSemialgebraic.prod`, `TauCeti.IsMixedSemialgebraic.preimage_swap`,
  `TauCeti.IsMixedSemialgebraic.image_fst`, `TauCeti.IsMixedSemialgebraic.image_snd`: products,
  factor swaps, and coordinate projections of mixed semialgebraic sets.
* `TauCeti.IsMixedSemialgebraicOn`, `TauCeti.IsMixedSemialgebraicMap`,
  `TauCeti.IsMultiprojectiveSemialgebraicOn`, `TauCeti.IsMultiprojectiveSemialgebraicMap`:
  semialgebraic maps via graphs.
* `TauCeti.isMixedSemialgebraic_graphOn_iff_forall_chart`,
  `TauCeti.isMixedSemialgebraicOn_iff_forall_isSemialgebraicOn`,
  `TauCeti.isMixedSemialgebraic_affine_graphOn_iff_forall_chart`,
  `TauCeti.isMixedSemialgebraic_affine_graphOn_iff_forall_isSemialgebraicOn`: chartwise
  characterizations of mixed semialgebraic graphs and maps.
* `TauCeti.isMixedSemialgebraicOn_id`, `TauCeti.isMixedSemialgebraicOn_diag`,
  `TauCeti.IsMixedSemialgebraicOn.prodMk`, `TauCeti.IsMixedSemialgebraicOn.comp`,
  `TauCeti.IsMixedSemialgebraicOn.isMixedSemialgebraic_image_inter`,
  `TauCeti.IsMixedSemialgebraicOn.isMixedSemialgebraic_inter_preimage`: basic calculus of mixed
  semialgebraic maps.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Chapter 2.
-/

public section

open MvPolynomial Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Canonical product equivalences -/

section IndexEquiv

variable {ι₁ ι₂ : Type*} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}

/-- Combine chart index choices on `ι₁` and `ι₂` into a chart index choice on `ι₁ ⊕ ι₂`. -/
def sumPiFinIndex (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)) :
    ∀ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)
  | .inl i => I₁ i
  | .inr j => I₂ j

@[simp]
theorem sumPiFinIndex_inl (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (i : ι₁) : sumPiFinIndex I₁ I₂ (.inl i) = I₁ i :=
  (rfl)

@[simp]
theorem sumPiFinIndex_inr (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (j : ι₂) : sumPiFinIndex I₁ I₂ (.inr j) = I₂ j :=
  (rfl)

@[simp]
theorem sumPiFinIndex_eta (I : ∀ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) :
    sumPiFinIndex (fun i ↦ I (.inl i)) (fun j ↦ I (.inr j)) = I :=
  funext fun k ↦ by cases k <;> rfl

/-- Shared index combinator identifying `(σ₁ ⊕ Σ i, t (.inl i)) ⊕ (σ₂ ⊕ Σ j, t (.inr j))` with
`(σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, t k`. -/
private def mixedProdIndexEquiv (σ₁ σ₂ : Type*) {ι₁ ι₂ : Type*} (t : ι₁ ⊕ ι₂ → Type*) :
    ((σ₁ ⊕ Σ i, t (.inl i)) ⊕ (σ₂ ⊕ Σ j, t (.inr j))) ≃
      ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, t k) :=
  (Equiv.sumSumSumComm σ₁ (Σ i, t (.inl i)) σ₂ (Σ j, t (.inr j))).trans
    (Equiv.sumCongr (.refl (σ₁ ⊕ σ₂)) (Equiv.sumSigmaDistrib t).symm)

/-- Private cone-index specialization of `mixedProdIndexEquiv` with syntactic `Fin (n i + 1)`
factors. -/
private def mixedProdConeIndexEquiv (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    ((σ₁ ⊕ Σ i, Fin (n₁ i + 1)) ⊕ (σ₂ ⊕ Σ j, Fin (n₂ j + 1))) ≃
      ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) :=
  mixedProdIndexEquiv σ₁ σ₂ fun k ↦ Fin (Sum.elim n₁ n₂ k + 1)

@[simp]
private theorem mixedProdConeIndexEquiv_inl_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₁ : σ₁) :
    mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂ (.inl (.inl a₁)) = .inl (.inl a₁) :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_inl_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (p : Σ i, Fin (n₁ i + 1)) :
    mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂ (.inl (.inr p)) = .inr ⟨.inl p.1, p.2⟩ :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_inr_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₂ : σ₂) :
    mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂ (.inr (.inl a₂)) = .inl (.inr a₂) :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_inr_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (q : Σ j, Fin (n₂ j + 1)) :
    mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂ (.inr (.inr q)) = .inr ⟨.inr q.1, q.2⟩ :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_symm_inl_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₁ : σ₁) :
    (mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inl (.inl a₁)) = .inl (.inl a₁) :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_symm_inl_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₂ : σ₂) :
    (mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inl (.inr a₂)) = .inr (.inl a₂) :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_symm_inr_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (i : ι₁) (j : Fin (n₁ i + 1)) :
    (mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inr ⟨.inl i, j⟩) = .inl (.inr ⟨i, j⟩) :=
  (rfl)

@[simp]
private theorem mixedProdConeIndexEquiv_symm_inr_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (j : ι₂) (l : Fin (n₂ j + 1)) :
    (mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inr ⟨.inr j, l⟩) = .inr (.inr ⟨j, l⟩) :=
  (rfl)

/-- Chart coordinate index equivalence between
`(σ₁ ⊕ Σ i, Fin (n₁ i)) ⊕ (σ₂ ⊕ Σ j, Fin (n₂ j))` and
`(σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k)`. -/
def mixedProdChartIndexEquiv (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    ((σ₁ ⊕ Σ i, Fin (n₁ i)) ⊕ (σ₂ ⊕ Σ j, Fin (n₂ j))) ≃
      ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k)) :=
  mixedProdIndexEquiv σ₁ σ₂ fun k ↦ Fin (Sum.elim n₁ n₂ k)

@[simp]
theorem mixedProdChartIndexEquiv_inl_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) (a₁ : σ₁) :
    mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inl (.inl a₁)) = .inl (.inl a₁) :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_inl_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (p : Σ i, Fin (n₁ i)) :
    mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inl (.inr p)) = .inr ⟨.inl p.1, p.2⟩ :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_inr_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) (a₂ : σ₂) :
    mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inr (.inl a₂)) = .inl (.inr a₂) :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_inr_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (q : Σ j, Fin (n₂ j)) :
    mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inr (.inr q)) = .inr ⟨.inr q.1, q.2⟩ :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_symm_inl_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₁ : σ₁) :
    (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inl (.inl a₁)) = .inl (.inl a₁) :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_symm_inl_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (a₂ : σ₂) :
    (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inl (.inr a₂)) = .inr (.inl a₂) :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_symm_inr_inl (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (i : ι₁) (k : Fin (n₁ i)) :
    (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inr ⟨.inl i, k⟩) = .inl (.inr ⟨i, k⟩) :=
  (rfl)

@[simp]
theorem mixedProdChartIndexEquiv_symm_inr_inr (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ)
    (j : ι₂) (l : Fin (n₂ j)) :
    (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm (.inr ⟨.inr j, l⟩) = .inr (.inr ⟨j, l⟩) :=
  (rfl)

end IndexEquiv

section ProductEquiv

variable {K σ₁ σ₂ ι₁ ι₂ : Type*} [DivisionRing K] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}

/-- Canonical equivalence identifying a binary product of mixed affine–multiprojective spaces with
a single mixed space over `σ₁ ⊕ σ₂` and `ι₁ ⊕ ι₂`. -/
def mixedProdEquiv (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))) ≃
      ((σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow σ₁ σ₂ K).symm
      (Equiv.sumPiEquivProdPi fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)).symm)

@[simp]
theorem mixedProdEquiv_apply
    (xy : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))) :
    mixedProdEquiv σ₁ σ₂ n₁ n₂ xy =
      (Sum.elim xy.1.1 xy.2.1,
        (Equiv.sumPiEquivProdPi fun k : ι₁ ⊕ ι₂ ↦
          ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)).symm (xy.1.2, xy.2.2)) := by
  rcases xy with ⟨⟨_, _⟩, _, _⟩
  rfl

@[simp]
theorem mixedProdEquiv_symm_apply
    (z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) :
    (mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z =
      ((z.1 ∘ Sum.inl, fun i ↦ z.2 (.inl i)), (z.1 ∘ Sum.inr, fun j ↦ z.2 (.inr j))) := by
  rcases z with ⟨_, _⟩
  rfl

/-- Topological refinement of `TauCeti.mixedProdEquiv`. -/
def mixedProdHomeomorph [TopologicalSpace K] (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))) ≃ₜ
      ((σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) :=
  (Homeomorph.prodProdProdComm _ _ _ _).trans
    (Homeomorph.prodCongr Homeomorph.sumArrowHomeomorphProdArrow.symm
      (Homeomorph.sumPiEquivProdPi ι₁ ι₂ fun k ↦
        ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)).symm)

@[simp]
theorem mixedProdHomeomorph_toEquiv [TopologicalSpace K]
    (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    (mixedProdHomeomorph (K := K) σ₁ σ₂ n₁ n₂).toEquiv = mixedProdEquiv σ₁ σ₂ n₁ n₂ :=
  Equiv.ext fun ⟨⟨_, _⟩, _, _⟩ ↦
    Prod.ext (funext fun k ↦ by cases k <;> rfl) (funext fun k ↦ by cases k <;> rfl)

@[simp]
theorem coe_mixedProdHomeomorph [TopologicalSpace K]
    (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    ⇑(mixedProdHomeomorph (K := K) σ₁ σ₂ n₁ n₂) = mixedProdEquiv σ₁ σ₂ n₁ n₂ :=
  congrArg DFunLike.coe (mixedProdHomeomorph_toEquiv σ₁ σ₂ n₁ n₂)

@[simp]
theorem coe_mixedProdHomeomorph_symm [TopologicalSpace K]
    (σ₁ σ₂ : Type*) (n₁ : ι₁ → ℕ) (n₂ : ι₂ → ℕ) :
    ⇑(mixedProdHomeomorph (K := K) σ₁ σ₂ n₁ n₂).symm = (mixedProdEquiv σ₁ σ₂ n₁ n₂).symm :=
  congrArg (fun e : _ ≃ _ ↦ ⇑e.symm) (mixedProdHomeomorph_toEquiv σ₁ σ₂ n₁ n₂)

end ProductEquiv

/-! ### Products and coordinate projections of mixed semialgebraic sets -/

section ProdAndProj

variable {K σ₁ σ₂ ι₁ ι₂ : Type*} [Field K] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}

/-- Membership in `multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂)` splits into the two factor
standard product affine opens. -/
theorem mem_multiprojectiveAffineOpen_sumPiFinIndex
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    {r : ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)} :
    r ∈ multiprojectiveAffineOpen (sumPiFinIndex I₁ I₂) ↔
      (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) r).1 ∈
        multiprojectiveAffineOpen I₁ ∧
      (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) r).2 ∈
        multiprojectiveAffineOpen I₂ :=
  mem_multiprojectiveAffineOpen.trans <|
    (⟨fun h ↦ ⟨fun i ↦ h (.inl i), fun j ↦ h (.inr j)⟩,
      fun ⟨h₁, h₂⟩ ↦ fun | .inl i => h₁ i | .inr j => h₂ j⟩ :
      (∀ k, r k ∈ Projectivization.affineOpen (sumPiFinIndex I₁ I₂ k)) ↔
        (∀ i, r (.inl i) ∈ Projectivization.affineOpen (I₁ i)) ∧
          (∀ j, r (.inr j) ∈ Projectivization.affineOpen (I₂ j))).trans
      (and_congr mem_multiprojectiveAffineOpen.symm mem_multiprojectiveAffineOpen.symm)

/-- Left-factor coordinates of `multiprojectiveAffineChart (sumPiFinIndex I₁ I₂)`. -/
theorem multiprojectiveAffineChart_sumPiFinIndex_inl
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K))
    (i : ι₁) (k : Fin (n₁ i)) :
    multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ⟨.inl i, k⟩ =
      multiprojectiveAffineChart I₁
        (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) r).1
        ⟨i, k⟩ :=
  (multiprojectiveAffineChart_apply (sumPiFinIndex I₁ I₂) r ⟨.inl i, k⟩).trans
    (multiprojectiveAffineChart_apply I₁ (fun i' ↦ r (.inl i')) ⟨i, k⟩).symm

/-- Right-factor coordinates of `multiprojectiveAffineChart (sumPiFinIndex I₁ I₂)`. -/
theorem multiprojectiveAffineChart_sumPiFinIndex_inr
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (r : ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K))
    (j : ι₂) (l : Fin (n₂ j)) :
    multiprojectiveAffineChart (sumPiFinIndex I₁ I₂) r ⟨.inr j, l⟩ =
      multiprojectiveAffineChart I₂
        (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) r).2
        ⟨j, l⟩ :=
  (multiprojectiveAffineChart_apply (sumPiFinIndex I₁ I₂) r ⟨.inr j, l⟩).trans
    (multiprojectiveAffineChart_apply I₂ (fun j' ↦ r (.inr j')) ⟨j, l⟩).symm

/-- Membership in `mixedCone ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' W)` unpacked into the left and
right cone representatives. -/
theorem mem_mixedCone_preimage_mixedProdEquiv_symm
    {W : Set (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))}
    {w : ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) → K} :
    w ∈ mixedCone ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' W) ↔
      ∃ (hw₁ : ∀ i : ι₁, (fun j : Fin (n₁ i + 1) ↦ w (.inr ⟨.inl i, j⟩)) ≠ 0)
        (hw₂ : ∀ j : ι₂, (fun l : Fin (n₂ j + 1) ↦ w (.inr ⟨.inr j, l⟩)) ≠ 0),
        (((fun a₁ ↦ w (.inl (.inl a₁)),
            fun i ↦ Projectivization.mk K
              (fun j : Fin (n₁ i + 1) ↦ w (.inr ⟨.inl i, j⟩)) (hw₁ i)),
          (fun a₂ ↦ w (.inl (.inr a₂)),
            fun j ↦ Projectivization.mk K
              (fun l : Fin (n₂ j + 1) ↦ w (.inr ⟨.inr j, l⟩)) (hw₂ j))) ∈ W) := by
  simp only [mem_mixedCone, mem_preimage, mixedProdEquiv_symm_apply]
  constructor
  · rintro ⟨hw, hwW⟩
    exact ⟨fun i ↦ hw (.inl i), fun j ↦ hw (.inr j), hwW⟩
  · rintro ⟨hw₁, hw₂, hwW⟩
    exact ⟨fun | .inl i => hw₁ i | .inr j => hw₂ j, hwW⟩

variable [LinearOrder K]

/-- The product of two mixed semialgebraic sets is mixed semialgebraic. -/
theorem IsMixedSemialgebraic.prod
    {S₁ : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {S₂ : Set ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hS₁ : IsMixedSemialgebraic S₁) (hS₂ : IsMixedSemialgebraic S₂) :
    IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' (S₁ ×ˢ S₂)) := by
  rw [isMixedSemialgebraic_def]
  let e := mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂
  convert ((isMixedSemialgebraic_def.1 hS₁).preimage_comp (fun c ↦ e (.inl c))).inter
    ((isMixedSemialgebraic_def.1 hS₂).preimage_comp (fun c ↦ e (.inr c))) using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff]
  simp only [mem_preimage, mem_mixedCone, Function.comp_def, e,
    mixedProdConeIndexEquiv_inl_inl, mixedProdConeIndexEquiv_inl_inr,
    mixedProdConeIndexEquiv_inr_inl, mixedProdConeIndexEquiv_inr_inr]
  exact ⟨fun ⟨hw₁, hw₂, h₁, h₂⟩ ↦ ⟨⟨hw₁, h₁⟩, ⟨hw₂, h₂⟩⟩,
    fun ⟨⟨hw₁, h₁⟩, ⟨hw₂, h₂⟩⟩ ↦ ⟨hw₁, hw₂, h₁, h₂⟩⟩

/-- Swapping the two factors of a product mixed space preserves mixed semialgebraicity. -/
theorem IsMixedSemialgebraic.preimage_swap
    {W : Set (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))}
    (hW : IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' W)) :
    IsMixedSemialgebraic ((mixedProdEquiv σ₂ σ₁ n₂ n₁).symm ⁻¹' (Prod.swap ⁻¹' W)) := by
  rw [isMixedSemialgebraic_def]
  let sw : ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) →
      ((σ₂ ⊕ σ₁) ⊕ Σ k : ι₂ ⊕ ι₁, Fin (Sum.elim n₂ n₁ k + 1))
    | .inl (.inl a₁) => .inl (.inr a₁)
    | .inl (.inr a₂) => .inl (.inl a₂)
    | .inr ⟨.inl i, j⟩ => .inr ⟨.inr i, j⟩
    | .inr ⟨.inr j, l⟩ => .inr ⟨.inl j, l⟩
  convert (isMixedSemialgebraic_def.1 hW).preimage_comp sw using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_preimage,
    mem_mixedCone_preimage_mixedProdEquiv_symm]
  simp only [Function.comp_def, mem_preimage, Prod.swap_prod_mk, sw]
  exact ⟨fun ⟨hw₂, hw₁, h⟩ ↦ ⟨hw₁, hw₂, h⟩, fun ⟨hw₁, hw₂, h⟩ ↦ ⟨hw₂, hw₁, h⟩⟩

/-- The product of two multiprojective semialgebraic sets is multiprojective semialgebraic. -/
theorem IsMultiprojectiveSemialgebraic.prod
    {S₁ : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {S₂ : Set (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hS₁ : IsMultiprojectiveSemialgebraic S₁) (hS₂ : IsMultiprojectiveSemialgebraic S₂) :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) ⁻¹'
        (S₁ ×ˢ S₂)) := by
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty ⊕ Empty)]
  have h₁ : IsMixedSemialgebraic ((univ : Set (Empty → K)) ×ˢ S₁) :=
    (isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 hS₁
  have h₂ : IsMixedSemialgebraic ((univ : Set (Empty → K)) ×ˢ S₂) :=
    (isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 hS₂
  convert h₁.prod h₂ using 1
  ext ⟨_, p⟩
  exact ⟨fun ⟨_, hp⟩ ↦ ⟨⟨trivial, hp.1⟩, ⟨trivial, hp.2⟩⟩,
    fun ⟨⟨_, hp₁⟩, ⟨_, hp₂⟩⟩ ↦ ⟨trivial, hp₁, hp₂⟩⟩

section Projections

variable [HasSemialgebraicProjections K]

/-- Given projection closure, projecting a mixed semialgebraic subset of `X₁ × X₂` onto `X₁`
preserves mixed semialgebraicity when `X₂` has finitely many affine and projective coordinates. -/
theorem IsMixedSemialgebraic.image_fst [Finite σ₂] [Finite ι₂]
    {W : Set (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))}
    (hW : IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' W)) :
    IsMixedSemialgebraic (Prod.fst '' W) := by
  rw [isMixedSemialgebraic_def]
  let e := mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂
  convert ((isMixedSemialgebraic_def.1 hW).preimage_comp e.symm).image_comp_inl using 1
  ext w₁
  simp only [mem_image, mem_preimage]
  constructor
  · rw [mem_mixedCone]
    rintro ⟨hw₁, ⟨y₁, x₂, p₂⟩, hmem, hy₁⟩
    let w₂ : (σ₂ ⊕ Σ j, Fin (n₂ j + 1)) → K := Sum.elim x₂ fun q ↦ (p₂ q.1).rep q.2
    refine ⟨Sum.elim w₁ w₂, ?_, Sum.elim_comp_inl w₁ w₂⟩
    rw [mem_mixedCone_preimage_mixedProdEquiv_symm]
    have hw₁' : ∀ i : ι₁,
        (fun j : Fin (n₁ i + 1) ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inr ⟨.inl i, j⟩)) ≠ 0 := by
      simpa [e] using hw₁
    have hw₂ : ∀ j : ι₂,
        (fun l : Fin (n₂ j + 1) ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inr ⟨.inr j, l⟩)) ≠ 0 := by
      intro j
      simpa [e, w₂] using (p₂ j).rep_ne_zero
    refine ⟨hw₁', hw₂, ?_⟩
    have h₁ : (fun a₁ ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inl (.inl a₁)),
        fun i ↦ Projectivization.mk K
          (fun j : Fin (n₁ i + 1) ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inr ⟨.inl i, j⟩)) (hw₁' i)) =
        y₁ := by
      simp only [Function.comp_def] at hy₁
      simp only [Function.comp_apply, e, mixedProdConeIndexEquiv_symm_inl_inl,
        mixedProdConeIndexEquiv_symm_inr_inl, Sum.elim_inl]
      exact hy₁.symm
    have h₂ : (fun a₂ ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inl (.inr a₂)),
        fun j ↦ Projectivization.mk K
          (fun l : Fin (n₂ j + 1) ↦ (Sum.elim w₁ w₂ ∘ e.symm) (.inr ⟨.inr j, l⟩)) (hw₂ j)) =
        (x₂, p₂) := by
      refine Prod.ext (funext fun a₂ ↦ by simp [e, w₂]) (funext fun j ↦ ?_)
      simp only [Function.comp_apply, e, mixedProdConeIndexEquiv_symm_inr_inr, w₂, Sum.elim_inr]
      exact (p₂ j).mk_rep
    rwa [h₁, h₂]
  · rintro ⟨u, hu, rfl⟩
    rw [mem_mixedCone_preimage_mixedProdEquiv_symm] at hu
    obtain ⟨hw₁, _, hmem⟩ := hu
    rw [mem_mixedCone]
    have hw₁' : ∀ i : ι₁,
        (fun j : Fin (n₁ i + 1) ↦ (u ∘ Sum.inl) (.inr ⟨i, j⟩)) ≠ 0 := by
      simpa [e] using hw₁
    refine ⟨hw₁', _, hmem, ?_⟩
    simp [e, Function.comp_def]

/-- Given projection closure, projecting a mixed semialgebraic subset of `X₁ × X₂` onto `X₂`
preserves mixed semialgebraicity when `X₁` has finitely many affine and projective coordinates. -/
theorem IsMixedSemialgebraic.image_snd [Finite σ₁] [Finite ι₁]
    {W : Set (((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) ×
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))}
    (hW : IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' W)) :
    IsMixedSemialgebraic (Prod.snd '' W) := by
  have hswap : Prod.snd '' W = Prod.fst '' (Prod.swap ⁻¹' W) := by
    ext y
    simp [Prod.exists, and_comm]
  rw [hswap]
  exact hW.preimage_swap.image_fst

end Projections

end ProdAndProj

/-! ### Semialgebraic maps via graphs -/

section Maps

variable {K σ σ₁ σ₂ σ₃ ι ι₁ ι₂ ι₃ : Type*} [Field K] [LinearOrder K]
  {n : ι → ℕ} {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ} {n₃ : ι₃ → ℕ}

/-- A map `f` between mixed affine–multiprojective spaces is *mixed semialgebraic on* `s` if both
`s` and the graph `s.graphOn f` (viewed in the combined mixed space via `TauCeti.mixedProdEquiv`)
are mixed semialgebraic. -/
def IsMixedSemialgebraicOn
    (f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))
    (s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))) : Prop :=
  IsMixedSemialgebraic s ∧
    IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f)

/-- A map between mixed affine–multiprojective spaces is *mixed semialgebraic* if its graph over
the whole domain is mixed semialgebraic. -/
def IsMixedSemialgebraicMap
    (f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))) : Prop :=
  IsMixedSemialgebraicOn f univ

/-- A map `f` between multiprojective spaces is *multiprojective semialgebraic on* `s` if both `s`
and its graph `s.graphOn f` (viewed via `Equiv.sumPiEquivProdPi`) are multiprojective
semialgebraic. -/
def IsMultiprojectiveSemialgebraicOn
    (f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))
    (s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))) : Prop :=
  IsMultiprojectiveSemialgebraic s ∧
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) ⁻¹'
        s.graphOn f)

/-- A map between multiprojective spaces is *multiprojective semialgebraic* if its graph over the
whole domain is multiprojective semialgebraic. -/
def IsMultiprojectiveSemialgebraicMap
    (f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) : Prop :=
  IsMultiprojectiveSemialgebraicOn f univ

@[simp]
theorem isMixedSemialgebraicOn_univ
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))} :
    IsMixedSemialgebraicOn f univ ↔ IsMixedSemialgebraicMap f :=
  Iff.rfl

@[simp]
theorem isMultiprojectiveSemialgebraicOn_univ
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)} :
    IsMultiprojectiveSemialgebraicOn f univ ↔ IsMultiprojectiveSemialgebraicMap f :=
  Iff.rfl

theorem isMixedSemialgebraicOn_def
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMixedSemialgebraicOn f s ↔
      IsMixedSemialgebraic s ∧
        IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f) :=
  Iff.rfl

theorem isMultiprojectiveSemialgebraicOn_def
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMultiprojectiveSemialgebraicOn f s ↔
      IsMultiprojectiveSemialgebraic s ∧
        IsMultiprojectiveSemialgebraic
          (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) ⁻¹'
            s.graphOn f) :=
  Iff.rfl

theorem IsMixedSemialgebraicOn.isMixedSemialgebraic
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) : IsMixedSemialgebraic s :=
  hf.1

theorem IsMixedSemialgebraicOn.graph
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) :
    IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f) :=
  hf.2

theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) : IsMultiprojectiveSemialgebraic s :=
  hf.1

theorem IsMultiprojectiveSemialgebraicOn.graph
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦ ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) ⁻¹'
        s.graphOn f) :=
  hf.2

/-- Pure multiprojective semialgebraicity on `s` coincides with mixed semialgebraicity on
`univ ×ˢ s` after adjoining an arbitrary domain affine factor `σ₁` and an empty target affine
factor `σ₂`. -/
theorem isMixedSemialgebraicOn_univ_prod_iff [IsEmpty σ₂]
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMixedSemialgebraicOn
        (fun xp : (σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K) ↦
          ((isEmptyElim : σ₂ → K), f xp.2))
        ((univ : Set (σ₁ → K)) ×ˢ s) ↔
      IsMultiprojectiveSemialgebraicOn f s := by
  refine and_congr (isMixedSemialgebraic_univ_prod_iff (σ := σ₁)) ?_
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := σ₁ ⊕ σ₂)]
  suffices h : (mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹'
      ((univ : Set (σ₁ → K)) ×ˢ s).graphOn
        (fun xp ↦ ((isEmptyElim : σ₂ → K), f xp.2)) =
      (univ : Set (σ₁ ⊕ σ₂ → K)) ×ˢ
        (Equiv.sumPiEquivProdPi (fun k : ι₁ ⊕ ι₂ ↦
          ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)) ⁻¹' s.graphOn f) by rw [h]
  ext ⟨x, p⟩
  refine ⟨fun h ↦ ⟨trivial, ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · obtain ⟨⟨_, hps⟩, heq⟩ := mem_graphOn.1 h
    exact mem_graphOn.2 ⟨hps, (Prod.mk.inj heq).2⟩
  · obtain ⟨hps, heq⟩ := mem_graphOn.1 h
    exact mem_graphOn.2 ⟨⟨trivial, hps⟩, Prod.ext (Subsingleton.elim _ _) heq⟩

/-- Restricting a mixed semialgebraic map to a mixed semialgebraic subset preserves mixed
semialgebraicity. -/
theorem IsMixedSemialgebraicOn.mono
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s t : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) (ht : IsMixedSemialgebraic t) (hts : t ⊆ s) :
    IsMixedSemialgebraicOn f t := by
  refine ⟨ht, isMixedSemialgebraic_def.2 ?_⟩
  let e := mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂
  convert (isMixedSemialgebraic_def.1 hf.2).inter
    ((isMixedSemialgebraic_def.1 ht).preimage_comp (fun c ↦ e (.inl c))) using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff,
    mem_mixedCone_preimage_mixedProdEquiv_symm, mem_preimage, mem_mixedCone]
  simp only [Function.comp_def, e,
    mixedProdConeIndexEquiv_inl_inl, mixedProdConeIndexEquiv_inl_inr]
  constructor
  · rintro ⟨hw₁, hw₂, hmem⟩
    obtain ⟨ht_mem, hfx⟩ := mem_graphOn.1 hmem
    exact ⟨⟨hw₁, hw₂, mem_graphOn.2 ⟨hts ht_mem, hfx⟩⟩, hw₁, ht_mem⟩
  · rintro ⟨⟨hw₁, hw₂, hmem⟩, _, ht_mem⟩
    obtain ⟨_, hfx⟩ := mem_graphOn.1 hmem
    exact ⟨hw₁, hw₂, mem_graphOn.2 ⟨ht_mem, hfx⟩⟩

/-- Restricting a multiprojective semialgebraic map to a multiprojective semialgebraic subset
preserves multiprojective semialgebraicity. -/
theorem IsMultiprojectiveSemialgebraicOn.mono
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s t : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) (ht : IsMultiprojectiveSemialgebraic t)
    (hts : t ⊆ s) : IsMultiprojectiveSemialgebraicOn f t :=
  (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 <|
    ((isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf).mono
      ((isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 ht) (prod_mono_right hts)

theorem IsMixedSemialgebraicMap.isMixedSemialgebraicOn
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hf : IsMixedSemialgebraicMap f)
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} (hs : IsMixedSemialgebraic s) :
    IsMixedSemialgebraicOn f s :=
  hf.mono hs (subset_univ _)

theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraicOn
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} (hs : IsMultiprojectiveSemialgebraic s) :
    IsMultiprojectiveSemialgebraicOn f s :=
  hf.mono hs (subset_univ _)

/-- Mixed semialgebraicity on `s` depends only on the values of `f` on `s`. -/
theorem IsMixedSemialgebraicOn.congr
    {f g : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) (hfg : EqOn f g s) :
    IsMixedSemialgebraicOn g s :=
  ⟨hf.1, graphOn_inj.2 hfg ▸ hf.2⟩

/-- Multiprojective semialgebraicity on `s` depends only on the values of `f` on `s`. -/
theorem IsMultiprojectiveSemialgebraicOn.congr
    {f g : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) (hfg : EqOn f g s) :
    IsMultiprojectiveSemialgebraicOn g s :=
  ⟨hf.1, graphOn_inj.2 hfg ▸ hf.2⟩

@[simp]
theorem isMixedSemialgebraicOn_empty
    (f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))) :
    IsMixedSemialgebraicOn f ∅ :=
  ⟨isMixedSemialgebraic_empty, by simp⟩

@[simp]
theorem isMultiprojectiveSemialgebraicOn_empty
    (f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) :
    IsMultiprojectiveSemialgebraicOn f ∅ :=
  (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 <| by
    rw [prod_empty]
    exact isMixedSemialgebraicOn_empty _

/-- Finite Boolean glueing: if `f` is mixed semialgebraic on `s` and on `t`, then it is mixed
semialgebraic on `s ∪ t`. -/
theorem IsMixedSemialgebraicOn.union
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s t : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hfs : IsMixedSemialgebraicOn f s) (hft : IsMixedSemialgebraicOn f t) :
    IsMixedSemialgebraicOn f (s ∪ t) :=
  ⟨hfs.1.union hft.1, by rw [graphOn_union, preimage_union]; exact hfs.2.union hft.2⟩

/-- Finite Boolean glueing: if `f` is multiprojective semialgebraic on `s` and on `t`, then it is
multiprojective semialgebraic on `s ∪ t`. -/
theorem IsMultiprojectiveSemialgebraicOn.union
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s t : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hfs : IsMultiprojectiveSemialgebraicOn f s) (hft : IsMultiprojectiveSemialgebraicOn f t) :
    IsMultiprojectiveSemialgebraicOn f (s ∪ t) :=
  (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 <| by
    rw [prod_union]
    exact ((isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hfs).union
      ((isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hft)

/-- Piecewise Boolean glueing of two mixed semialgebraic maps along a mixed semialgebraic set. -/
theorem IsMixedSemialgebraicOn.piecewise
    {f g : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s u : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    [DecidablePred (· ∈ s)]
    (hf : IsMixedSemialgebraicOn f (u ∩ s)) (hg : IsMixedSemialgebraicOn g (u \ s)) :
    IsMixedSemialgebraicOn (s.piecewise f g) u := by
  have hu : u = u ∩ s ∪ u \ s := (inter_union_sdiff u s).symm
  rw [hu]
  exact (hf.congr fun x hx ↦ (piecewise_eq_of_mem s f g hx.2).symm).union
    (hg.congr fun x hx ↦ (piecewise_eq_of_notMem s f g hx.2).symm)

/-- When both projective index types are empty, `TauCeti.IsMixedSemialgebraicOn` reduces to
`TauCeti.IsSemialgebraicOn` on the affine coordinate spaces. -/
theorem isMixedSemialgebraicOn_iff_isSemialgebraicOn_of_isEmpty [IsEmpty ι₁] [IsEmpty ι₂]
    {f : (σ₁ → K) → (σ₂ → K)} {s : Set (σ₁ → K)} :
    IsMixedSemialgebraicOn
        (fun xp : (σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K) ↦
          (f xp.1, (isEmptyElim : ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))))
        (Prod.fst ⁻¹' s) ↔
      IsSemialgebraicOn f s := by
  rw [isMixedSemialgebraicOn_def, isSemialgebraicOn_def]
  refine and_congr (isMixedSemialgebraic_of_isEmpty_iff (K := K) (ι := ι₁)) ?_
  have hpre : (mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹'
      (Prod.fst ⁻¹' s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))).graphOn
        (fun xp ↦ (f xp.1, (isEmptyElim : ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))) =
      Prod.fst ⁻¹' (Equiv.sumArrowEquivProdArrow σ₁ σ₂ K ⁻¹' s.graphOn f) := by
    ext ⟨z, p⟩
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨hzs, heq⟩ := mem_graphOn.1 h
      exact mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hzs, (Prod.mk.inj heq).1⟩
    · obtain ⟨hzs, heq⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 h
      exact mem_graphOn.2 ⟨hzs, Prod.ext heq (Subsingleton.elim _ _)⟩
  rw [hpre, isMixedSemialgebraic_of_isEmpty_iff (K := K) (ι := ι₁ ⊕ ι₂)]
  rfl

/-! ### Standard constructors and projections -/

private theorem isSemialgebraic_id_cone_eq (σ : Type*) [Finite σ] [Finite ι] (n : ι → ℕ) :
    IsSemialgebraic
      {w : ((σ ⊕ σ) ⊕ Σ k : ι ⊕ ι, Fin (Sum.elim n n k + 1)) → K |
        (∀ j : ι, (fun l : Fin (n j + 1) ↦ w (.inr ⟨.inr j, l⟩)) ≠ 0) ∧
        (∀ a : σ, w (.inl (.inl a)) = w (.inl (.inr a))) ∧
        ∀ (i : ι) (j k : Fin (n i + 1)),
          w (.inr ⟨.inl i, j⟩) * w (.inr ⟨.inr i, k⟩) =
            w (.inr ⟨.inl i, k⟩) * w (.inr ⟨.inr i, j⟩)} := by
  have h₁ : IsSemialgebraic
      ((fun w : ((σ ⊕ σ) ⊕ Σ k : ι ⊕ ι, Fin (Sum.elim n n k + 1)) → K ↦
        fun q : Σ j : ι, Fin (n j + 1) ↦ w (.inr ⟨.inr q.1, q.2⟩)) ⁻¹'
          multiprojectivePuncturedCone n K) :=
    isSemialgebraic_multiprojectivePuncturedCone.preimage_comp
      (fun q : Σ j : ι, Fin (n j + 1) ↦
        (Sum.inr ⟨.inr q.1, q.2⟩ : (σ ⊕ σ) ⊕ Σ k : ι ⊕ ι, Fin (Sum.elim n n k + 1)))
  have h₂ : IsSemialgebraic
      (⋂ a : σ, {w : ((σ ⊕ σ) ⊕ Σ k : ι ⊕ ι, Fin (Sum.elim n n k + 1)) → K |
        eval w (X (.inl (.inl a)) - X (.inl (.inr a))) = 0}) :=
    .iInter fun _ ↦ isSemialgebraic_eval_eq_zero _
  have h₃ : IsSemialgebraic
      (⋂ (i : ι) (j : Fin (n i + 1)) (k : Fin (n i + 1)),
        {w : ((σ ⊕ σ) ⊕ Σ k : ι ⊕ ι, Fin (Sum.elim n n k + 1)) → K |
          eval w (X (.inr ⟨.inl i, j⟩) * X (.inr ⟨.inr i, k⟩) -
            X (.inr ⟨.inl i, k⟩) * X (.inr ⟨.inr i, j⟩)) = 0}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ isSemialgebraic_eval_eq_zero _
  convert (h₁.inter h₂).inter h₃ using 1
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_multiprojectivePuncturedCone, mem_iInter,
    mem_ofPred_eq, map_sub, map_mul, eval_X, sub_eq_zero, and_assoc]

/-- The identity map on a mixed space with finitely many affine and projective factors is mixed
semialgebraic on every mixed semialgebraic domain. -/
theorem isMixedSemialgebraicOn_id [Finite σ] [Finite ι]
    {s : Set ((σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K))} (hs : IsMixedSemialgebraic s) :
    IsMixedSemialgebraicOn id s := by
  refine ⟨hs, ?_⟩
  rw [isMixedSemialgebraic_def]
  let e := mixedProdConeIndexEquiv σ σ n n
  convert ((isMixedSemialgebraic_def.1 hs).preimage_comp (fun c ↦ e (.inl c))).inter
      (isSemialgebraic_id_cone_eq (K := K) σ n) using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff, mem_preimage, mem_mixedCone]
  simp only [Function.comp_def, e,
    mixedProdConeIndexEquiv_inl_inl, mixedProdConeIndexEquiv_inl_inr, mem_ofPred_eq]
  constructor
  · rintro ⟨hw₁, hw₂, hmem⟩
    obtain ⟨hws, heq⟩ := mem_graphOn.1 hmem
    exact ⟨⟨hw₁, hws⟩, hw₂, fun a ↦ congrFun (congrArg Prod.fst heq) a,
      fun i ↦ (Projectivization.mk_eq_mk_iff_forall_mul_eq (hw₁ i) (hw₂ i)).1
        (congrFun (congrArg Prod.snd heq) i)⟩
  · rintro ⟨⟨hw₁, hws⟩, hw₂, ha, hp⟩
    refine ⟨hw₁, hw₂, mem_graphOn.2 ⟨hws, Prod.ext (funext ha) (funext fun i ↦ ?_)⟩⟩
    exact (Projectivization.mk_eq_mk_iff_forall_mul_eq (hw₁ i) (hw₂ i)).2 (hp i)

@[simp]
theorem isMixedSemialgebraicMap_id [Finite σ] [Finite ι] :
    IsMixedSemialgebraicMap
      (id : ((σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K)) →
        ((σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K))) :=
  isMixedSemialgebraicOn_id isMixedSemialgebraic_univ

@[simp]
theorem isMultiprojectiveSemialgebraicMap_id [Finite ι] :
    IsMultiprojectiveSemialgebraicMap
      (id : (∀ i : ι, ℙ K (Fin (n i + 1) → K)) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)) :=
  (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).1 <| by
    rw [univ_prod_univ]
    exact (isMixedSemialgebraicOn_id isMixedSemialgebraic_univ).congr fun x _ ↦
      Prod.ext (Subsingleton.elim _ _) rfl

/-- A constant map into a finite-dimensional mixed space is mixed semialgebraic on every mixed
semialgebraic domain. -/
theorem isMixedSemialgebraicOn_const [Finite σ₂] [Finite ι₂]
    (c : (σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} (hs : IsMixedSemialgebraic s) :
    IsMixedSemialgebraicOn (fun _ ↦ c) s := by
  refine ⟨hs, ?_⟩
  have hgraph : s.graphOn (fun _ ↦ c) = s ×ˢ {c} := by
    ext ⟨_, _⟩
    simp [eq_comm]
  rw [hgraph]
  exact hs.prod (isMixedSemialgebraic_singleton c)

/-- Pairing two mixed semialgebraic maps on the same domain produces a mixed semialgebraic map into
the product mixed space. -/
theorem IsMixedSemialgebraicOn.prodMk
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {g : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₃ → K) × ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) (hg : IsMixedSemialgebraicOn g s) :
    IsMixedSemialgebraicOn (fun x ↦ mixedProdEquiv σ₂ σ₃ n₂ n₃ (f x, g x)) s := by
  refine ⟨hf.1, ?_⟩
  rw [isMixedSemialgebraic_def]
  let f₁₂ : ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) →
      ((σ₁ ⊕ (σ₂ ⊕ σ₃)) ⊕ Σ k : ι₁ ⊕ (ι₂ ⊕ ι₃), Fin (Sum.elim n₁ (Sum.elim n₂ n₃) k + 1))
    | .inl (.inl a₁) => .inl (.inl a₁)
    | .inl (.inr a₂) => .inl (.inr (.inl a₂))
    | .inr ⟨.inl i, j⟩ => .inr ⟨.inl i, j⟩
    | .inr ⟨.inr j, l⟩ => .inr ⟨.inr (.inl j), l⟩
  let f₁₃ : ((σ₁ ⊕ σ₃) ⊕ Σ k : ι₁ ⊕ ι₃, Fin (Sum.elim n₁ n₃ k + 1)) →
      ((σ₁ ⊕ (σ₂ ⊕ σ₃)) ⊕ Σ k : ι₁ ⊕ (ι₂ ⊕ ι₃), Fin (Sum.elim n₁ (Sum.elim n₂ n₃) k + 1))
    | .inl (.inl a₁) => .inl (.inl a₁)
    | .inl (.inr a₃) => .inl (.inr (.inr a₃))
    | .inr ⟨.inl i, j⟩ => .inr ⟨.inl i, j⟩
    | .inr ⟨.inr l, m⟩ => .inr ⟨.inr (.inr l), m⟩
  convert ((isMixedSemialgebraic_def.1 hf.2).preimage_comp f₁₂).inter
    ((isMixedSemialgebraic_def.1 hg.2).preimage_comp f₁₃) using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff]
  simp only [mem_preimage, Function.comp_def, mem_mixedCone_preimage_mixedProdEquiv_symm,
    f₁₂, f₁₃]
  constructor
  · rintro ⟨hw₁, hw₂₃, hmem⟩
    obtain ⟨hws, hfg⟩ := mem_graphOn.1 hmem
    have hfg' := congrArg (mixedProdEquiv σ₂ σ₃ n₂ n₃).symm hfg
    rw [Equiv.symm_apply_apply] at hfg'
    obtain ⟨hf_eq, hg_eq⟩ := Prod.mk.inj hfg'
    exact ⟨⟨hw₁, fun j ↦ hw₂₃ (.inl j), mem_graphOn.2 ⟨hws, hf_eq⟩⟩,
      ⟨hw₁, fun l ↦ hw₂₃ (.inr l), mem_graphOn.2 ⟨hws, hg_eq⟩⟩⟩
  · rintro ⟨⟨hw₁, hw₂, hmem₁₂⟩, ⟨_, hw₃, hmem₁₃⟩⟩
    obtain ⟨hws, hf_eq⟩ := mem_graphOn.1 hmem₁₂
    obtain ⟨_, hg_eq⟩ := mem_graphOn.1 hmem₁₃
    refine ⟨hw₁, fun | .inl j => hw₂ j | .inr l => hw₃ l, mem_graphOn.2 ⟨hws, ?_⟩⟩
    exact (congrArg (mixedProdEquiv σ₂ σ₃ n₂ n₃) (Prod.ext hf_eq hg_eq)).trans
      ((mixedProdEquiv σ₂ σ₃ n₂ n₃).apply_symm_apply _)

/-- Pairing two multiprojective semialgebraic maps on the same domain produces a multiprojective
semialgebraic map into the product multiprojective space. -/
theorem IsMultiprojectiveSemialgebraicOn.prodMk
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {g : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) (hg : IsMultiprojectiveSemialgebraicOn g s) :
    IsMultiprojectiveSemialgebraicOn
      (fun p ↦ (Equiv.sumPiEquivProdPi fun k : ι₂ ⊕ ι₃ ↦
        ℙ K (Fin (Sum.elim n₂ n₃ k + 1) → K)).symm (f p, g p)) s := by
  rw [← isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty ⊕ Empty)]
  have hf' := (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf
  have hg' := (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hg
  exact (hf'.prodMk hg').congr fun xp _ ↦ Prod.ext (Subsingleton.elim _ _) rfl

/-- The diagonal map `x ↦ mixedProdEquiv σ σ n n (x, x)` on a finite-dimensional mixed space is
mixed semialgebraic on every mixed semialgebraic domain. -/
theorem isMixedSemialgebraicOn_diag [Finite σ] [Finite ι]
    {s : Set ((σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K))} (hs : IsMixedSemialgebraic s) :
    IsMixedSemialgebraicOn (fun x ↦ mixedProdEquiv σ σ n n (x, x)) s :=
  (isMixedSemialgebraicOn_id hs).prodMk (isMixedSemialgebraicOn_id hs)

/-- The diagonal map `p ↦ (Equiv.sumPiEquivProdPi _).symm (p, p)` on a multiprojective space is
multiprojective semialgebraic. -/
theorem isMultiprojectiveSemialgebraicMap_diag [Finite ι] :
    IsMultiprojectiveSemialgebraicMap
      (fun p : ∀ i : ι, ℙ K (Fin (n i + 1) → K) ↦
        (Equiv.sumPiEquivProdPi fun k : ι ⊕ ι ↦
          ℙ K (Fin (Sum.elim n n k + 1) → K)).symm (p, p)) :=
  isMultiprojectiveSemialgebraicMap_id.prodMk isMultiprojectiveSemialgebraicMap_id

/-- First projection from a product mixed space is mixed semialgebraic. -/
theorem isMixedSemialgebraicMap_fst [Finite σ₁] [Finite ι₁] [Finite ι₂] :
    IsMixedSemialgebraicMap
      (fun z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K) ↦
        ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).1) := by
  refine ⟨isMixedSemialgebraic_univ, ?_⟩
  rw [isMixedSemialgebraic_def]
  let f₁₁ : ((σ₁ ⊕ σ₁) ⊕ Σ k : ι₁ ⊕ ι₁, Fin (Sum.elim n₁ n₁ k + 1)) →
      (((σ₁ ⊕ σ₂) ⊕ σ₁) ⊕ Σ k : (ι₁ ⊕ ι₂) ⊕ ι₁, Fin (Sum.elim (Sum.elim n₁ n₂) n₁ k + 1))
    | .inl (.inl a₁) => .inl (.inl (.inl a₁))
    | .inl (.inr a₁') => .inl (.inr a₁')
    | .inr ⟨.inl i, j⟩ => .inr ⟨.inl (.inl i), j⟩
    | .inr ⟨.inr i', j⟩ => .inr ⟨.inr i', j⟩
  have h₂ : IsSemialgebraic
      ((fun w : (((σ₁ ⊕ σ₂) ⊕ σ₁) ⊕
          Σ k : (ι₁ ⊕ ι₂) ⊕ ι₁, Fin (Sum.elim (Sum.elim n₁ n₂) n₁ k + 1)) → K ↦
        fun q : Σ j : ι₂, Fin (n₂ j + 1) ↦ w (.inr ⟨.inl (.inr q.1), q.2⟩)) ⁻¹'
          multiprojectivePuncturedCone n₂ K) :=
    isSemialgebraic_multiprojectivePuncturedCone.preimage_comp
      (fun q : Σ j : ι₂, Fin (n₂ j + 1) ↦
        (Sum.inr ⟨.inl (.inr q.1), q.2⟩ :
          ((σ₁ ⊕ σ₂) ⊕ σ₁) ⊕ Σ k : (ι₁ ⊕ ι₂) ⊕ ι₁, Fin (Sum.elim (Sum.elim n₁ n₂) n₁ k + 1)))
  convert ((isMixedSemialgebraic_def.1
      (isMixedSemialgebraicMap_id (K := K) (σ := σ₁) (n := n₁)).2).preimage_comp f₁₁).inter
    h₂ using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff]
  simp only [mem_preimage, Function.comp_def, mem_mixedCone_preimage_mixedProdEquiv_symm,
    mem_multiprojectivePuncturedCone, f₁₁]
  constructor
  · rintro ⟨hw₁₂, hw₁', hmem⟩
    obtain ⟨_, heq⟩ := mem_graphOn.1 hmem
    exact ⟨⟨fun i ↦ hw₁₂ (.inl i), hw₁', mem_graphOn.2 ⟨trivial, heq⟩⟩, fun j ↦ hw₁₂ (.inr j)⟩
  · rintro ⟨⟨hw₁, hw₁', hmem⟩, hw₂⟩
    obtain ⟨_, heq⟩ := mem_graphOn.1 hmem
    exact ⟨fun | .inl i => hw₁ i | .inr j => hw₂ j, hw₁', mem_graphOn.2 ⟨trivial, heq⟩⟩

/-- Second projection from a product mixed space is mixed semialgebraic. -/
theorem isMixedSemialgebraicMap_snd [Finite σ₂] [Finite ι₁] [Finite ι₂] :
    IsMixedSemialgebraicMap
      (fun z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K) ↦
        ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).2) := by
  refine ⟨isMixedSemialgebraic_univ, ?_⟩
  rw [isMixedSemialgebraic_def]
  let swG : (((σ₂ ⊕ σ₁) ⊕ σ₂) ⊕ Σ k : (ι₂ ⊕ ι₁) ⊕ ι₂, Fin (Sum.elim (Sum.elim n₂ n₁) n₂ k + 1)) →
      (((σ₁ ⊕ σ₂) ⊕ σ₂) ⊕ Σ k : (ι₁ ⊕ ι₂) ⊕ ι₂, Fin (Sum.elim (Sum.elim n₁ n₂) n₂ k + 1))
    | .inl (.inl (.inl a₂)) => .inl (.inl (.inr a₂))
    | .inl (.inl (.inr a₁)) => .inl (.inl (.inl a₁))
    | .inl (.inr a₂') => .inl (.inr a₂')
    | .inr ⟨.inl (.inl j), l⟩ => .inr ⟨.inl (.inr j), l⟩
    | .inr ⟨.inl (.inr i), j⟩ => .inr ⟨.inl (.inl i), j⟩
    | .inr ⟨.inr j', l⟩ => .inr ⟨.inr j', l⟩
  convert (isMixedSemialgebraic_def.1
      (isMixedSemialgebraicMap_fst (K := K) (σ₁ := σ₂) (σ₂ := σ₁) (n₁ := n₂) (n₂ := n₁)).2
    ).preimage_comp swG using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_preimage,
    mem_mixedCone_preimage_mixedProdEquiv_symm]
  constructor
  · rintro ⟨hw₁₂, hw₂, hmem⟩
    obtain ⟨_, heq⟩ := mem_graphOn.1 hmem
    exact ⟨fun | .inl j => hw₁₂ (.inr j) | .inr i => hw₁₂ (.inl i), hw₂,
      mem_graphOn.2 ⟨trivial, heq⟩⟩
  · rintro ⟨hw₂₁, hw₂, hmem⟩
    obtain ⟨_, heq⟩ := mem_graphOn.1 hmem
    exact ⟨fun | .inl i => hw₂₁ (.inr i) | .inr j => hw₂₁ (.inl j), hw₂,
      mem_graphOn.2 ⟨trivial, heq⟩⟩

/-! ### Images, preimages, and composition under projection closure -/

section ProjectionClosure

variable [HasSemialgebraicProjections K]

/-- Given projection closure, a map into a finite-dimensional mixed space is mixed semialgebraic on
`s` if and only if its graph over `s` is mixed semialgebraic. -/
theorem isMixedSemialgebraicOn_iff_graph [Finite σ₂] [Finite ι₂]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMixedSemialgebraicOn f s ↔
      IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f) := by
  refine ⟨fun hf ↦ hf.graph, fun hG ↦ ⟨?_, hG⟩⟩
  have hfst : Prod.fst '' s.graphOn f = s := by
    ext x
    simp
  rw [← hfst]
  exact hG.image_fst

/-- Given projection closure, the image of `s ∩ t` under a mixed semialgebraic map on `s` from a
finite-dimensional mixed space is mixed semialgebraic when `t` is mixed semialgebraic. -/
theorem IsMixedSemialgebraicOn.isMixedSemialgebraic_image_inter [Finite σ₁] [Finite ι₁]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s t : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) (ht : IsMixedSemialgebraic t) :
    IsMixedSemialgebraic (f '' (s ∩ t)) := by
  have himg : f '' (s ∩ t) = Prod.snd '' ((s ∩ t).graphOn f) := by
    ext y
    simp
  rw [himg]
  exact (hf.mono (hf.1.inter ht) inter_subset_left).graph.image_snd

theorem IsMixedSemialgebraicMap.isMixedSemialgebraic_image [Finite σ₁] [Finite ι₁]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hf : IsMixedSemialgebraicMap f)
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} (hs : IsMixedSemialgebraic s) :
    IsMixedSemialgebraic (f '' s) := by
  simpa using IsMixedSemialgebraicOn.isMixedSemialgebraic_image_inter hf hs

theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_image_inter [Finite ι₁]
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s t : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) (ht : IsMultiprojectiveSemialgebraic t) :
    IsMultiprojectiveSemialgebraic (f '' (s ∩ t)) := by
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)]
  have hf' := (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf
  have ht' : IsMixedSemialgebraic ((univ : Set (Empty → K)) ×ˢ t) :=
    (isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 ht
  convert hf'.isMixedSemialgebraic_image_inter ht' using 1
  ext ⟨x₀, q⟩
  simp only [mem_prod, mem_univ, true_and, mem_image, mem_inter_iff, Prod.exists, Prod.mk.injEq]
  refine ⟨fun ⟨p, hp, hfp⟩ ↦ ⟨x₀, p, hp, Subsingleton.elim _ _, hfp⟩,
    fun ⟨_, p, hp, _, hfp⟩ ↦ ⟨p, hp, hfp⟩⟩

theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraic_image [Finite ι₁]
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} (hs : IsMultiprojectiveSemialgebraic s) :
    IsMultiprojectiveSemialgebraic (f '' s) := by
  simpa using IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_image_inter hf hs

/-- Given projection closure, the preimage of a mixed semialgebraic set inside the domain of a
mixed semialgebraic map into a finite-dimensional mixed space is mixed semialgebraic. -/
theorem IsMixedSemialgebraicOn.isMixedSemialgebraic_inter_preimage [Finite σ₂] [Finite ι₂]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {t : Set ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hf : IsMixedSemialgebraicOn f s) (ht : IsMixedSemialgebraic t) :
    IsMixedSemialgebraic (s ∩ f ⁻¹' t) := by
  have hpre : s ∩ f ⁻¹' t = Prod.fst '' (s.graphOn f ∩ univ ×ˢ t) := by
    ext x
    simp
  rw [hpre]
  have hinter : IsMixedSemialgebraic
      ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' (s.graphOn f ∩ univ ×ˢ t)) := by
    rw [isMixedSemialgebraic_def]
    let e := mixedProdConeIndexEquiv σ₁ σ₂ n₁ n₂
    convert (isMixedSemialgebraic_def.1 hf.2).inter
      ((isMixedSemialgebraic_def.1 ht).preimage_comp (fun c ↦ e (.inr c))) using 1
    ext w
    rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff,
      mem_mixedCone_preimage_mixedProdEquiv_symm, mem_preimage, mem_mixedCone]
    dsimp only [Function.comp_def, e,
      mixedProdConeIndexEquiv_inr_inl, mixedProdConeIndexEquiv_inr_inr]
    constructor
    · rintro ⟨hw₁, hw₂, hG, _, ht_mem⟩
      exact ⟨⟨hw₁, hw₂, hG⟩, hw₂, ht_mem⟩
    · rintro ⟨⟨hw₁, hw₂, hG⟩, _, ht_mem⟩
      exact ⟨hw₁, hw₂, hG, trivial, ht_mem⟩
  exact hinter.image_fst

theorem IsMixedSemialgebraicMap.isMixedSemialgebraic_preimage [Finite σ₂] [Finite ι₂]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hf : IsMixedSemialgebraicMap f)
    {t : Set ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))} (ht : IsMixedSemialgebraic t) :
    IsMixedSemialgebraic (f ⁻¹' t) := by
  simpa using IsMixedSemialgebraicOn.isMixedSemialgebraic_inter_preimage hf ht

theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_inter_preimage [Finite ι₂]
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {t : Set (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f s) (ht : IsMultiprojectiveSemialgebraic t) :
    IsMultiprojectiveSemialgebraic (s ∩ f ⁻¹' t) := by
  rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)]
  have hf' := (isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf
  have ht' : IsMixedSemialgebraic ((univ : Set (Empty → K)) ×ˢ t) :=
    (isMixedSemialgebraic_univ_prod_iff (σ := Empty)).2 ht
  convert hf'.isMixedSemialgebraic_inter_preimage ht' using 1
  ext ⟨_, p⟩
  simp

theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraic_preimage [Finite ι₂]
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {t : Set (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))} (ht : IsMultiprojectiveSemialgebraic t) :
    IsMultiprojectiveSemialgebraic (f ⁻¹' t) := by
  simpa using IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_inter_preimage hf ht

/-- Given projection closure, composing mixed semialgebraic maps through a finite-dimensional
intermediate mixed space preserves mixed semialgebraicity. -/
theorem IsMixedSemialgebraicOn.comp [Finite σ₂] [Finite ι₂]
    {g : ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) →
      ((σ₃ → K) × ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K))}
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {t : Set ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hg : IsMixedSemialgebraicOn g t) (hf : IsMixedSemialgebraicOn f s) (hst : MapsTo f s t) :
    IsMixedSemialgebraicOn (g ∘ f) s := by
  refine ⟨hf.1, ?_⟩
  let e₁₃ := mixedProdEquiv (K := K) σ₁ σ₃ n₁ n₃
  let W : Set (((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) ×
      ((σ₁ ⊕ σ₃ → K) × ∀ k : ι₁ ⊕ ι₃, ℙ K (Fin (Sum.elim n₁ n₃ k + 1) → K))) :=
    {yz | ((e₁₃.symm yz.2).1, yz.1) ∈ s.graphOn f ∧ (yz.1, (e₁₃.symm yz.2).2) ∈ t.graphOn g}
  have hW_img : Prod.snd '' W = e₁₃.symm ⁻¹' s.graphOn (g ∘ f) := by
    ext z
    simp only [W, mem_image, mem_ofPred_eq, mem_graphOn, mem_preimage, Function.comp_apply]
    constructor
    · rintro ⟨⟨y, _⟩, ⟨⟨hz₁, hfy⟩, ⟨_, hgz⟩⟩, rfl⟩
      exact ⟨hz₁, hfy ▸ hgz⟩
    · rintro ⟨hz₁, hgz⟩
      exact ⟨(f (e₁₃.symm z).1, z), ⟨⟨hz₁, rfl⟩, ⟨hst hz₁, hgz⟩⟩, rfl⟩
  rw [← hW_img]
  refine IsMixedSemialgebraic.image_snd ?_
  rw [isMixedSemialgebraic_def]
  let f₁₂ : ((σ₁ ⊕ σ₂) ⊕ Σ k : ι₁ ⊕ ι₂, Fin (Sum.elim n₁ n₂ k + 1)) →
      ((σ₂ ⊕ (σ₁ ⊕ σ₃)) ⊕ Σ k : ι₂ ⊕ (ι₁ ⊕ ι₃), Fin (Sum.elim n₂ (Sum.elim n₁ n₃) k + 1))
    | .inl (.inl a₁) => .inl (.inr (.inl a₁))
    | .inl (.inr a₂) => .inl (.inl a₂)
    | .inr ⟨.inl i, j⟩ => .inr ⟨.inr (.inl i), j⟩
    | .inr ⟨.inr j, l⟩ => .inr ⟨.inl j, l⟩
  let f₂₃ : ((σ₂ ⊕ σ₃) ⊕ Σ k : ι₂ ⊕ ι₃, Fin (Sum.elim n₂ n₃ k + 1)) →
      ((σ₂ ⊕ (σ₁ ⊕ σ₃)) ⊕ Σ k : ι₂ ⊕ (ι₁ ⊕ ι₃), Fin (Sum.elim n₂ (Sum.elim n₁ n₃) k + 1))
    | .inl (.inl a₂) => .inl (.inl a₂)
    | .inl (.inr a₃) => .inl (.inr (.inr a₃))
    | .inr ⟨.inl j, l⟩ => .inr ⟨.inl j, l⟩
    | .inr ⟨.inr l, m⟩ => .inr ⟨.inr (.inr l), m⟩
  convert ((isMixedSemialgebraic_def.1 hf.2).preimage_comp f₁₂).inter
    ((isMixedSemialgebraic_def.1 hg.2).preimage_comp f₂₃) using 1
  ext w
  rw [mem_mixedCone_preimage_mixedProdEquiv_symm, mem_inter_iff, mem_preimage,
    mem_mixedCone_preimage_mixedProdEquiv_symm, mem_preimage,
    mem_mixedCone_preimage_mixedProdEquiv_symm]
  dsimp only [W, e₁₃, Function.comp_def, mixedProdEquiv_symm_apply, f₁₂, f₂₃]
  exact ⟨fun ⟨hw₂, hw₁₃, h₁₂, h₂₃⟩ ↦
      ⟨⟨fun i ↦ hw₁₃ (.inl i), hw₂, h₁₂⟩, ⟨hw₂, fun l ↦ hw₁₃ (.inr l), h₂₃⟩⟩,
    fun ⟨⟨hw₁, hw₂, h₁₂⟩, ⟨_, hw₃, h₂₃⟩⟩ ↦
      ⟨hw₂, fun | .inl i => hw₁ i | .inr l => hw₃ l, h₁₂, h₂₃⟩⟩

theorem IsMixedSemialgebraicMap.comp [Finite σ₂] [Finite ι₂]
    {g : ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) →
      ((σ₃ → K) × ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K))}
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hg : IsMixedSemialgebraicMap g) (hf : IsMixedSemialgebraicMap f) :
    IsMixedSemialgebraicMap (g ∘ f) :=
  IsMixedSemialgebraicOn.comp hg hf (mapsTo_univ _ _)

theorem IsMultiprojectiveSemialgebraicOn.comp [Finite ι₂]
    {g : (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) → ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K)}
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    {s : Set (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))}
    {t : Set (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    (hg : IsMultiprojectiveSemialgebraicOn g t) (hf : IsMultiprojectiveSemialgebraicOn f s)
    (hst : MapsTo f s t) :
    IsMultiprojectiveSemialgebraicOn (g ∘ f) s := by
  rw [← isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)]
  exact ((isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hg).comp
    ((isMixedSemialgebraicOn_univ_prod_iff (σ₁ := Empty) (σ₂ := Empty)).2 hf)
    fun _ hx ↦ ⟨trivial, hst hx.2⟩

theorem IsMultiprojectiveSemialgebraicMap.comp [Finite ι₂]
    {g : (∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)) → ∀ l : ι₃, ℙ K (Fin (n₃ l + 1) → K)}
    {f : (∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) → ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)}
    (hg : IsMultiprojectiveSemialgebraicMap g) (hf : IsMultiprojectiveSemialgebraicMap f) :
    IsMultiprojectiveSemialgebraicMap (g ∘ f) :=
  IsMultiprojectiveSemialgebraicOn.comp hg hf (mapsTo_univ _ _)

end ProjectionClosure

/-! ### Chartwise characterization of graphs and maps -/

section ChartGraphs

omit [LinearOrder K] in
/-- Membership in the product mixed affine open `mixedAffineOpen (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂)`
splits into the two factor mixed affine opens. -/
theorem mem_mixedAffineOpen_sumPiFinIndex
    {I₁ : ∀ i : ι₁, Fin (n₁ i + 1)} {I₂ : ∀ j : ι₂, Fin (n₂ j + 1)}
    {z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K)} :
    z ∈ mixedAffineOpen (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂) ↔
      ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).1 ∈ mixedAffineOpen σ₁ I₁ ∧
        ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).2 ∈ mixedAffineOpen σ₂ I₂ := by
  rw [mem_mixedAffineOpen, mem_mixedAffineOpen, mem_mixedAffineOpen]
  exact mem_multiprojectiveAffineOpen_sumPiFinIndex

omit [LinearOrder K] in
/-- Left-factor coordinates of `mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂)`. -/
theorem mixedAffineChart_sumPiFinIndex_inl
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K))
    (c : σ₁ ⊕ Σ i, Fin (n₁ i)) :
    mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂) z
        (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inl c)) =
      mixedAffineChart σ₁ I₁ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).1 c := by
  rcases c with a₁ | ⟨i, k⟩
  · exact (mixedAffineChart_apply_inl (sumPiFinIndex I₁ I₂) z (.inl a₁)).trans
      (mixedAffineChart_apply_inl I₁ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).1 a₁).symm
  · exact (mixedAffineChart_apply_inr (sumPiFinIndex I₁ I₂) z ⟨.inl i, k⟩).trans
      ((multiprojectiveAffineChart_sumPiFinIndex_inl I₁ I₂ z.2 i k).trans
        (mixedAffineChart_apply_inr I₁ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).1 ⟨i, k⟩).symm)

omit [LinearOrder K] in
/-- Right-factor coordinates of `mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂)`. -/
theorem mixedAffineChart_sumPiFinIndex_inr
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (z : (σ₁ ⊕ σ₂ → K) × ∀ k : ι₁ ⊕ ι₂, ℙ K (Fin (Sum.elim n₁ n₂ k + 1) → K))
    (c : σ₂ ⊕ Σ j, Fin (n₂ j)) :
    mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂) z
        (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂ (.inr c)) =
      mixedAffineChart σ₂ I₂ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).2 c := by
  rcases c with a₂ | ⟨j, l⟩
  · exact (mixedAffineChart_apply_inl (sumPiFinIndex I₁ I₂) z (.inr a₂)).trans
      (mixedAffineChart_apply_inl I₂ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).2 a₂).symm
  · exact (mixedAffineChart_apply_inr (sumPiFinIndex I₁ I₂) z ⟨.inr j, l⟩).trans
      ((multiprojectiveAffineChart_sumPiFinIndex_inr I₁ I₂ z.2 j l).trans
        (mixedAffineChart_apply_inr I₂ ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm z).2 ⟨j, l⟩).symm)

omit [LinearOrder K] in
private theorem mixedProdEquiv_symm_mixedAffineChart_symm
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1))
    (u : ((σ₁ ⊕ Σ i, Fin (n₁ i)) ⊕ (σ₂ ⊕ Σ j, Fin (n₂ j))) → K) :
    (mixedProdEquiv σ₁ σ₂ n₁ n₂).symm
        ((mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂)).symm
          (u ∘ (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm)) =
      ((mixedAffineChart σ₁ I₁).symm (u ∘ Sum.inl),
        (mixedAffineChart σ₂ I₂).symm (u ∘ Sum.inr)) := by
  refine Prod.ext
    (Prod.ext (funext fun _ ↦ by simp)
      (funext fun _ ↦ by
        simp only [mixedAffineChart_symm_apply, mixedProdEquiv_symm_apply, Sum.elim_inl,
          Sum.elim_inr, multiprojectiveAffineChart_symm_apply, sumPiFinIndex_inl,
          Function.comp_apply, mixedProdChartIndexEquiv_symm_inr_inl, sumPiFinIndex_inr,
          mixedProdChartIndexEquiv_symm_inr_inr, Projectivization.affineChart_symm_apply]
        exact Projectivization.affineChart_symm_apply _ _))
    (Prod.ext (funext fun _ ↦ by simp)
      (funext fun _ ↦ by
        simp only [mixedAffineChart_symm_apply, mixedProdEquiv_symm_apply, Sum.elim_inl,
          Sum.elim_inr, multiprojectiveAffineChart_symm_apply, sumPiFinIndex_inl,
          Function.comp_apply, mixedProdChartIndexEquiv_symm_inr_inl, sumPiFinIndex_inr,
          mixedProdChartIndexEquiv_symm_inr_inr, Projectivization.affineChart_symm_apply]
        exact Projectivization.affineChart_symm_apply _ _))

omit [LinearOrder K] in
/-- In standard product affine charts `(I₁, I₂)`, the chart image of
`(mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f` corresponds under
`TauCeti.mixedProdChartIndexEquiv` to the encoded graph of
`mixedAffineChart σ₂ I₂ ∘ f ∘ (mixedAffineChart σ₁ I₁).symm` over
`mixedAffineChart σ₁ I₁ '' (s ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂)`. -/
theorem preimage_mixedProdChartIndexEquiv_image_graphOn
    (f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K)))
    (s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)))
    (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)) :
    (fun u ↦ u ∘ (mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂).symm) ⁻¹'
      (mixedAffineChart (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂) ''
        (((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f) ∩
          mixedAffineOpen (σ₁ ⊕ σ₂) (sumPiFinIndex I₁ I₂))) =
      Equiv.sumArrowEquivProdArrow (σ₁ ⊕ Σ i, Fin (n₁ i)) (σ₂ ⊕ Σ j, Fin (n₂ j)) K ⁻¹'
        (mixedAffineChart σ₁ I₁ ''
          (s ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂)).graphOn
          (mixedAffineChart σ₂ I₂ ∘ f ∘ (mixedAffineChart σ₁ I₁).symm) := by
  rw [mixedAffineChart_image_inter_affineOpen, inter_right_comm s,
    mixedAffineChart_image_inter_affineOpen]
  ext u
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_preimage, mem_preimage, mem_preimage,
    mixedProdEquiv_symm_mixedAffineChart_symm, mem_graphOn, mem_preimage, mem_inter_iff,
    mem_preimage, Function.comp_apply, Function.comp_apply]
  constructor
  · rintro ⟨hx₁s, hfx₁⟩
    refine ⟨⟨hx₁s, ?_⟩, ?_⟩
    · rw [hfx₁]
      exact mixedAffineChart_symm_mem_affineOpen I₂ _
    · rw [hfx₁]
      exact (mixedAffineChart σ₂ I₂).right_inv (by rw [mixedAffineChart_target]; exact mem_univ _)
  · rintro ⟨⟨hx₁s, hfx₁I⟩, hchart⟩
    refine ⟨hx₁s, ?_⟩
    rw [← hchart]
    exact ((mixedAffineChart σ₂ I₂).left_inv (by rw [mixedAffineChart_source]; exact hfx₁I)).symm

variable [IsStrictOrderedRing K]

/-- Over a strict ordered field and finitely many projective factors, the graph of `f` over `s` is
mixed semialgebraic if and only if its local graph in every pair of standard product affine charts
is semialgebraic. No projection closure is required. -/
theorem isMixedSemialgebraic_graphOn_iff_forall_chart [Finite ι₁] [Finite ι₂]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMixedSemialgebraic ((mixedProdEquiv σ₁ σ₂ n₁ n₂).symm ⁻¹' s.graphOn f) ↔
      ∀ (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
        IsSemialgebraic
          (Equiv.sumArrowEquivProdArrow (σ₁ ⊕ Σ i, Fin (n₁ i)) (σ₂ ⊕ Σ j, Fin (n₂ j)) K ⁻¹'
            (mixedAffineChart σ₁ I₁ ''
              (s ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂)).graphOn
              (mixedAffineChart σ₂ I₂ ∘ f ∘ (mixedAffineChart σ₁ I₁).symm)) := by
  let e := mixedProdChartIndexEquiv σ₁ σ₂ n₁ n₂
  rw [isMixedSemialgebraic_iff_forall_chart]
  constructor
  · intro h I₁ I₂
    rw [← preimage_mixedProdChartIndexEquiv_image_graphOn]
    exact (h (sumPiFinIndex I₁ I₂)).preimage_comp e.symm
  · intro h I
    rw [← sumPiFinIndex_eta I]
    exact (isSemialgebraic_preimage_comp_equiv e.symm).1 <|
      (preimage_mixedProdChartIndexEquiv_image_graphOn f s _ _).symm ▸ h _ _

/-- Given projection closure, `f` is mixed semialgebraic on `s` if and only if in every pair of
standard product affine charts `(I₁, I₂)` the chart map `mixedAffineChart σ₂ I₂ ∘ f ∘
(mixedAffineChart σ₁ I₁).symm` is `TauCeti.IsSemialgebraicOn` on the chart image of
`s ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂`. -/
theorem isMixedSemialgebraicOn_iff_forall_isSemialgebraicOn
    [HasSemialgebraicProjections K] [Finite σ₂] [Finite ι₁] [Finite ι₂]
    {f : ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K)) →
      ((σ₂ → K) × ∀ j : ι₂, ℙ K (Fin (n₂ j + 1) → K))}
    {s : Set ((σ₁ → K) × ∀ i : ι₁, ℙ K (Fin (n₁ i + 1) → K))} :
    IsMixedSemialgebraicOn f s ↔
      ∀ (I₁ : ∀ i : ι₁, Fin (n₁ i + 1)) (I₂ : ∀ j : ι₂, Fin (n₂ j + 1)),
        IsSemialgebraicOn
          (mixedAffineChart σ₂ I₂ ∘ f ∘ (mixedAffineChart σ₁ I₁).symm)
          (mixedAffineChart σ₁ I₁ ''
            (s ∩ mixedAffineOpen σ₁ I₁ ∩ f ⁻¹' mixedAffineOpen σ₂ I₂)) := by
  rw [isMixedSemialgebraicOn_iff_graph, isMixedSemialgebraic_graphOn_iff_forall_chart]
  exact forall₂_congr fun _ _ ↦ isSemialgebraicOn_iff_graph.symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- For a map `τ : (σ → K) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)` from an affine space into a
multiprojective space, the `I`-chart image of `s.graphOn τ` is the encoded graph of
`multiprojectiveAffineChart I ∘ τ` over `s ∩ τ ⁻¹' multiprojectiveAffineOpen I`. -/
theorem mixedAffineChart_image_affine_graphOn
    (τ : (σ → K) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)) (s : Set (σ → K))
    (I : ∀ i : ι, Fin (n i + 1)) :
    mixedAffineChart σ I '' (s.graphOn τ ∩ mixedAffineOpen σ I) =
      Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i)) K ⁻¹'
        (s ∩ τ ⁻¹' multiprojectiveAffineOpen I).graphOn (multiprojectiveAffineChart I ∘ τ) := by
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  simp only [mem_inter_iff, mem_graphOn, mem_mixedAffineOpen, mem_preimage, Prod.exists]
  constructor
  · rintro ⟨x, p, ⟨⟨hxs, rfl⟩, hpI⟩, rfl⟩
    have hx_inl : mixedAffineChart σ I (x, τ x) ∘ Sum.inl = x :=
      funext fun a ↦ mixedAffineChart_apply_inl I (x, τ x) a
    refine ⟨⟨by rwa [hx_inl], by rwa [hx_inl]⟩, ?_⟩
    ext q
    simp [hx_inl]
  · rintro ⟨⟨hzs, hτz⟩, hchart⟩
    refine ⟨z ∘ Sum.inl, τ (z ∘ Sum.inl), ⟨⟨hzs, rfl⟩, hτz⟩, ?_⟩
    ext (a | q)
    · simp
    · rw [mixedAffineChart_apply_inr]
      exact congrFun hchart q

/-- The graph `s.graphOn τ ⊆ (σ → K) × ∀ i : ι, ℙ K (Fin (n i + 1) → K)` of a map from an affine
set `s` to a multiprojective space is mixed semialgebraic if and only if in every standard product
affine chart `I` the encoded graph of `multiprojectiveAffineChart I ∘ τ` over
`s ∩ τ ⁻¹' multiprojectiveAffineOpen I` is semialgebraic. -/
theorem isMixedSemialgebraic_affine_graphOn_iff_forall_chart [Finite ι]
    {τ : (σ → K) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)} :
    IsMixedSemialgebraic (s.graphOn τ) ↔
      ∀ I : ∀ i : ι, Fin (n i + 1),
        IsSemialgebraic
          (Equiv.sumArrowEquivProdArrow σ (Σ i, Fin (n i)) K ⁻¹'
            (s ∩ τ ⁻¹' multiprojectiveAffineOpen I).graphOn
              (multiprojectiveAffineChart I ∘ τ)) := by
  rw [isMixedSemialgebraic_iff_forall_chart]
  exact forall_congr' fun I ↦ by rw [mixedAffineChart_image_affine_graphOn]

/-- Given projection closure, `s.graphOn τ` is mixed semialgebraic if and only if
`multiprojectiveAffineChart I ∘ τ` is `TauCeti.IsSemialgebraicOn` on
`s ∩ τ ⁻¹' multiprojectiveAffineOpen I` for every standard product affine chart `I`. -/
theorem isMixedSemialgebraic_affine_graphOn_iff_forall_isSemialgebraicOn
    [HasSemialgebraicProjections K] [Finite ι]
    {τ : (σ → K) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)} :
    IsMixedSemialgebraic (s.graphOn τ) ↔
      ∀ I : ∀ i : ι, Fin (n i + 1),
        IsSemialgebraicOn (multiprojectiveAffineChart I ∘ τ)
          (s ∩ τ ⁻¹' multiprojectiveAffineOpen I) := by
  rw [isMixedSemialgebraic_affine_graphOn_iff_forall_chart]
  exact forall_congr' fun _ ↦ isSemialgebraicOn_iff_graph.symm

/-- Given projection closure, if the graph `s.graphOn τ` of a map into a finite-dimensional
multiprojective space is mixed semialgebraic, then the affine domain `s` is semialgebraic. -/
theorem IsMixedSemialgebraic.isSemialgebraic_of_graphOn
    [HasSemialgebraicProjections K] [Finite ι]
    {τ : (σ → K) → ∀ i : ι, ℙ K (Fin (n i + 1) → K)} {s : Set (σ → K)}
    (h : IsMixedSemialgebraic (s.graphOn τ)) : IsSemialgebraic s := by
  have hI := isMixedSemialgebraic_affine_graphOn_iff_forall_isSemialgebraicOn.1 h
  have hs : s = ⋃ I : ∀ i : ι, Fin (n i + 1), s ∩ τ ⁻¹' multiprojectiveAffineOpen I := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage]
    exact ⟨fun hxs ↦ let ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen (τ x); ⟨I, hxs, hpI⟩,
      fun ⟨_, hxs, _⟩ ↦ hxs⟩
  rw [hs]
  exact .iUnion fun I ↦ (hI I).isSemialgebraic

end ChartGraphs

end Maps

end TauCeti
