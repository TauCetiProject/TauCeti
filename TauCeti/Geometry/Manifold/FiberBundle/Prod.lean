/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Prod

/-!
# Smooth fibrewise products of bundles

Mathlib's fibrewise product `FiberBundle.prod` of two `C^n` fibre bundles is a `C^n` fibre
bundle (`TauCeti.ContMDiffFiberBundle.prod`), since the changes of fibre coordinates are
componentwise (`Bundle.Trivialization.coordChange_prod`).

The projections detect smoothness of maps into the charted total space
(`TauCeti.ManifoldTotalSpace.contMDiff_prod_iff`), using the preferred-chart criterion
`TauCeti.ManifoldTotalSpace.contMDiffWithinAt_iff`. Pairs with equal base projections lift uniquely
to a smooth map (`TauCeti.ManifoldTotalSpace.existsUnique_contMDiff_of_proj_eq`), using the range
and injectivity of the fibrewise-product diagonal.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {B F₁ F₂ : Type*} [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] {H₁ : Type*} [TopologicalSpace H₁]
  {I₁ : ModelWithCorners 𝕜 V₁ H₁} [ChartedSpace H₁ F₁]
  {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] {H₂ : Type*} [TopologicalSpace H₂]
  {I₂ : ModelWithCorners 𝕜 V₂ H₂} [ChartedSpace H₂ F₂]
  {E₁ E₂ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, TopologicalSpace (E₂ b)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] [∀ b, Zero (E₁ b)] [∀ b, Zero (E₂ b)]

/-- The fibrewise product of two `C^n` fibre bundles is `C^n`. The fibre points provided
by `Zero` are the values of the inverse trivializations outside their base sets. -/
instance ContMDiffFiberBundle.prod
    [ContMDiffFiberBundle n F₁ E₁ IB I₁] [ContMDiffFiberBundle n F₂ E₂ IB I₂] :
    ContMDiffFiberBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) IB (I₁.prod I₂) where
  contMDiffOn_coordChange e e' he he' := by
    obtain ⟨e₁, e₂, h₁, h₂, rfl⟩ := he.out
    obtain ⟨e₁', e₂', h₁', h₂', rfl⟩ := he'.out
    let overlap : Set (B × F₁ × F₂) :=
      ((e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)) ×ˢ univ
    have hc₁ : ContMDiffOn (IB.prod (I₁.prod I₂)) I₁ n
        (fun p : B × F₁ × F₂ ↦ e₁.coordChange e₁' p.1 p.2.1) overlap := by
      exact (ContMDiffFiberBundle.contMDiffOn_coordChange e₁ e₁').comp
        (contMDiffOn_fst.prodMk (contMDiff_fst.comp_contMDiffOn contMDiffOn_snd))
        (fun _ hx ↦ ⟨⟨hx.1.1.1, hx.1.2.1⟩, mem_univ _⟩)
    have hc₂ : ContMDiffOn (IB.prod (I₁.prod I₂)) I₂ n
        (fun p : B × F₁ × F₂ ↦ e₂.coordChange e₂' p.1 p.2.2) overlap := by
      exact (ContMDiffFiberBundle.contMDiffOn_coordChange e₂ e₂').comp
        (contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn contMDiffOn_snd))
        (fun _ hx ↦ ⟨⟨hx.1.1.2, hx.1.2.2⟩, mem_univ _⟩)
    refine (hc₁.prodMk hc₂).congr ?_
    rintro ⟨b, v₁, v₂⟩ hb
    exact e₁.coordChange_prod e₁' e₂ e₂' hb.1.1.1 hb.1.1.2 v₁ v₂

namespace ManifoldTotalSpace

variable {M EM HM : Type*} [TopologicalSpace M]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [ChartedSpace HM M]
  {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}

/-- A family in a fibrewise product is `C^n` within a set at a point if and only if both
component families are `C^n` there. This does not require smooth transition functions. -/
theorem contMDiffWithinAt_prod_iff {s : Set M} {x : M} :
    ContMDiffWithinAt IM (IB.prod (I₁.prod I₂)) n
      (fun y ↦ homeomorph (F₁ × F₂) (E₁ ×ᵇ E₂) (f y)) s x ↔
      ContMDiffWithinAt IM (IB.prod I₁) n
        (fun y ↦ homeomorph F₁ E₁ ⟨(f y).proj, (f y).snd.fst⟩) s x ∧
      ContMDiffWithinAt IM (IB.prod I₂) n
        (fun y ↦ homeomorph F₂ E₂ ⟨(f y).proj, (f y).snd.snd⟩) s x := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff, ManifoldTotalSpace.contMDiffWithinAt_iff,
    ManifoldTotalSpace.contMDiffWithinAt_iff]
  simp only [trivializationAt_prod_snd, _root_.contMDiffWithinAt_prod_iff, Function.comp_def]
  tauto

/-- A map into the charted total space of a fibrewise product is `C^n` if and only if both
of its projections are `C^n`. In particular, a pair of smooth maps into the two factors
with a common base projection has a smooth lift to the fibrewise product. -/
theorem contMDiff_prod_iff :
    ContMDiff IM (IB.prod (I₁.prod I₂)) n
      (fun y ↦ homeomorph (F₁ × F₂) (E₁ ×ᵇ E₂) (f y)) ↔
      ContMDiff IM (IB.prod I₁) n
        (fun y ↦ homeomorph F₁ E₁ ⟨(f y).proj, (f y).snd.fst⟩) ∧
      ContMDiff IM (IB.prod I₂) n
        (fun y ↦ homeomorph F₂ E₂ ⟨(f y).proj, (f y).snd.snd⟩) := by
  simp only [ContMDiff, ← contMDiffWithinAt_univ, contMDiffWithinAt_prod_iff, forall_and]

/-- Two `C^n` families with the same base projection lift uniquely to a `C^n` family
in the fibrewise product. -/
theorem existsUnique_contMDiff_of_proj_eq {p : M → TotalSpace F₁ E₁} {q : M → TotalSpace F₂ E₂}
    (hp : ContMDiff IM (IB.prod I₁) n (fun x ↦ homeomorph F₁ E₁ (p x)))
    (hq : ContMDiff IM (IB.prod I₂) n (fun x ↦ homeomorph F₂ E₂ (q x)))
    (hproj : ∀ x, (p x).proj = (q x).proj) :
    ∃! f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂),
      ContMDiff IM (IB.prod (I₁.prod I₂)) n
        (fun x ↦ homeomorph (F₁ × F₂) (E₁ ×ᵇ E₂) (f x)) ∧
      ∀ x, ((⟨(f x).proj, (f x).snd.fst⟩ : TotalSpace F₁ E₁),
        (⟨(f x).proj, (f x).snd.snd⟩ : TotalSpace F₂ E₂)) = (p x, q x) := by
  let diag (z : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    (⟨z.proj, z.snd.fst⟩, ⟨z.proj, z.snd.snd⟩)
  have hrange : range diag = {z | z.1.proj = z.2.proj} := FiberBundle.Prod.range_diag
  have hexists (x : M) : (p x, q x) ∈ range diag := by
    rw [hrange]
    exact hproj x
  choose lift hlift using hexists
  have hsmooth : ContMDiff IM (IB.prod (I₁.prod I₂)) n
      (fun x ↦ homeomorph (F₁ × F₂) (E₁ ×ᵇ E₂) (lift x)) := by
    refine contMDiff_prod_iff.2 ⟨hp.congr ?_, hq.congr ?_⟩
    · exact fun x ↦ congrArg (homeomorph F₁ E₁) (congrArg Prod.fst (hlift x))
    · exact fun x ↦ congrArg (homeomorph F₂ E₂) (congrArg Prod.snd (hlift x))
  refine ⟨lift, ⟨hsmooth, hlift⟩, fun g hg ↦ ?_⟩
  have hinj : Function.Injective diag := FiberBundle.Prod.isEmbedding_diag.injective
  exact funext fun x ↦ hinj ((hg.2 x).trans (hlift x).symm)

end ManifoldTotalSpace

end TauCeti
