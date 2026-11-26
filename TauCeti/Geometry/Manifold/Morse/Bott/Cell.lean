/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle

/-!
# Negative discs of Morse–Bott submanifolds and Morse cells

Let `i : S → M` be a nondegenerate critical submanifold of a function `f`, with a fibre metric
`g` on its normal bundle `ν`, and let `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}` be its negative
disc bundle (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`). This file shows
that each fibre of `D_ε` is a closed disc whose dimension is the Morse index `λ`, and deduces that
for a critical submanifold consisting of one point, the Morse–Bott attachment theorem
`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation` is
Milnor's attachment of a cell of dimension `λ`. So the Morse–Bott attachment specializes to the
cell attachment of an ordinary Morse function at an isolated critical point.

On the negative normal space at `s` the form `-½ Hessₛ` is positive definite, so it is the
squared norm of a Euclidean space of dimension `λ`
(`IsNondegenerateCriticalSubmanifold.exists_linearEquiv_negativeNormalSpace`). Reading this
linear equivalence in the fibre over `s` of the normal bundle gives a closed embedding
`x ↦ (s, L x)` of `ℝ^λ` into the total space which carries the closed ball of radius `√ε` onto
the fibre of `D_ε` over `s`.

When `S` is a point `s₀`, the negative disc bundle is this single fibre. Composing the embedding
with the Morse–Bott normal form `Θ : ν → M`, in which `f (Θ v) = c + ½ Hessₛ (v, v)`, gives a map
`e` from `ℝ^λ` to `M` with `e 0 = i s₀` and `f (e x) = c - ‖x‖²` on the closed ball of radius
`√ε`, injective and continuous there, such that `{f ≤ c + ε}` strong deformation retracts onto
`{f ≤ c - ε} ∪ e(closedBall 0 √ε)`. The formula for `f` places the boundary sphere of the cell on
the level `c - ε` and its interior above it, so this is the attachment of a cell of dimension `λ`
along its boundary sphere.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isClosedEmbedding_image_closedBall_eq_negativeDiscBundle_inter`: each fibre of the
  negative disc bundle of size `ε ≥ 0` is the image of the closed ball of radius `√ε` in a
  Euclidean space whose dimension is the Morse index.
* `exists_sublevel_union_image_closedBall_deformation`: crossing the level of a Morse–Bott
  critical point attaches a cell whose dimension is its Morse index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Bundle Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding

namespace IsNondegenerateCriticalSubmanifold

section Fibre

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S]
  [ChartedSpace H' S] [TopologicalSpace P] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}
  (hn : n ≠ 0)

/-- **The fibres of the negative disc bundle are discs whose dimension is the Morse index.** For a
Morse–Bott submanifold and a point `s`, there is an injective linear map `L` from the Euclidean
space whose dimension is the Morse index at `i s` to the normal space at `s`, along which
`-½ Hessₛ (v, v)` is the squared norm, such that `x ↦ (s, L x)` is a closed embedding into the
normal bundle carrying the closed ball of radius `√ε` onto the fibre over `s` of the negative disc
bundle of size `ε`, for every `ε ≥ 0`. -/
theorem exists_isClosedEmbedding_image_closedBall_eq_negativeDiscBundle_inter [T1Space S]
    [FiberBundle P fun s ↦ i.isImmersion.NormalSpace s hn]
        (h : i.IsNondegenerateCriticalSubmanifold f)
    (g : RiemannianMetric fun s ↦ i.isImmersion.NormalSpace s hn) (s : S) :
    ∃ L : EuclideanSpace ℝ
        (Fin (manifoldMorseIndex I f (i s))) →ₗ[ℝ] i.isImmersion.NormalSpace s hn,
      IsClosedEmbedding (fun x ↦ (⟨s, L x⟩ : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn)) ∧
      (∀ x, -(2⁻¹ * h.normalHessian hn s (L x) (L x)) = ‖x‖ ^ 2) ∧
      ∀ ε, 0 ≤ ε →
        (fun x ↦
            (⟨s, L x⟩ : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn)) '' closedBall 0 √ε =
          h.negativeDiscBundle hn P g ε ∩ π P (fun s ↦ i.isImmersion.NormalSpace s hn) ⁻¹' {s} := by
  obtain ⟨e, he⟩ := h.exists_linearEquiv_negativeNormalSpace hn g s
  refine ⟨(h.negativeNormalSpace hn g s).subtype ∘ₗ e.toLinearMap,
    (FiberBundle.totalSpaceMk_isClosedEmbedding P _ s).comp
      (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2
        (Subtype.val_injective.comp e.injective))), he, fun ε hε ↦ ?_⟩
  set k := TotalSpace.mk' P (E := fun s ↦ i.isImmersion.NormalSpace s hn) s
  -- The fibre over `s` of the negative disc bundle is the image of a set of normal vectors at `s`.
  have hfib : h.negativeDiscBundle hn P g ε ∩ π P (fun s ↦ i.isImmersion.NormalSpace s hn) ⁻¹' {s} =
      k '' {v | v ∈ h.negativeNormalSpace hn g s ∧ -(2⁻¹ * h.normalHessian hn s v v) ≤ ε} := by
    ext ⟨b, v⟩
    constructor
    · rintro ⟨hv, rfl⟩
      exact ⟨v, (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hv, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      cases hwv
      exact ⟨(IsCriticalSubmanifold.mem_negativeDiscBundle hn).2 hw, rfl⟩
  rw [hfib, ← image_image k]
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e x).property, ?_⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, he x]
    exact (Real.le_sqrt (norm_nonneg x) hε).1 (mem_closedBall_zero_iff.1 hx)
  · rintro ⟨hv, hq⟩
    refine ⟨e.symm ⟨v, hv⟩, mem_closedBall_zero_iff.2 ((Real.le_sqrt (norm_nonneg _) hε).2 ?_),
      by simp⟩
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hq

end Fibre

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Crossing the level of a Morse–Bott critical point attaches a cell whose dimension is its
Morse index.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth `f` whose source
is the single point `s₀`, with `f (i s₀) = c` and a smooth fibre metric `g` on its normal bundle.
Then there are a map `e` from the Euclidean space whose dimension is the Morse index at `i s₀` to
`M`, with `e 0 = i s₀`, and an `ε₀ > 0` with the following property. For `0 < ε < ε₀`, if the band
`f⁻¹[c - ε, c + ε]` is compact and its only critical point is `i s₀`, then `e` is continuous and
injective on the closed ball of radius `√ε`, with `f (e x) = c - ‖x‖²` there, and the sublevel
`{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε} ∪ e(closedBall 0 √ε)`. -/
theorem exists_sublevel_union_image_closedBall_deformation [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Subsingleton S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (s₀ : S) {c : ℝ}
    (hc : f (i s₀) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.isImmersion.NormalSpace s hn) :
    ∃ e : EuclideanSpace ℝ (Fin (manifoldMorseIndex I f (i s₀))) → M, e 0 = i s₀ ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ {i s₀} →
        ContinuousOn e (closedBall 0 √ε) ∧ InjOn e (closedBall 0 √ε) ∧
        (∀ x ∈ closedBall 0 √ε, f (e x) = c - ‖x‖ ^ 2) ∧
        ∃ r : C({y | f y ≤ c + ε},
            ↥({y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪ e '' closedBall 0 √ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈ {y | f y ≤ c - ε} ∪ e '' closedBall 0 √ε}) := by
  have : Nonempty S := ⟨s₀⟩
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨Θ, -, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs
      (fun s ↦ by rw [Subsingleton.elim s s₀, hc]) hdim g
  obtain ⟨L, hL, hLq, hLD⟩ :=
    h.exists_isClosedEmbedding_image_closedBall_eq_negativeDiscBundle_inter hn (P := P)
      g.toRiemannianMetric s₀
  -- Over a point the negative disc bundle is its fibre over `s₀`.
  set φ := fun x ↦ (⟨s₀, L x⟩ : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn)
  have hD (ε : ℝ) (hε : 0 ≤ ε) :
      φ '' closedBall 0 √ε = h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
    rw [hLD ε hε, inter_eq_left]
    exact fun x _ ↦ Subsingleton.elim x.proj s₀
  refine ⟨fun x ↦ Θ (φ x), ?_, ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  · have h0 : φ 0 = zeroSection P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀ := by
      simp [φ, zeroSection]
    exact (congrArg Θ h0).trans (hΘi s₀)
  obtain ⟨hsource, hdef⟩ := hmain ε hε hcomp (hcrit.trans (singleton_subset_iff.2 ⟨s₀, rfl⟩))
  have hmaps : MapsTo φ (closedBall 0 √ε) Θ.source :=
    fun x hx ↦ hsource (hD ε hε.1.le ▸ mem_image_of_mem _ hx)
  refine ⟨Θ.contMDiffOn.continuousOn.comp hL.continuous.continuousOn hmaps,
    Θ.toPartialEquiv.injOn.comp hL.injective.injOn hmaps, fun x hx ↦ ?_, ?_⟩
  · rw [hΘf _ (hmaps hx)]
    linarith [hLq x]
  · rw [← image_image Θ, hD ε hε.1.le]
    exact hdef

end Attachment

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

end TauCeti
