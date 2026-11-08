/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Attachment
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Sphere
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Topology.Category.TopCat.ClosedCover

/-!
# Handle attachment across a critical level as a pushout

Let `f` be a smooth function on a boundaryless manifold `M` of dimension `n`, and let `c` be a
value at which `f` has finitely many critical points, all nondegenerate, with a compact band
`f⁻¹[c - ε, c + ε]`. Milnor's handle attachment theorem
(`TauCeti.exists_diffeomorph_sublevel_eq_union_handles`) gives a diffeomorphism `Φ` of `M`
carrying the upper sublevel `M_{c+ε} = {f ≤ c + ε}` onto the lower sublevel
`M_{c-ε} = {f ≤ c - ε}` together with one handle `H_p ≅ D^λ × D^(n-λ)` at each critical point `p`
of index `λ`, meeting `M_{c-ε}` exactly in its attaching region `∂D^λ × D^(n-λ)`.

This file identifies `M_{c+ε}` with the topological handle adjunction

`M_{c-ε} ∪_α ⨆ₚ (D^λ × D^(n-λ))`,

the pushout in `TopCat` of the attaching maps `α_p : ∂D^λ × D^(n-λ) → M_{c-ε}` along the
inclusions `∂D^λ × D^(n-λ) ⟶ D^λ × D^(n-λ)`, where `D^m` is Mathlib's closed unit disc
`TopCat.disk m`. The legs of the pushout square are `x ↦ Φ⁻¹(x)` on the lower sublevel and the
characteristic maps `χ_p : D^λ × D^(n-λ) → M_{c+ε}` of the handles. The identification respects
the boundary level `f⁻¹(c + ε)`: it consists of the tops `D^λ × ∂D^(n-λ)` of the handles and of the
points of the level `f⁻¹(c - ε)` away from the attaching regions. The core `D^λ × 0` of the handle
at `p` is the disc of the negative coordinates of its Morse chart.

The pushout property is an instance of the recognition of adjunction spaces from finite closed
covers (`TauCeti.TopCat.isPushout_sigmaDesc_of_isClosedEmbedding`): `M_{c+ε}` is covered by the
closed image of the lower sublevel and by the compact, pairwise disjoint handles.

## Main results

* `TauCeti.exists_isPushout_sublevel_handles`: for normal-form charts with disjoint sources around
  the critical points of a compact band `f⁻¹[c - ε, c + ε]`, the sublevel `M_{c+ε}` is the handle
  adjunction of `M_{c-ε}`.
* `TauCeti.IsMorse.exists_isPushout_sublevel_handles`: **Milnor's handle attachment theorem** in
  pushout form, for a Morse function with a compact band around a critical value, with the charts
  and the width supplied by `TauCeti.IsMorse.exists_admissible_morseCharts`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory Limits
open scoped ContDiff Manifold

universe u

namespace TauCeti

section HandleAdjunction

variable {n k : ℕ}

/-- The product of the closed unit balls of the first `k` and of the remaining coordinates of
`ℝⁿ` is homeomorphic to `D^k × D^(n-k)`, by linear isometries reindexing the coordinates. -/
private def handleDiskHomeomorph (hk : k ≤ n) :
    closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) 1 ×
        closedBall (0 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) 1 ≃ₜ
      TopCat.disk.{u} k × TopCat.disk.{u} (n - k) :=
  Homeomorph.prodCongr
    (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fin.castLEquiv hk).symm).toHomeomorph.subtype
      fun x ↦ by simp).trans Homeomorph.ulift.symm)
    (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_fin,
        ← Fintype.card_congr (Fin.castLEquiv hk), Fintype.card_fin]))).toHomeomorph.subtype
        fun x ↦ by simp).trans Homeomorph.ulift.symm)

private theorem norm_fst_handleDiskHomeomorph (hk : k ≤ n)
    (z : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) 1 ×
      closedBall (0 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) 1) :
    ‖(((handleDiskHomeomorph.{u} hk z).1 :
      ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).down : EuclideanSpace ℝ (Fin k))‖ =
      ‖(z.1 : EuclideanSpace ℝ {j : Fin n // j.val < k})‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ _).norm_map _

private theorem norm_snd_handleDiskHomeomorph (hk : k ≤ n)
    (z : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) 1 ×
      closedBall (0 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) 1) :
    ‖(((handleDiskHomeomorph.{u} hk z).2 :
      ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k))) 1)).down :
        EuclideanSpace ℝ (Fin (n - k)))‖ =
      ‖(z.2 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k})‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ _).norm_map _

variable {M : Type u} [TopologicalSpace M] [T2Space M] {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- A space covered by the closed lower sublevel and by finitely many disjoint handles, each meeting
the lower sublevel in its attaching region `∂D^λ × D^(n-λ)`, is the handle adjunction: the pushout
of the lower sublevel and the handles along the attaching regions. -/
private theorem exists_isPushout_of_handles [Finite ι] (hfc : Continuous f) (k : ι → ℕ)
    (hk : ∀ i, k i ≤ n) (H : ι → Set M) (hH : Pairwise (Disjoint on H))
    (e : ∀ i, H i ≃ₜ closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) 1 ×
      closedBall (0 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k i}) 1) (Φ : M ≃ₜ M)
    (he : ∀ i (x : H i),
      f x ≤ c - ε ↔ ‖((e i x).1 : EuclideanSpace ℝ {j : Fin n // j.val < k i})‖ = 1)
    (hΦ : ∀ x, Φ x ∈ {x | f x ≤ c - ε} ∪ ⋃ i, H i ↔ f x ≤ c + ε) :
    ∃ (g : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε})
      (α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c - ε})
      (χ : ∀ i, TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c + ε}),
      IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
          ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id _)))
        g (Sigma.desc χ) ∧
      (∀ x, (g x : M) = Φ.symm x) ∧
      (∀ i (x : {x | f x ≤ c - ε}), (x : M) ∈ H i → x ∈ range (α i)) ∧
      ∀ i w, ∃ h : Φ (χ i w) ∈ H i, handleDiskHomeomorph (hk i) (e i ⟨_, h⟩) = w := by
  -- The handles, parametrized by `D^λ × D^(n-λ)`.
  set E : ∀ i, H i ≃ₜ TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i) :=
    fun i ↦ (e i).trans (handleDiskHomeomorph (hk i))
  have hE (i : ι) (x : H i) :
      ‖(((E i x).1 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1)).down :
        EuclideanSpace ℝ (Fin (k i)))‖ =
        ‖((e i x).1 : EuclideanSpace ℝ {j : Fin n // j.val < k i})‖ :=
    norm_fst_handleDiskHomeomorph _ _
  have hL (y : M) (hy : f y ≤ c - ε) : f (Φ.symm y) ≤ c + ε :=
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact Or.inl hy)
  have hH' (i : ι) (y : H i) : f (Φ.symm y) ≤ c + ε :=
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact Or.inr (mem_iUnion.2 ⟨i, y.2⟩))
  -- The attaching region `∂D^λ × D^(n-λ)` of a handle lies in the lower sublevel.
  have hα (i : ι) (s : TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) :
      f ((E i).symm (TopCat.diskBoundaryInclusion _ s.1, s.2)) ≤ c - ε := by
    rw [he, ← hE i, Homeomorph.apply_symm_apply, TopCat.coe_diskBoundaryInclusion_apply_down]
    exact mem_sphere_zero_iff_norm.1
      (s.1 : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (k i))) 1)).down.2
  let g : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε} :=
    TopCat.ofHom ⟨fun x ↦ ⟨Φ.symm x, hL x x.2⟩,
      (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let α (i : ι) : TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
      TopCat.of {x | f x ≤ c - ε} :=
    TopCat.ofHom ⟨fun s ↦ ⟨(E i).symm (TopCat.diskBoundaryInclusion _ s.1, s.2), hα i s⟩,
      (continuous_subtype_val.comp ((E i).symm.continuous.comp
        ((TopCat.diskBoundaryInclusion _).hom.continuous.prodMap continuous_id))).subtype_mk _⟩
  let χ (i : ι) : TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
      TopCat.of {x | f x ≤ c + ε} :=
    TopCat.ofHom ⟨fun w ↦ ⟨Φ.symm ((E i).symm w), hH' i _⟩,
      ((Φ.symm.continuous.comp continuous_subtype_val).comp (E i).symm.continuous).subtype_mk _⟩
  have hsub : IsClosed {x | f x ≤ c + ε} := isClosed_le hfc continuous_const
  refine ⟨g, α, χ, TopCat.isPushout_sigmaDesc_of_isClosedEmbedding (fun i ↦ rfl) ?_
    (fun i ↦ (χ i).hom.continuous.isClosedEmbedding fun w w' h ↦
      (E i).symm.injective (Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)))) ?_ ?_ ?_,
    fun x ↦ rfl, fun i x hx ↦ ?_, fun i w ↦ ?_⟩
  · -- The lower sublevel is closed, and `Φ⁻¹` is a homeomorphism.
    rw [← hsub.isClosedEmbedding_subtypeVal.of_comp_iff]
    exact Φ.symm.isClosedEmbedding.comp
      (isClosed_le hfc continuous_const).isClosedEmbedding_subtypeVal
  · -- The handles are pairwise disjoint.
    rintro i i' hii'
    refine Set.disjoint_left.2 ?_
    rintro y ⟨w, rfl⟩ ⟨w', hw'⟩
    exact (hH hii').ne_of_mem ((E i).symm w).2 ((E i').symm w').2
      (Φ.symm.injective (congrArg Subtype.val hw')).symm
  · -- A point of a handle in the lower sublevel lies in the attaching region.
    rintro i d ⟨x, hx⟩
    have hxd : (x : M) = (E i).symm d := Φ.symm.injective (congrArg Subtype.val hx)
    have hd := (he i ((E i).symm d)).1 (hxd ▸ x.2)
    rw [← hE i, Homeomorph.apply_symm_apply,
      ← mem_range_diskBoundaryInclusion_iff] at hd
    obtain ⟨s, hs⟩ := hd
    exact ⟨(s, d.2), Prod.ext hs rfl⟩
  · -- The lower sublevel and the handles cover the upper sublevel.
    refine eq_univ_of_forall fun y ↦ ?_
    obtain hy | hy := (hΦ y).2 y.2
    · exact Or.inl ⟨⟨Φ y, hy⟩, Subtype.ext (Φ.symm_apply_apply y)⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      exact Or.inr (mem_iUnion.2 ⟨i, E i ⟨Φ y, hi⟩,
        Subtype.ext (by simp [χ])⟩)
  · -- A point of the lower sublevel in a handle is the image of a point of its attaching region.
    have hd := (he i ⟨x, hx⟩).1 x.2
    rw [← hE i, ← mem_range_diskBoundaryInclusion_iff] at hd
    obtain ⟨s, hs⟩ := hd
    exact ⟨(s, (E i ⟨x, hx⟩).2), Subtype.ext (by simp [α, hs])⟩
  · -- The characteristic map of a handle is the inverse of its parametrization, read through `Φ`.
    have h : Φ (χ i w) = (E i).symm w := Φ.apply_symm_apply _
    refine ⟨h ▸ ((E i).symm w).2, ?_⟩
    have : (⟨Φ (χ i w), h ▸ ((E i).symm w).2⟩ : H i) = (E i).symm w := Subtype.ext h
    rw [this]
    exact (E i).apply_symm_apply w

end HandleAdjunction

section Manifold

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {n : ℕ}
  {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- The conclusion of Milnor's handle attachment theorem
(`TauCeti.exists_diffeomorph_sublevel_eq_union_handles`), recast as a pushout. -/
private theorem exists_isPushout_of_diffeomorph_sublevel_eq_union_handles [Finite ι]
    (hfc : Continuous f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (H : ι → Set M)
    (e : ∀ i, H i ≃ₜ closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) 1 ×
      closedBall (0 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k i}) 1) (Φ : M ≃ₘ⟮I, I⟯ M)
    (hHψ : ∀ i, H i ⊆ (ψ i).source)
    (he₁ : ∀ i (x : H i),
      f x ≤ c - ε ↔ ‖((e i x).1 : EuclideanSpace ℝ {j : Fin n // j.val < k i})‖ = 1)
    (he₂ : ∀ i (x : H i), ((e i x).2 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k i}) = 0 ↔
      ∀ j : Fin n, k i ≤ j.val → ψ i x j = 0)
    (hΦ : ∀ x, Φ x ∈ {x | f x ≤ c - ε} ∪ ⋃ i, H i ↔ f x ≤ c + ε)
    (hlevel : ∀ x, f x = c + ε ↔
      (∀ i (h : Φ x ∈ H i),
        ‖((e i ⟨Φ x, h⟩).2 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k i})‖ = 1) ∧
      (Φ x ∉ ⋃ i, H i → f (Φ x) = c - ε)) :
    ∃ (g : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε})
      (α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c - ε})
      (χ : ∀ i, TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c + ε}),
      IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
          ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id _)))
        g (Sigma.desc χ) ∧
      (∀ x, (g x : M) = Φ.symm x) ∧
      (∀ i w, Φ (χ i w) ∈ (ψ i).source) ∧
      (∀ i w, ((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i))) = 0 ↔
        ∀ j : Fin n, k i ≤ j.val → ψ i (Φ (χ i w)) j = 0) ∧
      (∀ i w, f (χ i w) = c + ε ↔
        ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i)))‖ = 1) ∧
      ∀ x, x ∉ ⋃ i, range (α i) → (f (g x) = c + ε ↔ f x = c - ε) := by
  have hH : Pairwise (Disjoint on H) := fun i i' hii' ↦ (hψ hii').mono (hHψ i) (hHψ i')
  obtain ⟨g, α, χ, hpush, hg, hα, hχ⟩ :=
    exists_isPushout_of_handles hfc k hk H hH e Φ.toHomeomorph he₁ hΦ
  -- On the handle of `ψ i`, the second factor of `D^λ × D^(n-λ)` has the norm of the
  -- coordinates of `e i` beyond the first `k i`.
  have hn (i : ι) (w) : ∃ h : Φ.toHomeomorph (χ i w) ∈ H i,
      ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
        EuclideanSpace ℝ (Fin (n - k i)))‖ =
        ‖((e i ⟨_, h⟩).2 : EuclideanSpace ℝ {j : Fin n // ¬j.val < k i})‖ := by
    obtain ⟨h, hw⟩ := hχ i w
    exact ⟨h, by rw [← norm_snd_handleDiskHomeomorph (hk i), hw]⟩
  refine ⟨g, α, χ, hpush, hg, fun i w ↦ hHψ i (hχ i w).1, fun i w ↦ ?_, fun i w ↦ ?_,
    fun x hx ↦ ?_⟩
  · obtain ⟨h, hn⟩ := hn i w
    rw [← norm_eq_zero, hn, norm_eq_zero]
    exact he₂ i ⟨_, h⟩
  · obtain ⟨h, hn⟩ := hn i w
    rw [hn, hlevel]
    -- The handle containing `Φ (χ i w)` is the `i`-th one, as the handles are disjoint.
    refine ⟨fun h' ↦ h'.1 i h, fun h' ↦ ⟨fun i' hi' ↦ ?_, fun hn ↦ absurd (mem_iUnion.2 ⟨i, h⟩) hn⟩⟩
    obtain rfl : i = i' := by_contra fun hii' ↦ Set.disjoint_left.1 (hH hii') h hi'
    exact h'
  · -- A point of the lower sublevel away from the attaching regions lies in no handle.
    have hgx : Φ (g x) = x := by rw [hg, Φ.coe_toHomeomorph_symm, Φ.apply_symm_apply]
    have hxH : (x : M) ∉ ⋃ i, H i := fun hxH ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hxH
      exact hx (mem_iUnion.2 ⟨i, hα i x hi⟩)
    rw [hlevel, hgx]
    exact ⟨fun h ↦ h.2 hxH, fun h ↦ ⟨fun i hi ↦ absurd (mem_iUnion.2 ⟨i, hi⟩) hxH, fun _ ↦ h⟩⟩

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]

/-- **Handle attachment in disjoint Morse charts, as a pushout** (Milnor, Remark 3.3). Let `f` be
smooth, and let `ψ i` be charts of `M` with pairwise disjoint sources, each containing the closed
ball of radius `√(2ε)` about `0` in its target, in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`
with `k i ≤ n`. Suppose the band `f⁻¹[c - ε, c + ε]` is compact and its critical points lie in the
chart sources.

Then there are a diffeomorphism `Φ` of `M`, attaching maps `α i : ∂D^{k i} × D^{n - k i} → M_{c-ε}`
and characteristic maps `χ i : D^{k i} × D^{n - k i} → M_{c+ε}` such that `M_{c+ε}` is the pushout
of `M_{c-ε}` and `⨆ᵢ D^{k i} × D^{n - k i}` along the `α i` and the inclusions of
`∂D^{k i} × D^{n - k i}`, with legs `g : x ↦ Φ⁻¹(x)` on `M_{c-ε}` and the `χ i`. Moreover:
* the handle `χ i` lies in the chart `ψ i` after `Φ`, and its core `D^{k i} × 0` is the set where
  the coordinates of `ψ i ∘ Φ` beyond the first `k i` vanish;
* the level `f⁻¹(c + ε)` meets the handle `χ i` in its top `D^{k i} × ∂D^{n - k i}`, and meets the
  image of `g` away from the attaching regions in the image of the level `f⁻¹(c - ε)`. -/
theorem exists_isPushout_sublevel_handles [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
    (hf : ∀ i, ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source) :
    ∃ (Φ : M ≃ₘ⟮I, I⟯ M) (g : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε})
      (α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c - ε})
      (χ : ∀ i, TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c + ε}),
      IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
          ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id _)))
        g (Sigma.desc χ) ∧
      (∀ x, (g x : M) = Φ.symm x) ∧
      (∀ i w, Φ (χ i w) ∈ (ψ i).source) ∧
      (∀ i w, ((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i))) = 0 ↔
        ∀ j : Fin n, k i ≤ j.val → ψ i (Φ (χ i w)) j = 0) ∧
      (∀ i w, f (χ i w) = c + ε ↔
        ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i)))‖ = 1) ∧
      ∀ x, x ∉ ⋃ i, range (α i) → (f (g x) = c + ε ↔ f x = c - ε) := by
  obtain ⟨H, e, Φ, hHψ, he₁, he₂, hΦ, hlevel⟩ :=
    exists_diffeomorph_sublevel_eq_union_handles hfs ψ hψ k hε hball hf hcompact hcrit
  exact ⟨Φ, exists_isPushout_of_diffeomorph_sublevel_eq_union_handles hfs.continuous ψ hψ k hk H e
    Φ hHψ he₁ he₂ hΦ hlevel⟩

/-- **Milnor's handle attachment theorem, as a pushout** (Milnor, Remark 3.3). Let `f` be a Morse
function on a Hausdorff manifold of dimension `m` whose band `f⁻¹[c - δ, c + δ]` is compact, for
some `0 < δ`. Then there are a width `0 < ε ≤ δ` and normalized Morse charts `ψ p` with pairwise
disjoint sources, indexed by the critical points `p` on the level `f⁻¹(c)`, with `ψ p p = 0`, with
the closed ball of radius `√(2ε)` in the target of `ψ p`, and in which
`f = c - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`, where `λ` is the Morse index of `f` at `p`.

The upper sublevel `{f ≤ c + ε}` is the handle adjunction of the lower sublevel `{f ≤ c - ε}`: the
pushout in `TopCat` obtained by attaching one handle `D^λ × D^(m-λ)` at each critical point `p`
along `∂D^λ × D^(m-λ)`, with the further properties of
`TauCeti.exists_isPushout_sublevel_handles` for these charts. -/
theorem IsMorse.exists_isPushout_sublevel_handles (hf : IsMorse I f) {δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧
        (∀ p, ↑p ∈ (ψ p).source ∧ ψ p p = 0 ∧ closedBall 0 √(2 * ε) ⊆ (ψ p).target ∧
          ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2) ∧
        ∃ (Φ : M ≃ₘ⟮I, I⟯ M) (g : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε})
          (α : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
            TopCat.of (TopCat.diskBoundary.{u} (manifoldMorseIndex I f p) ×
              TopCat.disk.{u} (Module.finrank ℝ E - manifoldMorseIndex I f p)) ⟶
            TopCat.of {x | f x ≤ c - ε})
          (χ : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
            TopCat.of (TopCat.disk.{u} (manifoldMorseIndex I f p) ×
              TopCat.disk.{u} (Module.finrank ℝ E - manifoldMorseIndex I f p)) ⟶
            TopCat.of {x | f x ≤ c + ε}),
          IsPushout (Sigma.desc α) (Limits.Sigma.map fun p ↦ TopCat.ofHom
              ((TopCat.diskBoundaryInclusion.{u} (manifoldMorseIndex I f p)).hom.prodMap
                (ContinuousMap.id _)))
            g (Sigma.desc χ) ∧
          (∀ x, (g x : M) = Φ.symm x) ∧
          (∀ p w, Φ (χ p w) ∈ (ψ p).source) ∧
          (∀ (p : ↥(criticalPoints I f ∩ f ⁻¹' {c})) w,
            ((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p))) 1)).down :
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p))) = 0 ↔
            ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I f p ≤ i.val →
              ψ p (Φ (χ p w)) i = 0) ∧
          (∀ (p : ↥(criticalPoints I f ∩ f ⁻¹' {c})) w, f (χ p w) = c + ε ↔
            ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p))) 1)).down :
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p)))‖ = 1) ∧
          ∀ x, x ∉ ⋃ p, range (α p) → (f (g x) = c + ε ↔ f x = c - ε) := by
  obtain ⟨ε, hε, hεδ, ψ, hψ, hψp, H, e, Φ, hHψ, he₁, he₂, hΦ, hlevel⟩ :=
    hf.exists_diffeomorph_sublevel_eq_union_handles hδ hcompact
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  exact ⟨ε, hε, hεδ, ψ, hψ, hψp, Φ,
    exists_isPushout_of_diffeomorph_sublevel_eq_union_handles hf.contMDiff.continuous ψ hψ _
      (fun _ ↦ manifoldMorseIndex_le_finrank) H e Φ hHψ he₁ he₂ hΦ hlevel⟩

end Manifold

end TauCeti
