/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Manifold.Morse.Cell.Attachment
public import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.AlgebraicTopology.Disk

/-!
# Handle attachment across a critical level as a pushout

Let `f` be a smooth function on a boundaryless manifold of dimension `n`, and let `c` be a value
whose band `f⁻¹[c - ε, c + ε]` is compact and whose critical points in that band are the centres
of normal-form charts `ψ i` of index `k i`. Milnor's handle attachment theorem
(`TauCeti.exists_diffeomorph_sublevel_eq_union_handles`) carries the upper sublevel
`M_{c+ε} = {f ≤ c + ε}` by a diffeomorphism of `M` onto the lower sublevel `M_{c-ε}` together with
one handle in each chart, meeting `M_{c-ε}` in its attaching region.

This file repackages that union as the topological handle adjunction. With the closed unit discs
`𝔻 m = TopCat.disk m` and their boundary spheres `∂𝔻 m`, the square

```
∐ᵢ ∂𝔻 (k i) × 𝔻 (n - k i) ──α──> M_{c-ε}
          │                          │
          ↓                          ↓
∐ᵢ 𝔻 (k i) × 𝔻 (n - k i)  ──χ──> M_{c+ε}
```

is a pushout in `TopCat`, so `M_{c+ε}` is homeomorphic to `M_{c-ε} ∪_α ⨆ᵢ 𝔻 (k i) × 𝔻 (n - k i)`.
The attaching maps `α i` are closed embeddings with pairwise disjoint images in the level
`f⁻¹(c - ε)`. The square also respects the regular boundary `f⁻¹(c + ε)` of `M_{c+ε}`: it consists
of the tops `𝔻 (k i) × ∂𝔻 (n - k i)` of the handles and of the points of `f⁻¹(c - ε)` off the
attaching regions.

The pushout property comes from the closed cover of `M_{c-ε} ∪ ⋃ᵢ Hᵢ` by the lower sublevel and
the compact handles `Hᵢ` (`CategoryTheory.IsPushout.of_isClosedEmbedding`). Each handle is a
product of closed balls in the coordinates `{j | j < k i}` and `{j | k i ≤ j}` of its chart; these
are reindexed to the standard discs by relabelling the coordinates
(`LinearIsometryEquiv.closedBallHomeomorphDisk`).

## Main results

* `TauCeti.exists_isPushout_sublevel_handles`: for normal-form charts with disjoint sources around
  the critical points of a compact band `f⁻¹[c - ε, c + ε]`, the upper sublevel is the lower one
  with the handles `𝔻 (k i) × 𝔻 (n - k i)` attached, as a pushout in `TopCat`.
* `TauCeti.IsMorse.exists_isPushout_sublevel_handles`: **Milnor's handle attachment theorem** in
  pushout form, for a Morse function with a compact band around a critical value, with one handle
  of index `λ` at each critical point of index `λ` on the level.

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

section HandlePushout

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type u} {n : ℕ} {f : M → ℝ} {c ε : ℝ}

/-- The pushout form of a handle attachment, from the handles `H i` with their homeomorphisms
`e i` to `𝔻 (k i) × 𝔻 (n - k i)` and a homeomorphism `Φ` of `M` carrying `{f ≤ c + ε}` onto
`{f ≤ c - ε} ∪ ⋃ᵢ H i`. -/
private theorem isPushout_of_handles [Finite ι] [T2Space M] (hfc : Continuous f) (k : ι → ℕ)
    (Φ : M ≃ₜ M) (H : ι → Set M)
    (e : ∀ i, H i ≃ₜ TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i))
    (hH : Pairwise (Disjoint on H)) (hge : ∀ i (x : H i), c - ε ≤ f x)
    (he : ∀ i (x : H i), f x ≤ c - ε ↔
      ‖(((e i x).1 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1)).down :
        EuclideanSpace ℝ (Fin (k i)))‖ = 1)
    (hΦ : ∀ x, Φ x ∈ {x | f x ≤ c - ε} ∪ ⋃ i, H i ↔ f x ≤ c + ε)
    (hΦtop : ∀ x, f x = c + ε ↔
      (∀ i (h : Φ x ∈ H i),
        ‖(((e i ⟨Φ x, h⟩).2 :
          ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
            EuclideanSpace ℝ (Fin (n - k i)))‖ = 1) ∧
      (Φ x ∉ ⋃ i, H i → f (Φ x) = c - ε)) :
    ∃ (α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c - ε})
      (χ : ∀ i, TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c + ε})
      (j : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε}),
      IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
          ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _)))
        j (Sigma.desc χ) ∧
      (∀ i, IsClosedEmbedding (α i)) ∧ Pairwise (Disjoint on fun i ↦ range (α i)) ∧
      (∀ i s, f (α i s : M) = c - ε) ∧
      (∀ i w, f (χ i w : M) = c + ε ↔
        ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i)))‖ = 1) ∧
      ∀ x, (∀ i, x ∉ range (α i)) → (f (j x : M) = c + ε ↔ f (x : M) = c - ε) := by
  -- The proof builds the three maps of the square from `e` and `Φ`, checks the hypotheses of
  -- `CategoryTheory.IsPushout.of_isClosedEmbedding` for the closed cover of `{f ≤ c + ε}` by
  -- `Φ⁻¹ {f ≤ c - ε}` and the compact handles `Φ⁻¹ (H i)`, and then reads off the levels.
  -- The attaching region of the handle `H i` is the image of `∂𝔻 (k i) × 𝔻 (n - k i)`.
  have hbd (i : ι) (s : TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) :
      f ((e i).symm (TopCat.diskBoundaryInclusion (k i) s.1, s.2) : M) ≤ c - ε := by
    rw [he, Homeomorph.apply_symm_apply, TopCat.coe_diskBoundaryInclusion_apply_down]
    exact mem_sphere_zero_iff_norm.1 s.1.down.2
  have hmem (i : ι) (x : H i) (hx : f x ≤ c - ε) :
      ∃ s : TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i),
        (TopCat.diskBoundaryInclusion (k i) s.1, s.2) = e i x := by
    obtain ⟨s, hs⟩ := (mem_range_diskBoundaryInclusion_iff (e i x).1).2 ((he i x).1 hx)
    exact ⟨(s, (e i x).2), Prod.ext hs rfl⟩
  have hup (y : M) (hy : y ∈ {x | f x ≤ c - ε} ∪ ⋃ i, H i) : f (Φ.symm y) ≤ c + ε :=
    (hΦ _).1 (by rwa [Homeomorph.apply_symm_apply])
  let α (i : ι) : TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
      TopCat.of {x | f x ≤ c - ε} :=
    TopCat.ofHom ⟨fun s ↦ ⟨(e i).symm (TopCat.diskBoundaryInclusion (k i) s.1, s.2), hbd i s⟩,
      (continuous_subtype_val.comp ((e i).symm.continuous.comp
        ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.prodMap continuous_id))).subtype_mk _⟩
  let χ (i : ι) : TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
      TopCat.of {x | f x ≤ c + ε} :=
    TopCat.ofHom ⟨fun w ↦ ⟨Φ.symm ((e i).symm w),
        hup _ (Or.inr (mem_iUnion.2 ⟨i, ((e i).symm w).2⟩))⟩,
      (Φ.symm.continuous.comp (continuous_subtype_val.comp (e i).symm.continuous)).subtype_mk _⟩
  let j : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε} :=
    TopCat.ofHom ⟨fun x ↦ ⟨Φ.symm x, hup _ (Or.inl x.2)⟩,
      (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hα (i : ι) (s) : (α i s : M) = (e i).symm (TopCat.diskBoundaryInclusion (k i) s.1, s.2) :=
    rfl
  have hχ (i : ι) (w) : (χ i w : M) = Φ.symm ((e i).symm w) := rfl
  have hj (x) : (j x : M) = Φ.symm x := rfl
  -- A point of the lower sublevel lying in a handle is in the image of its attaching map.
  have hrange (i : ι) (x : H i) (hx : f x ≤ c - ε) : ∃ s, (α i s : M) = x := by
    obtain ⟨s, hs⟩ := hmem i x hx
    exact ⟨s, by rw [hα, hs, Homeomorph.symm_apply_apply]⟩
  -- The square commutes by construction: both ways round send `s` to `Φ⁻¹ (e i⁻¹ (s.1, s.2))`.
  refine ⟨α, χ, j, IsPushout.of_isClosedEmbedding (fun i ↦ rfl) ?_ (fun i ↦ ?_) ?_ ?_ ?_,
    fun i ↦ ?_, fun i l hil ↦ ?_, fun i s ↦ ?_, fun i w ↦ ?_, fun x hx ↦ ?_⟩
  · -- The lower sublevel is closed, and `Φ⁻¹` carries it homeomorphically into `{f ≤ c + ε}`.
    have hcl (a : ℝ) : IsClosed {x | f x ≤ a} := isClosed_le hfc continuous_const
    rw [← (hcl (c + ε)).isClosedEmbedding_subtypeVal.of_comp_iff]
    exact Φ.symm.isClosedEmbedding.comp (hcl (c - ε)).isClosedEmbedding_subtypeVal
  · -- Each handle map is injective on a compact space.
    refine (χ i).hom.continuous.isClosedEmbedding fun w w' h ↦ (e i).symm.injective ?_
    exact Subtype.ext (Φ.symm.injective (congrArg Subtype.val h))
  · -- `Φ` carries every point of `{f ≤ c + ε}` into the lower sublevel or into a handle.
    refine eq_univ_of_forall fun y ↦ ?_
    obtain hy | hy := (hΦ y).2 y.2
    · exact Or.inl ⟨⟨Φ y, hy⟩, Subtype.ext (Φ.symm_apply_apply y)⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      refine Or.inr (mem_iUnion.2 ⟨i, e i ⟨Φ y, hi⟩, Subtype.ext ?_⟩)
      rw [hχ, Homeomorph.symm_apply_apply, Φ.symm_apply_apply]
  · -- Distinct handles are disjoint.
    rintro i l hil y ⟨⟨w, rfl⟩, ⟨w', hw'⟩⟩
    have h : ((e i).symm w : M) = (e l).symm w' :=
      Φ.symm.injective ((congrArg Subtype.val hw').symm)
    exact absurd h ((hH hil).ne_of_mem ((e i).symm w).2 ((e l).symm w').2)
  · -- A handle meets the lower sublevel in its attaching region.
    intro i a b hab
    have h : (a : M) = (e i).symm b := Φ.symm.injective (congrArg Subtype.val hab)
    obtain ⟨s, hs⟩ := hmem i ((e i).symm b) (h ▸ a.2)
    rw [Homeomorph.apply_symm_apply] at hs
    exact ⟨s, Subtype.ext (by rw [hα, hs, h]), hs⟩
  · -- The attaching maps are injective on compact spaces, with disjoint images.
    refine (α i).hom.continuous.isClosedEmbedding fun s s' h ↦ ?_
    have h₀ := congrArg Subtype.val h
    rw [hα, hα] at h₀
    obtain ⟨s₁, s₂⟩ := s
    obtain ⟨s₁', s₂'⟩ := s'
    have h' := (e i).symm.injective (Subtype.ext h₀)
    simp only [Prod.mk.injEq] at h' ⊢
    exact ⟨(TopCat.isClosedEmbedding_diskBoundaryInclusion (k i)).injective h'.1, h'.2⟩
  · rw [Function.onFun, disjoint_iff_forall_ne]
    rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ h
    exact (hH hil).ne_of_mem ((e i).symm _).2 ((e l).symm _).2 (congrArg Subtype.val h)
  · -- The attaching regions lie in the level `f⁻¹(c - ε)`.
    exact le_antisymm (α i s).2 (hge i _)
  · -- `Φ` carries this point into the handle `H i` only, at the point `w` of the handle.
    have hw : Φ (χ i w) ∈ H i := by rw [hχ, Φ.apply_symm_apply]; exact ((e i).symm w).2
    have hwi (hw : Φ (χ i w) ∈ H i) : (⟨Φ (χ i w), hw⟩ : H i) = (e i).symm w :=
      Subtype.ext ((congrArg Φ (hχ i w)).trans (Φ.apply_symm_apply _))
    rw [hΦtop]
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun l hl ↦ ?_, fun h' ↦ absurd (mem_iUnion.2 ⟨i, hw⟩) h'⟩⟩
    · have := h.1 i hw
      rwa [hwi hw, Homeomorph.apply_symm_apply] at this
    · obtain rfl : i = l := by
        by_contra hil
        exact (hH hil).ne_of_mem hw hl rfl
      rwa [hwi hl, Homeomorph.apply_symm_apply]
  · -- Off the attaching regions, a point of the lower sublevel lies in no handle.
    have hH' : (x : M) ∉ ⋃ i, H i := by
      rw [mem_iUnion]
      rintro ⟨i, hi⟩
      obtain ⟨s, hs⟩ := hrange i ⟨x, hi⟩ x.2
      exact hx i ⟨s, Subtype.ext hs⟩
    have hΦx : Φ (j x) = x := by rw [hj, Φ.apply_symm_apply]
    rw [hΦtop, hΦx]
    exact ⟨fun h ↦ h.2 hH', fun h ↦ ⟨fun i hi ↦ absurd (mem_iUnion.2 ⟨i, hi⟩) hH', fun _ ↦ h⟩⟩

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Handle attachment in disjoint Morse charts, as a pushout** (Milnor, Remark 3.3). Let `f` be
smooth, and let `ψ i` be charts of `M` with pairwise disjoint sources, each containing the closed
ball of radius `√(2ε)` about `0` in its target, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` with `k i ≤ n`. Suppose the band `f⁻¹[c - ε, c + ε]`
is compact and its critical points lie in the chart sources. Write `M_a = {f ≤ a}`.

Then `M_{c+ε}` is obtained from `M_{c-ε}` by attaching one handle `𝔻 (k i) × 𝔻 (n - k i)` for each
chart: there are attaching maps `α i : ∂𝔻 (k i) × 𝔻 (n - k i) → M_{c-ε}`, maps
`χ i : 𝔻 (k i) × 𝔻 (n - k i) → M_{c+ε}` and `j : M_{c-ε} → M_{c+ε}` forming a pushout square in
`TopCat`. The attaching maps are closed embeddings with pairwise disjoint images in the level
`f⁻¹(c - ε)`. The level `f⁻¹(c + ε)` consists of the images of the tops
`𝔻 (k i) × ∂𝔻 (n - k i)` of the handles and of the points of `f⁻¹(c - ε)` off the attaching
regions. -/
theorem exists_isPushout_sublevel_handles [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
    (hf : ∀ i, ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source) :
    ∃ (α : ∀ i, TopCat.of (TopCat.diskBoundary.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c - ε})
      (χ : ∀ i, TopCat.of (TopCat.disk.{u} (k i) × TopCat.disk.{u} (n - k i)) ⟶
        TopCat.of {x | f x ≤ c + ε})
      (j : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε}),
      IsPushout (Sigma.desc α) (Limits.Sigma.map fun i ↦ TopCat.ofHom
          ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id _)))
        j (Sigma.desc χ) ∧
      (∀ i, IsClosedEmbedding (α i)) ∧ Pairwise (Disjoint on fun i ↦ range (α i)) ∧
      (∀ i s, f (α i s : M) = c - ε) ∧
      (∀ i w, f (χ i w : M) = c + ε ↔
        ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin (n - k i))) 1)).down :
          EuclideanSpace ℝ (Fin (n - k i)))‖ = 1) ∧
      ∀ x, (∀ i, x ∉ range (α i)) → (f (j x : M) = c + ε ↔ f (x : M) = c - ε) := by
  obtain ⟨H, e, Φ, hH, hge, he, -, hΦ, hΦtop⟩ :=
    exists_diffeomorph_sublevel_eq_union_handles hfs ψ hψ k hε hball hf hcompact hcrit
  -- Relabel the coordinates `{j | j < k i}` and `{j | k i ≤ j}` of each handle as `Fin (k i)` and
  -- `Fin (n - k i)`, carrying it to the standard discs `𝔻 (k i) × 𝔻 (n - k i)`.
  have hcard : ∀ i, Fintype.card {j : Fin n // ¬j.val < k i} = n - k i := fun i ↦ by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin_lt_of_le (hk i)]
  refine isPushout_of_handles hfs.continuous k Φ.toHomeomorph H
    (fun i ↦ (e i).trans <|
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Fin.castLEquiv (hk i)).symm).closedBallHomeomorphDisk.{u}.prodCongr
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Fintype.equivFinOfCardEq (hcard i))).closedBallHomeomorphDisk.{u})
    (fun i l hil ↦ (hψ hil).mono (hH i) (hH l)) hge
    (fun i x ↦ by simp [he]) hΦ fun x ↦ ?_
  simp [hΦtop x]

/-- **Milnor's handle attachment theorem, as a pushout** (Milnor, Remark 3.3). Let `f` be a Morse
function on a Hausdorff manifold of dimension `m` whose band `f⁻¹[c - δ, c + δ]` is compact, for
some `0 < δ`, and write `M_a = {f ≤ a}` and `λ p` for the Morse index of `f` at a critical point
`p`. Then for some width `0 < ε ≤ δ`, the sublevel `M_{c+ε}` is obtained from `M_{c-ε}` by
attaching one handle `𝔻 (λ p) × 𝔻 (m - λ p)` at each critical point `p` on the level `f⁻¹(c)`: there
are attaching maps `α p : ∂𝔻 (λ p) × 𝔻 (m - λ p) → M_{c-ε}`, maps
`χ p : 𝔻 (λ p) × 𝔻 (m - λ p) → M_{c+ε}` and `j : M_{c-ε} → M_{c+ε}` forming a pushout square in
`TopCat`. The attaching maps are closed embeddings with pairwise disjoint images in the level
`f⁻¹(c - ε)`, and the level `f⁻¹(c + ε)` consists of the images of the tops
`𝔻 (λ p) × ∂𝔻 (m - λ p)` of the handles and of the points of `f⁻¹(c - ε)` off the attaching
regions. Indices `0` and `m` are included. -/
theorem IsMorse.exists_isPushout_sublevel_handles (hf : IsMorse I f) {δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧
      ∃ (α : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
          TopCat.of (TopCat.diskBoundary.{u} (manifoldMorseIndex I f p) ×
            TopCat.disk.{u} (Module.finrank ℝ E - manifoldMorseIndex I f p)) ⟶
          TopCat.of {x | f x ≤ c - ε})
        (χ : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
          TopCat.of (TopCat.disk.{u} (manifoldMorseIndex I f p) ×
            TopCat.disk.{u} (Module.finrank ℝ E - manifoldMorseIndex I f p)) ⟶
          TopCat.of {x | f x ≤ c + ε})
        (j : TopCat.of {x | f x ≤ c - ε} ⟶ TopCat.of {x | f x ≤ c + ε}),
        IsPushout (Sigma.desc α) (Limits.Sigma.map fun p ↦ TopCat.ofHom
            ((TopCat.diskBoundaryInclusion (manifoldMorseIndex I f p)).hom.prodMap
              (ContinuousMap.id _)))
          j (Sigma.desc χ) ∧
        (∀ p, IsClosedEmbedding (α p)) ∧ Pairwise (Disjoint on fun p ↦ range (α p)) ∧
        (∀ p s, f (α p s : M) = c - ε) ∧
        (∀ p w, f (χ p w : M) = c + ε ↔
          ‖((w.2 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p))) 1)).down :
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E - manifoldMorseIndex I f p)))‖ = 1) ∧
        ∀ x, (∀ p, x ∉ range (α p)) → (f (j x : M) = c + ε ↔ f (x : M) = c - ε) := by
  obtain ⟨ε, hε, hεδ, hband, ψ, hψ, hψp⟩ :=
    hf.exists_admissible_morseCharts hδ hcompact (U := fun _ ↦ univ) fun _ _ ↦ Filter.univ_mem
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  exact ⟨ε, hε, hεδ, TauCeti.exists_isPushout_sublevel_handles hf.contMDiff ψ hψ _
    (fun _ ↦ manifoldMorseIndex_le_finrank) hε (fun p ↦ (hψp p).2.2.2.1)
    (fun p ↦ (hψp p).2.2.2.2)
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx.1, hband hx⟩, (hψp _).1⟩⟩

end HandlePushout

end TauCeti
