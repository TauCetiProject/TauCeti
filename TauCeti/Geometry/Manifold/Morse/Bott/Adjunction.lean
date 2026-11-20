/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
import TauCeti.Topology.Category.TopCat.Pushout

/-!
# The negative disc bundle is attached along its sphere bundle

Let `i : S → M` be a critical submanifold of a function `f` on the level `f = c`, let `g` be a
fibre metric on its normal bundle `ν`, and let `Θ` be a Morse–Bott normal form on the negative
disc bundle `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}`: `f (Θ v) = c + ½ Hessₛ (v, v)`. For a compact
Morse–Bott submanifold, crossing the critical level, there are such a `Θ` and an `ε₀ > 0` such
that for `0 < ε < ε₀` with the band `f⁻¹[c - ε, c + ε]` compact and its critical points on `i`,
the sublevel `{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε} ∪ Θ(D_ε)`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in
the namespace `TauCeti.SmoothEmbedding`). This file shows that this union is the space obtained
from the lower sublevel by attaching `D_ε` along the negative sphere bundle
`S_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) = ε}`, through `Θ`.

The normal Hessian is negative semidefinite on `ν⁻`, so on `D_ε` the value `f (Θ v)` lies between
`c - ε` and `c`, and it equals `c - ε` exactly on `S_ε`. Hence `Θ(D_ε)` lies in the critical
sublevel `{f ≤ c}` (`IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle`) and meets the lower
sublevel exactly in `Θ(S_ε)` (`IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le`,
`IsCriticalSubmanifold.image_negativeDiscBundle_inter_sublevel`). With a closed embedding of
`D_ε`, these conditions are analogous to the hypotheses of
`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`, which computes the relative homology
of a closed embedding of the disc bundle `TauCeti.gaugeDiscBundle` of a fibre gauge on a vector
bundle attached along its sphere bundle. `D_ε` is cut out of the whole normal bundle by the normal
Hessian, as the disc bundle of the gauge `v ↦ √(-Hess(v, v) / (2ε))` on the negative normal
spaces, so applying that theorem to `D_ε` still needs the negative normal bundle as a vector bundle
with that gauge.

When `D_ε` is compact, as it is for a compact Morse–Bott submanifold and a smooth fibre metric
(`IsNondegenerateCriticalSubmanifold.isCompact_negativeDiscBundle`), a normal form which is
continuous and injective on `D_ε` embeds it as a closed subset of the Hausdorff manifold `M`.
Covered by the closed sets `{f ≤ c - ε}` and `Θ(D_ε)`, which meet in `Θ(S_ε)`, the union is
therefore a pushout in `TopCat` of the attaching map `Θ : S_ε → {f ≤ c - ε}` along the inclusion
`S_ε → D_ε` (`IsCriticalSubmanifold.isPushout_negativeDiscBundle`). Together with the deformation
theorem, for `0 < ε < ε₀` with `f⁻¹[c - ε, c + ε]` compact and its critical points on `i`,
`{f ≤ c + ε}` is homotopy equivalent, relative to `{f ≤ c - ε}`, to
`{f ≤ c - ε} ∪_{Θ|S_ε} D_ε`: crossing the level of a compact Morse–Bott submanifold attaches its
negative disc bundle along its sphere bundle. For an isolated nondegenerate critical point the
base is a point, `D_ε` is a closed ellipsoid of dimension the index and `S_ε` its boundary sphere.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le`: a point of the negative disc
  bundle is carried into the lower sublevel exactly when it lies in the negative sphere bundle.
* `IsCriticalSubmanifold.isPushout_negativeDiscBundle`: the lower sublevel together with the image
  of the negative disc bundle is the adjunction space `{f ≤ c - ε} ∪_{Θ|S_ε} D_ε`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle Function Set Topology CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding

section Sublevel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {E' H' S : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S]
  [ChartedSpace H' S] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {P : Type*} (h : i.IsCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ}

namespace IsCriticalSubmanifold

variable {hn h g}

variable [FiniteDimensional ℝ E] in
/-- **The negative disc bundle lies below the critical level.** If `Θ` puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)` on the negative disc bundle `D_ε`, then `f`
is at most `c` on `Θ(D_ε)`, since the normal Hessian is negative semidefinite on the negative
normal spaces. -/
theorem apply_le_of_mem_negativeDiscBundle
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {x : TotalSpace P fun s ↦ i.NormalSpace s hn} (hx : x ∈ h.negativeDiscBundle hn P g ε) :
    f (Θ x) ≤ c := by
  rw [hΘ x hx]
  linarith [h.normalHessian_apply_self_nonpos_of_mem_negativeNormalSpace hn g
    (mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx)]

/-- **The negative disc bundle meets the lower sublevel along its sphere bundle.** If `Θ` puts
`f` in the Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)` on the negative disc bundle
`D_ε`, then a point `v` of `D_ε` is carried into the lower sublevel `{f ≤ c - ε}` exactly when it
lies in the negative sphere bundle `S_ε`. -/
theorem mem_negativeSphereBundle_iff_apply_le
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {x : TotalSpace P fun s ↦ i.NormalSpace s hn} (hx : x ∈ h.negativeDiscBundle hn P g ε) :
    x ∈ h.negativeSphereBundle hn P g ε ↔ f (Θ x) ≤ c - ε := by
  rw [mem_negativeSphereBundle, hΘ x hx]
  obtain ⟨hxν, hxε⟩ := (mem_negativeDiscBundle hn).1 hx
  exact ⟨fun hS ↦ by linarith [hS.2], fun hle ↦ ⟨hxν, le_antisymm hxε (by linarith)⟩⟩

/-- The image of the negative disc bundle under a Morse–Bott normal form `Θ` meets the lower
sublevel `{f ≤ c - ε}` exactly in the image of the negative sphere bundle. -/
theorem image_negativeDiscBundle_inter_sublevel
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) :
    Θ '' h.negativeDiscBundle hn P g ε ∩ {y | f y ≤ c - ε} =
      Θ '' h.negativeSphereBundle hn P g ε := by
  ext y
  refine ⟨fun ⟨⟨x, hx, hxy⟩, hy⟩ ↦ ⟨x, (mem_negativeSphereBundle_iff_apply_le hΘ hx).2
    (hxy ▸ hy), hxy⟩, fun ⟨x, hx, hxy⟩ ↦ ?_⟩
  have hxD := h.negativeSphereBundle_subset_negativeDiscBundle hn P g ε hx
  exact ⟨⟨x, hxD, hxy⟩, hxy ▸ (mem_negativeSphereBundle_iff_apply_le hΘ hxD).1 hx⟩

end IsCriticalSubmanifold

end Sublevel

section Pushout

universe u

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] [T2Space M] {E' H' : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S]
  [ChartedSpace H' S] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} {hn : n ≠ 0}
  {P : Type*} {h : i.IsCriticalSubmanifold f} {g : RiemannianMetric fun s ↦ i.NormalSpace s hn}
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ}

namespace IsCriticalSubmanifold

/-- **The lower sublevel with the image of the negative disc bundle is an adjunction space.** Let
`i : S → M` be a critical submanifold of a continuous function `f` on a Hausdorff manifold, with a
fibre metric `g` on its normal bundle, and suppose that the negative disc bundle `D_ε` is compact,
as it is for a compact Morse–Bott submanifold and a smooth fibre metric
(`IsNondegenerateCriticalSubmanifold.isCompact_negativeDiscBundle`). Let `Θ` be continuous and
injective on `D_ε` and put `f` there in the Morse–Bott normal form
`f (Θ v) = c + ½ Hessₛ (v, v)`, as the normal form of
`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation` does.

Then `Θ` restricts to an attaching map `α : S_ε → {f ≤ c - ε}` on the negative sphere bundle and
to a map `χ : D_ε → {f ≤ c - ε} ∪ Θ(D_ε)`, and the square formed by `α`, the inclusion
`S_ε → D_ε`, the inclusion of the lower sublevel and `χ` is a pushout in `TopCat`: the space
`{f ≤ c - ε} ∪ Θ(D_ε)` is the adjunction space `{f ≤ c - ε} ∪_α D_ε`. -/
theorem isPushout_negativeDiscBundle (hf : Continuous f)
    (hD : IsCompact (h.negativeDiscBundle hn P g ε))
    (hΘc : ContinuousOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘi : InjOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) :
    ∃ (α : C(h.negativeSphereBundle hn P g ε, {y | f y ≤ c - ε}))
      (χ : C(h.negativeDiscBundle hn P g ε,
        ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g ε : Set M))),
      (∀ x, (α x : M) = Θ x) ∧ (∀ x, (χ x : M) = Θ x) ∧
      IsPushout (TopCat.ofHom α)
        (TopCat.ofHom (ContinuousMap.inclusion
          (h.negativeSphereBundle_subset_negativeDiscBundle hn P g ε)))
        (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) (TopCat.ofHom χ) := by
  set D := h.negativeDiscBundle hn P g ε
  set L : Set M := {y | f y ≤ c - ε}
  have hSD := h.negativeSphereBundle_subset_negativeDiscBundle hn P g ε
  have hα : MapsTo Θ (h.negativeSphereBundle hn P g ε) L := fun x hx ↦
    (mem_negativeSphereBundle_iff_apply_le hΘ (hSD hx)).1 hx
  have hχ : MapsTo Θ D (L ∪ Θ '' D) := fun x hx ↦ Or.inr (mem_image_of_mem Θ hx)
  refine ⟨⟨hα.restrict, (hΘc.mono hSD).mapsToRestrict hα⟩, ⟨hχ.restrict, hΘc.mapsToRestrict hχ⟩,
    fun _ ↦ rfl, fun _ ↦ rfl, IsPushout.of_isClosedEmbedding_of_range_union_range rfl ?_ ?_ ?_ ?_⟩
  · exact IsClosedEmbedding.inclusion subset_union_left
      ((isClosed_le hf continuous_const).preimage continuous_subtypeVal)
  · have := isCompact_iff_compactSpace.1 hD
    exact (hΘc.mapsToRestrict hχ).isClosedEmbedding fun x y hxy ↦
      hΘi.injective (congrArg Subtype.val hxy)
  · refine eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
    rcases hy with hy | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩ ⟨x, hx⟩ hxy
    have hxy : y = Θ x := congrArg Subtype.val hxy
    subst hxy
    exact ⟨⟨x, (mem_negativeSphereBundle_iff_apply_le hΘ hx).2 hy⟩, rfl, rfl⟩

end IsCriticalSubmanifold

end Pushout

end SmoothEmbedding

end TauCeti
