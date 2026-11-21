/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.Homotopic.Rel

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

A level may carry several critical submanifolds `i a`, of different dimensions and indices, whose
negative disc bundles `D a` are then attached at once. If their images `Θ a (D a)` meet only inside
the lower sublevel, for instance if they are disjoint, the space `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a)` is
the pushout of the coproduct of the disc bundles along the coproduct of their sphere bundles
(`isPushout_iUnion_negativeDiscBundle`). For a Morse–Bott function on a compact manifold the
images are disjoint for small `ε`, and the deformation theorem
(`IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`) makes the
inclusion of this adjunction space into `{f ≤ c + ε}` a homotopy equivalence relative to
`{f ≤ c - ε}`, whose homotopy inverse is a retraction
(`TauCeti.IsMorseBottFamily.exists_isPushout_iUnion_negativeDiscBundle_homotopyEquiv`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le`: a point of the negative disc
  bundle is carried into the lower sublevel exactly when it lies in the negative sphere bundle.
* `IsCriticalSubmanifold.isPushout_negativeDiscBundle`: the lower sublevel together with the image
  of the negative disc bundle is the adjunction space `{f ≤ c - ε} ∪_{Θ|S_ε} D_ε`.
* `isPushout_iUnion_negativeDiscBundle`: the same for finitely many critical submanifolds, with the
  coproduct of their negative disc bundles attached along the coproduct of their sphere bundles.

In the namespace `TauCeti.IsMorseBottFamily`:

* `exists_isPushout_iUnion_negativeDiscBundle_homotopyEquiv`: crossing a critical level of a
  Morse–Bott function on a compact manifold attaches the negative disc bundles of its critical
  submanifolds on that level, up to a homotopy equivalence relative to the lower sublevel.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle Function Set Topology CategoryTheory
open scoped ContDiff Manifold ContinuousMap

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

section FamilyPushout

universe u

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] [T2Space M] {ι : Type u} [Finite ι] {E' H' : ι → Type*}
  {S : ι → Type u} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)] {f : M → ℝ} {n : ℕ∞ω}
  {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {hn : n ≠ 0} {P : ι → Type*}
  {h : ∀ a, (i a).IsCriticalSubmanifold f}
  {g : ∀ a, RiemannianMetric fun s ↦ (i a).NormalSpace s hn}
  {Θ : ∀ a, TotalSpace (P a) (fun s ↦ (i a).NormalSpace s hn) → M} {c ε : ℝ}

/-- **The lower sublevel with the images of several negative disc bundles is an adjunction
space.** Let `i a : S a → M`, for `a` in a finite index type, be critical submanifolds of a
continuous function `f` on a Hausdorff manifold, each with its own model and a fibre metric `g a`
on its normal bundle, and suppose that each negative disc bundle `D a = D_ε(i a)` is compact. Let
`Θ a` be continuous and injective on `D a` and put `f` there in the Morse–Bott normal form
`f (Θ a v) = c + ½ Hessₛ (v, v)`, and suppose that two different images `Θ a (D a)` and
`Θ b (D b)` meet only inside the lower sublevel `{f ≤ c - ε}`, as they do when they are disjoint.

Then the maps `Θ a` restrict to attaching maps `α a : S_ε(i a) → {f ≤ c - ε}` on the negative
sphere bundles and to maps `χ a : D a → {f ≤ c - ε} ∪ ⋃ a, Θ a (D a)`, and these form a pushout
square in `TopCat`: the space `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a)` is the adjunction space
`{f ≤ c - ε} ∪_α ⨆ a, D a` of the coproduct of the disc bundles along the coproduct of their sphere
bundles. -/
theorem isPushout_iUnion_negativeDiscBundle (hf : Continuous f)
    (hD : ∀ a, IsCompact ((h a).negativeDiscBundle hn (P a) (g a) ε))
    (hΘc : ∀ a, ContinuousOn (Θ a) ((h a).negativeDiscBundle hn (P a) (g a) ε))
    (hΘi : ∀ a, InjOn (Θ a) ((h a).negativeDiscBundle hn (P a) (g a) ε))
    (hΘ : ∀ a, ∀ x ∈ (h a).negativeDiscBundle hn (P a) (g a) ε,
      f (Θ a x) = c + 2⁻¹ * (h a).normalHessian hn x.proj x.snd x.snd)
    (hd : Pairwise fun a b ↦ Θ a '' (h a).negativeDiscBundle hn (P a) (g a) ε ∩
      Θ b '' (h b).negativeDiscBundle hn (P b) (g b) ε ⊆ {y | f y ≤ c - ε}) :
    ∃ (α : ∀ a, C((h a).negativeSphereBundle hn (P a) (g a) ε, {y | f y ≤ c - ε}))
      (χ : ∀ a, C((h a).negativeDiscBundle hn (P a) (g a) ε,
        ({y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' (h a).negativeDiscBundle hn (P a) (g a) ε : Set M))),
      (∀ a x, (α a x : M) = Θ a x) ∧ (∀ a x, (χ a x : M) = Θ a x) ∧
      IsPushout (Limits.Sigma.desc fun a ↦ TopCat.ofHom (α a))
        (Limits.Sigma.map fun a ↦ TopCat.ofHom (ContinuousMap.inclusion
          ((h a).negativeSphereBundle_subset_negativeDiscBundle hn (P a) (g a) ε)))
        (TopCat.ofHom (ContinuousMap.inclusion subset_union_left))
        (Limits.Sigma.desc fun a ↦ TopCat.ofHom (χ a)) := by
  set D := fun a ↦ (h a).negativeDiscBundle hn (P a) (g a) ε
  set L : Set M := {y | f y ≤ c - ε}
  have hSD (a : ι) := (h a).negativeSphereBundle_subset_negativeDiscBundle hn (P a) (g a) ε
  have hα (a : ι) : MapsTo (Θ a) ((h a).negativeSphereBundle hn (P a) (g a) ε) L := fun x hx ↦
    (IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le (hΘ a) (hSD a hx)).1 hx
  have hχ (a : ι) : MapsTo (Θ a) (D a) (L ∪ ⋃ a, Θ a '' D a) := fun x hx ↦
    Or.inr (mem_iUnion.2 ⟨a, mem_image_of_mem (Θ a) hx⟩)
  refine ⟨fun a ↦ ⟨(hα a).restrict, ((hΘc a).mono (hSD a)).mapsToRestrict (hα a)⟩,
    fun a ↦ ⟨(hχ a).restrict, (hΘc a).mapsToRestrict (hχ a)⟩, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
    IsPushout.of_isClosedEmbedding (fun _ ↦ rfl) ?_ (fun a ↦ ?_) ?_ ?_ ?_⟩
  · exact IsClosedEmbedding.inclusion subset_union_left
      ((isClosed_le hf continuous_const).preimage continuous_subtypeVal)
  · have := isCompact_iff_compactSpace.1 (hD a)
    exact ((hΘc a).mapsToRestrict (hχ a)).isClosedEmbedding fun x y hxy ↦
      (hΘi a).injective (congrArg Subtype.val hxy)
  · refine eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
    rcases hy with hy | hy
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨a, x, hx, rfl⟩ := mem_iUnion.1 hy
      exact Or.inr (mem_iUnion.2 ⟨a, ⟨x, hx⟩, rfl⟩)
  · -- Two different discs meet only inside the lower sublevel.
    rintro a b hab _ ⟨⟨x, rfl⟩, ⟨x', hxx'⟩⟩
    have hL : Θ a x ∈ L := hd hab ⟨mem_image_of_mem (Θ a) x.property,
      ⟨x', x'.property, congrArg Subtype.val hxx'⟩⟩
    exact ⟨⟨Θ a x, hL⟩, rfl⟩
  · -- A point of the lower sublevel on a disc lies on its sphere bundle.
    rintro a ⟨y, hy⟩ ⟨x, hx⟩ hxy
    have hxy : y = Θ a x := congrArg Subtype.val hxy
    subst hxy
    exact ⟨⟨x, (IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le (hΘ a) hx).2 hy⟩,
      rfl, rfl⟩

end FamilyPushout

end SmoothEmbedding

namespace IsMorseBottFamily

universe u

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type u} {E' H' P : ι → Type*}
  {S : ι → Type u} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  [∀ a, FiniteDimensional ℝ (E' a)] [∀ a, TopologicalSpace (H' a)]
  {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)} [∀ a, TopologicalSpace (S a)]
  [∀ a, ChartedSpace (H' a) (S a)] [∀ a, IsManifold (J a) ∞ (S a)]
  [∀ a, NormedAddCommGroup (P a)] [∀ a, NormedSpace ℝ (P a)] [∀ a, FiniteDimensional ℝ (P a)]
  {f : M → ℝ} {i : ∀ a, SmoothEmbedding (J a) I ∞ (S a) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Crossing a critical level of a Morse–Bott function attaches the negative disc bundles of its
critical submanifolds on that level, up to a homotopy equivalence relative to the lower
sublevel.** Let the family `i a : S a → M` exhibit `f` as a Morse–Bott function
(`TauCeti.IsMorseBottFamily`) on a compact Hausdorff second-countable boundaryless manifold, with
pieces modelled on boundaryless models, and let `g a` be a smooth fibre metric on the normal bundle
of `i a`. Fix `c : ℝ`, and index the pieces on the level `f = c` by `{a // ∀ s, f (i a s) = c}`.

Then there are smooth partial diffeomorphisms `Θ a` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i a`,
which put `f` in the Morse–Bott normal form `f (Θ a v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with
the following property for `0 < ε < ε₀`. Write `D a` and `S_ε(a)` for the negative disc and sphere
bundles of size `ε` relative to `g a`, and `X = {f ≤ c - ε} ∪ ⋃ a, Θ a (D a)`.

* `X` is the adjunction space `{f ≤ c - ε} ∪_α ⨆ a, D a`: the restrictions `α a` of `Θ a` to the
  sphere bundles, with values in `{f ≤ c - ε}`, and `χ a` to the disc bundles, with values in `X`,
  form a pushout square in `TopCat` with the inclusions `S_ε(a) ⊆ D a` and `{f ≤ c - ε} ⊆ X`.
* The inclusion `e : X → {f ≤ c + ε}` is a homotopy equivalence relative to `{f ≤ c - ε}`: it has
  a homotopy inverse which is a retraction, `e⁻¹ ∘ e = id`, and `e ∘ e⁻¹` is homotopic to the
  identity relative to `{f ≤ c - ε}`.

For an isolated nondegenerate critical point the disc bundle is a cell of dimension the index, and
this is Milnor's cell attachment. -/
theorem exists_isPushout_iUnion_negativeDiscBundle_homotopyEquiv [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [∀ a, (J a).Boundaryless]
    (h : IsMorseBottFamily i f) (c : ℝ)
    (hdim : ∀ a, Module.finrank ℝ (P a) = Module.finrank ℝ E - Module.finrank ℝ (E' a))
    (g : letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
      letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
      ∀ a, ContMDiffRiemannianMetric (J a) ∞ (P a) fun s ↦ (i a).NormalSpace s hn) :
    letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
    letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
    ∃ Θ : ∀ a : {a // ∀ s, f (i a s) = c}, PartialDiffeomorph ((J a).prod 𝓘(ℝ, P a)) I
        (TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) M ∞,
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s ∈ (Θ a).source) ∧
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        Θ a (zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s) = i a s) ∧
      (∀ a : {a // ∀ s, f (i a s) = c}, ∀ x ∈ (Θ a).source, f (Θ a x) =
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold a).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        ∃ (α : ∀ a : {a // ∀ s, f (i a s) = c},
            C((h.isNondegenerateCriticalSubmanifold a).negativeSphereBundle hn (P a)
              (g a).toRiemannianMetric ε, {y | f y ≤ c - ε}))
          (χ : ∀ a : {a // ∀ s, f (i a s) = c},
            C((h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
              (g a).toRiemannianMetric ε,
              ({y | f y ≤ c - ε} ∪ ⋃ a : {a // ∀ s, f (i a s) = c},
                Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
                  (g a).toRiemannianMetric ε : Set M))),
          (∀ a x, (α a x : M) = Θ a x) ∧ (∀ a x, (χ a x : M) = Θ a x) ∧
          IsPushout (Limits.Sigma.desc fun a ↦ TopCat.ofHom (α a))
            (Limits.Sigma.map fun a ↦ TopCat.ofHom <| ContinuousMap.inclusion <|
            (h.isNondegenerateCriticalSubmanifold a).negativeSphereBundle_subset_negativeDiscBundle
              hn (P a) (g a).toRiemannianMetric ε)
            (TopCat.ofHom (ContinuousMap.inclusion subset_union_left))
            (Limits.Sigma.desc fun a ↦ TopCat.ofHom (χ a)) ∧
          ∃ e : ↥({y | f y ≤ c - ε} ∪ ⋃ a : {a // ∀ s, f (i a s) = c},
                Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
                  (g a).toRiemannianMetric ε) ≃ₕ {y | f y ≤ c + ε},
            (∀ x, (e x : M) = x) ∧ (∀ x, e.invFun (e x) = x) ∧
            (e.toFun.comp e.invFun).HomotopicRel (ContinuousMap.id _)
              {y | f y ≤ c - ε} := by
  let : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
    fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
  let : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
    fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
  have := h.finite
  have (a : ι) : T2Space (S a) := (i a).isEmbedding.t2Space
  have (a : ι) : CompactSpace (S a) :=
    (Topology.IsClosedEmbedding.mk (i a).isEmbedding (h.isClosed_range a)).compactSpace
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_iUnion_negativeDiscBundle_deformation hn c hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨hsrc, hdisj, r, hr, ⟨G⟩⟩ := hmain ε hε
  set D := fun a : {a // ∀ s, f (i a s) = c} ↦
    (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a) (g a).toRiemannianMetric ε
  obtain ⟨α, χ, hα, hχ, hP⟩ := SmoothEmbedding.isPushout_iUnion_negativeDiscBundle
    (ι := {a // ∀ s, f (i a s) = c}) (S := fun a ↦ S a) (P := fun a ↦ P a) (J := fun a ↦ J a)
    (i := fun a ↦ i a) (Θ := fun a ↦ Θ a) (c := c)
    (h := fun a ↦ (h.isNondegenerateCriticalSubmanifold a).toIsCriticalSubmanifold)
    h.contMDiff.continuous
    (fun a ↦ (h.isNondegenerateCriticalSubmanifold a).isCompact_negativeDiscBundle hn h.contMDiff
      (hdim a) (g a) ε)
    (fun a ↦ (Θ a).contMDiffOn.continuousOn.mono (hsrc a)) (fun a ↦ (Θ a).injOn.mono (hsrc a))
    (fun a x hx ↦ hΘf a x (hsrc a hx))
    (fun a b hab _ hx ↦ (Set.disjoint_iff.1 (hdisj hab) hx).elim)
  refine ⟨α, χ, hα, hχ, hP, ?_⟩
  -- The lower sublevel and the discs lie in `{f ≤ c + ε}`, since `f ≤ c` on the discs.
  have hX : {y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' D a ⊆ {y | f y ≤ c + ε} := by
    refine union_subset (fun y hy ↦ ?_) (iUnion_subset fun a ↦ ?_)
    · simp only [mem_ofPred_eq] at hy ⊢
      linarith [hε.1]
    · rintro _ ⟨x, hx, rfl⟩
      exact (SmoothEmbedding.IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle
        (fun x hx ↦ hΘf a x (hsrc a hx)) hx).trans (by linarith [hε.1])
  -- The retraction `r`, read as a map onto `X`, is a left inverse of the inclusion of `X`. Both
  -- `ContinuousMap.inclusion hX x` and `ContinuousMap.inclusion inter_subset_left ⟨x, _⟩` are the
  -- point `x` of `M` with a membership proof, so `hr` applies to `x` as it stands.
  set ρ := (ContinuousMap.inclusion inter_subset_right).comp r
  have hρ (x) : ρ (ContinuousMap.inclusion hX x) = x :=
    Subtype.ext (congrArg Subtype.val (hr ⟨x.val, hX x.property, x.property⟩) :)
  have hρ' : (ContinuousMap.inclusion hX).comp ρ =
      (ContinuousMap.inclusion inter_subset_left).comp r :=
    ContinuousMap.ext fun _ ↦ rfl
  set e := ContinuousMap.HomotopyEquiv.ofRetraction hX ρ hρ (G.toHomotopy.cast hρ'.symm rfl)
  have he₁ (x) : (e x : M) = x := ContinuousMap.HomotopyEquiv.coe_ofRetraction_apply _ _ _ _ x
  have he : e.toFun = ContinuousMap.inclusion hX := ContinuousMap.ext fun x ↦ Subtype.ext (he₁ x)
  have he' : e.invFun = ρ :=
    ContinuousMap.ext (ContinuousMap.HomotopyEquiv.coe_ofRetraction_symm_apply _ _ _ _)
  refine ⟨e, he₁, fun x ↦ ?_, ?_⟩
  · simpa only [← he, ← he'] using hρ x
  · rw [he, he', hρ']; exact ContinuousMap.HomotopicRel.mono ⟨G⟩ fun y hy ↦ Or.inl hy

end IsMorseBottFamily

end TauCeti
