/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Topology.Homotopy.Extension.Pushout
import TauCeti.Geometry.Manifold.Morse.Deformation.Attachment
import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Topology.VectorBundle.Smul

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

The file then moves this attachment between arbitrary regular levels around `c`. Write
`M_t = {f ≤ t}`, and let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and its critical
points all lie on `i`. Then `M_b` is homotopy equivalent to `M_a` with `D_ε` attached along its
sphere bundle, by a homotopy equivalence which is the inclusion `M_a → M_b` on `M_a`
(`IsNondegenerateCriticalSubmanifold.exists_homotopyEquiv_pushout_negativeDiscBundle`). The
attaching map is `Θ` on `S_ε` followed by a retraction `r` of `M_{c-ε}` onto `M_a` along the band
`f⁻¹[a, c - ε]`, which contains no critical point. For an isolated nondegenerate critical point
this is Milnor's attachment of a cell
(`TauCeti.IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace`).

The homotopy equivalence is the composite of three. First, the adjunction space
`M_{c-ε} ∪_{Θ|S_ε} D_ε` above is a strong deformation retract of `M_{c+ε}`. Second, the inclusion
`M_{c+ε} → M_b` is a homotopy equivalence across the band `f⁻¹[c + ε, b]`
(`TauCeti.exists_sublevelHomotopyEquiv`). Third, `r` is a homotopy equivalence with homotopy inverse
the inclusion, and attaching along a cofibration is homotopy invariant under a change of base
(`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_pushout`). The inclusion `S_ε → D_ε` is a
cofibration because the cylinder over `D_ε` retracts radially onto its bottom and its part over
`S_ε`, fibre by fibre (`TauCeti.hasHomotopyExtensionProperty_setOf_eq_one`). The last two steps
move the attachment across the regular collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]`, as in the
Morse case (`TauCeti.exists_homotopyEquiv_pushout_comp_sublevelRetraction`). This is the step by
which the sublevels of a Morse–Bott function are built, one critical submanifold at a time, along a
sequence of regular levels separating its critical values.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le`: a point of the negative disc
  bundle is carried into the lower sublevel exactly when it lies in the negative sphere bundle.
* `IsCriticalSubmanifold.isPushout_negativeDiscBundle`: the lower sublevel together with the image
  of the negative disc bundle is the adjunction space `{f ≤ c - ε} ∪_{Θ|S_ε} D_ε`.
* `IsCriticalSubmanifold.hasHomotopyExtensionProperty_negativeSphereBundle`: the
  negative sphere bundle has the homotopy extension property in the negative disc bundle.
* `IsNondegenerateCriticalSubmanifold.exists_homotopyEquiv_pushout_negativeDiscBundle`: if
  `a < c < b`, the band `f⁻¹[a, b]` is compact and its critical points lie on the critical
  submanifold, then `M_b` is homotopy equivalent to `M_a` with the negative disc bundle attached,
  by a homotopy equivalence which is the inclusion on `M_a`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Bundle Function Set Topology CategoryTheory Limits
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

section Adjunction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsCriticalSubmanifold

/-- **The negative sphere bundle is a cofibration in the negative disc bundle.** Let `i : S → M` be
a critical submanifold of a smooth function `f`, and let `g` be a smooth fibre metric
on its normal bundle. Then the negative sphere bundle `S_ε`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeSphereBundle`) has the homotopy extension
property inside the negative disc bundle `D_ε`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`). For `ε ≤ 0` the two are
equal, the zero section or empty. -/
theorem hasHomotopyExtensionProperty_negativeSphereBundle
    (h : i.IsCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) (ε : ℝ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasHomotopyExtensionProperty
      (range (ContinuousMap.inclusion (h.negativeSphereBundle_subset_negativeDiscBundle hn P
        g.toRiemannianMetric ε))) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set gR := g.toRiemannianMetric
  -- The gauge `ρ = √(q / ε)`, `q v = -½ Hessₛ (v, v)`, of the negative disc bundle, which is
  -- homogeneous of degree one for the fibrewise scalar multiplication.
  set q : TotalSpace P (fun s ↦ i.NormalSpace s hn) → ℝ :=
    fun x ↦ -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) with hq
  have hqc : Continuous q :=
    (continuous_const.mul (h.contMDiff_normalHessian_apply_self hn
      (k := ∞) (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim).continuous).neg
  have hqsmul (c : ℝ) (x : TotalSpace P (fun s ↦ i.NormalSpace s hn)) :
      q (TotalSpace.mk' P x.proj (c • x.snd)) = c ^ 2 * q x := by
    simp only [hq, TotalSpace.mk', map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- For `ε ≤ 0` every point of `D_ε` lies on `S_ε`, since `q ≥ 0` on the negative normal spaces.
  rcases le_or_gt ε 0 with hε | hε
  · convert isClopen_univ.hasHomotopyExtensionProperty
    refine eq_univ_of_forall fun x ↦ ⟨⟨x, ?_⟩, rfl⟩
    have hx := (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 x.property
    refine (IsCriticalSubmanifold.mem_negativeSphereBundle hn).2 ⟨hx.1, le_antisymm hx.2 ?_⟩
    linarith [h.normalHessian_apply_self_nonpos_of_mem_negativeNormalSpace hn gR hx.1]
  have hrange : range (ContinuousMap.inclusion
      (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)) =
      {x : h.negativeDiscBundle hn P gR ε | √(q x / ε) = 1} := by
    refine (range_inclusion (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)).trans ?_
    ext x
    refine (IsCriticalSubmanifold.mem_negativeSphereBundle hn).trans ?_
    rw [mem_ofPred_eq, Real.sqrt_eq_one, div_eq_one_iff_eq hε.ne']
    exact and_iff_right ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 x.property).1
  rw [hrange]
  refine hasHomotopyExtensionProperty_setOf_eq_one (ρ := fun x ↦ √(q x / ε))
    (Real.continuous_sqrt.comp (hqc.div_const ε)).continuousOn (fun x hx ↦ ⟨Real.sqrt_nonneg _,
      Real.sqrt_le_one.2 ((div_le_one hε).2 ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1
        hx).2)⟩) (φ := fun c x ↦ TotalSpace.mk' P x.proj (c • x.snd))
    (VectorBundle.continuous_smul ℝ P _).continuousOn (fun x hx c hc hcx ↦ ?_) fun x _ ↦ by
      simp [TotalSpace.mk']
  -- Rescaling by `c ≥ 0` multiplies the gauge by `c`.
  have hρ : √(q (TotalSpace.mk' P x.proj (c • x.snd)) / ε) = c * √(q x / ε) := by
    rw [hqsmul, mul_div_assoc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  refine ⟨(IsCriticalSubmanifold.mem_negativeDiscBundle hn).2
    ⟨Submodule.smul_mem _ c ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx).1, ?_⟩, hρ⟩
  rw [← hρ, Real.sqrt_le_one, div_le_one hε] at hcx
  exact hcx

end IsCriticalSubmanifold

end Adjunction

section Attachment

universe u

variable {E : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type u}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {E' H' : Type*}
  {S : Type u} {P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- Across a narrow band `f⁻¹[c - ε, c + ε]`, the output of the attachment theorem
`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation` in
pushout form: `M_{c+ε}` is homotopy equivalent to `M_{c-ε}` with `D_ε` attached along `Θ`, by a
homotopy equivalence which is the inclusion on `M_{c-ε}`. -/
private theorem exists_homotopyEquiv_pushout_of_deformation [T2Space S] [CompactSpace S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hε : 0 < ε) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∀ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) →
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source →
      ∀ ρ : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
          ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))),
      (∀ y, ρ (ContinuousMap.inclusion inter_subset_left y) = y) →
      ((ContinuousMap.inclusion inter_subset_left).comp ρ).HomotopyRel (ContinuousMap.id _)
          {y | (y : M) ∈
            {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε} →
      ∃ α : C(h.negativeSphereBundle hn P g.toRiemannianMetric ε, {y | f y ≤ c - ε}),
        (∀ x, (α x : M) = Θ x) ∧
        ∃ e : ↑(pushout (TopCat.ofHom (ContinuousMap.inclusion
              (h.negativeSphereBundle_subset_negativeDiscBundle hn P g.toRiemannianMetric ε)))
            (TopCat.ofHom α)) ≃ₕ {y | f y ≤ c + ε},
          ∀ z, (e (pushout.inr (TopCat.ofHom (ContinuousMap.inclusion
              (h.negativeSphereBundle_subset_negativeDiscBundle hn P g.toRiemannianMetric ε)))
            (TopCat.ofHom α) z) : M) = z := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set gR := g.toRiemannianMetric
  intro Θ hΘf hD ρ hρ R
  -- `M_{c-ε} ∪ Θ(D_ε)` is the adjunction space, and it lies in `M_{c+ε}` since `f ≤ c` on
  -- `Θ(D_ε)`.
  obtain ⟨α, χ, hα, -, sq⟩ := IsCriticalSubmanifold.isPushout_negativeDiscBundle
    (h := h.toIsCriticalSubmanifold) hfs.continuous (h.isCompact_negativeDiscBundle hn hfs hdim g ε)
    (Θ.contMDiffOn.continuousOn.mono hD) (Θ.toPartialEquiv.injOn.mono hD) fun x hx ↦ hΘf x (hD hx)
  have hU : {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P gR ε ⊆ {y | f y ≤ c + ε} := by
    rintro _ (hy | ⟨x, hx, rfl⟩)
    · exact (show f _ ≤ c - ε from hy).trans (by linarith)
    · exact (IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle
        (h := h.toIsCriticalSubmanifold) (fun x hx ↦ hΘf x (hD hx)) hx).trans (by linarith)
  replace sq := sq.flip
  -- The pushout is identified with `M_{c-ε} ∪ Θ(D_ε)` compatibly with the inclusions of
  -- `M_{c-ε}`, and that union is a strong deformation retract of `M_{c+ε}`.
  have hinr (w : {y | f y ≤ c - ε}) : (TopCat.homeoOfIso sq.isoPushout.symm (pushout.inr
      (TopCat.ofHom (ContinuousMap.inclusion
        (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε))) (TopCat.ofHom α) w) : M) =
        w := by
    rw [TopCat.homeoOfIso_apply, Iso.symm_hom, ← ConcreteCategory.comp_apply,
      sq.inr_isoPushout_inv, TopCat.ofHom_apply, ContinuousMap.inclusion_apply_coe]
  refine ⟨α, hα, ((TopCat.homeoOfIso sq.isoPushout.symm).trans
    (Homeomorph.setCongr (inter_eq_right.2 hU).symm)).toHomotopyEquiv.trans
    (ContinuousMap.HomotopyEquiv.ofRetraction _ ρ hρ R.toHomotopy), fun z ↦ ?_⟩
  rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.HomotopyEquiv.coe_ofRetraction_apply]
  exact hinr z

/-- **Crossing a Morse–Bott level between regular levels attaches the negative disc bundle.** Let
`i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `S` compact and nonempty and
`f = c` along `i`, and let `g` be a smooth fibre metric on the normal bundle of `i`. Let `a < c < b`
be such that the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`. Write
`M_t = {f ≤ t}`.

Then there are a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and a width `ε > 0` with `a ≤ c - ε` and
`c + ε ≤ b`, such that the negative disc bundle `D_ε` relative to `g`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`) lies in the source of `Θ`,
and the following holds. Let `α : S_ε → M_{c-ε}` be `Θ` on the negative sphere bundle `S_ε`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeSphereBundle`), which `Θ` carries into
the level `f⁻¹(c - ε)`. There is a retraction `r` of `M_{c-ε}` onto `M_a` such that `M_b` is
homotopy equivalent to `M_a` with `D_ε` attached along `r ∘ α`, the pushout in `TopCat` of the
inclusion `S_ε → D_ε` and of `r ∘ α`, by a homotopy equivalence which is the inclusion
`M_a → M_b` on `M_a`. -/
theorem exists_homotopyEquiv_pushout_negativeDiscBundle [SecondCountableTopology M]
    [J.Boundaryless] [CompactSpace S] [Nonempty S] (h : i.IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε > 0, a ≤ c - ε ∧ c + ε ≤ b ∧
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ (α : C(h.negativeSphereBundle hn P g.toRiemannianMetric ε, {y | f y ≤ c - ε}))
          (r : C({y | f y ≤ c - ε}, {y | f y ≤ a})),
          (∀ x, (α x : M) = Θ x) ∧ (∀ y : {y | f y ≤ c - ε}, f y ≤ a → (r y : M) = y) ∧
          ∃ e : ↑(pushout (TopCat.ofHom (ContinuousMap.inclusion
                (h.negativeSphereBundle_subset_negativeDiscBundle hn P g.toRiemannianMetric ε)))
              (TopCat.ofHom (r.comp α))) ≃ₕ {y | f y ≤ b},
            ∀ z, (e (pushout.inr (TopCat.ofHom (ContinuousMap.inclusion
                (h.negativeSphereBundle_subset_negativeDiscBundle hn P g.toRiemannianMetric ε)))
              (TopCat.ofHom (r.comp α)) z) : M) = z := by
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set gR := g.toRiemannianMetric
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ?_⟩
  -- A width `ε` below `ε₀` and within the band `[a, b]`.
  set ε := min (ε₀ / 2) (min (c - a) (b - c))
  have hε : 0 < ε := lt_min (half_pos hε₀) (lt_min (sub_pos.2 hac) (sub_pos.2 hcb))
  have hεa : a ≤ c - ε := by
    linarith [(min_le_right (ε₀ / 2) _).trans (min_le_left (c - a) (b - c))]
  have hεb : c + ε ≤ b := by
    linarith [(min_le_right (ε₀ / 2) _).trans (min_le_right (c - a) (b - c))]
  -- Attach `D_ε` to `M_{c-ε}`, giving a space homotopy equivalent to `M_{c+ε}`.
  obtain ⟨hD, ρ, hρ, ⟨R⟩⟩ := hmain ε ⟨hε, (min_le_left _ _).trans_lt (half_lt_self hε₀)⟩
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
    fun x hx ↦ hcrit ⟨hx.1, Icc_subset_Icc (by linarith) (by linarith) hx.2⟩
  obtain ⟨α, hα, e₁, he₁⟩ :=
    h.exists_homotopyEquiv_pushout_of_deformation hn hfs hε hdim g Θ hΘf hD ρ hρ R
  -- Move the attachment across the collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]`: the critical
  -- points of the band lie on `i`, on the level `c`.
  obtain ⟨r, hr, E, hE⟩ :=
    exists_homotopyEquiv_pushout_comp_sublevelRetraction_of_isCompact_preimage_Icc hfs hεa
      (by linarith) hεb hcompact fun x hx hxab ↦ by
        obtain ⟨y, rfl⟩ := hcrit ⟨hx, hxab⟩
        rw [hc y]
        exact ⟨by linarith, by linarith⟩
    (TopCat.ofHom (ContinuousMap.inclusion
      (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)))
    (IsEmbedding.inclusion (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε))
    (h.hasHomotopyExtensionProperty_negativeSphereBundle hn hfs hdim g ε) (TopCat.ofHom α) e₁ he₁
  refine ⟨ε, hε, hεa, hεb, hD, α, r, hα, hr, ?_⟩
  rw [TopCat.ofHom_comp]
  exact ⟨E, hE⟩

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

end TauCeti
