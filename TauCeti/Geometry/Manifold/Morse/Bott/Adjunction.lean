/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Topology.Homotopy.Extension.Pushout
import TauCeti.Geometry.Manifold.Morse.Deformation.Attachment
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Topology.VectorBundle.Smul

/-!
# Crossing a Morse–Bott level between regular levels attaches the negative disc bundle

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c`, and let `g` be a smooth fibre metric on its normal
bundle. Write `M_t = {f ≤ t}`, and let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and
its critical points all lie on `i`. This file shows that `M_b` is homotopy equivalent to `M_a` with
the negative disc bundle of `i` attached along its sphere bundle, by a homotopy equivalence which
is the inclusion `M_a → M_b` on `M_a`
(`IsNondegenerateCriticalSubmanifold.exists_homotopyEquiv_pushout_negativeDiscBundle`, in the
namespace `TauCeti.SmoothEmbedding`). This is Bott's attachment theorem between arbitrary regular
levels around `c`: the space `M_a ∪_α D_ε` is the pushout in `TopCat` of the inclusion of the
negative sphere bundle `S_ε` into the negative disc bundle `D_ε`
(`IsCriticalSubmanifold.negativeSphereBundle`, `IsCriticalSubmanifold.negativeDiscBundle`) and of
an attaching map `α : S_ε → M_a`. For an isolated nondegenerate critical point the base is a
point, the negative disc bundle is a disc of dimension the index, and this is Milnor's attachment
of a cell (`TauCeti.IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace`).

The attaching map is explicit. A Morse–Bott normal form `Θ` on the normal bundle, with
`f (Θ v) = c + ½ Hessₛ (v, v)`, carries `S_ε` into the level `f⁻¹(c - ε)` for a small width
`ε > 0`, and `α` is `Θ` on `S_ε` followed by a retraction `r` of `M_{c-ε}` onto `M_a` along the
band `f⁻¹[a, c - ε]`, which contains no critical point.

The homotopy equivalence is the composite of three. First, `M_{c-ε} ∪ Θ(D_ε)` is the pushout of
`S_ε → D_ε` along `Θ : S_ε → M_{c-ε}`, since it is covered by the closed set `M_{c-ε}` and the
compact set `Θ(D_ε)` (`IsNondegenerateCriticalSubmanifold.isCompact_negativeDiscBundle`), which
meet exactly in `Θ(S_ε)` (`TauCeti.TopCat.exists_isPushout_union_image`). By the
attachment theorem it is a strong deformation retract of `M_{c+ε}`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`).
Second, the inclusion `M_{c+ε} → M_b` is a homotopy equivalence across the band `f⁻¹[c + ε, b]`
(`TauCeti.exists_sublevelHomotopyEquiv`). Third, `r` is a homotopy equivalence with homotopy inverse
the inclusion, and attaching along a cofibration is homotopy invariant under a change of base
(`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_pushout`). The inclusion `S_ε → D_ε` is a
cofibration because the cylinder over `D_ε` retracts radially onto its bottom and its part over
`S_ε`, fibre by fibre (`TauCeti.hasHomotopyExtensionProperty_setOf_eq_one`). The last two steps
move the attachment across the regular collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]`, as in the
Morse case (`TauCeti.exists_homotopyEquiv_pushout_comp_sublevelRetraction`).

This is the step by which the sublevels of a Morse–Bott function are built, one critical
submanifold at a time, along a sequence of regular levels separating its critical values.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

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

open Bundle Function Set Filter Topology CategoryTheory Limits
open scoped ContDiff Manifold ContinuousMap

universe u

namespace TauCeti

namespace SmoothEmbedding

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
    fun x ↦ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) with hq
  have hqc : Continuous q :=
    (continuous_const.mul (h.contMDiff_normalHessian_apply_self hn
      (k := ∞) (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim).continuous).neg
  have hqsmul (c : ℝ) (x : TotalSpace P (fun s ↦ i.NormalSpace s hn)) :
      q (TotalSpace.mk' P x.proj (c • x.2)) = c ^ 2 * q x := by
    simp only [hq, TotalSpace.mk', map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- For `ε ≤ 0` every point of `D_ε` lies on `S_ε`, since `q ≥ 0` on the negative normal spaces.
  rcases le_or_gt ε 0 with hε | hε
  · convert isClopen_univ.hasHomotopyExtensionProperty
    refine eq_univ_of_forall fun x ↦ ⟨⟨x, ?_⟩, rfl⟩
    have hx := (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 x.2
    refine (IsCriticalSubmanifold.mem_negativeSphereBundle hn).2 ⟨hx.1, le_antisymm hx.2 ?_⟩
    linarith [h.normalHessian_apply_self_nonpos_of_mem_negativeNormalSpace hn gR hx.1]
  have hrange : range (ContinuousMap.inclusion
      (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)) =
      {x : h.negativeDiscBundle hn P gR ε | √(q x / ε) = 1} := by
    refine (range_inclusion (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)).trans ?_
    ext x
    refine (IsCriticalSubmanifold.mem_negativeSphereBundle hn).trans ?_
    rw [mem_ofPred_eq, Real.sqrt_eq_one, div_eq_one_iff_eq hε.ne']
    exact and_iff_right ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 x.2).1
  rw [hrange]
  refine hasHomotopyExtensionProperty_setOf_eq_one (ρ := fun x ↦ √(q x / ε))
    (Real.continuous_sqrt.comp (hqc.div_const ε)).continuousOn (fun x hx ↦ ⟨Real.sqrt_nonneg _,
      Real.sqrt_le_one.2 ((div_le_one hε).2 ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1
        hx).2)⟩) (φ := fun c x ↦ TotalSpace.mk' P x.proj (c • x.2))
    (VectorBundle.continuous_smul ℝ P _).continuousOn (fun x hx c hc hcx ↦ ?_) fun x _ ↦ by
      simp [TotalSpace.mk']
  -- Rescaling by `c ≥ 0` multiplies the gauge by `c`.
  have hρ : √(q (TotalSpace.mk' P x.proj (c • x.2)) / ε) = c * √(q x / ε) := by
    rw [hqsmul, mul_div_assoc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  refine ⟨(IsCriticalSubmanifold.mem_negativeDiscBundle hn).2
    ⟨Submodule.smul_mem _ c ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx).1, ?_⟩, hρ⟩
  rw [← hρ, Real.sqrt_le_one, div_le_one hε] at hcx
  exact hcx

end IsCriticalSubmanifold

end Adjunction

section Attachment

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
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) →
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
  -- On the negative disc bundle `f ∘ Θ = c - q`, `q v = -½ Hessₛ (v, v)`, with `0 ≤ q ≤ ε`.
  have hfD {x} (hx : x ∈ h.negativeDiscBundle hn P gR ε) :
      f (Θ x) = c - -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) := by
    rw [hΘf x (hD hx)]
    ring
  have hq0 {x} (hx : x ∈ h.negativeDiscBundle hn P gR ε) :
      0 ≤ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) := by
    linarith [h.normalHessian_apply_self_nonpos_of_mem_negativeNormalSpace hn gR
      ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx).1]
  -- So `Θ(D_ε)` lies in `M_c` and meets `M_{c-ε}` in `Θ(S_ε)`.
  obtain ⟨α, χ, j, hα, hj, sq⟩ := TopCat.exists_isPushout_union_image
    (F := {y | f y ≤ c - ε}) (U := {y | f y ≤ c + ε})
    (isClosed_le hfs.continuous continuous_const) (fun y hy ↦ by
      rw [mem_ofPred_eq] at hy ⊢
      linarith)
    (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε)
    (h.isCompact_negativeDiscBundle hn hfs hdim g ε) (Θ.contMDiffOn.continuousOn.mono hD)
    (Θ.toPartialEquiv.injOn.mono hD) (fun x hx ↦ by
      rw [mem_ofPred_eq]
      linarith [hfD hx, hq0 hx]) fun x hx ↦ by
      rw [mem_ofPred_eq, hfD hx, IsCriticalSubmanifold.mem_negativeSphereBundle]
      have := ((IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx)
      exact ⟨fun h' ↦ ⟨this.1, le_antisymm this.2 (by linarith)⟩, fun h' ↦ by linarith [h'.2]⟩
  -- The pushout is identified with `M_{c-ε} ∪ Θ(D_ε)` compatibly with the inclusions of
  -- `M_{c-ε}`, and that union is a strong deformation retract of `M_{c+ε}`.
  have hinr (w : {y | f y ≤ c - ε}) : TopCat.homeoOfIso sq.isoPushout.symm (pushout.inr
      (TopCat.ofHom (ContinuousMap.inclusion
        (h.negativeSphereBundle_subset_negativeDiscBundle hn P gR ε))) (TopCat.ofHom α) w) =
        j w := by
    rw [TopCat.homeoOfIso_apply, Iso.symm_hom, ← ConcreteCategory.comp_apply,
      sq.inr_isoPushout_inv, TopCat.ofHom_apply]
  refine ⟨α, hα, (TopCat.homeoOfIso sq.isoPushout.symm).toHomotopyEquiv.trans
    (ContinuousMap.HomotopyEquiv.ofRetraction _ ρ hρ R.toHomotopy), fun z ↦ ?_⟩
  rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.HomotopyEquiv.coe_ofRetraction_apply]
  exact (congrArg Subtype.val (hinr z)).trans (hj z)

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
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
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
