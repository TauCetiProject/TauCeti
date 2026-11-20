/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Adjunction
public import TauCeti.Geometry.Manifold.Morse.Bott.Homology

/-!
# The relative homology across a Morse–Bott level is that of the negative normal bundle

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on the
level `f = c`, with Morse index `r` at every point, and let `g` be a smooth fibre metric on its
normal bundle `ν`. The negative normal spaces `ν⁻ s` relative to `g`, on which the normal Hessian
`Hessₛ` is negative definite, form a smooth subbundle of `ν` of rank `r`, the **negative normal
bundle** (`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`,
in the namespace `TauCeti.SmoothEmbedding`). Write `M_t = {f ≤ t}`. Crossing the level attaches the
negative disc bundle `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}` along the negative sphere bundle
`S_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) = ε}` through a Morse–Bott normal form `Θ`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`).

This file identifies `D_ε` and `S_ε` with the disc and sphere bundles of a fibre gauge on the
negative normal bundle, as a vector bundle in its own right. The gauge is
`ρ_ε (v) = √(-½ Hessₛ (v, v) / ε)` (`IsCriticalSubmanifold.negativeNormalGauge`): it is continuous,
positively homogeneous on each fibre and positive off the zero section, since the normal Hessian is
negative definite on `ν⁻` (`IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge`), and its disc
and sphere bundles are carried onto `D_ε` and `S_ε` by the inclusion of `ν⁻` into `ν`
(`IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge`,
`IsCriticalSubmanifold.mem_gaugeSphereBundle_negativeNormalGauge`).

With this gauge, the attachment theorem for disc bundles of vector bundles
(`TauCeti.exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle`) applies to the
attachment of `D_ε`: the normal form `Θ`, restricted to the negative normal bundle, induces a map of
pairs `(D_{ρ_ε}(ν⁻), S_{ρ_ε}(ν⁻)) ⟶ (M_{c+ε}, M_{c-ε})` which is an isomorphism on relative
singular homology in every degree
(`IsNondegenerateCriticalSubmanifold.exists_isIso_singularHomologyMap_negativeNormalGauge`). The
disc-sphere pair of a fibre gauge has the homology of the Thom pair `(ν⁻, ν⁻₀)`, `ν⁻₀` the
complement of the zero section, so for regular levels `a < c < b` around the critical level with
compact band `f⁻¹[a, b]` whose critical points lie on the submanifold,

`Hₙ(M_b, M_a) ≅ Hₙ(ν⁻, ν⁻₀)`

for coefficients in any abelian category with coproducts
(`IsNondegenerateCriticalSubmanifold.nonempty_singularHomology_sublevelPair_iso_thomPair`). This is
the input of the Thom isomorphism, which identifies the homology of the Thom pair of the rank `r`
bundle `ν⁻` with the homology of `S` shifted by `r` and twisted by the orientation of `ν⁻`; for
an isolated nondegenerate critical point of index `r` the Thom pair is `(ℝʳ, ℝʳ ∖ {0})`.

## Main definitions

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalGauge`: the fibre gauge
  `v ↦ √(-½ Hessₛ (v, v) / ε)` on the negative normal spaces, whose disc bundle is the negative disc
  bundle of size `ε`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isIso_singularHomologyMap_negativeNormalGauge`: the Morse–Bott normal form induces
  isomorphisms `Hₙ(D_{ρ_ε}(ν⁻), S_{ρ_ε}(ν⁻)) ≅ Hₙ(M_{c+ε}, M_{c-ε})`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`: the relative homology `Hₙ(M_b, M_a)`
  across the level of a compact Morse–Bott submanifold is that of the Thom pair of its negative
  normal bundle.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle Function Set Topology CategoryTheory Limits
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

namespace SmoothEmbedding

section Gauge

variable {E S : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0) {P F' : Type*}

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The **gauge of the negative disc bundle** of size `ε` of a critical submanifold, relative to a
fibre metric `g` on its normal spaces: the function `v ↦ √(-½ Hessₛ (v, v) / ε)` on the total space
of the negative normal spaces `ν⁻ s`, where `Hessₛ` is the normal Hessian. For `ε > 0` it is a
fibre gauge (`IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge`) whose disc and sphere
bundles are the negative disc and sphere bundles of size `ε`
(`IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge`). The model fibre `F'` of the
total space plays no role. -/
def negativeNormalGauge (F' : Type*) (ε : ℝ) :
    TotalSpace F' (fun s ↦ h.negativeNormalSpace hn g s) → ℝ :=
  fun v ↦ √(-(2⁻¹ * h.normalHessian hn v.proj v.2 v.2) / ε)

@[simp]
theorem negativeNormalGauge_apply {ε : ℝ}
    (v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s) :
    h.negativeNormalGauge hn g F' ε v = √(-(2⁻¹ * h.normalHessian hn v.proj v.2 v.2) / ε) :=
  (rfl)

variable {h g}

/-- A vector of the negative normal bundle lies in the disc bundle of the gauge of size `ε > 0`
exactly when, as a normal vector, it lies in the negative disc bundle of size `ε`. -/
theorem mem_gaugeDiscBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε)
    {v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s} :
    v ∈ gaugeDiscBundle (h.negativeNormalGauge hn g F' ε) ↔
      (⟨v.proj, v.2⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeDiscBundle hn P g ε := by
  rw [mem_gaugeDiscBundle, negativeNormalGauge_apply, Real.sqrt_le_one, div_le_one hε,
    mem_negativeDiscBundle]
  exact (and_iff_right v.2.2).symm

/-- A vector of the negative normal bundle lies in the sphere bundle of the gauge of size `ε > 0`
exactly when, as a normal vector, it lies in the negative sphere bundle of size `ε`. -/
theorem mem_gaugeSphereBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε)
    {v : TotalSpace F' fun s ↦ h.negativeNormalSpace hn g s} :
    v ∈ gaugeSphereBundle (h.negativeNormalGauge hn g F' ε) ↔
      (⟨v.proj, v.2⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈
        h.negativeSphereBundle hn P g ε := by
  rw [mem_gaugeSphereBundle, negativeNormalGauge_apply, Real.sqrt_eq_one, div_eq_one_iff_eq hε.ne',
    mem_negativeSphereBundle]
  exact (and_iff_right v.2.2).symm

variable (h g) in
/-- The inclusion of the negative normal bundle into the normal bundle carries the disc bundle of
the gauge of size `ε > 0` onto the negative disc bundle of size `ε`. -/
theorem image_gaugeDiscBundle_negativeNormalGauge {ε : ℝ} (hε : 0 < ε) :
    (fun v : TotalSpace F' (fun s ↦ h.negativeNormalSpace hn g s) ↦
        (⟨v.proj, v.2⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn)) ''
      gaugeDiscBundle (h.negativeNormalGauge hn g F' ε) = h.negativeDiscBundle hn P g ε := by
  ext x
  refine ⟨fun ⟨v, hv, hvx⟩ ↦ hvx ▸ (mem_gaugeDiscBundle_negativeNormalGauge hn hε).1 hv,
    fun hx ↦ ⟨⟨x.proj, ⟨x.2, mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx⟩⟩,
      (mem_gaugeDiscBundle_negativeNormalGauge hn hε).2 hx, rfl⟩⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] [IsManifold J 1 S]

variable (h g) in
/-- **The gauge of the negative disc bundle is a fibre gauge.** Let `i` be a critical submanifold
of a function `f` which is `C²` along it, with a fibre metric `g` on its normal bundle, and give the
negative normal spaces the topology of a subspace of the normal bundle. For `ε > 0` the function
`v ↦ √(-½ Hessₛ (v, v) / ε)` is continuous, positively homogeneous on each fibre and positive off
the zero section, since the normal Hessian is negative definite on the negative normal spaces. -/
theorem isFiberGauge_negativeNormalGauge (hk : 1 ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) 2 f (i s))
    (hdim : Module.finrank ℝ E'' = Module.finrank ℝ E - Module.finrank ℝ E') {ε : ℝ}
    (hε : 0 < ε) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := subbundleTopology E'' (F' := F') (h.negativeNormalSpace hn g)
    IsFiberGauge (h.negativeNormalGauge hn g F' ε) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := subbundleTopology E'' (F' := F') (h.negativeNormalSpace hn g)
  have : IsManifold I (0 + 2) M := by simpa using ‹IsManifold I 2 M›
  have : IsManifold J (0 + 1) S := by simpa using ‹IsManifold J 1 S›
  have hH := h.contMDiff_normalHessian_apply_self hn (k := 0) (by simpa using hk)
    (fun s ↦ by simpa using hf s) hdim
  rw [show h.negativeNormalGauge hn g F' ε = _ from funext (negativeNormalGauge_apply hn h g)]
  refine isFiberGauge_sqrt ?_ (fun {t} _ v ↦ ?_) fun {v} hv ↦ ?_
  · -- The quadratic form of the normal Hessian is continuous on the normal bundle, which contains
    -- the negative normal spaces as a subspace.
    exact ((continuous_const.mul (hH.continuous.comp
      (isEmbedding_totalSpace_subbundle E'' F' _).continuous)).neg).div_const ε
  · simp only [TotalSpace.mk', Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g v.2.2
      fun h0 ↦ hv (Subtype.ext h0)
    exact div_pos (by linarith) hε

end IsCriticalSubmanifold

end Gauge

section Attachment

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {E' H' P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **Crossing the level of a compact Morse–Bott submanifold attaches the disc bundle of its
negative normal bundle.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth
function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S`
compact and nonempty, `f = c` along `i` and Morse index `r` at every point of `i`, and let `g` be a
smooth fibre metric on its normal bundle. Give the total space of the negative normal spaces
relative to `g` the topology of a subspace of the normal bundle; with it they form a vector bundle
`ν⁻` of rank `r` over `S` (`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then `Θ` induces a map of pairs
`(D_ρ(ν⁻), S_ρ(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` from the disc-sphere pair of the gauge
`ρ = IsCriticalSubmanifold.negativeNormalGauge` of size `ε` on the negative normal bundle `ν⁻`,
which is an isomorphism on relative singular homology, with coefficients in any abelian category
with coproducts, in every degree. -/
theorem exists_isIso_singularHomologyMap_negativeNormalGauge [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        ∃ ψ : gaugeDiscSpherePair
            (h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε) ⟶
            sublevelPair f (a := c - ε) (b := c + ε) (by linarith),
          (∀ v : gaugeDiscBundle (h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε),
            Subtype.val (TopPair.Hom.fst ψ v) = Θ ⟨v.1.proj, v.1.2⟩) ∧
          ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ),
            IsIso (TopPair.singularHomologyMap ψ R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  set D := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  obtain ⟨hDΘ, ret, -, ⟨G⟩⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact hcrit
  set ρ := h.negativeNormalGauge hn g.toRiemannianMetric (Fin r → ℝ) ε
  -- The inclusion `ι` of the negative normal bundle into the normal bundle carries `D_ρ` onto `D`.
  set ι := fun v : TotalSpace (Fin r → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ↦
    (⟨v.proj, v.2⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn)
  have hι : IsEmbedding ι := isEmbedding_totalSpace_subbundle P _ _
  have hdisc : ι '' gaugeDiscBundle ρ = D :=
    IsCriticalSubmanifold.image_gaugeDiscBundle_negativeNormalGauge hn _ _ hε
  have hΘD (x) (hx : x ∈ D) : f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2 :=
    hΘf x (hDΘ hx)
  -- `Θ ∘ ι` is continuous and injective on the compact set `D_ρ`, so it embeds it as a closed set.
  have : T2Space S := i.isEmbedding.t2Space
  have : CompactSpace (gaugeDiscBundle ρ) := isCompact_iff_compactSpace.1 <|
    hι.isCompact_iff.2 (hdisc ▸ h.isCompact_negativeDiscBundle hn hfs hdim g ε)
  have hmaps : MapsTo ι (gaugeDiscBundle ρ) D := hdisc ▸ mapsTo_image ι _
  have hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict (Θ ∘ ι)) :=
    Continuous.isClosedEmbedding ((Θ.contMDiffOn.continuousOn.mono hDΘ).comp_continuous
      (hι.continuous.comp continuous_subtype_val) fun v ↦ hmaps v.2)
      fun v w hvw ↦ Subtype.ext (hι.injective (Θ.injOn (hDΘ (hmaps v.2)) (hDΘ (hmaps w.2)) hvw))
  refine exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle
    (IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge hn h.toIsCriticalSubmanifold _ (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim hε)
    (sublevel_mono f (by linarith)) (isClosed_le hfs.continuous continuous_const) hg
    (by rw [image_comp, hdisc]) ?_ (fun v hv ↦ ?_) ret G
  · -- On `D` the normal form gives `f ∘ Θ ≤ c`.
    rintro _ ⟨x, hx, rfl⟩
    exact (IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle hΘD hx).trans (by linarith)
  · -- A point of `D_ρ` is carried into `{f ≤ c - ε}` exactly when it lies in `S_ρ`.
    rw [IsCriticalSubmanifold.mem_gaugeSphereBundle_negativeNormalGauge hn hε (P := P)]
    exact (IsCriticalSubmanifold.mem_negativeSphereBundle_iff_apply_le hΘD
      ((IsCriticalSubmanifold.mem_gaugeDiscBundle_negativeNormalGauge hn hε).1 hv)).symm

/-- **The relative homology across the level of a compact Morse–Bott submanifold is that of the
Thom pair of its negative normal bundle.** Let `i : S → M` be a nondegenerate critical submanifold
of a smooth function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless
manifold, with `S` nonempty, `f = c` along `i` and Morse index `r` at every point of `i`, and let
`g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the band
`f⁻¹[a, b]` is compact and all its critical points lie on `i`. Give the total space of the
negative normal spaces relative to `g` the topology of a subspace of the normal bundle; with it
they form a vector bundle `ν⁻` of rank `r` over `S`
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).

Then the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to the relative homology
`Hₙ(ν⁻, ν⁻₀)` of the Thom pair of `ν⁻`, with `ν⁻₀` the complement of the zero section, for
coefficients in any abelian category with coproducts and in every degree. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
      (thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
        ).singularHomology R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨Θ, -, -, -, ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_negativeNormalGauge hn hfs hc hdim g hr
  -- Choose a width `ε` below `ε₀` with `[c - ε, c + ε] ⊆ [a, b]`.
  set ε := min ε₀ (min (c - a) (b - c)) / 2
  have hm : 0 < min ε₀ (min (c - a) (b - c)) := lt_min hε₀ (lt_min (by linarith) (by linarith))
  have hε : 0 < ε := half_pos hm
  have hεm : ε < min ε₀ (min (c - a) (b - c)) := half_lt_self hm
  -- Every critical point of the band lies on the submanifold, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨s, rfl⟩ := hcrit ⟨hx, hfx⟩
    exact hc s
  obtain ⟨hε', hcompact'⟩ :=
    Icc_subset_and_isCompact_preimage_Icc hfs.continuous hcompact
      (hεm.trans_le (min_le_right _ _)).le
  obtain ⟨φ, -, hφ⟩ := hmain ε hε (hεm.trans_le (min_le_left _ _)) hcompact'
    fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  have hρ := IsCriticalSubmanifold.isFiberGauge_negativeNormalGauge hn h.toIsCriticalSubmanifold
    g.toRiemannianMetric (F' := Fin r → ℝ) (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim hε
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  exact ⟨singularHomologySublevelPairIsoSymmetricBand hfs hac hcb hcompact hlev hε
    (hεm.trans_le (min_le_right _ _)).le R n ≪≫ (@asIso _ _ _ _ _ (hφ R n)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n)⟩

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

end TauCeti
