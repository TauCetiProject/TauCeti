/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Localized variations of smooth almost complex structures at injective points

Transversality for pseudoholomorphic spheres in a symplectic manifold `M` varies the almost
complex structure `J` of the target. A variation of `J` is a section `Y` of the endomorphism
bundle `End(TM)` which anticommutes with `J` at every point; along a map `u` it changes the
Cauchy–Riemann operator by the term `Y(u) w` for the relevant tangent field `w` along `u`, for
instance `w = ∂ₜu` for a holomorphic sphere or `w = ∂ₜu - X_{K_t}(u)` for an inhomogeneous
equation. The universal linearized operator is onto as soon as no nonzero cokernel element `η`, a
covector field along `u`, annihilates all of these terms. A variation of a domain-independent `J`
is a function of the target point alone, so it is localized near `u(z₀)`, and an *injective
point* `z₀` (points of the domain whose image is close to `u(z₀)` are close to `z₀`) turns this
into a localization in the domain.

This file proves the resulting pairing statement on the actual tangent bundle of a
finite-dimensional real manifold `M`, for a smooth almost complex structure
`J : SmoothAlmostComplexStructure I M` and a domain `S` which is any locally compact Hausdorff
space with a measure that is positive on open sets and finite on compact sets. The map
`u : S → M` carries a tangent field `w z ∈ T_{u z} M` and a covector field
`η z ∈ T*_{u z} M`, continuous near `z₀` as maps into the tangent and cotangent bundles. If
`w z₀ ≠ 0` and `η z₀ ≠ 0`, then for every neighbourhood `W` of `u z₀` there is a smooth section
`Y` of `End(TM)` with compact support in `W` such that

`0 < ∫ η z (Y (u z) (w z)) ∂μ`.

There are two versions, one for each tangent condition:

* `SmoothAlmostComplexStructure.exists_contMDiffSection_mem_tangentSpace_integral_pos`: `Y x`
  anticommutes with `J x` at every point, the variations of tame structures;
* `SmoothTwoForm.IsNondegenerate.exists_contMDiffSection_mem_compatibleTangentSpace_integral_pos`:
  if `J` preserves a nondegenerate two-form `σ` and is tamed by `σ` at `u z₀`, then `Y x` moreover
  is skew-adjoint for `σ_x`, the variations of compatible structures.

Their contrapositives,
`SmoothAlmostComplexStructure.eq_zero_of_forall_mem_tangentSpace_integral_eq_zero` and
`SmoothTwoForm.IsNondegenerate.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero`,
say that a covector field annihilating all such variations vanishes at every injective point
where `w ≠ 0`.

The variation is `Y = ρ • (A + J A J) / 2` for a smooth bump function `ρ` at `u z₀` and a smooth
section `A` of `End(TM)` whose value at `u z₀` is a tangent vector at `J (u z₀)` with
`η z₀ (A (w z₀)) > 0`. Averaging with the conjugate by `J` makes the section anticommute with `J`
everywhere (`AlmostComplexStructure.add_mul_mul_mem_tangentSpace`), without changing its value at
`u z₀`. On a manifold there are no constant endomorphism fields: `A` is obtained from a section
with prescribed value at `u z₀` (`ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset`).
For the compatible version this section `C` is first replaced by its `σ`-skew part
`(σ♭)⁻¹ ∘ (β + βᵀ) / 2`, where `β = σ(C ·, ·)` and `σ♭` is the flat map of `σ`: skew-adjointness
is a pointwise condition for the varying form `σ_x`, so a section with a skew-adjoint value at one
point need not be skew-adjoint elsewhere. Averaging with `J` then preserves skew-adjointness
(`SymplecticForm.Invariant.add_mul_mul_mem_compatibleTangentSpace_of_skew`).

These are the manifold forms of
`AlmostComplexStructure.exists_contDiff_mem_tangentSpace_integral_pos` and
`SymplecticForm.exists_contDiff_mem_compatibleTangentSpace_integral_pos`, where the target is a
vector space with a constant form. They are statements about one cokernel pairing; they do not
assert density of injective points of simple curves, nor any Sobolev or Fredholm surjectivity.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the proof of Proposition 3.2.1, where a nonzero
  cokernel element is paired with a variation of `J` supported near an injective point).
-/

public section

open Bundle Filter MeasureTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] {μ : Measure S} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  {J : SmoothAlmostComplexStructure I M} {u : S → M} {w : (z : S) → TangentSpace I (u z)}
  {η : (z : S) → TangentSpace I (u z) →L[ℝ] ℝ} {z₀ : S}

/-- The average `(A + J A J) / 2` of a section `A` of `End(TM)` with its conjugate by `J`. -/
private noncomputable def average (J : SmoothAlmostComplexStructure I M)
    (A : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯ :=
  (2⁻¹ : ℝ) • (A + J.toEndomorphism.clmComp (A.clmComp J.toEndomorphism))

omit [T2Space S] [FiniteDimensional ℝ E] [T2Space M] in
private theorem coe_average_apply
    (A : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M) :
    (average J A x : Module.End ℝ (TangentSpace I x)) =
      (2⁻¹ : ℝ) • ((A x : Module.End ℝ (TangentSpace I x)) +
        (J.almostComplexStructureAt x).toLinearMap * A x *
          (J.almostComplexStructureAt x).toLinearMap) := by
  ext v
  simp [average]

omit [T2Space S] [FiniteDimensional ℝ E] [T2Space M] in
/-- The average of a section with its conjugate by `J` anticommutes with `J` at every point. -/
private theorem average_mem_tangentSpace
    (A : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M) :
    (average J A x : Module.End ℝ (TangentSpace I x)) ∈
      (J.almostComplexStructureAt x).tangentSpace := by
  rw [coe_average_apply]
  exact Submodule.smul_mem _ _ ((J.almostComplexStructureAt x).add_mul_mul_mem_tangentSpace _)

omit [T2Space S] [LocallyCompactSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
  [FiniteDimensional ℝ E] [T2Space M] in
/-- A section of `End(TM)`, evaluated along `u` on a tangent field and paired with a covector
field, is continuous wherever both fields are continuous into their bundles. -/
private theorem continuousAt_apply_apply
    (B : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) {z : S}
    (hw : ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z) :
    ContinuousAt (fun z ↦ η z (B (u z) (w z))) z := by
  have hu : ContinuousAt u z :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hw
  have hBw := (B.contMDiff.continuous.continuousAt.comp hu).clm_bundle_apply hw
  have h := ContinuousAt.clm_bundle_apply (E₂ := Bundle.Trivial M ℝ) hη hBw
  exact continuous_snd.continuousAt.comp
    ((Bundle.Trivial.homeomorphProd M ℝ).continuous.continuousAt.comp h)

/-- Cutting off the average of a section `A` by a bump function at `u z₀`. If `A (u z₀)`
anticommutes with `J (u z₀)` and pairs positively with `η z₀` at `w z₀`, a suitable cutoff gives
a compactly supported section in `W` whose pairing along `u` has positive integral. The cutoff is
supported in a neighbourhood of `u z₀` whose preimage lies in a compact neighbourhood of `z₀` on
which the uncut pairing is positive. -/
private theorem exists_localizedVariation
    (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    {A : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯}
    (hA : (A (u z₀) : Module.End ℝ (TangentSpace I (u z₀))) ∈
      (J.almostComplexStructureAt (u z₀)).tangentSpace)
    (hpos : 0 < η z₀ (A (u z₀) (w z₀))) {W : Set M} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ ρ : C^∞⟮I, M; ℝ⟯, IsCompact (ρ • average J A).tsupport ∧
      (ρ • average J A).tsupport ⊆ W ∧
      0 < ∫ z, η z ((ρ • average J A) (u z) (w z)) ∂μ := by
  -- The pairing before the cutoff, and its value `η z₀ (A (w z₀))` at `z₀`.
  set G : S → ℝ := fun z ↦ η z (average J A (u z) (w z))
  have hG₀ : G z₀ = η z₀ (A (u z₀) (w z₀)) := by
    have h := LinearMap.congr_fun (congrArg (fun B : Module.End ℝ (TangentSpace I (u z₀)) ↦ B)
      (coe_average_apply (J := J) A (u z₀))) (w z₀)
    rw [AlmostComplexStructure.mul_mul_eq_of_mem_tangentSpace hA, ← two_smul ℝ, smul_smul,
      inv_mul_cancel₀ (two_ne_zero' ℝ), one_smul] at h
    simp only [G, ContinuousLinearMap.coe_coe] at h ⊢
    rw [h]
  -- A compact neighbourhood `K` of `z₀` on which the data are continuous and `G` is positive,
  -- and a neighbourhood `W₀` of `u z₀` whose preimage lies in `K`.
  have hev : ∀ᶠ z in 𝓝 z₀,
      (ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z ∧
        ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z) ∧ 0 < G z :=
    have hGc : ContinuousAt G z₀ :=
      continuousAt_apply_apply (average J A) hw.self_of_nhds hη.self_of_nhds
    (hw.and hη).and (hGc.eventually (lt_mem_nhds (hG₀ ▸ hpos)))
  obtain ⟨K, hKn, hKsub, hK⟩ := local_compact_nhds hev
  obtain ⟨W₀, hW₀, hW₀K⟩ := mem_comap.1 (hinj hKn)
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (u z₀)).mem_iff.1
    (inter_mem hW₀ hW)
  let ρ' : C^∞⟮I, M; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  have hsupp : (ρ' • average J A).tsupport ⊆ tsupport ρ :=
    (ContMDiffSection.tsupport_smul_function_subset _ _).trans inter_subset_left
  refine ⟨ρ', ρ.hasCompactSupport.isCompact.of_isClosed_subset
    (ContMDiffSection.isClosed_tsupport _) hsupp, hsupp.trans (hρ.trans inter_subset_right), ?_⟩
  have hF : (fun z ↦ η z ((ρ' • average J A) (u z) (w z))) = fun z ↦ ρ (u z) * G z := by
    funext z
    simp only [ContMDiffSection.smul_apply, smul_apply, map_smul,
      smul_eq_mul]
    rfl
  have hmemK : ∀ z, ρ (u z) ≠ 0 → z ∈ K := fun z hz ↦
    hW₀K (mem_preimage.2 (hρ (subset_tsupport _ hz)).1)
  have hzero : ∀ z ∉ K, ρ (u z) * G z = 0 := fun z hz ↦ by
    rw [not_not.1 (mt (hmemK z) hz), zero_mul]
  rw [hF]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := z₀) ?_
    (HasCompactSupport.intro hK hzero) (fun z ↦ ?_) (by simp [hG₀, hpos.ne'])
  · refine continuous_iff_continuousAt.2 fun z ↦ ?_
    by_cases hz : z ∈ K
    · obtain ⟨⟨hwz, hηz⟩, -⟩ := hKsub hz
      have hu : ContinuousAt u z :=
        (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hwz
      exact (ρ.contMDiff.continuous.continuousAt.comp hu).mul
        (continuousAt_apply_apply (average J A) hwz hηz)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy using (hzero y hy).symm
  · by_cases hz : ρ (u z) = 0
    · simp [hz]
    · exact mul_nonneg ρ.nonneg (hKsub (hmemK z hz)).2.le

/-- **Variations of almost complex structures detect cokernel elements at injective points.**
Let `J` be a smooth almost complex structure on `M` and let `z₀` be an injective point of
`u : S → M`, in the sense that points whose image is close to `u z₀` are close to `z₀`. Let the
tangent field `w` and the covector field `η` along `u` be continuous near `z₀` into the tangent
and cotangent bundles, with `w z₀ ≠ 0` and `η z₀ ≠ 0`. Then for any neighbourhood `W` of `u z₀`,
some smooth section `Y` of `End(TM)` with compact support in `W`, anticommuting with `J` at
every point, pairs positively with `η` along `u`: `0 < ∫ η z (Y (u z) (w z)) ∂μ`. -/
theorem exists_contMDiffSection_mem_tangentSpace_integral_pos
    (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0) (hη₀ : η z₀ ≠ 0) {W : Set M}
    (hW : W ∈ 𝓝 (u z₀)) :
    ∃ Y : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯,
      IsCompact Y.tsupport ∧ Y.tsupport ⊆ W ∧
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈ (J.almostComplexStructureAt x).tangentSpace) ∧
      0 < ∫ z, η z (Y (u z) (w z)) ∂μ := by
  obtain ⟨e, he⟩ : ∃ e, η z₀ e ≠ 0 := by simpa using DFunLike.ne_iff.1 hη₀
  obtain ⟨A₀, hA₀, hA₀w⟩ :=
    (J.almostComplexStructureAt (u z₀)).exists_mem_tangentSpace_apply_eq hw₀ ((η z₀ e)⁻¹ • e)
  obtain ⟨A, hA, -, -⟩ := ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset (n := ⊤)
    (I := I) (F := E →L[ℝ] E) (V := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (u z₀)
    (LinearMap.toContinuousLinearMap A₀) univ_mem
  obtain ⟨ρ, hYc, hYW, hpos⟩ := exists_localizedVariation (μ := μ) (J := J) hw hη hinj (A := A)
    (by simpa [hA] using hA₀) (by simp [hA, hA₀w, he]) hW
  refine ⟨_, hYc, hYW, fun x ↦ ?_, hpos⟩
  rw [ContMDiffSection.smul_apply, ContinuousLinearMap.toLinearMap_smul]
  exact Submodule.smul_mem _ _ (average_mem_tangentSpace A x)

/-- **A covector field annihilating all variations of an almost complex structure vanishes at
injective points.** If `η` pairs to zero with every smooth section `Y` of `End(TM)` with compact
support in a neighbourhood `W` of `u z₀` which anticommutes with `J`, then `η z₀ = 0` at every
injective point `z₀` of `u` where `w z₀ ≠ 0`, provided `w` and `η` are continuous near `z₀` into
the tangent and cotangent bundles. -/
theorem eq_zero_of_forall_mem_tangentSpace_integral_eq_zero
    (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0) {W : Set M} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯,
      IsCompact Y.tsupport → Y.tsupport ⊆ W →
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (J.almostComplexStructureAt x).tangentSpace) →
      ∫ z, η z (Y (u z) (w z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨Y, hYc, hYW, hYJ, hpos⟩ :=
    exists_contMDiffSection_mem_tangentSpace_integral_pos (μ := μ) (J := J) hw hη hinj hw₀ hη₀ hW
  exact hpos.ne' (h Y hYc hYW hYJ)

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.SmoothTwoForm

open SmoothAlmostComplexStructure

variable {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] {μ : Measure S} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {J : SmoothAlmostComplexStructure I M} {u : S → M} {w : (z : S) → TangentSpace I (u z)}
  {η : (z : S) → TangentSpace I (u z) →L[ℝ] ℝ} {z₀ : S}

/-- Mathlib's derived `IsNormableSpace` instance on `TangentSpace I x` is stated with the model
space's `Module` instance instead of the tangent space's own one, so instance search never finds
it; restate it against the tangent space's structure. It is needed to transpose sections of
`Hom(TM, Hom(TM, ℝ))`. -/
local instance (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
  instIsNormableSpaceTangentSpace I x

/-- The bilinear forms `σ(C ·, ·)` of a section `C` of `End(TM)`. -/
private noncomputable def flatComp (σ : SmoothTwoForm I M)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯ :=
  (⟨σ.flat, σ.contMDiff_flat⟩ : Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯).clmComp C

/-- The `σ`-skew part `(C - C^†) / 2` of a section `C` of `End(TM)`, where `C^†` is the adjoint
for `σ`: it is `(σ♭)⁻¹ ∘ (β + βᵀ) / 2` for the bilinear forms `β = σ(C ·, ·)`. -/
private noncomputable def skewPart (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯ :=
  (2⁻¹ : ℝ) • ((⟨fun x ↦ (σ.flat x).inverse,
      σ.contMDiff_flat.clm_bundle_inverse hσ.isInvertible_flat⟩ :
      Cₛ^∞⟮I; (E →L[ℝ] ℝ) →L[ℝ] E,
        fun x : M ↦ (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x⟯).clmComp
    (flatComp σ C + ⟨fun x ↦ (flatComp σ C x).flip, fun x ↦ contMDiffWithinAt_univ.1
      ((flatComp σ C).contMDiff x).contMDiffWithinAt.clm_bundle_flip⟩))

omit [T2Space M] in
/-- The defining identity of the skew part: `σ(S v, w) = (σ(C v, w) + σ(C w, v)) / 2`. -/
private theorem flat_skewPart_apply (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M)
    (v w : TangentSpace I x) :
    σ.flat x (skewPart hσ C x v) w = 2⁻¹ * (σ.flat x (C x v) w + σ.flat x (C x w) v) := by
  simp [skewPart, flatComp, (hσ.isInvertible_flat x).self_apply_inverse, mul_add]

omit [T2Space M] in
/-- The skew part of a section is skew-adjoint for `σ` at every point. -/
private theorem skewPart_skew (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M)
    (v w : TangentSpace I x) :
    hσ.symplecticFormAt x (skewPart hσ C x v) w + hσ.symplecticFormAt x v (skewPart hσ C x w) =
      0 := by
  have h := (hσ.symplecticFormAt x).isAlt.neg_eq (skewPart hσ C x w) v
  simp only [IsNondegenerate.symplecticFormAt_apply, ← flat_apply] at h ⊢
  rw [← h, flat_skewPart_apply, flat_skewPart_apply]
  ring

omit [T2Space M] in
/-- The skew part does not change a value which is already skew-adjoint for `σ`. -/
private theorem skewPart_apply_of_skew (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) {x : M}
    (hC : ∀ v w, hσ.symplecticFormAt x (C x v) w + hσ.symplecticFormAt x v (C x w) = 0) :
    skewPart hσ C x = C x := by
  ext v
  refine (hσ.isInvertible_flat x).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  have h₁ := hC v w
  have h₂ := (hσ.symplecticFormAt x).isAlt.neg_eq (C x w) v
  simp only [IsNondegenerate.symplecticFormAt_apply, ← flat_apply] at h₁ h₂
  rw [flat_skewPart_apply]
  linarith

/-- **Compatible variations of almost complex structures detect cokernel elements at injective
points.** Let `σ` be a nondegenerate two-form on `M`, let `J` be a smooth almost complex
structure preserving `σ`, tamed by `σ` at `u z₀`, and let `z₀` be an injective point of
`u : S → M`. Let the tangent field `w` and the covector field `η` along `u` be continuous near
`z₀` into the tangent and cotangent bundles, with `w z₀ ≠ 0` and `η z₀ ≠ 0`. Then for any
neighbourhood `W` of `u z₀`, some smooth section `Y` of `End(TM)` with compact support in `W`,
lying in the compatible tangent space of `J` (anticommuting with `J` and skew-adjoint for `σ`) at
every point, pairs positively with `η` along `u`: `0 < ∫ η z (Y (u z) (w z)) ∂μ`. -/
theorem IsNondegenerate.exists_contMDiffSection_mem_compatibleTangentSpace_integral_pos
    (hσ : σ.IsNondegenerate) (hJσ : σ.Invariant J)
    (hJ₀ : (hσ.symplecticFormAt (u z₀)).Tames (J.almostComplexStructureAt (u z₀)))
    (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0) (hη₀ : η z₀ ≠ 0) {W : Set M}
    (hW : W ∈ 𝓝 (u z₀)) :
    ∃ Y : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯,
      IsCompact Y.tsupport ∧ Y.tsupport ⊆ W ∧
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (hσ.symplecticFormAt x).compatibleTangentSpace (J.almostComplexStructureAt x)) ∧
      0 < ∫ z, η z (Y (u z) (w z)) ∂μ := by
  have hJσ' := hσ.invariant_iff.1 hJσ
  obtain ⟨e, he⟩ : ∃ e, η z₀ e ≠ 0 := by simpa using DFunLike.ne_iff.1 hη₀
  obtain ⟨A₀, hA₀, hA₀w⟩ := (SymplecticForm.Compatible.of_tames (hJσ' (u z₀)) hJ₀
    ).exists_mem_compatibleTangentSpace_apply_eq hw₀ ((η z₀ e)⁻¹ • e)
  obtain ⟨C, hC, -, -⟩ := ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset (n := ⊤)
    (I := I) (F := E →L[ℝ] E) (V := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (u z₀)
    (LinearMap.toContinuousLinearMap A₀) univ_mem
  have hA : skewPart hσ C (u z₀) = LinearMap.toContinuousLinearMap A₀ := by
    rw [skewPart_apply_of_skew hσ C (by
      simpa [hC] using (SymplecticForm.mem_compatibleTangentSpace.1 hA₀).2), hC]
  obtain ⟨ρ, hYc, hYW, hpos⟩ := exists_localizedVariation (μ := μ) (J := J) hw hη hinj
    (A := skewPart hσ C)
    (by simpa [hA] using SymplecticForm.compatibleTangentSpace_le_tangentSpace hA₀)
    (by simp [hA, hA₀w, he]) hW
  refine ⟨_, hYc, hYW, fun x ↦ ?_, hpos⟩
  rw [ContMDiffSection.smul_apply, ContinuousLinearMap.toLinearMap_smul, coe_average_apply]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    ((hJσ' x).add_mul_mul_mem_compatibleTangentSpace_of_skew (skewPart_skew hσ C x)))

/-- **A covector field annihilating all compatible variations vanishes at injective points.**
Let `σ` be a nondegenerate two-form on `M` and let `J` be a smooth almost complex structure
preserving `σ`, tamed by `σ` at `u z₀`. If `η` pairs to zero with every smooth section `Y` of
`End(TM)` with compact support in a neighbourhood `W` of `u z₀` which lies in the compatible
tangent space of `J` at every point, then `η z₀ = 0` at every injective point `z₀` of `u` where
`w z₀ ≠ 0`, provided `w` and `η` are continuous near `z₀` into the tangent and cotangent
bundles. -/
theorem IsNondegenerate.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero
    (hσ : σ.IsNondegenerate) (hJσ : σ.Invariant J)
    (hJ₀ : (hσ.symplecticFormAt (u z₀)).Tames (J.almostComplexStructureAt (u z₀)))
    (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0) {W : Set M} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯,
      IsCompact Y.tsupport → Y.tsupport ⊆ W →
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (hσ.symplecticFormAt x).compatibleTangentSpace (J.almostComplexStructureAt x)) →
      ∫ z, η z (Y (u z) (w z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨Y, hYc, hYW, hYJ, hpos⟩ :=
    hσ.exists_contMDiffSection_mem_compatibleTangentSpace_integral_pos (μ := μ) hJσ hJ₀ hw hη
      hinj hw₀ hη₀ hW
  exact hpos.ne' (h Y hYc hYW hYJ)

end TauCeti.SmoothTwoForm
