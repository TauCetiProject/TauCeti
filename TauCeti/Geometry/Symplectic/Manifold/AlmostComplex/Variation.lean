/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Localized variations of almost complex structures on a manifold

Transversality for pseudoholomorphic spheres, and for sphere components of Floer configurations,
varies an almost complex structure `J` of the target which does not depend on the domain point.
Along a map `u` from a domain `S` into a manifold `M`, a variation `Y` of `J`, a section of the
endomorphism bundle of `TM`, changes the Cauchy–Riemann operator by `Y(u) w` for the vector field
`w = ∂ₜu` along `u` in a local coordinate `z = s + i t` of the domain, and by
`w = ∂ₜu - X_{K_t}(u)` for an inhomogeneous equation with Hamiltonian perturbation `K`. A cokernel
element of the universal linearized operator is a covector field `η` along `u`, and it must vanish
once it annihilates all these terms. A variation of `J` is a function of the target point, so it is
localized near `u z₀`; an *injective point* `z₀`, at which points of the domain whose image is
close to `u z₀` are close to `z₀`, turns this into a localization in the domain.

This file proves the resulting pairing statement on an actual manifold target, for structures
`J : ContMDiffAlmostComplexStructure I n M` of any regularity `n`, and for variations in the
tangent space of the almost complex structures at `J`: `Y x` anticommutes with `J x` at every
point. These are the variations of tame almost complex structures; no two-form enters. The domain
is any locally compact Hausdorff space with a measure that is positive on open sets and finite on
compact sets, and the vector field `w` and the covector field `η` along `u` are continuous near
`z₀` as maps into the tangent and cotangent bundles of `M`. If `w z₀ ≠ 0` and `η z₀ ≠ 0`, then for
every neighbourhood `W` of `u z₀` some `Cⁿ` section `Y` with compact support in `W`, anticommuting
with `J`, satisfies

`0 < ∫ z, η z (Y (u z) (w z)) ∂μ`,

with an integrable integrand
(`TauCeti.ContMDiffAlmostComplexStructure.exists_mem_tangentSpace_integral_pos`). Its
contrapositive
(`TauCeti.ContMDiffAlmostComplexStructure.eq_zero_of_forall_mem_tangentSpace_integral_eq_zero`)
says that a covector field annihilating all such variations vanishes at every injective point
where `w ≠ 0`. The test class includes integrability of the pairing, so the hypothesis is not met
through the junk value of a nonintegrable integral.

The variation is `Y = ρ • B` for a smooth bump function `ρ` at `u z₀` and a global section `B`
anticommuting with `J` whose value at `u z₀` pairs positively with `η z₀` on `w z₀`. Such a `B`
exists for every prescribed value anticommuting with `J (u z₀)`
(`TauCeti.ContMDiffAlmostComplexStructure.exists_forall_mem_tangentSpace_eq`): extend the value to
a global section `A` (`FiberBundle.exists_contMDiff_section_eq`) and average it with its conjugate,
`B = (A + J A J) / 2`, which anticommutes with `J` at every point
(`TauCeti.AlmostComplexStructure.add_mul_mul_mem_tangentSpace`) and keeps the prescribed value.
This is the manifold counterpart of the coordinate statement
`TauCeti.AlmostComplexStructure.exists_contDiff_mem_tangentSpace_integral_pos`, whose constant
endomorphism is replaced here by a section of the endomorphism bundle. The variations of
compatible structures, which are moreover skew-adjoint for a symplectic form, are not treated
here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the proof of Proposition 3.2.1, where a nonzero
  cokernel element is paired with a variation of `J` supported near an injective point).
-/

public noncomputable section

open Bundle Filter MeasureTheory Set Topology
open scoped ContDiff Manifold

namespace TauCeti.ContMDiffAlmostComplexStructure

variable {S : Type*} [TopologicalSpace S]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ∞}

/-- **Tangent variations extend to global sections.** An endomorphism of the tangent space at
`x₀` anticommuting with `J x₀` is the value at `x₀` of a global `Cⁿ` section of the endomorphism
bundle of `TM` anticommuting with `J` at every point. -/
theorem exists_forall_mem_tangentSpace_eq (J : ContMDiffAlmostComplexStructure I n M) {x₀ : M}
    {A₀ : TangentSpace I x₀ →L[ℝ] TangentSpace I x₀}
    (hA₀ : (A₀ : Module.End ℝ (TangentSpace I x₀)) ∈ (J.almostComplexStructureAt x₀).tangentSpace) :
    ∃ B : ContMDiffSection I (E →L[ℝ] E) n
        (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x),
      (∀ x, (B x : Module.End ℝ (TangentSpace I x)) ∈
        (J.almostComplexStructureAt x).tangentSpace) ∧ B x₀ = A₀ := by
  -- Average a global section `A` with value `A₀` at `x₀` with its conjugate by `J`.
  obtain ⟨s, hs, hs₀⟩ := FiberBundle.exists_contMDiff_section_eq I (E →L[ℝ] E) n
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) A₀
  let A : ContMDiffSection I (E →L[ℝ] E) n
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) := ⟨s, hs⟩
  let B : ContMDiffSection I (E →L[ℝ] E) n
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) :=
    (2⁻¹ : ℝ) • (A + J.toEndomorphism.clmComp (A.clmComp J.toEndomorphism))
  have hB (x : M) : (B x : Module.End ℝ (TangentSpace I x)) =
      (2⁻¹ : ℝ) • ((A x : Module.End ℝ (TangentSpace I x)) +
        (J.almostComplexStructureAt x).toLinearMap * A x *
          (J.almostComplexStructureAt x).toLinearMap) := by
    ext v
    simp [B]
  refine ⟨B, fun x ↦ ?_, ?_⟩
  · rw [hB]
    exact Submodule.smul_mem _ _ ((J.almostComplexStructureAt x).add_mul_mul_mem_tangentSpace _)
  · -- At `x₀` the average is `(A₀ + J A₀ J) / 2 = A₀`, since `A₀` anticommutes with `J`.
    apply ContinuousLinearMap.coe_injective
    have hA : (A x₀ : Module.End ℝ (TangentSpace I x₀)) = A₀ := by simp [A, hs₀]
    rw [hB, hA, AlmostComplexStructure.mul_mul_eq_of_mem_tangentSpace hA₀, ← two_smul ℝ,
      smul_smul, inv_mul_cancel₀ (two_ne_zero' ℝ), one_smul]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A covector field along `u`, paired with a continuous section of the endomorphism bundle
applied to a vector field along `u`, is continuous wherever both fields are continuous into their
bundles. -/
private theorem continuousAt_apply_apply
    (B : ContMDiffSection I (E →L[ℝ] E) n
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x))
    {u : S → M} {w : ∀ z, TangentSpace I (u z)} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ} {z : S}
    (hw : ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z) :
    ContinuousAt (fun z ↦ η z (B (u z) (w z))) z := by
  have hu : ContinuousAt u z := (FiberBundle.continuous_proj E _).continuousAt.comp hw
  have hB : ContinuousAt (fun z ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (u z) (B (u z))) z :=
    B.contMDiff.continuous.continuousAt.comp hu
  have h := ContinuousAt.clm_bundle_apply (E₂ := Bundle.Trivial M ℝ) hη (hB.clm_bundle_apply hw)
  exact (continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous).continuousAt.comp h

variable [T2Space S] [LocallyCompactSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
  {μ : Measure S} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- Cut off a section near `u z₀` where its pairing with `η` along `u` is positive. The bump
function is supported in a neighbourhood of `u z₀` whose preimage lies in a compact neighbourhood
of `z₀` on which the uncut pairing is positive, so the cut-off pairing is continuous, nonnegative
and compactly supported. -/
private theorem exists_smul_integral_pos
    (B : ContMDiffSection I (E →L[ℝ] E) n
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x))
    {u : S → M} {w : ∀ z, TangentSpace I (u z)} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
    {z₀ : S} (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hpos : 0 < η z₀ (B (u z₀) (w z₀)))
    {W : Set M} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ ρ : C^n⟮I, M; ℝ⟯, HasCompactSupport ρ ∧ tsupport ρ ⊆ W ∧
      Integrable (fun z ↦ η z ((ρ • B) (u z) (w z))) μ ∧
      0 < ∫ z, η z ((ρ • B) (u z) (w z)) ∂μ := by
  let G : S → ℝ := fun z ↦ η z (B (u z) (w z))
  -- A compact neighbourhood `K` of `z₀` on which the data are continuous and `G` is positive,
  -- and a neighbourhood `W₀` of `u z₀` whose preimage lies in `K`.
  have hev : ∀ᶠ z in 𝓝 z₀, (ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z ∧
      ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z) ∧ 0 < G z :=
    (hw.and hη).and ((continuousAt_apply_apply B hw.self_of_nhds hη.self_of_nhds).eventually
      (lt_mem_nhds hpos))
  obtain ⟨K, hKn, hKsub, hK⟩ := local_compact_nhds hev
  obtain ⟨W₀, hW₀, hW₀K⟩ := mem_comap.1 (hinj hKn)
  obtain ⟨b, -, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (u z₀)).mem_iff.1 (inter_mem hW₀ hW)
  let ρ : C^n⟮I, M; ℝ⟯ := ⟨b, b.contMDiff.of_le (mod_cast le_top)⟩
  have hF : (fun z ↦ η z ((ρ • B) (u z) (w z))) = fun z ↦ b (u z) * G z := by
    funext z
    rw [ContMDiffSection.smul_apply]
    simp [ρ, G]
  have hsupp (z : S) (hz : b (u z) ≠ 0) : z ∈ K :=
    hW₀K (mem_preimage.2 (hb (subset_tsupport _ hz)).1)
  have hzero (z : S) (hz : z ∉ K) : b (u z) * G z = 0 := by
    rw [not_not.1 (mt (hsupp z) hz), zero_mul]
  have hcs : HasCompactSupport fun z ↦ b (u z) * G z := HasCompactSupport.intro hK hzero
  have hcont : Continuous fun z ↦ b (u z) * G z := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    by_cases hz : z ∈ K
    · obtain ⟨⟨hwz, hηz⟩, -⟩ := hKsub hz
      exact (b.continuous.continuousAt.comp
        ((FiberBundle.continuous_proj E _).continuousAt.comp hwz)).mul
          (continuousAt_apply_apply B hwz hηz)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy using (hzero y hy).symm
  refine ⟨ρ, b.hasCompactSupport, hb.trans inter_subset_right, ?_, ?_⟩
  · rw [hF]
    exact hcont.integrable_of_hasCompactSupport hcs
  · rw [hF]
    refine hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := z₀) hcs (fun z ↦ ?_)
      (by simpa [b.eq_one] using hpos.ne')
    by_cases hz : b (u z) = 0
    · simp [hz]
    · exact mul_nonneg b.nonneg (hKsub (hsupp z hz)).2.le

/-- **Variations of an almost complex structure on a manifold detect covectors at injective
points.** Let `z₀` be an injective point of `u : S → M`, in the sense that points whose image is
close to `u z₀` are close to `z₀`, and let the vector field `w` and the covector field `η` along
`u` be continuous into the tangent and cotangent bundles near `z₀`, with `w z₀ ≠ 0` and
`η z₀ ≠ 0`. Then for any neighbourhood `W` of `u z₀` some `Cⁿ` section `Y` of the endomorphism
bundle of `TM`, with compact support in `W` and with `Y x` anticommuting with `J x` at every point,
pairs integrably and positively with `η` along `u`: `0 < ∫ z, η z (Y (u z) (w z)) ∂μ`. -/
theorem exists_mem_tangentSpace_integral_pos (J : ContMDiffAlmostComplexStructure I n M)
    {u : S → M} {w : ∀ z, TangentSpace I (u z)} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
    {z₀ : S} (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0) (hη₀ : η z₀ ≠ 0)
    {W : Set M} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ Y : ContMDiffSection I (E →L[ℝ] E) n
        (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x),
      IsCompact Y.tsupport ∧ Y.tsupport ⊆ W ∧
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (J.almostComplexStructureAt x).tangentSpace) ∧
      Integrable (fun z ↦ η z (Y (u z) (w z))) μ ∧ 0 < ∫ z, η z (Y (u z) (w z)) ∂μ := by
  -- A tangent variation `A₀` at `u z₀` with `η z₀ (A₀ (w z₀)) = 1`, extended to a global section
  -- `B` of tangent variations, and then cut off near `u z₀`.
  obtain ⟨e, he⟩ : ∃ e, η z₀ e ≠ 0 := by simpa using DFunLike.ne_iff.1 hη₀
  obtain ⟨A₀, hA₀, hA₀w⟩ :=
    (J.almostComplexStructureAt (u z₀)).exists_mem_tangentSpace_apply_eq hw₀ ((η z₀ e)⁻¹ • e)
  obtain ⟨B, hBJ, hB₀⟩ := J.exists_forall_mem_tangentSpace_eq
    (A₀ := LinearMap.toContinuousLinearMap A₀) (by simpa using hA₀)
  obtain ⟨ρ, hρc, hρW, hi, hpos⟩ := exists_smul_integral_pos (μ := μ) B hw hη hinj
    (by simp [hB₀, hA₀w, he]) hW
  have hYsupp : (ρ • B).tsupport ⊆ tsupport ρ :=
    (ContMDiffSection.tsupport_smul_function_subset ρ B).trans inter_subset_left
  refine ⟨ρ • B, hρc.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _) hYsupp,
    hYsupp.trans hρW, fun x ↦ ?_, hi, hpos⟩
  have hY : ((ρ • B) x : Module.End ℝ (TangentSpace I x)) =
      ρ x • (B x : Module.End ℝ (TangentSpace I x)) := by
    ext v
    simp
  rw [hY]
  exact Submodule.smul_mem _ _ (hBJ x)

/-- **A covector field annihilating all variations of an almost complex structure vanishes at
injective points.** If `η` pairs integrably to zero with every `Cⁿ` section `Y` of the
endomorphism bundle of `TM` with compact support in a neighbourhood `W` of `u z₀` and with `Y x`
anticommuting with `J x`, then `η z₀ = 0` at every injective point `z₀` of `u` where `w z₀ ≠ 0`.
Here `w` and `η` are continuous into the tangent and cotangent bundles near `z₀`. -/
theorem eq_zero_of_forall_mem_tangentSpace_integral_eq_zero
    (J : ContMDiffAlmostComplexStructure I n M)
    {u : S → M} {w : ∀ z, TangentSpace I (u z)} {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
    {z₀ : S} (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, w z⟩ : TangentBundle I M)) z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)) z)
    (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀) (hw₀ : w z₀ ≠ 0)
    {W : Set M} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : ContMDiffSection I (E →L[ℝ] E) n
        (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x),
      IsCompact Y.tsupport → Y.tsupport ⊆ W →
      (∀ x, (Y x : Module.End ℝ (TangentSpace I x)) ∈
        (J.almostComplexStructureAt x).tangentSpace) →
      Integrable (fun z ↦ η z (Y (u z) (w z))) μ → ∫ z, η z (Y (u z) (w z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨Y, hYc, hYW, hYJ, hYi, hpos⟩ :=
    J.exists_mem_tangentSpace_integral_pos (μ := μ) hw hη hinj hw₀ hη₀ hW
  exact hpos.ne' (h Y hYc hYW hYJ hYi)

end TauCeti.ContMDiffAlmostComplexStructure
