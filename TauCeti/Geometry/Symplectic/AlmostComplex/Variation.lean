/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Localized variations of almost complex structures at injective points

Transversality for pseudoholomorphic spheres varies the almost complex structure `J` of the
target. Along a map `u`, a variation `Y` of `J` changes the Cauchy–Riemann operator by the term
`Y(u) ∂ₜu` in a local coordinate `z = s + i t` of the domain, and by `Y(u)(∂ₜu - X_{K_t}(u))` for
an inhomogeneous equation with Hamiltonian perturbation `K`. The universal linearized operator is
onto as soon as no nonzero cokernel element `η` annihilates all these terms. Unlike a Hamiltonian
perturbation, a variation of a domain-independent `J` is a function of the target point alone, so
it cannot be localized in the domain directly. It is localized near `u(z₀)` instead, and an
*injective point* `z₀` makes this a localization in the domain: points of the domain whose image
is close to `u(z₀)` are close to `z₀`.

This file proves the resulting pairing statement, in a coordinate model with target a
finite-dimensional real vector space `V` and the domain any locally compact Hausdorff space `S`
with a measure that is positive on open sets and finite on compact sets. The inputs are a
`Cⁿ` family of complex structures `J : V → AlmostComplexStructure V`, maps `u, w : S → V` and a
covector field `η : S → V →L[ℝ] ℝ`, continuous near a point `z₀`. Write the injective point
condition as `(𝓝 (u z₀)).comap u ≤ 𝓝 z₀`; for a continuous map on a compact domain whose fibre
over `u z₀` is `{z₀}` it follows from `IsClosedMap.comap_nhds_le` and `nhdsSet_singleton`. If
`w z₀ ≠ 0` and `η z₀ ≠ 0`, then for every neighbourhood `W` of `u z₀` there is a compactly
supported `Cⁿ` variation `Y : V → V →L[ℝ] V`, supported in `W` and tangent to the space of
complex structures at every point, with

`0 < ∫ η z (Y (u z) (w z)) ∂μ`.

There are two versions, one for each tangent condition:

* `AlmostComplexStructure.exists_contDiff_mem_tangentSpace_integral_pos`: `Y x` anticommutes
  with `J x`, the variations of tame structures;
* `SymplecticForm.exists_contDiff_mem_compatibleTangentSpace_integral_pos`: if every `J x`
  preserves `ω` and `J (u z₀)` is tamed by `ω`, then `Y x` moreover is skew-adjoint for `ω`, the
  variations of compatible structures.

Their contrapositives, `AlmostComplexStructure.eq_zero_of_forall_mem_tangentSpace_integral_eq_zero`
and `SymplecticForm.eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero`, say that a
covector field annihilating all such variations vanishes at every injective point where
`w ≠ 0`. If `u` is `J`-holomorphic and `w = ∂ₜu`, so that `∂ₛu = -J ∂ₜu`, these are the
points where `du ≠ 0`.

The variation is `Y x = ρ x • (A + J x A J x) / 2` for a bump function `ρ` at `u z₀` and an
endomorphism `A` tangent at `J (u z₀)` with `η z₀ (A (w z₀)) > 0`. Averaging with the conjugate by
`J x` keeps `Y x` tangent at `J x` (`AlmostComplexStructure.add_mul_mul_mem_tangentSpace`,
`SymplecticForm.Invariant.add_mul_mul_mem_compatibleTangentSpace_of_skew`) and does not change
`A` at `u z₀`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the proof of Proposition 3.2.1, where a nonzero
  cokernel element is paired with a variation of `J` supported near an injective point).
-/

public section

open Filter Topology MeasureTheory Set

namespace TauCeti

variable {S V : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  [MeasurableSpace S] [OpensMeasurableSpace S] {μ : Measure S} [μ.IsOpenPosMeasure]
  [IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- The variation `x ↦ ρ x • (A + J x A J x) / 2` obtained by averaging `A` with its conjugates
by the complex structures `J x` and cutting it off by `ρ`. -/
private noncomputable def localizedVariation (J : V → AlmostComplexStructure V) (ρ : V → ℝ)
    (A : V →L[ℝ] V) (x : V) : V →L[ℝ] V :=
  ρ x • (2⁻¹ : ℝ) • (A + LinearMap.toContinuousLinearMap (J x).toLinearMap ∘L A ∘L
    LinearMap.toContinuousLinearMap (J x).toLinearMap)

private theorem coe_localizedVariation (J : V → AlmostComplexStructure V) (ρ : V → ℝ)
    (A : V →L[ℝ] V) (x : V) :
    (localizedVariation J ρ A x : Module.End ℝ V) =
      ρ x • (2⁻¹ : ℝ) • ((A : Module.End ℝ V) + (J x).toLinearMap * A * (J x).toLinearMap) := by
  ext v
  simp [localizedVariation]

private theorem localizedVariation_mem_tangentSpace (J : V → AlmostComplexStructure V)
    (ρ : V → ℝ) (A : V →L[ℝ] V) (x : V) :
    (localizedVariation J ρ A x : Module.End ℝ V) ∈ (J x).tangentSpace := by
  rw [coe_localizedVariation]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ((J x).add_mul_mul_mem_tangentSpace _))

/-- Smoothness, support and tangency of the localized variation, and the positivity of its
pairing for a suitable cutoff. The cutoff is a bump function at `u z₀` supported in a
neighbourhood of `u z₀` whose preimage lies in a compact neighbourhood of `z₀` on which the
uncut pairing is positive. -/
private theorem exists_localizedVariation
    {J : V → AlmostComplexStructure V} {n : ℕ∞}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    {u w : S → V} {η : S → V →L[ℝ] ℝ} {z₀ : S}
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z) (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt w z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    {A : V →L[ℝ] V} (hA : (A : Module.End ℝ V) ∈ (J (u z₀)).tangentSpace)
    (hpos : 0 < η z₀ (A (w z₀))) {W : Set V} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ ρ : V → ℝ, ContDiff ℝ n (localizedVariation J ρ A) ∧
      HasCompactSupport (localizedVariation J ρ A) ∧ tsupport (localizedVariation J ρ A) ⊆ W ∧
      0 < ∫ z, η z (localizedVariation J ρ A (u z) (w z)) ∂μ := by
  set Jc : V → V →L[ℝ] V := fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap
  -- The pairing before the cutoff, and its value `η z₀ (A (w z₀))` at `z₀`.
  set G : S → ℝ := fun z ↦ η z (((2⁻¹ : ℝ) • (A + Jc (u z) ∘L A ∘L Jc (u z))) (w z))
  have hG₀ : G z₀ = η z₀ (A (w z₀)) := by
    have hJAJ : Jc (u z₀) ∘L A ∘L Jc (u z₀) = A := by
      ext v
      exact LinearMap.congr_fun (mul_mul_eq_of_mem_tangentSpace hA) v
    simp only [G, hJAJ]
    rw [← two_smul ℝ A, smul_smul, inv_mul_cancel₀ (two_ne_zero' ℝ), one_smul]
  have hGc : ∀ z, ContinuousAt u z → ContinuousAt w z → ContinuousAt η z →
      ContinuousAt G z := by
    intro z hu hw hη
    have hJu : ContinuousAt (fun z ↦ Jc (u z)) z := hJ.continuous.continuousAt.comp hu
    have hB : ContinuousAt (fun z ↦ (2⁻¹ : ℝ) • (A + Jc (u z) ∘L A ∘L Jc (u z))) z :=
      ((continuousAt_const : ContinuousAt (fun _ : S ↦ A) z).add
        ((hJu.clm_comp continuousAt_const).clm_comp hJu)).const_smul (2⁻¹ : ℝ)
    exact hη.clm_apply (hB.clm_apply hw)
  -- A compact neighbourhood `K` of `z₀` on which the data are continuous and `G` is positive,
  -- and a neighbourhood `W₀` of `u z₀` whose preimage lies in `K`.
  have hev : ∀ᶠ z in 𝓝 z₀,
      (ContinuousAt u z ∧ ContinuousAt w z ∧ ContinuousAt η z) ∧ 0 < G z :=
    (hu.and (hw.and hη)).and ((hGc z₀ hu.self_of_nhds hw.self_of_nhds
      hη.self_of_nhds).eventually (lt_mem_nhds (hG₀ ▸ hpos)))
  obtain ⟨K, hKn, hKsub, hK⟩ := local_compact_nhds hev
  obtain ⟨W₀, hW₀, hW₀K⟩ := mem_comap.1 (hinj hKn)
  obtain ⟨ρ, hρW, hρc, hρ, hρI, hρ₁⟩ :=
    exists_contDiff_tsupport_subset (n := n) (inter_mem hW₀ hW)
  refine ⟨ρ, hρ.smul ((contDiff_const.add ((hJ.clm_comp contDiff_const).clm_comp hJ)).const_smul _),
    hρc.smul_right, (tsupport_smul_subset_left _ _).trans (hρW.trans inter_subset_right), ?_⟩
  have hF : (fun z ↦ η z (localizedVariation J ρ A (u z) (w z))) = fun z ↦ ρ (u z) * G z := by
    funext z
    simp [localizedVariation, G, Jc]
    ring
  have hsupp : ∀ z, ρ (u z) ≠ 0 → z ∈ K := fun z hz ↦
    hW₀K (mem_preimage.2 (hρW (subset_tsupport _ hz)).1)
  have hzero : ∀ z ∉ K, ρ (u z) * G z = 0 := fun z hz ↦ by
    rw [not_not.1 (mt (hsupp z) hz), zero_mul]
  rw [hF]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := z₀) ?_
    (HasCompactSupport.intro hK hzero) (fun z ↦ ?_) (by simp [hρ₁, hG₀, hpos.ne'])
  · refine continuous_iff_continuousAt.2 fun z ↦ ?_
    by_cases hz : z ∈ K
    · obtain ⟨⟨hu, hw, hη⟩, -⟩ := hKsub hz
      exact (hρ.continuous.continuousAt.comp hu).mul (hGc z hu hw hη)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy using (hzero y hy).symm
  · by_cases hz : ρ (u z) = 0
    · simp [hz]
    · exact mul_nonneg (hρI (mem_range_self _)).1 (hKsub (hsupp z hz)).2.le

/-- **Variations of complex structures detect cokernel elements at injective points.** Let
`z₀` be an injective point of `u`, in the sense that points whose image is close to `u z₀` are
close to `z₀`, and let `u`, `w` and the covector field `η` be continuous near `z₀`, with
`w z₀ ≠ 0` and `η z₀ ≠ 0`. Then for a `Cⁿ` family of complex structures `J` and any
neighbourhood `W` of `u z₀`, some compactly supported `Cⁿ` variation `Y` supported in `W`, with
`Y x` anticommuting with `J x` at every point, pairs positively with `η` along `u`:
`0 < ∫ η z (Y (u z) (w z)) ∂μ`. -/
theorem exists_contDiff_mem_tangentSpace_integral_pos
    {J : V → AlmostComplexStructure V} {n : ℕ∞}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    {u w : S → V} {η : S → V →L[ℝ] ℝ} {z₀ : S}
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z) (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt w z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hw₀ : w z₀ ≠ 0) (hη₀ : η z₀ ≠ 0) {W : Set V} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ Y : V → V →L[ℝ] V, ContDiff ℝ n Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      (∀ x, (Y x : Module.End ℝ V) ∈ (J x).tangentSpace) ∧
      0 < ∫ z, η z (Y (u z) (w z)) ∂μ := by
  obtain ⟨e, he⟩ : ∃ e, η z₀ e ≠ 0 := by simpa using DFunLike.ne_iff.1 hη₀
  obtain ⟨A, hA, hAw⟩ := (J (u z₀)).exists_mem_tangentSpace_apply_eq hw₀ ((η z₀ e)⁻¹ • e)
  obtain ⟨ρ, hY, hYc, hYW, hpos⟩ := exists_localizedVariation (μ := μ) hJ hu hw hη hinj
    (A := LinearMap.toContinuousLinearMap A) (by simpa using hA) (by simp [hAw, he]) hW
  exact ⟨_, hY, hYc, hYW, localizedVariation_mem_tangentSpace J ρ _, hpos⟩

/-- **A covector field annihilating all variations of complex structures vanishes at injective
points.** If `η` pairs to zero with every compactly supported `Cⁿ` variation `Y` supported in a
neighbourhood `W` of `u z₀`, with `Y x` anticommuting with `J x`, then `η z₀ = 0` at every
injective point `z₀` of `u` where `w z₀ ≠ 0`, provided `u`, `w` and `η` are continuous near
`z₀`. -/
theorem eq_zero_of_forall_mem_tangentSpace_integral_eq_zero
    {J : V → AlmostComplexStructure V} {n : ℕ∞}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    {u w : S → V} {η : S → V →L[ℝ] ℝ} {z₀ : S}
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z) (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt w z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hw₀ : w z₀ ≠ 0) {W : Set V} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ x, (Y x : Module.End ℝ V) ∈ (J x).tangentSpace) → ∫ z, η z (Y (u z) (w z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨Y, hY, hYc, hYW, hYJ, hpos⟩ :=
    exists_contDiff_mem_tangentSpace_integral_pos (μ := μ) hJ hu hw hη hinj hw₀ hη₀ hW
  exact hpos.ne' (h Y hY hYc hYW hYJ)

end AlmostComplexStructure

namespace SymplecticForm

/-- **Compatible variations detect cokernel elements at injective points.** Let `z₀` be an
injective point of `u`, in the sense that points whose image is close to `u z₀` are close to
`z₀`, and let `u`, `w` and the covector field `η` be continuous near `z₀`, with `w z₀ ≠ 0` and
`η z₀ ≠ 0`. Let `J` be a `Cⁿ` family of complex structures preserving `ω`, tamed by `ω` at
`u z₀`. Then for any neighbourhood `W` of `u z₀`, some compactly supported `Cⁿ` variation `Y`
supported in `W`, with `Y x` in the compatible tangent space of `J x` at every point, pairs
positively with `η` along `u`: `0 < ∫ η z (Y (u z) (w z)) ∂μ`. -/
theorem exists_contDiff_mem_compatibleTangentSpace_integral_pos {ω : SymplecticForm V}
    {J : V → AlmostComplexStructure V} {n : ℕ∞}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hJω : ∀ x, ω.Invariant (J x)) {u w : S → V} {η : S → V →L[ℝ] ℝ} {z₀ : S}
    (hJ₀ : ω.Tames (J (u z₀)))
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z) (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt w z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hw₀ : w z₀ ≠ 0) (hη₀ : η z₀ ≠ 0) {W : Set V} (hW : W ∈ 𝓝 (u z₀)) :
    ∃ Y : V → V →L[ℝ] V, ContDiff ℝ n Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) ∧
      0 < ∫ z, η z (Y (u z) (w z)) ∂μ := by
  obtain ⟨e, he⟩ : ∃ e, η z₀ e ≠ 0 := by simpa using DFunLike.ne_iff.1 hη₀
  obtain ⟨A, hA, hAw⟩ :=
    (Compatible.of_tames (hJω _) hJ₀).exists_mem_compatibleTangentSpace_apply_eq hw₀
      ((η z₀ e)⁻¹ • e)
  obtain ⟨ρ, hY, hYc, hYW, hpos⟩ := AlmostComplexStructure.exists_localizedVariation (μ := μ)
    hJ hu hw hη hinj (A := LinearMap.toContinuousLinearMap A)
    (by simpa using compatibleTangentSpace_le_tangentSpace hA) (by simp [hAw, he]) hW
  refine ⟨_, hY, hYc, hYW, fun x ↦ ?_, hpos⟩
  rw [AlmostComplexStructure.coe_localizedVariation]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    ((hJω x).add_mul_mul_mem_compatibleTangentSpace_of_skew (by
      simpa using (mem_compatibleTangentSpace.1 hA).2)))

/-- **A covector field annihilating all compatible variations vanishes at injective points.**
Let `J` be a `Cⁿ` family of complex structures preserving `ω`, tamed by `ω` at `u z₀`. If `η`
pairs to zero with every compactly supported `Cⁿ` variation `Y` supported in a neighbourhood `W`
of `u z₀`, with `Y x` in the compatible tangent space of `J x`, then `η z₀ = 0` at every
injective point `z₀` of `u` where `w z₀ ≠ 0`, provided `u`, `w` and `η` are continuous near
`z₀`. -/
theorem eq_zero_of_forall_mem_compatibleTangentSpace_integral_eq_zero {ω : SymplecticForm V}
    {J : V → AlmostComplexStructure V} {n : ℕ∞}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hJω : ∀ x, ω.Invariant (J x)) {u w : S → V} {η : S → V →L[ℝ] ℝ} {z₀ : S}
    (hJ₀ : ω.Tames (J (u z₀)))
    (hu : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z) (hw : ∀ᶠ z in 𝓝 z₀, ContinuousAt w z)
    (hη : ∀ᶠ z in 𝓝 z₀, ContinuousAt η z) (hinj : (𝓝 (u z₀)).comap u ≤ 𝓝 z₀)
    (hw₀ : w z₀ ≠ 0) {W : Set V} (hW : W ∈ 𝓝 (u z₀))
    (h : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z, η z (Y (u z) (w z)) ∂μ = 0) :
    η z₀ = 0 := by
  by_contra hη₀
  obtain ⟨Y, hY, hYc, hYW, hYJ, hpos⟩ := exists_contDiff_mem_compatibleTangentSpace_integral_pos
    (μ := μ) hJ hJω hJ₀ hu hw hη hinj hw₀ hη₀ hW
  exact hpos.ne' (h Y hY hYc hYW hYJ)

end SymplecticForm

end TauCeti
