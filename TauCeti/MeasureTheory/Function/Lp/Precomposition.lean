/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Precomposition on `Lᵖ` by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ` and suppose that it pushes `μ` forward to
at most `C • ν` for a finite constant `C`. Then precomposition `g ↦ g ∘ f` is well defined on
almost-everywhere classes and is a bounded linear operator `Lᵖ(ν) → Lᵖ(μ)` of norm at most
`C ^ (1/p)` (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). This generalizes Mathlib's
`MeasureTheory.Lp.compMeasurePreserving`, the case `μ.map f = ν`, to maps such as
diffeomorphisms or maps defined only on a measurable domain, which change measures only up to a
bounded density. When `μ.map f = C • ν` with `0 < C < ∞`, such as a finite covering map
multiplying volume by its degree, the norm is multiplied by exactly `C ^ (1/p)`, so
`g ↦ C ^ (-1/p) • g ∘ f` is a linear isometry.

When `f` and `g : β → α` are mutually inverse and both have dominated pushforward, the two
precompositions are mutually inverse, giving a continuous linear equivalence
`Lᵖ(ν) ≃L Lᵖ(μ)`.

## Main declarations

* `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_mem_Lp`: precomposition with a map of
  dominated pushforward preserves membership in `Lᵖ`.
* `MeasureTheory.Lp.compOfMapLeSmul`: precomposition with `f`, as a continuous linear map
  `Lp E p ν →L[𝕜] Lp E p μ`.
* `MeasureTheory.Lp.coeFn_compOfMapLeSmul` and `MeasureTheory.Lp.norm_compOfMapLeSmul_le`: it is
  `g ↦ g ∘ f` almost everywhere, with norm at most `C ^ (1/p)`.
* `MeasureTheory.Lp.norm_compOfMapLeSmul`: when `μ.map f = C • ν`, the norm is multiplied by
  exactly `C ^ (1/p)`.
* `MeasureTheory.Lp.mem_range_compOfMapLeSmul_iff`: in that case the range consists of the
  classes of the functions `u ∘ f` with `u` strongly measurable.
* `MeasureTheory.Lp.normalizedCompOfMapEqSmul`: when `μ.map f = C • ν` with `0 < C < ∞`, the
  normalized precomposition `g ↦ C ^ (-1/p) • g ∘ f`, as a linear isometry
  `Lp E p ν →ₗᵢ[𝕜] Lp E p μ`, with the same range
  (`MeasureTheory.Lp.mem_range_normalizedCompOfMapEqSmul_iff`).
* `MeasureTheory.Lp.compOfMapLeSmul_comp`: precomposition is contravariant in `f`.
* `MeasureTheory.Lp.compEquivOfMapLeSmul`: the continuous linear equivalence attached to a pair of
  mutually inverse maps with dominated pushforwards.
* `MeasureTheory.Lp.compContinuousLinearEquivAddRestrict` and
  `MeasureTheory.Lp.coeFn_compContinuousLinearEquivAddRestrict`: restricted additive Haar `Lᵖ`
  precomposition along an invertible affine map `x ↦ B x + b`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {α β γ E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ρ : Measure γ} [NormedAddCommGroup E] {p : ℝ≥0∞}
  {f : α → β} {C : ℝ≥0∞}

/-- Precomposition with a map whose pushforward is dominated by a finite multiple of `ν` preserves
membership in `Lᵖ`, for every exponent `p`. This generalizes Mathlib's
`MeasureTheory.AEEqFun.compMeasurePreserving_mem_Lp`. -/
theorem AEEqFun.compQuasiMeasurePreserving_mem_Lp {g : β →ₘ[ν] E} (hg : g ∈ Lp E p ν)
    (hf : QuasiMeasurePreserving f μ ν) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν) :
    g.compQuasiMeasurePreserving f hf ∈ Lp E p μ := by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rw [eLpNorm_congr_ae (AEEqFun.coeFn_compQuasiMeasurePreserving g hf)]
  exact (eLpNorm_comp_le_of_map_le_smul hf.aemeasurable hmap p).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hC) hg)

namespace Lp

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- Precomposition with `f`, as a linear map `Lᵖ(ν) → Lᵖ(μ)`, when `f` pushes `μ` forward to at
most `C • ν` with `C` finite. -/
private def compOfMapLeSmulₗ (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν) :
    Lp E p ν →ₗ[𝕜] Lp E p μ where
  toFun g := ⟨_, AEEqFun.compQuasiMeasurePreserving_mem_Lp g.property
    (QuasiMeasurePreserving.of_map_le_smul hf hmap) hC hmap⟩
  map_add' g h := by
    have hqmp := QuasiMeasurePreserving.of_map_le_smul hf hmap
    refine Lp.ext <| (AEEqFun.coeFn_compQuasiMeasurePreserving _ hqmp).trans <|
      .trans ?_ (Lp.coeFn_add _ _).symm
    filter_upwards [hqmp.ae_eq_comp (Lp.coeFn_add g h),
      AEEqFun.coeFn_compQuasiMeasurePreserving (g : β →ₘ[ν] E) hqmp,
      AEEqFun.coeFn_compQuasiMeasurePreserving (h : β →ₘ[ν] E) hqmp] with x hx hgx hhx
    exact hx.trans (congr_arg₂ (· + ·) hgx.symm hhx.symm)
  map_smul' c g := by
    have hqmp := QuasiMeasurePreserving.of_map_le_smul hf hmap
    refine Lp.ext <| (AEEqFun.coeFn_compQuasiMeasurePreserving _ hqmp).trans <|
      .trans ?_ (Lp.coeFn_smul _ _).symm
    filter_upwards [hqmp.ae_eq_comp (Lp.coeFn_smul c g),
      AEEqFun.coeFn_compQuasiMeasurePreserving (g : β →ₘ[ν] E) hqmp] with x hx hgx
    exact hx.trans (congr_arg (c • ·) hgx.symm)

private theorem coeFn_compOfMapLeSmulₗ (hf : AEMeasurable f μ) (hC : C ≠ ∞)
    (hmap : μ.map f ≤ C • ν) (g : Lp E p ν) :
    compOfMapLeSmulₗ 𝕜 hf hC hmap g =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_compQuasiMeasurePreserving (g : β →ₘ[ν] E)
    (QuasiMeasurePreserving.of_map_le_smul hf hmap)

private theorem norm_compOfMapLeSmulₗ_le (hf : AEMeasurable f μ) (hC : C ≠ ∞)
    (hmap : μ.map f ≤ C • ν) (g : Lp E p ν) :
    ‖compOfMapLeSmulₗ 𝕜 hf hC hmap g‖ ≤ (C ^ (1 / p).toReal).toReal * ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_compOfMapLeSmulₗ 𝕜 hf hC hmap g),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC)
      (Lp.eLpNorm_ne_top g))
    (eLpNorm_comp_le_of_map_le_smul hf hmap p)

variable [Fact (1 ≤ p)]

/-- **Precomposition with a map of dominated pushforward.** If `f` is almost everywhere measurable
for `μ` and `μ.map f ≤ C • ν` with `C < ∞`, then `g ↦ g ∘ f` is a continuous linear map
`Lᵖ(ν) → Lᵖ(μ)`. -/
def compOfMapLeSmul (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν) :
    Lp E p ν →L[𝕜] Lp E p μ :=
  (compOfMapLeSmulₗ 𝕜 hf hC hmap).mkContinuous (C ^ (1 / p).toReal).toReal
    (norm_compOfMapLeSmulₗ_le 𝕜 hf hC hmap)

variable {𝕜}

/-- The almost-everywhere class underlying the precomposition of `g` with `f` is
`AEEqFun.compQuasiMeasurePreserving`. -/
@[simp]
theorem compOfMapLeSmul_val (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν)
    (g : Lp E p ν) :
    (compOfMapLeSmul 𝕜 hf hC hmap g).val =
      g.val.compQuasiMeasurePreserving f (.of_map_le_smul hf hmap) :=
  (rfl)

/-- Precomposition with `f` is `g ↦ g ∘ f` almost everywhere. -/
theorem coeFn_compOfMapLeSmul (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν)
    (g : Lp E p ν) : compOfMapLeSmul 𝕜 hf hC hmap g =ᵐ[μ] g ∘ f :=
  coeFn_compOfMapLeSmulₗ 𝕜 hf hC hmap g

/-- If `μ.map f ≤ C • ν`, then precomposition with `f` has norm at most `C ^ (1/p)`. -/
theorem norm_compOfMapLeSmul_le (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν)
    (g : Lp E p ν) :
    ‖compOfMapLeSmul 𝕜 hf hC hmap g‖ ≤ (C ^ (1 / p).toReal).toReal * ‖g‖ :=
  norm_compOfMapLeSmulₗ_le 𝕜 hf hC hmap g

/-- If `μ.map f = C • ν` with `C ≠ 0`, then precomposition with `f` multiplies the norm by exactly
`C ^ (1/p)`. -/
theorem norm_compOfMapLeSmul (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) (g : Lp E p ν) :
    ‖compOfMapLeSmul 𝕜 hf hC hmap.le g‖ = (C ^ (1 / p).toReal).toReal * ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_compOfMapLeSmul hf hC hmap.le g),
    ← eLpNorm_map_measure (by rw [hmap]; exact (Lp.aestronglyMeasurable g).smul_measure _)
      hf, hmap, eLpNorm_smul_measure_of_ne_zero hC₀, smul_eq_mul, ENNReal.toReal_mul]

/-- If `μ.map f = C • ν`, then `h ∈ Lᵖ(μ)` is the precomposition with `f` of an element of `Lᵖ(ν)`
exactly when it agrees almost everywhere with `u ∘ f` for a strongly measurable `u`; such a `u`
then automatically lies in `Lᵖ(ν)` when `C ≠ 0`. -/
theorem mem_range_compOfMapLeSmul_iff (hf : AEMeasurable f μ) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) (h : Lp E p μ) :
    h ∈ Set.range (compOfMapLeSmul 𝕜 hf hC hmap.le) ↔
      ∃ u : β → E, StronglyMeasurable u ∧ h =ᵐ[μ] u ∘ f := by
  refine ⟨?_, fun ⟨u, hu, hh⟩ ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, Lp.stronglyMeasurable g, coeFn_compOfMapLeSmul hf hC hmap.le g⟩
  -- If `C = 0`, then `μ = 0` and every element of `Lᵖ(μ)` is zero.
  rcases eq_or_ne C 0 with rfl | hC₀
  · rw [zero_smul, Measure.map_eq_zero_iff hf] at hmap
    subst hmap
    exact ⟨0, Lp.ext (by simp [Filter.EventuallyEq])⟩
  -- `‖u ∘ f‖_{Lᵖ(μ)} = C ^ (1/p) ‖u‖_{Lᵖ(ν)}`, and the left side is the finite norm of `h`.
  have hnorm : eLpNorm (u ∘ f) p μ = C ^ (1 / p).toReal * eLpNorm u p ν := by
    rw [← eLpNorm_map_measure (by rw [hmap]; exact hu.aestronglyMeasurable) hf, hmap,
      eLpNorm_smul_measure_of_ne_zero hC₀, smul_eq_mul]
  have hu' : MemLp u p ν := by
    refine ENNReal.lt_top_of_mul_ne_top_right (a := C ^ (1 / p).toReal) ?_
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hC₀) hC).ne'
    rw [← hnorm, ← eLpNorm_congr_ae hh]
    exact Lp.eLpNorm_ne_top h
  refine ⟨hu'.toLp u, Lp.ext ((coeFn_compOfMapLeSmul hf hC hmap.le _).trans ?_)⟩
  exact ((QuasiMeasurePreserving.of_map_le_smul hf hmap.le).ae_eq_comp hu'.coeFn_toLp).trans hh.symm

section Normalized

variable [NormedAlgebra ℝ 𝕜]

variable (𝕜) in
/-- **Normalized precomposition.** If `f` is almost everywhere measurable for `μ` and
`μ.map f = C • ν` with `0 < C < ∞`, then `g ↦ C ^ (-1/p) • g ∘ f` is a linear isometry
`Lᵖ(ν) → Lᵖ(μ)` (`MeasureTheory.Lp.coeFn_normalizedCompOfMapEqSmul`). -/
def normalizedCompOfMapEqSmul (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) : Lp E p ν →ₗᵢ[𝕜] Lp E p μ where
  toLinearMap :=
    algebraMap ℝ 𝕜 (C.toReal ^ (-(1 / p).toReal)) • (compOfMapLeSmul 𝕜 hf hC hmap.le).toLinearMap
  norm_map' g := by
    have hC' : 0 < C.toReal := ENNReal.toReal_pos hC₀ hC
    simp only [LinearMap.smul_apply, norm_smul, norm_algebraMap', ContinuousLinearMap.coe_coe,
      norm_compOfMapLeSmul hf hC₀ hC hmap, ← ENNReal.toReal_rpow, Real.rpow_neg hC'.le, norm_inv,
      Real.norm_of_nonneg (Real.rpow_nonneg hC'.le _)]
    exact inv_mul_cancel_left₀ (Real.rpow_pos_of_pos hC' _).ne' _

/-- Normalized precomposition with `f` is `g ↦ C ^ (-1/p) • g ∘ f` almost everywhere. -/
theorem coeFn_normalizedCompOfMapEqSmul (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) (g : Lp E p ν) :
    normalizedCompOfMapEqSmul 𝕜 hf hC₀ hC hmap g =ᵐ[μ]
      fun x ↦ algebraMap ℝ 𝕜 (C.toReal ^ (-(1 / p).toReal)) • g (f x) := by
  filter_upwards [Lp.coeFn_smul (algebraMap ℝ 𝕜 (C.toReal ^ (-(1 / p).toReal)))
      (compOfMapLeSmul 𝕜 hf hC hmap.le g),
    coeFn_compOfMapLeSmul (𝕜 := 𝕜) hf hC hmap.le g] with x hx hx'
  rw [normalizedCompOfMapEqSmul, LinearIsometry.coe_mk, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, hx, Pi.smul_apply, hx', Function.comp_apply]

/-- Normalized precomposition with `f` is precomposition with `f` multiplied by `C ^ (-1/p)`. -/
theorem normalizedCompOfMapEqSmul_apply (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) (g : Lp E p ν) :
    normalizedCompOfMapEqSmul 𝕜 hf hC₀ hC hmap g =
      algebraMap ℝ 𝕜 (C.toReal ^ (-(1 / p).toReal)) • compOfMapLeSmul 𝕜 hf hC hmap.le g :=
  (rfl)

/-- Normalized precomposition with `f` has the same range as precomposition with `f`. -/
theorem range_normalizedCompOfMapEqSmul (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) :
    Set.range (normalizedCompOfMapEqSmul (E := E) (p := p) 𝕜 hf hC₀ hC hmap) =
      Set.range (compOfMapLeSmul (E := E) (p := p) 𝕜 hf hC hmap.le) := by
  have hc : algebraMap ℝ 𝕜 (C.toReal ^ (-(1 / p).toReal)) ≠ 0 :=
    (map_ne_zero _).2 (Real.rpow_pos_of_pos (ENNReal.toReal_pos hC₀ hC) _).ne'
  rw [congrArg Set.range (funext (normalizedCompOfMapEqSmul_apply hf hC₀ hC hmap))]
  have := congrArg SetLike.coe <|
    LinearMap.range_smul (compOfMapLeSmul (E := E) (p := p) 𝕜 hf hC hmap.le).toLinearMap _ hc
  simpa only [LinearMap.coe_range, LinearMap.coe_smul, ContinuousLinearMap.coe_coe, Pi.smul_def]
    using this

/-- If `μ.map f = C • ν` with `0 < C < ∞`, then `h ∈ Lᵖ(μ)` lies in the range of the normalized
precomposition with `f` exactly when it agrees almost everywhere with `u ∘ f` for a strongly
measurable `u`. -/
theorem mem_range_normalizedCompOfMapEqSmul_iff (hf : AEMeasurable f μ) (hC₀ : C ≠ 0) (hC : C ≠ ∞)
    (hmap : μ.map f = C • ν) (h : Lp E p μ) :
    h ∈ Set.range (normalizedCompOfMapEqSmul 𝕜 hf hC₀ hC hmap) ↔
      ∃ u : β → E, StronglyMeasurable u ∧ h =ᵐ[μ] u ∘ f := by
  rw [range_normalizedCompOfMapEqSmul, mem_range_compOfMapLeSmul_iff hf hC hmap]

end Normalized

/-- Precomposition is contravariant: precomposing with `g ∘ f` is precomposing with `g`, then
with `f`. -/
theorem compOfMapLeSmul_comp {g : β → γ} {D : ℝ≥0∞} (hf : AEMeasurable f μ) (hC : C ≠ ∞)
    (hmap : μ.map f ≤ C • ν) (hg : AEMeasurable g ν) (hD : D ≠ ∞) (hmapg : ν.map g ≤ D • ρ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hmapgf : μ.map (g ∘ f) ≤ B • ρ) :
    (compOfMapLeSmul 𝕜
        ((hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)).comp_aemeasurable hf)
        hB hmapgf : Lp E p ρ →L[𝕜] Lp E p μ) =
      (compOfMapLeSmul 𝕜 hf hC hmap).comp (compOfMapLeSmul 𝕜 hg hD hmapg) := by
  ext1 h
  exact Subtype.ext <| by
    simp [AEEqFun.compQuasiMeasurePreserving_comp _ (.of_map_le_smul hg hmapg)
      (.of_map_le_smul hf hmap)]

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem compOfMapLeSmul_id (hC : C ≠ ∞) (hmap : μ.map id ≤ C • μ) :
    (compOfMapLeSmul 𝕜 aemeasurable_id hC hmap : Lp E p μ →L[𝕜] Lp E p μ) =
      ContinuousLinearMap.id 𝕜 _ := by
  ext1 g
  exact Subtype.ext <| by simp

variable (𝕜) in
/-- **Precomposition with mutually inverse maps.** If `f : α → β` and `g : β → α` are mutually
inverse almost everywhere measurable maps whose pushforwards are dominated by finite multiples of
`ν` and `μ` respectively, then precomposition with `f` is a continuous linear equivalence
`Lᵖ(ν) ≃L Lᵖ(μ)`, with inverse the precomposition with `g`. -/
def compEquivOfMapLeSmul {g : β → α} {D : ℝ≥0∞} (hf : AEMeasurable f μ) (hC : C ≠ ∞)
    (hmap : μ.map f ≤ C • ν) (hg : AEMeasurable g ν) (hD : D ≠ ∞) (hmapg : ν.map g ≤ D • μ)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    Lp E p ν ≃L[𝕜] Lp E p μ :=
  ContinuousLinearEquiv.ofContinuousLinearMap (compOfMapLeSmul 𝕜 hf hC hmap)
    (compOfMapLeSmul 𝕜 hg hD hmapg)
    (ContinuousLinearMap.ext fun h ↦ Subtype.ext <| by
      simp [← AEEqFun.compQuasiMeasurePreserving_comp _ (.of_map_le_smul hg hmapg)
        (.of_map_le_smul hf hmap), hgf.comp_eq_id])
    (ContinuousLinearMap.ext fun h ↦ Subtype.ext <| by
      simp [← AEEqFun.compQuasiMeasurePreserving_comp _ (.of_map_le_smul hf hmap)
        (.of_map_le_smul hg hmapg), hfg.comp_eq_id])

section Equiv

variable {g : β → α} {D : ℝ≥0∞} (hf : AEMeasurable f μ) (hC : C ≠ ∞) (hmap : μ.map f ≤ C • ν)
  (hg : AEMeasurable g ν) (hD : D ≠ ∞) (hmapg : ν.map g ≤ D • μ) (hgf : Function.LeftInverse g f)
  (hfg : Function.RightInverse g f)

@[simp]
theorem compEquivOfMapLeSmul_apply (h : Lp E p ν) :
    compEquivOfMapLeSmul 𝕜 hf hC hmap hg hD hmapg hgf hfg h = compOfMapLeSmul 𝕜 hf hC hmap h :=
  (rfl)

@[simp]
theorem compEquivOfMapLeSmul_symm_apply (h : Lp E p μ) :
    (compEquivOfMapLeSmul 𝕜 hf hC hmap hg hD hmapg hgf hfg).symm h =
      compOfMapLeSmul 𝕜 hg hD hmapg h :=
  (rfl)

end Equiv

section Affine

variable {E' F G : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Affine precomposition on restricted `Lᵖ` spaces.** For an invertible continuous linear map
`B : E' ≃L[ℝ] F`, translation `b : F`, measurable target set `t`, and `s` mapped into `t` by
`x ↦ B x + b`, precomposition `f ↦ f (B · + b)` is a bounded `𝕜`-linear operator
`Lᵖ(ν.restrict t) →L[𝕜] Lᵖ(μ.restrict s)` for any additive Haar measures `μ` and `ν`. -/
def compContinuousLinearEquivAddRestrict (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 G]
    (μ : Measure E') [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    {s : Set E'} {t : Set F} (B : E' ≃L[ℝ] F) (b : F) (ht : MeasurableSet t)
    (hst : Set.MapsTo (fun x ↦ B x + b) s t) :
    Lp G p (ν.restrict t) →L[𝕜] Lp G p (μ.restrict s) :=
  compOfMapLeSmul 𝕜 (B.continuous.add (continuous_const (y := b))).measurable.aemeasurable
    (ENNReal.coe_ne_top (r := Measure.addHaarScalarFactor (μ.map B) ν))
    (Measure.map_restrict_continuousLinearEquiv_add_le_smul_restrict μ ν B b ht hst)

/-- Precomposing an `Lᵖ` function on `ν.restrict t` with `x ↦ B x + b` agrees almost everywhere
on `μ.restrict s` with `x ↦ f (B x + b)`. -/
theorem coeFn_compContinuousLinearEquivAddRestrict {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 G]
    {μ : Measure E'} [μ.IsAddHaarMeasure] {ν : Measure F} [ν.IsAddHaarMeasure]
    {s : Set E'} {t : Set F} (B : E' ≃L[ℝ] F) (b : F) (ht : MeasurableSet t)
    (hst : Set.MapsTo (fun x ↦ B x + b) s t) (f : Lp G p (ν.restrict t)) :
    compContinuousLinearEquivAddRestrict 𝕜 μ ν B b ht hst f =ᵐ[μ.restrict s]
      fun x ↦ f (B x + b) :=
  coeFn_compOfMapLeSmul _ _ _ f

end Affine

end Lp

end MeasureTheory
