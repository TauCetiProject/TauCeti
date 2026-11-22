/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Kernel.Composition.IntegralCompProd

/-!
# Disintegration along a measurable map

This file develops generic measure- and kernel-theoretic identities for a disintegration of the
graph pushforward along a measurable map `T : X → S`, i.e. a relation
`μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K` for an s-finite measure `μ : Measure X` and an s-finite
kernel `K : Kernel S X`.

It builds directly on Mathlib's `MeasureTheory.Measure.compProd`,
`MeasureTheory.Measure.integral_compProd`, and `MeasureTheory.Measure.withDensity_compProd`,
together with Tau Ceti's `MeasureTheory.Measure.map_withDensity_comp` and
`MeasureTheory.Measure.integrable_integral_compProd`.

## Main statements

* `ProbabilityTheory.comp_map_eq_self_of_map_prodMk_eq_compProd`: marginal reconstruction
  `K ∘ₘ μ.map T = μ`.
* `ProbabilityTheory.map_prodMk_eq_compProd_iff`: rectangle characterization of disintegration
  for a finite measure `μ`.
* `ProbabilityTheory.lintegral_eq_lintegral_lintegral_of_map_prodMk_eq_compProd`: Lebesgue iterated
  integral identity.
* `ProbabilityTheory.integral_eq_integral_integral_of_map_prodMk_eq_compProd`,
  `ProbabilityTheory.integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd`, and
  `ProbabilityTheory.integral_mul_eq_integral_mul_integral_of_map_prodMk_eq_compProd`: Bochner
  iterated integral identities.
* `ProbabilityTheory.condExp_ae_eq_integral_of_map_prodMk_eq_compProd`: conditional expectation
  given `σ(T)` as fiberwise integration against `K`.
* `ProbabilityTheory.setIntegral_fst_map_prodMk_eq_measureReal_of_condExp_ae_eq`: rectangle mass
  identity for a conditional-expectation version `ψ ∘ T` of an indicator `1_{e ∈ B}`.
* `ProbabilityTheory.map_prodMk_comp_eq_compProd`: preservation of disintegrations under mixtures
  `P ∘ₘ Λ`.
* `ProbabilityTheory.eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd`: if `P ≪ L` share a
  disintegrating kernel `K` given `T`, then `P = L.withDensity ((P.map T).rnDeriv (L.map T) ∘ T)`.
* `ProbabilityTheory.map_prodMk_withDensity_comp_eq_compProd`: tilting `L` by a measurable weight
  `q ∘ T` preserves any disintegrating kernel `K` given `T`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Θ X S F : Type*} [MeasurableSpace X] [MeasurableSpace S]
  {μ : Measure X} [SFinite μ] {T : X → S} {K : Kernel S X} [IsSFiniteKernel K]

/-- Reconstructing `μ` from a disintegration `μ.map (T, id) = μ.map T ⊗ₘ K`: composing the kernel
with the marginal law `μ.map T` recovers `μ`. -/
theorem comp_map_eq_self_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) :
    K ∘ₘ μ.map T = μ := by
  rw [← Measure.snd_compProd, ← h, Measure.snd_map_prodMk hT measurable_id', Measure.map_id']

/-- Rectangle characterization of graph disintegration for a finite measure `μ`:
`μ.map (T, id) = μ.map T ⊗ₘ K` holds if and only if for all measurable `A : Set S` and
`B : Set X`, `∫⁻ x in T ⁻¹' A, K (T x) B ∂μ = μ (T ⁻¹' A ∩ B)`. -/
theorem map_prodMk_eq_compProd_iff [IsFiniteMeasure μ] (hT : Measurable T) :
    μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K ↔
      ∀ {A : Set S} {B : Set X}, MeasurableSet A → MeasurableSet B →
        ∫⁻ x in T ⁻¹' A, K (T x) B ∂μ = μ (T ⁻¹' A ∩ B) := by
  rw [Measure.ext_prod_iff]
  refine forall₂_congr fun A B ↦ forall₂_congr fun hA hB ↦ ?_
  rw [Measure.map_apply (hT.prodMk measurable_id') (hA.prod hB), Set.mk_preimage_prod,
    Set.preimage_id', Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (Kernel.measurable_coe K hB) hT, eq_comm]

/-- Lebesgue integral disintegration identity for `μ.map (T, id) = μ.map T ⊗ₘ K`. -/
theorem lintegral_eq_lintegral_lintegral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {f : S × X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (T x, x) ∂μ = ∫⁻ x, ∫⁻ y, f (T x, y) ∂K (T x) ∂μ := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hmeas : Measurable fun s ↦ ∫⁻ y, f (s, y) ∂K s :=
    Measurable.lintegral_kernel_prod_right' hf
  rw [← lintegral_map hf hpair, h, Measure.lintegral_compProd hf, lintegral_map hmeas hT]

section Bochner

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bochner integral disintegration identity for `μ.map (T, id) = μ.map T ⊗ₘ K`. -/
theorem integral_eq_integral_integral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {f : S × X → F}
    (hfm : AEStronglyMeasurable f (μ.map (fun x ↦ (T x, x))))
    (hf : Integrable (fun x ↦ f (T x, x)) μ) :
    ∫ x, f (T x, x) ∂μ = ∫ x, ∫ y, f (T x, y) ∂K (T x) ∂μ := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hf_map : Integrable f (μ.map (fun x ↦ (T x, x))) :=
    (integrable_map_measure hfm hpair.aemeasurable).mpr hf
  have hf_cp : Integrable f (μ.map T ⊗ₘ K) := h ▸ hf_map
  have hinner : AEStronglyMeasurable (fun s ↦ ∫ y, f (s, y) ∂K s) (μ.map T) :=
    (Measure.integrable_integral_compProd hf_cp).aestronglyMeasurable
  rw [← MeasureTheory.integral_map hpair.aemeasurable hfm, h, Measure.integral_compProd hf_cp,
    MeasureTheory.integral_map hT.aemeasurable hinner]

/-- Product-form Bochner integration identity under a disintegration `μ.map (T, id) = μ.map T ⊗ₘ K`,
with scalar multiplication `g (T x) • φ x`. -/
theorem integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {g : S → ℝ} (hg : Measurable g)
    {φ : X → F} (hφ : StronglyMeasurable φ) (hint : Integrable (fun x ↦ g (T x) • φ x) μ) :
    ∫ x, g (T x) • φ x ∂μ = ∫ x, g (T x) • ∫ y, φ y ∂K (T x) ∂μ := by
  have hf : StronglyMeasurable fun p : S × X ↦ g p.1 • φ p.2 :=
    (hg.comp measurable_fst).stronglyMeasurable.smul (hφ.comp_measurable measurable_snd)
  simpa [integral_smul] using
    integral_eq_integral_integral_of_map_prodMk_eq_compProd hT h hf.aestronglyMeasurable hint

/-- Product-form Bochner integration identity for bounded measurable real functions under a
disintegration of a finite measure. -/
theorem integral_mul_eq_integral_mul_integral_of_map_prodMk_eq_compProd [IsFiniteMeasure μ]
    (hT : Measurable T) (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {g : S → ℝ} (hg : Measurable g) (hgb : ∃ C, ∀ s, |g s| ≤ C)
    {φ : X → ℝ} (hφ : Measurable φ) (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    ∫ x, g (T x) * φ x ∂μ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ := by
  obtain ⟨Cg, hCg⟩ := hgb
  obtain ⟨Cφ, hCφ⟩ := hφb
  have hint : Integrable (fun x ↦ g (T x) * φ x) μ := by
    refine Integrable.of_bound ((hg.comp hT).mul hφ).aestronglyMeasurable (Cg * Cφ)
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCg (T x)) (hCφ x) (abs_nonneg _) ((abs_nonneg _).trans (hCg (T x)))
  simpa [smul_eq_mul] using
    integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd hT h hg
      hφ.stronglyMeasurable hint

/-- Conditional expectation given `σ(T)` equals integration against a disintegrating kernel `K`. -/
theorem condExp_ae_eq_integral_of_map_prodMk_eq_compProd [CompleteSpace F]
    (hT : Measurable T) [SigmaFinite (μ.trim hT.comap_le)]
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {φ : X → F} (hφ : Integrable φ μ) :
    μ[φ | MeasurableSpace.comap T inferInstance] =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x) := by
  -- Replace `φ` by a strongly measurable `μ`-a.e. equal version `φ'` so fiberwise integrals are
  -- measurable, and show both sides have the same set integrals over `T ⁻¹' B`.
  let φ' : X → F := hφ.aestronglyMeasurable.mk φ
  have hφ'm : StronglyMeasurable φ' := hφ.aestronglyMeasurable.stronglyMeasurable_mk
  have hφ'ae : φ =ᵐ[μ] φ' := hφ.aestronglyMeasurable.ae_eq_mk
  have hcomp : K ∘ₘ μ.map T = μ := comp_map_eq_self_of_map_prodMk_eq_compProd hT h
  have hinner_ae : (fun x ↦ ∫ y, φ' y ∂K (T x)) =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x) := by
    have hae_s : ∀ᵐ s ∂μ.map T, φ =ᵐ[K s] φ' :=
      Measure.ae_ae_of_ae_comp (p := fun y ↦ φ y = φ' y) (hcomp.symm ▸ hφ'ae)
    exact (ae_of_ae_map hT.aemeasurable hae_s).mono fun _ hs ↦
      integral_congr_ae (Filter.EventuallyEq.symm hs)
  have hgm : StronglyMeasurable[MeasurableSpace.comap T inferInstance]
      (fun x ↦ ∫ y, φ' y ∂K (T x)) :=
    hφ'm.integral_kernel.comp_measurable (Measurable.of_comap_le le_rfl)
  have hφ'int : Integrable φ' μ := hφ.congr hφ'ae
  have hg_int : Integrable (fun x ↦ ∫ y, φ' y ∂K (T x)) μ := by
    have hφ'cp : Integrable (fun p : S × X ↦ φ' p.2) (μ.map T ⊗ₘ K) := by
      rw [Measure.integrable_compProd_snd_iff (hcomp.symm ▸ hφ'int.aestronglyMeasurable)]
      rwa [hcomp]
    exact (integrable_map_measure hφ'm.integral_kernel.aestronglyMeasurable hT.aemeasurable).mp
      (Measure.integrable_integral_compProd hφ'cp)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hT.comap_le hφ
    (fun _ _ _ ↦ hg_int.integrableOn) (fun A hA _ ↦ ?_)
    hgm.aestronglyMeasurable).symm.trans hinner_ae
  rcases hA with ⟨B, hB, rfl⟩
  have hind (u : X → F) :
      (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ)) (T x) • u x) = (T ⁻¹' B).indicator u := by
    ext x
    rw [← Set.indicator_comp_right (f := T), ← Set.indicator_smul_apply_left]
    simp
  have hBφ : Integrable (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ)) (T x) • φ' x) μ :=
    (hind φ').symm ▸ hφ'int.indicator (hT hB)
  rw [← integral_indicator₀ (hT hB).nullMeasurableSet, ← hind,
    ← integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd hT h
      (measurable_const.indicator hB) hφ'm hBφ,
    hind, integral_indicator₀ (hT hB).nullMeasurableSet]
  exact setIntegral_congr_ae (hT hB) (hφ'ae.symm.mono fun _ hx _ ↦ hx)

end Bochner

/-- Set-integral identity for a conditional-expectation version `ψ ∘ T` of the indicator
`1_{e ∈ B}`: integrating `ψ` over `A` under the first marginal of `μ.map (T, e)` gives the
real joint mass `(μ.map (T, e)).real (A ×ˢ B)`. -/
theorem setIntegral_fst_map_prodMk_eq_measureReal_of_condExp_ae_eq {Y : Type*}
    [MeasurableSpace Y] {μ : Measure X} {T : X → S} (hT : Measurable T)
    [SigmaFinite (μ.trim hT.comap_le)] {e : X → Y} (he : Measurable e)
    {B : Set Y} (hB : MeasurableSet B) {ψ : S → ℝ}
    (hψ : AEStronglyMeasurable ψ (μ.map T))
    (hce : μ[(e ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) |
      MeasurableSpace.comap T inferInstance] =ᵐ[μ] ψ ∘ T)
    {A : Set S} (hA : MeasurableSet A) (hBfin : μ (e ⁻¹' B) ≠ ∞ := by finiteness) :
    ∫ s in A, ψ s ∂(μ.map (fun x ↦ (T x, e x))).fst =
      (μ.map (fun x ↦ (T x, e x))).real (A ×ˢ B) := by
  have hφint : Integrable ((e ⁻¹' B).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrableOn_const hBfin).integrable_indicator (he hB)
  calc ∫ s in A, ψ s ∂(μ.map (fun x ↦ (T x, e x))).fst
    _ = ∫ s in A, ψ s ∂μ.map T := by rw [Measure.fst_map_prodMk hT he]
    _ = ∫ x in T ⁻¹' A, ψ (T x) ∂μ :=
        setIntegral_map hA hψ hT.aemeasurable
    _ = ∫ x in T ⁻¹' A,
          μ[(e ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) |
            MeasurableSpace.comap T inferInstance] x ∂μ :=
        setIntegral_congr_ae (hT hA) (hce.symm.mono fun _ hx _ ↦ hx)
    _ = ∫ x in T ⁻¹' A, (e ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
        setIntegral_condExp hT.comap_le hφint ⟨A, hA, rfl⟩
    _ = μ.real (T ⁻¹' A ∩ e ⁻¹' B) := by
        rw [setIntegral_indicator (he hB), setIntegral_const, smul_eq_mul, mul_one]
    _ = (μ.map (fun x ↦ (T x, e x))).real (A ×ˢ B) := by
        rw [Measure.real, Measure.real,
          Measure.map_apply (hT.prodMk he) (hA.prod hB), Set.mk_preimage_prod]

/-- Disintegration is preserved under mixtures `P ∘ₘ Λ`: if `K` disintegrates `(P θ).map (T, id)`
for `Λ`-almost every `θ`, then `K` disintegrates `(P ∘ₘ Λ).map (T, id)`. -/
theorem map_prodMk_comp_eq_compProd [MeasurableSpace Θ] {P : Kernel Θ X} [IsSFiniteKernel P]
    {Λ : Measure Θ} [SFinite Λ] (hT : Measurable T)
    (h : ∀ᵐ θ ∂Λ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K) :
    (P ∘ₘ Λ).map (fun x ↦ (T x, x)) = (P ∘ₘ Λ).map T ⊗ₘ K := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  ext A hA
  rw [Measure.map_comp Λ P hpair, Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.compProd_apply hA, Measure.map_comp Λ P hT,
    Measure.lintegral_bind (Kernel.aemeasurable _)
      (Kernel.measurable_kernel_prodMk_left hA).aemeasurable]
  refine lintegral_congr_ae (h.mono fun θ hθ ↦ ?_)
  dsimp only
  rw [Kernel.map_apply _ hpair, Kernel.map_apply _ hT, hθ, Measure.compProd_apply hA]

/-- Reweighting a measure `L` by a measurable density `q ∘ T` factoring through `T` preserves any
disintegrating kernel `K` given `T`. -/
theorem map_prodMk_withDensity_comp_eq_compProd {L : Measure X} [SFinite L] {T : X → S}
    (hT : Measurable T) {K : Kernel S X} [IsSFiniteKernel K]
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) {q : S → ℝ≥0∞} (hq : Measurable q) :
    (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x)) = (L.withDensity (q ∘ T)).map T ⊗ₘ K := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  calc (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x))
    _ = (L.map (fun x ↦ (T x, x))).withDensity (fun p ↦ q p.1) :=
        Measure.map_withDensity_comp hpair.aemeasurable (hq.comp measurable_fst).aemeasurable
    _ = (L.map T ⊗ₘ K).withDensity (fun p ↦ q p.1) := by rw [hL]
    _ = (L.map T).withDensity q ⊗ₘ K := (Measure.withDensity_compProd hq).symm
    _ = (L.withDensity (q ∘ T)).map T ⊗ₘ K := by
        rw [← Measure.map_withDensity_comp hT.aemeasurable hq.aemeasurable]

/-- If `P ≪ L` share a disintegrating kernel `K` given a measurable map `T`, then `P` has
`L`-density `((P.map T).rnDeriv (L.map T)) ∘ T`. -/
theorem eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd {P L : Measure X} [SFinite L]
    {T : X → S} (hT : Measurable T) [(P.map T).HaveLebesgueDecomposition (L.map T)]
    {K : Kernel S X} [IsSFiniteKernel K] (hPL : P ≪ L)
    (hP : P.map (fun x ↦ (T x, x)) = P.map T ⊗ₘ K)
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) :
    P = L.withDensity ((P.map T).rnDeriv (L.map T) ∘ T) := by
  let q : S → ℝ≥0∞ := (P.map T).rnDeriv (L.map T)
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hmarg : (L.withDensity (q ∘ T)).map T = P.map T := by
    rw [Measure.map_withDensity_comp hT.aemeasurable hq.aemeasurable,
      Measure.withDensity_rnDeriv_eq (P.map T) (L.map T) (hPL.map hT)]
  have hjoint : P.map (fun x ↦ (T x, x)) = (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x)) := by
    rw [map_prodMk_withDensity_comp_eq_compProd hT hL hq, hmarg, hP]
  have hsnd := congrArg Measure.snd hjoint
  rwa [Measure.snd_map_prodMk hT measurable_id', Measure.snd_map_prodMk hT measurable_id',
    Measure.map_id', Measure.map_id'] at hsnd

end ProbabilityTheory
