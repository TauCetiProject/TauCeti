/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic

/-!
# Fenchel–Young integrability and correlation bounds along couplings

Let `E` and `F` be measurable real vector spaces paired by a bilinear map `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`,
and let `π` be a coupling of a finite measure `μ` on `E` and a measure `ν` on `F` concentrated on
the subdifferential graph `{(x, y) | y ∈ ∂u(x)}` of an extended-real function `u : E → EReal`.

By Fenchel–Young equality on the subdifferential graph, `(u x).toReal + (u⋆ y).toReal = B x y` for
`π`-almost every `(x, y)`, where `u⋆ = TauCeti.fenchelConjugate B u`. Whenever `B` is integrable
against `π` and in each coordinate separately against `μ` and `ν`, choosing any witness `(x₀, y₀)`
in the support of a nonzero plan squeezes `(u x).toReal` and `(u⋆ y).toReal` between affine
functions of the pairing and `B`, making both real representatives integrable for the marginals.
Integrating Fenchel–Young against any competing coupling `σ` of `μ` and `ν` then shows that `π`
maximizes `∫ z, B z.1 z.2` among all such couplings.

## Main statements

* `TauCeti.IsCoupling.integrable_toReal_of_ae_mem_subdifferential` — marginal integrability of the
  real representatives of `u` and `fenchelConjugate B u` for a coupling concentrated on the
  subdifferential graph of `u`;
* `TauCeti.IsCoupling.integral_apply_le_of_ae_mem_subdifferential` — a coupling concentrated on the
  subdifferential graph of `u` maximizes `∫ z, B z.1 z.2` among couplings of the same marginals.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

section BilinearPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
  [MeasurableSpace E] [MeasurableSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  {μ : Measure E} {ν : Measure F} {π σ : Measure (E × F)}

private theorem ae_toReal_add_toReal_fenchelConjugate_eq_of_ae_mem_subdifferential
    {u : E → EReal} (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential B u z.1) :
    ∀ᵐ z ∂π, u z.1 ≠ ⊤ ∧ fenchelConjugate B u z.2 ≠ ⊤ ∧
      (u z.1).toReal + (fenchelConjugate B u z.2).toReal = B z.1 z.2 :=
  h.mono fun _ hz =>
    ⟨ne_top_of_mem_subdifferential B hz,
      fenchelConjugate_ne_top_of_mem_subdifferential B hz,
      toReal_add_toReal_fenchelConjugate_eq_of_mem_subdifferential B hz⟩

/-- For a coupling `π` of a finite measure `μ` and a measure `ν` concentrated on the
subdifferential graph of `u : E → EReal` with respect to a bilinear pairing `B`, the real
representatives of `u` and of its Legendre–Fenchel conjugate `fenchelConjugate B u` are
integrable for the marginals, provided `B` is integrable against `π` and in each coordinate
separately against the corresponding marginal. -/
theorem IsCoupling.integrable_toReal_of_ae_mem_subdifferential [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) {u : E → EReal}
    (hu : Measurable u) (hv : Measurable (fenchelConjugate B u))
    (hBπ : Integrable (fun z : E × F => B z.1 z.2) π)
    (hBμ : ∀ y : F, Integrable (fun x => B x y) μ)
    (hBν : ∀ x : E, Integrable (fun y => B x y) ν)
    (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential B u z.1) :
    Integrable (fun x => (u x).toReal) μ ∧
      Integrable (fun y => (fenchelConjugate B u y).toReal) ν := by
  have := hπ.isFiniteMeasure
  rcases eq_or_ne π 0 with rfl | hπ0
  · have hμ0 : μ = 0 := by rw [← hπ.fst_eq]; simp
    have hν0 : ν = 0 := by rw [← hπ.snd_eq]; simp
    exact ⟨by simp [hμ0], by simp [hν0]⟩
  have := ae_neBot.2 hπ0
  obtain ⟨⟨x₀, y₀⟩, h₀⟩ := h.exists
  have hx₀ := ne_top_of_mem_subdifferential B h₀
  have hy₀ := fenchelConjugate_ne_top_of_mem_subdifferential B h₀
  have hgraph := ae_toReal_add_toReal_fenchelConjugate_eq_of_ae_mem_subdifferential h
  refine ⟨?_, ?_⟩
  · refine (hπ.measurePreserving_fst.integrable_comp hu.ereal_toReal.aestronglyMeasurable).1 <|
      integrable_of_le_of_le (f := fun z => (u z.1).toReal)
        (hu.ereal_toReal.comp measurable_fst).aestronglyMeasurable
        (g₁ := fun z : E × F => B z.1 y₀ - (fenchelConjugate B u y₀).toReal)
        (g₂ := fun z : E × F => B z.1 z.2 - (B x₀ z.2 - (u x₀).toReal)) ?_ ?_
        ((hπ.integrable_comp_fst (hBμ y₀)).sub (integrable_const _))
        (hBπ.sub ((hπ.integrable_comp_snd (hBν x₀)).sub (integrable_const _)))
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate B hz.1 hy₀]
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate B hx₀ hz.2.1, hz.2.2]
  · refine (hπ.measurePreserving_snd.integrable_comp hv.ereal_toReal.aestronglyMeasurable).1 <|
      integrable_of_le_of_le (f := fun z => (fenchelConjugate B u z.2).toReal)
        (hv.ereal_toReal.comp measurable_snd).aestronglyMeasurable
        (g₁ := fun z : E × F => B x₀ z.2 - (u x₀).toReal)
        (g₂ := fun z : E × F => B z.1 z.2 - (B z.1 y₀ - (fenchelConjugate B u y₀).toReal))
        ?_ ?_
        ((hπ.integrable_comp_snd (hBν x₀)).sub (integrable_const _))
        (hBπ.sub ((hπ.integrable_comp_fst (hBμ y₀)).sub (integrable_const _)))
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate B hx₀ hz.2.1]
    · filter_upwards [hgraph] with z hz
      linarith [le_toReal_add_toReal_fenchelConjugate B hz.1 hy₀, hz.2.2]

/-- A coupling `π` concentrated on the subdifferential graph of `u : E → EReal` (where `u` and
its Legendre–Fenchel conjugate are measurable) maximizes the expected pairing `∫ z, B z.1 z.2`
among all couplings `σ` of its marginals for which `B` is integrable. -/
theorem IsCoupling.integral_apply_le_of_ae_mem_subdifferential [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hσ : IsCoupling σ μ ν) {u : E → EReal}
    (hu : Measurable u) (hv : Measurable (fenchelConjugate B u))
    (hBπ : Integrable (fun z : E × F => B z.1 z.2) π)
    (hBσ : Integrable (fun z : E × F => B z.1 z.2) σ)
    (hBμ : ∀ y : F, Integrable (fun x => B x y) μ)
    (hBν : ∀ x : E, Integrable (fun y => B x y) ν)
    (h : ∀ᵐ z ∂π, z.2 ∈ subdifferential B u z.1) :
    ∫ z, B z.1 z.2 ∂σ ≤ ∫ z, B z.1 z.2 ∂π := by
  have := hπ.isFiniteMeasure
  obtain ⟨hφ, hψ⟩ := hπ.integrable_toReal_of_ae_mem_subdifferential hu hv hBπ hBμ hBν h
  have hgraph := ae_toReal_add_toReal_fenchelConjugate_eq_of_ae_mem_subdifferential h
  have hμfin : ∀ᵐ x ∂μ, u x ≠ ⊤ := by
    rw [← hπ.measurePreserving_fst.map_eq, ae_map_iff (p := fun x => u x ≠ ⊤)
      measurable_fst.aemeasurable (hu (measurableSet_singleton ⊤).compl)]
    exact hgraph.mono fun z hz => hz.1
  have hνfin : ∀ᵐ y ∂ν, fenchelConjugate B u y ≠ ⊤ := by
    rw [← hπ.measurePreserving_snd.map_eq,
      ae_map_iff (p := fun y => fenchelConjugate B u y ≠ ⊤)
      measurable_snd.aemeasurable (hv (measurableSet_singleton ⊤).compl)]
    exact hgraph.mono fun z hz => hz.2.1
  have hσfin : ∀ᵐ z ∂σ,
      B z.1 z.2 ≤ (u z.1).toReal + (fenchelConjugate B u z.2).toReal := by
    filter_upwards [hσ.measurePreserving_fst.quasiMeasurePreserving.ae hμfin,
      hσ.measurePreserving_snd.quasiMeasurePreserving.ae hνfin] with z hx hy
    exact le_toReal_add_toReal_fenchelConjugate B hx hy
  calc ∫ z, B z.1 z.2 ∂σ
      ≤ ∫ z, ((u z.1).toReal + (fenchelConjugate B u z.2).toReal) ∂σ :=
        integral_mono_ae hBσ ((hσ.integrable_comp_fst hφ).add (hσ.integrable_comp_snd hψ)) hσfin
    _ = ∫ z, ((u z.1).toReal + (fenchelConjugate B u z.2).toReal) ∂π := by
        rw [← kantorovichDualValue_eq_integral hσ hφ hψ, kantorovichDualValue_eq_integral hπ hφ hψ]
    _ = ∫ z, B z.1 z.2 ∂π := integral_congr_ae (hgraph.mono fun z hz => hz.2.2)

end BilinearPairing

end TauCeti
