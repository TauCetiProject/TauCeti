/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Constancy.Current
public import TauCeti.Analysis.Distribution.Rectifiable.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.Analysis.Matrix.MeasurableSpace

/-!
# Integral constancy in top degree

Let `V` be a real inner product space of dimension `k + 1`, `b` an orthonormal basis and `Ω ⊆ V` a
connected open set. The constancy theorem
(`Orientation.existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero`) says that a
top-degree current `T` on `Ω` with `∂T = 0` is `c • [[Ω]]` for a unique real `c`. If `T` is moreover
integer-rectifiable, in particular if it is locally integral, then `c` is an integer.

Write `T ω = ∫ θ(x) ω_x(τ(x)) dx` with integer multiplicity `θ` and orthonormal frames `τ`. Since
`τ(x)` and `b` are orthonormal bases of the same space, `ω_x(τ(x)) = d(x) ω_x(b)` with
`d(x) = det ⟪b_i, τ(x)_j⟫ = ±1`. Testing against the forms `g • det_b` for scalar tests `g` gives
`∫ g (θ d - c) = 0` for every test `g` on `Ω`, so `θ d = c` almost everywhere on `Ω`; as `Ω` has
positive measure, `c = ±θ(x)` at some point.

This is the integer constancy of G2 of the GeometricCurrents roadmap, in top degree.

## Main results

* `Distribution.IsIntegerRectifiable.exists_eq_zsmul_integrationCurrent`: an integer-rectifiable
  top-degree current with zero boundary on a connected open set is an integer multiple of `[[Ω]]`.
* `Distribution.IsLocallyIntegral.exists_eq_zsmul_integrationCurrent`: the same for locally
  integral currents.
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction MeasureTheory Module
open scoped Distributions RealInnerProductSpace

namespace Distribution

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {k : ℕ}

/-- If `d θ = c` almost everywhere on a nonempty open set, where `θ` is integer-valued and `d = ±1`
wherever `θ ≠ 0`, then `c` is an integer. -/
private theorem exists_int_of_ae_mul_sub_eq_zero (hΩ : (Ω : Set V).Nonempty) {θ : V → ℤ}
    {d : V → ℝ} (hd : ∀ x, θ x ≠ 0 → d x = 1 ∨ d x = -1) {c : ℝ}
    (hzero : ∀ᵐ x ∂volume, x ∈ (Ω : Set V) → d x * θ x - c = 0) : ∃ n : ℤ, c = n := by
  have hpos : volume.restrict (Ω : Set V) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (Ω.isOpen.measure_pos volume hΩ).ne'
  have : (ae (volume.restrict (Ω : Set V))).NeBot := ae_neBot.2 hpos
  obtain ⟨x, hx⟩ := ((ae_restrict_iff' Ω.isOpen.measurableSet).2 hzero).exists
  have hfx : d x * θ x = c := sub_eq_zero.1 hx
  by_cases hθx : θ x = 0
  · exact ⟨0, by simp [← hfx, hθx]⟩
  · rcases hd x hθx with h1 | h1
    · exact ⟨θ x, by simp [← hfx, h1]⟩
    · exact ⟨-θ x, by simp [← hfx, h1]⟩

/-- If the frame current of an integer multiplicity in top degree is a real multiple `c` of the
integration current on a nonempty open set, then `c` is an integer. -/
private theorem exists_int_eq_of_frameCurrent_eq_smul (b : OrthonormalBasis (Fin (k + 1)) ℝ V)
    (hΩ : (Ω : Set V).Nonempty) {θ : V → ℤ} {τ : V → Fin (k + 1) → V} (hτ : Measurable τ)
    (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k + 1])
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {c : ℝ}
    (h : (frameCurrent (fun x ↦ (θ x : ℝ)) τ : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      c • b.toBasis.orientation.integrationCurrent Ω) :
    ∃ n : ℤ, c = n := by
  have hμ : (μHE[k + 1] : Measure V) = volume := by
    rw [← (by simpa using finrank_eq_card_basis b.toBasis : finrank ℝ V = k + 1)]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have hτo' : ∀ x, (θ x : ℝ) ≠ 0 → Orthonormal ℝ (τ x) := fun x hx ↦ hτo x (by exact_mod_cast hx)
  have hspan (x : V) : ∀ j, τ x j ∈ Submodule.span ℝ (range b) := fun j ↦ by
    simpa [b.coe_toBasis] using b.toBasis.mem_span (τ x j)
  -- Change to the constant frame `b`; the multiplicity picks up the sign
  -- `d(x) = det ⟪b_i, τ(x)_j⟫` of the frame relative to `b`.
  rw [frameCurrent_eq_det_inner_mul hθ measurable_const (fun _ _ ↦ b.orthonormal) hτ hτo'
    fun x _ ↦ hspan x] at h
  set d : V → ℝ := fun x ↦ (Matrix.of fun j i ↦ ⟪b i, τ x j⟫).det
  have hd (x : V) (hx : θ x ≠ 0) : d x = 1 ∨ d x = -1 :=
    Orthonormal.det_inner_eq_one_or_eq_neg_one b.orthonormal (hτo x hx) (hspan x)
  have hdθ : LocallyIntegrableOn (fun x ↦ d x * θ x) Ω μHE[k + 1] :=
    hθ.bdd_mul_of_ne_zero (C := 1) (by fun_prop : Measurable d).aestronglyMeasurable
      (ae_of_all _ fun x hx ↦ by rcases hd x (by exact_mod_cast hx) with h1 | h1 <;> simp [h1])
  have hf : LocallyIntegrableOn (fun x ↦ d x * θ x - c) Ω volume :=
    (hμ ▸ hdθ).sub ((locallyIntegrable_const c).locallyIntegrableOn _)
  -- Testing against `g • det_b` gives `∫ g (d θ - c) = 0`.
  have hzero := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
    fun g hg hgc hgΩ ↦ by
      set ω : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
        b.toBasis.testTopFormEquiv.symm ⟨g, hg, hgc, hgΩ⟩
      have hωb (x : V) : ω x b = g x := by
        rw [← b.coe_toBasis]
        exact Basis.testTopFormEquiv_symm_apply_self _ _ x
      have h1 := congrArg (fun T ↦ T ω) h
      rw [frameCurrent_apply hdθ measurable_const (fun _ _ ↦ b.orthonormal), smul_apply,
        smul_eq_mul, Orientation.integrationCurrent_apply_eq_integral_volume _ b rfl, hμ] at h1
      have hint1 : Integrable (fun x ↦ d x * θ x * ω x b) volume :=
        hμ ▸ integrable_frameCurrent_integrand hdθ measurable_const (fun _ _ ↦ b.orthonormal) ω
      have hint2 : Integrable (fun x ↦ ω x b) volume := by
        simpa only [hωb] using hg.continuous.integrable_of_hasCompactSupport hgc
      calc ∫ x, g x • (d x * θ x - c) = ∫ x, (d x * θ x * ω x b - c * ω x b) :=
            integral_congr_ae (ae_of_all _ fun x ↦ by simp only [hωb, smul_eq_mul]; ring)
        _ = 0 := by
          rw [integral_sub hint1 (hint2.const_mul c), integral_const_mul, h1, sub_self]
  exact exists_int_of_ae_mul_sub_eq_zero hΩ hd hzero

/-- **Integral constancy in top degree.** On a connected open subset `Ω` of a real inner product
space of dimension `k + 1`, an integer-rectifiable top-degree current with zero boundary is an
integer multiple of the integration current `[[Ω]]` (for the orientation of any orthonormal basis
`b`). -/
theorem IsIntegerRectifiable.exists_eq_zsmul_integrationCurrent
    (b : OrthonormalBasis (Fin (k + 1)) ℝ V) (hΩ : IsConnected (Ω : Set V))
    {T : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsIntegerRectifiable T)
    (hdT : T ∘L extDerivCLM = 0) :
    ∃ n : ℤ, T = (n : ℝ) • b.toBasis.orientation.integrationCurrent Ω := by
  have hm : finrank ℝ V = k + 1 := by simpa using finrank_eq_card_basis b.toBasis
  obtain ⟨c, hc, -⟩ :=
    b.toBasis.orientation.existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero hm
      hΩ hdT
  obtain ⟨θ, τ, -, hτ, -, hθ, hτo, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  obtain ⟨n, rfl⟩ := exists_int_eq_of_frameCurrent_eq_smul b hΩ.nonempty hτ hθ hτo hc
  exact ⟨n, hc⟩

/-- **Integral constancy for locally integral currents in top degree.** On a connected open subset
`Ω` of a real inner product space of dimension `k + 1`, a locally integral top-degree current with
zero boundary is an integer multiple of `[[Ω]]`. -/
theorem IsLocallyIntegral.exists_eq_zsmul_integrationCurrent
    (b : OrthonormalBasis (Fin (k + 1)) ℝ V) (hΩ : IsConnected (Ω : Set V))
    {T : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsLocallyIntegral T)
    (hdT : T ∘L extDerivCLM = 0) :
    ∃ n : ℤ, T = (n : ℝ) • b.toBasis.orientation.integrationCurrent Ω :=
  hT.isIntegerRectifiable.exists_eq_zsmul_integrationCurrent b hΩ hdT

end Distribution
