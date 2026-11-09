/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Analysis.Distribution.Mass.Measure
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.MeasureTheory.Measure.Decomposition.CommonDensity
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.OrderZero
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.AEEqOfLIntegral

/-!
# The polar decomposition of a current of locally finite mass

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a
finite-dimensional real normed space and let `T : 𝓓(Ω, F) →L[ℝ] ℝ` have locally finite mass
(`Distribution.HasLocallyFiniteMass`). With `F = E [⋀^Fin k]→L[ℝ] ℝ` this is a `k`-current of
locally finite mass. Then `T` is represented by integration against its mass measure
`‖T‖ = Distribution.massMeasure T` with a density of dual norm one:

`T φ = ∫ τ(x) (φ x) d‖T‖(x)` for every `φ ∈ 𝓓(Ω, F)`, and `‖τ(x)‖ = 1` for `‖T‖`-almost every `x`.

The **polar density** `τ = Distribution.polarDensity T` takes values in the native normed dual
`StrongDual ℝ F` of the fibre, with its dual norm. For `F = E [⋀^Fin k]→L[ℝ] ℝ` over an inner
product space `E`, the norm on `F` is the comass and its dual norm is the mass norm of `k`-vectors,
under `exteriorPower.formDualEquiv`; so `τ(x)` is Federer's orientation `vec T (x)` of the current,
and the representation is `T = ‖T‖ ∧ vec T`. The density is unique `‖T‖`-almost everywhere
(`Distribution.ae_eq_polarDensity`). The mass measure lives on the open domain `Ω` and need not be
finite near its frontier, so the density is only locally integrable.

The proof assembles the scalar distributions `ψ ↦ T (ψ • bᵢ)` along a basis `b` of `F`. Each has
order zero, so it is a difference of two regular measures
(`Distribution.forall_exists_abs_le_iff_exists_regular`). With respect to a common reference
measure `ρ`, which also dominates `‖T‖` (`MeasureTheory.Measure.exists_common_density_sub`),
their densities form a dual-valued field `g` with `T φ = ∫ g(x) (φ x) dρ`. A test of norm at
most one supported in an open `U` has `|T φ| ≤ ‖T‖(U)`, so the dual norm of `g` is at most the
density of `‖T‖` with respect to `ρ` (`TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le`), and
`τ = g / (d‖T‖/dρ)` has norm at most one. Testing the supremum that defines `‖T‖(U)` against this
representation gives `‖T‖(U) ≤ ∫_U ‖τ‖ d‖T‖`, hence `‖τ‖ = 1`
(`TauCeti.ae_eq_one_of_measure_le_setLIntegral`).

## Main declarations

* `Distribution.polarDensity T`: the polar density `τ : Ω → StrongDual ℝ F` of `T` with respect to
  its mass measure.
* `Distribution.apply_eq_integral_polarDensity`: the representation `T φ = ∫ τ(x) (φ x) d‖T‖`.
* `Distribution.ae_norm_polarDensity_eq_one`: `‖τ‖ = 1` at `‖T‖`-almost every point.
* `Distribution.locallyIntegrable_polarDensity`: `τ` is locally integrable with respect to `‖T‖`.
* `Distribution.integrable_polarDensity_apply`: the integrand `x ↦ τ(x) (φ x)` is integrable.
* `Distribution.ae_eq_polarDensity`: a locally integrable dual-valued field representing `T`
  against `‖T‖` is `τ` almost everywhere.
* `Distribution.polarDensity_of_not_hasLocallyFiniteMass`: without locally finite mass the polar
  density is `0` by convention.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7 (currents representable by
  integration, `T = ‖T‖ ∧ vec T`).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8 (the Riesz representation theorem for vector-valued functionals and its polar density).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

namespace Distribution

open MeasureTheory TopologicalSpace TestFunction Set
open scoped ENNReal Distributions BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {Ω : Opens E} {T : 𝓓(Ω, F) →L[ℝ] ℝ}

/-- A distribution of locally finite mass is represented by integration against a measurable
field `g` of linear functionals, locally integrable with respect to a measure `ρ` that is finite on
compact sets and dominates `‖T‖`. -/
private theorem exists_measurable_dual_density (hT : HasLocallyFiniteMass T) :
    ∃ ρ : Measure Ω, IsFiniteMeasureOnCompacts ρ ∧ massMeasure T ≪ ρ ∧
      ∃ g : Ω → StrongDual ℝ F, Measurable g ∧ LocallyIntegrable g ρ ∧
        ∀ φ : 𝓓(Ω, F), T φ = ∫ x, g x (φ x) ∂ρ := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := massMeasure T
  let b := Module.finBasis ℝ F
  -- The coordinate functionals of `b`.
  let c : Fin _ → StrongDual ℝ F := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  -- The scalar distributions `ψ ↦ T (ψ • b i)` have order zero.
  let S : Fin _ → 𝓓(Ω, ℝ) →L[ℝ] ℝ := fun i =>
    T ∘L postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i))
  have hS (i) : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ ψ : 𝓓(Ω, ℝ), tsupport ψ ⊆ K →
      |S i ψ| ≤ C * ‖(ψ : E →ᵇ ℝ)‖ := by
    have hL : HasLocallyFiniteMass (S i) :=
      hT.comp_of_norm_apply_le (L := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)))
        continuous_const (b := fun _ => ‖b i‖) fun ψ x => by simp [norm_smul, mul_comm]
    intro K hK hKΩ
    obtain ⟨C, -, hC⟩ := hasLocallyFiniteMass_def.1 hL K hK hKΩ
    exact ⟨C, fun ψ hψ => (Real.norm_eq_abs _).symm.trans_le (hC ψ hψ)⟩
  choose ν₁ ν₂ h₁ h₂ hν using fun i => (forall_exists_abs_le_iff_exists_regular (S i)).1 (hS i)
  -- Densities `f i` of the scalar distributions against a reference measure `ρ` dominating `‖T‖`.
  have (i : _) : IsFiniteMeasureOnCompacts (ν₁ i) := ⟨fun _ hK => (h₁ i).lt_top_of_isCompact hK⟩
  have (i : _) : IsFiniteMeasureOnCompacts (ν₂ i) := ⟨fun _ hK => (h₂ i).lt_top_of_isCompact hK⟩
  obtain ⟨ρ, hρ, hlam, f, hfm, hfK, hf⟩ := lam.exists_common_density_sub ν₁ ν₂
  have hψ (ν : Measure Ω) [IsFiniteMeasureOnCompacts ν] (ψ : 𝓓(Ω, ℝ)) :
      Integrable (fun x : Ω => ψ x) ν :=
    ψ.toCompactlySupportedContinuousMap.integrable.congr
      (ae_of_all _ (toCompactlySupportedContinuousMap_apply ψ))
  have hf' (i) (ψ : 𝓓(Ω, ℝ)) := hf i _ (hψ (ν₁ i) ψ) (hψ (ν₂ i) ψ)
  -- The dual-valued field `g` assembled from the densities `f i`.
  set g : Ω → StrongDual ℝ F := fun x => ∑ i, f i x • c i with hg
  have hgm : Measurable g := Finset.measurable_sum _ fun i _ => (hfm i).smul_const _
  have hrep (φ : 𝓓(Ω, F)) : T φ = ∫ x, g x (φ x) ∂ρ := by
    -- The coordinates of `φ` in the basis `b`.
    set ψ : _ → 𝓓(Ω, ℝ) := fun i => postcompCLM (c i) φ
    have hφ : φ = ∑ i, postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ψ i) := by
      simpa only [ψ, c] using (sum_postcompCLM_toSpanSingleton_coord b φ).symm
    calc T φ = ∑ i, S i (ψ i) := by
          conv_lhs => rw [hφ]
          simp [S]
      _ = ∑ i, ∫ x, f i x * ψ i x ∂ρ :=
          Finset.sum_congr rfl fun i _ => (hν i (ψ i)).trans (hf' i (ψ i)).2.symm
      _ = ∫ x, g x (φ x) ∂ρ := by
          rw [← integral_finsetSum _ fun i _ => (hf' i (ψ i)).1]
          congr 1 with x
          simp [hg, ψ]
  have hgint : LocallyIntegrable g ρ := locallyIntegrable_iff.2 fun K hK =>
    integrable_finsetSum _ fun i _ => (hfK i K hK).smul_const (c i)
  exact ⟨ρ, hρ, hlam, g, hgm, hgint, hrep⟩

/-- Existence of a density of dual norm at most one representing `T` against `‖T‖`. -/
private theorem exists_le_one (hT : HasLocallyFiniteMass T) :
    ∃ τ : Ω → StrongDual ℝ F, Measurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ ≤ 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := massMeasure T
  obtain ⟨ρ, hρ, hlam, g, hgm, hgint, hrep⟩ := exists_measurable_dual_density hT
  -- The dual norm of `g` is bounded by the density `k` of `‖T‖` with respect to `ρ`.
  set k := lam.rnDeriv ρ
  have hbound : ∀ᵐ x ∂ρ, ‖g x‖ₑ ≤ k x := by
    refine TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le hgint
      (Measure.measurable_rnDeriv _ _)
      (fun K hK => ne_top_of_le_ne_top hK.measure_lt_top.ne (Measure.setLIntegral_rnDeriv_le K))
      fun U hU φ hφU hφ => ?_
    rw [Measure.setLIntegral_rnDeriv hlam, ← hrep, massMeasure_preimage_coe hT U.isOpen]
    exact enorm_le_localMass hφU hφ
  -- Normalize `g` by `k`.
  obtain ⟨σ, hσm, hσ1, hσg⟩ := Measure.exists_norm_le_one_toReal_rnDeriv_smul_eq hlam hgm hbound
  refine ⟨σ, hσm, hσ1, fun φ => ?_⟩
  rw [hrep, ← integral_toReal_rnDeriv_mul hlam]
  refine integral_congr_ae ?_
  filter_upwards [hσg] with x hx
  rw [← hx, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ F] in
/-- A density of dual norm at most one representing `T` against `‖T‖` has norm one almost
everywhere. -/
private theorem ae_norm_eq_one_of_le_one (hT : HasLocallyFiniteMass T) {τ : Ω → StrongDual ℝ F}
    (hτ1 : ∀ᵐ x ∂massMeasure T, ‖τ x‖ ≤ 1)
    (hτ : ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T) :
    ∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1 := by
  have := Ω.isOpen.locallyCompactSpace
  -- Testing the supremum defining `‖T‖(V)` gives `‖T‖(V) ≤ ∫_V ‖τ‖ d‖T‖` on open sets.
  have hopen (V : Set Ω) (hV : IsOpen V) : massMeasure T V ≤ ∫⁻ x in V, ‖τ x‖ₑ ∂massMeasure T := by
    set U : Set E := (↑) '' V
    have hU : IsOpen U := Ω.isOpen.isOpenMap_subtype_val V hV
    have hUV : ((↑) : Ω → E) ⁻¹' U = V := preimage_image_eq V Subtype.val_injective
    rw [← hUV, massMeasure_preimage_coe hT hU, localMass_le_iff]
    intro φ hφU hφ
    rw [hτ φ, hUV, ← lintegral_indicator hV.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx]
      refine ((τ x).le_opENorm (φ x)).trans ?_
      calc ‖τ x‖ₑ * ‖φ x‖ₑ ≤ ‖τ x‖ₑ * 1 := by
            gcongr
            rw [← ofReal_norm, ENNReal.ofReal_le_one]
            exact hφ x
        _ = ‖τ x‖ₑ := mul_one _
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        obtain ⟨y, hy, hyx⟩ := hφU h
        exact hx (Subtype.val_injective hyx ▸ hy)
      simp [this]
  filter_upwards [TauCeti.ae_eq_one_of_measure_le_setLIntegral
    (hτ1.mono fun x hx => by rwa [← ofReal_norm, ENNReal.ofReal_le_one]) hopen] with x hx
  rwa [← ofReal_norm, ENNReal.ofReal_eq_one] at hx

private theorem exists_polarDensity (hT : HasLocallyFiniteMass T) :
    ∃ τ : Ω → StrongDual ℝ F, Measurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T :=
  let ⟨τ, hτm, hτ1, hτ⟩ := exists_le_one hT
  ⟨τ, hτm, ae_norm_eq_one_of_le_one hT hτ1 hτ, hτ⟩

open scoped Classical in
/-- The **polar density** `τ` of a functional `T` on `F`-valued test functions on `Ω` with respect
to its mass measure `‖T‖`: if `T` has locally finite mass, it is a measurable field
`τ : Ω → StrongDual ℝ F` of dual norm one at `‖T‖`-almost every point
(`Distribution.ae_norm_polarDensity_eq_one`) such that `T φ = ∫ τ(x) (φ x) d‖T‖` for every test
`φ` (`Distribution.apply_eq_integral_polarDensity`). For a `k`-current, with
`F = E [⋀^Fin k]→L[ℝ] ℝ`, it is the orientation `vec T` of `T`, read as a `k`-vector through
`exteriorPower.formDualEquiv`. It is determined `‖T‖`-almost everywhere
(`Distribution.ae_eq_polarDensity`). If no such field exists it is `0` by convention. -/
def polarDensity (T : 𝓓(Ω, F) →L[ℝ] ℝ) : Ω → StrongDual ℝ F :=
  if h : ∃ τ : Ω → StrongDual ℝ F, Measurable τ ∧ (∀ᵐ x ∂massMeasure T, ‖τ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T then h.choose
  else 0

omit [FiniteDimensional ℝ F] in
/-- The polar density is measurable. -/
@[fun_prop]
theorem measurable_polarDensity : Measurable (polarDensity T) := by
  unfold polarDensity
  split_ifs with h
  exacts [h.choose_spec.1, measurable_const]

omit [FiniteDimensional ℝ F] in
/-- The polar density of a functional without locally finite mass is `0`, by convention. -/
@[simp]
theorem polarDensity_of_not_hasLocallyFiniteMass (hT : ¬HasLocallyFiniteMass T) :
    polarDensity T = 0 := by
  unfold polarDensity
  split_ifs with h
  · obtain ⟨τ, -, -, h⟩ := h
    have hT0 : T = 0 := by
      ext φ
      simp [h φ, massMeasure_of_not_hasLocallyFiniteMass hT]
    subst hT0
    exact absurd (by simpa using hasLocallyFiniteMass_zero) hT
  · rfl

private theorem polarDensity_spec (hT : HasLocallyFiniteMass T) :
    (∀ᵐ x ∂massMeasure T, ‖polarDensity T x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, F), T φ = ∫ x, polarDensity T x (φ x) ∂massMeasure T := by
  rw [polarDensity, dite_eq_left (exists_polarDensity hT)]
  exact (exists_polarDensity hT).choose_spec.2

/-- **The polar decomposition `T = τ ‖T‖`.** A functional `T` on test functions with locally
finite mass is integration of `τ(x) (φ x)` against its mass measure, where `τ` is its polar
density. -/
theorem apply_eq_integral_polarDensity (hT : HasLocallyFiniteMass T) (φ : 𝓓(Ω, F)) :
    T φ = ∫ x, polarDensity T x (φ x) ∂massMeasure T :=
  (polarDensity_spec hT).2 φ

/-- The polar density of a functional of locally finite mass has dual norm one at `‖T‖`-almost
every point. -/
theorem ae_norm_polarDensity_eq_one (hT : HasLocallyFiniteMass T) :
    ∀ᵐ x ∂massMeasure T, ‖polarDensity T x‖ = 1 :=
  (polarDensity_spec hT).1

/-- The polar density of a functional of locally finite mass is locally integrable with respect
to its mass measure. -/
theorem locallyIntegrable_polarDensity (hT : HasLocallyFiniteMass T) :
    LocallyIntegrable (polarDensity T) (massMeasure T) := by
  have := Ω.isOpen.locallyCompactSpace
  exact locallyIntegrable_iff.2 fun K hK => Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    measurable_polarDensity.aestronglyMeasurable (M := 1)
    (ae_restrict_of_ae ((ae_norm_polarDensity_eq_one hT).mono fun x hx => hx.le))

/-- The pairing `x ↦ τ(x) (φ x)` of a test with the polar density is integrable with respect to
the mass measure, for a functional of locally finite mass. -/
theorem integrable_polarDensity_apply (hT : HasLocallyFiniteMass T) (φ : 𝓓(Ω, F)) :
    Integrable (fun x : Ω => polarDensity T x (φ x)) (massMeasure T) :=
  φ.integrable_bilin_subtype (ContinuousLinearMap.apply ℝ ℝ) (locallyIntegrable_polarDensity hT)

/-- **Uniqueness of the polar density.** A locally integrable field `τ : Ω → StrongDual ℝ F` with
`T φ = ∫ τ(x) (φ x) d‖T‖` for every test `φ` agrees with the polar density of `T` at `‖T‖`-almost
every point. -/
theorem ae_eq_polarDensity (hT : HasLocallyFiniteMass T) {τ : Ω → StrongDual ℝ F}
    (hτ : LocallyIntegrable τ (massMeasure T))
    (h : ∀ φ : 𝓓(Ω, F), T φ = ∫ x, τ x (φ x) ∂massMeasure T) :
    τ =ᵐ[massMeasure T] polarDensity T := by
  have := Ω.isOpen.locallyCompactSpace
  have hint (φ : 𝓓(Ω, F)) : Integrable (fun x : Ω => τ x (φ x)) (massMeasure T) :=
    φ.integrable_bilin_subtype (ContinuousLinearMap.apply ℝ ℝ) hτ
  have h0 := TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le (k := 0)
    (hτ.sub (locallyIntegrable_polarDensity hT)) measurable_const (by simp)
    fun U _ φ _ _ => by
      simp only [Pi.sub_apply, sub_apply]
      rw [integral_sub (hint φ) (integrable_polarDensity_apply hT φ), ← h,
        ← apply_eq_integral_polarDensity hT]
      simp
  filter_upwards [h0] with x hx
  rwa [Pi.zero_apply, nonpos_iff_eq_zero, enorm_eq_nnnorm, ENNReal.coe_eq_zero, nnnorm_eq_zero,
    Pi.sub_apply, sub_eq_zero] at hx

end Distribution
