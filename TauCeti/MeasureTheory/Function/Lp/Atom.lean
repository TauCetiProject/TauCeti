/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Measure.Atom
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum

/-!
# Bochner spaces over atoms

Let `A` be an atom of a measure `μ` (`MeasureTheory.Measure.IsAtom`): a measurable set of positive
measure whose measurable subsets have measure `0` or `μ A`. This file describes functions and
functionals on the Bochner space `Lᵖ(μ; X)` on and over atoms.

If `μ A < ∞`, every a.e. strongly measurable function is a.e. constant on `A`
(`MeasureTheory.AEStronglyMeasurable.exists_ae_eq_const_restrict_of_atom`), so the part of
`Lᵖ(μ; X)` living on `A` is a copy of `X`. A continuous linear map `T` on `Lᵖ(μ; X)` therefore
acts on functions supported on `A` through the single map `x ↦ T (1_A x)`, whose norm is at most
`‖T‖ μ(A) ^ (1 / p)` (`ContinuousLinearMap.norm_comp_indicatorConstLpL_le`). In integral form,
`T (1_A f) = ∫_A μ(A)⁻¹ T (1_A f(s)) dμ(s)`
(`ContinuousLinearMap.apply_toLp_indicator_eq_setIntegral_of_atom`): for a functional `Φ`,
the density of `Φ` on `A` is the functional `x ↦ μ(A)⁻¹ Φ (1_A x)`. If instead `μ A = ∞`, an `Lᵖ`
function with `p < ∞` vanishes almost everywhere on `A`
(`MeasureTheory.MemLp.ae_eq_zero_restrict_of_atom`).

If almost every point lies in one of countably many pairwise disjoint finite-measure atoms `Aᵢ`
and `p < ∞`, then `f ∈ Lᵖ(μ; X)` is the sum of its cut-offs to the atoms
(`MeasureTheory.MemLp.hasSum_toLp_indicator`), so `T f` is the sum over `i` of these integrals over
`Aᵢ` (`ContinuousLinearMap.hasSum_setIntegral_of_atoms`). At `p = 1` the local densities of a
functional `Φ` have norm at most `‖Φ‖` and assemble into one essentially bounded `X*`-valued
density. Hence, for σ-finite `μ`, the integral pairing `L∞(μ; X*) → L¹(μ; X)*` of
`ContinuousLinearMap.lpPairing` is onto, and every `Φ` has a preimage of norm `‖Φ‖`
(`TauCeti.exists_lpPairing_eq_of_atoms`).

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I, Springer,
  2016, Proposition 1.3.3 and the discussion of atomic measure spaces preceding it.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, errata to *Analysis in Banach Spaces*, Vol. I,
  <https://fa.ewi.tudelft.nl/~neerven/ABS/errata-vol1.pdf>, entry for p. 39, which corrects an
  inequality in the proof there.
-/

public section

noncomputable section

open Filter Function Set MeasureTheory Measure
open scoped ENNReal NNReal

variable {S X : Type*} [MeasurableSpace S] {μ : Measure S} [NormedAddCommGroup X] {p : ℝ≥0∞}

namespace MeasureTheory.MemLp

/-- **Infinite atoms carry no `Lᵖ` functions for finite `p`.** A function in `Lᵖ`, `0 < p < ∞`,
vanishes almost everywhere on an atom of infinite measure. -/
theorem ae_eq_zero_restrict_of_atom {f : S → X} (hf : MemLp f p μ) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {A : Set S} (hAinf : μ A = ∞) (hAatom : μ.IsAtom A) : f =ᵐ[μ.restrict A] 0 := by
  -- A nonzero `Lᵖ` function on `A` sees a subset of `A` of positive finite measure.
  by_contra hne
  obtain ⟨t, ht, ht0, htfin⟩ :=
    ((hf.restrict A).aefinStronglyMeasurable hp0 hp).exists_measurableSet_measure_pos_lt_top hne
  rw [restrict_apply ht] at ht0 htfin
  exact htfin.ne (((hAatom.measure_eq_zero_or_eq inter_subset_right).resolve_left ht0.ne').trans
    hAinf)

end MeasureTheory.MemLp

namespace ContinuousLinearMap

variable {𝕜 Y : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **A continuous linear map on `Lᵖ` over a finite atom.** On a finite-measure atom `A`, a
continuous linear map `T` on `Lᵖ(μ; X)` acts on the cut-off `1_A f` of `f ∈ Lᵖ(μ; X)` by
integrating the density `μ(A)⁻¹ T (1_A ·)` against `f` over `A`. -/
theorem apply_toLp_indicator_eq_setIntegral_of_atom [Fact (1 ≤ p)] (T : Lp X p μ →L[𝕜] Y)
    {f : S → X} (hf : MemLp f p μ) {A : Set S} (hAfin : μ A ≠ ∞) (hAatom : μ.IsAtom A) :
    T ((hf.indicator hAatom.measurableSet.nullMeasurableSet).toLp (A.indicator f)) =
      ∫ x in A, (μ.real A)⁻¹ • T.comp (TauCeti.indicatorConstLpL 𝕜 p hAatom.measurableSet hAfin)
        (f x) ∂μ := by
  obtain ⟨c, hc⟩ :=
    hf.aestronglyMeasurable.restrict.exists_ae_eq_const_restrict_of_atom hAfin hAatom
  have hA : μ.real A ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hAatom.measure_ne_zero, hAfin⟩
  rw [hf.toLp_indicator_eq_indicatorConstLp hAatom.measurableSet hAfin hc,
    integral_congr_ae (hc.mono fun x hx ↦ by rw [hx]),
    setIntegral_const, smul_inv_smul₀ hA, comp_apply, TauCeti.indicatorConstLpL_apply]

/-- **A continuous linear map on `Lᵖ` of a purely atomic measure**, `1 ≤ p < ∞`. If almost every
point lies in one of countably many pairwise disjoint finite-measure atoms `Aᵢ`, the value of a
continuous linear map `T` at `f ∈ Lᵖ(μ; X)` is the sum over the atoms of the integrals over `Aᵢ` of
the densities `μ(Aᵢ)⁻¹ T (1_{Aᵢ} ·)` against `f`. -/
theorem hasSum_setIntegral_of_atoms [Fact (1 ≤ p)] (hp : p ≠ ∞) (T : Lp X p μ →L[𝕜] Y)
    {ι : Type*} [Countable ι] {A : ι → Set S} (hA : ∀ i, μ.IsAtom (A i))
    (hAfin : ∀ i, μ (A i) ≠ ∞) (hd : Pairwise (Disjoint on A)) (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ i, A i)
    (f : Lp X p μ) :
    HasSum (fun i ↦ ∫ x in A i, (μ.real (A i))⁻¹ •
      T.comp (TauCeti.indicatorConstLpL 𝕜 p (hA i).measurableSet (hAfin i)) (f x) ∂μ) (T f) := by
  have h := ((Lp.memLp f).hasSum_toLp_indicator hp
    (fun i ↦ (hA i).measurableSet.nullMeasurableSet) hd hcov).mapL T
  rw [Lp.toLp_coeFn] at h
  exact h.congr_fun fun i ↦
    (T.apply_toLp_indicator_eq_setIntegral_of_atom (Lp.memLp f) (hAfin i) (hA i)).symm

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 X]

/-- **The dual of `L¹` of a σ-finite atomic measure.** Let `μ` be σ-finite and let almost every
point lie in one of countably many pairwise disjoint atoms `Aᵢ`. Every continuous linear functional
`Φ` on `L¹(μ; X)` is the integral pairing `f ↦ ∫ ⟨f, g⟩ dμ` with some `g ∈ L∞(μ; X*)` of norm `‖Φ‖`,
equal on each atom `Aᵢ` to the functional `x ↦ μ(Aᵢ)⁻¹ Φ (1_{Aᵢ} x)`. Thus the integral pairing
`L∞(μ; X*) → L¹(μ; X)*` is onto, and `‖Φ‖` is attained by a preimage of `Φ`. -/
theorem exists_lpPairing_eq_of_atoms [SigmaFinite μ] {ι : Type*} [Countable ι]
    {A : ι → Set S} (hA : ∀ i, μ.IsAtom (A i)) (hd : Pairwise (Disjoint on A))
    (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ i, A i) (Φ : StrongDual 𝕜 (Lp X 1 μ)) :
    ∃ g : Lp (StrongDual 𝕜 X) ∞ μ,
      (∀ i, ∀ᵐ x ∂μ.restrict (A i), g x = (μ.real (A i))⁻¹ •
        Φ.comp (indicatorConstLpL 𝕜 1 (hA i).measurableSet (hA i).measure_ne_top)) ∧
      ‖g‖ = ‖Φ‖ ∧ (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ ∞ 1 g = Φ := by
  set c : ι → StrongDual 𝕜 X := fun i ↦ (μ.real (A i))⁻¹ •
    Φ.comp (indicatorConstLpL 𝕜 1 (hA i).measurableSet (hA i).measure_ne_top)
  set g : S → StrongDual 𝕜 X := fun x ↦ ∑' i, (A i).indicator (fun _ ↦ c i) x
  have hg_eq (i : ι) (x : S) (hx : x ∈ A i) : g x = c i := by
    refine (tsum_eq_single i fun j hj ↦ ?_).trans (indicator_of_mem hx _)
    exact indicator_of_notMem (disjoint_left.1 (hd hj.symm) hx) _
  -- On each atom the density has norm at most `‖Φ‖`, by the bound for `x ↦ Φ (1_{Aᵢ} x)`.
  have hc_norm (i : ι) : ‖c i‖ ≤ ‖Φ‖ := by
    have hpos : 0 < μ.real (A i) :=
      ENNReal.toReal_pos (hA i).measure_ne_zero (hA i).measure_ne_top
    have hT := Φ.norm_comp_indicatorConstLpL_le (hA i).measurableSet (hA i).measure_ne_top
    rw [ENNReal.toReal_one, div_one, Real.rpow_one] at hT
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_le_iff₀ hpos, mul_comm]
    exact hT
  have hg_norm (x : S) : ‖g x‖ ≤ ‖Φ‖ := by
    by_cases hx : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hx
      exact (hg_eq i x hi).symm ▸ hc_norm i
    · simp_all [g]
  have hg_meas : AEStronglyMeasurable g μ := by
    rw [← restrict_eq_self_of_ae_mem hcov, aestronglyMeasurable_iUnion_iff]
    exact fun i ↦ aestronglyMeasurable_const.congr
      ((ae_restrict_mem (hA i).measurableSet).mono fun x hx ↦ (hg_eq i x hx).symm)
  have hg_mem : MemLp g ∞ μ := memLp_top_of_bound hg_meas ‖Φ‖ (.of_forall hg_norm)
  -- `Φ f` is the sum over the atoms of `Φ (1_{Aᵢ} f) = ∫_{Aᵢ} g f`.
  have hJ : (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ ∞ 1 (hg_mem.toLp g) = Φ := by
    ext f
    rw [ContinuousLinearMap.lpPairing_eq_integral, integral_congr_ae
      (hg_mem.coeFn_toLp.mono fun x hx ↦ by rw [ContinuousLinearMap.id_apply, hx])]
    have h₁ := Φ.hasSum_setIntegral_of_atoms ENNReal.one_ne_top hA (fun i ↦ (hA i).measure_ne_top)
      hd hcov f
    have h₂ := hasSum_integral_iUnion (fun i ↦ (hA i).measurableSet) hd
      (hg_mem.integrable_apply (Lp.memLp f)).integrableOn
    rw [restrict_eq_self_of_ae_mem hcov] at h₂
    refine h₂.unique (h₁.congr_fun fun i ↦ setIntegral_congr_fun (hA i).measurableSet fun x hx ↦ ?_)
    simp [hg_eq i x hx, c]
  refine ⟨hg_mem.toLp g, fun i ↦ ?_, le_antisymm ?_ ?_, hJ⟩
  · filter_upwards [ae_restrict_of_ae hg_mem.coeFn_toLp, ae_restrict_mem (hA i).measurableSet]
      with x hx hxA
    rw [hx, hg_eq i x hxA]
  · exact Lp.norm_le_of_ae_bound_top (norm_nonneg Φ)
      (hg_mem.coeFn_toLp.mono fun x hx ↦ hx ▸ hg_norm x)
  · -- the integral pairing is a contraction, by Hölder's inequality
    calc ‖Φ‖
        = ‖(ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ ∞ 1 (hg_mem.toLp g)‖ := by
          rw [hJ]
      _ ≤ ‖hg_mem.toLp g‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans <| mul_le_of_le_one_left (norm_nonneg _) <|
          (ContinuousLinearMap.norm_lpPairing_le _).trans (ContinuousLinearMap.norm_id_le)

end TauCeti
