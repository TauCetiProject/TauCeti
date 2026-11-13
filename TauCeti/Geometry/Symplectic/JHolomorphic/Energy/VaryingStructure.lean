/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
import TauCeti.Geometry.Symplectic.Area.Basic
import TauCeti.Geometry.Symplectic.Duality

/-!
# The `L²` estimate of Cauchy--Riemann operators with domain-dependent structures

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `J(z)` be an `ω`-compatible
complex structure on `V` depending continuously on the domain point `z = (s, t)` of a compact set
`K ⊆ ℝ × ℝ`, with associated inner products `g_z = ω(·, J(z) ·)`. The Wirtinger identity
`e_z(dξ) - 2 ω(∂s ξ, ∂t ξ) = g_z(∂s ξ + J(z) ∂t ξ, ∂s ξ + J(z) ∂t ξ)` holds pointwise for every
`z`, and the area density `ω(∂s ξ, ∂t ξ)` does not involve `J` at all. So whenever the symplectic
area of `ξ` over `K` vanishes, the energy identity

`∫_K e_z(dξ) = ∫_K g_z(∂s ξ + J(z) ∂t ξ, ∂s ξ + J(z) ∂t ξ)`

holds although `J` varies with `z`
(`SymplecticForm.setIntegral_stdComplexLineEnergyDensity_eq_of_setIntegral_symplecticForm_eq_zero`).
Because `ω` is constant, no smallness of the variation of `J` is needed. The area vanishes for
`C²` maps with compact support in `K` (`SymplecticForm.setIntegral_symplecticForm_fderiv_eq_zero`
in `TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport`), and for `C²` maps that close
up in `t`, `ξ(s, 1) = ξ(s, 0)` for `s ∈ [a, b]`, and vanish on the two slices `s = a` and `s = b`
of the rectangle `[a, b] × [0, 1]`
(`SymplecticForm.integral_symplecticForm_fderiv_prod_Icc_eq_zero_of_periodic` in
`TauCeti.Geometry.Symplectic.Area.Basic`).

Together with the uniform equivalence of the `g_z` with the norm of `V` over `K`, this gives the
`L²` estimate of the operator `D ξ = ∂s ξ + J(z) ∂t ξ + T(z) ξ` with a continuous zeroth-order
term `T`: there is a constant `C`, depending only on `J`, `T` and `K`, such that

`∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖D ξ‖² + ‖ξ‖²)`

for every such `ξ`. This is the plane version
`SymplecticForm.exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset` and the cylinder
version `SymplecticForm.exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic`, both derived from
`SymplecticForm.exists_forall_setIntegral_norm_fderiv_sq_le_of_setIntegral_symplecticForm_eq_zero`.
Linearized operators of Floer theory have this form
(`TauCeti.Geometry.Symplectic.Floer.InteriorEstimate`), and this is their estimate on a compact
part of the domain, which needs no nondegeneracy hypothesis. In contrast with
`TauCeti.Geometry.Symplectic.JHolomorphic.InteriorEstimate`, the structure need not be close to a
constant one, but it must be compatible with `ω` at every point of `K`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 2.2
  (the energy identity) and Appendix B (`L²` estimates for the Cauchy--Riemann operator).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

namespace TauCeti

open MeasureTheory Set

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : ℝ × ℝ → AlmostComplexStructure V} {K : Set (ℝ × ℝ)}
variable {μ : Measure (ℝ × ℝ)}

/-- **The energy identity for a domain-dependent structure.** Let `J(z)` leave `ω` invariant at
every point of a compact set `K` and depend continuously on `z ∈ K`, and let `ξ` be a `C¹` map
whose symplectic area over `K` vanishes. Then the integrated energy density of `ξ` over `K`
equals the integrated square `g_z(D ξ, D ξ)` of its Cauchy--Riemann defect
`D ξ = ∂s ξ + J(z) ∂t ξ`, for `g_z = ω(·, J(z) ·)`, against any measure that is finite on compact
sets. For a constant structure and a compactly supported `ξ` with `K` containing its support, this
is `SymplecticForm.integral_stdComplexLineEnergyDensity_eq_of_integral_symplecticForm_eq_zero`. -/
theorem setIntegral_stdComplexLineEnergyDensity_eq_of_setIntegral_symplecticForm_eq_zero
    [IsFiniteMeasureOnCompacts μ] (hK : IsCompact K) (hJ : ∀ z ∈ K, ω.Invariant (J z))
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) K) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ)
    (hzero : ∫ z in K,
      ω (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineImag) ∂μ = 0) :
    ∫ z in K, ω.stdComplexLineEnergyDensity (J z) (fderiv ℝ ξ z).toLinearMap ∂μ =
      ∫ z in K, ω.associatedBilinForm (J z)
        (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag))
        (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag)) ∂μ := by
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hs : ContinuousOn (fun z ↦ fderiv ℝ ξ z stdComplexLineReal) K :=
    (hdξ.clm_apply continuous_const).continuousOn
  have ht : ContinuousOn (fun z ↦ fderiv ℝ ξ z stdComplexLineImag) K :=
    (hdξ.clm_apply continuous_const).continuousOn
  have he : IntegrableOn
      (fun z ↦ ω.stdComplexLineEnergyDensity (J z) (fderiv ℝ ξ z).toLinearMap) K μ := by
    simp only [stdComplexLineEnergyDensity_def, ContinuousLinearMap.coe_coe]
    exact ((continuousOn_associatedBilinForm_apply_self hJc hs).add
      (continuousOn_associatedBilinForm_apply_self hJc ht)).integrableOn_compact hK
  have harea : IntegrableOn
      (fun z ↦ ω (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineImag)) K μ :=
    (ω.continuousOn_apply_comp hs ht).integrableOn_compact hK
  rw [← sub_zero (∫ z in K, _ ∂μ), ← mul_zero (2 : ℝ), ← hzero, ← integral_const_mul,
    ← integral_sub he (harea.const_mul 2)]
  refine setIntegral_congr_fun hK.measurableSet fun z hz ↦ ?_
  simpa using stdComplexLineEnergyDensity_sub_two_mul_symplecticForm (hJ z hz)
    (fderiv ℝ ξ z).toLinearMap

/-- **The `L²` estimate of a Cauchy--Riemann operator with a domain-dependent compatible
structure.** Let `J(z)` be `ω`-compatible at every point of a compact set `K` and depend
continuously on `z ∈ K`, and let `T(z)` be a continuous family of operators on `K`. Then there is
a constant `C ≥ 0` such that every `C¹` map `ξ` whose symplectic area over `K` vanishes satisfies

`∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖∂s ξ + J(z) ∂t ξ + T(z) ξ‖² + ‖ξ‖²)`

with respect to a measure `μ` that is finite on compact sets. The constant depends only on `J`,
`T` and `K`, not on `μ`. -/
theorem exists_forall_setIntegral_norm_fderiv_sq_le_of_setIntegral_symplecticForm_eq_zero
    [IsFiniteMeasureOnCompacts μ] {T : ℝ × ℝ → V →L[ℝ] V} (hK : IsCompact K)
    (hJ : ∀ z ∈ K, ω.Compatible (J z))
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) K)
    (hT : ContinuousOn T K) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ →
      ∫ z in K, ω (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineImag) ∂μ = 0 →
      ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ∂μ ≤
        C * ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + T z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2) ∂μ := by
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm hK hJc
    fun z hz ↦ (hJ z hz).tames
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hT
  refine ⟨2 * b * (1 + N ^ 2) / a, by positivity, fun ξ hξ hzero ↦ ?_⟩
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  set ξs : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineReal
  set ξt : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineImag
  set F : ℝ × ℝ → V := fun z ↦ ξs z + J z (ξt z)
  have hξs : Continuous ξs := hdξ.clm_apply continuous_const
  have hξt : Continuous ξt := hdξ.clm_apply continuous_const
  have hJt : ContinuousOn (fun z ↦ J z (ξt z)) K := by
    simpa using hJc.clm_apply hξt.continuousOn
  have hF : ContinuousOn F K := hξs.continuousOn.add hJt
  have hD : ContinuousOn (fun z ↦ F z + T z (ξ z)) K :=
    hF.add (hT.clm_apply hξ.continuous.continuousOn)
  -- The energy identity, with the pointwise comparison of `g_z` with the norm on both sides.
  have hid := setIntegral_stdComplexLineEnergyDensity_eq_of_setIntegral_symplecticForm_eq_zero
    hK (fun z hz ↦ (hJ z hz).invariant) hJc hξ hzero
  simp only [stdComplexLineEnergyDensity_def, ContinuousLinearMap.coe_coe] at hid
  have hlow : ∫ z in K, a * (‖ξs z‖ ^ 2 + ‖ξt z‖ ^ 2) ∂μ ≤
      ∫ z in K, (ω.associatedBilinForm (J z) (ξs z) (ξs z) +
        ω.associatedBilinForm (J z) (ξt z) (ξt z)) ∂μ :=
    setIntegral_mono_on
      ((continuous_const.mul ((hξs.norm.pow 2).add (hξt.norm.pow 2))).continuousOn
        |>.integrableOn_compact hK)
      (((continuousOn_associatedBilinForm_apply_self hJc hξs.continuousOn).add
        (continuousOn_associatedBilinForm_apply_self hJc hξt.continuousOn)).integrableOn_compact hK)
      hK.measurableSet fun z hz ↦ by linarith [(hab z hz (ξs z)).1, (hab z hz (ξt z)).1]
  have hup : ∫ z in K, ω.associatedBilinForm (J z) (F z) (F z) ∂μ ≤
      ∫ z in K, 2 * b * (1 + N ^ 2) * (‖F z + T z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2) ∂μ :=
    setIntegral_mono_on
      ((continuousOn_associatedBilinForm_apply_self hJc hF).integrableOn_compact hK)
      ((continuousOn_const.mul ((hD.norm.pow 2).add (hξ.continuous.norm.pow 2).continuousOn))
        |>.integrableOn_compact hK)
      hK.measurableSet fun z hz ↦ by
        -- `‖F‖ ≤ ‖F + T ξ‖ + ‖T ξ‖` and `‖T ξ‖ ≤ N ‖ξ‖`.
        have hTξ : ‖T z (ξ z)‖ ≤ N * ‖ξ z‖ :=
          ((T z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hN z hz) (norm_nonneg _))
        have h₁ : ‖F z‖ ≤ ‖F z + T z (ξ z)‖ + N * ‖ξ z‖ :=
          (norm_le_norm_add_norm_sub' (F z) (F z + T z (ξ z))).trans (by simpa using hTξ)
        have hpos : 0 ≤ b * (‖ξ z‖ ^ 2 + N ^ 2 * ‖F z + T z (ξ z)‖ ^ 2) := by positivity
        calc ω.associatedBilinForm (J z) (F z) (F z) ≤ b * ‖F z‖ ^ 2 := (hab z hz (F z)).2
          _ ≤ b * (‖F z + T z (ξ z)‖ + N * ‖ξ z‖) ^ 2 := by gcongr
          _ ≤ b * (2 * (‖F z + T z (ξ z)‖ ^ 2 + (N * ‖ξ z‖) ^ 2)) := by gcongr; exact add_sq_le
          _ ≤ 2 * b * (1 + N ^ 2) * (‖F z + T z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2) := by
            linear_combination 2 * hpos
  rw [integral_const_mul] at hlow hup
  rw [← hid] at hup
  rw [div_mul_eq_mul_div, le_div_iff₀' ha]
  linarith

/-- **The `L²` estimate for compactly supported maps.** Let `J(z)` be `ω`-compatible at every
point of a compact set `K ⊆ ℝ × ℝ` and depend continuously on `z ∈ K`, and let `T` be continuous
on `K`. Then there is a constant `C ≥ 0` such that every `C²` map `ξ` with support in `K`
satisfies `∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖∂s ξ + J(z) ∂t ξ + T(z) ξ‖² + ‖ξ‖²)` with respect to
an additive Haar measure. -/
theorem exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset
    [μ.IsAddHaarMeasure] {T : ℝ × ℝ → V →L[ℝ] V} (hK : IsCompact K)
    (hJ : ∀ z ∈ K, ω.Compatible (J z))
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) K)
    (hT : ContinuousOn T K) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → tsupport ξ ⊆ K →
      ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ∂μ ≤
        C * ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + T z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2) ∂μ := by
  obtain ⟨C, hC, h⟩ :=
    exists_forall_setIntegral_norm_fderiv_sq_le_of_setIntegral_symplecticForm_eq_zero (μ := μ)
      hK hJ hJc hT
  exact ⟨C, hC, fun ξ hξ hξK ↦
    h (hξ.of_le one_le_two) (setIntegral_symplecticForm_fderiv_eq_zero ω hK hξ hξK)⟩

/-- **The `L²` estimate on a finite cylinder.** Let `J(z)` be `ω`-compatible at every point of
the rectangle `[a, b] × [0, 1]` and depend continuously on `z` there, and let `T` be continuous
on the rectangle. Then there is a constant `C ≥ 0` such that every `C²` map `ξ` with
`ξ(s, 1) = ξ(s, 0)` for `s ∈ [a, b]` that vanishes on the slices `s = a` and `s = b` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖∂s ξ + J(z) ∂t ξ + T(z) ξ‖² + ‖ξ‖²)`

over `[a, b] × [0, 1]`. -/
theorem exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic
    {T : ℝ × ℝ → V →L[ℝ] V} {a b : ℝ} (hab : a ≤ b)
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Compatible (J z))
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
      (Icc a b ×ˢ Icc 0 1))
    (hT : ContinuousOn T (Icc a b ×ˢ Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s ∈ Icc a b, ξ (s, 1) = ξ (s, 0)) →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + T z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ :=
    exists_forall_setIntegral_norm_fderiv_sq_le_of_setIntegral_symplecticForm_eq_zero
      (μ := volume) (isCompact_Icc.prod isCompact_Icc) hJ hJc hT
  exact ⟨C, hC, fun ξ hξ hper ha hb ↦ h (hξ.of_le one_le_two)
    (ω.integral_symplecticForm_fderiv_prod_Icc_eq_zero_of_periodic hab
      (fun _ _ ↦ hξ.contDiffAt) hper ha hb)⟩

end SymplecticForm

end TauCeti
