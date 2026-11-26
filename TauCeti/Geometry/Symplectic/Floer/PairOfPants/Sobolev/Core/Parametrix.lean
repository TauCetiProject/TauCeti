/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.End.Model
public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# The contribution of the compact core to a right parametrix on the pair of pants

Let `D` be a first-order operator on the pair of pants `S = ℂ ∖ {0, 1}`, realized on
`W^{1,2}_0(S, V)` through an essentially bounded coefficient field `M` on the conformal jets of the
cylindrical weight, such as the linearized Floer operator
`TauCeti.SymplecticForm.floerConformalSobolevOperator` of a pair of pants. A right parametrix of
`D`, an operator `P` with `D P - 1` compact, gives the finiteness of the cokernel
(`ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one`). It is spliced from local
pieces: far out on each end an inverse of the end model of `D`
(`TauCeti.Floer.exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq`),
and on the compact part of `S` the pieces constructed here. Each is the transfer, along an end
chart `φ'_q` and with a cutoff `β` (`TauCeti.Floer.endTransfer`), of an operator on the cylinder.

* **The abstract core piece.** Let the first-order operator on the cylinder with an essentially
  bounded coefficient field `G` have a right inverse `Q`, and let the cutoff `β` live in a compact
  range of heights of the band of `φ'_q`. If, wherever `β ≠ 0`, the coefficient field of `D` read
  along `φ'_q` has the same principal part as `G`, then `D` applied to the transfer of `Q h` is,
  through the `L²` isometry `TauCeti.Floer.positiveEndChartLp`, `β(φ'_q) h + K h` with `K` compact
  (`exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq_of_principal`,
  in the namespace `TauCeti.Floer`).
  Indeed the coefficient field of `D` applied to the transfer is `β(φ'_q) G` plus a field that only
  reads the value of a jet and vanishes outside a compact range of heights, which is compact by
  Rellich's theorem
  (`TauCeti.CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_eq_zero_of_le_or_le`).
* **The local piece of the linearized operator.** Read along `φ'_q`, the principal part of the
  linearized Floer operator at `φ'_q(ζ)` is `r⁻¹ (a + b J) (∂s + J ∂t)` with `J = J(φ'_q ζ, u)`,
  `(a, b) = dφ'_q (1, 0)` and `r` the conformal scale of the chart. Freezing `J` at a point `z₀`
  gives the end model `TauCeti.Floer.endModelCoeff` of the constant loop `J₀ = J(z₀, u z₀)`,
  which is invertible when the stationary cylinder operator `∂s + J₀ (∂t - S₀)` is
  (`TauCeti.Floer.isInvertible_endModelSobolevOperator_iff`); the zeroth-order part `S₀` may be
  any continuous loop, since only the principal part is frozen. Near `z₀` the two principal parts
  differ by `r⁻¹ (b (J - J₀) ∂s + a (J - J₀) ∂t)`, which is small when `J` is continuous at
  `z₀`. Adding this difference to the frozen model over the preimage of a small neighbourhood `U`
  of `z₀` gives a small perturbation of an invertible operator, hence an invertible operator
  (`TauCeti.CylinderSobolev.exists_pos_forall_isInvertible_jetOperator_add_comp_subtypeL`)
  `G` with the principal part of `D` over `U`. So every cutoff supported in `U` gives a core piece
  (`exists_mem_nhds_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`,
  in the namespace `TauCeti.SymplecticForm`).

The end chart `φ'_q` of each end covers the whole plane except its center, so every point of `S`
is reached by these pieces, and finitely many of them, with cutoffs forming a partition of unity
with those of the ends, cover the compact part of `S`. That assembly is not carried out here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends, and the
  local parametrices of elliptic operators.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Topology

namespace TauCeti.Floer

open StripSobolev

section Abstract

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Read along the end chart, the coefficient field of `D` applied to the transfer with a cutoff `β`
living in a compact range of heights, minus `β` times a field `G` with the same principal part
wherever `β ≠ 0`, only reads the value of a jet and vanishes outside that range of heights, so it
gives a compact operator on `W^{1,2}` of the cylinder. -/
private theorem isCompactOperator_jetOperator_comp_endTransferCoeff_sub_smul (q : Puncture)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {B : ℝ} (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
        (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B)
    {T₀ T₁ : ℝ} (hβ₀ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → β (positiveEndChart q ζ) = 0)
    (hdβ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0)
    (hMG : ∀ᵐ ζ ∂stripMeasure, β (positiveEndChart q ζ) ≠ 0 → ∀ a b : V,
      M (positiveEndChart q ζ) (endTransferCoeff q (fun _ ↦ 1) ζ (0, a, b)) = G ζ (0, a, b)) :
    IsCompactOperator ((jetOperator 2 stripMeasure fun ζ ↦
      (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) -
        β (positiveEndChart q ζ) • G ζ).comp (CylinderSobolev.H1 V).subtypeL) := by
  refine CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_eq_zero_of_le_or_le
    (((hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart q)).clm_comp ∞
      (memLp_endTransferCoeff q hβ hβS hB)).sub
      ((memLp_comp_positiveEndChart q hβ.continuous fun z hz ↦ (hB z hz).1).smul hG)) ?_
    (ae_of_all _ fun ζ (hout : ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1) ↦ ?_)
  · -- On principal parts, the transfer with the cutoff `β` is `β` times that with the cutoff `1`.
    filter_upwards [hMG] with ζ hζ a b
    have hcut : endTransferCoeff q β ζ (0, a, b) =
        β (positiveEndChart q ζ) • endTransferCoeff q (fun _ ↦ 1) ζ (0, a, b) := by
      rw [endTransferCoeff_apply_eq_smul_add]
      simp [Prod.mk_zero_zero]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hcut, map_smul]
    by_cases h0 : β (positiveEndChart q ζ) = 0
    · simp [h0]
    · rw [hζ h0 a b, sub_self]
  · -- Where the cutoff and its derivative vanish, so does the jet coefficient of the transfer.
    have h0 : endTransferCoeff (V := V) q β ζ = 0 := by
      refine ContinuousLinearMap.ext fun v ↦ ?_
      simp [endTransferCoeff_apply, hβ₀ ζ hout, hdβ ζ hout, Prod.mk_zero_zero]
    simp only [h0, hβ₀ ζ hout, ContinuousLinearMap.comp_zero, zero_smul, sub_zero]

/-- **A core contribution to a right parametrix.** Let `D` be a first-order operator on the pair
of pants `S` with an essentially bounded coefficient field `M` on conformal jets, and let the
first-order operator on the cylinder with an essentially bounded coefficient field `G` have a right
inverse `Q : L²(ℝ × S¹, W) → W^{1,2}(ℝ × S¹, V)`. Let `β` be a cutoff on the plane as in
`endTransfer_mem_H1` which, with its derivative, vanishes on the parts `s ≤ T₀` and `s ≥ T₁` of the
band of the end chart `φ'_q`. If, wherever `β ≠ 0`, the coefficient field of `D` read along `φ'_q`
with the cutoff `1` has the same principal part as `G`, then

`D (β · (Q h ∘ ψ)) = φ'_q-transfer of (β(φ'_q) h + K h)`

for a compact operator `K` on `L²` of the strip; here `ψ` is the inverse of the chart, and both
sides are compared through the `L²` isometry `positiveEndChartLp`. -/
theorem exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq_of_principal
    (q : Puncture)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    {Q : Lp W 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V}
    (hQ : ∀ h, jetOperator 2 stripMeasure G (Q h) = h)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {B : ℝ} (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
        (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B)
    {T₀ T₁ : ℝ} (hβ₀ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → β (positiveEndChart q ζ) = 0)
    (hdβ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0)
    (hMG : ∀ᵐ ζ ∂stripMeasure, β (positiveEndChart q ζ) ≠ 0 → ∀ a b : V,
      M (positiveEndChart q ζ) (endTransferCoeff q (fun _ ↦ 1) ζ (0, a, b)) = G ζ (0, a, b)) :
    ∃ K : Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure, IsCompactOperator K ∧
      ∀ h, ((positiveEndChartLp q).symm (jetOperator 2
        (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))) :
          ℝ × ℝ → W) =ᵐ[stripMeasure] fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ := by
  have hT := memLp_endTransferCoeff (V := V) q hβ hβS hB
  have hβφ := memLp_comp_positiveEndChart q hβ.continuous fun z hz ↦ (hB z hz).1
  -- Read along the chart, the coefficient field of `D` applied to the transfer is the cutoff times
  -- the model plus a field `E` which gives a compact operator.
  set E : ℝ × ℝ → V × V × V →L[ℝ] W := fun ζ ↦
    (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) - β (positiveEndChart q ζ) • G ζ
  have hEm : MemLp E ∞ stripMeasure :=
    ((hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart q)).clm_comp ∞
      hT).sub (hβφ.smul hG)
  refine ⟨((jetOperator 2 stripMeasure E).comp (CylinderSobolev.H1 V).subtypeL).comp Q,
    (isCompactOperator_jetOperator_comp_endTransferCoeff_sub_smul q hM hG hβ hβS hB hβ₀ hdβ
      hMG).comp_clm Q, fun h ↦ ?_⟩
  have hsplit : (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) =
      (fun ζ ↦ β (positiveEndChart q ζ) • G ζ) + E := by
    funext ζ
    simp [E]
  rw [jetOperator_endTransfer q hT hM, LinearIsometryEquiv.symm_apply_apply, hsplit,
    jetOperator_add (M := fun ζ ↦ β (positiveEndChart q ζ) • G ζ) (hβφ.smul hG) hEm]
  filter_upwards [Lp.coeFn_add (jetOperator 2 stripMeasure (fun ζ ↦ β (positiveEndChart q ζ) • G ζ)
      (Q h)) (jetOperator 2 stripMeasure E (Q h)),
    coeFn_jetOperator_smul (p := 2) hβφ hG (Q h)] with ζ h₁ h₂
  rw [add_apply, h₁, Pi.add_apply, h₂, hQ h, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

end Abstract

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer ContinuousLinearMap
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The jet coefficient of the transfer along an end chart with the cutoff `1`, restricted to the
derivative components: `(x, y, z) ↦ (0, a' y - b' z, b' y + a' z)` for the rotation part
`(a', b')` of the chart. -/
private def endPrincipalCoeff (q : Puncture) (ζ : ℝ × ℝ) : V × V × V →L[ℝ] V × V × V :=
  let I₁ := (ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V)
  let I₂ := (ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inr ℝ V V)
  let P₁ := (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  let P₂ := (ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  (endUnitTangent q ζ).1 • I₁.comp P₁ - (endUnitTangent q ζ).2 • I₁.comp P₂ +
    ((endUnitTangent q ζ).2 • I₂.comp P₁ + (endUnitTangent q ζ).1 • I₂.comp P₂)

omit [FiniteDimensional ℝ V] in
private theorem endPrincipalCoeff_apply (q : Puncture) (ζ : ℝ × ℝ) (v : V × V × V) :
    endPrincipalCoeff q ζ v = (0, (endUnitTangent q ζ).1 • v.2.1 - (endUnitTangent q ζ).2 • v.2.2,
      (endUnitTangent q ζ).2 • v.2.1 + (endUnitTangent q ζ).1 • v.2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [endPrincipalCoeff]

omit [FiniteDimensional ℝ V] in
private theorem endPrincipalCoeff_apply_zero (q : Puncture) (ζ : ℝ × ℝ) (a b : V) :
    endPrincipalCoeff q ζ (0, a, b) = endTransferCoeff q (fun _ ↦ 1) ζ (0, a, b) := by
  rw [endPrincipalCoeff_apply, endTransferCoeff_apply]
  simp only [endUnitTangent_def, smul_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, smul_zero, fderiv_const_apply, zero_apply, mul_zero,
    zero_add, one_mul, div_eq_inv_mul]

omit [FiniteDimensional ℝ V] in
private theorem continuous_endPrincipalCoeff (q : Puncture) :
    Continuous (endPrincipalCoeff (V := V) q) := by
  have hc := continuous_endUnitTangent q
  unfold endPrincipalCoeff
  fun_prop

omit [FiniteDimensional ℝ V] in
private theorem memLp_endPrincipalCoeff (q : Puncture) :
    MemLp (endPrincipalCoeff (V := V) q) ∞ stripMeasure :=
  CylinderSobolev.memLp_top_of_eq_comp_snd ((continuous_endPrincipalCoeff q).comp
    (continuous_const.prodMk continuous_id)) fun ζ ↦ by
      simp only [endPrincipalCoeff]
      rw [endUnitTangent_eq_of_snd_eq q (ζ := ζ) (ζ' := (0, ζ.2)) rfl]

/-- The principal part `(x, y, z) ↦ (0, y, z)` of a jet. -/
private def principalProj : V × V × V →L[ℝ] V × V × V :=
  (ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.snd ℝ V (V × V))

omit [FiniteDimensional ℝ V] in
private theorem principalProj_apply (v : V × V × V) : principalProj v = (0, v.2) := rfl

/-- The principal part of the linearized operator read along an end chart, minus that of the end
model of a constant structure `J₀`, is `b' (J - J₀) ∂s + a' (J - J₀) ∂t` for the rotation part
`(a', b')` of the chart, so it is at most `2 ‖J - J₀‖`. -/
private theorem norm_floerConformalJetCoeff_comp_endPrincipalCoeff_sub_le (ω : SymplecticForm V)
    (q : Puncture) (ρ : ℝ × ℝ → ℝ) (J : ℝ × ℝ → V → AlmostComplexStructure V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (J₀ : AlmostComplexStructure V)
    (S₀ : ℝ → V →L[ℝ] V) (ζ : ℝ × ℝ) :
    ‖(ω.floerConformalJetCoeff ρ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q ζ)).comp (endPrincipalCoeff q ζ) -
        (endModelCoeff q (fun _ ↦ J₀) S₀ ζ).comp principalProj‖ ≤
      2 * ‖(J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap -
        J₀.toLinearMap.toContinuousLinearMap‖ := by
  set L := J (positiveEndChart q ζ) (u (positiveEndChart q ζ))
  set Δ := L.toLinearMap.toContinuousLinearMap - J₀.toLinearMap.toContinuousLinearMap
  have hc₁ := abs_fst_endUnitTangent_le_one q ζ
  have hc₂ := abs_snd_endUnitTangent_le_one q ζ
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- Since `L² = J₀² = -1`, the difference of the two principal parts is `c₂ Δ y + c₁ Δ z`.
  have hid : ((ω.floerConformalJetCoeff ρ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u (positiveEndChart q ζ)).comp (endPrincipalCoeff q ζ) -
      (endModelCoeff q (fun _ ↦ J₀) S₀ ζ).comp principalProj) v =
        (endUnitTangent q ζ).2 • Δ v.2.1 + (endUnitTangent q ζ).1 • Δ v.2.2 := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      floerConformalJetCoeff_apply, endPrincipalCoeff_apply, principalProj_apply, endModelCoeff_def,
      stationaryJetCoeff_apply, endModelRotation_apply, map_zero, sub_zero, smul_zero,
      add_zero, LinearMap.coe_toContinuousLinearMap', Δ, map_add, map_smul, J₀.apply_apply]
    module
  have hy : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have hz : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  rw [hid]
  calc ‖(endUnitTangent q ζ).2 • Δ v.2.1 + (endUnitTangent q ζ).1 • Δ v.2.2‖
        ≤ ‖Δ‖ * ‖v‖ + ‖Δ‖ * ‖v‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs]
        · exact (mul_le_of_le_one_left (norm_nonneg _) hc₂).trans
            ((Δ.le_opNorm _).trans (by gcongr))
        · exact (mul_le_of_le_one_left (norm_nonneg _) hc₁).trans
            ((Δ.le_opNorm _).trans (by gcongr))
    _ = 2 * ‖Δ‖ * ‖v‖ := by ring

/-- **The local core contribution to a right parametrix of the linearized operator.** Let
`(J, K_s, K_t)` be Floer data on the pair of pants `S` along a map `u`, with essentially bounded
coefficient field `M` on conformal jets, and let `z₀` be a point at which the structures
`J(z, u z)` along `u` depend continuously on `z`. Suppose that for the frozen structure
`J₀ = J(z₀, u z₀)` and some continuous loop `S₀`, the stationary cylinder operator
`∂s + J₀ (∂t - S₀)` is invertible on `W^{1,2}(ℝ × S¹, V)`.

Then for every end `q` there are a neighbourhood `U` of `z₀` and a bounded operator
`Q : L²(ℝ × S¹, V) → W^{1,2}(ℝ × S¹, V)` such that for every cutoff `β` supported in `U` (as in
`TauCeti.Floer.endTransfer_mem_H1`, and vanishing with its derivative on the parts `s ≤ T₀` and
`s ≥ T₁` of the band of the end chart `φ'_q`), the linearized operator `D_u` applied to the
transfer `β · (Q h ∘ ψ)` along `φ'_q` is the transfer by the `L²` isometry
`TauCeti.Floer.positiveEndChartLp` of `β(φ'_q) h + K h`, with `K` compact. -/
theorem
    exists_mem_nhds_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer
    (ω : SymplecticForm V) (q : Puncture) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    {z₀ : ℝ × ℝ} (hJ : ContinuousAt (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) z₀)
    {S₀ : ℝ → V →L[ℝ] V} (hS₀ : Continuous S₀)
    (hD : (stationarySobolevOperator (fun _ ↦ J z₀ (u z₀)) S₀).IsInvertible) :
    ∃ U ∈ 𝓝 z₀, ∃ Q : Lp V 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V,
      ∀ {β : ℝ × ℝ → ℝ} {B T₀ T₁ : ℝ}, ContDiff ℝ 1 β →
        (∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
          z ∈ thricePuncturedSphereReal) →
        (∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
          |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
            (√(cylindricalWeight z) * |β z|) ≤ B ∧
            ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B) →
        tsupport β ⊆ U →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → β (positiveEndChart q ζ) = 0) →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0) →
        ∃ K : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure, IsCompactOperator K ∧
          ∀ h, ((positiveEndChartLp q).symm (jetOperator 2
            (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
                (endTransfer q β (Q h))) : ℝ × ℝ → V) =ᵐ[stripMeasure]
            fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ := by
  set M := ω.floerConformalJetCoeff cylindricalWeight
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
  set J₀ := J z₀ (u z₀)
  set G₀ := endModelCoeff q (fun _ ↦ J₀) S₀
  have hG₀ : MemLp G₀ ∞ stripMeasure := memLp_endModelCoeff q continuous_const hS₀
  -- The frozen end model is invertible, and so is every operator close enough to it.
  obtain ⟨ε, hε, hinv⟩ :=
    CylinderSobolev.exists_pos_forall_isInvertible_jetOperator_add_comp_subtypeL hG₀ (by
    simpa only [endModelSobolevOperator_def] using
      (isInvertible_endModelSobolevOperator_iff q continuous_const hS₀).2 hD)
  -- Near `z₀` the structures along `u` are within `ε / 2` of `J₀`.
  obtain ⟨r, hr, hU⟩ := Metric.continuousAt_iff.1 hJ (ε / 2) (half_pos hε)
  set U := Metric.ball z₀ r
  have hUm : MeasurableSet (positiveEndChart q ⁻¹' U) :=
    Metric.isOpen_ball.measurableSet.preimage (contDiff_positiveEndChart q 0).continuous.measurable
  -- The correction adding to the frozen model the difference of the principal parts over `U`.
  set P : ℝ × ℝ → V × V × V →L[ℝ] V := (positiveEndChart q ⁻¹' U).indicator fun ζ ↦
    (M (positiveEndChart q ζ)).comp (endPrincipalCoeff q ζ) - (G₀ ζ).comp principalProj
  have hPm : MemLp P ∞ stripMeasure :=
    (((hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart q)).clm_comp ∞
      (memLp_endPrincipalCoeff q)).sub
      (hG₀.clm_comp ∞ (memLp_top_const principalProj))).indicator hUm.nullMeasurableSet
  have hPb : ∀ ζ, ‖P ζ‖ ≤ ε := by
    intro ζ
    by_cases hζ : ζ ∈ positiveEndChart q ⁻¹' U
    · simp only [P, indicator_of_mem hζ]
      refine (norm_floerConformalJetCoeff_comp_endPrincipalCoeff_sub_le ω q _ J Ks Kt u J₀ S₀
        ζ).trans ?_
      have := hU hζ
      rw [dist_eq_norm] at this
      linarith
    · simp only [P, indicator_of_notMem hζ, norm_zero]
      exact hε.le
  have hA := hinv hPm (ae_of_all _ hPb)
  refine ⟨U, Metric.ball_mem_nhds z₀ hr, ContinuousLinearMap.inverse
    ((jetOperator 2 stripMeasure (G₀ + P)).comp (CylinderSobolev.H1 V).subtypeL),
    fun {β B T₀ T₁} hβ hβS hB hβU hβ₀ hdβ ↦ ?_⟩
  refine exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq_of_principal
    q hM (hG₀.add hPm) (fun h ↦ hA.self_apply_inverse h) hβ hβS hB hβ₀ hdβ
    (ae_of_all _ fun ζ hβζ a b ↦ ?_)
  -- Where `β ≠ 0` the correction is on, and the corrected model has the principal part of `M`.
  have hζ : ζ ∈ positiveEndChart q ⁻¹' U := hβU (subset_tsupport β hβζ)
  simp only [P, Pi.add_apply, add_apply, indicator_of_mem hζ,
    sub_apply, ContinuousLinearMap.comp_apply, principalProj_apply,
    endPrincipalCoeff_apply_zero]
  abel

end TauCeti.SymplecticForm
