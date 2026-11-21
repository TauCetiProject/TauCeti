/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology
import TauCeti.Analysis.Complex.Circle

/-!
# The continuous gauge action on the framed vortex fields and its Hausdorff quotient

For an integer `k > 1`, the Sobolev framed gauge group `G_(k+1)` acts on the affine field space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` of framed degree-`m` plane vortex fields by the charge-one
transformation `(a, α) ↦ (a - u⁻¹ du, u α)` (`TauCeti.Vortex.gaugeTransform`). Both carry Sobolev
topologies: `G_(k+1)` that of `u - 1 ∈ H^(k+1)(ℂ)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`), and the continuous fields of `A_m^k` that of
`x - x_m ∈ H^k(ℂ)⁴` (`TauCeti.Vortex.SobolevFieldSpace`). This file shows that the action is
jointly continuous for these topologies, and draws the consequences for the quotient
`A_m^k / G_(k+1)`, the Sobolev moduli space of framed fields.

**Continuity.** Write `R = Re u - 1` and `J = Im u`, which lie in `H^(k+1)`; in terms of
`u - 1` and `u⁻¹ - 1 = conj (u - 1)` they are `R = ((u - 1) + (u⁻¹ - 1)) / 2` and
`J = -i ((u - 1) - (u⁻¹ - 1)) / 2`, so they depend continuously on `u`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.reSubOne`,
`TauCeti.Vortex.SobolevTopologicalGaugeGroup.imPart`). With `y = x - x_m` and
`x_m = (b_m, p_m, q_m)` the coordinates of the transformed field
(`TauCeti.Vortex.SobolevFieldSpace.smulCoord`, `TauCeti.Vortex.SobolevFieldSpace.subRef_smul`) are

* `y_b(v) - Im (u⁻¹ ∂_v u) = y_b(v) - (∂_v J + R ∂_v J - J ∂_v R)` for the connection,
* `y_p + R y_p - J y_q + p_m R - q_m J` and `y_q + J y_p + R y_q + p_m J + q_m R` for the section.

Each term is a continuous operation on the Sobolev scale: the derivative
`∂_v : H^(k+1) → H^k` (`BesselPotentialSpace.lineDerivCLM`), the products on the algebra `H^k(ℂ)`,
`k > 1` (`BesselPotentialSpace.mulCLM`), and the multiplication by a reference coordinate, which is
smooth with bounded derivatives (`TauCeti.Vortex.referenceMulCLM`). Hence
`(u, x) ↦ u · x` is continuous (`TauCeti.Vortex.SobolevFieldSpace.instContinuousSMul`).

**The quotient.** The action is free, and two fields lie in the same orbit exactly when a gauge
of `G_(k+1)` carries one to the other (`TauCeti.Vortex.SobolevFieldSpace.orbitRel_iff`). Since
every `x ↦ u · x` is a homeomorphism, the quotient map onto the orbit space is open
(`MulAction.isOpenQuotientMap_quotientMk`). For `k ≥ 3` the orbit relation is moreover closed
(`TauCeti.Vortex.SobolevFieldSpace.isClosed_setOf_exists_gaugeTransform_eq`), so the quotient is
Hausdorff (`TauCeti.Vortex.SobolevFieldSpace.t2Space_quotient`). The slice theorem, which would
give the quotient a manifold structure near the vortices, is not treated here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.instMulAction`: the free action of `G_(k+1)` on the
  continuous fields of `A_m^k`, `k > 1`, with `TauCeti.Vortex.SobolevFieldSpace.coe_smul`.
* `TauCeti.Vortex.SobolevFieldSpace.subRef_smul`: the coordinates of `u · x - x_m` in `H^k(ℂ)` are
  `TauCeti.Vortex.SobolevFieldSpace.smulCoord` of `Re u - 1`, `Im u` and those of `x - x_m`.
* `TauCeti.Vortex.SobolevFieldSpace.instContinuousSMul`: the action is jointly continuous.
* `TauCeti.Vortex.SobolevFieldSpace.t2Space_quotient`: for `k ≥ 3`, `A_m^k / G_(k+1)` is
  Hausdorff.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace ComplexConjugate

/-! ### The action on the continuous fields -/

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

private theorem two_lt_natCast_add_one : (2 : ℝ) < k + 1 := by
  have : (1 : ℝ) < k := by exact_mod_cast (Fact.out : 1 < k)
  linarith

/-- A gauge of `G_(k+1)`, `k > 1`, is `C¹`. -/
private theorem contDiff_one_coe (u : SobolevTopologicalGaugeGroup hs) :
    ContDiff ℝ 1 fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) :=
  contDiff_of_mem_sobolevGaugeGroup (k := 1)
    (by push_cast; linarith [two_lt_natCast_add_one (k := k)]) (toSubgroup hs u).property

instance : SMul (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) where
  smul u x := ⟨gaugeTransform (toSubgroup hs u) x,
    gaugeTransform_mem_framedFieldSpace Fact.out (toSubgroup hs u).property x.mem_framedFieldSpace,
    (contDiff_gaugeTransform (n := 0) (by simpa using contDiff_one_coe u)
      (contDiff_zero.2 x.continuous)).continuous⟩

/-- A gauge `u ∈ G_(k+1)` acts on a continuous field of `A_m^k` by the charge-one transformation
`(a, α) ↦ (a - u⁻¹ du, u α)`. -/
@[simp]
theorem coe_smul (u : SobolevTopologicalGaugeGroup hs) (x : SobolevFieldSpace f m k) :
    ⇑(u • x) = gaugeTransform (toSubgroup hs u) x :=
  (rfl)

/-- **The action of `G_(k+1)` on the continuous fields of `A_m^k`**, for an integer `k > 1`, by the
charge-one transformation `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
instance instMulAction : MulAction (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) where
  one_smul x := ext <| by
    rw [coe_smul, map_one]
    exact gaugeTransform_one x
  mul_smul u v x := ext <| by
    rw [coe_smul, coe_smul, coe_smul, map_mul]
    exact gaugeTransform_mul ((contDiff_one_coe u).differentiable one_ne_zero)
      ((contDiff_one_coe v).differentiable one_ne_zero) x

/-- **The action of `G_(k+1)` on `A_m^k` is free**: a gauge fixing one field is the identity. -/
instance : IsCancelSMul (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.mpr fun u x hux ↦ (toSubgroup hs).injective ?_
  rw [map_one]
  exact Subtype.ext <| eq_one_of_gaugeTransform_eq_self
    ((contDiff_one_coe u).differentiable one_ne_zero)
    (tendsto_cocompact_of_mem_sobolevGaugeGroup (toSubgroup hs u).property)
    (by simpa only [coe_smul] using congrArg (⇑) hux)

/-! ### The coordinates of the transformed field -/

private theorem finrank_lt : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ) :=
  finrank_real_complex_lt_two_mul (by exact_mod_cast (Fact.out : 1 < k))

variable (f m) in
/-- **The coordinates of the transformed field.** The coordinates of `u · x - x_m` in `H^k(ℂ)⁴`,
in terms of `R = Re u - 1` and `J = Im u` in `H^(k+1)(ℂ)` and the coordinates `y` of `x - x_m`
(`TauCeti.Vortex.SobolevFieldSpace.subRef_smul`). Its entries are given by
`TauCeti.Vortex.SobolevFieldSpace.smulCoord_zero` to
`TauCeti.Vortex.SobolevFieldSpace.smulCoord_three`. -/
def smulCoord (R J : H^{(k : ℝ) + 1}(ℂ)) (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    Fin 4 → H^{(k : ℝ)}(ℂ) :=
  let ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  let M := mulCLM (finrank_lt (k := k))
  let D (v : ℂ) : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  let G (v : ℂ) := D v J + M (ι R) (D v J) - M (ι J) (D v R)
  ![y 0 - G 1, y 1 - G I,
    y 2 + M (ι R) (y 2) - M (ι J) (y 3) + referenceMulCLM f m k 2 (ι R) -
      referenceMulCLM f m k 3 (ι J),
    y 3 + M (ι J) (y 2) + M (ι R) (y 3) + referenceMulCLM f m k 2 (ι J) +
      referenceMulCLM f m k 3 (ι R)]

section smulCoord

variable (hs' : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ)) (R J : H^{(k : ℝ) + 1}(ℂ))
  (y : Fin 4 → H^{(k : ℝ)}(ℂ))

/-- The first connection coordinate of the transformed field is
`y_0 - (∂_1 J + R ∂_1 J - J ∂_1 R)`. -/
theorem smulCoord_zero :
    smulCoord f m R J y 0 = y 0 -
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 J +
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le R)
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 J) -
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le J)
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 R)) :=
  (rfl)

/-- The second connection coordinate of the transformed field is
`y_1 - (∂_i J + R ∂_i J - J ∂_i R)`. -/
theorem smulCoord_one :
    smulCoord f m R J y 1 = y 1 -
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I J +
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le R)
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I J) -
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le J)
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I R)) :=
  (rfl)

/-- The first section coordinate of the transformed field is
`y_2 + R y_2 - J y_3 + p_m R - q_m J`. -/
theorem smulCoord_two :
    smulCoord f m R J y 2 =
      y 2 + mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le R) (y 2) -
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le J) (y 3) +
        referenceMulCLM f m k 2 (inclusion (lt_add_one (k : ℝ)).le R) -
        referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le J) :=
  (rfl)

/-- The second section coordinate of the transformed field is
`y_3 + J y_2 + R y_3 + p_m J + q_m R`. -/
theorem smulCoord_three :
    smulCoord f m R J y 3 =
      y 3 + mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le J) (y 2) +
        mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le R) (y 3) +
        referenceMulCLM f m k 2 (inclusion (lt_add_one (k : ℝ)).le J) +
        referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le R) :=
  (rfl)

end smulCoord

/-- The coordinates `smulCoord` of the transformed field depend continuously on `Re u - 1`, `Im u`
and the coordinates of `x - x_m`. -/
theorem continuous_smulCoord :
    Continuous fun p : H^{(k : ℝ) + 1}(ℂ) × H^{(k : ℝ) + 1}(ℂ) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
      smulCoord f m p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j <;> simp only [smulCoord] <;> fun_prop

omit [Fact (1 < k)] in
/-- The `L²` function of `Re u - 1`, included in `H^k(ℂ)`. -/
private theorem coeFn_inclusionLp_inclusion_reSubOne (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusionLp k.cast_nonneg (inclusion (lt_add_one (k : ℝ)).le (reSubOne u))) =ᵐ[volume]
      fun z ↦ ((((toSubgroup hs u : ℂ → Circle) z : ℂ).re - 1 : ℝ) : ℂ) := by
  rw [inclusionLp_inclusion]
  exact coeFn_inclusionLp_reSubOne _ u

omit [Fact (1 < k)] in
/-- The `L²` function of `Im u`, included in `H^k(ℂ)`. -/
private theorem coeFn_inclusionLp_inclusion_imPart (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusionLp k.cast_nonneg (inclusion (lt_add_one (k : ℝ)).le (imPart u))) =ᵐ[volume]
      fun z ↦ ((((toSubgroup hs u : ℂ → Circle) z : ℂ).im : ℝ) : ℂ) := by
  rw [inclusionLp_inclusion]
  exact coeFn_inclusionLp_imPart _ u

/-- The `L²` function of `∂_v (Re u - 1)` is `-Im u · Im (u⁻¹ ∂_v u)`. -/
private theorem coeFn_inclusionLp_lineDerivCLM_reSubOne (u : SobolevTopologicalGaugeGroup hs)
    (v : ℂ) :
    ⇑(inclusionLp k.cast_nonneg
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (reSubOne u))) =ᵐ[volume]
      fun z ↦ ((-((toSubgroup hs u : ℂ → Circle) z : ℂ).im *
        gaugeForm (toSubgroup hs u) z v : ℝ) : ℂ) := by
  have hC1 := contDiff_one_coe u
  filter_upwards [coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
    k.cast_nonneg (f := fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ).re - 1)
    ((reCLM.contDiff.comp hC1).sub contDiff_const)
    (coeFn_inclusionLp_reSubOne _ u) v] with z hz
  rw [hz, fderiv_sub_const,
    fderiv_re_coe_eq_neg_im_mul_gaugeForm (hC1.differentiable one_ne_zero z)]

/-- The `L²` function of `∂_v Im u` is `Re u · Im (u⁻¹ ∂_v u)`. -/
private theorem coeFn_inclusionLp_lineDerivCLM_imPart (u : SobolevTopologicalGaugeGroup hs)
    (v : ℂ) :
    ⇑(inclusionLp k.cast_nonneg
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (imPart u))) =ᵐ[volume]
      fun z ↦ ((((toSubgroup hs u : ℂ → Circle) z : ℂ).re *
        gaugeForm (toSubgroup hs u) z v : ℝ) : ℂ) := by
  have hC1 := contDiff_one_coe u
  filter_upwards [coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
    k.cast_nonneg (f := fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ).im)
    (imCLM.contDiff.comp hC1) (coeFn_inclusionLp_imPart _ u) v] with z hz
  rw [hz, fderiv_im_coe_eq_re_mul_gaugeForm (hC1.differentiable one_ne_zero z)]

/-- **The connection increment in `H^k(ℂ)`.** The `L²` function of
`∂_v J + R ∂_v J - J ∂_v R`, with `R = Re u - 1` and `J = Im u`, is `Im (u⁻¹ ∂_v u)`. -/
private theorem coeFn_inclusionLp_gaugeFormCoord (u : SobolevTopologicalGaugeGroup hs) (v : ℂ) :
    ⇑(inclusionLp k.cast_nonneg
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (imPart u) +
        mulCLM finrank_lt (inclusion (lt_add_one (k : ℝ)).le (reSubOne u))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (imPart u)) -
        mulCLM finrank_lt (inclusion (lt_add_one (k : ℝ)).le (imPart u))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (reSubOne u)))) =ᵐ[volume]
      fun z ↦ ((gaugeForm (toSubgroup hs u) z v : ℝ) : ℂ) := by
  have hM (a b : H^{(k : ℝ)}(ℂ)) := coeFn_toLp_inclusion_mulCLM finrank_lt k.cast_nonneg a b
  simp only [toLp_inclusion] at hM
  filter_upwards [coeFn_inclusionLp_sub_ae_eq k.cast_nonneg
      (coeFn_inclusionLp_add_ae_eq k.cast_nonneg .rfl (hM _ _)) (hM _ _),
    coeFn_inclusionLp_inclusion_reSubOne u, coeFn_inclusionLp_inclusion_imPart u,
    coeFn_inclusionLp_lineDerivCLM_reSubOne u v, coeFn_inclusionLp_lineDerivCLM_imPart u v]
    with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅]
  -- With `ω = Im (u⁻¹ du)`, the derivatives are `∂_v Re u = -Im u · ω(v)` and
  -- `∂_v Im u = Re u · ω(v)`, so the sum is `(Re u² + Im u²) ω(v) = ω(v)` as `|u| = 1`.
  have hn : ((((toSubgroup hs u : ℂ → Circle) z : ℂ).re : ℝ) : ℂ) ^ 2 +
      ((((toSubgroup hs u : ℂ → Circle) z : ℂ).im : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Circle.re_sq_add_im_sq ((toSubgroup hs u : ℂ → Circle) z)
  push_cast
  linear_combination ((gaugeForm (toSubgroup hs u) z v : ℝ) : ℂ) * hn

/-- **The connection coordinates of the transformed field.** If the coordinate `j` of `u · x` is
`x_j - Im (u⁻¹ ∂_v u)`, then the `L²` function of `y_j - (∂_v J + R ∂_v J - J ∂_v R)`, with
`R = Re u - 1`, `J = Im u` and `y = x - x_m`, is the coordinate `j` of `u · x - x_m`. -/
private theorem coeFn_inclusionLp_connectionCoord (u : SobolevTopologicalGaugeGroup hs)
    (x : SobolevFieldSpace f m k) {j : Fin 4} {v : ℂ}
    (hj : ∀ z, (u • x) z j = x z j - gaugeForm (toSubgroup hs u) z v) :
    ⇑(inclusionLp k.cast_nonneg (subRef x j -
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (imPart u) +
        mulCLM finrank_lt (inclusion (lt_add_one (k : ℝ)).le (reSubOne u))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (imPart u)) -
        mulCLM finrank_lt (inclusion (lt_add_one (k : ℝ)).le (imPart u))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (reSubOne u))))) =ᵐ[volume]
      fun z ↦ (((u • x) z j - referenceField f m z j : ℝ) : ℂ) := by
  have hy := coeFn_toLp_inclusion_subRef k.cast_nonneg x j
  rw [toLp_inclusion] at hy
  filter_upwards [coeFn_inclusionLp_sub_ae_eq k.cast_nonneg hy
    (coeFn_inclusionLp_gaugeFormCoord u v)] with z hz
  rw [hz, hj]
  push_cast
  ring

/-- **The section coordinates of the transformed field.** With `R = Re u - 1`, `J = Im u` and
`y = x - x_m`, the `L²` functions of `y_p + R y_p - J y_q + p_m R - q_m J` and of
`y_q + J y_p + R y_q + p_m J + q_m R` are the section coordinates `Re u · p - Im u · q` and
`Im u · p + Re u · q` of `u · x`, minus those of `x_m`. -/
private theorem coeFn_inclusionLp_sectionCoord (u : SobolevTopologicalGaugeGroup hs)
    (x : SobolevFieldSpace f m k) :
    (⇑(inclusionLp k.cast_nonneg (smulCoord f m (reSubOne u) (imPart u) (subRef x) 2)) =ᵐ[volume]
      fun z ↦ (((u • x) z 2 - referenceField f m z 2 : ℝ) : ℂ)) ∧
    (⇑(inclusionLp k.cast_nonneg (smulCoord f m (reSubOne u) (imPart u) (subRef x) 3)) =ᵐ[volume]
      fun z ↦ (((u • x) z 3 - referenceField f m z 3 : ℝ) : ℂ)) := by
  have hy (a : Fin 4) := coeFn_toLp_inclusion_subRef k.cast_nonneg x a
  have hR := coeFn_inclusionLp_inclusion_reSubOne (k := k) u
  have hJ := coeFn_inclusionLp_inclusion_imPart (k := k) u
  have hM (a b : H^{(k : ℝ)}(ℂ)) := coeFn_toLp_inclusion_mulCLM finrank_lt k.cast_nonneg a b
  have href (a : Fin 4) (b : H^{(k : ℝ)}(ℂ)) :=
    coeFn_inclusionLp_referenceMulCLM_ae_eq (f := f) (m := m) a b
  simp only [toLp_inclusion] at hy hM
  rw [smulCoord_two finrank_lt, smulCoord_three finrank_lt]
  -- Split each coordinate into its summands, whatever their order, and read off the `L²` function
  -- of each summand; then compare the two sides pointwise.
  constructor <;>
  · apply EventuallyEq.trans
    · repeat' with_reducible first
        | exact hy _ | exact hM _ _ | exact href _ _
        | apply coeFn_inclusionLp_add_ae_eq | apply coeFn_inclusionLp_sub_ae_eq
    · filter_upwards [hy 2, hy 3, hR, hJ] with z h₁ h₂ h₃ h₄
      simp only [h₁, h₂, h₃, h₄, coe_smul, gaugeTransform_apply, Fin.isValue, Matrix.cons_val]
      push_cast
      ring

/-- **The coordinates of the transformed field.** For `u ∈ G_(k+1)` and a continuous field `x` of
`A_m^k`, the coordinates of `u · x - x_m` in `H^k(ℂ)` are `smulCoord` of `Re u - 1`, `Im u` and
the coordinates of `x - x_m`. -/
theorem subRef_smul (u : SobolevTopologicalGaugeGroup hs) (x : SobolevFieldSpace f m k) :
    subRef (u • x) = smulCoord f m (reSubOne u) (imPart u) (subRef x) := by
  funext j
  rw [subRef_eq_iff k.cast_nonneg, toLp_inclusion]
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [smulCoord_zero finrank_lt]
    exact coeFn_inclusionLp_connectionCoord u x fun z ↦ by simp [gaugeTransform_apply]
  · rw [smulCoord_one finrank_lt]
    exact coeFn_inclusionLp_connectionCoord u x fun z ↦ by simp [gaugeTransform_apply]
  · exact (coeFn_inclusionLp_sectionCoord u x).1
  · exact (coeFn_inclusionLp_sectionCoord u x).2

/-! ### Continuity and the quotient -/

/-- **The action of `G_(k+1)` on `A_m^k` is continuous**, for an integer `k > 1`: the coordinates
of `u · x - x_m` in `H^k(ℂ)` are continuous functions of `u - 1 ∈ H^(k+1)(ℂ)` and of the
coordinates of `x - x_m` in `H^k(ℂ)`. -/
instance instContinuousSMul :
    ContinuousSMul (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) where
  continuous_smul := (isEmbedding_subRef k.cast_nonneg).continuous_iff.2 <| by
    simp only [Function.comp_def, subRef_smul]
    exact continuous_smulCoord.comp ((continuous_reSubOne.comp continuous_fst).prodMk
      ((continuous_imPart.comp continuous_fst).prodMk (continuous_subRef.comp continuous_snd)))

/-- Two continuous fields of `A_m^k` lie in the same orbit of `G_(k+1)` exactly when a gauge of
`G_(k+1)` carries the first to the second. -/
theorem orbitRel_iff {x y : SobolevFieldSpace f m k} :
    MulAction.orbitRel (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) x y ↔
      ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u x = y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨toSubgroup hs u⁻¹, (toSubgroup hs u⁻¹).property, ?_⟩
    rw [← coe_smul, inv_smul_smul]
  · rintro ⟨u, hu, hxy⟩
    refine ⟨((toSubgroup hs).symm ⟨u, hu⟩)⁻¹, ?_⟩
    rw [inv_smul_eq_iff]
    ext1
    simp [hxy]

/-- **The Sobolev moduli space of framed fields is Hausdorff**: for an integer `k ≥ 3`, the
quotient `A_m^k / G_(k+1)` of the continuous fields of `A_m^k` by the Sobolev gauge group is a
Hausdorff space. -/
theorem t2Space_quotient (hk : 2 < k) :
    T2Space (MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs)
      (SobolevFieldSpace f m k)) := by
  rw [t2Space_iff_of_isOpenQuotientMap MulAction.isOpenQuotientMap_quotientMk]
  convert isClosed_setOf_exists_gaugeTransform_eq (f := f) (m := m) hk using 1
  ext p
  simp only [Set.mem_ofPred_eq, Quotient.eq]
  exact orbitRel_iff

end SobolevFieldSpace

end TauCeti.Vortex
