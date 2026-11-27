/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Fredholm
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart.Output
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.Topology.Circle.AddCircle
import TauCeti.Topology.Circle.Metric

/-!
# The linearized operator along the input-exchange family is Fredholm

Graded commutativity of the pair-of-pants product counts the members of the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, on the pair of pants
`S = ℂ ∖ {0, 1}`. Each member is the pair-of-pants datum far out on the two input ends, and on the
output end it is the pair-of-pants datum translated by `c`: it is `H_∞(t) dt` in the end chart
`c + φ'_∞` recentred at `c`, not in the standard end chart `φ'_∞`. The realization
`D_u : W^{1,2}_0(S, F) → L²(S, F)` of its linearized operator for the cylindrical metric has
finite-dimensional kernel and closed range
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_of_recentered`). This
file proves that its cokernel is finite too, so that `D_u` is Fredholm, for data with a recentred
output end (`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_recentered`) and
along the whole input-exchange family
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_exchangePerturbation`).

The finiteness of the cokernel comes from a right parametrix spliced from local inverses, as for
the pair of pants
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_endParametrix`).
The core pieces are those of the pair of pants, and so are the pieces of the two input ends
(`hasEndParametrixPiece_floerConformalJetCoeff_of_isNondegenerateFixedPt`, in the namespace
`TauCeti.SymplecticForm`). The new piece is the output end, where the parametrix is still
transferred along the standard end chart `φ'_∞`, so its inverse must be that of the end model in
the standard chart
(`TauCeti.Floer.hasEndParametrixPiece_of_tendsto_endModelCoeff`). This needs the
coefficient field of `D_u` read in the standard chart to converge to that end model
(`exists_ae_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_recentered`, in the
namespace `TauCeti.SymplecticForm`), which gives the end piece of the output end
(`hasEndParametrixPiece_floerConformalJetCoeff_of_recentered`, in the same
namespace).

* **Translating the data.** The translates by `c` of the data and of `u` are, far out, the
  pair-of-pants datum and a solution of its Floer equation in the standard chart, so their
  coefficient field converges to the end model there
  (`eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt`, in the namespace
  `TauCeti.SymplecticForm`).
  At the point `φ'_∞(ζ')` it is the coefficient field of the original data at
  `z = φ'_∞(ζ') + c`, except that the weight is read at `φ'_∞(ζ')` rather than at `z`.
* **Comparing the charts.** The point `z = φ'_∞(ζ)` is also `φ'_∞(ζ') + c`. Writing `Z` for `z` as
  a complex number, far out the translation by `c` changes `|Z|² ρ(Z)`, which tends to `2`, the
  weight `ρ(Z)` relative to `ρ(Z - c)`, and the direction `Z / |Z|`, by vanishing amounts
  (`|c|` is fixed while `|Z| → ∞`). The direction is `exp (2π i t)` at `ζ = (s, t)`
  (`TauCeti.Floer.equivRealProdCLM_symm_positiveEndChart_inf_div_norm`), so the angular
  coordinates of `ζ` and `ζ'` are close on the circle, and the end model, a continuous function of
  period one in `t`, is uniformly continuous in `exp (2π i t)`. The jet coefficients of the transfer
  along the chart at `ζ` and `ζ'` differ by the difference of the weighted conformal scales `r √ρ`
  and of the unit tangents of the chart (`TauCeti.Floer.norm_endTransferCoeff_one_sub_le`).

The index of `D_u` is not computed here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and its graded
  commutativity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends and their
  parametrices spliced from local inverses.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Topology Manifold

namespace TauCeti.Floer

/-- The quantity `|Z|² ρ(Z)` for the cylindrical weight `ρ(Z) = |Z|⁻² + |Z - 1|⁻²` of the pair of
pants in complex coordinates. Far out it tends to `2`, and the weighted conformal scale `r √ρ` of
the output end chart is `2π` times its square root. -/
private def weightNormSq (Z : ℂ) : ℝ := ‖Z‖ ^ 2 * ((‖Z‖ ^ 2)⁻¹ + (‖Z - 1‖ ^ 2)⁻¹)

/-- In terms of the point `z` of the plane, `√(|Z|² ρ(Z)) = |Z| √ρ(z)`. -/
private theorem sqrt_weightNormSq_eq (z : ℝ × ℝ) :
    √(weightNormSq (Complex.equivRealProdCLM.symm z)) =
      ‖Complex.equivRealProdCLM.symm z‖ * √(cylindricalWeight z) := by
  rw [weightNormSq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    cylindricalWeight_apply, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

/-- The weighted conformal scale `r √ρ` of the output end chart is `2π √(|Z|² ρ(Z))`. -/
private theorem positiveEndChartScale_inf_mul_sqrt_cylindricalWeight (ζ : ℝ × ℝ) :
    positiveEndChartScale inf ζ * √(cylindricalWeight (positiveEndChart inf ζ)) =
      2 * π * √(weightNormSq (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ))) := by
  rw [positiveEndChartScale_apply, endCenter_inf, sub_zero, sqrt_weightNormSq_eq]
  ring

/-- Far out, `|Z|² ρ(Z)` is `1 + |(1 - Z⁻¹)⁻¹|²`, a continuous function of `Z⁻¹` near `0`. -/
private theorem weightNormSq_eq {Z : ℂ} (hZ : Z ≠ 0) (hZ1 : Z ≠ 1) :
    weightNormSq Z = 1 + ‖(1 - Z⁻¹)⁻¹‖ ^ 2 := by
  have h1 : (1 - Z⁻¹)⁻¹ = Z / (Z - 1) := by
    field_simp [sub_ne_zero.2 hZ1]
  have hZn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.2 hZ
  rw [weightNormSq, h1, norm_div, mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hZn), div_pow,
    div_eq_mul_inv]

/-- Far out, `|Z|² ρ(Z)` tends to `2`: the cylindrical weight is `2 |Z|⁻²` up to a vanishing
relative error. -/
private theorem tendsto_weightNormSq :
    Tendsto weightNormSq (Bornology.cobounded ℂ) (𝓝 2) := by
  have hc : ContinuousAt (fun w : ℂ ↦ 1 + ‖(1 - w)⁻¹‖ ^ 2) 0 :=
    continuousAt_const.add (((continuousAt_const.sub continuousAt_id).inv₀
      (by simp)).norm.pow 2)
  have h := hc.tendsto.comp tendsto_inv₀_cobounded
  rw [show (1 : ℝ) + ‖(1 - (0 : ℂ))⁻¹‖ ^ 2 = 2 by norm_num] at h
  refine h.congr' ((eventually_cobounded_le_norm 2).mono fun Z hZ ↦ ?_)
  have hZ0 : Z ≠ 0 := by rintro rfl; norm_num at hZ
  have hZ1 : Z ≠ 1 := by rintro rfl; norm_num at hZ
  exact (weightNormSq_eq hZ0 hZ1).symm

/-- **Far out, the translation by `c` barely changes the weight and the direction.** For tolerances
`η, δ > 0` there is a radius `R` beyond which `√(|Z|² ρ(Z))` and `√(|Z - c|² ρ(Z - c))` differ by
less than `η`, their ratio times `|1 - c Z⁻¹| = |Z - c| / |Z|` (which is `√ρ(Z) / √ρ(Z - c)`) is
within `η` of `1`, the directions of `Z` and `Z - c` differ by less than `δ`, `|Z|² ρ(Z) ≤ 4` and
`|Z| ≥ 2`. -/
private theorem exists_forall_le_norm_weightNormSq (c : ℂ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ R, ∀ Z : ℂ, R ≤ ‖Z‖ → |√(weightNormSq Z) - √(weightNormSq (Z - c))| < η ∧
      |1 - √(weightNormSq Z) / √(weightNormSq (Z - c)) * ‖1 - c * Z⁻¹‖| < η ∧
      ‖Z / ‖Z‖ - (Z - c) / ‖Z - c‖‖ < δ ∧ weightNormSq Z ≤ 4 ∧ 2 ≤ ‖Z‖ := by
  have hf := tendsto_weightNormSq
  have hfc := hf.comp (tendsto_sub_const_cobounded c)
  have hs := Real.continuous_sqrt.continuousAt (x := 2)
  have h1 : Tendsto (fun Z ↦ √(weightNormSq Z) - √(weightNormSq (Z - c))) (Bornology.cobounded ℂ)
      (𝓝 0) := by
    have h := (hs.tendsto.comp hf).sub (hs.tendsto.comp hfc)
    rwa [sub_self] at h
  have hv : Tendsto (fun Z : ℂ ↦ ‖1 - c * Z⁻¹‖) (Bornology.cobounded ℂ) (𝓝 1) := by
    have hcv : Continuous fun w : ℂ ↦ ‖(1 : ℂ) - c * w‖ := by fun_prop
    have h := (hcv.tendsto 0).comp (tendsto_inv₀_cobounded (α := ℂ))
    rwa [show ‖(1 : ℂ) - c * 0‖ = 1 by simp] at h
  have hs2 : (√2 : ℝ) ≠ 0 := by positivity
  have h2 := ((hs.tendsto.comp hf).div (hs.tendsto.comp hfc) hs2).mul hv
  rw [div_self hs2, one_mul] at h2
  have hev := (h1.eventually (Metric.ball_mem_nhds 0 hη)).and
    ((h2.eventually (Metric.ball_mem_nhds 1 hη)).and
      (((NormedSpace.tendsto_normalize_sub_normalize_sub_cobounded c).eventually
        (Metric.ball_mem_nhds 0 hδ)).and
        ((hf.eventually (Iic_mem_nhds (by norm_num : (2 : ℝ) < 4))).and
          (eventually_cobounded_le_norm 2))))
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
  refine ⟨R, fun Z hZ ↦ ?_⟩
  obtain ⟨ha, hb, hc, hd, he⟩ := hR hZ
  refine ⟨?_, ?_, ?_, hd, he⟩
  · simpa [Metric.mem_ball, Real.dist_eq] using ha
  · simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hb
  · rwa [dist_zero_right, NormedSpace.normalize_eq_div_norm, NormedSpace.normalize_eq_div_norm,
      Complex.coe_algebraMap] at hc

/-- **The end model is uniformly continuous in the angle.** For continuous loops `L_t` and `S_t` of
period one and every `η > 0`, two points of the strip whose angular coordinates `t`, `t'` have
images `exp (2π i t)`, `exp (2π i t')` within `δ` on the circle have unit tangents of the end chart,
and end models, within `η`. -/
private theorem exists_pos_forall_norm_endModelCoeff_sub_lt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (q : Puncture) {L : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} (hL : Continuous fun t ↦ (L t).toLinearMap.toContinuousLinearMap)
    (hS : Continuous S) (hLp : Periodic L 1) (hSp : Periodic S 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ζ ζ' : ℝ × ℝ,
      ‖(Circle.exp (2 * π * ζ.2) : ℂ) - Circle.exp (2 * π * ζ'.2)‖ < δ →
        ‖endUnitTangent q ζ - endUnitTangent q ζ'‖ < η ∧
          ‖endModelCoeff q L S ζ - endModelCoeff q L S ζ'‖ < η := by
  -- Both depend only on `t`, through a continuous function of period one.
  set P : ℝ → (ℝ × ℝ) × (V × V × V →L[ℝ] V) :=
    fun t ↦ (endUnitTangent q (0, t), endModelCoeff q L S (0, t))
  have hGeq : endModelCoeff q L S =
      fun ζ ↦ (endModelRotation q L ζ).comp (stationaryJetCoeff L S ζ) :=
    funext fun ζ ↦ endModelCoeff_def q L S ζ
  have hPc : Continuous P := by
    refine ((continuous_endUnitTangent q).comp (continuous_const.prodMk continuous_id)).prodMk ?_
    rw [hGeq]
    exact ((continuous_endModelRotation q hL).clm_comp
      (continuous_stationaryJetCoeff hL hS)).comp (continuous_const.prodMk continuous_id)
  have hPp : Periodic P 1 := fun t ↦ by
    simp only [P, endUnitTangent_add_one, hGeq, endModelRotation_eq, hLp t]
    congr 2
    exact ContinuousLinearMap.ext fun v ↦ by simp only [stationaryJetCoeff_apply, hLp t, hSp t]
  obtain ⟨G, hGu, hGg⟩ := hPp.exists_uniformContinuous_eq_comp_circleExp hPc
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.1 hGu η hη
  refine ⟨δ, hδ, fun ζ ζ' h ↦ ?_⟩
  -- The metric of `Circle` is the subspace metric of `ℂ`.
  rw [← Circle.dist_eq_norm_coe_sub] at h
  have hd := hG h
  rw [← hGg, ← hGg, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd
  rwa [endUnitTangent_eq_of_snd_eq q (ζ := ζ) (ζ' := (0, ζ.2)) rfl,
    endUnitTangent_eq_of_snd_eq q (ζ := ζ') (ζ' := (0, ζ'.2)) rfl,
    endModelCoeff_eq_of_snd_eq q L S (ζ := ζ) (ζ' := (0, ζ.2)) rfl,
    endModelCoeff_eq_of_snd_eq q L S (ζ := ζ') (ζ' := (0, ζ'.2)) rfl]

/-- With `|Z|² ρ(Z) ≤ 4` at `Z = φ'_∞(ζ)`, the jet coefficient of the transfer along the output end
chart with the cutoff `1` has norm at most `4π + 2`. -/
private theorem norm_endTransferCoeff_inf_one_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {ζ : ℝ × ℝ}
    (h4 : weightNormSq (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) ≤ 4) :
    ‖endTransferCoeff (V := V) inf (fun _ ↦ 1) ζ‖ ≤ 4 * π + 2 := by
  have h := norm_endTransferCoeff_le (V := V) inf (fun _ ↦ 1) ζ
  simp only [abs_one, mul_one, fderiv_const_apply, norm_zero, mul_zero, add_zero,
    positiveEndChartScale_inf_mul_sqrt_cylindricalWeight] at h
  have hs : √(weightNormSq (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ))) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]]
    exact Real.sqrt_le_sqrt h4
  nlinarith [Real.pi_pos]

/-- If `φ'_∞(ζ) = φ'_∞(ζ') + c`, the jet coefficients of the transfer along the output end chart
with the cutoff `1` at `ζ` and `ζ'` differ by at most `2π η + 2η`, when the weighted scales
`√(|Z|² ρ(Z))` at `Z = φ'_∞(ζ)` and `Z - c` and the unit tangents at `ζ` and `ζ'` differ by less
than `η`. -/
private theorem norm_endTransferCoeff_inf_one_sub_le_of_eq_add {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {c η : ℝ} {ζ ζ' : ℝ × ℝ} {Z : ℂ}
    (hζζ' : positiveEndChart inf ζ = positiveEndChart inf ζ' + (c, 0))
    (hZ : Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) = Z)
    (h1 : |√(weightNormSq Z) - √(weightNormSq (Z - c))| < η)
    (he : ‖endUnitTangent inf ζ - endUnitTangent inf ζ'‖ < η) :
    ‖endTransferCoeff (V := V) inf (fun _ ↦ 1) ζ - endTransferCoeff inf (fun _ ↦ 1) ζ'‖ ≤
      2 * π * η + 2 * η := by
  subst hZ
  refine (norm_endTransferCoeff_one_sub_le inf ζ ζ').trans ?_
  rw [positiveEndChartScale_inf_mul_sqrt_cylindricalWeight,
    positiveEndChartScale_inf_mul_sqrt_cylindricalWeight,
    equivRealProdCLM_symm_positiveEndChart_inf_eq_sub hζζ', ← mul_sub, abs_mul,
    abs_of_pos (by positivity)]
  gcongr

/-- **Assembling four comparisons.** If `a` is within `η B` of `a'` with `‖a'‖ ≤ 2B`, `T` has norm
at most `4π + 2` and is within `2π η + 2η` of `T'`, `a' T'` is within `ε / 4` of `g'` and `g'`
within `η` of `g`, and `η (40 B + 1) ≤ ε / 4`, then `a T` is within `ε` of `g`. -/
private theorem norm_comp_sub_le_of_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a a' : F →L[ℝ] G} {T T' : E →L[ℝ] F} {g g' : E →L[ℝ] G} {B η ε : ℝ} (hη : 0 ≤ η)
    (hB : 0 ≤ B) (hε : 0 < ε) (hηε : η * (40 * B + 1) ≤ ε / 4) (ha : ‖a - a'‖ ≤ η * B)
    (ha' : ‖a'‖ ≤ 2 * B) (hT : ‖T‖ ≤ 4 * π + 2) (hTT : ‖T - T'‖ ≤ 2 * π * η + 2 * η)
    (h' : ‖a'.comp T' - g'‖ ≤ ε / 4) (hg : ‖g' - g‖ ≤ η) : ‖a.comp T - g‖ ≤ ε := by
  have hsplit :
      a.comp T - g = (a - a').comp T + a'.comp (T - T') + (a'.comp T' - g') + (g' - g) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  refine norm_add₄_le.trans ?_
  have hηB : 0 ≤ η * B := mul_nonneg hη hB
  have hc1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ha hT (norm_nonneg _) hηB)
  have hc2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ha' hTT (norm_nonneg _) (by linarith))
  have hπ := mul_le_mul_of_nonneg_left Real.pi_le_four hηB
  have hsum : η * B * (4 * π + 2) + 2 * B * (2 * π * η + 2 * η) ≤ η * B * 38 := by
    calc η * B * (4 * π + 2) + 2 * B * (2 * π * η + 2 * η) = 8 * (η * B * π) + 6 * (η * B) := by
          ring
      _ ≤ 8 * (η * B * 4) + 6 * (η * B) := by gcongr
      _ = η * B * 38 := by ring
  have hηε' : η * B * 38 + η ≤ ε / 4 := by nlinarith only [hηε, hηB]
  linarith only [hc1, hc2, h', hg, hsum, hηε', hε]

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Translating the data changes the coefficient field only through the weight.** If
`w + v = z`, the coefficient field on conformal jets at `w` of the data translated by `v` differs
from that of the data at `z` by at most `|1 - √ρ(z) / √ρ(w)|` times the norm of the latter: only
the weight in front of the zeroth-order term is read at a different point. -/
private theorem norm_floerConformalJetCoeff_sub_floerConformalJetCoeff_comp_add_le
    (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) {v z w : ℝ × ℝ} (hwz : w + v = z) (hρz : 0 < √(ρ z)) :
    ‖ω.floerConformalJetCoeff ρ J Ks Kt u z - ω.floerConformalJetCoeff ρ (fun z ↦ J (z + v))
        (fun z ↦ Ks (z + v)) (fun z ↦ Kt (z + v)) (fun z ↦ u (z + v)) w‖ ≤
      |1 - √(ρ z) / √(ρ w)| * ‖ω.floerConformalJetCoeff ρ J Ks Kt u z‖ := by
  rw [floerConformalJetCoeff_comp_add_right, hwz, floerConformalJetCoeff_def]
  -- The zeroth-order parts are `k L` and `k' L`, and `k L - k' L = (1 - k' / k) k L`.
  set L := ω.floerLinearizationCoeff J Ks Kt u z
  set k := (√(ρ z))⁻¹
  set k' := (√(ρ w))⁻¹
  have hkk : k • L - k' • L = (1 - k' / k) • (k • L) := by
    rw [smul_smul, ← sub_smul, sub_mul, one_mul, div_mul_cancel₀ _ (inv_ne_zero hρz.ne')]
  calc _ ≤ ‖k • L - k' • L‖ := norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le _ _ _
    _ = |1 - √(ρ z) / √(ρ w)| * ‖k • L‖ := by rw [hkk, norm_smul, Real.norm_eq_abs, inv_div_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_norm_firstOrderJetCoeff_right _ _) (abs_nonneg _)

/-- **The pointwise comparison with the end model across the recentring.** Let
`z = φ'_∞(ζ) = φ'_∞(ζ') + c`, with `Z = z` read in `ℂ`. Suppose that at `Z` the translation by `c`
changes `√(|Z|² ρ(Z))` by less than `η` and the weight by a factor within `η` of `1`, with
`|Z|² ρ(Z) ≤ 4`; that the unit tangents of the chart at `ζ` and `ζ'`, and the values of `G`
there, differ by less than `η`; that the coefficient field of the data translated by `c`, read at
`ζ'` in the standard chart, is within `ε / 4` of `G`; and that `‖M(z)‖ ≤ B` with
`η (40 B + 1) ≤ ε / 4`, `η ≤ 1`. Then `M` read at `ζ` in the standard chart is within `ε` of `G`. -/
private theorem norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_eq_add
    (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {c : ℝ} (G : ℝ × ℝ → V × V × V →L[ℝ] V) {ζ ζ' : ℝ × ℝ}
    (hζζ' : positiveEndChart inf ζ = positiveEndChart inf ζ' + (c, 0)) {B η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) (hηε : η * (40 * B + 1) ≤ ε / 4)
    (hMB : ‖ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u (positiveEndChart inf ζ)‖ ≤ B)
    {Z : ℂ} (hZ : Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) = Z)
    (h1 : |√(weightNormSq Z) - √(weightNormSq (Z - c))| < η)
    (h2 : |1 - √(weightNormSq Z) / √(weightNormSq (Z - c)) * ‖1 - (c : ℂ) * Z⁻¹‖| < η)
    (h4 : weightNormSq Z ≤ 4) (he : ‖endUnitTangent inf ζ - endUnitTangent inf ζ'‖ < η)
    (hg : ‖G ζ' - G ζ‖ < η)
    (h5 : ‖(ω.floerConformalJetCoeff cylindricalWeight (fun z ↦ J (z + (c, 0)))
        (fun z ↦ Ks (z + (c, 0))) (fun z ↦ Kt (z + (c, 0))) (fun z ↦ u (z + (c, 0)))
        (positiveEndChart inf ζ')).comp (endTransferCoeff inf (fun _ ↦ 1) ζ') - G ζ'‖ ≤ ε / 4) :
    ‖(ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u (positiveEndChart inf ζ)).comp
        (endTransferCoeff inf (fun _ ↦ 1) ζ) - G ζ‖ ≤ ε := by
  set M := ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u
  set M' := ω.floerConformalJetCoeff cylindricalWeight (fun z ↦ J (z + (c, 0)))
    (fun z ↦ Ks (z + (c, 0))) (fun z ↦ Kt (z + (c, 0))) (fun z ↦ u (z + (c, 0)))
  set T := fun ζ ↦ endTransferCoeff (V := V) inf (fun _ ↦ 1) ζ
  subst hZ
  have hW := equivRealProdCLM_symm_positiveEndChart_inf_eq_sub hζζ'
  have hZ0 : 0 < ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)‖ := by
    have := equivRealProdCLM_symm_positiveEndChart_ne_endCenter inf ζ
    rw [endCenter_inf] at this
    exact norm_pos_iff.2 this
  have hW0 : 0 < ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) - c‖ := by
    have := equivRealProdCLM_symm_positiveEndChart_ne_endCenter inf ζ'
    rw [endCenter_inf, hW] at this
    exact norm_pos_iff.2 this
  have hfZ := sqrt_weightNormSq_eq (positiveEndChart inf ζ)
  have hfW := sqrt_weightNormSq_eq (positiveEndChart inf ζ')
  rw [hW] at hfW
  set Z := Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hMB
  have hρz := sqrt_cylindricalWeight_positiveEndChart_pos inf ζ
  have hρw := sqrt_cylindricalWeight_positiveEndChart_pos inf ζ'
  -- (a) The weight: `√(f Z) / √(f (Z - c)) |1 - c Z⁻¹| = √ρ(z) / √ρ(w)`.
  have hq : √(weightNormSq Z) / √(weightNormSq (Z - c)) * ‖1 - (c : ℂ) * Z⁻¹‖ =
      √(cylindricalWeight (positiveEndChart inf ζ)) /
        √(cylindricalWeight (positiveEndChart inf ζ')) := by
    rw [hfZ, hfW, show (1 : ℂ) - c * Z⁻¹ = (Z - c) / Z by field_simp [norm_pos_iff.1 hZ0], norm_div]
    field_simp
  have ha1 : ‖M (positiveEndChart inf ζ) - M' (positiveEndChart inf ζ')‖ ≤ η * B :=
    (norm_floerConformalJetCoeff_sub_floerConformalJetCoeff_comp_add_le ω cylindricalWeight J Ks Kt
      u hζζ'.symm hρz).trans (mul_le_mul (hq ▸ h2).le hMB (norm_nonneg _) hη.le)
  -- (b) Assemble with the comparison of the transfer coefficients at `ζ` and `ζ'`.
  have ha3 : ‖M' (positiveEndChart inf ζ')‖ ≤ 2 * B := by
    have h := norm_sub_le (M (positiveEndChart inf ζ))
      (M (positiveEndChart inf ζ) - M' (positiveEndChart inf ζ'))
    rw [sub_sub_cancel] at h
    nlinarith [mul_le_mul_of_nonneg_right hη1 hB0]
  exact norm_comp_sub_le_of_le hη.le hB0 hε hηε ha1 ha3 (norm_endTransferCoeff_inf_one_le h4)
    (norm_endTransferCoeff_inf_one_sub_le_of_eq_add hζζ' rfl h1 he) h5 hg.le

/-- **The translated data converge to the end model in the standard chart.** Under the
hypotheses of `exists_ae_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_recentered`,
the translates by `c` of the data and of `u` are, beyond the height `R₁` of the standard chart
`φ'_∞`, the pair-of-pants data and a solution of their Floer equation, so their coefficient field
read along `φ'_∞` is eventually uniformly within `ε` of the end model of `x`. -/
private theorem eventually_forall_norm_floerConformalJetCoeff_comp_add_comp_endTransferCoeff_sub_lt
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ContDiff ℝ 2 (uncurry (H inf))) {c : ℝ}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hu : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart inf ζ + (c, 0)))
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    {x : ℝ → V} (hxc : Continuous x)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J (z + (c, 0)) y).toLinearMap.toContinuousLinearMap)
          (fun z ↦ Ks (z + (c, 0))) (fun z ↦ Kt (z + (c, 0))) (fun z ↦ u (z + (c, 0)))
          (positiveEndChart inf (s, t))).comp (endTransferCoeff inf (fun _ ↦ 1) (s, t)) -
        endModelCoeff inf (fun t ↦ Je t (x t))
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t)) (x t))
          (s, t)‖ < ε :=
  ω.eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt hH hHs hJe
    (J := fun z ↦ J (z + (c, 0))) (Ks := fun z ↦ Ks (z + (c, 0)))
    (Kt := fun z ↦ Kt (z + (c, 0))) (u := fun z ↦ u (z + (c, 0))) (T := R₁) hJeq
    (fun ζ hζ ↦ hK _ (by rwa [fst_positiveEndCoord_positiveEndChart]))
    (fun ζ hζ ↦ DifferentiableAt.comp (positiveEndChart inf ζ) (hu ζ hζ)
      (differentiableAt_id.add_const ((c, 0) : ℝ × ℝ)))
    (fun ζ hζ ↦ by
      rw [ω.perturbedFDeriv_comp_add_right]
      exact hF _ (by rwa [fst_positiveEndCoord_positiveEndChart]))
    (β := fun _ ↦ 1) (fun _ _ ↦ ⟨rfl, by simp⟩) hxc hux hδ hε

/-- **The linearized operator with a recentred output end converges to the end model in the
standard end chart.** Let `|c| ≤ 1`, and far out on the output end, beyond the height `R₁` of the
end chart `c + φ'_∞` recentred at `c`, let the Floer data be cylindrical, `J(φ'_∞(s, t) + c) =
J_∞(t)` for a `C¹` family `J_∞`, with the pair-of-pants perturbation of period-one Hamiltonians
`H_q` (with `H_∞` jointly `C²`) translated by `c`; let `u` be differentiable and solve the Floer
equation there, and let the loops of `u` read in the recentred chart converge uniformly to a
continuous loop `x` of period one, with slice defect tending uniformly to zero. If the coefficient
field `M` of the linearized operator on the conformal jets of the cylindrical weight is
essentially bounded on `S`, then `M` read in the standard end chart `φ'_∞` with the cutoff `1`
converges in `L^∞` to the end model `TauCeti.Floer.endModelCoeff` of the orbit `x`: for every
`ε > 0`, beyond some height it is within `ε` of the end model almost everywhere.

The two charts differ by the translation by `c`, which far out on the end moves points by an
amount that is small compared with their distance to the centre: it changes the weighted
conformal scale `r √ρ`, the direction of the chart and the angular coordinate by vanishing
amounts, while the translated data are the pair-of-pants data in the standard chart. -/
theorem exists_ae_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ContDiff ℝ 2 (uncurry (H inf))) {c : ℝ} (hc : |c| ≤ 1)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hu : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart inf ζ + (c, 0)))
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    {x : ℝ → V} (hxc : Continuous x) (hxp : Periodic x 1)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ᵐ ζ ∂stripMeasure, T₀ < ζ.1 →
      ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart inf ζ)).comp (endTransferCoeff inf (fun _ ↦ 1) ζ) -
        endModelCoeff inf (fun t ↦ Je t (x t))
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t)) (x t))
          ζ‖ ≤ ε := by
  set Jx : ℝ → AlmostComplexStructure V := fun t ↦ Je t (x t)
  set S : ℝ → V →L[ℝ] V :=
    fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t)) (x t) with hS_def
  -- The coefficient field is essentially bounded along the end chart, by `B ≥ 1`.
  have hMb := ae_le_lpNorm_exponent_top
    (hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart inf))
  set B := lpNorm (ω.floerConformalJetCoeff cylindricalWeight
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ∘ positiveEndChart inf) ∞
      stripMeasure + 1
  -- The data along the orbit are continuous and have period one.
  have hJxc : Continuous fun t ↦ (Jx t).toLinearMap.toContinuousLinearMap :=
    hJe.continuous.comp (continuous_id.prodMk hxc)
  have hSc : Continuous S :=
    ω.continuous_fderiv_hamiltonianVectorField_positiveEndHamiltonian hHs hxc
  -- Choose the tolerance `η`, then the angular tolerance `δ`, the radius `R` and the height `T₄`.
  set η := min 1 (ε / (4 * (40 * B + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity [show (1 : ℝ) ≤ B by simp [B]])
  have hηε : η * (40 * B + 1) ≤ ε / 4 := by
    rw [← le_div_iff₀ (by positivity [show (1 : ℝ) ≤ B by simp [B]]), div_div]
    exact min_le_right _ _
  obtain ⟨δ, hδpos, hang⟩ := exists_pos_forall_norm_endModelCoeff_sub_lt inf hJxc hSc
    (periodic_apply_of_forall_positiveEndChart_add_eq inf (c, 0) hJeq hxp)
    (fun t ↦ by simp only [hS_def, hxp t, periodic_positiveEndHamiltonian (hH inf) t]) hη
  obtain ⟨R, hR⟩ := exists_forall_le_norm_weightNormSq (c : ℂ) hη hδpos
  -- Far out, the translated data are those of the pair of pants in the standard chart.
  obtain ⟨T₄, hT₄⟩ := eventually_atTop.1
    (ω.eventually_forall_norm_floerConformalJetCoeff_comp_add_comp_endTransferCoeff_sub_lt hH hHs
      hJe hJeq hK hu hF hxc hux hδ (by positivity : 0 < ε / 4))
  set T₁ := max T₄ (max R₁ 0)
  refine ⟨max (T₁ + 1) R, ?_⟩
  filter_upwards [hMb] with ζ hζM hζ
  -- Read the point `z = φ'_∞(ζ)` in the recentred chart: `z = φ'_∞(ζ') + c`; far out
  -- `|z| = 2 exp (2π ζ₁)` exceeds `R`.
  have hT₁ : 0 ≤ T₁ := (le_max_right R₁ 0).trans (le_max_right _ _)
  obtain ⟨ζ', hζ'1, hζ'2, hζζ'⟩ := exists_positiveEndChart_inf_eq_add hc hT₁
    ((le_max_left _ _).trans_lt hζ)
  have hRZ := le_norm_equivRealProdCLM_symm_positiveEndChart_inf (R := R) (ζ := ζ)
    (max_le ((le_max_right _ _).trans hζ.le) (by linarith [(le_max_left (T₁ + 1) R).trans hζ.le]))
  obtain ⟨h1, h2, h3, h4, -⟩ := hR _ hRZ
  obtain ⟨he, hg⟩ := hang ζ ζ' (by
    rw [Circle.coe_exp, Circle.coe_exp, ← equivRealProdCLM_symm_positiveEndChart_inf_div_norm,
      ← equivRealProdCLM_symm_positiveEndChart_inf_div_norm,
      equivRealProdCLM_symm_positiveEndChart_inf_eq_sub hζζ']
    exact h3)
  have h5 := hT₄ ζ'.1 ((le_max_left _ _).trans hζ'1.le) ζ'.2 (Ico_subset_Icc_self hζ'2)
  rw [Prod.mk.eta] at h5
  exact norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_eq_add ω _ Ks Kt u _ hζζ' hη
    (min_le_left _ _) hε hηε (hζM.trans (le_add_of_nonneg_right zero_le_one)) rfl h1 h2 h4 he
    (by rw [norm_sub_rev]; exact hg) h5.le

section Fredholm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The output-end contribution to a right parametrix for a recentred output end.** Under the
hypotheses of `exists_ae_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_recentered`,
if the stationary cylinder operator `∂s + J_∞(t, x(t)) (∂t - dX_{H'_∞(t)}(x(t)))` is invertible on
`W^{1,2}(ℝ × S¹, F)`, then the output end carries an end piece of a right parametrix of `D_u` in the
standard end chart `φ'_∞` (`TauCeti.Floer.HasEndParametrixPiece`): an operator `Q` such that `D_u`
applied to the transfer `β · (Q h ∘ ψ)` along `φ'_∞`, for a cutoff `β` living far enough out on the
end, is the transfer of `β(φ'_∞) h + K h + E h` with `K` compact and `‖E‖ ≤ B ε`. This is the
recentred counterpart of
`hasEndParametrixPiece_floerConformalJetCoeff`. -/
theorem hasEndParametrixPiece_floerConformalJetCoeff_of_recentered
    (ω : SymplecticForm F) {H : Puncture → ℝ → F → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ContDiff ℝ 2 (uncurry (H inf))) {c : ℝ} (hc : |c| ≤ 1)
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Je : ℝ → F → AlmostComplexStructure F}
    (hJe : ContDiff ℝ 1 fun p : ℝ × F ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hu : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart inf ζ + (c, 0)))
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] F))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    {x : ℝ → F} (hxc : Continuous x) (hxp : Periodic x 1)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    (hD : (stationarySobolevOperator (fun t ↦ Je t (x t)) fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t)) (x t)).IsInvertible) :
    HasEndParametrixPiece inf (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) :=
  hasEndParametrixPiece_of_tendsto_endModelCoeff inf hM
    (hJe.continuous.comp (continuous_id.prodMk hxc))
    (ω.continuous_fderiv_hamiltonianVectorField_positiveEndHamiltonian hHs hxc) hD
    fun _ hε ↦ ω.exists_ae_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le_of_recentered hH
      hHs hc hJe hJeq hK hu hF hM hxc hxp hux hδ hε

/-- **The linearized operator with a recentred output end is Fredholm.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_q`
be jointly `C³` period-one Hamiltonians on the three ends of the pair of pants `S = ℂ ∖ {0, 1}`,
with nondegenerate one-periodic orbits `x_q` of the end Hamiltonians, and let `0 ≤ c ≤ 1`. Let
`(J, K_s, K_t)` be Floer data on `S` which far out on the input ends are the structures `J_q(t)` of
a `C¹` family and the pair-of-pants perturbation of the `H_q` in the positive end charts `φ'_q`,
and far out on the output end are the structures `J_∞(t)` and the pair-of-pants perturbation
translated by `c`, in the end chart `c + φ'_∞` recentred at `c`; the structures `J_q(t)` are
compatible with `ω` and `C²` in `t` along `x_q`. Let `u` be `C¹` on `S`, solve the Floer equation
far out on the ends, and converge there, in these end charts, to the orbits `x_q`, while on all of
`S` the structures `J(z, u z)` are `ω`-compatible and the data are regular along `u`. Then the
realization `D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator for the
cylindrical metric is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_of_recentered
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : Puncture → ℝ → F → ℝ}
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] F))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] F))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  have hcabs : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have hM := ω.memLp_floerConformalJetCoeff_of_recentered hH hHs₂ hcabs
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe hJeq
    hJeq_inf hK hK_inf hJ hKs hKt hu hF hF_inf hux hux_inf hδ hδ_inf
  refine isFredholm_floerConformalSobolevOperator_of_endParametrix ω hω (hX zero)
    (contDiff_uncurry_positiveEndHamiltonian (hHs zero)) (periodic_positiveEndHamiltonian (hH zero))
    (hx zero) (hxp zero) (hnd zero) (fun z hz ↦ (hJ z hz).continuousAt.comp
      (f := fun z ↦ (z, u z)) (continuousAt_id.prodMk (hu z hz).continuousAt)) hc hM
    (ω.finiteDimensional_ker_floerConformalSobolevOperator_of_recentered hH hHs₂ hc₀ hc₁ hX hx hnd
      hJe hJex hJeq hJeq_inf hK hK_inf hJ hKs hKt hu hc hF hF_inf hux hux_inf hδ hδ_inf)
    fun q ↦ ?_
  set R := max R₁ 1
  have hR₁ : R₁ ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_right _ _
  by_cases hq : q = inf
  · -- The output end: the end model is reached in the standard chart by translating by `c`.
    subst hq
    exact ω.hasEndParametrixPiece_floerConformalJetCoeff_of_recentered
      hH (hHs₂ inf) hcabs (hJe inf) (R₁ := R) (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ))
      (fun z hz ↦ hK_inf z (hR₁.trans hz))
      (fun ζ hζ ↦ (hu _ (positiveEndChart_inf_add_mem_thricePuncturedSphereReal hcabs
        (hR1.trans hζ))).differentiableAt one_ne_zero)
      (fun z hz ↦ hF_inf z (hR₁.trans hz)) hM
      (continuous_iff_continuousAt.2 fun t ↦ (hx inf t).continuousAt) (hxp inf) hux_inf hδ_inf
      (isInvertible_stationarySobolevOperator_of_compatible ω hω (hX inf)
        (contDiff_uncurry_positiveEndHamiltonian (hHs inf))
        (periodic_positiveEndHamiltonian (hH inf)) (hx inf) (hxp inf) (hnd inf) (hJex inf)
        (hJx inf) (periodic_apply_of_forall_positiveEndChart_add_eq inf (c, 0) hJeq_inf (hxp inf)))
  · -- An input end: far out the data are those of the pair of pants.
    exact ω.hasEndParametrixPiece_floerConformalJetCoeff_of_isNondegenerateFixedPt hω hH (hHs q)
      (hX q) (hx q) (hxp q) (hnd q) (hJe q) (hJex q) (hJx q) (hJeq q hq) (hK q hq)
      (fun z hz _ ↦ (hu z hz).differentiableAt one_ne_zero) (hF q hq) hM (hux q hq) (hδ q hq)

/-- **The linearized operator along the input-exchange family is Fredholm.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_q`
be jointly `C³` period-one Hamiltonians on the three ends of the pair of pants `S = ℂ ∖ {0, 1}`,
with nondegenerate one-periodic orbits `x_q` of the end Hamiltonians, and let `0 ≤ c ≤ 1`. For
the member `K_c = TauCeti.Floer.exchangePerturbation H c` of the input-exchange family, whose
output end is recentred at `c`, and structures `J` which far out on the ends are `C¹` families
`J_q(t)`, compatible with `ω` and `C²` in `t` along `x_q`, let `u` be `C¹` on `S`, solve the Floer
equation of `(J, K_c)` far out on the ends and converge there, in the end charts of `K_c`, to the
orbits `x_q`, while `J(z, u z)` is `ω`-compatible on all of `S`. Then the realization
`D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator of `(J, K_c)` for the
cylindrical metric is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_exchangePerturbation
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : Puncture → ℝ → F → ℝ}
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] F))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] F))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm := by
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  -- Beyond the height `max R₁ 2`, `K_c` is the pair-of-pants datum on the input ends and its
  -- translate by `c` on the output end.
  have hR₁ : R₁ ≤ max R₁ 2 := le_max_left _ _
  have h1 {r : ℝ} (hr : max R₁ 2 ≤ r) : 1 < r := by linarith [le_max_right R₁ 2]
  exact ω.isFredholm_floerConformalSobolevOperator_of_recentered hω hH hHs hc₀ hc₁ hX hx hxp hnd
    hJe hJex hJx (fun q hq ζ hζ ↦ hJeq q hq ζ (hR₁.trans hζ))
    (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ))
    (fun q hq _ _ hz ↦ by
      have h := exchangePerturbation_eq_of_pos_fst_positiveEndCoord (H := H) hc₀ hc₁ hq
        (by linarith [h1 hz])
      exact ⟨funext fun x ↦ by rw [h], funext fun x ↦ by rw [h]⟩)
    (fun _ hz ↦ by
      have h := exchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord (H := H) hc₀ hc₁ (h1 hz)
      exact ⟨funext fun x ↦ by rw [h], funext fun x ↦ by rw [h]⟩) hJ
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs₂ c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs₂ c hz (u z) Complex.I) hu hc
    (fun q hq z hz hzR ↦ hF q hq z hz (hR₁.trans hzR)) (fun z hz ↦ hF_inf z (hR₁.trans hz)) hux
    hux_inf hδ hδ_inf

end Fredholm

end TauCeti.SymplecticForm
