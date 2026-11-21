/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
public import TauCeti.MeasureTheory.Function.Lp.Exponent
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Basic
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.AbsRpow

/-!
# The Sobolev embedding of `H¹` on a closed Riemannian manifold

Let `M` be a compact boundaryless manifold of dimension `n > 2` with a continuous Riemannian metric
and volume `dV`. Extending the smooth Sobolev inequality
(`TauCeti.Manifold.exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add`) by continuity from dense smooth
functions and composing with `MeasureTheory.Lp.ofExponentLEL` yields the continuous linear inclusion

`TauCeti.Manifold.SobolevH1.toLpOfLE : H¹(M) →L[ℝ] L^q(M)`

for every `1 ≤ q ≤ 2 n / (n - 2)`, preserving the underlying equivalence class
(`TauCeti.Manifold.SobolevH1.coeFn_toLpOfLE`). Consequently `toLp w ∈ L^q(M)` for all
`q ≤ 2 n / (n - 2)` (`TauCeti.Manifold.SobolevH1.memLp_toLp`), both `w ↦ ∫ |toLp w| ^ p dV` and
`v ↦ ∫ |toLp w| ^ (p - 2) (toLp w) (toLp v) dV` are norm-continuous on `H¹(M)` for
`1 ≤ p ≤ 2 n / (n - 2)` (`TauCeti.Manifold.SobolevH1.continuous_integral_abs_toLp_rpow`,
`TauCeti.Manifold.SobolevH1.continuous_integral_abs_toLp_rpow_sub_two_mul`), and for
`0 < p ≤ 2 n / (n - 2)` with a `C¹` metric, `0 < ∫ |toLp w| ^ p dV ↔ w ≠ 0`
(`TauCeti.Manifold.SobolevH1.integral_abs_toLp_rpow_pos_iff`).

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 2.21.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities* (1999), Theorem 3.1.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

open Bundle MeasureTheory Module
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

section Exponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem two_lt_criticalReal (hn : 2 < finrank ℝ E) :
    2 < (2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ) := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  rw [lt_div_iff₀ (by linarith)]; linarith

private theorem one_le_ofReal_critical (hn : 2 < finrank ℝ E) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)) :=
  ENNReal.one_le_ofReal.2 ((by norm_num : (1 : ℝ) ≤ 2).trans (two_lt_criticalReal hn).le)

end Exponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Smooth functions satisfy `‖u‖_{L^{2n/(n-2)}} ≤ 2 C ‖u‖_{H¹}` for the Sobolev constant `C`. -/
private theorem exists_norm_toLp_critical_le (hn : 2 < finrank ℝ E) :
    letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
      ⟨one_le_ofReal_critical hn⟩
    ∃ A : ℝ, ∀ u : C^∞⟮I, M; ℝ⟯,
      ‖ContinuousMap.toLp (ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)))
          (riemannianVolume I M) ℝ (u : C(M, ℝ))‖ ≤ A * ‖ofSmooth u‖ := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNorm_mgradient_two_add (I := I) (M := M) hn
  refine ⟨2 * C, fun u ↦ ?_⟩
  set dV := riemannianVolume I M
  set pstar := ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))
  have hval : eLpNorm u 2 dV ≤ ENNReal.ofReal ‖ofSmooth u‖ := by
    rw [← eLpNorm_congr_ae (toLp_ofSmooth_ae_eq u), ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_toLp_le _)
  have hgrad : eLpNorm (fun x ↦ ‖mgradient I u x‖) 2 dV ≤ ENNReal.ofReal ‖ofSmooth u‖ := by
    let G : C(M, ℝ) :=
      ⟨fun x ↦ ‖mgradient I u x‖, continuous_norm_mgradient (u.contMDiff.of_le (by simp))⟩
    have hG : ContinuousMap.toLp 2 dV ℝ G =ᵐ[dV] fun x ↦ ‖mgradient I u x‖ := by
      simpa only [G, ContinuousMap.coe_mk] using ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) dV G
    rw [← eLpNorm_congr_ae hG, ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_toLp_norm_mgradient_le u)
  rw [Lp.norm_def,
    eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := pstar) (𝕜 := ℝ) dV (u : C(M, ℝ)))]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((hC u (u.contMDiff.of_le (by simp))).trans ?_)
  calc (C : ℝ≥0∞) * (eLpNorm (fun x ↦ ‖mgradient I u x‖) 2 dV + eLpNorm u 2 dV)
      ≤ C * (ENNReal.ofReal ‖ofSmooth u‖ + ENNReal.ofReal ‖ofSmooth u‖) := by gcongr
    _ = ENNReal.ofReal (2 * C * ‖ofSmooth u‖) := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul C.coe_nonneg]; ring_nf

/-- The critical Sobolev inclusion `H¹(M) →L[ℝ] L^{2n/(n-2)}(M)` constructed by completion. -/
private def toCriticalLpAux (hn : 2 < finrank ℝ E) :
    letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
      ⟨one_le_ofReal_critical hn⟩
    SobolevH1 I M →L[ℝ]
      Lp ℝ (ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (riemannianVolume I M) :=
  letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  liftSmooth
    ((ContinuousMap.toLp (ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)))
        (riemannianVolume I M) ℝ).toLinearMap ∘ₗ
      (⟨⟨fun u ↦ (u : C(M, ℝ)), fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C(M, ℝ)))
    (exists_norm_toLp_critical_le hn)

/-- **The Sobolev embedding on a closed Riemannian manifold.** On a compact manifold without
boundary of dimension `n > 2` with a continuous Riemannian metric, `H¹(M)` embeds continuously and
linearly into `L^q(M)` for every `1 ≤ q ≤ 2 n / (n - 2)`, preserving the underlying equivalence
class (`TauCeti.Manifold.SobolevH1.coeFn_toLpOfLE`). -/
def toLpOfLE {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :
    SobolevH1 I M →L[ℝ] Lp ℝ q (riemannianVolume I M) :=
  letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  (Lp.ofExponentLEL ℝ ℝ hq).comp (toCriticalLpAux hn)

/-- On a smooth function `u`, the Sobolev embedding into `L^q(M)` gives the `L^q` class of `u`. -/
@[simp]
theorem toLpOfLE_ofSmooth {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (u : C^∞⟮I, M; ℝ⟯) :
    toLpOfLE hn hq (ofSmooth u) = ContinuousMap.toLp q (riemannianVolume I M) ℝ (u : C(M, ℝ)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  rw [toLpOfLE, ContinuousLinearMap.comp_apply, toCriticalLpAux, liftSmooth_ofSmooth]
  simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine Lp.ext ?_
  rw [Lp.coeFn_ofExponentLEL]
  exact (ContinuousMap.coeFn_toLp _ (u : C(M, ℝ))).trans
    (ContinuousMap.coeFn_toLp (p := q) (𝕜 := ℝ) (riemannianVolume I M) (u : C(M, ℝ))).symm

/-- Lowering the exponent commutes with `TauCeti.Manifold.SobolevH1.toLpOfLE`. -/
@[simp]
theorem ofExponentLEL_toLpOfLE {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hn : 2 < finrank ℝ E) (hqr : q ≤ r)
    (hr : r ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    Lp.ofExponentLEL ℝ ℝ hqr (toLpOfLE hn hr w) = toLpOfLE hn (hqr.trans hr) w := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  simp [toLpOfLE]

/-- At `q = 2`, the Sobolev embedding `toLpOfLE` coincides with `toLp`. -/
@[simp]
theorem toLpOfLE_two (hn : 2 < finrank ℝ E)
    (h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :
    toLpOfLE (I := I) (M := M) hn h2 = toLp := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ by simp

/-- For every `1 ≤ q ≤ 2 n / (n - 2)`, `toLpOfLE hn hq w` has the same underlying function as the
`L²` value `toLp w`. -/
@[simp]
theorem coeFn_toLpOfLE {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    ⇑(toLpOfLE hn hq w) = ⇑(toLp w) := by
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)) :=
    ENNReal.ofReal_ofNat 2 ▸ ENNReal.ofReal_le_ofReal (two_lt_criticalReal hn).le
  have h1 : Lp.ofExponentLEL ℝ ℝ (Fact.out : 1 ≤ q) (toLpOfLE hn hq w) =
      Lp.ofExponentLEL ℝ ℝ one_le_two (toLp w) := by
    rw [ofExponentLEL_toLpOfLE, ← toLpOfLE_two hn h2, ofExponentLEL_toLpOfLE]
  simpa only [Lp.coeFn_ofExponentLEL] using congrArg (fun f : Lp ℝ 1 (riemannianVolume I M) ↦ ⇑f) h1

/-- `toLpOfLE hn hq w` vanishes in `L^q(M)` if and only if `toLp w` vanishes in `L²(M)`. -/
theorem toLpOfLE_eq_zero_iff_toLp_eq_zero {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    toLpOfLE hn hq w = 0 ↔ toLp w = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero, Lp.eq_zero_iff_ae_eq_zero, coeFn_toLpOfLE]

/-- **Integrability up to the critical exponent.** On a closed Riemannian manifold of dimension
`n > 2`, the value `toLp w` of every `w ∈ H¹(M)` belongs to `L^q(M)` for all
`q ≤ 2 n / (n - 2)`. -/
theorem memLp_toLp {q : ℝ≥0∞} (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    MemLp (toLp w) q (riemannianVolume I M) := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_ofReal_critical hn⟩
  exact coeFn_toLpOfLE hn le_rfl w ▸ (Lp.memLp (toLpOfLE hn le_rfl w)).mono_exponent hq

/-! ### Integral functionals up to the critical exponent -/

/-- For `1 ≤ q ≤ 2 n / (n - 2)`, `∫ |toLp w| ^ q dV` equals the `q`-th power of the `L^q` norm of
`toLpOfLE hn hq w`. -/
theorem integral_abs_toLp_rpow_eq_norm_toLpOfLE_rpow {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    ∫ x, |toLp w x| ^ q.toReal ∂riemannianVolume I M = ‖toLpOfLE hn hq w‖ ^ q.toReal := by
  simpa only [coeFn_toLpOfLE hn hq w, Real.norm_eq_abs] using Lp.integral_norm_rpow_eq_norm_rpow
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq)
    (toLpOfLE hn hq w)

/-- **Norm continuity of `Lᵖ` moments on `H¹(M)`.** In dimension `n > 2`, for every
`1 ≤ p ≤ 2 n / (n - 2)` the functional `w ↦ ∫ |toLp w| ^ p dV` is continuous on `H¹(M)`. -/
theorem continuous_integral_abs_toLp_rpow (hn : 2 < finrank ℝ E) {p : ℝ}
    (hp1 : 1 ≤ p) (hp : p ≤ 2 * finrank ℝ E / (finrank ℝ E - 2)) :
    Continuous fun w : SobolevH1 I M ↦ ∫ x, |toLp w x| ^ p ∂riemannianVolume I M := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp1⟩
  have hp0 : 0 ≤ p := zero_le_one.trans hp1
  have heq (w : SobolevH1 I M) : ∫ x, |toLp w x| ^ p ∂riemannianVolume I M =
      ‖toLpOfLE hn (ENNReal.ofReal_le_ofReal hp) w‖ ^ p := by
    simpa only [ENNReal.toReal_ofReal hp0] using
      integral_abs_toLp_rpow_eq_norm_toLpOfLE_rpow hn (ENNReal.ofReal_le_ofReal hp) w
  simp_rw [heq]
  exact ((toLpOfLE hn (ENNReal.ofReal_le_ofReal hp)).continuous.norm).rpow_const fun _ ↦ Or.inr hp0

/-- **Norm continuity of nonlinear `Lᵖ` pairings on `H¹(M)`.** In dimension `n > 2`, for every
`1 ≤ p ≤ 2 n / (n - 2)` and fixed `w ∈ H¹(M)`, the functional
`v ↦ ∫ |toLp w| ^ (p - 2) (toLp w) (toLp v) dV` is continuous on `H¹(M)`. -/
theorem continuous_integral_abs_toLp_rpow_sub_two_mul (hn : 2 < finrank ℝ E) {p : ℝ}
    (hp1 : 1 ≤ p) (hp : p ≤ 2 * finrank ℝ E / (finrank ℝ E - 2)) (w : SobolevH1 I M) :
    Continuous fun v : SobolevH1 I M ↦
      ∫ x, |toLp w x| ^ (p - 2) * toLp w x * toLp v x ∂riemannianVolume I M := by
  set q := ENNReal.ofReal p
  set q' := ENNReal.conjExponent q
  set μ := riemannianVolume I M
  have : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.2 hp1⟩
  have hconj : q'.HolderConjugate q := (inferInstance : q.HolderConjugate q').symm
  have : Fact (1 ≤ q') := ⟨hconj.one_le⟩
  have hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2)) :=
    ENNReal.ofReal_le_ofReal hp
  have hg : MemLp (fun x ↦ |toLp w x| ^ (p - 2) * toLp w x) q' μ :=
    (memLp_toLp hn hq w).abs_rpow_sub_two_mul (q' := q')
  let L : SobolevH1 I M →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q' q (hg.toLp _)).comp (toLpOfLE hn hq)
  refine L.continuous.congr fun v ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lpPairing_mul_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, coeFn_toLpOfLE hn hq v]

/-- For `0 < p ≤ 2 n / (n - 2)`, `∫ |toLp w| ^ p dV` is positive if and only if `toLp w ≠ 0`. -/
theorem integral_abs_toLp_rpow_pos_iff_toLp_ne_zero (hn : 2 < finrank ℝ E) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 2 * finrank ℝ E / (finrank ℝ E - 2)) {w : SobolevH1 I M} :
    0 < ∫ x, |toLp w x| ^ p ∂riemannianVolume I M ↔ toLp w ≠ 0 := by
  have hint : Integrable (fun x ↦ |toLp w x| ^ p) (riemannianVolume I M) := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using
      (memLp_toLp hn (ENNReal.ofReal_le_ofReal hp) w).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top
  rw [integral_pos_iff_support_of_nonneg_ae (.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    hint, pos_iff_ne_zero, Ne, measure_eq_zero_iff_ae_notMem, Ne, Lp.eq_zero_iff_ae_eq_zero]
  refine not_congr ⟨fun h ↦ h.mono fun x hx ↦ ?_, fun h ↦ h.mono fun x hx ↦ ?_⟩
  · exact abs_eq_zero.1 ((Real.rpow_eq_zero (abs_nonneg _) hp0.ne').1 (not_not.1 hx))
  · simp [Function.mem_support, hx, Real.zero_rpow hp0.ne']

/-- **The critical Sobolev inequality on `H¹(M)`.** On a closed Riemannian manifold of dimension
`n > 2` with a continuous metric, let `p' = 2 n / (n - 2)`. There is a constant `K > 0` such that
`(∫ |toLp w| ^ p' dV) ^ (2 / p') ≤ K ‖w‖²` for every `w ∈ H¹(M)`. -/
theorem exists_integral_abs_toLp_rpow_rpow_le_mul_norm_sq (hn : 2 < finrank ℝ E) :
    ∃ K, 0 < K ∧ ∀ w : SobolevH1 I M,
      (∫ x, |toLp w x| ^ (2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ) ∂riemannianVolume I M) ^
          (2 / (2 * finrank ℝ E / (finrank ℝ E - 2) : ℝ)) ≤ K * ‖w‖ ^ 2 := by
  set p : ℝ := 2 * finrank ℝ E / (finrank ℝ E - 2)
  have hp : 2 < p := two_lt_criticalReal hn
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨one_le_ofReal_critical hn⟩
  set S := toLpOfLE (I := I) (M := M) hn (le_refl (ENNReal.ofReal p))
  refine ⟨(‖S‖ + 1) ^ 2, by positivity, fun w ↦ ?_⟩
  have hI : ∫ x, |toLp w x| ^ p ∂riemannianVolume I M = ‖S w‖ ^ p := by
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
      integral_abs_toLp_rpow_eq_norm_toLpOfLE_rpow hn (le_refl (ENNReal.ofReal p)) w
  rw [hI, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ (by linarith : p ≠ 0), Real.rpow_two,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((S.le_opNorm w).trans (by gcongr; linarith)) 2

/-! ### Injectivity for `C¹` metrics -/

section Injectivity

variable [IsManifold I ∞ M] [T2Space M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- On a closed manifold with a `C¹` metric, the Sobolev embedding `H¹(M) →L[ℝ] L^q(M)` is
injective for every `1 ≤ q ≤ 2 n / (n - 2)`. -/
theorem toLpOfLE_injective {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :
    Function.Injective (toLpOfLE (I := I) (M := M) hn hq) :=
  (injective_iff_map_eq_zero _).2 fun w hw ↦
    toLp_injective (map_zero (toLp (I := I) (M := M)) ▸
      (toLpOfLE_eq_zero_iff_toLp_eq_zero hn hq w).1 hw)

@[simp]
theorem toLpOfLE_eq_zero_iff {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) (w : SobolevH1 I M) :
    toLpOfLE hn hq w = 0 ↔ w = 0 :=
  map_eq_zero_iff _ (toLpOfLE_injective hn hq)

/-- **Positivity of `Lᵖ` moments on `H¹(M)`.** On a closed manifold of dimension `n > 2` with a
`C¹` metric, for `0 < p ≤ 2 n / (n - 2)` and `w ∈ H¹(M)`, `0 < ∫ |toLp w| ^ p dV` holds if and only
if `w ≠ 0`. -/
theorem integral_abs_toLp_rpow_pos_iff (hn : 2 < finrank ℝ E) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 2 * finrank ℝ E / (finrank ℝ E - 2)) {w : SobolevH1 I M} :
    0 < ∫ x, |toLp w x| ^ p ∂riemannianVolume I M ↔ w ≠ 0 := by
  rw [integral_abs_toLp_rpow_pos_iff_toLp_ne_zero hn hp0 hp, Ne,
    map_eq_zero_iff _ toLp_injective]

end Injectivity

end TauCeti.Manifold.SobolevH1
