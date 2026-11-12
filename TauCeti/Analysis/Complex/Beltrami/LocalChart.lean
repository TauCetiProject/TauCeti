/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Chart
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# Planar isothermal charts without a smallness hypothesis

Let `J` be a field of almost complex structures on the plane, tame at `c` and of class `C¹` near
`c`. There is a local chart `e` of the plane around `c`, of class `C¹` with `C¹` inverse, whose
differential carries `J` to multiplication by `i` at every point of its source
(`TauCeti.Beltrami.exists_isothermalChart_of_contDiffAt`).

The planar Beltrami chart `TauCeti.Beltrami.exists_isComplexLinear_chart` needs a coefficient
that is small in the Hölder norm. The coefficient `μ_J` of `J` is reduced to this case in three
steps, following McDuff–Salamon, Appendix E.

* *Normalization.* The real-linear map `A = linearEquiv μ_J(c)` carries `J c` to the standard
  structure (`TauCeti.Beltrami.transport_linearEquiv_eq_std`), so the coefficient `μ₁` of the
  structure `J` read through `w ↦ A (w - c)` vanishes at `0`.
* *Rescaling and cutoff.* Rescaling by `ε` does not change the structures, and with a fixed cutoff
  `χ`, equal to `1` on the unit disc and vanishing off the disc of radius `2`, the coefficient
  `ν(z) = χ(z) μ₁(ε z)` has Hölder norm `O(ε)`, because `μ₁` is Lipschitz near `0` and vanishes
  there.
* *Inversion.* For `ε` small the Beltrami solution has real derivative within `C ‖ν‖ < 1` of the
  identity on the disc, so the chart has an invertible derivative and a `C¹` inverse.

Composing the chart of `ν` with `w ↦ ε⁻¹ A (w - c)` and restricting it to the unit disc, where `ν`
is the coefficient of the rescaled structure, gives the chart of `J`.

## Main results

* `TauCeti.Beltrami.exists_isothermalChart_of_contDiffAt`: a `C¹` structure tame at `c` has a
  `C¹` chart at `c`, with `C¹` inverse, in which it is the standard structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E.
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
-/

public noncomputable section

open Complex Filter Metric Set Topology
open scoped NNReal Manifold ContDiff BoundedContinuousFunction

namespace TauCeti.Beltrami

/-- **Rescaled cutoff.** Let `G` be `C`-Lipschitz with `G 0 = 0`, and let `χ` be `Lχ`-Lipschitz,
bounded by `1` and vanishing off `closedBall 0 R`. For `ε ≥ 0` and `α ≤ 1`, the function
`z ↦ χ z • G (ε • z)` is an `α`-Hölder function supported in `closedBall 0 R` with norm at most
`C ε (3 R + 1 + R Lχ)`. -/
private theorem exists_mem_supportedHolderSubmodule_cutoff {α : ℝ≥0} (hα : α ≤ 1) {R : ℝ}
    (hR : 0 ≤ R) {χ : ℂ → ℝ} {Lχ : ℝ≥0} (hχ : LipschitzWith Lχ χ) (hχ1 : ∀ z, |χ z| ≤ 1)
    (hχR : ∀ z ∉ closedBall (0 : ℂ) R, χ z = 0) {G : ℂ → ℂ} {C : ℝ≥0} (hG : LipschitzWith C G)
    (hG0 : G 0 = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ ν ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall (0 : ℂ) R),
      (∀ z, ν z = χ z • G (ε • z)) ∧ ‖ν‖ ≤ C * ε * (3 * R + 1 + R * Lχ) := by
  set f : ℂ → ℂ := fun z ↦ χ z • G (ε • z)
  have hGb : ∀ y ∈ closedBall (0 : ℂ) R, ‖G (ε • y)‖ ≤ C * ε * R := fun y hy ↦ by
    have h := hG.norm_sub_le (ε • y) 0
    rw [hG0, sub_zero, sub_zero, norm_smul, Real.norm_of_nonneg hε] at h
    rw [mem_closedBall_zero_iff] at hy
    calc ‖G (ε • y)‖ ≤ C * (ε * ‖y‖) := h
      _ ≤ C * (ε * R) := by gcongr
      _ = C * ε * R := by ring
  have hzero : ∀ z ∉ closedBall (0 : ℂ) R, f z = 0 := fun z hz ↦ by simp [f, hχR z hz]
  -- The sup bound `‖f z‖ ≤ C ε R`.
  have hM : ∀ z, ‖f z‖ ≤ C * ε * R := fun z ↦ by
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · rw [norm_smul, Real.norm_eq_abs]
      calc |χ z| * ‖G (ε • z)‖ ≤ 1 * (C * ε * R) := by
            gcongr
            · exact hχ1 z
            · exact hGb z hz
        _ = C * ε * R := one_mul _
    · rw [hzero z hz, norm_zero]
      positivity
  -- The Lipschitz bound, first when one of the points lies in the disc.
  set K : ℝ := C * ε * (1 + R * Lχ)
  have hK0 : 0 ≤ K := by positivity
  have hlip₁ : ∀ x, ∀ y ∈ closedBall (0 : ℂ) R, dist (f x) (f y) ≤ K * dist x y := by
    intro x y hy
    have hsplit : f x - f y = χ x • (G (ε • x) - G (ε • y)) + (χ x - χ y) • G (ε • y) := by
      simp only [f, smul_sub, sub_smul]
      abel
    have h1 : ‖G (ε • x) - G (ε • y)‖ ≤ C * ε * ‖x - y‖ := by
      refine (hG.norm_sub_le _ _).trans_eq ?_
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hε, mul_assoc]
    have h2 : |χ x - χ y| ≤ Lχ * ‖x - y‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hχ.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm, hsplit]
    calc ‖χ x • (G (ε • x) - G (ε • y)) + (χ x - χ y) • G (ε • y)‖
        ≤ |χ x| * ‖G (ε • x) - G (ε • y)‖ + |χ x - χ y| * ‖G (ε • y)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * (C * ε * ‖x - y‖) + (Lχ * ‖x - y‖) * (C * ε * R) := by
          gcongr
          · exact hχ1 x
          · exact hGb y hy
      _ = K * ‖x - y‖ := by ring
  have hlip : LipschitzWith K.toNNReal f := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.coe_toNNReal _ hK0]
    by_cases hy : y ∈ closedBall (0 : ℂ) R
    · exact hlip₁ x y hy
    by_cases hx : x ∈ closedBall (0 : ℂ) R
    · rw [dist_comm, dist_comm x]
      exact hlip₁ y x hx
    · rw [hzero x hx, hzero y hy, dist_self]
      positivity
  set M : ℝ≥0 := (C * ε * R : ℝ).toNNReal
  have hM' : ∀ z, ‖f z‖ ≤ M := fun z ↦ by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hM z
  have hhol : HolderWith (K.toNNReal + 2 * M) α f :=
    holderOnWith_univ.mp ((hlip.lipschitzOnWith (s := univ)).holderOnWith_of_norm_le
      (fun z _ ↦ hM' z) hα)
  let fb : ℂ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup f hlip.continuous M hM'
  obtain ⟨ν, hν⟩ : ∃ ν : HolderSpace α ℂ ℂ, ⇑ν = f :=
    ⟨HolderSpace.ofBoundedContinuousFunction fb ⟨_, hhol⟩, funext fun z ↦
      (HolderSpace.ofBoundedContinuousFunction_apply fb _ z).trans rfl⟩
  refine ⟨ν, mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ by rw [hν, hzero z hz],
    fun z ↦ by rw [hν], ?_⟩
  refine (HolderSpace.norm_le_of_norm_le_of_holderWith M.coe_nonneg
    (fun z ↦ by rw [hν]; exact hM' z)
    (hν ▸ hhol)).trans_eq ?_
  push_cast
  rw [Real.coe_toNNReal _ hK0, Real.coe_toNNReal _ (by positivity)]
  ring

/-- **Planar isothermal charts.** Let `J` be a field of almost complex structures on the plane,
tame at `c`, with `z ↦ J z` of class `C¹` at `c` in the operator norm. Then there is an open
partial homeomorphism `e` of the plane with `c` in its source and `e c = 0`, of class `C¹` on its
source with `C¹` inverse on its target, whose real differential carries `J z` to multiplication by
`i` at every point `z` of its source. No smallness of the Beltrami coefficient of `J` is
assumed. -/
theorem exists_isothermalChart_of_contDiffAt {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : stdComplexSymplecticForm.Tames (J c))
    (hJs : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e c = 0 ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧ (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, IsComplexLinear (J z).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e z).toLinearMap := by
  set J₀ := AlmostComplexStructure.ofComplexModule ℂ
  /- Step 1: normalize at `c`. Read `J` through `w ↦ A (w - c)`, where `A` carries `J c` to the
  standard structure; the coefficient `μ₁` of the new field `J₁` vanishes at `0`. -/
  have hna : Complex.normSq (coefficientEquiv ⟨J c, hJ⟩).val ≠ 1 := by
    simpa only [Complex.UnitDisc.coe_mk] using
      (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk _
        (coefficientEquiv ⟨J c, hJ⟩).property)).ne
  set A := linearEquiv (coefficientEquiv ⟨J c, hJ⟩).val hna
  let J₁ : ℂ → AlmostComplexStructure ℂ := fun w ↦
    (J (c + A.symm w)).transport A.toLinearEquiv
  have hJ₁ : ∀ w v, J₁ w (A v) = A (J (c + A.symm w) v) := fun w v ↦ by
    simp [J₁, AlmostComplexStructure.transport_toLinearMap, LinearEquiv.conj_apply]
  have hJ₁0 : J₁ 0 = J₀ := by
    simp only [J₁, map_zero, add_zero]
    exact transport_linearEquiv_eq_std (J c) hJ
  have hJ₁s : ContDiffAt ℝ 1 (fun w ↦ LinearMap.toContinuousLinearMap (J₁ w).toLinearMap) 0 := by
    have hcl : (fun w ↦ LinearMap.toContinuousLinearMap (J₁ w).toLinearMap) = fun w ↦
        (A : ℂ →L[ℝ] ℂ) ∘L LinearMap.toContinuousLinearMap (J (c + A.symm w)).toLinearMap ∘L
          (A.symm : ℂ →L[ℝ] ℂ) := by
      funext w
      ext v
      rw [← A.apply_symm_apply v]
      simp only [LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      exact hJ₁ w _
    rw [hcl]
    have hin : ContDiffAt ℝ 1 (fun w : ℂ ↦ c + A.symm w) 0 :=
      contDiffAt_const.add A.symm.contDiff.contDiffAt
    have hJs' : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
        (c + A.symm 0) := by
      simpa using hJs
    have hJc : ContDiffAt ℝ 1
        (fun w ↦ LinearMap.toContinuousLinearMap (J (c + A.symm w)).toLinearMap) 0 :=
      ContDiffAt.comp (g := fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
        (f := fun w ↦ c + A.symm w) (0 : ℂ) hJs' hin
    exact contDiffAt_const.clm_comp (hJc.clm_comp contDiffAt_const)
  have htame₀ : stdComplexSymplecticForm.Tames (J₁ 0) := hJ₁0 ▸ stdComplexSymplecticForm_tames
  let μ₁ : ℂ → ℂ := fun w ↦ J₀.cayley (J₁ w) 1
  have hμ₁0 : μ₁ 0 = 0 := by simp [μ₁, hJ₁0]
  have hμ₁s : ContDiffAt ℝ 1 μ₁ 0 := by
    have h := stdComplexSymplecticForm_tames.contMDiffAt_cayley (I := 𝓘(ℝ, ℂ)) htame₀
      (contMDiffAt_iff_contDiffAt.2 hJ₁s)
    exact contMDiffAt_iff_contDiffAt.1 (h.clm_apply contMDiffAt_const)
  obtain ⟨ρ, hρ, hρ'⟩ : ∃ ρ > 0, ∀ w ∈ ball (0 : ℂ) ρ,
      ContDiffAt ℝ 1 μ₁ w ∧ stdComplexSymplecticForm.Tames (J₁ w) :=
    Metric.eventually_nhds_iff_ball.1 ((hμ₁s.eventually (by simp)).and
      (SymplecticForm.Tames.eventually_of_continuousAt hJ₁s.continuousAt htame₀))
  /- Step 2: cut `μ₁` off at scale `ρ`, to a compactly supported `C¹`, hence Lipschitz,
  function `G` equal to `μ₁` near `0`. -/
  let χ₀ : ContDiffBump (0 : ℂ) := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  let G : ℂ → ℂ := fun w ↦ χ₀ w • μ₁ w
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) ρ
    · exact χ₀.contDiff.contDiffAt.smul (hρ' w hw).1
    · have hws : w ∉ tsupport χ₀ := by
        rw [χ₀.tsupport_eq, mem_closedBall_zero_iff]
        rw [mem_ball_zero_iff, not_lt] at hw
        intro h
        have : ρ ≤ ρ / 2 := hw.trans h
        linarith
      refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ ↦ (0 : ℂ)) ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hws] with y hy
      simp [G, hy]
  obtain ⟨CG, hCG⟩ := hG.lipschitzWith_of_hasCompactSupport χ₀.hasCompactSupport.smul_right
    one_ne_zero
  have hG0 : G 0 = 0 := by simp [G, hμ₁0]
  have hGμ : ∀ w ∈ ball (0 : ℂ) (ρ / 4), G w = μ₁ w := fun w hw ↦ by
    simp [G, χ₀.one_of_mem_closedBall (ball_subset_closedBall hw)]
  /- Step 3: the planar Beltrami chart on the disc of radius `2`, applied to the rescaled cutoff
  coefficient `ν(z) = χ(z) G(ε z)` for `ε` small. -/
  obtain ⟨δ, hδ, Cb, hchart⟩ := exists_isComplexLinear_chart (α := 1 / 2) (by norm_num)
    (by norm_num) 0 (r := 2) two_pos
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨Lχ, hLχ⟩ := (χ.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport χ.hasCompactSupport
    one_ne_zero
  set K : ℝ := CG * (3 * 2 + 1 + 2 * Lχ)
  set η : ℝ := min δ (min 1 ((Cb : ℝ) + 1)⁻¹)
  have hη : 0 < η := lt_min hδ (lt_min one_pos (by positivity))
  set ε : ℝ := min (ρ / 8) (η / (K + 1))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hερ : ε < ρ / 4 := (min_le_left _ _).trans_lt (by linarith)
  have hεK : K * ε < η := by
    calc K * ε ≤ K * (η / (K + 1)) := by gcongr; exact min_le_right _ _
      _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  obtain ⟨ν, hνmem, hνapp, hνnorm⟩ := exists_mem_supportedHolderSubmodule_cutoff
    (α := 1 / 2) (by norm_num) (R := 2) zero_le_two hLχ
    (fun z ↦ by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one)
    (fun z hz ↦ χ.zero_of_le_dist (by
      rw [mem_closedBall, not_le] at hz
      exact hz.le)) (G := G) hCG hG0 hε.le
  have hνη : ‖ν‖ < η := hνnorm.trans_lt (by linarith [hεK])
  have hν1 : ∀ z, ‖ν z‖ < 1 := fun z ↦
    (HolderSpace.norm_apply_le _ z).trans_lt
      (hνη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hCbν : Cb * ‖ν‖ < 1 := by
    have h1 : ‖ν‖ ≤ ((Cb : ℝ) + 1)⁻¹ := hνη.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc (Cb : ℝ) * ‖ν‖ ≤ Cb * ((Cb : ℝ) + 1)⁻¹ := by gcongr
      _ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one (by positivity)]
        linarith
  let J'' : ℂ → AlmostComplexStructure ℂ := fun z ↦ (coefficientEquiv.symm ⟨ν z, hν1 z⟩).val
  have hJ''t : ∀ z, stdComplexSymplecticForm.Tames (J'' z) := fun z ↦
    (coefficientEquiv.symm _).property
  have hJ''μ : ∀ z, ν z = (coefficientEquiv ⟨J'' z, hJ''t z⟩).val := fun z ↦ by
    simp [J'']
  obtain ⟨h, -, -, hψC1, -, hnear, -, -, ha, hφC1, hφ0, -, hφlin, e, he, hce, hesub⟩ :=
    hchart J'' (fun z _ ↦ hJ''t z) ν hνmem (fun z _ ↦ hJ''μ z)
      (hνη.trans_le (min_le_left _ _))
  set ψ := cauchySolution h
  set φ := normalizedChart ψ 0
  -- On the unit disc, `J''` is the rescaled normalized structure.
  have hJ''J₁ : ∀ z ∈ ball (0 : ℂ) 1, J'' z = J₁ (ε • z) := by
    intro z hz
    have hεz : ε • z ∈ ball (0 : ℂ) (ρ / 4) := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.le]
      rw [mem_ball_zero_iff] at hz
      calc ε * ‖z‖ < ε * 1 := by gcongr
        _ < ρ / 4 := by linarith
    have hT := (hρ' _ (ball_subset_ball (by linarith) hεz)).2
    have hν' : ν z = μ₁ (ε • z) := by
      rw [hνapp, χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul, hGμ _ hεz]
    have hc : coefficientEquiv ⟨J₁ (ε • z), hT⟩ = ⟨ν z, hν1 z⟩ :=
      Subtype.ext (by rw [coefficientEquiv_apply]; exact hν'.symm)
    simp only [J'', ← hc, Equiv.symm_apply_apply]
  /- Step 4: on the disc, `dψ` is within `Cb ‖ν‖ < 1` of the identity, so `dφ` is invertible. -/
  have hsub2 : closedBall (0 : ℂ) 2 ⊆ ball 0 (2 + 1) := closedBall_subset_ball (by norm_num)
  have hφd : ∀ z ∈ closedBall (0 : ℂ) 2, ContDiffAt ℝ 1 φ z := fun z hz ↦
    hφC1.contDiffAt (isOpen_ball.mem_nhds (hsub2 hz))
  have hinv : ∀ z ∈ closedBall (0 : ℂ) 2, ∃ L : ℂ ≃L[ℝ] ℂ, HasFDerivAt φ (L : ℂ →L[ℝ] ℂ) z := by
    intro z hz
    have hψd : DifferentiableAt ℝ ψ z :=
      (hψC1.contDiffAt (isOpen_ball.mem_nhds (hsub2 hz))).differentiableAt one_ne_zero
    obtain ⟨L, hL⟩ := ContinuousLinearMap.isInvertible_of_norm_sub_lt
      (ContinuousLinearEquiv.refl ℝ ℂ) (A := fderiv ℝ ψ z) (by
        rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
          ContinuousLinearMap.nnnorm_id, inv_one, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
        exact (hnear z hz).trans_lt hCbν)
    set a := wirtingerDeriv ψ 0 1
    let M : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))
    refine ⟨L.trans M, ?_⟩
    have hLM : ((L.trans M : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = a⁻¹ • fderiv ℝ ψ z := by
      ext v
      simp [M, Units.smul_def, ← hL]
    rw [hLM]
    exact hasFDerivAt_normalizedChart hψd.hasFDerivAt
  /- Step 5: restrict the chart to the unit disc and compose with `w ↦ ε⁻¹ A (w - c)`. -/
  let e₁ := e.restrOpen (ball (0 : ℂ) 1) isOpen_ball
  have he₁ : ⇑e₁ = φ := by rw [OpenPartialHomeomorph.coe_restrOpen, he]
  have he₁s : e₁.source ⊆ ball (0 : ℂ) 1 ∩ closedBall 0 2 := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun z hz ↦ ⟨hz.2, ball_subset_closedBall (hesub hz.1)⟩
  let B : ℂ ≃L[ℝ] ℂ := A.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne')))
  have hB : ∀ v, B v = ε⁻¹ • A v := fun v ↦ by simp [B, Units.smul_def]
  let S : OpenPartialHomeomorph ℂ ℂ :=
    ((Homeomorph.subRight c).trans B.toHomeomorph).toOpenPartialHomeomorph
  have hS : ∀ w, S w = B (w - c) := fun _ ↦ rfl
  have hSs : ∀ z, S.symm z = B.symm z + c := fun _ ↦ rfl
  have hSf : ⇑S = fun w ↦ B (w - c) := funext hS
  have hSd : ∀ w, HasFDerivAt S (B : ℂ →L[ℝ] ℂ) w := fun w ↦ by
    rw [hSf]
    exact B.hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const c)
  have hSc : ContDiff ℝ 1 S := by
    rw [hSf]
    exact B.contDiff.comp (contDiff_id.sub contDiff_const)
  have hSsc : ContDiff ℝ 1 S.symm := by
    have : ⇑S.symm = fun z ↦ B.symm z + c := funext hSs
    rw [this]
    exact B.symm.contDiff.add contDiff_const
  refine ⟨S.trans e₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_univ c, ?_⟩
    rw [mem_preimage, hS, sub_self, map_zero, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hce, mem_ball_self one_pos⟩
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hS, sub_self, map_zero, he₁]
    exact normalizedChart_self ψ 0
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    rw [OpenPartialHomeomorph.coe_trans, he₁]
    exact (hφd _ (he₁s hz.2).2).comp z hSc.contDiffAt
  · intro z hz
    rw [OpenPartialHomeomorph.trans_target] at hz
    have hz' : e₁.symm z ∈ e₁.source := e₁.map_target hz.1
    obtain ⟨L, hL⟩ := hinv _ (he₁s hz').2
    have hsymm : ContDiffAt ℝ 1 e₁.symm z :=
      e₁.contDiffAt_symm hz.1 (by rw [he₁]; exact hL) (by rw [he₁]; exact hφd _ (he₁s hz').2)
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans]
    exact hSsc.contDiffAt.comp z hsymm
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hSz := he₁s hz.2
    have hd : HasFDerivAt (S.trans e₁) ((fderiv ℝ φ (S z)).comp (B : ℂ →L[ℝ] ℂ)) z := by
      rw [OpenPartialHomeomorph.coe_trans, he₁]
      exact ((hφd _ hSz.2).differentiableAt one_ne_zero).hasFDerivAt.comp z (hSd z)
    rw [hd.fderiv]
    -- `B` carries `J z` to `J'' (S z)`.
    have hBJ : ∀ v, B (J z v) = J'' (S z) (B v) := fun v ↦ by
      have hεS : ε • S z = A (z - c) := by
        rw [hS, hB, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
      have hzc : c + A.symm (A (z - c)) = z := by
        rw [ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel]
      rw [hJ''J₁ _ hSz.1, hεS, hB, hB, map_smul, hJ₁, hzc]
    refine isComplexLinear_of_apply fun v ↦ ?_
    have := (hφlin (S z) hSz.2).apply (B v)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [hBJ]
    exact this

end TauCeti.Beltrami
