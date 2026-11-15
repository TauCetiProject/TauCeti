/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
public import TauCeti.Geometry.Symplectic.Floer.Pregluing
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# The semi-Fredholm estimate of the linearized Floer operator on a cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H_t` a Hamiltonian, `J_t(y)` a
`C¹` family of almost complex structures and `u : ℝ × ℝ → V` a `C¹` map whose loops converge
uniformly to orbits `x₋` as `s → -∞` and `x₊` as `s → +∞`, with slice defect
`∂t u - X_{H_t}(u)` tending to zero, as for a Floer cylinder between the two orbits. The
linearized Floer operator of the cylindrical datum `K = H_t dt` along `u` is

`D_u ξ = ∂s ξ + J_t(u) (∂t ξ - dX_{H_t}(u) ξ) + (dJ_t(u) ξ) (∂t u - X_{H_t}(u))`

(`TauCeti.SymplecticForm.floerLinearization`). This file proves its semi-Fredholm estimate: if
`x₋(0)` and `x₊(0)` are nondegenerate fixed points of the time-one map and the structures are
`ω`-compatible along `u`, `x₋` and `x₊`, there are constants `C` and `T` such that

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every `C²` map `ξ` of period one in `t` and with support in a slab `[a, b] × ℝ`, both
integrals on the left and the first on the right being over `[a, b] × [0, 1]`
(`SymplecticForm.exists_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization_add`).
The constants depend neither on `ξ` nor on the slab. This is the a priori estimate behind the
Fredholm property of `D_u`: on the Sobolev completion `W^{1,2}` of such maps, the restriction to
`L²([-T, T] × S¹)` is compact, and an estimate of this form then gives a finite-dimensional
kernel and a closed range (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
`ContinuousLinearMap.isClosed_range_of_compact_estimate`). The Sobolev completion is not treated
here.

The estimate patches two estimates already available.

* **On the ends.** At a nondegenerate orbit, `D_u` is bounded below on the far part of each end
  (`TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`),
  in the metrics `g_t = ω(·, J_t(x(t)) ·)` and with `∂t ξ - S_t ξ` in place of `∂t ξ`. Since the
  metrics are uniformly equivalent to the norm and `S_t` is bounded, this gives the same estimate
  in the norm
  (`SymplecticForm.exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization`).
* **On the compact part.** The `L²` estimate of the derivatives on `[-T, T] × [0, 1]`
  (`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic`).

They are joined by cutting `ξ` off in `s`, with the pre-gluing cutoff
`TauCeti.Floer.pregluingCutoff`. For a cutoff `β(s)`, the operator satisfies the Leibniz rule
`D_u(β ξ) = β D_u ξ + β' ξ` (`TauCeti.SymplecticForm.floerLinearization_comp_fst_smul`), and the
error terms `β' ξ` are supported in `[-T, T] × ℝ`, where they are controlled by the last term of
the estimate.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of the linearized operator along a
  Floer trajectory between nondegenerate orbits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B.
-/

public section

open Filter MeasureTheory Set Topology ContinuousLinearMap
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The squared norm of `D_u(β ξ)` is at most `2 ‖D_u ξ‖² + 2 β'² ‖ξ‖²` where `|β| ≤ 1`. -/
private theorem norm_floerLinearization_comp_fst_smul_sq_le (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    {β : ℝ → ℝ} (hβ : DifferentiableAt ℝ β z.1) (hβ₁ : |β z.1| ≤ 1)
    (hξ : DifferentiableAt ℝ ξ z) :
    ‖ω.floerLinearization J Ks Kt u (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
      2 * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 + 2 * (deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2) := by
  rw [floerLinearization_comp_fst_smul ω J Ks Kt u ξ hβ hξ]
  set D := ω.floerLinearization J Ks Kt u ξ z
  have h₁ : ‖β z.1 • D‖ ≤ ‖D‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hβ₁
  have h₂ : ‖deriv β z.1 • ξ z‖ ^ 2 = deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc _ ≤ 2 * (‖β z.1 • D‖ ^ 2 + ‖deriv β z.1 • ξ z‖ ^ 2) :=
        (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
    _ ≤ _ := by
        rw [h₂, mul_add]
        gcongr

/-! ### Patching the end and interior estimates -/

/-- An integral over `[a, b] × [0, 1]` of a function vanishing off `([a, b] ∩ [c, d]) × ℝ` is
the integral over `[c, d] × [0, 1]`. -/
private theorem setIntegral_Icc_prod_eq {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (h : ∀ z : ℝ × ℝ, z.1 ∉ Icc a b ∩ Icc c d → f z = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, f z = ∫ z in Icc c d ×ˢ Icc (0 : ℝ) 1, f z :=
  setIntegral_eq_setIntegral_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
    (measurableSet_Icc.prod measurableSet_Icc) (fun z hz ↦ h z fun h' ↦ hz.2 ⟨h'.2, hz.1.2⟩)
    fun z hz ↦ h z fun h' ↦ hz.2 ⟨h'.1, hz.1.2⟩

/-- The linearized operator of the cylindrical datum `K = H_t dt` along a `C¹` map, applied to a
`C¹` direction, is continuous. -/
private theorem continuous_floerLinearization_cylindrical (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {u ξ : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 1 ξ) :
    Continuous (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ) :=
  continuous_iff_continuousAt.2 fun _ ↦ ω.continuousAt_floerLinearization
    (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
    contDiffAt_const (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt hu.contDiffAt
    hξ.contDiffAt

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The error term of a cutoff: if `|β'| ≤ M`, `β' = 0` off `[-T, T]` and `ξ = 0` off
`[a, b] × ℝ`, then `∫ β'(s)² ‖ξ‖²` over `[a, b] × [0, 1]` is at most `M² ∫ ‖ξ‖²` over
`[-T, T] × [0, 1]`. -/
private theorem setIntegral_deriv_sq_mul_norm_sq_le {ξ : ℝ × ℝ → V} (hξ : Continuous ξ)
    {β : ℝ → ℝ} (hβ : Continuous (deriv β)) {M T : ℝ} (hβM : ∀ s, |deriv β s| ≤ M)
    (hβT : ∀ s, T < |s| → deriv β s = 0) {a b : ℝ} (hξab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc 0 1, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 ≤
      M ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  have hW : IsCompact (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  rw [setIntegral_Icc_prod_eq (c := -T) (d := T) fun z hz ↦ ?_, ← integral_const_mul]
  · refine setIntegral_mono_on ((((hβ.comp continuous_fst).pow 2).mul
      (hξ.norm.pow 2)).continuousOn.integrableOn_compact hW)
      (((hξ.norm.pow 2).continuousOn.integrableOn_compact hW).const_mul _) hW.measurableSet
      fun z _ ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hβM _) 2
  · by_cases hab : z.1 ∈ Icc a b
    · have hz' : T < |z.1| := by
        by_contra h'
        exact hz ⟨hab, abs_le.1 (not_lt.1 h')⟩
      simp [hβT _ hz']
    · have h₀ : ξ z = 0 := hξab z.1 hab z.2
      simp [h₀]

/-- **One cut-off piece.** Let `η = β(s) ξ` with `|β| ≤ 1`, `|β'| ≤ M` and `β' = 0` off
`[-T, T]`, where `ξ` vanishes off `[a, b] × ℝ`. If `η` vanishes near every point off
`([a, b] ∩ [c, d]) × ℝ` and satisfies an estimate `∫ N(η) ≤ C ∫ ‖D_u η‖² + E` over the window
`[c, d] × [0, 1]`, then over `[a, b] × [0, 1]`, `∫ N(η)` is at most
`C (2 ∫ ‖D_u ξ‖² + 2 M² ∫_{[-T, T] × [0, 1]} ‖ξ‖²) + E`, where
`N(η) = ‖∂s η‖² + ‖∂t η‖² + ‖η‖²`. -/
private theorem setIntegral_comp_fst_smul_le (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {u ξ : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ) {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {M T : ℝ}
    (hβ₁ : ∀ s, |β s| ≤ 1) (hβM : ∀ s, |deriv β s| ≤ M) (hβT : ∀ s, T < |s| → deriv β s = 0)
    {a b c d : ℝ} (hξab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0)
    (hη : ∀ z : ℝ × ℝ, z.1 ∉ Icc a b ∩ Icc c d → (fun w ↦ β w.1 • ξ w) =ᶠ[𝓝 z] 0)
    {C E : ℝ} (hC : 0 ≤ C)
    (hwin : ∫ z in Icc c d ×ˢ Icc 0 1,
        (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) ≤
      C * (∫ z in Icc c d ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) u (fun w ↦ β w.1 • ξ w) z‖ ^ 2) + E) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) ≤
      C * (2 * (∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
          (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) u ξ z‖ ^ 2) +
        2 * M ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) + E := by
  set D := ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ H w.2) u
  have hβd : Differentiable ℝ β := hβ.differentiable two_ne_zero
  have hξd : Differentiable ℝ ξ := hξ.differentiable two_ne_zero
  have hR : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hηc : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ β w.1 • ξ w :=
    ((hβ.comp contDiff_fst).smul hξ).of_le one_le_two
  have hDξ := continuous_floerLinearization_cylindrical ω hJ hH hu (hξ.of_le one_le_two)
  have hDη := continuous_floerLinearization_cylindrical ω hJ hH hu hηc
  -- The integrands vanish where `η` vanishes locally.
  have hN : ∫ z in Icc a b ×ˢ Icc 0 1,
      (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) =
      ∫ z in Icc c d ×ˢ Icc 0 1,
      (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) :=
    setIntegral_Icc_prod_eq fun z hz ↦ by
      have h := hη z hz
      have h₀ : β z.1 • ξ z = 0 := h.eq_of_nhds
      simp [h.fderiv_eq, h₀]
  have hD : ∫ z in Icc c d ×ˢ Icc 0 1, ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2 =
      ∫ z in Icc a b ×ˢ Icc 0 1, ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2 :=
    (setIntegral_Icc_prod_eq fun z hz ↦ by
      have h₀ : D (fun w ↦ β w.1 • ξ w) z = 0 :=
        (floerLinearization_congr_of_eventuallyEq ω _ _ _ u (hη z (by rwa [inter_comm]))).trans
          (floerLinearization_zero ω _ _ _ u z)
      rw [h₀, norm_zero, zero_pow two_ne_zero])
  -- The error term `β' ξ` lives on `[-T, T] × ℝ`.
  have hT := setIntegral_deriv_sq_mul_norm_sq_le hξ.continuous (hβ.continuous_deriv one_le_two)
    hβM hβT hξab
  calc _ ≤ C * (∫ z in Icc a b ×ˢ Icc 0 1, ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2) + E := by
        rw [hN]
        exact hwin.trans_eq (by rw [hD])
    _ ≤ C * (∫ z in Icc a b ×ˢ Icc 0 1,
          (2 * ‖D ξ z‖ ^ 2 + 2 * (deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2))) + E := by
        refine (add_le_add_iff_right E).2 (mul_le_mul_of_nonneg_left ?_ hC)
        refine setIntegral_mono_on ((hDη.norm.pow 2).continuousOn.integrableOn_compact hR) ?_
          hR.measurableSet fun z _ ↦
            norm_floerLinearization_comp_fst_smul_sq_le ω _ _ _ u ξ (hβd _) (hβ₁ _) (hξd z)
        exact (((hDξ.norm.pow 2).const_smul (2 : ℝ)).add
          ((((hβ.continuous_deriv one_le_two).comp continuous_fst).pow 2).mul
            (hξ.continuous.norm.pow 2) |>.const_smul (2 : ℝ))).continuousOn.integrableOn_compact hR
    _ ≤ _ := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact (add_le_add_iff_right E).2 (mul_le_mul_of_nonneg_left (by linarith) hC)
        · exact ((hDξ.norm.pow 2).continuousOn.integrableOn_compact hR).const_mul _
        · exact (((((hβ.continuous_deriv one_le_two).comp continuous_fst).pow 2).mul
            (hξ.continuous.norm.pow 2)).continuousOn.integrableOn_compact hR).const_mul _

/-! ### The cutoffs -/

/-- The end cutoff `s ↦ ρ(σ s + T - 1)` for the pre-gluing cutoff `ρ`. For `σ = -1` it is `0` on
`(-∞, T - 2]` and `1` on `[T, ∞)`; for `σ = 1` it is `1` on `(-∞, -T]` and `0` on `[2 - T, ∞)`. -/
private noncomputable def endCutoff (σ T s : ℝ) : ℝ :=
  Floer.pregluingCutoff (σ * s + (T - 1))

/-- The middle cutoff `1 - ρ(-s + T - 1) - ρ(s + T - 1)`, which vanishes off `[-T, T]`. -/
private noncomputable def middleCutoff (T s : ℝ) : ℝ :=
  1 - endCutoff (-1) T s - endCutoff 1 T s

private theorem contDiff_endCutoff (σ T : ℝ) : ContDiff ℝ 2 (endCutoff σ T) :=
  Floer.contDiff_pregluingCutoff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

private theorem abs_endCutoff_le (σ T s : ℝ) : |endCutoff σ T s| ≤ 1 := by
  rw [endCutoff, abs_of_nonneg (Floer.pregluingCutoff_nonneg _)]
  exact Floer.pregluingCutoff_le_one _

private theorem deriv_endCutoff (σ T s : ℝ) :
    deriv (endCutoff σ T) s = σ * deriv Floer.pregluingCutoff (σ * s + (T - 1)) := by
  have h := ((Floer.contDiff_pregluingCutoff (n := 1)).differentiable one_ne_zero
    (σ * s + (T - 1))).hasDerivAt.comp s (((hasDerivAt_id s).const_mul σ).add_const (T - 1))
  rw [show endCutoff σ T = Floer.pregluingCutoff ∘ fun s ↦ σ * id s + (T - 1) from rfl, h.deriv]
  ring

/-- The derivative of an end cutoff with `|σ| = 1` is bounded by any bound of `ρ'`. -/
private theorem abs_deriv_endCutoff_le {σ B : ℝ} (hσ : |σ| = 1)
    (hB : ∀ s, |deriv Floer.pregluingCutoff s| ≤ B) (T s : ℝ) :
    |deriv (endCutoff σ T) s| ≤ B := by
  rw [deriv_endCutoff, abs_mul, hσ, one_mul]
  exact hB _

/-- For `T ≥ 2` and `|σ| = 1`, the end cutoff is locally constant off `[-T, T]`. -/
private theorem deriv_endCutoff_eq_zero {σ T s : ℝ} (hσ : |σ| = 1) (hT : 2 ≤ T)
    (hs : T < |s|) : deriv (endCutoff σ T) s = 0 := by
  have hσs : T < |σ * s| := by rwa [abs_mul, hσ, one_mul]
  rw [deriv_endCutoff, Floer.deriv_pregluingCutoff_of_one_lt_abs, mul_zero]
  rcases lt_abs.1 hσs with h | h
  · exact lt_abs.2 (Or.inl (by linarith))
  · exact lt_abs.2 (Or.inr (by linarith))

private theorem endCutoff_eq_zero {σ T s : ℝ} (h : 1 ≤ σ * s + (T - 1)) :
    endCutoff σ T s = 0 :=
  Floer.pregluingCutoff_of_one_le h

private theorem contDiff_middleCutoff (T : ℝ) : ContDiff ℝ 2 (middleCutoff T) :=
  (contDiff_const.sub (contDiff_endCutoff _ _)).sub (contDiff_endCutoff _ _)

/-- For `T ≥ 2` the supports of the two end cutoffs are disjoint, so `0 ≤ middleCutoff T ≤ 1`. -/
private theorem abs_middleCutoff_le {T : ℝ} (hT : 2 ≤ T) (s : ℝ) : |middleCutoff T s| ≤ 1 := by
  have hp := Floer.pregluingCutoff_nonneg (-1 * s + (T - 1))
  have hp' := Floer.pregluingCutoff_le_one (-1 * s + (T - 1))
  have hm := Floer.pregluingCutoff_nonneg (1 * s + (T - 1))
  have hm' := Floer.pregluingCutoff_le_one (1 * s + (T - 1))
  rw [middleCutoff, endCutoff, endCutoff]
  rcases le_total 0 s with hs | hs
  · rw [Floer.pregluingCutoff_of_one_le (s := 1 * s + (T - 1)) (by linarith)]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [Floer.pregluingCutoff_of_one_le (s := -1 * s + (T - 1)) (by linarith)]
    exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem abs_deriv_middleCutoff_le {B : ℝ}
    (hB : ∀ s, |deriv Floer.pregluingCutoff s| ≤ B) (T s : ℝ) :
    |deriv (middleCutoff T) s| ≤ 2 * B := by
  have hd (σ : ℝ) : DifferentiableAt ℝ (endCutoff σ T) s :=
    (contDiff_endCutoff σ T).differentiable two_ne_zero s
  have h : deriv (middleCutoff T) s = -deriv (endCutoff (-1) T) s - deriv (endCutoff 1 T) s :=
    (((hd (-1)).hasDerivAt.const_sub 1).sub (hd 1).hasDerivAt).deriv
  rw [h]
  have hp := abs_deriv_endCutoff_le (σ := -1) (by norm_num) hB T s
  have hm := abs_deriv_endCutoff_le (σ := 1) (by norm_num) hB T s
  calc _ ≤ |-deriv (endCutoff (-1) T) s| + |deriv (endCutoff 1 T) s| := abs_sub _ _
    _ ≤ 2 * B := by rw [abs_neg]; linarith

/-- For `T ≥ 2` the middle cutoff vanishes at every `s` with `|s| ≥ T`. -/
private theorem middleCutoff_eq_zero {T s : ℝ} (hT : 2 ≤ T) (hs : T ≤ |s|) :
    middleCutoff T s = 0 := by
  rw [middleCutoff, endCutoff, endCutoff]
  rcases le_abs'.1 hs with h | h
  · rw [Floer.pregluingCutoff_of_one_le (by linarith),
      Floer.pregluingCutoff_of_le_neg_one (by linarith)]
    ring
  · rw [Floer.pregluingCutoff_of_le_neg_one (by linarith),
      Floer.pregluingCutoff_of_one_le (by linarith)]
    ring

/-- For `T ≥ 2` the middle cutoff vanishes near every `s` with `|s| > T`. -/
private theorem middleCutoff_eventuallyEq_zero {T s : ℝ} (hT : 2 ≤ T) (hs : T < |s|) :
    middleCutoff T =ᶠ[𝓝 s] 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
    (show s ∈ {s' : ℝ | T < |s'|} from hs)] with s' hs'
  exact middleCutoff_eq_zero hT (le_of_lt hs')

omit [FiniteDimensional ℝ V] in
/-- Splitting `ξ = ξ₁ + ξ₂ + ξ₃`: the integral of `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` over a compact set
is at most three times the sum of the integrals of the same expressions for the pieces. -/
private theorem setIntegral_add_add_le {ξ₁ ξ₂ ξ₃ : ℝ × ℝ → V} (h₁ : ContDiff ℝ 1 ξ₁)
    (h₂ : ContDiff ℝ 1 ξ₂) (h₃ : ContDiff ℝ 1 ξ₃) {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    ∫ z in S, (‖fderiv ℝ (ξ₁ + ξ₂ + ξ₃) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ₁ + ξ₂ + ξ₃) z stdComplexLineImag‖ ^ 2 + ‖(ξ₁ + ξ₂ + ξ₃) z‖ ^ 2) ≤
      3 * ((∫ z in S, (‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2 + ‖ξ₁ z‖ ^ 2)) +
        (∫ z in S, (‖fderiv ℝ ξ₂ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₂ z stdComplexLineImag‖ ^ 2 + ‖ξ₂ z‖ ^ 2)) +
        ∫ z in S, (‖fderiv ℝ ξ₃ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₃ z stdComplexLineImag‖ ^ 2 + ‖ξ₃ z‖ ^ 2)) := by
  have hc {f : ℝ × ℝ → V} (hf : ContDiff ℝ 1 f) : Continuous fun z ↦
      ‖fderiv ℝ f z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ f z stdComplexLineImag‖ ^ 2 +
        ‖f z‖ ^ 2 :=
    ((((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 2).add
      (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 2)).add
      (hf.continuous.norm.pow 2)
  have hi {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f S :=
    hf.continuousOn.integrableOn_compact hS
  -- `‖x + y + w‖² ≤ 3 (‖x‖² + ‖y‖² + ‖w‖²)`.
  have h3 (x y w : V) : ‖x + y + w‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖w‖ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_add₃_le (a := x) (b := y) (c := w)) 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖w‖), sq_nonneg (‖x‖ - ‖w‖)]
  calc _ ≤ ∫ z in S, 3 * ((‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2 + ‖ξ₁ z‖ ^ 2) +
        (‖fderiv ℝ ξ₂ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₂ z stdComplexLineImag‖ ^ 2 + ‖ξ₂ z‖ ^ 2) +
        (‖fderiv ℝ ξ₃ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₃ z stdComplexLineImag‖ ^ 2 + ‖ξ₃ z‖ ^ 2)) := by
        refine setIntegral_mono_on (hi (hc ((h₁.add h₂).add h₃))) ((hi (((hc h₁).add
          (hc h₂)).add (hc h₃))).const_mul 3) hS.measurableSet fun z _ ↦ ?_
        have hd {f : ℝ × ℝ → V} (hf : ContDiff ℝ 1 f) : DifferentiableAt ℝ f z :=
          hf.differentiable one_ne_zero z
        rw [fderiv_add ((hd h₁).add (hd h₂)) (hd h₃), fderiv_add (hd h₁) (hd h₂)]
        simp only [add_apply, Pi.add_apply]
        linarith [h3 (fderiv ℝ ξ₁ z stdComplexLineReal) (fderiv ℝ ξ₂ z stdComplexLineReal)
            (fderiv ℝ ξ₃ z stdComplexLineReal),
          h3 (fderiv ℝ ξ₁ z stdComplexLineImag) (fderiv ℝ ξ₂ z stdComplexLineImag)
            (fderiv ℝ ξ₃ z stdComplexLineImag), h3 (ξ₁ z) (ξ₂ z) (ξ₃ z)]
    _ = _ := by
        rw [integral_const_mul, integral_add, integral_add]
        exacts [hi (hc h₁), hi (hc h₂), (hi (hc h₁)).add (hi (hc h₂)), hi (hc h₃)]

omit [FiniteDimensional ℝ V] in
/-- Cutting `ξ` into the two end pieces and the middle piece: the integral of
`‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` is at most three times the sum of the integrals for the pieces. -/
private theorem setIntegral_le_three_mul_cutoff {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ)
    (T a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      3 * ((∫ z in Icc a b ×ˢ Icc 0 1,
          (‖fderiv ℝ (fun w ↦ endCutoff (-1) T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (fun w ↦ endCutoff (-1) T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
            ‖endCutoff (-1) T z.1 • ξ z‖ ^ 2)) +
        (∫ z in Icc a b ×ˢ Icc 0 1,
          (‖fderiv ℝ (fun w ↦ endCutoff 1 T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (fun w ↦ endCutoff 1 T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
            ‖endCutoff 1 T z.1 • ξ z‖ ^ 2)) +
        ∫ z in Icc a b ×ˢ Icc 0 1,
          (‖fderiv ℝ (fun w ↦ middleCutoff T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (fun w ↦ middleCutoff T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
            ‖middleCutoff T z.1 • ξ z‖ ^ 2)) := by
  have hcd {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ β w.1 • ξ w :=
    ((hβ.of_le one_le_two).comp contDiff_fst).smul hξ
  have hsum : (fun w : ℝ × ℝ ↦ endCutoff (-1) T w.1 • ξ w) +
      (fun w ↦ endCutoff 1 T w.1 • ξ w) + (fun w ↦ middleCutoff T w.1 • ξ w) = ξ := by
    funext w
    simp only [Pi.add_apply, middleCutoff]
    module
  have h := setIntegral_add_add_le (hcd (contDiff_endCutoff (-1) T))
    (hcd (contDiff_endCutoff 1 T)) (hcd (contDiff_middleCutoff T))
    (isCompact_Icc.prod isCompact_Icc) (S := Icc a b ×ˢ Icc 0 1)
  rwa [hsum] at h

omit [FiniteDimensional ℝ V] in
/-- The window estimate for the middle piece: the interior estimate
`∫ (‖∂s η‖² + ‖∂t η‖²) ≤ C₀ ∫ (‖F‖² + ‖η‖²)` over `[c, d] × [0, 1]`, for `‖η‖ ≤ ‖ξ‖`, gives
`∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C₀ ∫ ‖F‖² + (C₀ + 1) ∫ ‖ξ‖²`. -/
private theorem setIntegral_le_of_setIntegral_norm_fderiv_sq_le {η ξ F : ℝ × ℝ → V}
    (hη : ContDiff ℝ 1 η) (hξ : Continuous ξ) (hF : Continuous F) (hηξ : ∀ z, ‖η z‖ ≤ ‖ξ z‖)
    {c d C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
      C₀ * ∫ z in Icc c d ×ˢ Icc 0 1, (‖F z‖ ^ 2 + ‖η z‖ ^ 2)) :
    ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      C₀ * (∫ z in Icc c d ×ˢ Icc 0 1, ‖F z‖ ^ 2) +
        (C₀ + 1) * ∫ z in Icc c d ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  have hW : IsCompact (Icc c d ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hi {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f (Icc c d ×ˢ Icc 0 1) :=
    hf.continuousOn.integrableOn_compact hW
  have hdη (v : ℝ × ℝ) : Continuous fun z ↦ ‖fderiv ℝ η z v‖ ^ 2 :=
    ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 2
  have hηξ' : ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 ≤ ∫ z in Icc c d ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 :=
    setIntegral_mono_on (hi (hη.continuous.norm.pow 2)) (hi (hξ.norm.pow 2)) hW.measurableSet
      fun z _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hηξ z) 2
  have hη₀ : 0 ≤ ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 :=
    setIntegral_nonneg hW.measurableSet fun _ _ ↦ by positivity
  have e₁ : ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) =
      (∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2)) + ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 :=
    integral_add (hi ((hdη _).add (hdη _))) (hi (hη.continuous.norm.pow 2))
  have e₂ : ∫ z in Icc c d ×ˢ Icc 0 1, (‖F z‖ ^ 2 + ‖η z‖ ^ 2) =
      (∫ z in Icc c d ×ˢ Icc 0 1, ‖F z‖ ^ 2) + ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 :=
    integral_add (hi (hF.norm.pow 2)) (hi (hη.continuous.norm.pow 2))
  rw [e₁]
  rw [e₂] at h
  nlinarith [mul_le_mul_of_nonneg_left hηξ' hC₀]

omit [FiniteDimensional ℝ V] in
/-- A cut-off piece `β(s) ξ` of a map `ξ` vanishing off `[a, b] × ℝ` vanishes near `z` when `z`
lies off `[a, b] × ℝ` or `β` vanishes near `z.1`. -/
private theorem eventuallyEq_comp_fst_smul_zero {ξ : ℝ × ℝ → V} {a b : ℝ}
    (hab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) {β : ℝ → ℝ} {z : ℝ × ℝ}
    (h : z.1 ∉ Icc a b ∨ β =ᶠ[𝓝 z.1] 0) : (fun w ↦ β w.1 • ξ w) =ᶠ[𝓝 z] 0 := by
  rcases h with h | h
  · filter_upwards [(isClosed_Icc.isOpen_compl.preimage continuous_fst).mem_nhds h] with w hw
    simp [show ξ w = 0 from hab w.1 hw w.2]
  · filter_upwards [continuous_fst.continuousAt.tendsto.eventually h] with w hw
    simp [show β w.1 = 0 from hw]

/-- The piece `ρ(T - 1 - s) ξ` of `ξ` on the positive end, estimated on the window
`[T - 2, max b (T - 2) + 1]` by an end estimate valid on windows in `[N, ∞)`, where
`N + 2 ≤ T`. -/
private theorem setIntegral_endCutoff_neg_one_le (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {u ξ : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    {a b : ℝ} (hab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) {B C N T : ℝ}
    (hB : ∀ s, |deriv Floer.pregluingCutoff s| ≤ B) (hC : 0 ≤ C) (hT₂ : 2 ≤ T)
    (hNT : N + 2 ≤ T)
    (hest : ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃c d : ℝ⦄, c ≤ d → N ≤ c → (∀ t, η (c, t) = 0) → (∀ t, η (d, t) = 0) →
        ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc c d ×ˢ Icc 0 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u η z‖ ^ 2) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        (‖fderiv ℝ (fun w ↦ endCutoff (-1) T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ endCutoff (-1) T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
          ‖endCutoff (-1) T z.1 • ξ z‖ ^ 2) ≤
      C * (2 * (∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
          (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) u ξ z‖ ^ 2) +
        2 * (2 * B) ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) + 0 := by
  have hB₂ (s : ℝ) : |deriv (endCutoff (-1) T) s| ≤ 2 * B :=
    (abs_deriv_endCutoff_le (by norm_num) hB T s).trans
      (by linarith [(abs_nonneg _).trans (hB 0)])
  have hd : ∀ t, ξ (max b (T - 2) + 1, t) = 0 :=
    hab _ fun h ↦ by linarith [h.2, le_max_left b (T - 2)]
  refine setIntegral_comp_fst_smul_le ω hJ hH hu hξ (contDiff_endCutoff (-1) T)
    (abs_endCutoff_le (-1) T) hB₂ (fun s hs ↦ deriv_endCutoff_eq_zero (by norm_num) hT₂ hs) hab
    (c := T - 2) (d := max b (T - 2) + 1) (fun z hz ↦ eventuallyEq_comp_fst_smul_zero hab ?_) hC
    ((hest (c := T - 2) (d := max b (T - 2) + 1)
      (((contDiff_endCutoff _ _).comp contDiff_fst).smul hξ)
      (fun s t ↦ congrArg (endCutoff (-1) T s • ·) (hper s t))
      (by linarith [le_max_right b (T - 2)]) (by linarith)
      (fun t ↦ by simp [endCutoff_eq_zero (σ := -1) (s := T - 2) (T := T) (by linarith)])
      (fun t ↦ by simp [hd t])).trans_eq (add_zero _).symm)
  -- Off the window, a point of `[a, b]` lies in `s < T - 2`, where the cutoff vanishes.
  by_cases h : z.1 ∈ Icc a b
  · refine Or.inr ?_
    have hz' : z.1 < T - 2 := by
      by_contra hc
      exact hz ⟨h, not_lt.1 hc, by linarith [h.2, le_max_left b (T - 2)]⟩
    filter_upwards [eventually_lt_nhds hz'] with s hs
    exact endCutoff_eq_zero (by linarith)
  · exact Or.inl h

/-- The piece `ρ(s + T - 1) ξ` of `ξ` on the negative end, estimated on the window
`[min a (2 - T) - 1, 2 - T]` by an end estimate valid on windows in `(-∞, N]`, where
`2 - N ≤ T`. -/
private theorem setIntegral_endCutoff_one_le (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {u ξ : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    {a b : ℝ} (hab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) {B C N T : ℝ}
    (hB : ∀ s, |deriv Floer.pregluingCutoff s| ≤ B) (hC : 0 ≤ C) (hT₂ : 2 ≤ T)
    (hNT : 2 - N ≤ T)
    (hest : ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃c d : ℝ⦄, c ≤ d → d ≤ N → (∀ t, η (c, t) = 0) → (∀ t, η (d, t) = 0) →
        ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc c d ×ˢ Icc 0 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u η z‖ ^ 2) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        (‖fderiv ℝ (fun w ↦ endCutoff 1 T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ endCutoff 1 T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
          ‖endCutoff 1 T z.1 • ξ z‖ ^ 2) ≤
      C * (2 * (∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
          (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) u ξ z‖ ^ 2) +
        2 * (2 * B) ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) + 0 := by
  have hB₂ (s : ℝ) : |deriv (endCutoff 1 T) s| ≤ 2 * B :=
    (abs_deriv_endCutoff_le (by norm_num) hB T s).trans
      (by linarith [(abs_nonneg _).trans (hB 0)])
  have hc : ∀ t, ξ (min a (2 - T) - 1, t) = 0 :=
    hab _ fun h ↦ by linarith [h.1, min_le_left a (2 - T)]
  refine setIntegral_comp_fst_smul_le ω hJ hH hu hξ (contDiff_endCutoff 1 T)
    (abs_endCutoff_le 1 T) hB₂ (fun s hs ↦ deriv_endCutoff_eq_zero (by norm_num) hT₂ hs) hab
    (c := min a (2 - T) - 1) (d := 2 - T)
    (fun z hz ↦ eventuallyEq_comp_fst_smul_zero hab ?_) hC
    ((hest (c := min a (2 - T) - 1) (d := 2 - T)
      (((contDiff_endCutoff _ _).comp contDiff_fst).smul hξ)
      (fun s t ↦ congrArg (endCutoff 1 T s • ·) (hper s t))
      (by linarith [min_le_right a (2 - T)]) (by linarith)
      (fun t ↦ by simp [hc t])
      (fun t ↦ by simp [endCutoff_eq_zero (σ := 1) (s := 2 - T) (T := T) (by linarith)])).trans_eq
      (add_zero _).symm)
  -- Off the window, a point of `[a, b]` lies in `s > 2 - T`, where the cutoff vanishes.
  by_cases h : z.1 ∈ Icc a b
  · refine Or.inr ?_
    have hz' : 2 - T < z.1 := by
      by_contra hc
      exact hz ⟨h, by linarith [h.1, min_le_left a (2 - T)], not_lt.1 hc⟩
    filter_upwards [eventually_gt_nhds hz'] with s hs
    exact endCutoff_eq_zero (by linarith)
  · exact Or.inl h

/-- The middle piece `middleCutoff T s • ξ`, estimated on `[-T, T]` by the interior estimate. -/
private theorem setIntegral_middleCutoff_le (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {u ξ : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    {a b : ℝ} (hab : ∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) {B C₀ T : ℝ}
    (hB : ∀ s, |deriv Floer.pregluingCutoff s| ≤ B) (hC₀ : 0 ≤ C₀) (hT₂ : 2 ≤ T)
    (hint : ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → (∀ s ∈ Icc (-T) T, η (s, 1) = η (s, 0)) →
      (∀ t, η (-T, t) = 0) → (∀ t, η (T, t) = 0) →
      ∫ z in Icc (-T) T ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Icc (-T) T ×ˢ Icc 0 1, (‖ω.floerLinearization
          (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) u η z‖ ^ 2 + ‖η z‖ ^ 2)) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        (‖fderiv ℝ (fun w ↦ middleCutoff T w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ middleCutoff T w.1 • ξ w) z stdComplexLineImag‖ ^ 2 +
          ‖middleCutoff T z.1 • ξ z‖ ^ 2) ≤
      C₀ * (2 * (∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
          (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) u ξ z‖ ^ 2) +
        2 * (2 * B) ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) +
        (C₀ + 1) * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  have hη : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ middleCutoff T w.1 • ξ w :=
    ((contDiff_middleCutoff T).comp contDiff_fst).smul hξ
  refine setIntegral_comp_fst_smul_le ω hJ hH hu hξ (contDiff_middleCutoff T)
    (abs_middleCutoff_le hT₂) (abs_deriv_middleCutoff_le hB T)
    (fun s hs ↦ (middleCutoff_eventuallyEq_zero hT₂ hs).deriv_eq.trans (deriv_const s 0)) hab
    (c := -T) (d := T) (fun z hz ↦ eventuallyEq_comp_fst_smul_zero hab ?_) hC₀
    (setIntegral_le_of_setIntegral_norm_fderiv_sq_le (hη.of_le one_le_two) hξ.continuous
      (continuous_floerLinearization_cylindrical ω hJ hH hu (hη.of_le one_le_two))
      (fun z ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (abs_middleCutoff_le hT₂ _)) hC₀
      (hint hη (fun s _ ↦ by simpa using congrArg (middleCutoff T s • ·) (hper s 0))
        (fun t ↦ by simp [middleCutoff_eq_zero hT₂ (s := -T) (by
          rw [abs_neg, abs_of_nonneg (by linarith)])])
        (fun t ↦ by simp [middleCutoff_eq_zero hT₂ (s := T) (by
          rw [abs_of_nonneg (by linarith)])])))
  -- Off `[-T, T]` the middle cutoff vanishes.
  by_cases h : z.1 ∈ Icc a b
  · refine Or.inr (middleCutoff_eventuallyEq_zero hT₂ ?_)
    by_contra hc
    exact hz ⟨h, abs_le.1 (not_lt.1 hc)⟩
  · exact Or.inl h

/-- **The semi-Fredholm estimate of the linearized Floer operator on a cylinder.** Let `x₋` and
`x₊` be orbits of a jointly `C²` Hamiltonian `H` whose suspended vector field is globally
Lipschitz, with `x₋(0)` and `x₊(0)` nondegenerate fixed points of the time-one map, as for
nondegenerate one-periodic orbits of a one-periodic Hamiltonian. Let `J_t(y)` be a `C¹` family of
almost complex structures and `u` a `C¹` map, with `J_t(u(s, t))`, `J_t(x₋(t))` and `J_t(x₊(t))`
all `ω`-compatible, whose loops converge uniformly to `x₋` as `s → -∞` and to `x₊` as `s → +∞`
while its slice defect `∂t u - X_{H_t}(u)` tends uniformly to zero, as for a Floer cylinder from
`x₋` to `x₊`. Then there are constants `C ≥ 0` and `T` such that every `C²` map `ξ` of period one
in `t` vanishing off a slab `[a, b] × ℝ` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals being over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of
the datum `K = H_t dt`. The constants depend neither on `ξ` nor on `a` and `b`. -/
theorem exists_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot
      (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
      (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, (∀ s ∉ Icc a b, ∀ t, ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z‖ ^ 2) + ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) := by
  -- The end estimates hold on `[N₊, ∞)` and `(-∞, N₋]`; the cutoffs switch on `[T - 2, T]` and
  -- `[-T, 2 - T]`, and the interior estimate is used on `[-T, T]`.
  have hu₁ (l : Filter ℝ) : ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 u (s, t) :=
    Eventually.of_forall fun _ _ _ ↦ hu.contDiffAt
  obtain ⟨Cp, hCp, Up, hUp, hestp⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hxp hndp
      hJ hJxp (hu₁ atTop) huxp hδp
  obtain ⟨Cm, hCm, Um, hUm, hestm⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hxm hndm
      hJ hJxm (hu₁ atBot) huxm hδm
  obtain ⟨Np, hNp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Nm, hNm⟩ := mem_atBot_sets.1 hUm
  set T := max (max (Np + 2) (2 - Nm)) 2
  have hT₂ : 2 ≤ T := le_max_right _ _
  have hTp : Np + 2 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hTm : 2 - Nm ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨C₀, hC₀, hint⟩ :=
    exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic ω
      (J := fun w y ↦ J w.2 y) (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) (u := u)
      (by linarith : -T ≤ T)
      (fun _ _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
      (fun _ _ ↦ contDiffAt_const)
      (fun _ _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
      (fun _ _ ↦ hu.contDiffAt) fun z _ ↦ hJu z
  obtain ⟨B, hB⟩ := Floer.exists_abs_deriv_pregluingCutoff_le
  refine ⟨3 * ((Cp + Cm + C₀) * (2 + 2 * (2 * B) ^ 2) + C₀ + 1), by positivity, T,
    fun ξ hξ hper a b hab ↦ ?_⟩
  -- Cut `ξ` into a positive end piece, a negative end piece and a middle piece.
  have hp := setIntegral_endCutoff_neg_one_le ω hJ hH hu hξ hper hab hB hCp hT₂ hTp
    fun η hη hηp c d hcd hNc hc hd ↦ hestp hη hηp hcd (fun s hs ↦ hNp s (hNc.trans hs.1)) hc hd
  have hm := setIntegral_endCutoff_one_le ω hJ hH hu hξ hper hab hB hCm hT₂ hTm
    fun η hη hηp c d hcd hdN hc hd ↦ hestm hη hηp hcd (fun s hs ↦ hNm s (hs.2.trans hdN)) hc hd
  have h₀ := setIntegral_middleCutoff_le ω hJ hH hu hξ hper hab hB hC₀ hT₂ hint
  have hdec := setIntegral_le_three_mul_cutoff (hξ.of_le one_le_two) T a b
  -- Sum the three estimates.
  have hP : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1, ‖ω.floerLinearization
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ H w.2) u ξ z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  have hQ : 0 ≤ ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  have hCs : 0 ≤ Cp + Cm + C₀ := by positivity
  refine hdec.trans ?_
  nlinarith [mul_nonneg hCs hQ, mul_nonneg hCs (mul_nonneg (sq_nonneg B) hP),
    mul_nonneg (add_nonneg hC₀ zero_le_one) hP]

end TauCeti.SymplecticForm
