/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.CalderonZygmund
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.OfReal

/-!
# Interior `Lᵖ` estimates for the Cauchy–Riemann operator

Let `1 < p < ∞`, let `U ⊆ ℂ` be open and let `K ⊆ U` be compact. There is a constant `C` such that

`‖Du‖_{Lᵖ(K)} ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`

for every map `u : ℂ → F`, into a complex Hilbert space, that is smooth on `U`
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`). Here `Du` is the real
derivative of `u` and `\bar∂u = (∂ₛu + I ∂ₜu) / 2` is its conjugate Wirtinger derivative
`TauCeti.conjWirtingerDeriv u z 1`. Since `‖u‖_{Lᵖ(K)} ≤ ‖u‖_{Lᵖ(U)}`, this bounds the whole
`W^{1,p}(K)` norm of `u`. It is the interior form of the Calderón–Zygmund inequality
`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_of_hasCompactSupport`, which needs
`u` to be compactly supported, and it is the basic interior estimate of elliptic regularity for
`J`-holomorphic curves: the derivative of a solution is controlled on compact subsets by the
equation and the solution itself.

The estimate is stable under perturbations of `\bar∂` by a small multiple of the derivative and an
arbitrary bounded multiple of the map
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le`): there is `δ > 0`,
depending only on `p` and `F`, such that if `‖g - \bar∂u‖ ≤ δ ‖Du‖ + M ‖u‖` pointwise on `U`, then
`‖Du‖_{Lᵖ(K)} ≤ C (‖g‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`. Its main instance is the variable-coefficient
operator `(∂ₛu + J(z) ∂ₜu) / 2 + B(z) u` for a real-linear field `J` uniformly close to
multiplication by `I` and a bounded zeroth-order term `B`
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_I_smul_le`). This is the form taken by the
Cauchy–Riemann operator `∂ₛ + J ∂ₜ` and by its linearization in local coordinates in which the
almost complex structure is close to the standard one. The `L²` estimate for perturbations of a
constant compatible complex structure on a real inner product space, which needs no
Calderón–Zygmund inequality, is in `TauCeti.Geometry.Symplectic.JHolomorphic.InteriorEstimate`.

## The argument

Choose a smooth cutoff `χ` with values in `[0, 1]`, equal to one near `K` and compactly supported
in `U` (`IsCompact.exists_contDiff_cutoff`), and put `v = χ u`. Then `v` is smooth and compactly
supported, and `Dv = Du` on `K`. The Calderón–Zygmund inequality bounds `‖Dv‖_{Lᵖ}` by
`C₀ ‖\bar∂v‖_{Lᵖ}`, and the product rule gives `\bar∂v = χ \bar∂u + (\bar∂χ) u` with
`|\bar∂χ| ≤ ‖Dχ‖`. Under the perturbation hypothesis, `χ ‖Du‖ ≤ ‖Dv‖ + ‖Dχ‖ ‖u‖` turns the term
`δ χ ‖Du‖` into `δ ‖Dv‖` plus a multiple of `‖u‖`, and a choice with `C₀ δ ≤ 1 / 2` absorbs it
into the left-hand side, which is finite because `v` is smooth with compact support.

## Main results

* `TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le`: the interior estimate for
  perturbations of `\bar∂`.
* `TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`: the interior estimate
  for `\bar∂` itself.
* `TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_I_smul_le`: the interior estimate for the
  variable-coefficient operator `(∂ₛu + J(z) ∂ₜu) / 2 + B(z) u`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B (the Calderón–Zygmund inequality and the
  interior elliptic estimates for the Cauchy–Riemann operator).
-/

public section

open scoped ENNReal NNReal ContDiff Topology
open MeasureTheory Complex Set Function Filter

namespace TauCeti

section Cutoff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Against a real factor `χ`, `\bar∂(χ u)` differs from `χ \bar∂u` by `(\bar∂χ) u`, whose norm is
at most `‖Dχ‖ ‖u‖`. -/
private theorem norm_conjWirtingerDeriv_smul_sub_smul_le {χ : ℂ → ℝ} {u : ℂ → F} {z : ℂ}
    (hχ : DifferentiableAt ℝ χ z) (hu : DifferentiableAt ℝ u z) :
    ‖conjWirtingerDeriv (fun y ↦ χ y • u y) z 1 - χ z • conjWirtingerDeriv u z 1‖ ≤
      ‖fderiv ℝ χ z‖ * ‖u z‖ := by
  have hχℂ : DifferentiableAt ℝ (fun y ↦ (χ y : ℂ)) z := ofRealCLM.differentiableAt.comp z hχ
  have hfun : (fun y ↦ χ y • u y) = fun y ↦ (χ y : ℂ) • u y :=
    funext fun y ↦ (Complex.coe_smul _ _).symm
  rw [hfun, conjWirtingerDeriv_smul_apply hχℂ hu, Complex.coe_smul, add_sub_cancel_left,
    norm_smul]
  gcongr
  -- `\bar∂χ = (Dχ 1 + I Dχ I) / 2`, with both real derivatives at most `‖Dχ‖`.
  have h1 : ‖fderiv ℝ χ z 1‖ ≤ ‖fderiv ℝ χ z‖ := by
    simpa using (fderiv ℝ χ z).le_opNorm 1
  have hI : ‖fderiv ℝ χ z I‖ ≤ ‖fderiv ℝ χ z‖ := by
    simpa using (fderiv ℝ χ z).le_opNorm I
  rw [conjWirtingerDeriv_apply, fderiv_ofReal_comp_apply, fderiv_ofReal_comp_apply,
    smul_eq_mul I 1, mul_one, norm_smul, norm_inv, Complex.norm_two]
  calc 2⁻¹ * ‖(fderiv ℝ χ z 1 : ℂ) + I • (fderiv ℝ χ z I : ℂ)‖
      ≤ 2⁻¹ * (‖fderiv ℝ χ z 1‖ + ‖fderiv ℝ χ z I‖) := by
        gcongr
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
    _ ≤ 2⁻¹ * (‖fderiv ℝ χ z‖ + ‖fderiv ℝ χ z‖) := by gcongr
    _ = ‖fderiv ℝ χ z‖ := by ring

/-- The pointwise form of the interior estimate: if `g` is within `δ ‖Du‖ + M ‖u‖` of `\bar∂u`,
then `\bar∂(χ u)` is bounded by `‖g‖ + δ ‖D(χ u)‖` plus a multiple of `‖u‖`, for a cutoff `χ`
with values in `[0, 1]` and `‖Dχ‖ ≤ L`. -/
private theorem norm_conjWirtingerDeriv_smul_le {χ : ℂ → ℝ} {u g : ℂ → F} {z : ℂ} {δ M L : ℝ}
    (hχ : DifferentiableAt ℝ χ z) (hu : DifferentiableAt ℝ u z) (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hL : ‖fderiv ℝ χ z‖ ≤ L) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hg : ‖g z - conjWirtingerDeriv u z 1‖ ≤ δ * ‖fderiv ℝ u z‖ + M * ‖u z‖) :
    ‖conjWirtingerDeriv (fun y ↦ χ y • u y) z 1‖ ≤
      ‖g z‖ + δ * ‖fderiv ℝ (fun y ↦ χ y • u y) z‖ + (δ * L + M + L) * ‖u z‖ := by
  have hcut := norm_conjWirtingerDeriv_smul_sub_smul_le hχ hu
  -- `χ ‖Du‖ ≤ ‖D(χ u)‖ + ‖Dχ‖ ‖u‖`, read off the product rule for `D(χ u)`.
  have hDu : χ z * ‖fderiv ℝ u z‖ ≤
      ‖fderiv ℝ (fun y ↦ χ y • u y) z‖ + ‖fderiv ℝ χ z‖ * ‖u z‖ := by
    have hD := fderiv_fun_smul hχ hu
    have : χ z • fderiv ℝ u z =
        fderiv ℝ (fun y ↦ χ y • u y) z - (fderiv ℝ χ z).smulRight (u z) := by
      rw [hD, add_sub_cancel_right]
    calc χ z * ‖fderiv ℝ u z‖ = ‖χ z • fderiv ℝ u z‖ := by
          rw [norm_smul, Real.norm_of_nonneg hχ0]
      _ ≤ _ := by
          rw [this, ← ContinuousLinearMap.norm_smulRight_apply]
          exact norm_sub_le _ _
  have hdbar : ‖conjWirtingerDeriv u z 1‖ ≤ ‖g z‖ + (δ * ‖fderiv ℝ u z‖ + M * ‖u z‖) :=
    (norm_le_norm_add_norm_sub' _ (g z)).trans (by rw [norm_sub_rev]; gcongr)
  have hu0 := norm_nonneg (u z)
  calc ‖conjWirtingerDeriv (fun y ↦ χ y • u y) z 1‖
      ≤ ‖χ z • conjWirtingerDeriv u z 1‖ + ‖fderiv ℝ χ z‖ * ‖u z‖ :=
        (norm_le_norm_add_norm_sub' _ _).trans (by gcongr)
    _ = χ z * ‖conjWirtingerDeriv u z 1‖ + ‖fderiv ℝ χ z‖ * ‖u z‖ := by
        rw [norm_smul, Real.norm_of_nonneg hχ0]
    _ ≤ χ z * ‖g z‖ + δ * (χ z * ‖fderiv ℝ u z‖) + χ z * (M * ‖u z‖) + L * ‖u z‖ := by
        have := mul_le_mul_of_nonneg_left hdbar hχ0
        nlinarith [mul_le_mul_of_nonneg_right hL hu0]
    _ ≤ ‖g z‖ + δ * (‖fderiv ℝ (fun y ↦ χ y • u y) z‖ + L * ‖u z‖) + M * ‖u z‖ + L * ‖u z‖ := by
        have hgχ : χ z * ‖g z‖ ≤ ‖g z‖ := mul_le_of_le_one_left (norm_nonneg _) hχ1
        have hMχ : χ z * (M * ‖u z‖) ≤ M * ‖u z‖ :=
          mul_le_of_le_one_left (mul_nonneg hM hu0) hχ1
        have hDuL : χ z * ‖fderiv ℝ u z‖ ≤ ‖fderiv ℝ (fun y ↦ χ y • u y) z‖ + L * ‖u z‖ :=
          hDu.trans (by gcongr)
        gcongr
    _ = ‖g z‖ + δ * ‖fderiv ℝ (fun y ↦ χ y • u y) z‖ + (δ * L + M + L) * ‖u z‖ := by ring

/-- On a compact set where the cutoff `χ` is one nearby, `D u = D (χ u)`, so the `Lᵖ` norm of
`D u` there is at most that of `D (χ u)` on the whole plane. -/
private theorem eLpNorm_fderiv_restrict_le_of_subset_interior {χ : ℂ → ℝ} {u : ℂ → F}
    {K : Set ℂ} (hK : IsCompact K) (hKχ : K ⊆ interior (χ ⁻¹' {1})) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
      eLpNorm (fderiv ℝ fun y ↦ χ y • u y) p volume := by
  have heq : fderiv ℝ u =ᵐ[volume.restrict K] fderiv ℝ fun y ↦ χ y • u y := by
    refine ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ ?_
    refine (Filter.EventuallyEq.fderiv_eq ?_).symm
    filter_upwards [isOpen_interior.mem_nhds (hKχ hz)] with y hy
    have hy1 : χ y = 1 := interior_subset hy
    simp [hy1]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **The `Lᵖ` form of the cutoff estimate.** For a smooth cutoff `χ` with values in `[0, 1]`,
supported in `U` and with `‖Dχ‖ ≤ L`, and `g` within `δ ‖Du‖ + M ‖u‖` of `\bar∂u` on `U`,
`‖\bar∂(χ u)‖_{Lᵖ} ≤ ‖g‖_{Lᵖ(U)} + δ ‖D(χ u)‖_{Lᵖ} + (δ L + M + L) ‖u‖_{Lᵖ(U)}`. -/
private theorem eLpNorm_conjWirtingerDeriv_smul_le {χ : ℂ → ℝ} {u g : ℂ → F} {U : Set ℂ}
    {δ M L : ℝ≥0} {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hχr : range χ ⊆ Icc 0 1) (hχU : tsupport χ ⊆ U) (hL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)
    (hu : ContDiffOn ℝ ∞ u U) (hgm : AEStronglyMeasurable g (volume.restrict U))
    (hg : ∀ z ∈ U, ‖g z - conjWirtingerDeriv u z 1‖ ≤ δ * ‖fderiv ℝ u z‖ + M * ‖u z‖) :
    eLpNorm (fun z ↦ conjWirtingerDeriv (fun y ↦ χ y • u y) z 1) p volume ≤
      eLpNorm g p (volume.restrict U) +
        δ * eLpNorm (fderiv ℝ fun y ↦ χ y • u y) p volume +
          (δ * L + M + L : ℝ≥0) * eLpNorm u p (volume.restrict U) := by
  set v : ℂ → F := fun y ↦ χ y • u y
  have hv : ContDiff ℝ ∞ v := hu.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU
  have hDv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hdbar : Continuous fun z ↦ conjWirtingerDeriv v z 1 := by
    simp only [conjWirtingerDeriv_apply]
    fun_prop
  -- Off `U`, the map `v` vanishes near the point, and so does `\bar∂ v`.
  have hsupp : (fun z ↦ conjWirtingerDeriv v z 1).support ⊆ U := by
    intro z hz
    by_contra hzU
    have hzv : z ∉ tsupport v := fun h ↦ hzU (hχU (tsupport_smul_subset_left χ u h))
    exact hz (by simp [conjWirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hzv])
  rw [← eLpNorm_restrict_eq_of_support_subset hdbar.aestronglyMeasurable hsupp]
  have hpt : ∀ᵐ z ∂(volume.restrict U), ‖conjWirtingerDeriv v z 1‖ ≤
      ‖g z‖ + δ * ‖fderiv ℝ v z‖ + (δ * L + M + L : ℝ≥0) * ‖u z‖ := by
    refine ae_restrict_of_forall_mem hU.measurableSet fun z hz ↦ ?_
    have h := norm_conjWirtingerDeriv_smul_le (hχ.differentiable (by simp) z)
      ((hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)) (hχr ⟨z, rfl⟩).1
      (hχr ⟨z, rfl⟩).2 (hL z) δ.2 M.2 (hg z hz)
    simpa using h
  have hsplit : (fun z ↦ ‖g z‖ + δ * ‖fderiv ℝ v z‖ + (δ * L + M + L : ℝ≥0) * ‖u z‖) =
      (fun z ↦ ‖g z‖) + ((δ : ℝ) • fun z ↦ ‖fderiv ℝ v z‖) +
        (((δ * L + M + L : ℝ≥0) : ℝ) • fun z ↦ ‖u z‖) :=
    rfl
  refine (eLpNorm_mono_ae_real hdbar.aestronglyMeasurable hpt).trans ?_
  rw [hsplit]
  refine (eLpNorm_add_le hp).trans (add_le_add ((eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_norm _ hgm).le ?_)) ?_)
  · rw [eLpNorm_const_smul, NNReal.enorm_eq, eLpNorm_norm _ hDv.aestronglyMeasurable]
    exact mul_le_mul_right (eLpNorm_mono_measure (fderiv ℝ v) Measure.restrict_le_self) _
  · rw [eLpNorm_const_smul, NNReal.enorm_eq,
      eLpNorm_norm _ (hu.continuousOn.aestronglyMeasurable hU.measurableSet)]

end Cutoff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The interior `Lᵖ` estimate for perturbations of `\bar∂`.** For `1 < p < ∞` there is
`δ > 0` with the following property. For `U ⊆ ℂ` open, `K ⊆ U` compact and `M ≥ 0` there is a
constant `C` such that every map `u` smooth on `U` and every `g` with
`‖g - \bar∂u‖ ≤ δ ‖Du‖ + M ‖u‖` on `U` satisfy
`‖Du‖_{Lᵖ(K)} ≤ C (‖g‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`. -/
theorem exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃U K : Set ℂ⦄, IsOpen U → IsCompact K → K ⊆ U → ∀ M : ℝ≥0,
      ∃ C : ℝ≥0, ∀ u g : ℂ → F, ContDiffOn ℝ ∞ u U →
        (∀ z ∈ U, ‖g z - conjWirtingerDeriv u z 1‖ ≤ δ * ‖fderiv ℝ u z‖ + M * ‖u z‖) →
        eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
          C * (eLpNorm g p (volume.restrict U) + eLpNorm u p (volume.restrict U)) := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_of_hasCompactSupport (F := F) hp hp_top
  -- Enlarge the Calderón–Zygmund constant to make it positive, and take `δ` with `C₁ δ = 1 / 2`.
  set C₁ : ℝ≥0 := C₀ + 1
  have hC₁0 : C₁ ≠ 0 := by positivity
  set δ : ℝ≥0 := (2 * C₁)⁻¹ with hδ
  have hC₁δ : ((C₁ * δ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by
    rw [hδ, mul_inv, ← mul_assoc, mul_comm C₁, mul_assoc, mul_inv_cancel₀ hC₁0, mul_one,
      ENNReal.coe_inv two_ne_zero, ENNReal.coe_two]
  refine ⟨δ, by positivity, fun U K hU hK hKU M ↦ ?_⟩
  obtain ⟨χ, hχ, hχr, hKχ, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, ∀ z, ‖fderiv ℝ χ z‖ ≤ L := by
    obtain ⟨L, hL⟩ := (hχ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
      (hχc.fderiv ℝ).norm
    exact ⟨L.toNNReal, fun z ↦ (hL ⟨z, rfl⟩).trans (Real.le_coe_toNNReal L)⟩
  set N : ℝ≥0 := δ * L + M + L
  refine ⟨2 * C₁ * (1 + N), fun u g hu hg ↦ ?_⟩
  -- A nonmeasurable `g` has infinite `Lᵖ` norm, and there is nothing to prove.
  by_cases hgm : AEStronglyMeasurable g (volume.restrict U)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hgm, top_add, ENNReal.mul_top (by positivity)]
    exact le_top
  set v : ℂ → F := fun y ↦ χ y • u y
  have hv : ContDiff ℝ ∞ v := hu.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU
  have hvc : HasCompactSupport v := hχc.smul_right
  set X := eLpNorm (fderiv ℝ v) p volume
  have hX : X ≠ ⊤ :=
    ((hv.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hvc.fderiv ℝ)).eLpNorm_ne_top
  set G := eLpNorm g p (volume.restrict U)
  set Y := eLpNorm u p (volume.restrict U)
  -- The Calderón–Zygmund inequality for `v`, with the term `δ ‖D v‖` absorbed by `C₁ δ = 1 / 2`.
  have hXle : X ≤ C₁ * (G + N * Y) + X / 2 :=
    calc X ≤ C₀ * eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) p volume := hC₀ v hv hvc
      _ ≤ C₁ * (G + δ * X + N * Y) := by
          gcongr
          · exact_mod_cast le_self_add
          · exact eLpNorm_conjWirtingerDeriv_smul_le hp.le hU hχ hχr hχU hL hu hgm hg
      _ = C₁ * (G + N * Y) + ((C₁ * δ : ℝ≥0) : ℝ≥0∞) * X := by
          push_cast
          ring
      _ = C₁ * (G + N * Y) + X / 2 := by rw [hC₁δ, ENNReal.div_eq_inv_mul]
  have hX2 : X / 2 ≤ C₁ * (G + N * Y) := by
    have h : X / 2 + X / 2 ≤ C₁ * (G + N * Y) + X / 2 := by rwa [ENNReal.add_halves]
    exact (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hX two_ne_zero)).1 h
  rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)] at hX2
  have hGY : G + N * Y ≤ (1 + N) * (G + Y) := by
    rw [add_mul, one_mul, mul_add]
    exact add_le_add le_self_add le_add_self
  calc eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤ X :=
        eLpNorm_fderiv_restrict_le_of_subset_interior hK hKχ p
    _ ≤ C₁ * (G + N * Y) * 2 := hX2
    _ ≤ C₁ * ((1 + N) * (G + Y)) * 2 := by gcongr
    _ = ((2 * C₁ * (1 + N) : ℝ≥0) : ℝ≥0∞) * (G + Y) := by
        push_cast
        ring

/-- **The interior `Lᵖ` estimate for the Cauchy–Riemann operator.** For `1 < p < ∞`, `U ⊆ ℂ`
open and `K ⊆ U` compact, there is a constant `C` such that every map `u` smooth on `U` satisfies
`‖Du‖_{Lᵖ(K)} ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`. -/
theorem exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContDiffOn ℝ ∞ u U →
      eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
        C * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict U) +
          eLpNorm u p (volume.restrict U)) := by
  obtain ⟨δ, -, hδ⟩ :=
    exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le (F := F) hp hp_top
  obtain ⟨C, hC⟩ := hδ hU hK hKU 0
  exact ⟨C, fun u hu ↦ hC u _ hu fun z _ ↦ by simp [mul_nonneg]⟩

/-- **The interior `Lᵖ` estimate for a variable-coefficient Cauchy–Riemann operator.** For
`1 < p < ∞` there is `δ > 0` with the following property. For `U ⊆ ℂ` open, `K ⊆ U` compact and
`M ≥ 0` there is a constant `C` such that, whenever the real-linear maps `J z` satisfy
`‖J z w - I • w‖ ≤ δ ‖w‖` and the maps `B z` satisfy `‖B z‖ ≤ M` for `z ∈ U`, every map `u` smooth
on `U` satisfies `‖Du‖_{Lᵖ(K)} ≤ C (‖(∂ₛu + J ∂ₜu) / 2 + B u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`. For
`J z = I • ·` and `B = 0` the operator is `\bar∂`. -/
theorem exists_eLpNorm_fderiv_le_of_norm_sub_I_smul_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃U K : Set ℂ⦄, IsOpen U → IsCompact K → K ⊆ U → ∀ M : ℝ≥0,
      ∃ C : ℝ≥0, ∀ (u : ℂ → F) (J B : ℂ → F →L[ℝ] F), ContDiffOn ℝ ∞ u U →
        (∀ z ∈ U, ∀ w, ‖J z w - I • w‖ ≤ δ * ‖w‖) → (∀ z ∈ U, ‖B z‖ ≤ M) →
        eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
          C * (eLpNorm (fun z ↦ (2 : ℂ)⁻¹ • (fderiv ℝ u z 1 + J z (fderiv ℝ u z I)) + B z (u z))
            p (volume.restrict U) + eLpNorm u p (volume.restrict U)) := by
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le (F := F) hp hp_top
  refine ⟨2 * δ, by positivity, fun U K hU hK hKU M ↦ ?_⟩
  obtain ⟨C, hC⟩ := hδ hU hK hKU M
  refine ⟨C, fun u J B hu hJ hB ↦ hC u _ hu fun z hz ↦ ?_⟩
  have hsub : (2 : ℂ)⁻¹ • (fderiv ℝ u z 1 + J z (fderiv ℝ u z I)) + B z (u z) -
      conjWirtingerDeriv u z 1 =
        (2 : ℂ)⁻¹ • (J z (fderiv ℝ u z I) - I • fderiv ℝ u z I) + B z (u z) := by
    rw [conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
    module
  have hDI : ‖fderiv ℝ u z I‖ ≤ ‖fderiv ℝ u z‖ := by
    simpa using (fderiv ℝ u z).le_opNorm I
  rw [hsub]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((B z).le_opNorm _ |>.trans ?_))
  · rw [norm_smul, norm_inv, Complex.norm_two]
    calc 2⁻¹ * ‖J z (fderiv ℝ u z I) - I • fderiv ℝ u z I‖
        ≤ 2⁻¹ * ((2 * δ : ℝ≥0) * ‖fderiv ℝ u z I‖) := by gcongr; exact hJ z hz _
      _ ≤ 2⁻¹ * ((2 * δ : ℝ≥0) * ‖fderiv ℝ u z‖) := by gcongr
      _ = δ * ‖fderiv ℝ u z‖ := by push_cast; ring
  · gcongr
    exact hB z hz

end TauCeti
