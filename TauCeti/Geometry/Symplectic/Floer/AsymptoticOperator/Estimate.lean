/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Analysis.ODE.Periodic
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The `L²` estimate of the stationary cylinder operator at a nondegenerate orbit

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a continuous family of
`ω`-compatible complex structures with associated inner products `g_t = ω(·, J_t ·)`, and
`S_t` a continuous family of infinitesimally symplectic maps, the linearized Hamiltonian vector
field along an orbit. The linearized Floer operator at the stationary cylinder over the orbit is

`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ) = ∂s ξ + A ξ`

(`TauCeti.Floer.stationaryCylinderOperator`), with the asymptotic operator
`A ζ = J_t (ζ' - S_t ζ)` (`TauCeti.Floer.asymptoticOperator`). This file proves that `D` is
bounded below in `L²` when the orbit is nondegenerate, that is, when the return map `Ψ(1)` of
`ζ' = S_t ζ` does not have `1` as an eigenvalue. This is the basic estimate behind the Fredholm
property of the linearized operator on the cylindrical ends of Floer's moduli spaces.

* **The loop estimate.** If `det (1 - Ψ(1)) ≠ 0`, there is a constant `C` such that every loop
  `ζ` with `ζ 1 = ζ 0` satisfies `∫₀¹ g(ζ, ζ) ≤ C ∫₀¹ g(ζ' - S ζ, ζ' - S ζ)`
  (`Floer.exists_forall_integral_associatedBilinForm_le_mul_integral`), that is,
  `∫₀¹ g(ζ, ζ) ≤ C ∫₀¹ g(A ζ, A ζ)`
  (`Floer.exists_forall_integral_associatedBilinForm_le_mul_integral_asymptoticOperator`). It is
  the `L²` estimate `TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq` for the
  linear equation `ζ' = S_t ζ + f`, transported to the forms `g_t`, which are uniformly
  equivalent to the norm because `t` ranges over the compact interval `[0, 1]`.
* **The cylinder estimate.** The energy identity
  `Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator` writes
  `∫ g(D ξ, D ξ)` over `[a, b] × [0, 1]` as `∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ))` plus
  slice pairings at `s = a` and `s = b`, which vanish when `ξ` vanishes on those two slices.
  Applying the loop estimate on every slice and integrating over `s` bounds `∫ g(ξ, ξ)` by the
  same quantity, so

  `∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D ξ, D ξ)`

  with `C` independent of `a`, `b` and `ξ`
  (`Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`). For an actual
  nondegenerate one-periodic orbit of a Hamiltonian, the hypothesis on the return map holds
  (`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`).

In contrast, `Floer.eq_zero_of_stationaryCylinderOperator_eq_zero` shows that `D` is injective on
decaying maps with no nondegeneracy assumption, but without an estimate; at a degenerate orbit
the loops `t ↦ Ψ(t) v` with `Ψ(1) v = v`, cut off in `s`, show that no estimate of this form can
hold. The estimate is stated for maps vanishing on two slices, the form in which it is applied to
compactly supported maps on a cylindrical end; the Sobolev completion and the Fredholm property
themselves are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

/-- The forms `g_t = ω(·, J_t ·)` are uniformly equivalent to the square of the norm over
`t ∈ [0, 1]`, for tame `J_t` depending continuously on `t`. -/
private theorem exists_pos_forall_mul_norm_sq_le_associatedBilinForm (hJ : ∀ t, ω.Tames (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) :
    ∃ a > 0, ∃ b ≥ 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ v,
      a * ‖v‖ ^ 2 ≤ ω.associatedBilinForm (J t) v v ∧
        ω.associatedBilinForm (J t) v v ≤ b * ‖v‖ ^ 2 := by
  set e : ℝ → V →L[ℝ] V := fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap
  have he : Continuous e := continuous_clm_apply.2 fun v ↦ by
    simpa [e, Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  set ωc := ω.toBilinForm.toContinuousBilinearMap
  have hT : IsCompact (e '' Icc 0 1) := isCompact_Icc.image he
  obtain ⟨a, ha, hlow⟩ := hT.exists_pos_forall_mul_norm_sq_le_compRight ωc (by
    rintro _ ⟨t, -, rfl⟩ v hv
    simpa [e, ωc] using hJ t v hv)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn he.continuousOn (s := Icc (0 : ℝ) 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨a, ha, ‖ωc‖ * M, by positivity, fun t ht v ↦
    ⟨by simpa [e, ωc] using hlow _ ⟨t, ht, rfl⟩ v, ?_⟩⟩
  have h₁ : ω.associatedBilinForm (J t) v v = ωc v (e t v) := by simp [e, ωc]
  rw [h₁]
  calc ωc v (e t v) ≤ ‖ωc v (e t v)‖ := Real.le_norm_self _
    _ ≤ ‖ωc‖ * ‖v‖ * ‖e t v‖ := ωc.le_opNorm₂ _ _
    _ ≤ ‖ωc‖ * ‖v‖ * (M * ‖v‖) := by
        gcongr
        exact (e t).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))
    _ = ‖ωc‖ * M * ‖v‖ ^ 2 := by ring

/-- The diagonal `t ↦ g_t(ζ t, ζ t)` along a continuous loop is continuous. -/
private theorem continuous_associatedBilinForm_apply_self_comp
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) {ζ : ℝ → V} (hζ : Continuous ζ) :
    Continuous fun t ↦ ω.associatedBilinForm (J t) (ζ t) (ζ t) :=
  ω.continuous_apply_comp hζ (hJc.comp (continuous_id.prodMk hζ))

/-- **The `L²` loop estimate at a nondegenerate orbit.** Let each `J_t` be `ω`-tame and depend
continuously on `t`, let `S` be continuous, and suppose that `det (1 - Ψ(1)) ≠ 0` for the return
map `Ψ(1) = dysonSeriesLeft S 1` of `ζ' = S_t ζ`. Then there is a constant `C ≥ 0` such that
every solution of `ζ' = S_t ζ + f` with `f` continuous and `ζ 1 = ζ 0` satisfies
`∫₀¹ g_t(ζ, ζ) ≤ C ∫₀¹ g_t(f, f)` for `g_t = ω(·, J_t ·)`. -/
theorem exists_forall_integral_associatedBilinForm_le_mul_integral (hJ : ∀ t, ω.Tames (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ζ f : ℝ → V⦄, Continuous f → (∀ t, HasDerivAt ζ (S t (ζ t) + f t) t) →
      ζ 1 = ζ 0 → ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤
        C * ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_pos_forall_mul_norm_sq_le_associatedBilinForm hJ hJc
  have hdet' : LinearMap.det ((1 : ℝ) • 1 - (↑(dysonSeriesLeft S 1) : V →ₗ[ℝ] V)) ≠ 0 := by
    simpa using hdet
  obtain ⟨C, hC, hle⟩ := exists_forall_integral_norm_sq_le_mul_integral_norm_sq hSc zero_le_one
    hdet'
  refine ⟨b * C / a, by positivity, fun ζ f hf hζ hζ1 ↦ ?_⟩
  have hζc : Continuous ζ := continuous_iff_continuousAt.2 fun t ↦ (hζ t).continuousAt
  have h₁ : ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤ ∫ t in 0..1, b * ‖ζ t‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one
      ((continuous_associatedBilinForm_apply_self_comp hJc hζc).intervalIntegrable _ _)
      ((continuous_const.mul (hζc.norm.pow 2)).intervalIntegrable _ _)
      fun t ht ↦ (hab t ht _).2
  have h₂ : ∫ t in 0..1, a * ‖f t‖ ^ 2 ≤ ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) :=
    intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
      ((continuous_associatedBilinForm_apply_self_comp hJc hf).intervalIntegrable _ _)
      fun t ht ↦ (hab t ht _).1
  rw [intervalIntegral.integral_const_mul] at h₁ h₂
  have h₃ := hle hf hζ (by rw [hζ1, one_smul])
  calc _ ≤ b * ∫ t in 0..1, ‖ζ t‖ ^ 2 := h₁
    _ ≤ b * (C * ∫ t in 0..1, ‖f t‖ ^ 2) := by gcongr
    _ = b * C / a * (a * ∫ t in 0..1, ‖f t‖ ^ 2) := by field_simp
    _ ≤ b * C / a * ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) := by gcongr

/-- **The `L²` lower bound of the asymptotic operator at a nondegenerate orbit.** Under the
hypotheses of `exists_forall_integral_associatedBilinForm_le_mul_integral`, there is a constant
`C ≥ 0` such that every `C¹` loop `ζ` with `ζ 1 = ζ 0` satisfies
`∫₀¹ g_t(ζ, ζ) ≤ C ∫₀¹ g_t(A ζ, A ζ)` for the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)`. -/
theorem exists_forall_integral_associatedBilinForm_le_mul_integral_asymptoticOperator
    (hJ : ∀ t, ω.Tames (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ζ : ℝ → V⦄, ContDiff ℝ 1 ζ → ζ 1 = ζ 0 →
      ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤
        C * ∫ t in 0..1, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t)
          (asymptoticOperator J S ζ t) := by
  obtain ⟨C, hC, h⟩ := exists_forall_integral_associatedBilinForm_le_mul_integral hJ hJc hSc hdet
  refine ⟨C, hC, fun ζ hζ hζ1 ↦ ?_⟩
  have hd (t : ℝ) : HasDerivAt ζ (S t (ζ t) + (deriv ζ t - S t (ζ t))) t := by
    rw [add_sub_cancel]
    exact (hζ.differentiable one_ne_zero t).hasDerivAt
  simpa only [asymptoticOperator_def, SymplecticForm.associatedBilinForm_apply_apply_self_eq]
    using h (f := fun t ↦ deriv ζ t - S t (ζ t))
      ((hζ.continuous_deriv le_rfl).sub (hSc.clm_apply hζ.continuous)) hd hζ1

/-- The function `z ↦ g_{z.2}(f z, f z)` is integrable over every rectangle `[a, b] × [0, 1]`. -/
private theorem integrableOn_rect_associatedBilinForm (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    {f : ℝ × ℝ → V} (hf : Continuous f) (a b : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) (f z) (f z))
      (Icc a b ×ˢ Icc 0 1) :=
  (ω.continuous_apply_comp hf (hJc.comp (continuous_snd.prodMk hf))).continuousOn
    |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- **The cylinder estimate at a nondegenerate orbit.** Let each `J_t` be `ω`-compatible and
depend continuously on `t`, let each `S_t` be infinitesimally symplectic and `S` continuous, and
suppose that `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1) = dysonSeriesLeft S 1`. Then there is
a constant `C ≥ 0` such that for every `C²` map `ξ` of period one in `t` and every `a ≤ b` with
`ξ` vanishing on the slices `s = a` and `s = b`,

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D ξ, D ξ)`

over `[a, b] × [0, 1]`, for `g_t = ω(·, J_t ·)` and the stationary cylinder operator
`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`. The constant does not depend on `a`, `b` or `ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) := by
  obtain ⟨C, hC, hloop⟩ :=
    exists_forall_integral_associatedBilinForm_le_mul_integral (fun t ↦ (hJ t).tames) hJc hSc hdet
  refine ⟨1 + C, by positivity, fun ξ hξ hper a b hab ha hb ↦ ?_⟩
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv (by norm_num)
  set w : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)
  have hw : Continuous w :=
    (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  have hs : Continuous fun z ↦ fderiv ℝ ξ z stdComplexLineReal := hdξ.clm_apply continuous_const
  have hg0 (t : ℝ) (v : V) : 0 ≤ ω.associatedBilinForm (J t) v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((hJ t).associated_pos hv).le
  -- The energy identity, whose boundary slices vanish.
  have hid := setIntegral_associatedBilinForm_stationaryCylinderOperator
    (fun t ↦ (hJ t).invariant) hJc hS hSc hξ hper hab
  simp only [ha, hb, map_zero, intervalIntegral.integral_zero, sub_zero, add_zero] at hid
  -- On each slice, the loop estimate bounds `∫ g(ξ, ξ)` by `C ∫ g(w, w)`.
  have hslice (s : ℝ) : ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (ξ (s, t)) (ξ (s, t)) ≤
      C * ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (w (s, t)) (w (s, t)) := by
    have hd (t : ℝ) : HasDerivAt (fun t ↦ ξ (s, t)) (S t (ξ (s, t)) + w (s, t)) t := by
      have h := (hξ.differentiable (by norm_num) (s, t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_prodMk_right s t)
      simpa only [w, stdComplexLineImag_eq, add_sub_cancel, Function.comp_def] using h
    have h := hloop (hw.comp (Continuous.prodMk_right s)) hd (by simpa using hper s 0)
    simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      Function.comp_def] using h
  have hQ := integrableOn_rect_associatedBilinForm (ω := ω) hJc hξ.continuous a b
  have hW := integrableOn_rect_associatedBilinForm (ω := ω) hJc hw a b
  have hP := integrableOn_rect_associatedBilinForm (ω := ω) hJc hs a b
  have hfub : ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (ξ z) (ξ z) ≤
      C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (w z) (w z) :=
    setIntegral_rect_le_mul_of_forall_setIntegral_le hQ hW fun s _ ↦ hslice s
  -- Hence `∫ (g(∂s ξ) + g(w)) + ∫ g(ξ) ≤ (1 + C) ∫ (g(∂s ξ) + g(w)) = (1 + C) ∫ g(D ξ)`.
  have hW' : ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (w z) (w z) ≤
      ∫ z in Icc a b ×ˢ Icc 0 1, (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) + ω.associatedBilinForm (J z.2) (w z) (w z)) :=
    setIntegral_mono hW (hP.add hW) fun z ↦ le_add_of_nonneg_left (hg0 _ _)
  have hsplit := integral_add (hP.add hW) hQ
  simp only [Pi.add_apply, w] at hsplit hfub hW'
  rw [hsplit, hid]
  linarith [mul_le_mul_of_nonneg_left hW' hC]

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The cylinder estimate at a nondegenerate Hamiltonian orbit.** Let `x` be a one-periodic
orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field
is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t`
be `ω`-compatible complex structures depending continuously on `t`. Then the stationary cylinder
operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` along `x`, with `S_t = dX_{H_t}(x(t))`, satisfies the
estimate of `Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → AlmostComplexStructure V} (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z) := by
  have hSc : Continuous fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) :=
    ω.continuous_fderiv_hamiltonianVectorField_comp hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
  have hSp : Periodic (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 :=
    fun t ↦ by simp only [hHp t, hxp t]
  -- Nondegeneracy rules out a periodic kernel element, hence a fixed vector of `Ψ(1)`.
  have hdet : LinearMap.det ((1 - dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠
      0 := by
    intro h
    obtain ⟨ζ, hζ, hζp, hne, hA⟩ :=
      (Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero (J := J) hSc hSp).2 h
    exact hne ((isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero ω hX hH
      hHp hx hxp J).1 hnd ζ hζ hζp hA)
  exact Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) hJ hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt) hSc hdet

end SymplecticForm

end TauCeti
