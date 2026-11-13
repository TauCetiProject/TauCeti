/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The linearized Floer operator on a cylindrical end

Let `(V, ω)` be a symplectic vector space, `H_t` a time-dependent Hamiltonian and `J_t(y)` a
family of almost complex structures. On a cylindrical end of a punctured Floer domain the
perturbation is `K = H_t dt`, and the linearized Floer operator along a map `u` is

`D_u ξ = ∂s ξ + J_t(u) (∂t ξ - dX_{H_t}(u) ξ) + (dJ_t(u) ξ) (∂t u - X_{H_t}(u))`

(`TauCeti.SymplecticForm.floerLinearization` with `Ks = 0`, `Kt = H_t`). At the stationary cylinder
over an orbit `x` this is the translation-invariant operator
`D_x ξ = ∂s ξ + J_t(x) (∂t ξ - dX_{H_t}(x) ξ)`, which is `∂s + A` for the asymptotic operator `A`
(`TauCeti.Floer.stationaryCylinderOperator`). This file shows that along a map `u` whose loops
converge to a loop `x` while the slice defect `∂t u - X_{H_t}(u)` tends to zero, `D_u` converges to
`D_x`, with coefficients converging uniformly in `t` on compact sets: for every `ε > 0`, eventually
along the end

`‖D_u ξ (s, t) - D_x ξ (s, t)‖ ≤ ε (‖∂t ξ (s, t)‖ + ‖ξ (s, t)‖)`

for every `ξ`
(`TauCeti.SymplecticForm.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le`).
Thus on a far enough end, `D_u` is `D_x` plus an operator that is small relative to the `W^{1,p}`
norm. The same holds for the weighted operators: on maps `e^{-δ s} ξ` the operator `D_u` acts as
`D_u - δ` (`TauCeti.SymplecticForm.floerLinearization_exp_smul`), and `D_u - δ` converges in the
same sense to `∂s + A - δ`, the stationary cylinder operator of `dX_{H_t}(x) - δ J_t(x)`
(`SymplecticForm.eventually_norm_floerLinearization_sub_smul_sub_stationaryCylinderOperator_le`).
This is the form in which the Fredholm theory of operators `∂s + A(s)` with invertible limits
applies to the linearized operator at a Floer solution asymptotic to nondegenerate orbits.

The comparison is pointwise
(`TauCeti.SymplecticForm.norm_floerLinearization_sub_stationaryCylinderOperator_le`): the
difference is bounded by the change of `J`, the change of `J dX_H`, and the term `dJ` applied to
the slice defect. No differentiability of `u` or `x`, and no periodicity, is needed. The
convergence of the coefficients uses only continuity of `J`, `dJ` and `dX_H` in `(t, y)`, uniformly
over the compact set of values of `(t, x(t))`.

For a solution of the Floer equation `∂s u + J_t(u)(∂t u - X_{H_t}(u)) = 0` the slice defect is
`J_t(u) ∂s u`, so it tends to zero uniformly whenever `∂s u` does
(`TauCeti.SymplecticForm.tendstoUniformlyOn_sliceDefect_of_floerOperator_eq_zero`).

At a nondegenerate orbit `x` this gives the `L²` estimate of `D_u` on the far part of the end
(`TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`):
there is a set `U` of slices, a neighbourhood of the end, and a constant `C` such that every `C²`
map `ξ` of period one in `t` vanishing on two slices `s = a`, `s = b` with `[a, b] ⊆ U` satisfies

`∫ (|∂s ξ|² + |∂t ξ - S ξ|² + |ξ|²) ≤ C ∫ |D_u ξ|²`

over `[a, b] × [0, 1]`, in the norms `g_t = ω(·, J_t(x(t)) ·)`, uniformly in `a`, `b` and `ξ`. It
follows from the estimate of the stationary cylinder operator
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`),
which survives perturbations that are small relative to `‖∂t ξ‖ + ‖ξ‖`. Together with an interior
estimate on the compact part of the domain, this is the estimate on the ends behind the Fredholm
property of `D_u`; the Sobolev completion and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the linearized operator `∂s + J ∂t + S(s, t)` with
  `S(s, t) → S^±(t)` along a Floer trajectory.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 3.1 on the
  linearized operator, and the chapter on Floer homology.
-/

public section

open Filter Set Topology ContinuousLinearMap
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Pointwise comparison with the stationary cylinder operator.** At a point `z = (s, t)`, the
linearized Floer operator along `u` for the cylindrical datum `K = H_t dt` differs from the
stationary cylinder operator of a loop `x` by at most

`‖J_t(u) - J_t(x)‖ ‖∂t ξ‖ + (‖J_t(u) dX_{H_t}(u) - J_t(x) dX_{H_t}(x)‖ + ‖dJ_t(u)‖ ‖δ‖) ‖ξ‖`,

where all coefficients are evaluated at `u(z)` and `x(t)`, and `δ = ∂t u - X_{H_t}(u)` is the slice
defect of `u` at `z`. -/
theorem norm_floerLinearization_sub_stationaryCylinderOperator_le (ω : SymplecticForm V)
    (J : ℝ → V → AlmostComplexStructure V) (H : ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (x : ℝ → V)
    (z : ℝ × ℝ) :
    ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z -
        Floer.stationaryCylinderOperator (fun t ↦ J t (x t))
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z‖ ≤
      ‖(J z.2 (u z)).toLinearMap.toContinuousLinearMap -
          (J z.2 (x z.2)).toLinearMap.toContinuousLinearMap‖ *
          ‖fderiv ℝ ξ z stdComplexLineImag‖ +
        (‖(J z.2 (u z)).toLinearMap.toContinuousLinearMap ∘L
              fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z) -
            (J z.2 (x z.2)).toLinearMap.toContinuousLinearMap ∘L
              fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2)‖ +
          ‖fderiv ℝ (fun y ↦ (J z.2 y).toLinearMap.toContinuousLinearMap) (u z)‖ *
            ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖) * ‖ξ z‖ := by
  set Ju := (J z.2 (u z)).toLinearMap.toContinuousLinearMap
  set Jx := (J z.2 (x z.2)).toLinearMap.toContinuousLinearMap
  set Su := fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z)
  set Sx := fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2)
  set dJ := fderiv ℝ (fun y ↦ (J z.2 y).toLinearMap.toContinuousLinearMap) (u z)
  set δ := sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z
  set b := fderiv ℝ ξ z stdComplexLineImag
  -- The difference splits into a first-order term, a zeroth-order term and the defect term.
  have hdiff : ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z -
      Floer.stationaryCylinderOperator (fun t ↦ J t (x t))
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z =
      (Ju - Jx) b - (Ju ∘L Su - Jx ∘L Sx) (ξ z) + dJ (ξ z) δ := by
    simp only [Ju, Jx, Su, Sx, dJ, δ, b, floerLinearization_def,
      Floer.stationaryCylinderOperator_def, sliceDefect_def, hamiltonianVectorField_const,
      fderiv_zero, Pi.zero_apply, zero_apply, sub_zero, ← stdComplexLineImag_eq, sub_apply,
      comp_apply, map_sub, LinearMap.coe_toContinuousLinearMap']
    abel
  rw [hdiff]
  calc ‖(Ju - Jx) b - (Ju ∘L Su - Jx ∘L Sx) (ξ z) + dJ (ξ z) δ‖
      ≤ ‖(Ju - Jx) b‖ + ‖(Ju ∘L Su - Jx ∘L Sx) (ξ z)‖ + ‖dJ (ξ z) δ‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖Ju - Jx‖ * ‖b‖ + ‖Ju ∘L Su - Jx ∘L Sx‖ * ‖ξ z‖ + ‖dJ‖ * ‖ξ z‖ * ‖δ‖ := by
        gcongr
        · exact le_opNorm _ _
        · exact le_opNorm _ _
        · exact le_opNorm₂ _ _ _
    _ = _ := by ring

/-- **The linearized Floer operator on an end converges to the stationary cylinder operator.**
Let `J_t(y)` be a `C¹` family of almost complex structures and `H_t(y)` a `C²` Hamiltonian, and let
`u` be a map whose loops `u(s, ·)` converge uniformly on a compact set `T` of times, along a filter
`l` of `s` such as `atTop` for a positive end, to a loop `x` continuous on `T`, while the slice
defect `∂t u - X_{H_t}(u)` converges uniformly to zero on `T`. Then for every `ε > 0`, eventually
along `l`, at every `t ∈ T` and for every `ξ`, the linearized Floer operator along `u` for the
datum `K = H_t dt` differs from the stationary cylinder operator `∂s + J_t(x) (∂t - dX_{H_t}(x))` by
at most `ε (‖∂t ξ‖ + ‖ξ‖)`. -/
theorem eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le
    (ω : SymplecticForm V) {J : ℝ → V → AlmostComplexStructure V} {H : ℝ → V → ℝ}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {T : Set ℝ} (hT : IsCompact T) {x : ℝ → V}
    (hx : ContinuousOn x T) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l T)
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l T)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, ∀ t ∈ T, ∀ ξ : ℝ × ℝ → V,
      ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
            (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ (s, t) -
          Floer.stationaryCylinderOperator (fun t ↦ J t (x t))
            (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ (s, t)‖ ≤
        ε * (‖fderiv ℝ ξ (s, t) stdComplexLineImag‖ + ‖ξ (s, t)‖) := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  -- The three coefficient fields `J`, `J dX_H` and `dJ` are continuous in `(t, y)`.
  have hdJ := (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ Jc (p.1, y)) (g := Prod.snd)
    (n := 0) (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  have hdX := (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ ω.hamiltonianVectorField (H p.1) y)
    (g := Prod.snd) (n := 0) ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).comp
      (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  -- The coefficients along `u` converge uniformly on `T` to those along `x`.
  have hK := hT.image_of_continuousOn ((continuousOn_id' T).prodMk hx)
  have hpair := hu.graph
  have h₁ := Metric.tendstoUniformlyOn_iff.1
    (hK.comp_tendstoUniformlyOn (fun _ _ ↦ hJ.continuous.continuousAt) hpair) ε hε
  have h₂ := Metric.tendstoUniformlyOn_iff.1
    (hK.comp_tendstoUniformlyOn (fun _ _ ↦ (hJ.continuous.clm_comp hdX).continuousAt) hpair)
    (ε / 2) (half_pos hε)
  have h₃ := Metric.tendstoUniformlyOn_iff.1
    (hK.comp_tendstoUniformlyOn (fun _ _ ↦ hdJ.continuousAt) hpair) 1 one_pos
  -- `dJ` is bounded along `x` on the compact set `T`, hence eventually along `u`.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hdJ.continuousOn
  have h₄ := Metric.tendstoUniformlyOn_iff.1 hδ (ε / 2 / (|C| + 1)) (by positivity)
  filter_upwards [h₁, h₂, h₃, h₄] with s hs₁ hs₂ hs₃ hs₄ t ht ξ
  refine (norm_floerLinearization_sub_stationaryCylinderOperator_le ω J H u ξ x (s, t)).trans ?_
  have e₁ := hs₁ t ht
  have e₂ := hs₂ t ht
  have e₃ := hs₃ t ht
  have e₄ := hs₄ t ht
  simp only [dist_eq_norm', Pi.zero_apply, sub_zero, Jc] at e₁ e₂ e₃ e₄
  have hCt := hC _ (mem_image_of_mem _ ht)
  simp only [Jc] at hCt
  have hdJu : ‖fderiv ℝ (fun y ↦ (J t y).toLinearMap.toContinuousLinearMap) (u (s, t))‖ ≤
      |C| + 1 := by
    have := norm_le_insert' (fderiv ℝ (fun y ↦ (J t y).toLinearMap.toContinuousLinearMap)
      (u (s, t))) (fderiv ℝ (fun y ↦ (J t y).toLinearMap.toContinuousLinearMap) (x t))
    linarith [le_abs_self C]
  have hdef : ‖fderiv ℝ (fun y ↦ (J t y).toLinearMap.toContinuousLinearMap) (u (s, t))‖ *
      ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)‖ ≤ ε / 2 := by
    calc _ ≤ (|C| + 1) * (ε / 2 / (|C| + 1)) := by gcongr
      _ = ε / 2 := by field_simp
  nlinarith [norm_nonneg (fderiv ℝ ξ (s, t) stdComplexLineImag), norm_nonneg (ξ (s, t))]

/-- **The weighted linearized operator on an end.** Under the hypotheses of
`eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le`, the operator
`D_u - δ`, which is `D_u` conjugated by the weight `e^{δ s}` (`floerLinearization_exp_smul`),
differs eventually by at most `ε (‖∂t ξ‖ + ‖ξ‖)` from the stationary cylinder operator
`∂s + A - δ` of the linearized field `dX_{H_t}(x) - δ J_t(x)`. -/
theorem eventually_norm_floerLinearization_sub_smul_sub_stationaryCylinderOperator_le
    (ω : SymplecticForm V) {J : ℝ → V → AlmostComplexStructure V} {H : ℝ → V → ℝ}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {T : Set ℝ} (hT : IsCompact T) {x : ℝ → V}
    (hx : ContinuousOn x T) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l T)
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l T)
    (δ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, ∀ t ∈ T, ∀ ξ : ℝ × ℝ → V,
      ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
            (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ (s, t) - δ • ξ (s, t) -
          Floer.stationaryCylinderOperator (fun t ↦ J t (x t))
            (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
              δ • (J t (x t)).toLinearMap.toContinuousLinearMap) ξ (s, t)‖ ≤
        ε * (‖fderiv ℝ ξ (s, t) stdComplexLineImag‖ + ‖ξ (s, t)‖) := by
  filter_upwards [eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le ω hJ hH
    hT hx hu hδ hε] with s hs t ht ξ
  rw [Floer.stationaryCylinderOperator_sub_smul, sub_sub_sub_cancel_right]
  exact hs t ht ξ

/-- **The slice defect of a Floer solution.** On a cylindrical end with datum `K = H_t dt`, a
solution of `∂s u + J_t(u) (∂t u - X_{H_t}(u)) = 0` has slice defect
`∂t u - X_{H_t}(u) = J_t(u) ∂s u`. Hence, if its loops converge uniformly on a compact set `T` of
times to a loop continuous on `T`, and `∂s u` converges uniformly to zero on `T`, then so does the
slice defect. -/
theorem tendstoUniformlyOn_sliceDefect_of_floerOperator_eq_zero (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V} {H : ℝ → V → ℝ}
    (hJ : Continuous fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {T : Set ℝ} (hT : IsCompact T) {x : ℝ → V} (hx : ContinuousOn x T) {l : Filter ℝ}
    {u : ℝ × ℝ → V} (hu : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l T)
    (hF : ∀ᶠ s in l, ∀ t ∈ T,
      ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) u (s, t) = 0)
    (hs : TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineReal) 0 l T) :
    TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l T := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  have hK := hT.image_of_continuousOn ((continuousOn_id' T).prodMk hx)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hJ.continuousOn
  have hM : 0 < |C| + 1 := by positivity
  have h₁ := Metric.tendstoUniformlyOn_iff.1
    (hK.comp_tendstoUniformlyOn (fun _ _ ↦ hJ.continuousAt) hu.graph) 1 one_pos
  rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
  intro ε hε
  filter_upwards [hF, h₁, hs (ε / (|C| + 1)) (by positivity)] with s hsF hs₁ hs₂ t ht
  have e₁ := hs₁ t ht
  have e₂ := hs₂ t ht
  simp only [dist_eq_norm', Pi.zero_apply, sub_zero, Jc] at e₁ e₂ ⊢
  have hCt := hC _ (mem_image_of_mem _ ht)
  simp only [Jc] at hCt
  have hJu : ‖(J t (u (s, t))).toLinearMap.toContinuousLinearMap‖ ≤ |C| + 1 := by
    have := norm_le_insert' ((J t (u (s, t))).toLinearMap.toContinuousLinearMap)
      ((J t (x t)).toLinearMap.toContinuousLinearMap)
    linarith [le_abs_self C]
  -- Applying `J` to the equation `∂s u + J δ = 0` gives `δ = J ∂s u`.
  have hδ : sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t) =
      (J t (u (s, t))).toLinearMap.toContinuousLinearMap
        (fderiv ℝ u (s, t) stdComplexLineReal) := by
    have h := congrArg (J t (u (s, t))) (hsF t ht)
    simp only [floerOperator_def, hamiltonianVectorField_const, Pi.zero_apply, sub_zero,
      LinearMap.coe_toContinuousLinearMap', AlmostComplexStructure.apply_add,
      AlmostComplexStructure.apply_apply, AlmostComplexStructure.apply_zero] at h
    simp only [sliceDefect_def, ← stdComplexLineImag_eq, LinearMap.coe_toContinuousLinearMap']
    exact (add_neg_eq_zero.mp h).symm
  rw [hδ]
  calc _ ≤ ‖(J t (u (s, t))).toLinearMap.toContinuousLinearMap‖ *
        ‖fderiv ℝ u (s, t) stdComplexLineReal‖ := le_opNorm _ _
    _ ≤ (|C| + 1) * ‖fderiv ℝ u (s, t) stdComplexLineReal‖ := by gcongr
    _ < (|C| + 1) * (ε / (|C| + 1)) := by gcongr
    _ = ε := by field_simp

/-- **The `L²` estimate of the linearized operator on an end.** Let `x` be a nondegenerate
one-periodic orbit of a one-periodic, jointly `C²` Hamiltonian `H` whose suspended vector field is
globally Lipschitz, let `J_t(y)` be a `C¹` family of almost complex structures that are
`ω`-compatible along `x`, and let `u` be a map that is `C¹` on the slices `s` eventually along a
filter `l`, whose loops converge uniformly to `x` along `l` while its slice defect
`∂t u - X_{H_t}(u)` tends uniformly to zero, as for a Floer solution on a positive end
(`l = atTop`) or a negative end (`l = atBot`) asymptotic to `x`. Then there are a constant
`C ≥ 0` and a set `U ∈ l` of slices such that every `C²` map `ξ` of period one in `t`, vanishing
on the slices `s = a` and `s = b` with `[a, b] ⊆ U`, satisfies

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D_u ξ, D_u ξ)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`,
`S_t = dX_{H_t}(x(t))` and `g_t = ω(·, J_t(x(t)) ·)`. The constant does not depend on `a`, `b`
or `ξ`. -/
theorem exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hHp : Function.Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Function.Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ t, ω.Compatible (J t (x t))) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 u (s, t))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ U ∈ l, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ U →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))) +
              ω.associatedBilinForm (J z.2 (x z.2)) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2 (x z.2))
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z)
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJxc : Continuous fun p : ℝ × V ↦ J p.1 (x p.1) p.2 :=
    (hJ.continuous.comp (continuous_fst.prodMk (hxc.comp continuous_fst))).clm_apply
      continuous_snd
  -- The stationary cylinder estimate at `x`, and its stability under small perturbations.
  obtain ⟨C₀, hC₀, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator hX hH hHp hx hxp hnd
      hJx hJxc
  obtain ⟨ε, hε, C, hC, hpert⟩ :=
    Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
      (fun t ↦ (hJx t).tames) hJxc (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc) hC₀
  -- Eventually along the end, `D_u` is within `ε (‖∂t ξ‖ + ‖ξ‖)` of the stationary operator.
  refine ⟨C, hC, _, (eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le ω hJ hH
    isCompact_Icc hxc.continuousOn hux hδ hε).and hu,
    fun ξ hξ hper a b hab hU ha hb ↦ hpert (hξ.of_le one_le_two) (hest hξ hper hab ha hb)
      (fun z hz ↦ ?_) fun z hz ↦ (hU hz.1).1 z.2 hz.2 ξ⟩
  -- `D_u ξ` is continuous where `u` is `C¹`.
  exact (ω.continuousAt_floerLinearization
    (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
    contDiffAt_const (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
    ((hU hz.1).2 z.2 hz.2)
    (hξ.contDiffAt.of_le one_le_two)).continuousWithinAt

end TauCeti.SymplecticForm
