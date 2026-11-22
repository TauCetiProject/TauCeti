/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Geometry.Symplectic.Floer.Linearization.Cylindrical
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# The linearized Floer operator on the cylinder is Fredholm

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator along a map `u`
of the cylinder, for Floer data that are cylindrical near the ends: equal to `(J₋_t, 0, H₋_t)` for
`s ≤ -R` and to `(J₊_t, 0, H₊_t)` for `s ≥ R`, with the loops of `u` converging uniformly to
orbits `x₋` of `H₋` at `-∞` and `x₊` of `H₊` at `+∞`, and with the slice defects
`∂t u - X_{H±_t}(u)` tending uniformly to zero there. Floer trajectories (`K = H_t dt`) are the
case `R = 0`, and continuation cylinders the case `R = 1`. This file proves that `D_u` is
Fredholm when the asymptotic orbits are nondegenerate, in a unitary trivialization.

* **The end models.** Far out on each end, the coefficient field of `D_u` on jets is uniformly
  close to that of the linearization `∂s + J±_t(x±(t)) (∂t - dX_{H±_t}(x±(t)))` at the stationary
  cylinder `(s, t) ↦ x±(t)` over the asymptotic orbit
  (`TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_lt_atBot`,
  `TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_lt_atTop`). Both coefficient
  fields only see the time `t`, the value `y` and the slice velocity `η` of the map, and are
  uniformly continuous in `(t, y, η)` near the jets of the orbit
  (`TauCeti.SymplecticForm.exists_pos_forall_norm_floerJetCoeff_sub_lt`); at the orbit the slice
  defect vanishes, which removes the term with the derivative of `J`.
* **Fredholm in a unitary trivialization.** Let `F` be a finite-dimensional complex inner product
  space with `ω = Im ⟪·, ·⟫` and `J = i` everywhere. Then `D_u` and its two end models share the
  principal part `∂s + i ∂t`, and the end models are invertible at nondegenerate one-periodic
  orbits (`TauCeti.SymplecticForm.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt`).
  The parametrix theorem on the cylinder
  (`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`) therefore makes
  `D_u` Fredholm, for data cylindrical near the ends
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical`) and in particular
  along a Floer trajectory between any two nondegenerate orbits
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator`).

For a general loop of compatible structures `J_t(y)` the principal part `∂s + J(z, u z) ∂t` of
`D_u` differs from those of its end models, so the parametrix theorem does not apply directly; that
case, and the value of the Fredholm index (the relative Conley–Zehnder index `μ(x₋) - μ(x₊)`), are
not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J₀ ∂t + S(s, t)` between
  nondegenerate asymptotic operators.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linearized operator near an orbit.** Let `J_t(y)` be a `C¹` family of endomorphisms, `H`
a jointly `C²` Hamiltonian, `x` an orbit of `X_{H_t}` and `T` a compact set of times. For every
`ε > 0` there is `δ > 0` such that, for the cylindrical datum `K = H_t dt`, the coefficient field
on jets of the linearized operator along any map `u` at a point `z = (s, t)` with `t ∈ T` is within
`ε` of that along the stationary cylinder `(s, t) ↦ x(t)`, as soon as `u z` is within `δ` of
`x(t)` and the slice defect `∂t u - X_{H_t}(u)` at `z` is smaller than `δ`. -/
theorem exists_pos_forall_norm_floerJetCoeff_sub_lt (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} (hJ : ContDiff ℝ 1 (uncurry J)) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) {T : Set ℝ}
    (hT : IsCompact T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (u : ℝ × ℝ → V) (z : ℝ × ℝ), z.2 ∈ T → ‖u z - x z.2‖ < δ →
      ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ < δ →
      ‖ω.floerJetCoeff (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) u z -
        ω.floerJetCoeff (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z‖ <
          ε := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ₁, hδ₁, h₁⟩ :=
    ω.exists_pos_forall_norm_sub_lt_and_norm_cylindricalLinearizationCoeff_sub_lt hJ hH hT
      hxc.continuousOn (half_pos hε)
  -- Near the orbit the Hamiltonian vector field moves by less than `δ₁ / 2`.
  have hX := (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous
  obtain ⟨δ₂, hδ₂, h₂⟩ := hT.exists_pos_forall_dist_lt hxc.continuousOn
    (fun _ _ ↦ hX.continuousAt) (half_pos hδ₁)
  simp only [dist_eq_norm] at h₂
  refine ⟨min δ₂ (δ₁ / 2), by positivity, fun u z hz hu hδ ↦ ?_⟩
  rw [lt_min_iff] at hu hδ
  -- The slice velocity of `u` is within `δ₁` of the velocity `X_{H_t}(x t)` of the orbit.
  have hη : ‖fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (x z.2)‖ <
      δ₁ := by
    rw [sliceDefect_def] at hδ
    rw [stdComplexLineImag_eq, ← add_halves δ₁]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (ω.hamiltonianVectorField (H z.2) (u z)) _).trans_lt
      (add_lt_add hδ.2 (h₂ z.2 hz (u z) hu.1))
  obtain ⟨e₁, e₂⟩ := h₁ z.2 hz (u z) _ (hu.2.trans (half_lt_self hδ₁)) hη
  -- Along the stationary cylinder the slice velocity is `X_{H_t}(x t)`.
  have hdx : fderiv ℝ (fun w : ℝ × ℝ ↦ x w.2) z stdComplexLineImag =
      ω.hamiltonianVectorField (H z.2) (x z.2) := by
    have h := congrFun (sliceDefect_comp_snd_eq_zero
      (X := fun t ↦ ω.hamiltonianVectorField (H t)) hx) z
    rwa [sliceDefect_def, Pi.zero_apply, sub_eq_zero, ← stdComplexLineImag_eq] at h
  simp only [floerJetCoeff_def, floerLinearizationCoeff_eq_cylindricalLinearizationCoeff, hdx]
  exact (norm_firstOrderJetCoeff_sub_le _ _ _ _).trans_lt (by linarith)

variable {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}

/-- **The negative end model.** Let the Floer data be cylindrical near the ends along `u`, with
negative end data `(J₋, H₋)` for a `C¹` family `J₋` and a jointly `C²` Hamiltonian `H₋`, and let
`x₋` be an orbit of `X_{H₋_t}`. If the loops of `u` converge uniformly to `x₋` at `-∞` and the slice
defect `∂t u - X_{H₋_t}(u)` tends uniformly to zero there, then for every `ε > 0` and every
sufficiently negative `s`, the coefficient field of the linearized operator along `u` at `(s, t)`,
`t ∈ [0, 1]`, is within `ε` of that of the linearized operator of the end data along the stationary
cylinder `(s, t) ↦ x₋(t)`. -/
theorem eventually_forall_norm_floerJetCoeff_sub_lt_atBot (ω : SymplecticForm V)
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hHm : ContDiff ℝ 2 (uncurry Hm))
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xm : ℝ → V} (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u (s, t) -
        ω.floerJetCoeff (fun w y ↦ (Jm w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ Hm w.2) (fun w ↦ xm w.2) (s, t)‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := ω.exists_pos_forall_norm_floerJetCoeff_sub_lt
    (J := fun t y ↦ (Jm t y).toLinearMap.toContinuousLinearMap) hJm hHm hxm isCompact_Icc hε
  filter_upwards [eventually_le_atBot (-R), Metric.tendstoUniformlyOn_iff.1 huxm δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hδm δ hδ] with s hsR hu hd t ht
  -- For `s ≤ -R` the data are the end data `(J₋_t, 0, H₋_t)`.
  rw [ω.floerJetCoeff_congr_data u
    (J' := fun w y ↦ (Jm w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
    (Kt' := fun w ↦ Hm w.2) (by simp only [hcyl.almostComplex_eq_of_le_neg (s, t) hsR])
    (hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ absurd h.1 (not_lt.2 hsR))
    (hcyl.hamiltonianT_eq_of_le_neg (s, t) hsR)]
  refine h u (s, t) ht ?_ ?_
  · rw [← dist_eq_norm, dist_comm]
    exact hu t ht
  · simpa only [Pi.zero_apply, dist_zero_left] using hd t ht

/-- **The positive end model.** The counterpart at `+∞` of
`TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_lt_atBot`: for every `ε > 0` and
every sufficiently large `s`, the coefficient field of the linearized operator along `u` at
`(s, t)`, `t ∈ [0, 1]`, is within `ε` of that of the linearized operator of the positive end data
`(J₊_t, 0, H₊_t)` along the stationary cylinder `(s, t) ↦ x₊(t)`. -/
theorem eventually_forall_norm_floerJetCoeff_sub_lt_atTop (ω : SymplecticForm V)
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hHp : ContDiff ℝ 2 (uncurry Hp))
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xp : ℝ → V} (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u (s, t) -
        ω.floerJetCoeff (fun w y ↦ (Jp w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ Hp w.2) (fun w ↦ xp w.2) (s, t)‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := ω.exists_pos_forall_norm_floerJetCoeff_sub_lt
    (J := fun t y ↦ (Jp t y).toLinearMap.toContinuousLinearMap) hJp hHp hxp isCompact_Icc hε
  filter_upwards [eventually_ge_atTop R, Metric.tendstoUniformlyOn_iff.1 huxp δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hδp δ hδ] with s hsR hu hd t ht
  -- For `s ≥ R` the data are the end data `(J₊_t, 0, H₊_t)`.
  rw [ω.floerJetCoeff_congr_data u
    (J' := fun w y ↦ (Jp w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
    (Kt' := fun w ↦ Hp w.2) (by simp only [hcyl.almostComplex_eq_of_le (s, t) hsR])
    (hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ absurd h.2 (not_lt.2 hsR))
    (hcyl.hamiltonianT_eq_of_le (s, t) hsR)]
  refine h u (s, t) ht ?_ ?_
  · rw [← dist_eq_norm, dist_comm]
    exact hu t ht
  · simpa only [Pi.zero_apply, dist_zero_left] using hd t ht

end General

section Unitary

/-! ### The Fredholm property in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized Floer operator is Fredholm for data cylindrical near the ends.** Let `F` be
a finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, with
the complex structure `i` everywhere. Let the Floer data `(i, K_s, K_t)` be cylindrical near the
ends along a `C¹` map `u`, with end data `(i, H₋)` and `(i, H₊)`, for one-periodic, jointly `C³`
Hamiltonians `H±` whose suspended vector fields are globally Lipschitz. Let `x±` be one-periodic
orbits of `H±` with `x±(0)` nondegenerate fixed points of the time-one maps, such that the loops of
`u` converge uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, and the slice defects
`∂t u - X_{H±_t}(u)` tend uniformly to zero at the corresponding end. Then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator is Fredholm. -/
theorem isFredholm_floerSobolevOperator_of_cylindrical (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ}
    {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks
      Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u)
    (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmp : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmp : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpp : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpp : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        Ks Kt u).IsFredholm := by
  have hJ : ContDiff ℝ 1 fun _ : ℝ × F ↦
      (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap :=
    contDiff_const
  have hHm₂ : ContDiff ℝ 2 (uncurry Hm) := hHm.of_le (by norm_num)
  have hHp₂ : ContDiff ℝ 2 (uncurry Hp) := hHp.of_le (by norm_num)
  -- The end models are the linearizations at the stationary cylinders over `x±`.
  have hmodel {H : ℝ → F → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → F}
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) :
      MemLp (ω.floerJetCoeff
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)) ∞ stripMeasure := by
    rw [floerJetCoeff_eq_stationaryJetCoeff ω
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) H hx]
    exact Floer.memLp_stationaryJetCoeff continuous_const
      (ω.continuous_fderiv_hamiltonianVectorField_comp hH
        (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))
  have hDm := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt hXm hHm hHmp hxm hxmp
    hω hndm
  have hDp := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt hXp hHp hHpp hxp hxpp
    hω hndp
  rw [floerSobolevOperator_def] at hDm hDp ⊢
  -- `D_u` and its end models have the principal part `∂s + i ∂t`.
  have hprin {Ks' Kt' : ℝ × ℝ → F → ℝ} {u' : ℝ × ℝ → F} :
      ∀ᵐ z ∂stripMeasure, ∀ a b : F, ω.floerJetCoeff
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks Kt u z (0, a, b) = ω.floerJetCoeff
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks' Kt' u' z (0, a, b) :=
    Eventually.of_forall fun z a b ↦ by simp only [floerJetCoeff_apply, map_zero, add_zero]
  refine isFredholm_jetOperator_comp_subtypeL_of_isInvertible
    (ω.memLp_floerJetCoeff_of_cylindrical hcyl hu hHm₂ hJ huxm hδm hHp₂ hJ huxp hδp)
    (hmodel hHm₂ hxm) (hmodel hHp₂ hxp) hDm hDp hprin hprin (fun ε hε ↦ ?_) (fun ε hε ↦ ?_)
  · -- Far out on the negative end the coefficients are close to those of the negative model.
    obtain ⟨S, hS⟩ := eventually_atBot.1
      (ω.eventually_forall_norm_floerJetCoeff_sub_lt_atBot hcyl hHm₂ hJ hxm huxm hδm hε)
    refine ⟨-S, ?_⟩
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hzS
    exact (hS z.1 (by linarith) z.2 hz.2).le
  · -- Far out on the positive end the coefficients are close to those of the positive model.
    obtain ⟨S, hS⟩ := eventually_atTop.1
      (ω.eventually_forall_norm_floerJetCoeff_sub_lt_atTop hcyl hHp₂ hJ hxp huxp hδp hε)
    refine ⟨S, ?_⟩
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hzS
    exact (hS z.1 hzS.le z.2 hz.2).le

/-- **The linearized Floer operator along a Floer trajectory is Fredholm.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, with the
complex structure `i`, and let `H` be a one-periodic, jointly `C³` Hamiltonian whose suspended
vector field is globally Lipschitz. Let `x₋` and `x₊` be one-periodic orbits of `H`, with `x±(0)`
nondegenerate fixed points of the time-one map, and let `u` be a `C¹` map whose loops converge
uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, with slice defect `∂t u - X_{H_t}(u)` tending
uniformly to zero at both ends. Then the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of
the linearized Floer operator of the datum `K = H_t dt` is Fredholm. The map `u` need not solve the
Floer equation. -/
theorem isFredholm_floerSobolevOperator (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHp : Periodic H 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t) (hxmp : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t) (hxpp : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).IsFredholm :=
  ω.isFredholm_floerSobolevOperator_of_cylindrical hω
    (Floer.isCylindricalNearEnds_comp_snd (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      contDiff_const (hH.of_le (by norm_num)) u) hu hX hH hHp
    hxm hxmp hndm huxm hδm hX hH hHp hxp hxpp hndp huxp hδp

end Unitary

end TauCeti.SymplecticForm
