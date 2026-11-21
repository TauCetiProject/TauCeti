/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Regularity
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
public import TauCeti.Geometry.Symplectic.Floer.Translation.Kernel
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# The infinitesimal translation in the Sobolev kernel of the linearized Floer operator

Let `u` be a Floer trajectory of `K = H_t dt` in a symplectic vector space, between nondegenerate
one-periodic orbits, for almost complex structures `J_t` compatible along `u` and along the orbits.
Its data do not depend on `s`, so its translates `u(· + c, ·)` are Floer trajectories as well, and
the infinitesimal translation `∂s u` solves the linearized equation `D_u (∂s u) = 0`
(`TauCeti.SymplecticForm.floerLinearization_fderiv_apply_eq_zero`). This file shows that `∂s u`
is an element of the kernel of the Sobolev realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` (`TauCeti.SymplecticForm.floerSobolevOperator`) as soon
as it is square integrable on the cylinder, as it is for a trajectory of finite energy
(`TauCeti.SymplecticForm.exists_mem_ker_floerSobolevOperator_valueL_eq`). Since `D_u` satisfies the
semi-Fredholm estimate, the jet of `∂s u` is square integrable
(`TauCeti.CylinderSobolev.memLp_jet_of_hasSemiFredholmEstimate`), and
`TauCeti.CylinderSobolev.toLp_jet_mem_H1` places it in `W^{1,2}` although `∂s u` does not vanish
for `|s|` large. For a trajectory that is not stationary, `∂s u` does not vanish identically, so
this element is nonzero and the kernel of `D_u` is nontrivial
(`TauCeti.SymplecticForm.ker_floerSobolevOperator_ne_bot`).

This is the linear shadow of the translation action on Floer trajectories: the tangent line to the
orbit of `u` under translation lies in the kernel of `D_u`, so the moduli spaces of Floer
trajectories are divided by this action before their rigid elements are counted.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. **80** (1995), 251–292.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of the linearized operator along Floer
  trajectories and the translation action.
-/

public section

open Filter Set MeasureTheory Topology
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (jet stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Along a `C³` Floer trajectory of `K = H_t dt`, the infinitesimal translation `∂s u` solves
the linearized equation on its jet: `D_u (∂s u) = 0`. -/
private theorem floerJetCoeff_jet_fderiv_eq_zero (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u)
    (hF : ∀ z, ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0) (z : ℝ × ℝ) :
    ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ H w.2) u z (jet (fun z ↦ fderiv ℝ u z (1, 0)) z) = 0 := by
  have hslice : ContDiff ℝ 2 fun y : V ↦ (z.2, y) := contDiff_const.prodMk contDiff_id
  rw [floerJetCoeff_jet]
  refine floerLinearization_fderiv_apply_eq_zero (v := ((1 : ℝ), (0 : ℝ)))
    (.of_forall fun c ↦ by simp) (.of_forall fun _ ↦ rfl) (.of_forall fun c ↦ by simp)
    ((hJ.comp (hslice.of_le (by norm_num))).differentiable one_ne_zero _) contDiffAt_const
    (hH.comp hslice).contDiffAt (hu.contDiffAt.of_le (by norm_num)) (.of_forall hF)

/-- **The infinitesimal translation lies in the Sobolev kernel of the linearized Floer
operator.** Let `u` be a `C³` Floer trajectory of `K = H_t dt`, of period one in `t`, between
nondegenerate one-periodic orbits `xm` and `xp`, under the hypotheses of the semi-Fredholm
estimate `TauCeti.SymplecticForm.exists_hasSemiFredholmEstimate_floerJetCoeff`. If `∂s u` is
square integrable on the strip, it is the value of an element of the kernel of the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`. -/
theorem exists_mem_ker_floerSobolevOperator_valueL_eq (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {K : ℝ≥0} (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hF : ∀ z, ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hξ : MemLp (fun z ↦ fderiv ℝ u z (1, 0)) 2 stripMeasure) :
    ∃ x ∈ (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).ker,
      valueL x = hξ.toLp fun z ↦ fderiv ℝ u z (1, 0) := by
  have hξd : ContDiff ℝ 2 fun z ↦ fderiv ℝ u z (1, 0) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hξper (s t : ℝ) : fderiv ℝ u (s, t + 1) (1, 0) = fderiv ℝ u (s, t) (1, 0) := by
    rw [fderiv_add_snd_of_periodic_snd hper s t]
  obtain ⟨C, T, hest⟩ := exists_hasSemiFredholmEstimate_floerJetCoeff ω hX hH hxm hndm hxp hndp
    hJ hJxm hJxp (hu.of_le (by norm_num)) hJu huxm huxp hδm hδp
  have hM := ω.memLp_floerJetCoeff hH hJ (hu.of_le (by norm_num)) huxm huxp hδm hδp
  have hD0 := floerJetCoeff_jet_fderiv_eq_zero ω hH hJ hu hF
  have hD : MemLp (fun z ↦ ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z (jet (fun z ↦ fderiv ℝ u z (1, 0)) z)) 2 stripMeasure := by
    simp only [hD0, MemLp.zero']
  have hj := memLp_jet_of_hasSemiFredholmEstimate hM hest hξd hξper hξ hD
  have hmem := toLp_jet_mem_H1 hξd hξper hj
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · -- `D_u` sends the jet of `∂s u` to the class of `D_u (∂s u) = 0`.
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, floerSobolevOperator_def,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    refine Lp.ext ?_
    filter_upwards [coeFn_jetOperator hM (hj.toLp _), hj.coeFn_toLp,
      Lp.coeFn_zero V 2 stripMeasure] with z h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    exact hD0 z
  · -- The value of the jet of `∂s u` is `∂s u`.
    refine Lp.ext ((coeFn_valueL _).trans ?_)
    filter_upwards [hj.coeFn_toLp, hξ.coeFn_toLp] with z h₁ h₂
    simp only [h₁, h₂, StripSobolev.jet_apply]

/-- **The kernel of the linearized Floer operator along a nonstationary trajectory is
nontrivial.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_mem_ker_floerSobolevOperator_valueL_eq`, if `∂s u` does not vanish
identically, the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` has a nonzero kernel,
containing the infinitesimal translation `∂s u`. -/
theorem ker_floerSobolevOperator_ne_bot (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {K : ℝ≥0} (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hF : ∀ z, ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hξ : MemLp (fun z ↦ fderiv ℝ u z (1, 0)) 2 stripMeasure)
    (hne : ∃ z, fderiv ℝ u z (1, 0) ≠ 0) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u).ker ≠ ⊥ := by
  obtain ⟨x, hx, hval⟩ := exists_mem_ker_floerSobolevOperator_valueL_eq ω hX hH hxm hndm hxp hndp
    hJ hJxm hJxp hu hJu hper hF huxm huxp hδm hδp hξ
  intro hbot
  rw [hbot, Submodule.mem_bot] at hx
  rw [hx, map_zero] at hval
  -- The class of `∂s u` vanishes, so `∂s u` vanishes almost everywhere on the strip.
  have hae : (fun z ↦ fderiv ℝ u z (1, 0)) =ᵐ[stripMeasure] 0 := by
    filter_upwards [hξ.coeFn_toLp, Lp.coeFn_zero V 2 stripMeasure] with z h₁ h₂
    rw [← h₁, ← hval, h₂]
  obtain ⟨z, hz⟩ := hne
  refine hz (congrFun (eq_zero_of_ae_eq_zero
    ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const) (fun s t ↦ ?_) hae) z)
  rw [fderiv_add_snd_of_periodic_snd hper s t]

end TauCeti.SymplecticForm
