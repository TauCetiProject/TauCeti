/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Geometry.Symplectic.Floer.EndLinearization

/-!
# The linearized Floer operator is asymptotic to its end models

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator along a map `u`
of the cylinder, for Floer data that are cylindrical near the ends: equal to `(J₋_t, 0, H₋_t)` for
`s ≤ -R` and to `(J₊_t, 0, H₊_t)` for `s ≥ R`, with the loops of `u` converging uniformly to
orbits `x₋` of `H₋` at `-∞` and `x₊` of `H₊` at `+∞`, and with the slice defects
`∂t u - X_{H±_t}(u)` tending uniformly to zero there. Floer trajectories (`K = H_t dt`) are the
case `R = 0`, and continuation cylinders the case `R = 1`.

Far out on each end, the coefficient field of `D_u` on jets is uniformly close to that of the
linearization `∂s + J±_t(x±(t)) (∂t - dX_{H±_t}(x±(t)))` at the stationary cylinder
`(s, t) ↦ x±(t)` over the asymptotic orbit
(`TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_lt_atBot`,
`TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_lt_atTop`). This is the
convergence of the linearized operator on an end to the stationary cylinder operator
(`TauCeti.SymplecticForm.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le`),
read on the jets of affine sections, which realize every jet.

In a unitary trivialization, where the complex structure is constant, the Fredholm property of
`D_u` follows from a parametrix built from the invertible end models without these slice-defect
hypotheses (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical` in
`TauCeti.Geometry.Symplectic.Floer.Sobolev.Parametrix`). For a general loop of compatible
structures `J_t(y)` the principal part `∂s + J(z, u z) ∂t` of `D_u` differs from those of its end
models, so the parametrix theorem does not apply directly; the Fredholm property for such
structures follows instead by deforming them to `i`
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible` in
`TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J₀ ∂t + S(s, t)` between
  nondegenerate asymptotic operators.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (jet jet_apply stripMeasure)

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- If at a point `z` the linearized operator along `u` differs from a stationary cylinder operator
by at most `ε (‖∂t ξ‖ + ‖ξ‖)` on every section `ξ`, then their coefficient fields on jets are within
`2 ε` at `z`: every jet at `z` is the jet of an affine section. -/
private theorem norm_floerJetCoeff_sub_stationaryJetCoeff_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {Jx : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {z : ℝ × ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ ξ : ℝ × ℝ → V, ‖ω.floerLinearization J Ks Kt u ξ z -
      Floer.stationaryCylinderOperator Jx S ξ z‖ ≤
        ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) :
    ‖ω.floerJetCoeff J Ks Kt u z - Floer.stationaryJetCoeff Jx S z‖ ≤ 2 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- The affine section `w ↦ v.1 + (w.1 - z.1) v_s + (w.2 - z.2) v_t` has jet `v` at `z`.
  set L : ℝ × ℝ →L[ℝ] V := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v.2.1 +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v.2.2
  set ξ : ℝ × ℝ → V := fun w ↦ v.1 + L (w - z)
  have hL : HasFDerivAt ξ L z :=
    ((L.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const z)).const_add v.1).congr_fderiv
      (L.comp_id)
  have hjet : jet ξ z = v := by
    rw [jet_apply, hL.fderiv]
    simp [ξ, L]
  have hv := h ξ
  rw [hL.fderiv, stdComplexLineImag_eq, ← floerJetCoeff_jet, ← Floer.stationaryJetCoeff_jet, hjet,
    ← sub_apply] at hv
  simp only [ξ, sub_self, map_zero, add_zero] at hv
  refine hv.trans ?_
  have h₁ : ‖L (0, 1)‖ ≤ ‖v‖ := by
    simpa [L] using (norm_snd_le v.2).trans (norm_snd_le v)
  have h₂ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  nlinarith

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
  filter_upwards [eventually_le_atBot (-R),
    ω.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le hJm hHm isCompact_Icc
      (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt).continuousOn huxm hδm
      (by positivity : 0 < ε / 4)] with s hsR hs t ht
  -- For `s ≤ -R` the data are the end data `(J₋_t, 0, H₋_t)`.
  rw [ω.floerJetCoeff_congr_data u
    (J' := fun w y ↦ (Jm w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
    (Kt' := fun w ↦ Hm w.2) (by simp only [hcyl.almostComplex_eq_of_le_neg (s, t) hsR])
    (hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ absurd h.1 (not_lt.2 hsR))
    (hcyl.hamiltonianT_eq_of_le_neg (s, t) hsR), floerJetCoeff_eq_stationaryJetCoeff ω Jm Hm hxm]
  exact (norm_floerJetCoeff_sub_stationaryJetCoeff_le ω (by positivity) (hs t ht)).trans_lt
    (by linarith)

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
  filter_upwards [eventually_ge_atTop R,
    ω.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le hJp hHp isCompact_Icc
      (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt).continuousOn huxp hδp
      (by positivity : 0 < ε / 4)] with s hsR hs t ht
  -- For `s ≥ R` the data are the end data `(J₊_t, 0, H₊_t)`.
  rw [ω.floerJetCoeff_congr_data u
    (J' := fun w y ↦ (Jp w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
    (Kt' := fun w ↦ Hp w.2) (by simp only [hcyl.almostComplex_eq_of_le (s, t) hsR])
    (hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ absurd h.2 (not_lt.2 hsR))
    (hcyl.hamiltonianT_eq_of_le (s, t) hsR), floerJetCoeff_eq_stationaryJetCoeff ω Jp Hp hxp]
  exact (norm_floerJetCoeff_sub_stationaryJetCoeff_le ω (by positivity) (hs t ht)).trans_lt
    (by linarith)

end General

end TauCeti.SymplecticForm
