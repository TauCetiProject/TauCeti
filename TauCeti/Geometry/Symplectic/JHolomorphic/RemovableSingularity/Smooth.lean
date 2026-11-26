/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Geometry.Symplectic.JHolomorphic.Regularity

/-!
# Smooth removal of finite-energy punctures

Let `J` be a target structure on a finite-dimensional real inner product space `V`, of class `C^ℓ`
with `ℓ ≥ 2` on an open set `W`, and let `u` be a finite-energy solution of the Cauchy--Riemann
equation `∂ₜu = J(u) ∂ₛu` on a punctured disc, of class `C³` there, with image in a compact set
`K ⊆ W` on which `J` is a complex structure, uniformly tamed along `u` by a symplectic form `ω`
compatible with the inner product of `V` through a linear complex structure `J₀`, that is
`ω(v, J₀ w) = ⟨v, w⟩`. Then `u` has a limit `q` at the puncture, and the filling of the puncture
by `q` is of class `C^ℓ` on the whole disc and solves the Cauchy--Riemann equation there, the
puncture included (`SymplecticForm.exists_contDiffOn_update_of_finite_energy`). In particular the
filling is smooth when `J` is.

This completes the interior removal of singularities. The filling is a continuous weak solution
with derivative in `Lᵖ` for some `p > 2` near the puncture
(`SymplecticForm.exists_isWeakCauchyRiemannOn_update_of_finite_energy`), so interior elliptic
bootstrapping (`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`) makes it `C^ℓ` there. Away from the
puncture the map is a classical `C¹` solution, hence `C^ℓ` by the same bootstrapping
(`TauCeti.contDiffOn_of_fderiv_apply_I_eq`). The classical equation at the puncture follows from
the weak one, since the filling is `C¹`.

The same holds at the end of a plane. For a finite-energy solution of class `C³` on the exterior
`‖z‖ > R` of a disc, the inverted map `w ↦ u w⁻¹`, filled at `0` with the limit of `u` at
infinity, is of class `C^ℓ` on the disc `‖w‖ < R⁻¹` and solves the equation there
(`SymplecticForm.exists_contDiffOn_update_comp_inv_of_finite_energy`). Hence a finite-energy `C³`
solution on the whole plane extends to a `C^ℓ` map on the Riemann sphere `OnePoint ℂ`, regarded as
a real two-dimensional manifold through its affine and inverted charts
(`SymplecticForm.exists_contMDiff_onePoint_elim_of_finite_energy`). This identifies finite-energy
planes with spheres, the source of the sphere bubbles in Gromov compactness.

## Main results

* `TauCeti.SymplecticForm.exists_contDiffOn_update_of_finite_energy`: removal of a puncture.
* `TauCeti.SymplecticForm.exists_contDiffOn_update_comp_inv_of_finite_energy`: removal of the end
  of a plane.
* `TauCeti.SymplecticForm.exists_contMDiff_onePoint_elim_of_finite_energy`: a finite-energy plane
  extends to a `C^ℓ` map of the sphere.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities, Theorem 4.1.2).
-/

public section

open Complex Filter MeasureTheory Metric OnePoint Set Topology
open scoped Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c : ℝ} {W K : Set V} {ℓ : ℕ∞}

open Classical in
/-- **Removal of singularities.** Let `J` be `C^ℓ`, `ℓ ≥ 2`, on an open set `W`. A finite-energy
solution `u` of `∂ₜu = J(u) ∂ₛu` on the punctured disc `0 < ‖z - z₀‖ < R`, of class `C³` there,
with image in a compact set `K ⊆ W` on which `J² = -1`, and with `J(u)` uniformly tamed by a
symplectic form `ω` compatible with the inner product through a linear complex structure `J₀`
(`ω(v, J₀ w) = ⟨v, w⟩`), has a limit `q ∈ K` at `z₀`. Its filling by `q` takes values in `K`, is
of class `C^ℓ` on the whole disc `‖z - z₀‖ < R`, and solves `∂ₜu = J(u) ∂ₛu` at every point of
it, including `z₀`. -/
theorem exists_contDiffOn_update_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ContDiffOn ℝ ℓ (Function.update u z₀ q) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R, fderiv ℝ (Function.update u z₀ q) z I =
        J (Function.update u z₀ q z) (fderiv ℝ (Function.update u z₀ q) z 1) := by
  have hℓ2 : (2 : WithTop ℕ∞) ≤ ℓ := by simpa using WithTop.coe_le_coe.2 hℓ
  obtain ⟨q, hq, hlim, hmaps, ε, hε, hεR, p, hp, hweak⟩ :=
    ω.exists_isWeakCauchyRiemannOn_update_of_finite_energy hg hc hR hW (hJ.of_le hℓ2) hK hKW
      hJsq hu hCR huK htame henergy
  set v := Function.update u z₀ q
  set D : Set ℂ := ball z₀ R \ {z₀}
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_singleton
  have hvu : EqOn v u D := fun z hz ↦ Function.update_of_ne hz.2 _ _
  -- Away from the puncture `u` is a classical solution, hence `C^ℓ`.
  have hvD : ContDiffOn ℝ ℓ v D :=
    (contDiffOn_of_fderiv_apply_I_eq hD hW hJ (hu.of_le (by norm_num)) (huK.mono_right hKW)
      (fun z hz ↦ hJsq _ (huK hz)) hCR).congr hvu
  -- Near the puncture the filling is a weak solution, hence `C^ℓ` by bootstrapping.
  have hvε : ContDiffOn ℝ ℓ v (ball z₀ ε) :=
    contDiffOn_of_isWeakCauchyRiemannOn_of_sq_eq_neg_one (Ω := ⟨ball z₀ ε, isOpen_ball⟩)
      (by simpa using hp) hW hJ (fun z hz ↦ hKW (hmaps (ball_subset_ball hεR.le hz)))
      (fun z hz ↦ hJsq _ (hmaps (ball_subset_ball hεR.le hz))) hweak
  have hvR : ContDiffOn ℝ ℓ v (ball z₀ R) := by
    refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
    rcases eq_or_ne z z₀ with rfl | hz₀
    · exact ⟨ball z ε, isOpen_ball, mem_ball_self hε, hvε.mono inter_subset_right⟩
    · exact ⟨D, hD, ⟨hz, hz₀⟩, hvD.mono inter_subset_right⟩
  refine ⟨q, hq, hlim, hmaps, hvR, fun z hz ↦ ?_⟩
  rcases eq_or_ne z z₀ with rfl | hz₀
  · -- At the puncture, the weak equation for the `C¹` filling is the classical one.
    have hJv := hJsq _ (hmaps hz)
    have hcl := (isWeakCauchyRiemannOn_iff_of_contDiffOn (Ω := ⟨ball z ε, isOpen_ball⟩)
      (hvε.of_le (le_trans (by norm_num) hℓ2))
      ((hJ.continuousOn.comp (hvε.continuousOn) fun w hw ↦
        hKW (hmaps (ball_subset_ball hεR.le hw))))
      continuousOn_const).1 hweak z (mem_ball_self hε)
    have h := congrArg (J (v z)) hcl
    simp only [Pi.zero_apply, map_add, hJv, map_zero] at h
    exact (add_neg_eq_zero.1 h).symm
  · -- Away from it, `v` agrees with `u` near `z`.
    have heq : v =ᶠ[𝓝 z] u := Filter.eventuallyEq_of_mem (hD.mem_nhds ⟨hz, hz₀⟩) hvu
    rw [heq.fderiv_eq, Function.update_of_ne hz₀]
    exact hCR z ⟨hz, hz₀⟩

open Classical in
/-- **Removal of the end of a plane.** Let `J` be `C^ℓ`, `ℓ ≥ 2`, on an open set `W`. For a
finite-energy solution `u` of `∂ₜu = J(u) ∂ₛu` on the exterior `‖z‖ > R` of a disc, of class `C³`
there, with image in a compact set `K ⊆ W` on which `J² = -1`, and with `J(u)` uniformly tamed
by a symplectic form `ω` compatible with the inner product through a linear complex structure `J₀`
(`ω(v, J₀ w) = ⟨v, w⟩`), the limit `q ∈ K` of `u` at infinity exists. The inverted map
`w ↦ u w⁻¹`, filled at `0` by `q`, is of class `C^ℓ` on the disc `‖w‖ < R⁻¹` and solves
`∂ₜv = J(v) ∂ₛv` at every point of it. This is the chart of the Riemann sphere at the point at
infinity of the plane. -/
theorem exists_contDiffOn_update_comp_inv_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (closedBall 0 R)ᶜ K)
    (htame : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    ∃ q ∈ K, Tendsto u (cocompact ℂ) (𝓝 q) ∧
      ContDiffOn ℝ ℓ (Function.update (fun w ↦ u w⁻¹) 0 q) (ball 0 R⁻¹) ∧
      ∀ w ∈ ball (0 : ℂ) R⁻¹, fderiv ℝ (Function.update (fun w ↦ u w⁻¹) 0 q) w I =
        J (Function.update (fun w ↦ u w⁻¹) 0 q w)
          (fderiv ℝ (Function.update (fun w ↦ u w⁻¹) 0 q) w 1) := by
  -- For `R ≤ 0` the disc `‖w‖ < R⁻¹` is empty, and only the limit at infinity remains.
  rcases le_or_gt R 0 with hR | hR
  · obtain ⟨q, hq, hlim⟩ := ω.exists_tendsto_cocompact_of_finite_energy hg hc hW
      (hJ.of_le (by simpa using WithTop.coe_le_coe.2 hℓ)) hK hKW hJsq hu hCR huK htame henergy
    have hb : ball (0 : ℂ) R⁻¹ = ∅ := ball_eq_empty.2 (inv_nonpos.2 hR)
    exact ⟨q, hq, hlim, by simp [hb], by simp [hb]⟩
  have hDE := mapsTo_inv_ball_diff_singleton_compl_closedBall (𝕜 := ℂ) R
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  -- The inverted map is a finite-energy solution on the punctured disc of radius `R⁻¹`.
  obtain ⟨q, hq, hlim, -, hcont, hCR'⟩ :=
    ω.exists_contDiffOn_update_of_finite_energy hℓ hg hc (inv_pos.2 hR) hW hJ hK hKW hJsq
      (hu.comp ((contDiffOn_inv ℝ).mono fun w hw ↦ hw.2) hDE)
      (fun w hw ↦ fderiv_comp_inv_apply_I_eq hw.2 (hCR _ (hDE hw)) (hJsq _ (huK (hDE hw))))
      (huK.comp hDE) (fun w hw ↦ htame _ (hDE hw))
      (integrableOn_norm_fderiv_comp_inv_apply_one_sq hCR (fun z hz ↦ hM _ (huK hz)) henergy)
  refine ⟨q, hq, ?_, hcont, hCR'⟩
  rw [← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using hlim.comp tendsto_inv₀_cobounded'

/-- **Finite-energy planes extend to spheres.** Let `J` be `C^ℓ`, `ℓ ≥ 2`, on an open set `W`. A
finite-energy `C³` solution `u` of `∂ₜu = J(u) ∂ₛu` on the whole plane, with image in a compact set
`K ⊆ W` on which `J² = -1`, and with `J(u)` uniformly tamed by a symplectic form `ω` compatible
with the inner product through a linear complex structure `J₀` (`ω(v, J₀ w) = ⟨v, w⟩`), extends
to a map of class `C^ℓ` on the Riemann sphere `OnePoint ℂ`, sending the point at infinity to a
point `q ∈ K`. -/
theorem exists_contMDiff_onePoint_elim_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hu : ContDiff ℝ 3 u)
    (hCR : ∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (huK : ∀ z, u z ∈ K)
    (htame : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : Integrable (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2)) :
    ∃ q ∈ K, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, V) ℓ (fun x : OnePoint ℂ ↦ x.elim q u) := by
  classical
  obtain ⟨q, hqK, -, hinf, -⟩ := ω.exists_contDiffOn_update_comp_inv_of_finite_energy (R := 1) hℓ
    hg hc hW hJ hK hKW hJsq hu.contDiffOn (fun z _ ↦ hCR z) (fun z _ ↦ huK z)
    (fun z _ ↦ htame z) henergy.integrableOn
  -- On the plane `u` is a classical solution, hence `C^ℓ`.
  have hfin : ContDiff ℝ ℓ u := contDiffOn_univ.1 <|
    contDiffOn_of_fderiv_apply_I_eq isOpen_univ hW hJ (hu.contDiffOn.of_le (by norm_num))
      (fun z _ ↦ hKW (huK z)) (fun z _ ↦ hJsq _ (huK z)) fun z _ ↦ hCR z
  refine ⟨q, hqK, fun x ↦ ?_⟩
  induction x using OnePoint.rec with
  | coe z =>
    -- In the affine chart the extension is `u`.
    refine (hfin.contDiffAt.comp_contMDiffAt
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (x := (z : OnePoint ℂ)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (coe_ne_infty z)] with y hy
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hy
    | coe w => simp
  | infty =>
    -- In the inverted chart the extension is the filled inverted map.
    have h0 : ContDiffAt ℝ ℓ (Function.update (fun w ↦ u w⁻¹) 0 q)
        (extChartAt 𝓘(ℝ, ℂ) (∞ : OnePoint ℂ) ∞) := by
      simpa using hinf.contDiffAt (ball_mem_nhds 0 (by norm_num))
    refine (h0.comp_contMDiffAt
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (x := (∞ : OnePoint ℂ)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (infty_ne_coe 0)] with y hy
    induction y using OnePoint.rec with
    | infty => simp
    | coe w =>
      have hw : w ≠ 0 := fun h ↦ hy (by simp [h])
      simp [invChart_coe, hw]

end TauCeti.SymplecticForm
