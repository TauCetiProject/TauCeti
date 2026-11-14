/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the sign of
the end of `p` at `∞`. Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the whole plane
for uniformly tame almost complex structures `J(z)`, with image in a compact set and finite
energy. This file shows that `u` breaks off a one-periodic orbit `y` of `H` at its end, and that
the energy of `u` is `ε A_H(y) - ∫_ℂ R_K(u)`. These are the planes counted by the
Piunikhin–Salamon–Schwarz maps: positive planes have an input orbit at `∞` and negative planes an
output orbit.

**The end as a Floer half-cylinder.** In the real coordinates `ℝ × ℝ ≃ ℂ` the end lift
`φ(z) = exp (2π ε z)` is the map `ψ = TauCeti.Complex.realChart p.cylindricalEndLift`, which sends
`(s, t)` to `φ(s + i t)`. It is holomorphic, preserves orientation, is `1`-periodic in `t`
(`TauCeti.Floer.PSSPlane.realChart_cylindricalEndLift_add_one`) and is injective on every band of
angular width one (`TauCeti.Floer.PSSPlane.injOn_realChart_cylindricalEndLift`). On the part
`ε s ≥ 2` of the end the perturbation pulls back along `ψ` to `H(t) dt`
(`TauCeti.Floer.PSSPlane.perturbationPullback_realChart_cylindricalEndLift_of_two_le`), so there
`u ∘ ψ` solves the Floer equation `∂_s v + J (∂_t v - X_{H_t}(v)) = 0` of a cylinder
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift`),
and its energy over the band `{ε s ≥ 2} × [0, 1]` is at most the energy of `u`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le`).
The end is the positive half-cylinder `s > 2` on the positive plane and the negative half-cylinder
`s < -2` on the negative plane, and the results of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder` apply to either.

**The orbit at the end.** Write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, as in `TauCeti.Geometry.Symplectic.Floer.Plane.Action`. Then there are a
one-periodic orbit `y` of `X_H` and `R_n → ∞` such that `ℓ_{R_n}` converges uniformly to `y`, and
the actions `A_H(ℓ_R)` tend to `A_H(y)` as `R → ∞`
(`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`).
Hence the energy identity of the plane holds with the action of this orbit
(`TauCeti.SymplecticForm.exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq`):

`E(u) = ε A_H(y) - ∫_ℂ R_K(u)`.

The plane caps its own orbit, so no spherical correction appears on a vector space target.
Without nondegeneracy of the orbits of `H` the orbit is obtained along a sequence `R_n`, while the
convergence of the actions holds along the whole end; convergence of the whole end to a single
orbit is not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics and the energy of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart realChart_apply)
open scoped Topology

namespace TauCeti

namespace Floer.PSSPlane

/-! ### The end lift in real coordinates -/

/-- In the real coordinates the end lift sends `(s, t)` to `φ(s + i t)`. -/
theorem realChart_cylindricalEndLift_mk (p : PSSPlane) (s t : ℝ) :
    realChart p.cylindricalEndLift (s, t) =
      Complex.equivRealProdCLM (p.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  rw [realChart_apply]
  congr 2
  apply Complex.ext <;> simp

/-- The end lift in real coordinates is `1`-periodic in the angular coordinate. -/
theorem realChart_cylindricalEndLift_add_one (p : PSSPlane) (s t : ℝ) :
    realChart p.cylindricalEndLift (s, t + 1) = realChart p.cylindricalEndLift (s, t) := by
  rw [realChart_cylindricalEndLift_mk, realChart_cylindricalEndLift_mk]
  exact congrArg Complex.equivRealProdCLM (p.periodic_cylindricalEndLift s t)

/-- **The perturbation is `H(t) dt` far out on the end, in real coordinates.** On the part
`ε s ≥ 2` of the end, the pullback of the perturbation along the end lift in real coordinates sends
a tangent vector `v = (σ, τ)` of the cylinder to `τ H(t)`. -/
theorem perturbationPullback_realChart_cylindricalEndLift_of_two_le {X : Type*} (p : PSSPlane)
    {H : ℝ → X → ℝ} (hH : Periodic H 1) {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1) (v : ℝ × ℝ)
    (x : X) :
    perturbationPullback (realChart p.cylindricalEndLift)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ x =
      v.2 * H ζ.2 x := by
  have hζ' : Complex.equivRealProdCLM.symm ζ = ⟨ζ.1, ζ.2⟩ := Complex.ext (by simp) (by simp)
  rw [perturbationPullback_realChart _ (p.hasDerivAt_cylindricalEndLift _),
    ← deriv_cylindricalEndLift, perturbation_cylindricalEndLift_of_two_le hH (by rwa [hζ']) x]
  simp [hζ']

end Floer.PSSPlane

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}
  {p : PSSPlane} {H : ℝ → V → ℝ}

omit [FiniteDimensional ℝ V] in
/-- On the part `ε s ≥ 2` of the end, the perturbation is differentiable in the target point. -/
private theorem differentiableAt_perturbation_realChart (hHd : ∀ t, Differentiable ℝ (H t))
    {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1) (v : ℂ) (y : V) :
    DifferentiableAt ℝ (fun x ↦ p.perturbation H
      (Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)) x v) y := by
  have hre : 2 ≤ p.endSign *
      (p.endCoord (Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ))).re := by
    rw [TauCeti.Complex.equivRealProdCLM_symm_realChart, re_endCoord_cylindricalEndLift]
    simpa using hζ
  simp_rw [perturbation_eq_smul_endAngularForm hre, smul_apply, smul_eq_mul]
  exact ((hHd _) y).mul_const _

/-- On the part `ε s ≥ 2` of the end, the perturbed derivative of `u ∘ ψ` for the cylindrical
datum `H(t) dt` is its perturbed derivative for the pulled-back perturbation. -/
private theorem perturbedFDeriv_comp_realChart_eq (hH : Periodic H 1) {u : ℝ × ℝ → V}
    {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ζ =
      ω.perturbedFDeriv
        (perturbationPullback (realChart p.cylindricalEndLift)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (realChart p.cylindricalEndLift)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag)
        (u ∘ realChart p.cylindricalEndLift) ζ :=
  ω.perturbedFDeriv_congr _
    (funext fun x ↦ by
      rw [perturbationPullback_realChart_cylindricalEndLift_of_two_le p hH hζ]
      simp [stdComplexLineReal_eq])
    (funext fun x ↦ by
      rw [perturbationPullback_realChart_cylindricalEndLift_of_two_le p hH hζ]
      simp [stdComplexLineImag_eq])

/-- **The end of a PSS plane solves the Floer equation of a cylinder.** Let `u` solve the Floer
equation `(du - X_K)^{0,1} = 0` of a PSS plane for the almost complex structure `J` at the image
`ψ(ζ)` of a point `ζ` with `ε s ≥ 2` under the end lift `ψ` in real coordinates. Then `u ∘ ψ`
solves the Floer equation `∂_s v + J (∂_t v - X_{H_t}(v)) = 0` of a cylinder at `ζ`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift (hH : Periodic H 1)
    (hHd : ∀ t, Differentiable ℝ (H t)) {u : ℝ × ℝ → V} {J : AlmostComplexStructure V}
    {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1)
    (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ζ :
        ℝ × ℝ →ₗ[ℝ] V) := by
  rw [perturbedFDeriv_comp_realChart_eq hH hζ]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    (Ks := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((TauCeti.Complex.contDiff_realChart (p.contDiff_cylindricalEndLift (n := 1))).differentiable
      one_ne_zero ζ) hu
    (differentiableAt_perturbation_realChart hHd hζ 1 _)
    (differentiableAt_perturbation_realChart hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)) hfloer

/-- **The energy of the end of a PSS plane.** For a set `P` of longitudinal coordinates with
`ε s ≥ 2` on `P`, the energy of `u ∘ ψ` for the cylindrical datum `H(t) dt` over the band
`P × [0, 1]` is at most the energy of `u` over the plane. Here `ψ` is the end lift in real
coordinates. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le (hH : Periodic H 1)
    (hHd : ∀ t, Differentiable ℝ (H t)) {u : ℝ × ℝ → V} (hu : Differentiable ℝ u) {P : Set ℝ}
    (hP : MeasurableSet P) (hP₂ : ∀ s ∈ P, 2 ≤ p.endSign * s) :
    ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart p.cylindricalEndLift) z) ≤
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have hψ : Differentiable ℝ (realChart p.cylindricalEndLift) :=
    (TauCeti.Complex.contDiff_realChart (p.contDiff_cylindricalEndLift (n := 1))).differentiable
      one_ne_zero
  set s : Set (ℝ × ℝ) := P ×ˢ Ico 0 1
  have hs : MeasurableSet s := hP.prod measurableSet_Ico
  -- The closed band differs from the half-open one by a null set.
  have hae : (P ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  -- On the band the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (u ∘ realChart p.cylindricalEndLift) ζ =
        |(fderiv ℝ (realChart p.cylindricalEndLift) ζ).det| *
          ω.floerEnergyDensity (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
            (realChart p.cylindricalEndLift ζ) := by
    intro ζ hζ
    have hζ₂ := hP₂ ζ.1 hζ.1
    rw [floerEnergyDensity_def, perturbedFDeriv_comp_realChart_eq hH hζ₂,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_realChart_cylindricalEndLift_pos p ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (hψ ζ) (hu _) (differentiableAt_perturbation_realChart hHd hζ₂ 1 _)
      (differentiableAt_perturbation_realChart hHd hζ₂ Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    (p.injOn_realChart_cylindricalEndLift fun a ha b hb ↦
      abs_sub_lt_iff.2 ⟨by linarith [ha.2.2, hb.2.1], by linarith [ha.2.1, hb.2.2]⟩)
    (fun ζ _ ↦ hψ ζ) hdens]
  exact setLIntegral_le_lintegral _ _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The loop of `u` along the circle `‖w‖ = exp (2πR)` is the loop of `u ∘ ψ` at `s = ε R`. -/
private theorem endLoop_eq (p : PSSPlane) (u : ℝ × ℝ → V) (R t : ℝ) :
    u (Complex.equivRealProdCLM (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))) =
      (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) := by
  rw [comp_apply, realChart_cylindricalEndLift_mk]

/-- **A finite-energy PSS plane breaks off an orbit at its end.** Let `K` be the perturbation of a
PSS plane given by a period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` map, with image in a
compact set, solving the Floer equation `(du - X_K)^{0,1} = 0` on the whole plane for uniformly
tame almost complex structures, `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖`. If the energy of `u`
is finite, then there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `H` and
`R_n → ∞` such that the loops `ℓ_{R_n}(t) = u(φ(ε R_n + i t))` converge uniformly to `y`, and the
actions `A_H(ℓ_R)` tend to `A_H(y)` as `R → ∞`. Here `φ` is the end lift and `ε` the sign of the
end. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {B : Set V} (hB : IsCompact B) (huB : ∀ z, u z ∈ B) {c M : ℝ} (hc : 0 < c)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJc : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :
          ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) ∧
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * σ n) + ↑t * Complex.I)))) y atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H y)) := by
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  set v := u ∘ realChart p.cylindricalEndLift with hv
  have hvs : ContDiff ℝ 2 v := hu.comp (TauCeti.Complex.contDiff_realChart
    p.contDiff_cylindricalEndLift)
  have hper (s : ℝ) : Periodic (fun t ↦ v (s, t)) 1 := fun t ↦ by
    simp only [hv, comp_apply, realChart_cylindricalEndLift_add_one]
  have hfloer' {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart p.cylindricalEndLift) ζ)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v ζ : ℝ × ℝ →ₗ[ℝ] V) :=
    isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift hH hHd hζ
      ((hu.differentiable two_ne_zero) _) (hfloer _)
  have hE' {P : Set ℝ} (hP : MeasurableSet P) (hP₂ : ∀ s ∈ P, 2 ≤ p.endSign * s) :
      ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal
        (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) ≠ ⊤ :=
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le
      hH hHd (hu.differentiable two_ne_zero) hP hP₂)
  simp_rw [endLoop_eq p u]
  cases p with
  | positive =>
    -- On the positive plane the end is the positive half-cylinder `s > 2`.
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := 2) hHs hH hvs.contDiffOn
        (fun s _ ↦ hper s) hB (fun _ _ _ ↦ huB _) hc (fun z _ ↦ hJc _) (fun z _ ↦ hJM _)
        (fun z hz ↦ hfloer' (by simpa using hz.1.le))
        (hE' measurableSet_Ioi fun s hs ↦ by simpa using (mem_Ioi.1 hs).le)
    refine ⟨x, hxper, hx, ⟨φ, hφ, by simpa only [endSign_positive, one_mul] using hux⟩, ?_⟩
    simpa only [endSign_positive, one_mul] using hA
  | negative =>
    -- On the negative plane the end is the negative half-cylinder `s < -2`.
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer (a := -2) hHs hH
        hvs.contDiffOn (fun s _ ↦ hper s) hB (fun _ _ _ ↦ huB _) hc (fun z _ ↦ hJc _)
        (fun z _ ↦ hJM _)
        (fun z hz ↦ hfloer' (by simp only [endSign_negative]; linarith [mem_Iio.1 hz.1]))
        (hE' measurableSet_Iio fun s hs ↦ by
          simp only [endSign_negative]; linarith [mem_Iio.1 hs])
    refine ⟨x, hxper, hx, ⟨fun n ↦ -φ n, tendsto_neg_atBot_atTop.comp hφ, ?_⟩, ?_⟩
    · simpa only [endSign_negative, neg_mul, one_mul, neg_neg] using hux
    · refine (hA.comp tendsto_neg_atTop_atBot).congr fun R ↦ ?_
      simp only [comp_apply, endSign_negative, neg_mul, one_mul, hv]

/-- **The energy identity of a PSS plane with its asymptotic orbit.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation`,
there is a `1`-periodic orbit `y` of the Hamiltonian vector field of `H` such that

`E(u) = ε A_H(y) - ∫_ℂ R_K(u)`.

The orbit is an asymptotic orbit of `u` at the end: the loops `ℓ_{R_n}(t) = u(φ(ε R_n + i t))`
converge uniformly to `y` along some `R_n → ∞`, and the actions `A_H(ℓ_R)` tend to `A_H(y)` as
`R → ∞`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {B : Set V} (hB : IsCompact B) (huB : ∀ z, u z ∈ B) {c M : ℝ} (hc : 0 < c)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJc : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :
          ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y : ℝ → V, (Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) ∧
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * σ n) + ↑t * Complex.I)))) y atTop) ∧
        Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
          (𝓝 (ω.hamiltonianAction H y))) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H y - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨y, hy⟩ := exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation hH
    hHs hu hB huB hc hJc hJM hfloer hE
  refine ⟨y, hy, ?_⟩
  exact lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu
    (fun z v hv ↦ (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z v)) hfloer
    hy.2.2.2

end SymplecticForm

end TauCeti
