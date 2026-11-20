/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane in a manifold

This file proves the breaking of `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic` for a PSS
plane in a manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic manifold,
with the perturbation `𝔎` of a PSS plane `p` built from a period-one `C¹` Hamiltonian `H` on `M`.
Let `ε = ±1` be the sign of the end of `p` at `∞`, let `φ(z) = exp (2π ε z)` be the end lift, and
for `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`. Let `u` be `C¹` on a part `‖w‖ > r` of the end, with image in a compact set `K`,
solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)` on
the tangent spaces `T_{u(z)} M`, with finite energy there. Convergence and tameness are measured
through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on `K` with
injective differential at the points of `K`, as in the manifold half-cylinder theorem of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`: `c ‖d e v‖² ≤ ω(v, J(z) v)`. Then there
are a one-periodic orbit `x` of the Hamiltonian vector field in `K`, an element of
`TauCeti.periodicSolutions`, and radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge to `x`,
pointwise in `M` and uniformly after applying `e`
(`exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact` in
`TauCeti.SmoothTwoForm.IsNondegenerate`, with a closed-manifold corollary).

Under two further assumptions the loops converge for all `R → ∞`, not only along a sequence: if
the derivative of `e ∘ u ∘ φ` in the end coordinates `(s, t)` is bounded on the strip `ε s > b`,
`0 ≤ t ≤ 1` of the end and the one-periodic orbits in `K` are isolated, then `ℓ_R → x` for a
single orbit `x`
(`exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation_of_isCompact`). On a
compact boundaryless manifold, for a `C²` Hamiltonian all of whose one-periodic orbits are
nondegenerate, the orbits are isolated, so the end of a finite-energy PSS plane with bounded
derivative in end coordinates converges to one nondegenerate orbit
(`exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation`). These are the PSS
counterparts of the whole-end theorems for half-cylinders in
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`,
`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` and
`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`.

The proof is the one for a vector-space target: the Floer equation and the energy pull back along
the end lift
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive` and
`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_le`), the manifold
half-cylinder theorem applies on the positive plane, and on the negative plane the orbit of
`-H(-t)` is run backwards
(`TauCeti.SmoothTwoForm.comp_neg_mem_periodicSolutions_hamiltonianVectorField_iff`). The
convergence of the capped end actions and the energy identity at the orbit `x` are in
`TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Energy`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm

open Floer Floer.PSSPlane

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}

/-- **Translations preserve the energy.** Translating the map and the perturbation data by `v`
preserves the energy: the energy of the translate over `(· + v) ⁻¹' S` is the energy of the
original over `S`. -/
theorem lintegral_floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + v) ⁻¹' S, ENNReal.ofReal
        (ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [floerEnergyDensity_comp_add_right]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight v)
    (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)) S

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- A map differentiable on the part `‖w‖ > exp (2πa)` of the plane is differentiable at the image
under the end lift of the positive plane of every point of the half-cylinder `s > a`. -/
private theorem mdifferentiableAt_realChart_positive {a : ℝ}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {z : ℝ × ℝ} (hz : a < z.1) :
    MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart positive.cylindricalEndLift z) :=
  hu.mdifferentiableAt <| (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (exp_lt_norm_realChart_positive hz)

/-- From `s = 2` on, the pullback of the datum of the positive plane along its end lift is the
cylindrical datum `H(t) dt`, so the Floer operators of the two data agree there. -/
private theorem perturbedMFDeriv_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (u : ℝ × ℝ → M) {z : ℝ × ℝ} (hz : 2 ≤ z.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.perturbedMFDeriv
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) u z := by
  rw [positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal H,
    positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag hH]
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedMFDeriv_apply, endSign_positive, one_mul,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ z.1 - 1)]

/-- **The Floer equation on the end of the positive plane in a manifold.** From `s = 2` on, if `u`
solves the Floer equation for the datum of the positive plane and an almost complex structure `J`
on the tangent space at the image of `(s, t)` under the end lift `φ`, then `u ∘ φ` solves the Floer
equation at `(s, t)` for the cylindrical datum `H(t) dt` and the same structure `J`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {z : ℝ × ℝ}
    (hz : 2 ≤ z.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart positive.cylindricalEndLift z))
    {J : AlmostComplexStructure (TangentSpace I (u (realChart positive.cylindricalEndLift z)))}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (realChart positive.cylindricalEndLift z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z).toLinearMap := by
  rw [perturbedMFDeriv_comp_realChart_positive ω hH _ hz]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (mdifferentiableAt_perturbation_target hH hHs _ _ 1)
    (mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I)
    (isComplexLinearMap_fderiv_realChart (positive.hasDerivAt_cylindricalEndLift _)) hfloer

/-- From `s = 2` on, where `u` is differentiable at the image of `(s, t)` under the end lift `φ`
of the positive plane, the energy density of `u ∘ φ` at `(s, t)` for the cylindrical datum
`H(t) dt` is the Jacobian of `φ` times the energy density of `u` for the datum of the plane. -/
private theorem floerEnergyDensity_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {z : ℝ × ℝ}
    (hz : 2 ≤ z.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart positive.cylindricalEndLift z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z =
      (fderiv ℝ (realChart positive.cylindricalEndLift) z).det *
        ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          (realChart positive.cylindricalEndLift z) := by
  rw [floerEnergyDensity_def, perturbedMFDeriv_comp_realChart_positive ω hH _ hz,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (mdifferentiableAt_perturbation_target hH hHs _ _ 1)
    (mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I)

/-- **The energy on the end of the positive plane in a manifold.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` on
the half-cylinder `s > a`, `0 ≤ t ≤ 1`, for the cylindrical datum `H(t) dt`, is at most the energy
of `u` on that part of the plane: the end lift `φ` is injective on the half-strip `0 ≤ t < 1` and
preserves orientation. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {a : ℝ}
    (ha : 2 ≤ a)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) :=
  setLIntegral_ofReal_comp_realChart_positive_le fun _ hz ↦
    floerEnergyDensity_comp_realChart_positive ω hH hHs (ha.trans hz.1.le)
      (mdifferentiableAt_realChart_positive hu hz.1)

/-- **The energy on part of the end of the positive plane in a manifold.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` for
the cylindrical datum `H(t) dt` over a measurable subset `s` of a half-strip `s > a`,
`t₀ ≤ t < t₀ + 1` of angular width one is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset
    (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {a t₀ : ℝ} (ha : 2 ≤ a)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hst : s ⊆ Ioi a ×ˢ Ico t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) :=
  setLIntegral_ofReal_comp_realChart_positive_le_of_subset hs hst fun _ hz ↦
    floerEnergyDensity_comp_realChart_positive ω hH hHs (ha.trans (hst hz).1.le)
      (mdifferentiableAt_realChart_positive hu (hst hz).1)

/-- **The energy of a translated end of the positive plane in a manifold.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, and the translate `s + (R, 0)`
of a measurable set `s` lies in a half-strip `s > a`, `t₀ ≤ t < t₀ + 1` of angular width one, then
the energy of the translated end `z ↦ u(φ(z + (R, 0)))` for the cylindrical datum `H(t) dt` over
`s` is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le
    (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {a t₀ : ℝ} (ha : 2 ≤ a)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (R : ℝ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hst : ∀ z ∈ s, z + (R, 0) ∈ Ioi a ×ˢ Ico t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun z ↦ u (realChart positive.cylindricalEndLift (z + (R, 0)))) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) := by
  -- The energy of the translated end over `s` is that of `u ∘ φ` over `s + (R, 0)`.
  have h := ω.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2)
    (u ∘ realChart positive.cylindricalEndLift) (R, 0) ((· + ((R, 0) : ℝ × ℝ)) '' s)
  rw [preimage_image_eq _ (add_left_injective _)] at h
  simp only [Prod.snd_add, add_zero, comp_apply] at h
  rw [h]
  exact ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset hH hHs ha hu
    ((measurableEmbedding_addRight _).measurableSet_image' hs)
    (by rintro _ ⟨z, hz, rfl⟩; exact hst z hz)

/-- **The half-cylinder at the end of the positive plane in a manifold.** If `u` is `C¹` on a part
`‖w‖ > r` of the positive plane, solving the Floer equation there for structures `J(z)`, and with
finite energy there, then there is a half-cylinder `s > a` whose image under the end lift `φ` lies
in that part, on which `u ∘ φ` and the structures `J ∘ φ` satisfy the regularity, periodicity,
Floer equation and finite energy hypotheses of the manifold half-cylinder theorem
`exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact` in
`TauCeti.SmoothTwoForm.IsNondegenerate`, for the cylindrical datum `H(t) dt`. -/
private theorem exists_halfCylinder_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ a : ℝ, (∀ z : ℝ × ℝ, a < z.1 →
        r < ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (realChart positive.cylindricalEndLift z))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z).toLinearMap) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ 2`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_two_le_exp_lt_norm_subset r
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ :=
    hsub (exp_lt_norm_realChart_positive hz)
  have hud := (hu.mono hsub).mdifferentiableOn one_ne_zero
  refine ⟨a, fun z hz ↦ hmem hz, (hu.mono hsub).comp
      (contDiff_realChart positive.contDiff_cylindricalEndLift).contMDiff.contMDiffOn
      fun z hz ↦ exp_lt_norm_realChart_positive hz.1,
    fun s _ ↦ ?_, fun z hz ↦ ?_,
    ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le hH hHs ha hud).trans_lt
      ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne⟩
  · simpa only [comp_apply, comp_def, realChart_positive_mk] using
      (positive.periodic_cylindricalEndLift (positive.endSign * s)).comp
        fun w ↦ u (Complex.equivRealProdCLM w)
  · exact ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive hH hHs (ha.trans hz.1.le)
      (mdifferentiableAt_realChart_positive hud hz.1) (hfloer _ (hmem hz.1))

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The asymptotic orbit at the end of the positive plane in a manifold.** This is the case
`p = positive` of `exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact`,
for an arbitrary Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_mem_periodicSolutions_tendstoUniformly_positive
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))))
          (e ∘ x) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) atTop
          (𝓝 (x t)) := by
  obtain ⟨a, hmem, hu', hper, hfloer', hE'⟩ :=
    ω.exists_halfCylinder_comp_realChart_positive hH hHs hu J hfloer hE
  obtain ⟨x, hx, hxK, φ, -, hφ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact hHs hH he hK he_inj
      hde hu' hper (fun s hs t ↦ huK _ (hmem (s, t) hs))
      (fun z ↦ J (realChart positive.cylindricalEndLift z)) hc
      (fun z hz v ↦ hJc _ (hmem z hz.1) v)
      -- The Floer equation for the cylindrical datum, written in coordinates.
      (fun z hz ↦ by
        simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
          (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ _ _ _).1 (hfloer' z hz)) hE'
  simp only [comp_apply, realChart_positive_mk] at hconv hpt
  exact ⟨x, hx, hxK, φ, hφ, hconv, hpt⟩

/-- **Convergence of the end of the positive plane in a manifold to an isolated orbit.** This is
the case `p = positive` of
`exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation_of_isCompact`, for an
arbitrary Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_positive
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → z.2 ∈ Icc 0 1 →
      ‖fderiv ℝ (e ∘ u ∘ realChart positive.cylindricalEndLift) z‖ ≤ C)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ q in 𝓝 (x 0), ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → y 0 = q → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun R t ↦ e (u (Complex.equivRealProdCLM
        (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))))) (e ∘ x)
        atTop ∧
      ∀ t, Tendsto (fun R ↦ u (Complex.equivRealProdCLM
        (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) atTop
        (𝓝 (x t)) := by
  obtain ⟨a, hmem, hu', hper, hfloer', hE'⟩ :=
    ω.exists_halfCylinder_comp_realChart_positive hH hHs hu J hfloer hE
  -- Shrink the half-cylinder so that the derivative bound holds on it as well.
  have ha : a ≤ max a b := le_max_left a b
  have hsub : Ioi (max a b) ×ˢ (univ : Set ℝ) ⊆ Ioi a ×ˢ univ :=
    prod_mono (Ioi_subset_Ioi ha) subset_rfl
  obtain ⟨x, hx, hxK, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated hHs hH he hK
      he_inj hde (hu'.mono hsub) (fun s hs ↦ hper s (ha.trans_lt hs))
      (fun s hs t ↦ huK _ (hmem (s, t) (ha.trans_lt hs)))
      (fun z ↦ J (realChart positive.cylindricalEndLift z)) hc
      (fun z hz v ↦ hJc _ (hmem z (ha.trans_lt hz.1)) v)
      -- The Floer equation for the cylindrical datum, written in coordinates.
      (fun z hz ↦ by
        simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
          (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ _ _ _).1
            (hfloer' z ⟨ha.trans_lt hz.1, hz.2⟩))
      (ne_top_of_le_ne_top hE'
        (lintegral_mono_set (prod_mono (Ioi_subset_Ioi ha) subset_rfl)))
      (fun z hz ↦ hC z ((le_max_right a b).trans_lt hz.1) hz.2) hiso
  simp only [comp_apply, realChart_positive_mk] at hconv hpt
  exact ⟨x, hx, hxK, hconv, hpt⟩

/-- **The asymptotic orbit at the end of a finite-energy PSS plane in a manifold.** Let `ω` be a
nondegenerate two-form on a manifold `M`, and let `𝔎` be the perturbation of a PSS plane `p`
given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of the end, with
image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost
complex structures `J(z)` on the tangent spaces `T_{u(z)} M`, and with finite energy there. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `K` and with
injective differential at the points of `K`, and suppose that the structures are uniformly tame
with respect to `e`: `c ‖d e v‖² ≤ ω(v, J(z) v)` with `c > 0`. Then there is a one-periodic orbit
`x` of the Hamiltonian vector field in `K` such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where
`φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`, converge to `x` along some
`R_n → ∞`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I))))) (e ∘ x) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) atTop (𝓝 (x t)) := by
  cases p
  · exact hω.exists_mem_periodicSolutions_tendstoUniformly_positive hH hHs he hK he_inj hde hu
      huK J hc hJc hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t y ↦ -H (-t) y) :=
    (hHs.comp ((contDiff_neg.contMDiff (n := 1)).prodMap contMDiff_id)).neg
  obtain ⟨y, hy, hyK, R, hR, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_positive (hH.comp_neg.comp Neg.neg) hHs' he
      hK he_inj hde hu huK J hc hJc hfloer hE
  -- Its orbit, run backwards, is an orbit of `H`, and its loops are those of `u`, run backwards.
  refine ⟨fun t ↦ y (-t), (comp_neg_mem_periodicSolutions_hamiltonianVectorField_iff ω H).2 hy,
    fun t ↦ hyK _, R, hR, ?_, fun t ↦ ?_⟩
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hconv.comp fun t ↦ -t
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hpt (-t)

/-- **The asymptotic orbit at the end of a finite-energy PSS plane in a closed manifold.** Let `ω`
be a nondegenerate two-form on a compact manifold `M`, and let `𝔎` be the perturbation of a PSS
plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of the
end, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)`,
and with finite energy there. Let `e : M → F` be a `C¹` injective map with injective differential
into a finite-dimensional normed space, and suppose that the structures are uniformly tame with
respect to `e`: `c ‖d e v‖² ≤ ω(v, J(z) v)` with `c > 0`. Then there is a one-periodic orbit `x`
of the Hamiltonian vector field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the
end lift `p.cylindricalEndLift` and `ε = p.endSign`, converge to `x` along some `R_n → ∞`,
pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation
    [CompactSpace M] (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    (he_inj : Injective e) (hde : ∀ q, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I))))) (e ∘ x) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact p hH hHs he
      isCompact_univ he_inj.injOn (fun q _ ↦ hde q) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE
  exact ⟨x, hx, h⟩

/-- **Convergence of the end of a finite-energy PSS plane in a manifold to an isolated orbit.**
Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact`, suppose
moreover that the derivative of `e ∘ u ∘ φ` in the end coordinates `(s, t)` is bounded on the
strip `ε s > b`, `0 ≤ t ≤ 1` of the end, where `φ` is the end lift `p.cylindricalEndLift` and
`ε = p.endSign`, and that the one-periodic orbits of the Hamiltonian vector field in `K` are
isolated: for each such orbit `x`, no other orbit in `K` starts close to `x 0`. Then the loops
`ℓ_R(t) = u(φ(ε R + i t))` converge, as `R → ∞`, to a single one-periodic orbit `x` in `K`,
pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < p.endSign * z.1 → z.2 ∈ Icc 0 1 →
      ‖fderiv ℝ (e ∘ u ∘ realChart p.cylindricalEndLift) z‖ ≤ C)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ q in 𝓝 (x 0), ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → y 0 = q → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun R t ↦ e (u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun R ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t)) := by
  cases p
  · exact hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_positive hH hHs he hK he_inj hde
      hu huK J hc hJc hfloer hE (fun z hz ↦ hC z (by rwa [endSign_positive, one_mul])) hiso
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t y ↦ -H (-t) y) :=
    (hHs.comp ((contDiff_neg.contMDiff (n := 1)).prodMap contMDiff_id)).neg
  -- In end coordinates the end lift of the negative plane is that of the positive plane after the
  -- reflection `z ↦ -z`, and the loops of the positive plane are `1`-periodic, so the derivative
  -- bound at `(s, t)` is the bound at `(-s, 1 - t)` for the negative plane.
  have hC' (z : ℝ × ℝ) (hz : b < z.1) (ht : z.2 ∈ Icc 0 1) :
      ‖fderiv ℝ (e ∘ u ∘ realChart positive.cylindricalEndLift) z‖ ≤ C := by
    have hper : (fun w ↦ (e ∘ u ∘ realChart positive.cylindricalEndLift) (w + (0, -1))) =
        e ∘ u ∘ realChart positive.cylindricalEndLift := by
      funext ⟨s, t⟩
      simpa only [comp_apply, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg,
        realChart_positive_mk] using congrArg (fun w ↦ e (u (Complex.equivRealProdCLM w)))
          ((positive.periodic_cylindricalEndLift (positive.endSign * s)).sub_eq t)
    have h : e ∘ u ∘ realChart positive.cylindricalEndLift =
        fun w ↦ (e ∘ u ∘ realChart negative.cylindricalEndLift) ((-1 : ℝ) • w) := by
      funext w
      simp [TauCeti.Complex.realChart_apply, cylindricalEndLift_negative]
    rw [← hper, fderiv_comp_add_right, h, fderiv_comp_smul, neg_one_smul, norm_neg]
    exact hC _ (by simpa [endSign_negative] using hz) (by simpa using ⟨ht.2, ht.1⟩)
  -- The orbits of `-H(-t)` are those of `H` run backwards, so they are isolated as well.
  have hiso' (y) (hy : y ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (fun x ↦ -H (-t) x)) 1) (hyK : ∀ t, y t ∈ K) :
      ∀ᶠ q in 𝓝 (y 0), ∀ y' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (fun x ↦ -H (-t) x)) 1,
        (∀ t, y' t ∈ K) → y' 0 = q → y' = y := by
    have h := hiso _ ((comp_neg_mem_periodicSolutions_hamiltonianVectorField_iff ω H).2 hy)
      fun t ↦ hyK _
    simp only [neg_zero] at h
    filter_upwards [h] with q hq y' hy' hy'K hy'q
    have h' := hq _ ((comp_neg_mem_periodicSolutions_hamiltonianVectorField_iff ω H).2 hy')
      (fun t ↦ hy'K _) (by simpa only [neg_zero] using hy'q)
    funext t
    simpa only [neg_neg] using congrFun h' (-t)
  obtain ⟨y, hy, hyK, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_positive (hH.comp_neg.comp Neg.neg)
      hHs' he hK he_inj hde hu huK J hc hJc hfloer hE hC' hiso'
  -- Its orbit, run backwards, is an orbit of `H`, and its loops are those of `u`, run backwards.
  refine ⟨fun t ↦ y (-t), (comp_neg_mem_periodicSolutions_hamiltonianVectorField_iff ω H).2 hy,
    fun t ↦ hyK _, ?_, fun t ↦ ?_⟩
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hconv.comp fun t ↦ -t
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hpt (-t)

/-- **Convergence of the end of a finite-energy PSS plane in a closed manifold to a nondegenerate
orbit.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, and let `𝔎` be
the perturbation of a PSS plane `p` given by a period-one `C²` Hamiltonian `H`, all of whose
one-periodic orbits `x` are nondegenerate: `x 0` is a nondegenerate fixed point of the time-one
map. Let `u` be `C¹` on a part `‖w‖ > r` of the end, solving the Floer equation
`(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)`, with finite energy there. Let
`e : M → F` be a `C¹` injective map with injective differential into a finite-dimensional normed
space, suppose that the structures are uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J(z) v)` with `c > 0`, and that the derivative of `e ∘ u ∘ φ` in the end
coordinates `(s, t)` is bounded on the strip `ε s > b`, `0 ≤ t ≤ 1` of the end, where `φ` is the
end lift `p.cylindricalEndLift` and `ε = p.endSign`. Then the loops `ℓ_R(t) = u(φ(ε R + i t))`
converge, as `R → ∞`, to a single one-periodic orbit `x` of the Hamiltonian vector field, pointwise
in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ q, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < p.endSign * z.1 → z.2 ∈ Icc 0 1 →
      ‖fderiv ℝ (e ∘ u ∘ realChart p.cylindricalEndLift) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun R t ↦ e (u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun R ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t)) := by
  -- Nondegenerate orbits are isolated among the orbits.
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_pssPlanePerturbation_of_isCompact p hH
      (hHs.of_le one_le_two) he isCompact_univ he_inj.injOn (fun q _ ↦ hde q) hu
      (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE hC
      (hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq hHs
        fun x hx _ ↦ hnd x hx)
  exact ⟨x, hx, h⟩

end IsNondegenerate

end TauCeti.SmoothTwoForm
