/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `p` be a PSS plane, let `ε = ±1` be the sign of its end at `∞`, and let `H` be a period-one
`C¹` Hamiltonian on a symplectic vector space `(V, ω)`. Let `𝔎` be a perturbation that is
`H(t) dt` in end coordinates on the part `ε s ≥ T₀` of the end, as the perturbation
`TauCeti.Floer.PSSPlane.perturbation` given by `H` is for `T₀ = 2`. Let `u` be a solution of the
Floer equation `(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end, for uniformly tame almost
complex structures `J(z)`, with image in a compact set and with finite energy there.
For `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift. This file shows that `u` breaks
off a one-periodic orbit at its end:

* if `u` is `C¹`, there are a one-periodic orbit `x` of the Hamiltonian vector field,
  `x' = X_{H_t}(x)`, and radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`
  (`exists_periodic_hasDerivAt_tendstoUniformly_cylindricalEndLift_of_floer` and
  `exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation` in `TauCeti.SymplecticForm`);
* if `u` is `C²`, there are a one-periodic orbit `x` of the Hamiltonian vector field and radii
  `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`, and the actions `A_H(ℓ_R)`
  tend to `A_H(x)` as `R → ∞`
  (`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer` in
  `TauCeti.SymplecticForm`);
* hence, for the perturbation of a PSS plane and a `C²` solution on the whole plane with finite
  energy, for almost complex structures tamed by `ω` on the whole plane, the energy is
  `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`
  (`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SymplecticForm`).

So `x` is the generator at which a PSS plane meets the Floer complex: an input for the positive
plane, an output for the negative plane. The energy identity of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action` assumed convergence of the end actions; here it
follows from finite energy and compactness.

**The end as a Floer half-cylinder.** In the real coordinates `ℝ × ℝ ≃ ℂ` the end lift is the map
`ψ = TauCeti.Complex.realChart p.cylindricalEndLift`, which sends `(s, t)` to `φ(s + i t)`. It is
holomorphic, preserves orientation, is `1`-periodic in `t` and is injective on every half-open
band `t₀ ≤ t < t₀ + 1` of angular width one. On `ε s ≥ T₀` the perturbation `𝔎` pulls back along
`ψ` to `H(t) dt`
(`TauCeti.Floer.PSSPlane.perturbationPullback_realChart_cylindricalEndLift_of_le`), so `u ∘ ψ`
solves the Floer equation `∂_s v + J (∂_t v - X_{H_t}(v)) = 0` of a cylinder
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift`),
and its energy over a part of `{ε s ≥ T₀}` within a half-open band `t₀ ≤ t < t₀ + 1` is the energy
of `u` over the image
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_eq`).
Hence its energy over a band `P × [0, 1]` with `ε s ≥ T₀` on `P` is at most the energy of `u`
over any set containing the image
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le`).
These pullback results are proved in `TauCeti.Geometry.Symplectic.Floer.Plane.Curvature`. The end
is the positive half-cylinder `s > a` on the positive plane
(`floer_comp_realChart_positive_of_eq_smul_endAngularForm`) and the negative half-cylinder `s < -a`
on the negative plane, for `a ≥ T₀` large (`floer_comp_realChart_cylindricalEndLift`), and the
results of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` apply to either; when `J` is
cylindrical on the end, `u ∘ ψ_+` solves the cylindrical Floer equation for `(Jq, H)` on the
positive plane (`floer_comp_realChart_positive_of_cylindrical`) and for the reversed datum
`(t ↦ Jq (-t), -H(-t))` on the negative plane (`floer_comp_realChart_negative_of_cylindrical`).

Uniform convergence along the entire end under orbit isolation and derivative bounds on cylindrical
ends are proved in `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Convergence`. The case of a
manifold target is treated in `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Manifold`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart realChart_mk contDiff_realChart
  isOpen_setOf_lt_norm_equivRealProdCLM_symm)
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {K : Set V} {p : PSSPlane} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {W : Set (ℝ × V)}
  {Jq : ℝ → V → AlmostComplexStructure V}

/-! ### The end in real coordinates -/

/-- **Pullback of a finite-energy Floer end along `realChart p.cylindricalEndLift`.** Let `𝔎` agree
with `H(t) dt` on the part `ε s ≥ T₀` of the end of `p`. For any `a ≥ T₀` with `r ≤ exp (2πa)`, a
`Cⁿ` (`n ≠ 0`) finite-energy Floer solution `u` on `{‖w‖ > r}` with values in `K` pulls back along
`ψ = realChart p.cylindricalEndLift` to a `Cⁿ` Floer solution on `{ε s > a}` with values in `K` and
finite energy on `P × [0, 1]` for every measurable `P ⊆ {s | a < ε s}`. -/
theorem floer_comp_realChart_cylindricalEndLift (ω : SymplecticForm V) (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContDiffOn ℝ n (u ∘ realChart p.cylindricalEndLift) {z | a < p.endSign * z.1} ∧
      (∀ z, a < p.endSign * z.1 → (u ∘ realChart p.cylindricalEndLift) z ∈ K) ∧
      (∀ z, a < p.endSign * z.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart p.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart p.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∀ P : Set ℝ, MeasurableSet P → (∀ s ∈ P, a < p.endSign * s) →
        ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) z) ≠ ⊤ := by
  have hsub : {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := fun _ hz ↦ hr.trans_lt hz
  have hmem {z : ℝ × ℝ} (hz : a < p.endSign * z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ :=
    p.lt_norm_symm_realChart_cylindricalEndLift_of_le_exp hr hz
  have hdiff {z : ℝ × ℝ} (hz : a < p.endSign * z.1) :
      DifferentiableAt ℝ u (realChart p.cylindricalEndLift z) :=
    (hu.contDiffAt ((isOpen_setOf_lt_norm_equivRealProdCLM_symm r).mem_nhds
      (hmem hz))).differentiableAt hn
  refine ⟨(hu.mono hsub).comp (contDiff_realChart p.contDiff_cylindricalEndLift).contDiffOn
      fun z hz ↦ p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 hz,
    fun z hz ↦ huK _ (hmem hz),
    fun z hz ↦ isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift hKH hH
      (ha.trans hz.le) (hdiff hz) (hHd _ _) (hfloer _ (hmem hz)),
    fun P hP hPa ↦ ?_⟩
  exact ((setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le hKH hH hP
    (fun s hs ↦ ha.trans (hPa s hs).le)
    (U := {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (fun ζ hζ ↦ p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 (hPa _ hζ.1))
    (fun ζ hζ ↦ hdiff (hPa _ hζ.1)) fun _ _ ↦ hHd _ _).trans_lt
      ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne

/-- **Half-cylinder reduction on `(a, ∞)` of the positive plane.** Where `𝔎 = H(t) dt` beyond `T₀`
on the positive plane, for any `a ≥ T₀` with `r ≤ exp (2πa)`, a `Cⁿ` (`n ≠ 0`) finite-energy Floer
solution `u` on `{‖w‖ > r}` with values in `K` pulls back along `φ` to a `Cⁿ`, `1`-periodic,
finite-energy Floer half-cylinder on `(a, ∞) × ℝ` with values in `K`. -/
theorem floer_comp_realChart_positive_of_eq_smul_endAngularForm (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart positive.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  obtain ⟨hv, hvK, hfloer', hE'⟩ := ω.floer_comp_realChart_cylindricalEndLift positive
    (fun w x hw hre ↦ h𝔎 w x hw (by simpa using hre)) hH hHd hn ha hr hu huK hfloer hE
  have hpos {s : ℝ} (hs : a < s) : a < positive.endSign * s := by rwa [endSign_positive, one_mul]
  exact ⟨hv.mono fun z hz ↦ hpos hz.1,
    fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s,
    fun s hs t ↦ hvK (s, t) (hpos hs), fun z hz ↦ hfloer' z (hpos hz.1),
    hE' _ measurableSet_Ioi fun _ hs ↦ hpos hs⟩

/-- **Cylindrical half-cylinder pullback on `(a, ∞)` of the positive plane.** Where `𝔎 = H(t) dt`
and `J(realChart φ_+ (s, t)) = Jq(t, u(realChart φ_+ (s, t)))` for `s ≥ T₀` on the positive plane,
for any `a ≥ T₀` with `r ≤ exp (2πa)`, `u ∘ realChart φ_+` solves the cylindrical Floer equation for
`(Jq, H)` on `(a, ∞) × [0, 1]` with finite energy. -/
theorem floer_comp_realChart_positive_of_cylindrical (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart positive.cylindricalEndLift (s, t)) =
        Jq t (u (realChart positive.cylindricalEndLift (s, t)))) :
    ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq z.2 ((u ∘ realChart positive.cylindricalEndLift) z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH hHd hn ha hr hu huK hfloer hE
  refine ⟨hu', hper', huK', fun z hz ↦ ?_, hE'⟩
  have h := hfloer' z hz
  rwa [comp_apply, hJ z.1 z.2 (ha.trans hz.1.le)] at h

/-- **Cylindrical half-cylinder reduction of the negative plane to the positive plane.** Where
`𝔎 = H(t) dt` and `J(realChart φ_- (ε s, t)) = Jq(t, u(realChart φ_- (ε s, t)))` for `s ≥ T₀` on
the negative plane, `u ∘ realChart φ_+` solves the cylindrical Floer equation for the reversed datum
`(t ↦ Jq (-t), (t, y) ↦ -H (-t) y)` on `(a, ∞) × [0, 1]` whenever `T₀ ≤ a` and `r ≤ exp (2πa)`. -/
theorem floer_comp_realChart_negative_of_cylindrical (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ negative.endSign * (negative.endCoord w).re →
      𝔎 w x = H (negative.endCoord w).im x • negative.endAngularForm w)
    (hH : Periodic H 1) {n : WithTop ℕ∞} (hHs : ContDiff ℝ n (uncurry H)) (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart negative.cylindricalEndLift (negative.endSign * s, t)) =
        Jq t (u (realChart negative.cylindricalEndLift (negative.endSign * s, t)))) :
    Periodic (fun t y ↦ -H (-t) y) 1 ∧
      ContDiff ℝ n (uncurry fun t y ↦ -H (-t) y) ∧
      IsOpen ((fun q : ℝ × V ↦ (-q.1, q.2)) ⁻¹' W) ∧
      ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq (-q.1) q.2).toLinearMap.toContinuousLinearMap)
        ((fun q : ℝ × V ↦ (-q.1, q.2)) ⁻¹' W) ∧
      Periodic (fun t ↦ Jq (-t)) 1 ∧
      univ ×ˢ K ⊆ (fun q : ℝ × V ↦ (-q.1, q.2)) ⁻¹' W ∧
      (∀ t, ∀ x ∈ K, ω.Tames (Jq (-t) x)) ∧
      ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (-z.2) ((u ∘ realChart positive.cylindricalEndLift) z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w y ↦ -H (-w.2) y)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w y ↦ -H (-w.2) y) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  have hH' : Periodic (fun t y ↦ -H (-t) y) 1 := hH.comp_neg.comp Neg.neg
  have hHs' : ContDiff ℝ n (uncurry fun t y ↦ -H (-t) y) := hHs.uncurry_comp_neg.neg
  refine ⟨hH', hHs', hW.preimage (by fun_prop),
    hJq.comp (f := fun q : ℝ × V ↦ (-q.1, q.2)) (by fun_prop : ContDiff ℝ 2 _).contDiffOn
      fun _ hq ↦ hq,
    hJqper.comp_neg, fun _ hq ↦ hKW ⟨mem_univ _, hq.2⟩, fun t ↦ hJqt (-t),
    ω.floer_comp_realChart_positive_of_cylindrical (Jq := fun t ↦ Jq (-t))
      (fun w y hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 y hw hz) hH'
      (fun t ↦ (hHs'.of_uncurry_left t).differentiable hn) hn ha hr hu huK hfloer hE
      fun s t hs ↦ by simpa [realChart_cylindricalEndLift_negative] using hJ s (-t) hs⟩

/-- **The half-cylinder at the end of a PSS plane.** Let `𝔎` be a perturbation that is `H(t) dt`
on the part `ε s ≥ T₀` of the end. If `u` is `Cⁿ`, `n ≠ 0`, on a part `‖w‖ > r` of the plane,
with image in `K`, solving the Floer equation for `𝔎` there for structures `J(z)` bounded by `c`
and `M`, and with finite energy there, then on some half-cylinder `ε s > a` the map `u ∘ ψ` and the
structures `J ∘ ψ` satisfy the hypotheses of the finite-energy half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` for the cylindrical datum `H(t) dt`. -/
private theorem exists_halfCylinder_comp_realChart_cylindricalEndLift
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r : ℝ} (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ a : ℝ, ContDiffOn ℝ n (u ∘ realChart p.cylindricalEndLift) {z | a < p.endSign * z.1} ∧
      (∀ z, a < p.endSign * z.1 → (u ∘ realChart p.cylindricalEndLift) z ∈ K) ∧
      (∀ z, a < p.endSign * z.1 → ∀ v,
        c * ‖v‖ ^ 2 ≤ ω v ((J ∘ realChart p.cylindricalEndLift) z v)) ∧
      (∀ z, a < p.endSign * z.1 → ∀ v,
        ‖(J ∘ realChart p.cylindricalEndLift) z v‖ ≤ M * ‖v‖) ∧
      (∀ z, a < p.endSign * z.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart p.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart p.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∀ P : Set ℝ, MeasurableSet P → (∀ s ∈ P, a < p.endSign * s) →
        ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) z) ≠ ⊤ := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ T₀`, where the datum is cylindrical.
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp_mul Real.two_pi_pos r T₀
  have hmem {z : ℝ × ℝ} (hz : a < p.endSign * z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ :=
    p.lt_norm_symm_realChart_cylindricalEndLift_of_le_exp hr hz
  obtain ⟨hv, hvK, hfloer', hE'⟩ :=
    ω.floer_comp_realChart_cylindricalEndLift p hKH hH hHd hn ha hr hu huK hfloer hE
  exact ⟨a, hv, hvK, fun z hz ↦ hJc _ (hmem hz), fun z hz ↦ hJM _ (hmem hz), hfloer', hE'⟩

/-- **The energy on part of the end of the positive plane.** For `a ≥ 2`, if `u` is differentiable
on the part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` for the cylindrical
datum `H(t) dt` over a measurable subset `s` of a half-strip `s > a`, `t₀ ≤ t < t₀ + 1` of angular
width one is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a t₀ : ℝ}
    (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hst : s ⊆ Ioi a ×ˢ Ico t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) := by
  have hnorm {z : ℝ × ℝ} (hz : z ∈ s) :
      Real.exp (2 * π * a) <
        ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ :=
    exp_lt_norm_realChart_positive (hst hz).1
  rw [setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_eq (T₀ := 2)
    (fun _ x _ hw ↦ perturbation_eq_smul_endAngularForm hw x) hH hs
    (fun ζ hζ ↦ by simpa using ha.trans (hst hζ).1.le) (fun ζ hζ ↦ (hst hζ).2)
    (fun ζ hζ ↦ hu.differentiableAt <|
      (isOpen_setOf_lt_norm_equivRealProdCLM_symm _).mem_nhds (hnorm hζ))
    fun ζ _ ↦ (hHs.of_uncurry_left ζ.2).differentiable one_ne_zero _]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact hnorm hζ

/-- **The energy of a translated end of the positive plane.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, and the translate `s + (R, 0)`
of a measurable set `s` lies in a half-strip `s > a`, `t₀ ≤ t < t₀ + 1` of angular width one, then
the energy of the translated end `z ↦ u(φ(z + (R, 0)))` for the cylindrical datum `H(t) dt` over
`s` is at most the energy of `u` on that part of the plane. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_add_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a t₀ : ℝ}
    (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
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
  have h := ω.constSmooth.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) (R, 0)
    ((· + ((R, 0) : ℝ × ℝ)) '' s)
  rw [preimage_image_eq _ (add_left_injective _)] at h
  simp only [floerEnergyDensity_constSmooth, Prod.snd_add, add_zero, comp_apply] at h
  rw [h]
  exact ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le_of_subset hH hHs ha hu
    ((measurableEmbedding_addRight _).measurableSet_image' hs)
    (by rintro _ ⟨z, hz, rfl⟩; exact hst z hz)

/-! ### The orbit at the end -/

/-- **Subsequential orbit breaking at the end of a finite-energy PSS plane.** Let `𝔎` be a
perturbation of a PSS plane that is `H(t) dt` on the part `ε s ≥ T₀` of the end, for a period-one
`C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of the end, with image in a compact set
`K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)`
with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`, and with finite energy there. Then
there are a one-periodic orbit `x` of the Hamiltonian vector field and radii `R_n → ∞` such that the
loops `ℓ_{R_n}(t) = u(φ(ε R_n + i t))` converge uniformly to `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_cylindricalEndLift_of_floer
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨a, hv, hvK, hJc', hJM', hfloer', hE'⟩ :=
    exists_halfCylinder_comp_realChart_cylindricalEndLift hKH hH
      (fun t ↦ (hHs.of_uncurry_left t).differentiable one_ne_zero) one_ne_zero hu huK hJc hJM
      hfloer hE
  cases p with
  | positive =>
    -- On the positive plane the end is the positive half-cylinder `s > a`.
    have hpos (s : ℝ) (hs : a < s) : a < positive.endSign * s := by rwa [endSign_positive, one_mul]
    obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ :=
      exists_periodic_hasDerivAt_tendstoUniformly_of_floer hHs hH
        (hv.mono fun z hz ↦ hpos _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hpos s hs)) hc (fun z hz ↦ hJc' z (hpos _ hz.1))
        (fun z hz ↦ hJM' z (hpos _ hz.1)) (fun z hz ↦ hfloer' z (hpos _ hz.1))
        (hE' _ measurableSet_Ioi hpos)
    simp_rw [comp_apply, realChart_mk] at hux
    exact ⟨x, hxper, hx, φ, hφ, by simpa only [endSign_positive, one_mul] using hux⟩
  | negative =>
    -- On the negative plane the end is the negative half-cylinder `s < -a`.
    have hneg (s : ℝ) (hs : s < -a) : a < negative.endSign * s := by
      rw [endSign_negative]
      linarith
    obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ :=
      exists_periodic_hasDerivAt_tendstoUniformly_of_floer_Iio hHs hH
        (hv.mono fun z hz ↦ hneg _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hneg s hs)) hc (fun z hz ↦ hJc' z (hneg _ hz.1))
        (fun z hz ↦ hJM' z (hneg _ hz.1)) (fun z hz ↦ hfloer' z (hneg _ hz.1))
        (hE' _ measurableSet_Iio hneg)
    simp_rw [comp_apply, realChart_mk] at hux
    refine ⟨x, hxper, hx, fun n ↦ -φ n, tendsto_neg_atBot_atTop.comp hφ, ?_⟩
    simpa only [endSign_negative, neg_mul, one_mul, neg_neg] using hux

/-- **The asymptotic action at the end of a finite-energy PSS plane.** Let `𝔎` be a perturbation
of a PSS plane that is `H(t) dt` on the part `ε s ≥ T₀` of the end, for a period-one `C¹`
Hamiltonian `H`. Let `u` be `C²` on a part `‖w‖ > r` of the end, with image in a compact set `K`,
solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)` with
`c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`, and with finite energy there. Then there
is a one-periodic orbit `x` of the Hamiltonian vector field such that the loops
`ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`,
converge uniformly to `x` along some `R_n → ∞`, and their actions `A_H(ℓ_R)` tend to the action
`A_H(x)` as `R → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  obtain ⟨a, hv, hvK, hJc', hJM', hfloer', hE'⟩ :=
    exists_halfCylinder_comp_realChart_cylindricalEndLift hKH hH
      (fun t ↦ (hHs.of_uncurry_left t).differentiable one_ne_zero) two_ne_zero hu huK hJc hJM
      hfloer hE
  cases p with
  | positive =>
    -- On the positive plane the end is the positive half-cylinder `s > a`.
    have hpos (s : ℝ) (hs : a < s) : a < positive.endSign * s := by rwa [endSign_positive, one_mul]
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer hHs hH
        (hv.mono fun z hz ↦ hpos _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hpos s hs)) hc (fun z hz ↦ hJc' z (hpos _ hz.1))
        (fun z hz ↦ hJM' z (hpos _ hz.1)) (fun z hz ↦ hfloer' z (hpos _ hz.1))
        (hE' _ measurableSet_Ioi hpos)
    simp_rw [comp_apply, realChart_mk] at hux hA
    refine ⟨x, hxper, hx, ⟨φ, hφ, by simpa only [endSign_positive, one_mul] using hux⟩, ?_⟩
    simpa only [endSign_positive, one_mul] using hA
  | negative =>
    -- On the negative plane the end is the negative half-cylinder `s < -a`.
    have hneg (s : ℝ) (hs : s < -a) : a < negative.endSign * s := by
      rw [endSign_negative]
      linarith
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer hHs hH
        (hv.mono fun z hz ↦ hneg _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hneg s hs)) hc (fun z hz ↦ hJc' z (hneg _ hz.1))
        (fun z hz ↦ hJM' z (hneg _ hz.1)) (fun z hz ↦ hfloer' z (hneg _ hz.1))
        (hE' _ measurableSet_Iio hneg)
    simp_rw [comp_apply, realChart_mk] at hux hA
    refine ⟨x, hxper, hx, ⟨fun n ↦ -φ n, tendsto_neg_atBot_atTop.comp hφ, ?_⟩, ?_⟩
    · simpa only [endSign_negative, neg_mul, one_mul, neg_neg] using hux
    · refine (hA.comp tendsto_neg_atTop_atBot).congr fun R ↦ ?_
      simp only [comp_apply, endSign_negative, neg_mul, one_mul]

/-- **The asymptotic orbit at the end of a finite-energy PSS plane.** Let `𝔎` be the perturbation of
a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of
the end, with image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there
for almost complex structures `J(z)` with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`,
and with finite energy there. Then there is a one-periodic orbit `x` of the Hamiltonian vector
field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, converge uniformly to `x` along some `R_n → ∞`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_cylindricalEndLift_of_floer (p := p)
    (fun _ x _ hw ↦ p.perturbation_eq_smul_endAngularForm hw x) hH hHs hu hK huK hc hJc hJM
    hfloer hE

/-- **The energy of a finite-energy PSS plane.** Let `𝔎` be the perturbation of a PSS plane `p`
given by a period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on the whole plane, for almost complex structures `J(z)` tamed by `ω`, with
finite energy. Suppose that on a part `‖w‖ > r` of the end the image of `u` lies in a compact set
`K` and `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with `c > 0`. Then there is a one-periodic
orbit `x` of the Hamiltonian vector field, the uniform limit of the loops `ℓ_R(t) = u(φ(ε R + i t))`
along some `R_n → ∞`, where `φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`, such
that the actions `A_H(ℓ_R)` tend to `A_H(x)` as `R → ∞` and

`E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, hux, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer (p := p)
      (fun _ x _ hw ↦ perturbation_eq_smul_endAngularForm hw x) hH hHs hu.contDiffOn hK huK hc
      hJc hJM (fun z _ ↦ hfloer z) ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  exact ⟨x, hxper, hx, hux, hA, lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu hJ
    hfloer hA⟩

end TauCeti.SymplecticForm
