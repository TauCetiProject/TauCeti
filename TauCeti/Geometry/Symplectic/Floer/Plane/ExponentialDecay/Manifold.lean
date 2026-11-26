/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
public import TauCeti.Geometry.Symplectic.Floer.Plane.ExponentialDecay
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Exponential convergence at the end of a PSS plane in a symplectic chart of a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `𝔎` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a
PSS plane `p` given by a Hamiltonian `H` on `M`. Let `u` be a `C³` solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end of the plane, with finite energy there, for
an almost complex structure which is cylindrical there: `J_t(u(w))`, where `t = (p.endCoord w).im`
is the angular coordinate of `w`. On a manifold the loops of `u` along the end converge to a
one-periodic orbit (`TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Manifold`). This file shows
that, when the end of `u` stays in a compact set `B` inside a symplectic chart, the convergence is
exponentially fast in `C¹`, as it is for a symplectic vector space target
(`TauCeti.Geometry.Symplectic.Floer.Plane.ExponentialDecay`).

The chart is a smooth partial diffeomorphism `φ` from `M` onto an open subset of a
finite-dimensional real inner product space `V` with a constant symplectic form `ω₀`, pulling `ω₀`
back to `ω` at the points of `B ⊆ φ.source`; a Darboux chart
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_isInteriorPoint`) has this property on
its whole source. The Hamiltonian is read in the chart through a period-one `C³` Hamiltonian `H'`
on `V`, whose suspended Hamiltonian vector field is globally Lipschitz, with `H t = H' t ∘ φ` near
every point of `B`, and the structures through structures `J'_t` on `V` with
`dφ ∘ J_t = J'_t ∘ dφ`. The perturbation of the plane is `H` times a one-form on the domain, so it
is read in the chart as the perturbation of the plane given by `H'`
(`TauCeti.Floer.PSSPlane.perturbation_eventuallyEq_comp`). By
`TauCeti.Geometry.Symplectic.Floer.Chart`, the coordinate map `φ ∘ u` is then a solution of the
Floer equation of the plane in `(V, ω₀)` for `H'` and the cylindrical structure `J'_t`, with the
energy density of `u`, and `J'_t` is tamed by `ω₀` where `J_t` is tamed by `ω`. The vector-space
theorem, `exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation` in the
namespace `TauCeti.SymplecticForm`, therefore applies to `φ ∘ u`: if every one-periodic orbit of
`H'` in `φ(B)` is nondegenerate, there are such an orbit `x` and `κ > 0`, `C` with

`‖φ(u(φ_e(ε s + i t))) - x(t)‖ + ‖d(φ ∘ u ∘ φ_e)(ε s, t) - dt ⊗ X_{H'_t}(x(t))‖ ≤ C exp (-κ s)`

for all large `s` and all `t`, where `φ_e` is the end lift `p.cylindricalEndLift` and
`ε = p.endSign`. In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate` this is
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`.

This is the asymptotic condition under which a PSS plane in a manifold with a nondegenerate end
lies, in the chart, in the exponentially weighted function spaces of its linearized Floer
operator, and under which its end can be pre-glued to Floer cylinders and to the ends of pairs of
pants. A chart-free form, for an orbit that does not lie in a single chart, is not proved here.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`: exponential
  `C¹` convergence of the end of a PSS plane, read in a symplectic chart, to the stationary
  cylinder of an orbit;
* `exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation`: its `C⁰` part.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
-/

public section

open Filter Function MeasureTheory Set Topology
open TauCeti.Complex (realChart)
open scoped Manifold NNReal

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M} {B : Set M}
  {r : ℝ}

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {H' : ℝ → V → ℝ}

/-- At a point `z` of an open set `U` of the domain on which `u` is `Cⁿ`, `n ≠ 0`, with values in
`B ⊆ φ.source`, the coordinate map `φ ∘ u` has the energy density of `u` for the perturbations of
the plane given by `H'` and by `H`, and solves the Floer equation of the plane for `H'` and the
structure `J'` read in the chart wherever `u` solves it for `H` and `J`. -/
private theorem floerEnergyDensity_comp_and_isComplexLinearMap_perturbation (hω : ω.IsNondegenerate)
    (p : PSSPlane) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 1 (uncurry H'))
    (hH'per : Periodic H' 1) (hBφ : B ⊆ φ.source) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u U) (huB : ∀ z ∈ U, u z ∈ B) {z : ℝ × ℝ} (hz : z ∈ U) :
    ω₀.floerEnergyDensity
        (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x Complex.I) (φ ∘ u) z =
      ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z ∧
      ∀ {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V},
        IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
          (ω.perturbedMFDeriv
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            u z).toLinearMap →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
          (ω₀.perturbedFDeriv
            (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x Complex.I)
            (φ ∘ u) z).toLinearMap := by
  have huz : u z ∈ B := huB z hz
  have hum := ((hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt hn)
  have hφx := φ.mdifferentiableAt (by simp) (hBφ huz)
  have hsurj := (φ.bijective_mvfderiv (by simp) (hBφ huz)).surjective
  have hKs := perturbation_eventuallyEq_comp p (fun t ↦ hHH' t _ huz)
    (Complex.equivRealProdCLM.symm z) 1
  have hKt := perturbation_eventuallyEq_comp p (fun t ↦ hHH' t _ huz)
    (Complex.equivRealProdCLM.symm z) Complex.I
  have hKs' := differentiableAt_perturbation_target (p := p) hH'per hH'
    (Complex.equivRealProdCLM.symm z) (φ (u z)) 1
  have hKt' := differentiableAt_perturbation_target (p := p) hH'per hH'
    (Complex.equivRealProdCLM.symm z) (φ (u z)) Complex.I
  exact ⟨hω.floerEnergyDensity_comp hum hφx hsurj (hφ _ huz) hKs hKt hKs' hKt',
    fun hJJ' hfl ↦
      (hω.isComplexLinearMap_perturbedFDeriv_comp_iff hum hφx hsurj (hφ _ huz) hKs hKt hKs' hKt'
        hJJ').2 hfl⟩

end NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {H' : ℝ → V → ℝ}

/-- **Exponential `C¹` convergence at the end of a PSS plane in a symplectic chart.** Let `φ` be a
smooth partial diffeomorphism from `M` onto an open subset of `V`, pulling the symplectic form `ω₀`
back to the nondegenerate form `ω` at the points of a compact set `B ⊆ φ.source`. Let `H'` be a
`C³`, period-one Hamiltonian on `V` whose suspended Hamiltonian vector field is globally
Lipschitz, with `H t = H' t ∘ φ` near every point of `B`, and let `J'_t(y)` be a period-one family
of almost complex structures on `V`, `C²` on an open set `W` containing `ℝ × φ(B)`, which reads
`J` in the chart: `dφ_y ∘ J_t(y) = J'_t(φ y) ∘ dφ_y` for `y ∈ B`, with `J_t(y)` tamed by `ω` there.
Let `u` be `C³` on a part `‖w‖ > r` of the end of a PSS plane `p`, with values in `B` there,
solving the Floer equation `(du - X_𝔎)^{0,1} = 0` of the plane given by `H` there for the
cylindrical structure `J_t(u(w))`, `t = (p.endCoord w).im`, with finite energy there. Suppose that
every one-periodic orbit `x` of `H'` in `φ(B)` is nondegenerate: `x(0)` is a nondegenerate fixed
point of the time-one map. Then the end of `u`, read in the chart, converges exponentially fast in
`C¹` to the stationary cylinder of a one-periodic orbit `x` of `H'`: with `φ_e` the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, for some `κ > 0` and `C`, eventually

`‖φ(u(φ_e(ε s + i t))) - x(t)‖ + ‖d(φ ∘ u ∘ φ_e)(ε s, t) - dt ⊗ X_{H'_t}(x(t))‖ ≤ C exp (-κ s)`

for every `t`. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (p : PSSPlane) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × V)}
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 3 (uncurry H'))
    (hH'per : Periodic H' 1)
    (hJJ' : ∀ t, ∀ y ∈ B, IsComplexLinearMap (J t y) (J' t (φ y)) (mvfderiv I φ y).toLinearMap)
    (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ'per : Periodic J' 1) (hB : IsCompact B) (hBφ : B ⊆ φ.source) (hBW : univ ×ˢ (φ '' B) ⊆ W)
    (hJt : ∀ t, ∀ y ∈ B, (hω.symplecticFormAt y).Tames (J t y))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω₀.timeDependentHamiltonianSuspension H'))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) → (∀ t, x t ∈ φ '' B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow H' hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖φ (u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I)))) - x t‖ +
            ‖fderiv ℝ (φ ∘ u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
                (ω₀.hamiltonianVectorField (H' t) (x t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  set U : Set (ℝ × ℝ) := {z | r < ‖Complex.equivRealProdCLM.symm z‖}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hH'1 : ContDiff ℝ 1 (uncurry H') := hH'.of_le (by norm_num)
  have hchart (z : ℝ × ℝ) (hz : z ∈ U) :=
    floerEnergyDensity_comp_and_isComplexLinearMap_perturbation (n := 3) hω p φ hφ hHH' hH'1
      hH'per hBφ (by simp) hU hu huB hz
  -- In the chart, `J'` is tamed by `ω₀` over `ℝ × φ(B)`.
  have hJ't : ∀ t, ∀ x ∈ φ '' B, ω₀.Tames (J' t x) := fun t _ ↦
    hω.tames_of_mem_image φ hφ (hJJ' t) hBφ (hJt t)
  -- The coordinate map is `C³` on the end, with the energy of `u` there.
  have hu' : ContDiffOn ℝ 3 (φ ∘ u) U :=
    φ.contDiffOn_comp_of_contMDiffOn hu fun z hz ↦ hBφ (huB z hz)
  have hE' : ∫⁻ z in U, ENNReal.ofReal (ω₀.floerEnergyDensity
      (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H' (Complex.equivRealProdCLM.symm z) x Complex.I)
      (φ ∘ u) z) ≠ ⊤ := by
    rwa [setLIntegral_congr_fun hU.measurableSet fun z hz ↦ by rw [(hchart z hz).1]]
  exact
    SymplecticForm.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation
    (ω := ω₀) (u := φ ∘ u) (Jq := J')
    (J := fun z ↦ J' (p.endCoord (Complex.equivRealProdCLM.symm z)).im (φ (u z))) p hH'per hH'
    hu' (hB.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hBφ))
    (fun z hz ↦ ⟨u z, huB z hz, rfl⟩)
    (fun z hz ↦ (hchart z hz).2 (hJJ' _ _ (huB z hz)) (hfloer z hz)) hE' hW hJ' hJ'per hBW hJ't
    (fun _ _ ↦ rfl) hL hnd

/-- **Exponential convergence at the end of a PSS plane in a symplectic chart.** Under the
hypotheses of the `C¹` convergence theorem
`IsNondegenerate.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`,
the loops `ℓ_s(t) = u(φ_e(ε s + i t))` along the end, read in the chart, converge exponentially
fast to a one-periodic orbit `x` of `H'`: for some `κ > 0` and `C`, eventually
`‖φ(ℓ_s(t)) - x(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (p : PSSPlane) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × V)}
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 3 (uncurry H'))
    (hH'per : Periodic H' 1)
    (hJJ' : ∀ t, ∀ y ∈ B, IsComplexLinearMap (J t y) (J' t (φ y)) (mvfderiv I φ y).toLinearMap)
    (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ'per : Periodic J' 1) (hB : IsCompact B) (hBφ : B ⊆ φ.source) (hBW : univ ×ˢ (φ '' B) ⊆ W)
    (hJt : ∀ t, ∀ y ∈ B, (hω.symplecticFormAt y).Tames (J t y))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω₀.timeDependentHamiltonianSuspension H'))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) → (∀ t, x t ∈ φ '' B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow H' hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖φ (u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I)))) - x t‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation hω p φ hφ hHH'
      hH' hH'per hJJ' hW hJ' hJ'per hB hBφ hBW hJt hu huB hfloer hE hL hnd
  exact ⟨x, hxper, hx, κ, hκ, A,
    h.mono fun s hs t ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hs t)⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
