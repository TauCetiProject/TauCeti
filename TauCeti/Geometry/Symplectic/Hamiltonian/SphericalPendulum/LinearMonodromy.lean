/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Monodromy
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.ActionAngle
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.SpecialFunctions.Trigonometric.LevelSet
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace

/-!
# The linear monodromy of the spherical pendulum

Let `F = (H, J)` be the energy–momentum map of the spherical pendulum and let `U` be an open set of
regular values of `F`, so that over `U` the map `F` is a regular Lagrangian torus fibration
(`TauCeti.isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec`). Its period lattices
`Λ_b ⊆ T*_b U` form a covering space of `U`
(`IsLagrangianTorusFibration.isCoveringMap_latticeProj_periodLattice`), and lifting loops to it is
the **linear monodromy** `π₁(U, x₀) → GL(Λ_(x₀))` of the fibration (`TauCeti.latticeMonodromyHom`).
This file computes it around the focus–focus value `(1, 0)` of `F`.

In the coordinates of the plane, the covector `w ↦ v ⬝ᵥ w` is a period exactly when `v` is a period
of the flow action of `F`
(`TauCeti.mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice`). Write

* `γ_J` for the covector `w ↦ (0, 2π) ⬝ᵥ w`, the full turn of the rotation flow, a period over
  every regular value (`TauCeti.mem_periodLattice_sphericalPendulum_rotation`);
* `γ₂` for the covector `w ↦ (T(h, j), -Θ(h, j)) ⬝ᵥ w` at a regular value `(h, j)` with `j ≠ 0`,
  the energy flow for the period `T` of the height closed by the rotation flow backwards through
  the rotation angle `Θ` (`TauCeti.mem_periodLattice_sphericalPendulum_period`).

Let `γ(t) = (1 + r cos t, r sin t)` be the counterclockwise circle of radius `r > 0` about `(1, 0)`,
lying in `U`, and let `ℓ` be the loop at `x₀ = γ(π/2) = (1, r)` that runs once around it. Then
transport around `ℓ` fixes `γ_J` and sends `γ₂` to `γ₂ + γ_J`
(`TauCeti.latticeMonodromy_sphericalPendulum_rotation`,
`TauCeti.latticeMonodromy_sphericalPendulum_period`): in the basis `(γ_J, γ₂)` the monodromy is
the matrix `[[1, 1], [0, 1]]`, whose columns are the transported basis. In particular the linear
monodromy of the pendulum is nontrivial
(`TauCeti.latticeMonodromyHom_sphericalPendulum_ne_one`).

The constant covector `γ_J` is a period over every regular value and the differential of a linear
function, so it is transported to itself along every path
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration.latticeMonodromy_mk_mvfderiv`).
For `γ₂`, the section `b(t) = (T(γ(t)), -L(t))` along the circle, for a continuous lift `L` of
the rotation angle, is continuous and lies in the period lattices off the axis `j = 0`, and it
returns as `b(2π) = b(0) + (0, 2π)`
(`TauCeti.exists_continuousOn_mem_closure_sphericalPendulumPeriod_apply_two_mul_pi_eq_add`).
The period lattices are known explicitly only off the axis. At the two crossings `(1 ± r, 0)` of
the axis, `b` still takes values in them: a limit of periods of states over `γ(t)` is a period of
some state over the limit of the `γ(t)`, since the flow action is jointly continuous and `F` is
proper (`TauCeti.mem_periodLattice_sphericalPendulum_circle`). So the covectors of `b` along the
loop form a continuous lift of `ℓ` to the period lattice bundle, which transports `γ₂` to
`γ₂ + γ_J` (`TauCeti.latticeMonodromy_mk_of_continuous`).

## Main results

* `TauCeti.mem_periodLattice_sphericalPendulum_rotation`,
  `TauCeti.mem_periodLattice_sphericalPendulum_period`: `γ_J` and `γ₂` are periods.
* `TauCeti.mem_periodLattice_sphericalPendulum_circle`: a continuous family of vectors along the
  circle which are periods off the axis are periods on the axis too.
* `TauCeti.latticeMonodromy_sphericalPendulum_rotation`: transport fixes `γ_J`.
* `TauCeti.latticeMonodromy_sphericalPendulum_period`: transport around the focus–focus value
  sends `γ₂` to `γ₂ + γ_J`.
* `TauCeti.latticeMonodromyHom_sphericalPendulum_ne_one`: the linear monodromy is nontrivial.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 3 (the spherical pendulum).
* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum and its monodromy).
* K. Efstathiou, A. Giacobbe, P. Mardešić and D. Sugny, *Rotation forms and local Hamiltonian
  monodromy*, arXiv:1608.01579, Section III.
-/

public section

open Bundle Filter Function Set Real TopologicalSpace
open TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {U : Opens (Fin 2 → ℝ)} {r : ℝ}

/-- The period of a state `y` over `b ∈ U`, read as a covector at `b`. -/
private theorem mem_periodLattice_of_mem_hamiltonianFlowStabilizer
    (hU : U ≤ sphericalPendulumRegularValues) {b : U} {y : sphericalPendulumPhaseSpace}
    (hy : sphericalPendulumEnergyMomentumVec y = b) {v : Fin 2 → ℝ}
    (hv : v ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec y)
    {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : ∀ w, α w = v ⬝ᵥ w) :
    α ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed b := by
  have hyU : sphericalPendulumEnergyMomentumVec y ∈ U := hy ▸ b.property
  have hb : (⟨sphericalPendulumEnergyMomentumVec y, hyU⟩ : U) = b := Subtype.ext hy
  exact hb ▸ (mem_hamiltonianFlowStabilizer_sphericalPendulum_iff_mem_periodLattice hU
    ⟨y, hyU⟩ hα).1 hv

/-- **The full turn of the rotation flow is a period.** Over every regular value `b`, the covector
`γ_J : w ↦ (0, 2π) ⬝ᵥ w` lies in the period lattice, since the rotation flow, the flow of `J`, has
period `2π`. -/
theorem mem_periodLattice_sphericalPendulum_rotation (hU : U ≤ sphericalPendulumRegularValues)
    (b : U) {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : ∀ w, α w = ![0, 2 * π] ⬝ᵥ w) :
    α ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed b := by
  obtain ⟨y, hy⟩ := (mem_sphericalPendulumRegularValues_iff.1 (hU b.property)).1
  refine mem_periodLattice_of_mem_hamiltonianFlowStabilizer hU hy ?_ hα
  rw [SmoothTwoForm.IsSymplectic.mem_hamiltonianFlowStabilizer]
  have h : (![0, 2 * π] : Fin 2 → ℝ) = Pi.single 1 (2 * π) := by
    ext i
    fin_cases i <;> simp
  rw [h]
  exact sphericalPendulumFlowAction_single_one_two_mul_pi_apply y

/-- **The period lattice off the axis.** At a regular value `b = (h, j)` with `j ≠ 0`, the
covector `γ₂ : w ↦ (T(h, j), -Θ(h, j)) ⬝ᵥ w` lies in the period lattice: the energy flow for the
period `T` of the height, followed by the rotation flow backwards through the rotation angle `Θ`,
returns every state over `b` to itself. -/
theorem mem_periodLattice_sphericalPendulum_period (hU : U ≤ sphericalPendulumRegularValues)
    {b : U} (hb : (b : Fin 2 → ℝ) 1 ≠ 0)
    {α : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hα : ∀ w, α w = ![sphericalPendulumPeriod ((b : Fin 2 → ℝ) 0) ((b : Fin 2 → ℝ) 1),
      -sphericalPendulumRotationAngle ((b : Fin 2 → ℝ) 0) ((b : Fin 2 → ℝ) 1)] ⬝ᵥ w) :
    α ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed b := by
  obtain ⟨y, hy⟩ := (mem_sphericalPendulumRegularValues_iff.1 (hU b.property)).1
  refine mem_periodLattice_of_mem_hamiltonianFlowStabilizer hU hy ?_ hα
  rw [hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem
    (mem_sphericalPendulumTurningPointDomain_of_mem_sphericalPendulumRegularValues
      (hU b.property) hb) ((sphericalPendulumEnergyMomentumVec_eq_iff y _).1 hy)]
  exact AddSubgroup.subset_closure (mem_insert _ _)

/-- **Periods pass to limits.** Let `v t` be a period of a state `y t` of the spherical pendulum,
eventually along a nontrivial filter, with `v t → v₀` and `F (y t) → c₀`. Then `v₀` is a period
of some state over `c₀`: the states `y t` accumulate at a state over `c₀` because `F` is proper,
and the pairs of a state and one of its periods form a closed set because the flow action is
jointly continuous. -/
private theorem exists_mem_hamiltonianFlowStabilizer_of_tendsto {ι : Type*} {l : Filter ι}
    [l.NeBot] {v : ι → Fin 2 → ℝ} {y : ι → sphericalPendulumPhaseSpace} {v₀ c₀ : Fin 2 → ℝ}
    (hv : Tendsto v l (𝓝 v₀)) (hc : Tendsto (sphericalPendulumEnergyMomentumVec ∘ y) l (𝓝 c₀))
    (hvy : ∀ᶠ t in l, v t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (y t)) :
    ∃ y₀, sphericalPendulumEnergyMomentumVec y₀ = c₀ ∧
      v₀ ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec y₀ := by
  set C := {p : (Fin 2 → ℝ) × sphericalPendulumPhaseSpace |
    (sphericalPendulumFlowAction p.1).toMul p.2 = p.2}
  have hC : IsClosed C := isClosed_eq
    (isSymplectic_sphericalPendulumSymplecticForm.contMDiff_hamiltonianFlowAction_uncurry
      isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
      isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
      isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec).continuous
    continuous_snd
  -- The map `(v, y) ↦ (v, F y)` is proper, so the pairs `(v t, y t)` cluster at a pair over
  -- `(v₀, c₀)`.
  have hG :=
    (isProperMap_id (X := Fin 2 → ℝ)).prodMap isProperMap_sphericalPendulumEnergyMomentumVec
  obtain ⟨⟨v', y₀⟩, hp, hcl⟩ := hG.clusterPt_of_mapClusterPt (ℱ := map (fun t ↦ (v t, y t)) l)
    (y := (v₀, c₀)) (ClusterPt.of_le_nhds (by rw [map_map]; exact hv.prodMk_nhds hc))
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hp
  refine ⟨y₀, rfl, ?_⟩
  rw [SmoothTwoForm.IsSymplectic.mem_hamiltonianFlowStabilizer]
  exact hC.closure_subset (mem_closure_iff_clusterPt.2 (hcl.mono (tendsto_principal.2
    (hvy.mono fun t ht ↦ by rwa [SmoothTwoForm.IsSymplectic.mem_hamiltonianFlowStabilizer] at ht))))

/-- **Periods along the circle extend across the axis.** Let `γ(t) = (1 + r cos t, r sin t)`, with
`r > 0`, be a circle of regular values in `U` about the focus–focus value `(1, 0)`, and let `W` be
continuous on an open interval of times, with `W t` in the period lattice `ℤ (T, -Θ) + ℤ (0, 2π)`
at `γ(t)` whenever `γ(t)` is off the axis `j = 0`. Then at every time `t` of the interval, also
where `γ` crosses the axis, the covector `w ↦ W t ⬝ᵥ w` is a period at `γ(t)`. -/
theorem mem_periodLattice_sphericalPendulum_circle (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {a b : ℝ} {W : ℝ → Fin 2 → ℝ} (hW : ContinuousOn W (Ioo a b))
    (hWΛ : ∀ t ∈ Ioo a b, sin t ≠ 0 → W t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    {t : ℝ} (ht : t ∈ Ioo a b) {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : ∀ w, α w = W t ⬝ᵥ w) :
    α ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed
      ⟨_, hγU t⟩ := by
  -- States `y t` over `γ(t)`.
  choose y hy using fun t ↦ (mem_sphericalPendulumRegularValues_iff.1 (hU (hγU t))).1
  -- Off the axis, `W t` is a period of `y t`.
  have hoff (t : ℝ) (ht : t ∈ Ioo a b) (hs : sin t ≠ 0) :
      W t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (y t) := by
    rw [hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem
      (mem_sphericalPendulumTurningPointDomain_circle hr hU hγU hs)
      (by simpa using (sphericalPendulumEnergyMomentumVec_eq_iff _ _).1 (hy t))]
    exact hWΛ t ht hs
  -- The times off the axis are dense, since the zeros of `sin` are countable, so `W t` is a limit
  -- of periods of the `y s` with `s → t` off the axis, hence a period of a state over `γ(t)`.
  have hdense : Dense {s : ℝ | sin s ≠ 0} := by
    simpa [← compl_ofPred] using ((countable_setOf_mul_cos_add_mul_sin_eq (a := 0) (b := 1)
      (Or.inr one_ne_zero) 0).dense_compl ℝ)
  have : (𝓝[{s : ℝ | sin s ≠ 0}] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense t)
  have hIoo : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  obtain ⟨y₀, hy₀, hW₀⟩ := exists_mem_hamiltonianFlowStabilizer_of_tendsto
    (l := 𝓝[{s : ℝ | sin s ≠ 0}] t) (y := y)
    ((hW.continuousAt hIoo).tendsto.mono_left nhdsWithin_le_nhds)
    (by
      rw [show sphericalPendulumEnergyMomentumVec ∘ y =
        fun s ↦ ![1 + r * cos s, r * sin s] from funext hy]
      exact (Continuous.tendsto (by fun_prop) t).mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [nhdsWithin_le_nhds hIoo, self_mem_nhdsWithin] with s hs hsin
      exact hoff s hs hsin)
  exact mem_periodLattice_of_mem_hamiltonianFlowStabilizer hU (b := ⟨_, hγU t⟩) hy₀ hW₀ hα

/-- **Transport fixes `γ_J`.** Along every path in an open set `U` of regular values of the
spherical pendulum, transport of periods fixes the full turn `γ_J : w ↦ (0, 2π) ⬝ᵥ w` of the
rotation flow, a period over every point of `U`. -/
theorem latticeMonodromy_sphericalPendulum_rotation (hU : U ≤ sphericalPendulumRegularValues)
    {x y : U} (ℓ : Path x y) {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : ∀ w, α w = ![0, 2 * π] ⬝ᵥ w) :
    latticeMonodromy
        (isCoveringMap_latticeProj_periodLattice
          (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
          (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed)
        (.mk ℓ) ⟨α, mem_periodLattice_sphericalPendulum_rotation hU x hα⟩ =
      ⟨α, mem_periodLattice_sphericalPendulum_rotation hU y hα⟩ := by
  -- The constant covector `γ_J` is the differential of the linear function `α` on `U`.
  have hd (b : U) : mvfderiv 𝓘(ℝ, Fin 2 → ℝ) (α ∘ Subtype.val) b = α := by
    ext w
    rw [α.mvfderiv_comp_apply ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)]
    exact congrArg α (Manifold.mvfderiv_subtype_val_apply b w)
  have h := latticeMonodromy_mk_mvfderiv
    (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
    (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed
    (isCoveringMap_latticeProj_periodLattice
      (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed)
    (U := univ) (g := α ∘ Subtype.val)
    (fun _ _ ↦ (α.contMDiff.comp contMDiff_subtypeVal).contMDiffAt)
    (fun b _ ↦ by rw [hd]; exact mem_periodLattice_sphericalPendulum_rotation hU b hα) ℓ
    (fun _ ↦ trivial)
  simpa only [hd] using h

/-- **The transported period `γ₂` along the circle.** Along the circle
`γ(t) = (1 + r cos t, r sin t)` about `(1, 0)`, there is a continuous `W : ℝ → ℝ²` with `W t` in the
period lattice `ℤ γ₂(γ(t)) + ℤ (0, 2π)` at every time `t ∈ (0, 4π)` off the axis, starting from
`W(π/2) = γ₂(1, r)` and arriving at `W(π/2 + 2π) = γ₂(1, r) + (0, 2π)` after one turn. It is the
section `b(t) = (T(γ(t)), -L(t))` of
`TauCeti.exists_continuousOn_mem_closure_sphericalPendulumPeriod_apply_two_mul_pi_eq_add` on
`[0, 2π]`, continued by `b(t - 2π) + (0, 2π)`. -/
private theorem exists_continuous_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U) :
    ∃ W : ℝ → Fin 2 → ℝ, Continuous W ∧
      (∀ t ∈ Ioo 0 (4 * π), sin t ≠ 0 → W t ∈ AddSubgroup.closure
        {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
          -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]}) ∧
      W (π / 2) = ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] ∧
      W (π / 2 + 2 * π) =
        ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] + ![0, 2 * π] := by
  have hγT (t : ℝ) (hs : sin t ≠ 0) := mem_sphericalPendulumTurningPointDomain_circle hr hU hγU hs
  -- The section `b(t) = (T(γ(t)), -L(t))` of the period lattices along the circle, `t ∈ [0, 2π]`,
  -- with `b(2π) = b(0) + (0, 2π)`, clamped to `[0, 2π]` to make it continuous on `ℝ`.
  obtain ⟨b, hb, hbΛ, hb₂, hb2π⟩ :=
    exists_continuousOn_mem_closure_sphericalPendulumPeriod_apply_two_mul_pi_eq_add hr hγT
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set b' : ℝ → Fin 2 → ℝ := fun t ↦ b (projIcc 0 (2 * π) h2π t)
  have hb'c : Continuous b' :=
    hb.comp_continuous (continuous_subtypeVal.comp continuous_projIcc) fun t ↦ Subtype.prop _
  have hb' {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) : b' t = b t := by
    simp only [b', projIcc_of_mem h2π ht]
  -- Its continuation `W` past `2π` by `b(t - 2π) + (0, 2π)`, continuous on `ℝ`.
  set W : ℝ → Fin 2 → ℝ := fun t ↦ if t ≤ 2 * π then b' t else b' (t - 2 * π) + ![0, 2 * π]
  have hWc : Continuous W := Continuous.if_le hb'c
    ((hb'c.comp (continuous_id.sub continuous_const)).add continuous_const) continuous_id
    continuous_const fun t ht ↦ by
      rw [ht, sub_self, hb' ⟨h2π, le_rfl⟩, hb' ⟨le_rfl, h2π⟩, hb2π]
  have hπ2 : π / 2 ∈ Icc 0 (2 * π) := ⟨by positivity, by linarith [pi_pos]⟩
  have hb₂π2 : b (π / 2) =
      ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] := by
    rw [hb₂ _ ⟨by positivity, by linarith [pi_pos]⟩]
    simp
  refine ⟨W, hWc, fun t ht hs ↦ ?_, ?_, ?_⟩
  -- On `(0, 4π)`, off the axis, `W t` is in the period lattice spanned by `γ₂(γ(t))` and `γ_J`.
  · rcases le_or_gt t (2 * π) with ht2 | ht2
    · simp only [W, ite_eq_left ht2, hb' ⟨ht.1.le, ht2⟩]
      exact hbΛ t ⟨ht.1.le, ht2⟩ hs
    · have ht' : t - 2 * π ∈ Icc 0 (2 * π) := ⟨by linarith, by linarith [ht.2]⟩
      have hs' : sin (t - 2 * π) ≠ 0 := by rwa [sin_sub_two_pi]
      simp only [W, ite_eq_right ht2.not_ge, hb' ht']
      have h := hbΛ _ ht' hs'
      rw [cos_sub_two_pi, sin_sub_two_pi] at h
      exact add_mem h (AddSubgroup.subset_closure (mem_insert_of_mem _ rfl))
  -- At the start, `W(π/2) = b(π/2) = γ₂(1, r)`.
  · simp only [W, ite_eq_left hπ2.2, hb' hπ2, hb₂π2]
  -- After one turn, `W(5π/2) = b(π/2) + (0, 2π) = γ₂(1, r) + (0, 2π)`.
  · have hgt : ¬ π / 2 + 2 * π ≤ 2 * π := by linarith [pi_pos]
    simp only [W, ite_eq_right hgt, add_sub_cancel_right, hb' hπ2, hb₂π2]

/-- **The monodromy of the spherical pendulum sends `γ₂` to `γ₂ + γ_J`.** Let
`γ(t) = (1 + r cos t, r sin t)` be the counterclockwise circle of radius `r > 0` about the
focus–focus value `(1, 0)`, lying in an open set `U` of regular values of the energy–momentum map,
and let `ℓ` be the loop in `U` running once around it from `x₀ = γ(π/2) = (1, r)`,
`ℓ(s) = γ(π/2 + 2πs)`. Transport of periods around `ℓ` sends
`γ₂ : w ↦ (T(1, r), -Θ(1, r)) ⬝ᵥ w` to `γ₂ + γ_J`, where `γ_J : w ↦ (0, 2π) ⬝ᵥ w`. Together with
`TauCeti.latticeMonodromy_sphericalPendulum_rotation`, the monodromy around `ℓ` is the matrix
`[[1, 1], [0, 1]]` in the basis `(γ_J, γ₂)`. -/
theorem latticeMonodromy_sphericalPendulum_period (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    {x₀ : U} (ℓ : Path x₀ x₀)
    (hℓ : ∀ s : unitInterval, (ℓ s : Fin 2 → ℝ) =
      ![1 + r * cos (π / 2 + 2 * π * s), r * sin (π / 2 + 2 * π * s)])
    {α₂ αJ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hα₂ : ∀ w, α₂ w =
      ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] ⬝ᵥ w)
    (hαJ : ∀ w, αJ w = ![0, 2 * π] ⬝ᵥ w)
    (h₂ : α₂ ∈ (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU).periodLattice
      (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed x₀) :
    (latticeMonodromy
        (isCoveringMap_latticeProj_periodLattice
          (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
          (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed)
        (.mk ℓ) ⟨α₂, h₂⟩).val = α₂ + αJ := by
  obtain ⟨W, hWc, hWΛ, hW0, hW1⟩ := exists_continuous_mem_closure_sphericalPendulumPeriod hr hU hγU
  -- The covectors of `W(π/2 + 2πs)` along the loop are periods, also on the axis.
  set τ : unitInterval → ℝ := fun s ↦ π / 2 + 2 * π * s
  have hτ (s : unitInterval) : τ s ∈ Ioo 0 (4 * π) := by
    simp only [τ, mem_Ioo]
    constructor <;> nlinarith [pi_pos, unitInterval.nonneg s, unitInterval.le_one s]
  -- The covector `w ↦ v ⬝ᵥ w`, depending linearly on `v`.
  set δ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ (dotProductEquiv ℝ (Fin 2)).toLinearMap
  have hδ (v w : Fin 2 → ℝ) : δ v w = v ⬝ᵥ w := by simp [δ, dotProductEquiv]
  have hℓτ (s : unitInterval) : ℓ s = ⟨_, hγU (τ s)⟩ := Subtype.ext (hℓ s)
  refine congrArg Subtype.val (latticeMonodromy_mk_of_continuous _ ℓ
    (c := ⟨α₂ + αJ, add_mem h₂ (mem_periodLattice_sphericalPendulum_rotation hU x₀ hαJ)⟩)
    (s := fun s ↦ TotalSpace.mk' ((Fin 2 → ℝ) →L[ℝ] ℝ)
      (E := fun b : U ↦ TangentSpace 𝓘(ℝ, Fin 2 → ℝ) b →L[ℝ] ℝ) (ℓ s) (δ (W (τ s))))
    (CotangentBundle.continuous_totalSpaceMk_opens ℓ.continuous
      (δ.continuous_of_finiteDimensional.comp (hWc.comp (by fun_prop)))) (fun _ ↦ rfl)
    (fun s ↦ ?_) ?_ ?_)
  · rw [hℓτ s]
    exact mem_periodLattice_sphericalPendulum_circle hr hU hγU hWc.continuousOn hWΛ (hτ s)
      (hδ _)
  -- At the start of the loop, `W(π/2) = b(π/2) = γ₂(1, r)`.
  · have hW0' : W (τ 0) =
        ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] := by
      simpa [τ] using hW0
    rw [ℓ.source]
    congr 1
    ext w
    rw [hδ, hW0']
    exact (hα₂ w).symm
  -- At the end, `W(5π/2) = b(π/2) + (0, 2π) = γ₂(1, r) + γ_J`.
  · have hW1' : W (τ 1) =
        ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r] + ![0, 2 * π] := by
      simpa [τ] using hW1
    rw [ℓ.target]
    congr 1
    ext w
    rw [hδ, hW1', add_dotProduct]
    exact (congrArg₂ (· + ·) (hα₂ w) (hαJ w)).symm

/-- **The linear monodromy of the spherical pendulum is nontrivial.** Let `U` be an open set of
regular values of the energy–momentum map of the spherical pendulum containing a circle
`γ(t) = (1 + r cos t, r sin t)` of radius `r > 0` about the focus–focus value `(1, 0)`. Then the
linear monodromy of the Lagrangian torus fibration over `U`, at the point `(1, r)` of the circle,
is not trivial: transport around the circle sends `γ₂` to `γ₂ + γ_J ≠ γ₂`. -/
theorem latticeMonodromyHom_sphericalPendulum_ne_one (hr : 0 < r)
    (hU : U ≤ sphericalPendulumRegularValues) (hγU : ∀ t, ![1 + r * cos t, r * sin t] ∈ U)
    (x₀ : U) (hx₀ : (x₀ : Fin 2 → ℝ) = ![1, r]) :
    latticeMonodromyHom
        (isCoveringMap_latticeProj_periodLattice
          (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
          (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed)
        x₀ ≠ 1 := by
  -- The loop `ℓ(s) = γ(π/2 + 2πs)` at `x₀`.
  have hγ0 : (![1 + r * cos (π / 2 + 2 * π * 0), r * sin (π / 2 + 2 * π * 0)] : Fin 2 → ℝ) =
      x₀ := by
    rw [hx₀]
    simp
  have hγ1 : (![1 + r * cos (π / 2 + 2 * π * 1), r * sin (π / 2 + 2 * π * 1)] : Fin 2 → ℝ) =
      x₀ := by
    rw [hx₀, mul_one, cos_add_two_pi, sin_add_two_pi]
    simp
  let ℓ : Path x₀ x₀ :=
    { toFun s := ⟨_, hγU (π / 2 + 2 * π * s)⟩
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      source' := Subtype.ext hγ0
      target' := Subtype.ext hγ1 }
  -- The periods `γ₂` and `γ_J` at `x₀`.
  let α : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ := fun v ↦
    LinearMap.toContinuousLinearMap (dotProductEquiv ℝ (Fin 2) v)
  set v₂ : Fin 2 → ℝ := ![sphericalPendulumPeriod 1 r, -sphericalPendulumRotationAngle 1 r]
  have hα (v : Fin 2 → ℝ) (w : Fin 2 → ℝ) : α v w = v ⬝ᵥ w := by simp [α, dotProductEquiv]
  have h₂ := mem_periodLattice_sphericalPendulum_period hU (b := x₀)
    (by rw [hx₀]; simpa using hr.ne') (α := α v₂) fun w ↦ by rw [hα v₂ w, hx₀]; simp [v₂]
  intro h1
  have h := latticeMonodromy_sphericalPendulum_period hr hU hγU ℓ (fun _ ↦ rfl)
    (α₂ := α v₂) (hα v₂) (hα ![0, 2 * π]) h₂
  have hid := latticeMonodromyHom_apply (isCoveringMap_latticeProj_periodLattice
    (isLagrangianTorusFibration_sphericalPendulumEnergyMomentumVec hU)
    (isSymplectic_sphericalPendulumSymplecticForm.mpullback_subtype_val _).isClosed) x₀
    (FundamentalGroup.fromPath (.mk ℓ)) ⟨_, h₂⟩
  simp only [h1] at hid
  -- Then `γ₂ = γ₂ + γ_J`, so `γ_J = 0`, but `γ_J` takes the value `2π` on `(0, 1)`.
  have h0 := congrArg (fun a : (Fin 2 → ℝ) →L[ℝ] ℝ ↦ a ![0, 1])
    (left_eq_add.1 ((congrArg Subtype.val hid).trans h))
  simp [hα, dotProduct, Fin.sum_univ_two, pi_ne_zero] at h0

end TauCeti
