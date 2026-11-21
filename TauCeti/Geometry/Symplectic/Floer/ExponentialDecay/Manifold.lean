/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Exponential convergence at a nondegenerate end in a symplectic chart of a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, `H : ℝ → M → ℝ` a `1`-periodic Hamiltonian and `u` a solution of the Floer
equation

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

on the half-cylinder `s > a`, with `1`-periodic loops and finite energy, for the cylindrical
perturbation `K = H_t dt`. On a manifold the loops of such a half-cylinder converge to a
`1`-periodic orbit along a sequence `s_n → ∞`, and along the whole end at isolated orbits
(`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`). This file shows that, near a
nondegenerate orbit lying in a symplectic chart, the convergence is exponentially fast, in `C¹`,
as it is for a symplectic vector space target
(`TauCeti.Geometry.Symplectic.Floer.ExponentialDecay`).

The chart is a smooth partial diffeomorphism `φ` from `M` onto an open subset of a
finite-dimensional normed space `V` (an inner product space for the `C¹` theorem) with a constant
symplectic form `ω₀`, pulling `ω₀` back to `ω` at the points of a set `B ⊆ φ.source` containing the
end of `u`: a Darboux chart
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) has this property on its whole source.
The Hamiltonian is read in the chart through a Hamiltonian `H'` on `V` with `H t = H' t ∘ φ` near
every point of `B`, and the almost complex structures through structures `J'` on `V` with
`dφ ∘ J = J' ∘ dφ`. By `TauCeti.Geometry.Symplectic.Floer.Chart`, the coordinate map `φ ∘ u` is
then a Floer half-cylinder in `(V, ω₀)` for `H'` and `J'`, with the energy density of `u`, and
`J'` is tamed by `ω₀` where `J` is tamed by `ω`. The three main theorems of the vector-space file
transfer, in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* **Exponential decay of the energy**
  (`IsNondegenerate.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`): if the
  coordinate loops `φ ∘ u(s, ·)` converge uniformly to a nondegenerate `1`-periodic orbit `x` of
  `H'`, the Floer energy of `u` over `[s, ∞) × [0, 1]`, an intrinsic quantity on `M`, is eventually
  at most `C exp (-κ s)`. The almost complex structures may depend on the domain point, with
  uniform taming constants in the chart.
* **Exponential `C⁰` convergence** (`IsNondegenerate.exists_pos_eventually_norm_sub_le_exp`): if
  moreover `∂_s (φ ∘ u)` is bounded, eventually `‖φ (u (s, t)) - x t‖ ≤ C exp (-κ s)`.
* **Exponential `C¹` convergence at isolated nondegenerate orbits**
  (`IsNondegenerate.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp`): for a
  cylindrical end, `J = J_t(u)` with `J'_t(y)` of class `C²` and `1`-periodic, whose end stays in
  a compact set `B` on which the `1`-periodic orbits of `H'` are isolated and nondegenerate, the
  coordinate loops converge to one such orbit `x`, and

  `‖φ (u (s, t)) - x t‖ + ‖d(φ ∘ u)(s, t) - dt ⊗ X_{H'_t}(x t)‖ ≤ C exp (-κ s)`

  eventually, where `dt ⊗ X_{H'_t}(x t)` is the derivative of the stationary cylinder over `x`.
  No bound on the derivative of `u` and no convergence of the loops is assumed.

The `C¹` estimate in the chart is the asymptotic input of pre-gluing a Floer cylinder at a
nondegenerate orbit (in `TauCeti.Geometry.Symplectic.Floer.Pregluing`,
`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le_of_floerOperator_eq_zero`,
applied to the coordinate maps), and the
condition under which the end lies in the exponentially weighted function spaces of its linearized
operator.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the exponential decay of finite-energy Floer trajectories
  at nondegenerate orbits.
* J. Robbin and D. Salamon, *Asymptotic behaviour of holomorphic strips*, Ann. Inst. H. Poincaré
  Anal. Non Linéaire 18 (2001), 573–612.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M} {B : Set M}
  {a : ℝ}

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {H' : ℝ → V → ℝ} {x : ℝ → V}

/-- On the half-cylinder `s > a`, where `u` takes values in `B ⊆ φ.source`, the coordinate map
`φ ∘ u` has the energy density of `u` for the cylindrical perturbation, and solves the coordinate
Floer equation for the structure `J'` read in the chart wherever `u` solves the Floer equation for
`J`. -/
private theorem floerEnergyDensity_comp_and_isComplexLinearMap (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 1 (uncurry H'))
    (hBφ : B ⊆ φ.source) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u (Ioi a ×ˢ univ))
    (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B) {z : ℝ × ℝ} (hz : a < z.1) :
    ω₀.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z =
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z ∧
      ∀ {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V},
        IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
          (ω₀.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z).toLinearMap := by
  have huz : u z ∈ B := huB z.1 hz z.2
  have hum := (hu.contMDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)).mdifferentiableAt hn
  have hφx := φ.mdifferentiableAt (by simp) (hBφ huz)
  have hsurj := (φ.bijective_mvfderiv (by simp) (hBφ huz)).surjective
  have hH'z := (hH'.comp (contDiff_prodMk_right z.2)).differentiable one_ne_zero (φ (u z))
  exact ⟨hω.floerEnergyDensity_comp hum hφx hsurj (hφ _ huz) EventuallyEq.rfl (hHH' z.2 _ huz)
      (differentiableAt_const _) hH'z,
    fun hJJ' hfl ↦ (hω.isComplexLinearMap_perturbedFDeriv_comp_iff hum hφx hsurj (hφ _ huz)
      EventuallyEq.rfl (hHH' z.2 _ huz) (differentiableAt_const _) hH'z hJJ').2 hfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ V] in
/-- The coordinate map `φ ∘ u` of a `Cⁿ` map `u` with values in `B ⊆ φ.source` on the
half-cylinder is `Cⁿ` there. -/
private theorem contDiffOn_comp (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {n : ℕ}
    (hBφ : B ⊆ φ.source) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u (Ioi a ×ˢ univ))
    (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B) :
    ContDiffOn ℝ n (φ ∘ u) (Ioi a ×ˢ univ) :=
  contMDiffOn_iff_contDiffOn.1 <|
    (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp hu
      fun z hz ↦ hBφ (huB z.1 hz.1 z.2)

omit [FiniteDimensional ℝ E] in
/-- The energy of `u` over a measurable subset of the half-cylinder `s > a` is the energy of its
coordinate map. -/
private theorem setLIntegral_floerEnergyDensity_comp {φ : M → V} {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S)
    (hSa : ∀ z ∈ S, a < z.1)
    (h : ∀ z : ℝ × ℝ, a < z.1 →
      ω₀.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z =
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) :
    ∫⁻ z in S, ENNReal.ofReal
        (ω₀.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) :=
  setLIntegral_congr_fun hS fun z hz ↦ by rw [h z (hSa z hz)]

/-- The coordinate map `φ ∘ u` of a map `u` of finite energy on the half-cylinder `s > a`, with
values in `B ⊆ φ.source`, has finite energy there. -/
private theorem setLIntegral_floerEnergyDensity_comp_ne_top (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 1 (uncurry H'))
    (hBφ : B ⊆ φ.source) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u (Ioi a ×ˢ univ))
    (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω₀.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z) ≠ ⊤ := by
  rwa [setLIntegral_floerEnergyDensity_comp (measurableSet_Ioi.prod measurableSet_Icc)
    (fun z hz ↦ hz.1) fun z hz ↦
      (floerEnergyDensity_comp_and_isComplexLinearMap hω φ hn hφ hHH' hH' hBφ hu huB hz).1]

/-- **Exponential decay of the energy at a nondegenerate end in a symplectic chart.** Let `φ` be a
smooth partial diffeomorphism from `M` onto an open subset of `V`, pulling the symplectic form `ω₀`
back to the nondegenerate form `ω` at the points of `B ⊆ φ.source`, and let `H'` be a `C²`,
`1`-periodic Hamiltonian on `V` with `H t = H' t ∘ φ` near every point of `B`. Let `u` be a `C²`
solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder `s > a`,
with `1`-periodic loops in `B` and finite energy, for structures `J z` whose readings `J' z` in the
chart, `dφ ∘ J z = J' z ∘ dφ`, satisfy `c ‖v‖² ≤ ω₀(v, J' z v)` and `‖J' z v‖ ≤ M' ‖v‖` with
`c > 0`. Suppose that the coordinate loops `φ ∘ u(s, ·)` converge uniformly as `s → ∞` to a
`1`-periodic orbit `x` of `H'` which is nondegenerate: the propagator of `ζ' = dX_{H'_t}(x(t)) ζ`
has no nonzero fixed vector at time `1`. Then the energy of `u` over `[s, ∞) × [0, 1]` is eventually
at most `C exp (-κ s)`, for some `κ > 0`. -/
theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ × ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ × ℝ → AlmostComplexStructure V} {c M' : ℝ}
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 2 (uncurry H'))
    (hH'per : Periodic H' 1) (hBφ : B ⊆ φ.source)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B)
    (hJJ' : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (J z (u z)) (J' z) (mvfderiv I φ (u z)).toLinearMap)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω₀ v (J' z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J' z v‖ ≤ M' * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t)
    (hnd : ∀ v,
      dysonSeriesLeft (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (H' t)) (x t)) 1 v = v →
        v = 0)
    (hux : TendstoUniformly (fun s t ↦ φ (u (s, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∫⁻ z in Ici s ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * s))) := by
  have hH'1 : ContDiff ℝ 1 (uncurry H') := hH'.of_le (by norm_num)
  have hchart (z : ℝ × ℝ) (hz : a < z.1) :=
    floerEnergyDensity_comp_and_isComplexLinearMap (n := 2) hω φ (by simp) hφ hHH' hH'1 hBφ hu
      huB hz
  obtain ⟨κ, hκ, C, hdecay⟩ :=
    TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp
      (ω := ω₀) (u := φ ∘ u) (J := J') hH' hH'per (contDiffOn_comp φ hBφ hu huB)
    (fun s hs t ↦ congrArg φ (hper s hs t)) hc hJc hJM
    (fun z hz ↦ (hchart z hz.1).2 (hJJ' z hz) (hfloer z hz))
    (setLIntegral_floerEnergyDensity_comp_ne_top hω φ (by simp) hφ hHH' hH'1 hBφ hu huB hE)
    hxper hx hnd hux
  refine ⟨κ, hκ, C, (hdecay.and (eventually_gt_atTop a)).mono fun s ⟨hs, hsa⟩ ↦ ?_⟩
  rwa [setLIntegral_floerEnergyDensity_comp (measurableSet_Ici.prod measurableSet_Icc)
    (fun z hz ↦ hsa.trans_le hz.1) fun z hz ↦ (hchart z hz).1] at hs

/-- **Exponential convergence at a nondegenerate end in a symplectic chart.** Under the hypotheses
of the energy decay
`IsNondegenerate.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`, suppose
moreover that `∂_s (φ ∘ u)` is bounded by `L` on the half-cylinder. Then the coordinate
loops `φ ∘ u(s, ·)` converge to the nondegenerate orbit `x` exponentially fast: for some `κ > 0` and
`C`, eventually `‖φ (u (s, t)) - x(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ × ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ × ℝ → AlmostComplexStructure V} {c M' L : ℝ}
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 2 (uncurry H'))
    (hH'per : Periodic H' 1) (hBφ : B ⊆ φ.source)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B)
    (hJJ' : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (J z (u z)) (J' z) (mvfderiv I φ (u z)).toLinearMap)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω₀ v (J' z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J' z v‖ ≤ M' * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hL : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ (φ ∘ u) z (1, 0)‖ ≤ L)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t)
    (hnd : ∀ v,
      dysonSeriesLeft (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (H' t)) (x t)) 1 v = v →
        v = 0)
    (hux : TendstoUniformly (fun s t ↦ φ (u (s, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t, ‖φ (u (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)) := by
  have hH'1 : ContDiff ℝ 1 (uncurry H') := hH'.of_le (by norm_num)
  exact TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp
    (ω := ω₀) (u := φ ∘ u) (J := J') hH' hH'per (contDiffOn_comp φ hBφ hu huB)
    (fun s hs t ↦ congrArg φ (hper s hs t)) hc hJc hJM
    (fun z hz ↦ (floerEnergyDensity_comp_and_isComplexLinearMap (n := 2) hω φ (by simp) hφ hHH'
      hH'1 hBφ hu huB hz.1).2 (hJJ' z hz) (hfloer z hz))
    (setLIntegral_floerEnergyDensity_comp_ne_top hω φ (by simp) hφ hHH' hH'1 hBφ hu huB hE)
    hL hxper hx hnd hux

end NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {H' : ℝ → V → ℝ}

/-- **Exponential `C¹` convergence at isolated nondegenerate orbits in a symplectic chart.** Let
`φ` be a smooth partial diffeomorphism from `M` onto an open subset of `V`, pulling the symplectic
form `ω₀` back to the nondegenerate form `ω` at the points of a compact set `B ⊆ φ.source`. Let
`H'` be a `C³`, `1`-periodic Hamiltonian on `V` with `H t = H' t ∘ φ` near every point of `B`, and
let `J'_t(y)` be a `1`-periodic family of almost complex structures on `V`, `C²` on an open set
`W ⊆ ℝ × V` containing `ℝ × φ(B)`, which reads `J` in the chart:
`dφ_y ∘ J_t(y) = J'_t(φ y) ∘ dφ_y` for `y ∈ B`, with `J_t(y)` tamed by `ω` there. Let `u` be a `C³`
solution of the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder
`s > a`, with `1`-periodic loops in `B` and finite energy. Suppose that every `1`-periodic orbit of
`H'` in `φ(B)` is isolated and nondegenerate. Then the coordinate loops `φ ∘ u(s, ·)` converge to a
`1`-periodic orbit `x` of `H'`, exponentially fast in `C¹`: for some `κ > 0` and `C`, eventually

`‖φ (u (s, t)) - x(t)‖ + ‖d(φ ∘ u)(s, t) - dt ⊗ X_{H'_t}(x(t))‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp
    (hω : ω.IsNondegenerate) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × V)}
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H t =ᶠ[𝓝 y] H' t ∘ φ) (hH' : ContDiff ℝ 3 (uncurry H'))
    (hH'per : Periodic H' 1)
    (hJJ' : ∀ t, ∀ y ∈ B, IsComplexLinearMap (J t y) (J' t (φ y)) (mvfderiv I φ y).toLinearMap)
    (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJ'per : Periodic J' 1) (hB : IsCompact B) (hBφ : B ⊆ φ.source) (hBW : univ ×ˢ (φ '' B) ⊆ W)
    (hJt : ∀ t, ∀ y ∈ B, (hω.symplecticFormAt y).Tames (J t y))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huB : ∀ s, a < s → ∀ t, u (s, t) ∈ B)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) → (∀ t, x t ∈ φ '' B) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω₀.hamiltonianVectorField (H' t) (y t)) t) →
        dist (y 0) (x 0) < ε → y = x)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) → (∀ t, x t ∈ φ '' B) →
      ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (H' t)) (x t)) 1 v = v →
        v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t,
        ‖φ (u (s, t)) - x t‖ + ‖fderiv ℝ (φ ∘ u) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω₀.hamiltonianVectorField (H' t) (x t))‖ ≤
            C * Real.exp (-(κ * s)) := by
  have hH'1 : ContDiff ℝ 1 (uncurry H') := hH'.of_le (by norm_num)
  -- In the chart, `J'` is tamed by `ω₀` over `ℝ × φ(B)`.
  have hJ't : ∀ t, ∀ y ∈ φ '' B, ω₀.Tames (J' t y) := by
    rintro t _ ⟨y, hy, rfl⟩
    exact hω.tames_of_isComplexLinearMap_mvfderiv
      (φ.bijective_mvfderiv (by simp) (hBφ hy)).surjective (hφ y hy) (hJJ' t y hy) (hJt t y hy)
  exact TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp
    (ω := ω₀) (u := φ ∘ u) hH' hH'per hW hJ' hJ'per
    (hB.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hBφ)) hBW hJ't
    (contDiffOn_comp φ hBφ hu huB) (fun s hs t ↦ congrArg φ (hper s hs t))
    (fun s hs t ↦ ⟨u (s, t), huB s hs t, rfl⟩)
    (fun z hz ↦ (floerEnergyDensity_comp_and_isComplexLinearMap (n := 3) hω φ (by simp) hφ hHH'
      hH'1 hBφ hu huB hz.1).2 (hJJ' z.2 _ (huB z.1 hz.1 z.2)) (hfloer z hz))
    (setLIntegral_floerEnergyDensity_comp_ne_top hω φ (by simp) hφ hHH' hH'1 hBφ hu huB hE)
    hiso hnd

end TauCeti.SmoothTwoForm.IsNondegenerate

end
