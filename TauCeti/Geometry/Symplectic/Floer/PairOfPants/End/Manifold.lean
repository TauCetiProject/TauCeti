/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback

/-!
# Asymptotic orbits at the ends of a finite-energy Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a closed symplectic manifold, and
let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in
functions on `M`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one
Hamiltonians `H_q` with `H_q` jointly `C¹` at the end `q`. Let `u : S → M` be a `C¹` solution of the
Floer equation `(du - X_K)^{0,1} = 0` for almost complex structures `J(z)` on the tangent spaces
`T_{u z} M`, with image in a compact set `B` and finite energy. This file shows that `u` breaks off
a one-periodic orbit of `H_q` at the end `q` (and a contractible one when an end loop is
null-homotopic on `AddCircle 1`): there are an orbit `y` in `B` and `s_n → ∞` such that the loops
`t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`
(`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). On a compact manifold `B` can be the
whole manifold (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`,
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer`).
This is the first step of Floer breaking at the ends of a pair of pants in a closed symplectic
manifold; `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` proves it for a symplectic
vector space, and `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold.Convergence` upgrades
sequential breaking to whole-end convergence and the energy identity.

As in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`, convergence and uniform tameness
are measured through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on
`B` and with injective differential at the points of `B`: the loops converge pointwise in `M` and
uniformly after applying `e`, and the almost complex structures satisfy
`c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0` on some half-cylinder `s > b` of the positive end
chart `φ'_q`. On a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`.

The proof reduces each end to a finite-energy Floer half-cylinder.

* **Positive end charts.** On the end `q`, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
  (`TauCeti.Floer.positiveEndChart`) is holomorphic, and beyond `T₀` it pulls `K` back to
  `H'_q(t) dt` for the positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
  (`TauCeti.Floer.positiveEndHamiltonian`). Since the perturbed derivative is natural under
  changes of domain coordinates (`TauCeti.SmoothTwoForm.perturbedMFDeriv_perturbationPullback`),
  `u ∘ φ'_q` solves the Floer equation of a half-cylinder for `H'_q`
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`,
  `TauCeti.SmoothTwoForm.mfderiv_comp_positiveEndChart_add_eq_zero`), and its energy over a
  half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
  (`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). These
  statements are in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback`.
* **Orbits at the ends.** The half-cylinder theorem
  `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, in the
  namespace `TauCeti.SmoothTwoForm`, gives an orbit `x` of `H'_q` at the end of `u ∘ φ'_q`.
  Reading it with the time `±t` of the end gives an orbit of `H_q`, since
  `X_{H'_q(±t)} = ±X_{H_q(t)}` (`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`,
  `TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`,
  `TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`,
  `TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul`,
  `TauCeti.Floer.exists_nullhomotopic_positiveEndChart`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace Floer

/-- Reading a `1`-periodic loop with the time `±t` of an end preserves null-homotopy on
`AddCircle 1`. -/
theorem exists_nullhomotopic_comp_endSign_mul {X : Type*} [TopologicalSpace X] (q : Puncture)
    {x : ℝ → X} (hx : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x t) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x (q.endSign * t) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨g', hg', hg'x⟩ := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
  have habs : (1 : ℝ) / |q.endSign| = 1 := by rw [q.abs_endSign, div_one]
  exact habs ▸ ⟨g', hg', fun t ↦ by rw [hg'x t, hgx, mul_comm]⟩

/-- On a manifold `M`, a null-homotopic end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) of a map `u`
continuous on `S` yields a null-homotopic positive-end loop `t ↦ u(φ'_q(s, t))` at every `s > 0`. -/
theorem exists_nullhomotopic_positiveEndChart {E G M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace G] (I : ModelWithCorners ℝ E G) [TopologicalSpace M]
    [ChartedSpace G M] {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    {q : Puncture} {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : 0 < s)
    (hnull : ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s, t)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  exact (exists_nullhomotopic_slice_iff_of_isPreconnected isPreconnected_Ioi
    (hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn fun _ hz ↦
      positiveEndChart_mem_thricePuncturedSphereReal hz.1) one_pos
    (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one]) hs₀ hs).1
    (by simpa only [comp_apply, positiveEndChart_mk] using
      exists_nullhomotopic_comp_endSign_mul q hnull)

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Orbits in positive end charts -/

/-- Reading a one-periodic orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the
end gives a one-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
      1) :
    (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
  by
  rw [mem_periodicSolutions] at hx ⊢
  refine ⟨fun t ↦ ?_, periodic_comp_endSign_mul hx.2⟩
  -- The velocity `±X_{H'_q(±t)}` of `x` at `±t`, rescaled by the sign of the end, is `X_{H_q(t)}`.
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
            (x (q.endSign * t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight q.endSign := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight,
      hamiltonianVectorField_positiveEndHamiltonian_endSign_mul, smul_smul]
  rw [h]
  refine (hx.1 (q.endSign * t)).comp t (hasMFDerivAt_iff_hasFDerivAt.2 ?_)
  exact ((hasDerivAt_id' t).const_mul q.endSign).hasFDerivAt.congr_fderiv
    (ContinuousLinearMap.ext_ring (by simp))

/-- **Orbits in positive end charts.** A curve `x : ℝ → M` is a `1`-periodic solution of `X_{H'_q}`
iff `t ↦ x(±t)` is a `1`-periodic solution of `X_{H_q}`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  rw [show x = fun t ↦ (fun s ↦ x (q.endSign * s)) (q.endSign * t) from
    funext fun t ↦ congrArg x (endSign_mul_endSign_mul q t).symm]
  exact mem_periodicSolutions_comp_endSign_mul (H := positiveEndHamiltonian H)
    ((positiveEndHamiltonian_positiveEndHamiltonian H q).symm ▸ hx)

/-- **Contractible orbits in positive end charts.** A curve `x : ℝ → M` is a contractible
`1`-periodic solution of `X_{H'_q}` iff `t ↦ x(±t)` is one of `X_{H_q}`. -/
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff]
  refine and_congr_right fun _ ↦ ⟨exists_nullhomotopic_comp_endSign_mul q, fun h ↦ ?_⟩
  simpa only [endSign_mul_endSign_mul] using exists_nullhomotopic_comp_endSign_mul q h

/-! ### Asymptotic orbits at the ends -/

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F} {b c : ℝ} {B : Set M} {u : ℝ × ℝ → M} {q : Puncture}

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on each
end `q`, for `1`-periodic Hamiltonians `H` with `H_q` jointly `C¹`, and let `u` be `C¹` on `S`,
with image in a compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `B` and with
injective differential at the points of `B`, and suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q`, the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `S` is finite, then at the end
`q` there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `H_q` in `B` and
`s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`,
pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud := hu.mdifferentiableOn one_ne_zero
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder for `H'_q`.
  obtain ⟨x, hx, hxB, φ, -, hφ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ hmem z hz.1)
      (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem (s, t) hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v)
      (fun z hz ↦ mfderiv_comp_positiveEndChart_add_eq_zero hKH hH hHd (haT.trans hz.1.le)
        ((hud _ (hmem z hz.1)).mdifferentiableAt
          (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz.1)))
        (hfloer _ (hmem z hz.1)))
      (ne_top_of_le_ne_top hE
        (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd hud ha₀ haT))
  -- Read the orbit and the loops with the time `±t` of the end.
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, φ, hφ, ?_, fun t ↦ ?_⟩
  · simp only [endChart_eq_positiveEndChart]
    exact hconv.comp fun t ↦ q.endSign * t
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
`[CompactSpace M]` case of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHq he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE hc hJc).imp
    fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-- **A contractible end of a finite-energy Floer pair of pants breaks off a contractible periodic
orbit.** Under `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, if
some end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic on `AddCircle 1`, the sequential
limit orbit `y` is contractible. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧ ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  obtain ⟨y, hy, hyB, σ, hσ, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHq he
      hB he_inj hde hu huB J hfloer hE hc hJc
  have hpos := hσ.eventually_gt_atTop (0 : ℝ)
  have hmem {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs)
  refine ⟨y, (mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp
    (γ := fun n t ↦ u (endChart q (q.endSign * σ n, t))) hB
    he.continuous.continuousOn he_inj one_pos hy hyB
    (hpos.mono fun _ hn ↦ hu.continuousOn.comp_continuous ((contDiff_endChart q 0).continuous.comp
      (continuous_const.prodMk continuous_id)) (hmem hn))
    (.of_forall fun _ _ ↦ by simp only [endChart_add_one])
    (hpos.mono fun _ hn t ↦ huB _ (hmem hn t)) hux).2 (hpos.mono fun _ hn ↦ ?_), hyB, σ, hσ, hux,
    hpt⟩
  simpa only [← endChart_eq_positiveEndChart] using exists_nullhomotopic_comp_endSign_mul q
    (exists_nullhomotopic_positiveEndChart I hu.continuousOn hs₀ hn hnull₀)

/-- `[CompactSpace M]` case of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHq : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH
    hH hHq he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hfloer
    hE hc hJc).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
