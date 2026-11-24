/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Floer.Tameness
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# Contractible asymptotic orbits and energy identity at the ends of a Floer pair of pants

In Hamiltonian Floer cohomology and the pair-of-pants product on a general closed symplectic
manifold `(M, ω)`, generators are contractible `1`-periodic orbits of the end Hamiltonians `H_q`,
and generic perturbations make contractible `1`-periodic orbits nondegenerate without necessarily
controlling noncontractible `1`-periodic orbits. Moreover, for a capped pair-of-pants solution
whose symplectic area and curvature are integrable and whose image lies in a compact set `B ⊆ M`,
finiteness of the Floer energy is a consequence of the truncated energy identity rather than an
independent hypothesis.

This file upgrades the manifold pair-of-pants asymptotics and energy identity of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold` to the contractible sector:

* **Null-homotopy along positive ends.** Time reversal by `q.endSign` preserves circle
  null-homotopy on `AddCircle 1` (`TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul`) and
  identifies contractible `1`-periodic orbits of the positive end Hamiltonian `H'_q` with those of
  `H_q` (`TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_comp_endSign_mul` and
  `TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`). When one
  end loop `t ↦ u(φ_q(±s₀, t))` lifts to a null-homotopic map `AddCircle 1 → M`, every slice along
  that positive end does (`TauCeti.Floer.exists_nullhomotopic_positiveEndChart_of_subset` and
  `TauCeti.Floer.exists_nullhomotopic_positiveEndChart`).
* **Breaking and convergence in the contractible sector.** Sequential breaking along a contractible
  end produces a contractible `1`-periodic orbit in `B`
  (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`, and
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer`, in
  `TauCeti.SmoothTwoForm.IsNondegenerate`). Whole-end convergence as `s → ∞` holds assuming
  isolation or nondegeneracy only among contractible `1`-periodic orbits in `B`
  (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  and `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer`).
* **Energy identity without an a priori energy bound.** Boundedness of `H_q` on `[0, 1] × B`
  bounds the end-loop integrals eventually along each end, so
  `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm`
  automatically forces finite total Floer energy when symplectic area and curvature are integrable.
  Consequently, the end loops converge to contractible `1`-periodic orbits `y_q`, the Floer energy
  density is integrable on `S`, and `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`
  both for general perturbations cylindrical on the ends
  (`exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm_of_isolated` and
  `exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm`) and for
  `TauCeti.Floer.pairOfPantsPerturbation`
  (`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isolated`,
  `exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`, and
  `exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
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

/-- In a locally path-connected, semilocally simply connected space `X`, if `u` is continuous on a
domain `U ⊆ ℝ × ℝ` containing the positive end `s > a` of `q`, then a null-homotopic end loop
`t ↦ u(φ_q(±s₀, t))` (`s₀ > a`) yields a null-homotopic positive-end loop `t ↦ u(φ'_q(s, t))` at
every `s > a`. -/
theorem exists_nullhomotopic_positiveEndChart_of_subset {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] {U : Set (ℝ × ℝ)}
    {u : ℝ × ℝ → X} (hu : ContinuousOn u U) {q : Puncture} {a : ℝ}
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) {s₀ s : ℝ} (hs₀ : a < s₀)
    (hs : a < s)
    (hnull : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s, t)) := by
  refine (exists_nullhomotopic_slice_iff_of_isPreconnected isPreconnected_Ioi
    (hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn fun _ hz ↦ haU _ hz.1)
    one_pos (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one]) hs₀ hs).1 ?_
  simpa only [comp_apply, positiveEndChart_mk] using exists_nullhomotopic_comp_endSign_mul q hnull

/-- In a locally path-connected, semilocally simply connected space `X`, a null-homotopic end loop
`t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) of a map `u` continuous on `S` yields a null-homotopic positive-end
loop `t ↦ u(φ'_q(s, t))` at every `s > 0`. -/
theorem exists_nullhomotopic_positiveEndChart {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] {u : ℝ × ℝ → X}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture} {s₀ s : ℝ} (hs₀ : 0 < s₀)
    (hs : 0 < s)
    (hnull : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s, t)) :=
  exists_nullhomotopic_positiveEndChart_of_subset hu
    (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal hζ) hs₀ hs hnull

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-- Reading a contractible `1`-periodic orbit of `H'_q` with the time `±t` of the end gives a
contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ contractiblePeriodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions] at hx ⊢
  exact ⟨mem_periodicSolutions_comp_endSign_mul hx.1, exists_nullhomotopic_comp_endSign_mul q hx.2⟩

/-- A curve `x` is a contractible `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and
only if `t ↦ x(±t)`, with the sign of the end, is a contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff]
  refine and_congr_right fun _ ↦ ⟨exists_nullhomotopic_comp_endSign_mul q, fun h ↦ ?_⟩
  simpa only [endSign_mul_endSign_mul] using exists_nullhomotopic_comp_endSign_mul q h

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

namespace IsNondegenerate

/-! ### Breaking off contractible periodic orbits along sequences -/

/-- **A finite-energy Floer solution on an open end breaks off a contractible periodic orbit.** Let
`ω` be a nondegenerate two-form on a manifold `M`, `K` equal to `H_q(t) dt` beyond `T₀` on an end
`q` for a `1`-periodic `C¹` Hamiltonian `H_q`, and `u` a `C¹` map on an open set `U` containing the
part `±s > a` of the end `q`, with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on
`U` with finite energy and uniform tameness relative to `e : M → F`. If some end loop
`t ↦ u(φ_q(±s₀, t))` (`s₀ > a`) lifts to a null-homotopic map `AddCircle 1 → M`, then `u` breaks
off a contractible `1`-periodic orbit `y` of `H_q` in `B` along a sequence `σ_n → ∞`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (huB : ∀ z ∈ U, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧ ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  obtain ⟨y, hy, hyB, σ, hσ, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen q hKH hH hHs he hB
      he_inj hde hU hu huB J hc hJc hfloer hE haU
  have hgt := hσ.eventually_gt_atTop a
  have hmem {s : ℝ} (hs : a < s) (t : ℝ) : endChart q (q.endSign * s, t) ∈ U := by
    rw [endChart_eq_positiveEndChart]
    exact haU _ hs
  refine ⟨y, (mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp
    (γ := fun n t ↦ u (endChart q (q.endSign * σ n, t))) hB
    he.continuous.continuousOn he_inj one_pos hy hyB
    (hgt.mono fun _ hn ↦ hu.continuousOn.comp_continuous ((contDiff_endChart q 0).continuous.comp
      (continuous_const.prodMk continuous_id)) (hmem hn))
    (.of_forall fun _ _ ↦ by simp only [endChart_add_one])
    (hgt.mono fun _ hn t ↦ huB _ (hmem hn t)) hux).2 (hgt.mono fun _ hn ↦ ?_), hyB, σ, hσ, hux,
    hpt⟩
  simpa only [← endChart_eq_positiveEndChart] using exists_nullhomotopic_comp_endSign_mul q
    (exists_nullhomotopic_positiveEndChart_of_subset hu.continuousOn haU hs₀ hn hnull₀)

/-- **A contractible end of a finite-energy Floer pair of pants in a manifold breaks off a
contractible periodic orbit.** Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen` to the
whole thrice-punctured sphere `S`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧ ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen q hKH hH
    hHs he hB he_inj hde isOpen_thricePuncturedSphereReal hu huB J hc hJc hfloer hE (a := 0)
    (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal hζ) hnull

/-- **A contractible end of a finite-energy Floer pair of pants in a closed manifold breaks off a
contractible periodic orbit.** Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` when `M`
is compact and `B = univ`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact q hKH
    hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hc hJc
    hfloer hE).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-! ### Convergence along the whole end in the contractible sector -/

/-- **Convergence of a contractible end of a Floer pair of pants to an isolated contractible
orbit.** Let `ω` be a nondegenerate two-form on `M`, `K` equal to `H_q(t) dt` beyond `T₀` on an end
`q` for a `1`-periodic `C¹` Hamiltonian `H_q`, and `u` a `C¹` map on `S` with image in a compact set
`B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy, such that some end loop
`t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) lifts to a null-homotopic map `AddCircle 1 → M`. Let `e : M → F` be
`C¹`, injective on `B` with injective differential on `B`, suppose that `(e ∘ u) ∘ φ'_q` has bounded
derivative and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` (`c > 0`) on `(b, ∞) × [0, 1]`, and suppose that
each contractible `1`-periodic orbit `y` of `H_q` in `B` is isolated at `t = 0` among contractible
`1`-periodic orbits of `H_q` in `B` (noncontractible orbits need not be isolated). Then
`t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single contractible `1`-periodic orbit `y` of `H_q`
in `B`, uniformly after `e` and pointwise in `M`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b C : ℝ} (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : z ∈ Ioi a ×ˢ Icc 0 1) : z ∈ Ioi b ×ˢ Icc 0 1 :=
    ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩
  have hS {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ Icc 0 1) :
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
        J (positiveEndChart q z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
            ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
              (u (positiveEndChart q z))) = 0 := by
    have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
      (haT.trans hz.1.le)
      ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hz.1))).mdifferentiableAt
        one_ne_zero) (hfloer _ (hS hz.1))
    simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
      (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
        (J (positiveEndChart q z))).1 hcl
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  -- Time reversal fixes `t = 0`, so isolation at `0` among contractible orbits transfers to `H'_q`.
  have hiso' : ∀ x ∈ contractiblePeriodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1, (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have h0 := hiso (fun t ↦ x (q.endSign * t))
      (mem_contractiblePeriodicSolutions_comp_endSign_mul hx) (fun _ ↦ hxB _)
    rw [mul_zero] at h0
    refine h0.mono fun p hp x' hx' hx'B hx'0 ↦ funext fun t ↦ ?_
    have heq := congrFun (hp (fun r ↦ x' (q.endSign * r))
      (mem_contractiblePeriodicSolutions_comp_endSign_mul hx') (fun _ ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using heq
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian hHs) (periodic_positiveEndHamiltonian hH) he hB
      he_inj hde
      (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun _ hz ↦ hS hz.1)
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hS hs))
      ⟨a + 1, lt_add_one a, exists_nullhomotopic_positiveEndChart hu.continuousOn hs₀
        (add_pos_of_nonneg_of_pos ha₀ zero_lt_one) hnull₀⟩
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab hz) v) hfloer'
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le q hKH hH hHd
        (hu.mdifferentiableOn one_ne_zero) ha₀ haT))
      (fun z hz ↦ hC z (hab hz)) hiso'
  refine ⟨_, mem_contractiblePeriodicSolutions_comp_endSign_mul hx, fun _ ↦ hxB _, ?_, fun t ↦ ?_⟩
  · rw [funext fun s ↦ comp_endChart_eq_comp_positiveEndChart (fun z ↦ e (u z)) q s]
    exact hconv.comp _
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Convergence of a contractible end of a Floer pair of pants to a nondegenerate contractible
orbit.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` equal to
`H_q(t) dt` beyond `T₀` on an end `q` for a `1`-periodic `C²` Hamiltonian `H_q`, and `u` a `C¹` map
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy
and a null-homotopic end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`). If `(e ∘ u) ∘ φ'_q` has bounded
derivative and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` (`c > 0`) on `(b, ∞) × [0, 1]`, and every
contractible `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate (noncontractible orbits need
not be nondegenerate), then `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single contractible
`1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b C : ℝ} (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated q
    hKH hH (hHs.of_le one_le_two) he hB he_inj hde hu huB hnull J hfloer hE hC hc hJc
    fun y hy hyB ↦
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq hHs
        (contractiblePeriodicSolutions_subset hy) (hnd y hy hyB)).mono fun _ hp y' hy' _ ↦
          hp y' (contractiblePeriodicSolutions_subset hy')

/-- **Convergence of a contractible end of a Floer pair of pants in a closed manifold to a
nondegenerate contractible orbit.** Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
when `M` is compact and `B = univ`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {b C : ℝ} (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    q hKH hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J
    hfloer hE hC hc hJc fun y hy _ ↦ hnd y hy).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-! ### Global pair-of-pants energy identity at contractible asymptotic orbits -/

/-- **The pair-of-pants energy identity with isolated contractible asymptotic orbits, for a manifold
target.** Let `ω` be a nondegenerate two-form on `M`, `K` a `C¹` perturbation on `S × M` equal to
`H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with integrable
symplectic area and curvature and a null-homotopic end loop on each end `q`. Let `e : M → F` be
`C¹`, injective on `B` with injective differential on `B`, suppose `c ‖d e v‖² ≤ ω(v, J z v)` on
`S` (`c > 0`), that `(e ∘ u) ∘ φ'_q` has bounded derivative on some strip `(b, ∞) × [0, 1]` at each
end `q`, and that every contractible `1`-periodic orbit of `H_q` in `B` is isolated at `t = 0` among
contractible `1`-periodic orbits in `B`. Then finite energy follows automatically from
`lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm`, the end loops converge as `s → ∞` to
contractible `1`-periodic orbits `y_q` of `H_q` in `B`, the Floer energy density is integrable on
`S`, and `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm_of_isolated
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    floerEnergyDensity_nonneg hω (hω.tames_of_mul_norm_sq_le (hde _ (huB z hz)) hc (hJc z hz))
      (hfloer z hz)
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rwa [IntegrableOn, hS] at hR
  -- Boundedness of `H_q` on `[0, 1] × B` bounds end-loop integrals, forcing finite total energy.
  choose M₀ hM₀ using fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHs q).continuous.continuousOn
  have hM (q : Puncture) : ∀ᶠ σ in atTop,
      |∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t)))| ≤ M₀ q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := M₀ q) (f := fun t ↦ H q t (u (endChart q (q.endSign * σ, t))))
      fun t ht ↦ hM₀ q (t, _) ⟨Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht),
        huB _ (endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hσ))⟩
  have hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
    rw [hS]
    exact ((hω.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg hA'
      hR' hM).trans_lt ENNReal.ofReal_lt_top).ne
  have hy_ex : ∀ q,
      ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, hbC⟩ := hC q
    exact
      exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
        hω q (hKH q) (hH q) (hHs q) he hB he_inj hde hu huB (hnull q) J hfloer hE (b := max b 0)
        (fun z hz ↦ hbC z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) hc
        (fun z hz v ↦ hJc _
          (positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz.1)) v)
        (hiso q)
  choose y hy hyB hyu hyp using hy_ex
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
        atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB hu.continuousOn huB
      (hyp q)
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA' hR' hh
  refine ⟨y, fun q ↦ ⟨hy q, hyB q, hyu q, hyp q, hh q⟩, ?_, ?_⟩
  · rwa [IntegrableOn, hS]
  · simp only [hS]
    exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA' hR' hh

/-- **The pair-of-pants energy identity with nondegenerate contractible asymptotic orbits, for a
manifold target.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`,
`K` a `C¹` perturbation on `S × M` equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic
`C²` Hamiltonians `H_q`, and `u` a `C¹` map on `S` with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with integrable symplectic area and curvature and a null-homotopic end
loop on each end `q`. If `c ‖d e v‖² ≤ ω(v, J z v)` on `S` (`c > 0`), `(e ∘ u) ∘ φ'_q` has bounded
derivative on some strip `(b, ∞) × [0, 1]` at each end `q`, and every contractible `1`-periodic
orbit of `H_q` in `B` is nondegenerate (noncontractible orbits need not be nondegenerate), then the
end loops converge as `s → ∞` to contractible `1`-periodic orbits `y_q` in `B`, the Floer energy
density is integrable on `S`, and `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
  hω.exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm_of_isolated
    hK hKH hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB hnull J hc hJc hfloer hA
    hR hC fun q y hy hyB ↦
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q)
        (contractiblePeriodicSolutions_subset hy) (hnd q y hy hyB)).mono fun _ hp y' hy' _ ↦
          hp y' (contractiblePeriodicSolutions_subset hy')

/-- **The energy identity for `pairOfPantsPerturbation` with isolated contractible asymptotic orbits
in a compact set.** Specialization of
`exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm_of_isolated` to
`TauCeti.Floer.pairOfPantsPerturbation H`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isolated
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  hω.exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm_of_isolated
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hC hiso

/-- **The energy identity for `pairOfPantsPerturbation` with nondegenerate contractible asymptotic
orbits in a compact set.** Specialization of
`exists_mem_contractiblePeriodicSolutions_integral_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation H`. -/
theorem
    exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  hω.exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isolated
    hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB hnull J hc hJc hfloer hA hC
    fun q y hy hyB ↦
      (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq (hHs q)
        (contractiblePeriodicSolutions_subset hy) (hnd q y hy hyB)).mono fun _ hp y' hy' _ ↦
          hp y' (contractiblePeriodicSolutions_subset hy')

/-- **The energy identity for `pairOfPantsPerturbation` with nondegenerate contractible asymptotic
orbits on a closed manifold.** Specialization of
`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact` when `M` is
compact and `B = univ`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s₀ > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hid⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hc
      hJc hfloer hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
