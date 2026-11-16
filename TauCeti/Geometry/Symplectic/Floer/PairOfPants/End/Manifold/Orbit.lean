/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart

/-!
# Periodic-orbit breaking at the ends of a Floer pair of pants in a manifold

For a nondegenerate two-form `ω` on a finite-dimensional manifold `M`, a perturbation `K` on
`S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond `T₀` for `1`-periodic `H_q`, and a finite-energy `C¹`
Floer solution `u` in a compact `B ⊆ M` with uniformly tame `J` via `e`, this file adapts
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` to manifolds (see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold.Convergence` for end convergence and the
energy identity):

* **Positive end charts.** `u ∘ φ'_q` solves the half-cylinder Floer equation for `H'_q` with energy
  bounded by that on `S` (`isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`,
  `mfderiv_comp_positiveEndChart_add_eq_zero`,
  `setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`), and `t ↦ ±t` identifies full and
  contractible `1`-periodic orbits of `H'_q` and `H_q`
  (`Floer.exists_nullhomotopic_comp_endSign_mul`, `Floer.exists_nullhomotopic_positiveEndChart`,
  `mem_periodicSolutions_positiveEndHamiltonian_iff`,
  `mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`).
* **Sequential end breaking.** `t ↦ u(φ_q(±σ_n, t))` converges along some `σ_n → ∞` to a full or
  contractible `1`-periodic orbit in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer`, `_of_isCompact`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis, ETH Zürich
  (1995).
-/

public section

open Set Filter Topology MeasureTheory Function Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

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

section PositiveEnd

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {q : Puncture} {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}

/-- The Hamiltonian vector field of `H'_q(t)` is `±` that of `H_q(±t)`. -/
@[simp]
theorem hamiltonianVectorField_positiveEndHamiltonian (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (q : Puncture) (t : ℝ) (p : M) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q t) p =
      q.endSign • ω.hamiltonianVectorField (H q (q.endSign * t)) p := by
  rw [show positiveEndHamiltonian H q t = q.endSign • H q (q.endSign * t) from
    funext fun _ ↦ by simp [positiveEndHamiltonian_apply], hamiltonianVectorField_const_smul]

/-- Reading a curve with `±t` carries `1`-periodic orbits of `X_{H'_q}` to those of `X_{H_q}`. -/
private theorem mem_periodicSolutions_comp_endSign_mul {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  refine mem_periodicSolutions.2 ⟨fun t ↦ ?_, periodic_comp_endSign_mul hxper⟩
  have hφ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) := by
    simpa only [Pi.smul_def, id_eq, smul_eq_mul] using hasMFDerivAt_iff_hasFDerivAt.2
      ((hasFDerivAt_id t).const_smul q.endSign)
  have hd := hxd (q.endSign * t)
  simp only [hamiltonianVectorField_positiveEndHamiltonian, endSign_mul_endSign_mul] at hd
  have heq (r : ℝ) : (((1 : ℝ →L[ℝ] ℝ).smulRight
        (q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))).comp
        (q.endSign • ContinuousLinearMap.id ℝ ℝ)) r =
      (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) r := by
    rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> simp [h]
  exact (hd.comp t hφ).congr_mfderiv (ContinuousLinearMap.ext heq)

/-- **Orbits in positive end charts.** A curve `x : ℝ → M` is a `1`-periodic solution of `X_{H'_q}`
iff `t ↦ x(±t)` is a `1`-periodic solution of `X_{H_q}`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {x : ℝ → M} :
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
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff]
  refine and_congr_right fun _ ↦ ⟨exists_nullhomotopic_comp_endSign_mul q, fun h ↦ ?_⟩
  simpa only [endSign_mul_endSign_mul] using exists_nullhomotopic_comp_endSign_mul q h

omit [IsManifold I ⊤ M] in
/-- Beyond `T₀` on the end `q`, `K` is target-differentiable when `H_q(t)` is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) (hζ : T₀ ≤ ζ.1) (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]; simpa [← mul_assoc] using hζ
  rw [show (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) =
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im from
    funext fun x ↦ by simpa [hKH q _ x hre] using mul_comm _ _]
  exact (hHd _ y).const_smul _

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** When
`K = H_q(t) dt` beyond `T₀` and `u` solves `(du - X_K)^{0,1} = 0` at `φ'_q(ζ)` (`ζ.1 ≥ T₀`),
`u ∘ φ'_q` solves `(dv - X_{H'_q} dt)^{0,1} = 0` at `ζ`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [ω.perturbedMFDeriv_congr (u ∘ positiveEndChart q)
    (funext fun x ↦ (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x).symm)
    (funext fun x ↦
      (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x).symm)]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **Half-cylinder PDE form on a positive end chart.** Under
`isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`, `u ∘ φ'_q` satisfies
`∂_s (u ∘ φ'_q) + J (∂_t (u ∘ φ'_q) - X_{H'_q}) = 0` at `ζ`. -/
theorem mfderiv_comp_positiveEndChart_add_eq_zero
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) ζ stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) ζ stdComplexLineImag -
        ω.hamiltonianVectorField (positiveEndHamiltonian H q ζ.2) (u (positiveEndChart q ζ))) =
      0 := by
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
    (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) ζ J).1
      (isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd hζ hu hfloer)

/-- **The energy of an end of a Floer pair of pants in a manifold.** When `K = H_q(t) dt` beyond
`T₀` on each end `q`, the lower Lebesgue energy of `u ∘ φ'_q` for `H'_q` over `(a, ∞) × [0, 1]`
(`a ≥ max T₀ 0`) is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    (hu : ∀ z ∈ thricePuncturedSphereReal, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]; exact Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Icc.symm
  have hdens (ζ : ℝ × ℝ) (hζ : ζ ∈ s) : ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * e (positiveEndChart q ζ) := by
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    rw [floerEnergyDensity_def, ω.perturbedMFDeriv_congr (u ∘ positiveEndChart q)
      (funext fun x ↦
        (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζT x).symm)
      (funext fun x ↦
        (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζT x).symm),
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      (hu _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul
    (measurableSet_Ioi.prod measurableSet_Ioo)
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  exact lintegral_mono_set fun _ ⟨ζ, hζ, h⟩ ↦
    h ▸ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

end PositiveEnd

namespace IsNondegenerate

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ b c : ℝ} {e : M → F} {B : Set M} {u : ℝ × ℝ → M} {q : Puncture}

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
For `K = H_q(t) dt` beyond `T₀` with `1`-periodic `H_q` jointly `C¹` at `q`, a finite-energy `C¹`
Floer solution `u` on `S` in a compact `B ⊆ M` with uniformly tame `J` on `q` via `e` has
`t ↦ u(φ_q(±σ_n, t)) → y` along some `σ_n → ∞` for a `1`-periodic orbit `y` of `X_{H_q}` in `B`. -/
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
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) := fun x ↦
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have humd (z) (hz : z ∈ thricePuncturedSphereReal) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :=
    positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hz)
  obtain ⟨x, hx, hxB, σ, -, hσ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHq) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde (hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun _ hz ↦
        hmem hz.1)
      (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun _ hs _ ↦ huB _ (hmem hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v)
      (fun _ hz ↦ mfderiv_comp_positiveEndChart_add_eq_zero hKH hH hHd (haT.trans hz.1.le)
        (humd _ (hmem hz.1)) (hfloer _ (hmem hz.1)))
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
        humd ha₀ haT))
  exact ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_positiveEndHamiltonian_iff.1 hx,
    fun _ ↦ hxB _, σ, hσ,
    by simpa only [comp_def, ← endChart_eq_positiveEndChart] using hux.comp (q.endSign * ·),
    fun t ↦ by simpa only [comp_apply, ← endChart_eq_positiveEndChart] using hpt (q.endSign * t)⟩

/-- **A finite-energy Floer pair of pants on a closed manifold breaks off a periodic orbit at each
end.** `[CompactSpace M]` case of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
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
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
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
