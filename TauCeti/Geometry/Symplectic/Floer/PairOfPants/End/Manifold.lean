/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Asymptotic orbits and end convergence for Floer pairs of pants in manifolds

Let `K` be a Hamiltonian perturbation datum on the pair of pants `S = ℂ ∖ {0, 1}` — a one-form on
`S` valued in functions on a finite-dimensional target manifold `M` carrying a nondegenerate
two-form `ω` — equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one
Hamiltonians `H_q`, and let `u : S → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` for
uniformly tame almost complex structures `J z` on the tangent spaces `T_{u z} M`. Suppose that `u`
maps `S` into a compact set `B ⊆ M` and has finite Floer energy. This file shows that `u` breaks
off a `1`-periodic orbit of `X_{H_q}` at each end `q`, that the end loops converge along the whole
end `s → ∞` when the periodic orbits of `H_q` in `B` are nondegenerate and the end derivative is
bounded, and that the pair-of-pants energy identity holds with the boundary terms evaluated at
these asymptotic periodic orbits.

**Positive end charts on a manifold.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), where `s → +∞` along every end, the perturbation `K` pulls back
to `H'_q(t) dt` beyond `T₀` for the positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`). Since `φ'_q` is holomorphic and orientation preserving,
`u ∘ φ'_q` solves the half-cylinder Floer equation for `H'_q` beyond `T₀`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), and its energy
over `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). Reading a
`1`-periodic orbit of `X_{H'_q}` with the time `±t` of the end gives a `1`-periodic orbit of
`X_{H_q}` (`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`).

**Breaking and convergence at the ends.** Uniform convergence and uniform tameness near `B` are
measured through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on `B`
with injective differential on `B`, as in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`:

* Without nondegeneracy or derivative bounds, at each end `q` there are a `1`-periodic orbit `y_q`
  of `X_{H_q}` in `B` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))` converge to `y_q`,
  pointwise in `M` and uniformly after applying `e`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  and `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer` on a
  compact manifold).
* When `H_q` is `C²` on a Hausdorff boundaryless manifold, `d(e ∘ u ∘ φ'_q)` is bounded on some
  half-cylinder `s > b`, and every `1`-periodic orbit of `X_{H_q}` in `B` starts at a nondegenerate
  fixed point of the time-one map, time reversal transfers isolation to the `1`-periodic orbits of
  `X_{H'_q}`, so the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` along the whole end to a
  single `1`-periodic orbit `y_q` (`IsNondegenerate` theorem
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer` on a compact manifold).

**The manifold energy identity with asymptotic orbits.** Since `u` maps `S` into the compact set
`B`, a continuous Hamiltonian `H_q` is bounded on `[0, 1] × B`, so dominated convergence gives
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt → ∫₀¹ H_q(t, y_q(t)) dt` along any convergent end without a global
bound on `H_q` (`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`). Combined with
whole-end convergence at nondegenerate ends, the Floer energy density is integrable over `S` and
satisfies

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

for genuine asymptotic `1`-periodic orbits `y_q` of the end Hamiltonians
(`IsNondegenerate.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`, and
`IsNondegenerate.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`
for `TauCeti.Floer.pairOfPantsPerturbation`). This is the manifold counterpart of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and the nondegenerate end-convergence
theorems of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy identity of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti

namespace Floer

/-- If `u` maps `S` into a compact set `B` and its loops along the circles `±s` of the end `q`
converge pointwise to `y` as `s → ∞`, then the integrals of a continuous Hamiltonian `H` along them
converge to its integral along `y`. No global bound on `H` outside `B` is needed. -/
theorem tendsto_intervalIntegral_endChart_of_isCompact {M : Type*} [TopologicalSpace M]
    {H : ℝ → M → ℝ} (hHc : Continuous (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) {B : Set M} (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {q : Puncture} {y : ℝ → M}
    (hy : ∀ t, Tendsto (fun s : ℝ ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, H t (u (endChart q (q.endSign * s, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H t (y t))) := by
  -- On `[0, 1] × B` the continuous Hamiltonian is bounded, and for `s > 0` the end loops stay in
  -- `S`, hence in `B`.
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hB).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1 ×ˢ B) hHc.continuousOn
  have hmem {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C) ?_ ?_
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, y t)).comp (tendsto_const_nhds.prodMk_nhds (hy t)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hloop : Continuous fun t : ℝ ↦ u (endChart q (q.endSign * s, t)) :=
      hu.comp_continuous ((contDiff_endChart q 0).continuous.comp (by fun_prop)) (hmem hs)
    exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hC (t, u (endChart q (q.endSign * s, t))) ⟨⟨ht.1.le, ht.2⟩, huB _ (hmem hs t)⟩

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Orbits and positive end charts on a manifold -/

/-- Reading an orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the end gives an
orbit of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ x (q.endSign * t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ ↦ q.endSign * τ) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_smul q.endSign)
  have h := (hx (q.endSign * t)).comp t hg
  have hH : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self,
      one_mul]
  refine h.congr_mfderiv (ContinuousLinearMap.ext fun (r : ℝ) ↦ ?_)
  change (q.endSign * r) • ω.hamiltonianVectorField
      (positiveEndHamiltonian H q (q.endSign * t)) (x (q.endSign * t)) =
    r • ω.hamiltonianVectorField (H q t) (x (q.endSign * t))
  rw [hH, hamiltonianVectorField_const_smul, smul_smul,
    show q.endSign * r * q.endSign = r * (q.endSign * q.endSign) by ring, endSign_mul_self,
    mul_one]

/-- A `1`-periodic orbit of the positive end Hamiltonian `H'_q`, read with the time `±t` of the
end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  exact mem_periodicSolutions.2 ⟨hasMFDerivAt_comp_endSign_mul hxd, periodic_comp_endSign_mul hxper⟩

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the positive end chart are differentiable
in the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)
      y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact ((hHd q _) y).const_smul _

/-- Beyond `T₀` on the end `q`, the pulled-back perturbation along the positive end chart is
`H'_q(t) dt`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      ω.perturbedMFDeriv
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positiveEndChart q) ζ := by
  refine ContinuousLinearMap.ext fun (a : ℝ × ℝ) ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply,
    funext fun x ↦
      perturbationPullback_positiveEndChart_stdComplexLineReal_of_le (q := q) hKH hζ x,
    funext fun x ↦
      perturbationPullback_positiveEndChart_stdComplexLineImag_of_le (q := q) hKH hH hζ x]

/-- **The ends of a Floer pair of pants in a manifold solve the Floer equation of a
half-cylinder.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for Hamiltonians
`H_q` that are `1`-periodic in time and differentiable in the target variable, and let `u` be
differentiable at the image `φ'_q(ζ)` of a point `ζ` with `s ≥ T₀` of the positive end chart and
solve the Floer equation `(du - X_K)^{0,1} = 0` there for the almost complex structure `J` on
`T_{u(φ'_q(ζ))} M`. Then `u ∘ φ'_q` solves the half-cylinder Floer equation
`∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` at `ζ`, for the end Hamiltonian `H'_q` of the positive
end. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    {q : Puncture} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))}
    (hζ : T₀ ≤ ζ.1) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **The energy of an end of a Floer pair of pants in a manifold.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on each end `q`, for Hamiltonians `H_q` that are `1`-periodic in time and
differentiable in the target variable, and let `u` be differentiable on `S`. Then the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal) (q : Puncture) {a : ℝ}
    (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  -- On the open band the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * e (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζ₀ : 0 < ζ.1 := ha₀.trans_lt hζ.1
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

/-! ### Asymptotic orbits at the ends -/

section EndOrbits

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Reading the end loop of `e ∘ u ∘ φ'_q` with the time `±t` of the end gives the end loop of
`e ∘ u`. -/
private theorem comp_endChart_eq_comp_positiveEndChart {u : ℝ × ℝ → M} (q : Puncture) (s : ℝ) :
    (fun t ↦ e (u (endChart q (q.endSign * s, t)))) =
      (fun t ↦ e ((u ∘ positiveEndChart q) (s, t))) ∘ fun t ↦ q.endSign * t := by
  funext t
  simp only [comp_apply, endChart_eq_positiveEndChart]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- On a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0`, `u ∘ φ'_q` solves the coordinate
half-cylinder Floer equation and has finite energy when `u` solves `(du - X_K)^{0,1} = 0` on `S`
with finite energy. -/
private theorem floer_comp_positiveEndChart_of_le
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd : ∀ r t, MDifferentiable I 𝓘(ℝ) (H r t) := fun r t ↦
    ((hHs r).comp ((contMDiff_const (c := t)).prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn (fun _ hz ↦ hmem hz.1),
    fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      hud q ha₀ haT)⟩
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hud _ (hmem hz.1)).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds (hmem hz.1)))
    (hfloer _ (hmem hz.1))
  have heq := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at heq

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q` on a
manifold `M` carrying a nondegenerate two-form `ω`, and let `u` be `C¹` on `S`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `B` and with
injective differential at the points of `B`, and suppose that the almost complex structures are
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. Then at each end `q`
there are a `1`-periodic orbit `y` of `X_{H_q}` in `B` and `s_n → ∞` such that the loops
`t ↦ u(φ_q(±s_n, t))` converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max T₀ 0
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
  obtain ⟨hu', hfloer', hE'⟩ := floer_comp_positiveEndChart_of_le hKH hH hHs hu hfloer hE q
    (le_max_right _ _) (le_max_left _ _)
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder in `M`.
  obtain ⟨x, hx, hxB, φ, -, hφ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde hu'
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc _ (hmem hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, φ, hφ, ?_, fun t ↦ ?_⟩
  · rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart (e := e) (u := u) q (φ n)]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`
to a compact manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hc hJc hfloer hE q
  exact ⟨y, hy, h⟩

/-! ### Convergence along the whole end to nondegenerate orbits -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A `1`-periodic orbit of the positive end Hamiltonian `H'_q` in `B` is isolated at `t = 0` when
every `1`-periodic orbit of `H_q` in `B` starts at a nondegenerate fixed point of the time-one map
of `H_q`. -/
private theorem exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hHper : Periodic (H q) 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {B : Set M}
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hxB : ∀ t, x t ∈ B) :
    ∃ U ∈ 𝓝 (x 0), ∀ z ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      (∀ t, z t ∈ B) → z 0 ∈ U → z = x := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (H q p.1) p.2⟩ : TangentBundle I M)) :=
    hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (by norm_num [hHs])
  have hXper : Periodic (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
    fun t ↦ congrArg ω.hamiltonianVectorField (hHper t)
  have hy := mem_periodicSolutions_comp_endSign_mul hx
  have hnd₀ : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 (0 + 1))
      ((fun t ↦ x (q.endSign * t)) 0) := by
    simpa only [zero_add] using hnd _ hy (fun t ↦ hxB _)
  obtain ⟨U, hU, hU'⟩ :=
    hnd₀.exists_mem_nhds_forall_mem_periodicSolutions_eq hX hXper one_ne_zero hy
  rw [mul_zero] at hU
  refine ⟨U, hU, fun z hz _ hzU ↦ funext fun t ↦ ?_⟩
  have hzx := congrFun (hU' _ (mem_periodicSolutions_comp_endSign_mul hz)
    (by simpa only [mul_zero] using hzU)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using hzx

/-- **The ends of a Floer pair of pants in a manifold converge to nondegenerate orbits.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q` on a
Hausdorff boundaryless manifold `M` carrying a nondegenerate two-form `ω`, and let `u` be `C¹` on
`S`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix
an end `q` whose Hamiltonian `H_q` is `C²` and whose `1`-periodic orbits in `B` are nondegenerate
fixed points of the time-one map at `t = 0`. Suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q`, `d(e ∘ u ∘ φ'_q)` is bounded and the almost complex structures are
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`. Then the loops
`t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in `B`,
pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  obtain ⟨hu', hfloer', hE'⟩ :=
    floer_comp_positiveEndChart_of_le hKH hH hHs hu hfloer hE q ha₀ haT
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde hu'
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem hs)) (fun z hz ↦ hC z (hab hz.1))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z (hab hz.1) v) hfloer' hE'
      fun x hx hxB ↦
        hω.exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt (hH q) hHsq hnd hx hxB
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · rw [funext fun s ↦ comp_endChart_eq_comp_positiveEndChart (e := e) (u := u) q s]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **The ends of a Floer pair of pants in a closed manifold converge to nondegenerate orbits.**
The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
to a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE q
      hHsq (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, h⟩

end IsNondegenerate

end EndOrbits

end SmoothTwoForm

namespace SmoothTwoForm

open Floer

/-! ### The energy identity with asymptotic orbits on a manifold -/

section EnergyIdentity

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

namespace IsNondegenerate

/-- **The manifold pair-of-pants energy identity with nondegenerate asymptotic orbits.** Let `K` be
`C¹` on `S × M` and equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C²`
Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` with a nondegenerate two-form `ω`,
whose `1`-periodic orbits in a compact set `B` are nondegenerate. Let `u` be `C¹` on `S`, with
image in `B`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy for uniformly tame almost
complex structures measured through `e : M → F`, with integrable area density `u^*ω` and curvature
`R_K(u)` over `S`, and with `d(e ∘ u ∘ φ'_q)` bounded on some half-cylinder of each end `q`. Then
the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic orbits `y_q` of `X_{H_q}` in
`B`, the Floer energy density of `u` is integrable over `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
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
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  -- Obtain the asymptotic `1`-periodic orbit on each end `q`.
  choose b C hbC using hC
  choose y hy using fun q ↦
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH
      hH hHs1 he hB he_inj hde hu huB hfloer hE q (hHs q) (hnd q)
      (b := max (b q) 0) (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) hc
      fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hz)) v
  -- Uniform tameness wrt `e`, with `d e` injective on `B`, gives fiberwise tameness on `S`.
  have hJtame (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      (hω.symplecticFormAt (u z)).Tames (J z) := fun v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 fun hdv ↦
      hv ((hde _ (huB z hz)).eq_iff.1 (by rwa [map_zero]))) 2)).trans_le (hJc z hz v)
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    floerEnergyDensity_nonneg hω (hJtame z hz) (hfloer z hz)
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hu.continuousOn hB huB
      (hy q).2.2.2
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hA hR
  have hint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA hR hh
  refine ⟨y, hy, by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hint hA hR hh

/-- **The energy identity of the pair-of-pants perturbation with nondegenerate asymptotic orbits.**
The specialization of `exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`
to `TauCeti.Floer.pairOfPantsPerturbation`, for which the curvature term is automatically
integrable over `S`. -/
theorem
  exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hE hnd hC

/-- **The energy identity of the pair-of-pants perturbation in a closed manifold.** The
specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`
to a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
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
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hint, hid⟩ :=
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
      hω hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hc hJc
      hfloer hA hE (fun q y hy _ ↦ hnd q y hy) hC
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hint, hid⟩

end IsNondegenerate

end EnergyIdentity

end SmoothTwoForm

end TauCeti
