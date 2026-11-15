/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# Asymptotic orbits and end convergence for Floer pairs of pants in manifolds

Let `K` be a Hamiltonian perturbation datum on the pair of pants `S = ℂ ∖ {0, 1}` — a one-form on
`S` valued in functions on a finite-dimensional target manifold `M` carrying a nondegenerate
two-form `ω` — equal to `H_q(t) dt` beyond some height `T₀` on an end `q` (or on each end `q`), for
period-one Hamiltonians `H_q`, and let `u : S → M` solve the Floer equation `(du - X_K)^{0,1} = 0`
on `S` for uniformly tame almost complex structures `J z` on the tangent spaces `T_{u z} M`. Suppose
that `u` maps `S` into a compact set `B ⊆ M`. This file shows that when `u` has finite Floer energy
it breaks off a `1`-periodic orbit of `X_{H_q}` at `q`, that the end loops converge along the whole
end `s → ∞` when the cluster-point (in particular, contractible) periodic orbits of `H_q` in `B` are
nondegenerate and the end derivative is bounded, and that when `u^*ω` and `R_K(u)` are integrable
over `S` the Floer energy is automatically finite and satisfies the pair-of-pants energy identity
with the boundary terms evaluated at these asymptotic periodic orbits.

**Positive end charts on a manifold.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), where `s → +∞` along every end, the perturbation `K` pulls back
to `H'_q(t) dt` beyond `T₀` for the positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`). Since `φ'_q` is holomorphic and orientation preserving,
`u ∘ φ'_q` solves the half-cylinder Floer equation for `H'_q` beyond `T₀`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), and its energy
over `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). Reading a
`1`-periodic (respectively, contractible `1`-periodic) orbit of `X_{H'_q}` with the time `±t` of the
end gives a `1`-periodic (respectively, contractible `1`-periodic) orbit of `X_{H_q}`
(`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`,
`TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_comp_endSign_mul`).

**Breaking and convergence at an end.** Uniform convergence and uniform tameness near `B` are
measured through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on `B`
with injective differential on `B`, as in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`:

* Without nondegeneracy or derivative bounds, on any end `q` where `K = H_q(t) dt` beyond `T₀`,
  there are a `1`-periodic orbit `y_q` of `X_{H_q}` in `B` and `s_n → ∞` such that the loops
  `t ↦ u(φ_q(±s_n, t))` converge to `y_q`, pointwise in `M` and uniformly after applying `e`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  and `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer` on a
  compact manifold).
* When `H_q` is `C²` on a Hausdorff boundaryless manifold, `d(e ∘ u ∘ φ'_q)` is bounded on some
  half-cylinder `s > b`, and every `1`-periodic orbit of `X_{H_q}` in `B` along which a sequence of
  end loops converges uniformly starts at a nondegenerate fixed point of the time-one map, time
  reversal transfers isolation to the cluster-point `1`-periodic orbits of `X_{H'_q}`, so the end
  loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` along the whole end to a single `1`-periodic orbit
  `y_q` (`IsNondegenerate` theorem
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer` on a compact manifold).
  When some circle on the end `q` is contractible, nondegeneracy need only hold on
  `contractiblePeriodicSolutions`, and `y_q` is contractible
  (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer`).

**The manifold energy identity with asymptotic orbits.** When `u` maps `S` into `B` and has
integrable area density `u^*ω` and curvature `R_K(u)`, the truncated energy identity and monotone
convergence give finite Floer energy automatically
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_ne_top_of_isCompact`), and dominated
convergence on `[0, 1] × B` (`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`)
combines with whole-end convergence to show that the Floer energy density is integrable over `S` and
satisfies

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

for genuine asymptotic `1`-periodic (or contractible `1`-periodic) orbits `y_q` of the end
Hamiltonians (in `TauCeti.SmoothTwoForm.IsNondegenerate`:
`exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`,
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`,
`exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`, and
`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation` for
`TauCeti.Floer.pairOfPantsPerturbation`). This is the manifold counterpart of
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
  have hder :
      (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
        (((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField
          (positiveEndHamiltonian H q (q.endSign * t)) (x (q.endSign * t)))).comp
          (q.endSign • ContinuousLinearMap.id ℝ ℝ :
            TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (q.endSign * t))) := by
    apply ContinuousLinearMap.ext_ring
    -- `TangentSpace 𝓘(ℝ, ℝ)` is definitionally `ℝ`, so `q.endSign • id` sends `1` to `q.endSign`.
    have hg1 : (q.endSign • ContinuousLinearMap.id ℝ ℝ :
        TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (q.endSign * t)) 1 =
        (q.endSign : ℝ) := by simp
    rw [ContinuousLinearMap.comp_apply, hg1, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, one_apply_eq_self, hH,
      hamiltonianVectorField_const_smul, smul_smul, endSign_mul_self, one_smul]
  exact h.congr_mfderiv hder.symm

/-- A `1`-periodic orbit of the positive end Hamiltonian `H'_q`, read with the time `±t` of the
end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  exact mem_periodicSolutions.2 ⟨hasMFDerivAt_comp_endSign_mul hxd, periodic_comp_endSign_mul hxper⟩

/-- A contractible `1`-periodic orbit of the positive end Hamiltonian `H'_q`, read with the time
`±t` of the end, is a contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ contractiblePeriodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxp, g, hg, hgx⟩ := mem_contractiblePeriodicSolutions.1 hx
  have hdiv : (1 : ℝ) / |q.endSign| = 1 := by rw [abs_endSign, div_one]
  obtain ⟨g', hg', hg'g⟩ := Eq.ndrec
    (motive := fun p ↦ ∃ g' : C(AddCircle p, M), g'.Nullhomotopic ∧
      ∀ t : ℝ, g' t = g ((t * q.endSign : ℝ) : AddCircle (1 : ℝ)))
    (hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero) hdiv
  refine mem_contractiblePeriodicSolutions.2 ⟨mem_periodicSolutions_comp_endSign_mul hxp,
    g', hg', fun t ↦ ?_⟩
  rw [hg'g, hgx, mul_comm]

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the positive end chart are differentiable
in the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
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
    rw [hKH _ x hre, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h]
  exact (hHd _ y).const_smul _

/-- Beyond `T₀` on the end `q`, the pulled-back perturbation along the positive end chart is
`H'_q(t) dt`. -/
private theorem perturbedMFDeriv_comp_positiveEndChart_eq {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
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
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x,
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x]

/-- **An end of a Floer pair of pants in a manifold solves the Floer equation of a half-cylinder.**
Let `K` be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a Hamiltonian `H_q` that is
`1`-periodic in time and differentiable in the target variable, and let `u` be differentiable at
the image `φ'_q(ζ)` of a point `ζ` with `s ≥ T₀` of the positive end chart and solve the Floer
equation `(du - X_K)^{0,1} = 0` there for the almost complex structure `J` on `T_{u(φ'_q(ζ))} M`.
Then `u ∘ φ'_q` solves the half-cylinder Floer equation `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` at
`ζ`, for the end Hamiltonian `H'_q` of the positive end. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    {ζ : ℝ × ℝ}
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
`H_q(t) dt` beyond `T₀` on the end `q`, for a Hamiltonian `H_q` that is `1`-periodic in time and
differentiable in the target variable, and let `u` be differentiable on `S`. Then the energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal) {a : ℝ}
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

omit [NormedSpace ℝ F] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
/-- If some circle `±s₀` (`s₀ > 0`) of the end `q` is mapped by `u` to a contractible loop, then
every `1`-periodic orbit `y` in `B` to which `e ∘ u` converges uniformly along a family of positive
heights `σ i > 0` is contractible. -/
private theorem mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart
    {ι : Type*} {l : Filter ι} [l.NeBot] {q : Puncture}
    (he : Continuous e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {X : ℝ → (x : M) → TangentSpace I x} {σ : ι → ℝ} (hσ : ∀ᶠ i in l, 0 < σ i)
    {y : ℝ → M} (hy : y ∈ periodicSolutions X 1) (hyB : ∀ t, y t ∈ B)
    (hconv : TendstoUniformly (fun i t ↦ e (u (endChart q (q.endSign * σ i, t)))) (e ∘ y) l) :
    y ∈ contractiblePeriodicSolutions X 1 := by
  obtain ⟨s₀, hs₀, h₀⟩ := hnull
  have := isCompact_iff_compactSpace.1 hB
  have hemb : IsClosedEmbedding (B.domRestrict e) :=
    (he.comp continuous_subtype_val).isClosedEmbedding he_inj.injective
  have hmem {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by simpa [← mul_assoc] using hs)
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ u (endChart q (q.endSign * p.1, p.2)))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    hu.comp ((contDiff_endChart q 0).continuous.comp (by fun_prop)).continuousOn
      fun p hp ↦ hmem hp.1 p.2
  have hnull_all {s : ℝ} (hs : 0 < s) :
      ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
        ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)) :=
    ((convex_Ioi (0 : ℝ)).isPathConnected ⟨s₀, hs₀⟩).exists_nullhomotopic_addCircle_of_periodic
      hcont (fun s _ t ↦ by simp only [endChart_add_one]) hs₀ h₀ hs
  exact mem_contractiblePeriodicSolutions_of_tendstoUniformly one_pos hemb.isInducing
    (hσ.mono fun i hi ↦
      hu.comp_continuous ((contDiff_endChart q 0).continuous.comp (by fun_prop)) (hmem hi))
    (Eventually.of_forall fun i t ↦ congrArg u (endChart_add_one q (q.endSign * σ i) t))
    (hσ.mono fun i hi t ↦ huB _ (hmem hi t))
    hy hyB hconv (hσ.mono fun i hi ↦ hnull_all hi).frequently

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- On a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0`, `u ∘ φ'_q` solves the coordinate
half-cylinder Floer equation and has finite energy when `u` solves `(du - X_K)^{0,1} = 0` on `S`
with finite energy. -/
private theorem floer_comp_positiveEndChart_of_le {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHs.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn (fun _ hz ↦ hmem hz.1),
    fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      hud ha₀ haT)⟩
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hud _ (hmem hz.1)).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds (hmem hz.1)))
    (hfloer _ (hmem hz.1))
  have heq := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at heq

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at an end.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q` on a
manifold `M` carrying a nondegenerate two-form `ω`, and let `u` be `C¹` on `S`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `B` and with
injective differential at the points of `B`, and suppose that on some half-cylinder `s > b` of the
positive end chart `φ'_q`, the almost complex structures are uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`. Then there are a `1`-periodic orbit `y` of `X_{H_q}` in `B`
and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))` converge to `y`, pointwise in `M` and
uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  obtain ⟨hu', hfloer', hE'⟩ := floer_comp_positiveEndChart_of_le hKH hH hHs hu hfloer hE ha₀ haT
  -- In the positive end chart, the end is a finite-energy Floer half-cylinder in `M`.
  obtain ⟨x, hx, hxB, φ, -, hφ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHs)
      (periodic_positiveEndHamiltonian hH) he hB he_inj hde hu'
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem hs)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z (hab hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, φ, hφ, ?_, fun t ↦ ?_⟩
  · rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart (e := e) (u := u) q (φ n)]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at an end.**
The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`
to a compact manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hc hJc hfloer hE
  exact ⟨y, hy, h⟩

/-! ### Convergence along the whole end to nondegenerate orbits -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A `1`-periodic orbit `x` of the positive end Hamiltonian `H'_q` is isolated at `t = 0` when
`x 0` is a nondegenerate fixed point of the time-one map of `H_q`. -/
private theorem exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hnd : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (x 0)) :
    ∃ U ∈ 𝓝 (x 0), ∀ z ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      z 0 ∈ U → z = x := by
  have hy := mem_periodicSolutions_comp_endSign_mul hx
  obtain ⟨U, hU, hU'⟩ :=
    hω.exists_mem_nhds_forall_mem_periodicSolutions_hamiltonianVectorField_eq hHs
      (mem_periodicSolutions.1 hy).1 (by simpa only [mul_zero] using hnd)
  rw [mul_zero] at hU
  refine ⟨U, hU, fun z hz hzU ↦ funext fun t ↦ ?_⟩
  have hzx := congrFun (hU' _ (mem_periodicSolutions_comp_endSign_mul hz)
    (by simpa only [mul_zero] using hzU)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using hzx

/-- **An end of a Floer pair of pants in a manifold converges to a nondegenerate orbit.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a `1`-periodic `C²` Hamiltonian `H_q` on a
Hausdorff boundaryless manifold `M` carrying a nondegenerate two-form `ω`, and let `u` be `C¹` on
`S`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy.
Suppose that every `1`-periodic orbit of `H_q` in `B` along which a sequence of end loops converges
uniformly starts at a nondegenerate fixed point of the time-one map, and that on some half-cylinder
`s > b` of the positive end chart `φ'_q`, `d(e ∘ u ∘ φ'_q)` is bounded and the almost complex
structures are uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`. Then the
loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single `1`-periodic orbit `y` of `X_{H_q}` in
`B`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
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
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
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
    floer_comp_positiveEndChart_of_le hKH hH (hHsq.of_le one_le_two) hu hfloer hE ha₀ haT
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHsq.of_le one_le_two))
      (periodic_positiveEndHamiltonian hH) he hB he_inj hde hu'
      (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (hmem hs)) (fun z hz ↦ hC z (hab hz.1))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z (hab hz.1) v) hfloer' hE'
      fun x hx hxB ⟨σ, hσa, hσtop, hσu, hσpt⟩ ↦ by
        have hnd₀ := hnd (fun t ↦ x (q.endSign * t)) (mem_periodicSolutions_comp_endSign_mul hx)
          (fun t ↦ hxB _) ⟨σ, fun n ↦ ha₀.trans_lt (hσa n), hσtop, by
            rw [funext fun n ↦ comp_endChart_eq_comp_positiveEndChart (e := e) (u := u) q (σ n)]
            exact hσu.comp (fun t ↦ q.endSign * t),
          fun t ↦ by
            simpa only [endChart_eq_positiveEndChart, comp_apply] using hσpt (q.endSign * t)⟩
        rw [mul_zero] at hnd₀
        obtain ⟨U, hU, hU'⟩ :=
          hω.exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt hHsq hx hnd₀
        exact ⟨U, hU, fun z hz _ _ hzU ↦ hU' z hz hzU⟩
  refine ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · rw [funext fun s ↦ comp_endChart_eq_comp_positiveEndChart (e := e) (u := u) q s]
    exact hux.comp (fun t ↦ q.endSign * t)
  · simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)

/-- **An end of a Floer pair of pants in a closed manifold converges to a nondegenerate orbit.**
The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
to a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
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
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
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
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE hHsq
      (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, h⟩

/-- **A contractible end of a Floer pair of pants in a manifold converges to a nondegenerate
contractible orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, suppose that
some circle `t ↦ u(φ_q(±s, t))` (`s > 0`) on the end `q` is contractible in `M` and that every
contractible `1`-periodic orbit of `H_q` in `B` starts at a nondegenerate fixed point of the
time-one map; noncontractible periodic orbits may be degenerate. Then the loops `t ↦ u(φ_q(±s, t))`
converge as `s → ∞` to a single contractible `1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise
in `M` and uniformly after applying `e`. -/
theorem
  exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, hyB, huy, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      he hB he_inj hde hu huB hfloer hE hHsq
      (fun z hz hzB ⟨σ, hσpos, _, hσu, _⟩ ↦
        hnd z (mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart (l := atTop)
          he.continuous hB he_inj hu.continuousOn huB hnull (Eventually.of_forall hσpos) hz hzB
          hσu) hzB)
      hC hc hJc
  exact ⟨y, mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart he.continuous hB he_inj
    hu.continuousOn huB hnull (eventually_gt_atTop 0) hy hyB huy, hyB, huy, hpt⟩

/-- **A contractible end of a Floer pair of pants in a closed manifold converges to a nondegenerate
contractible orbit.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
to a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hω hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull
      hfloer hE hHsq (fun y hy _ ↦ hnd y hy) hC hc hJc
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
Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` with a nondegenerate two-form `ω`. Let
`u` be `C¹` on `S`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` on `S` for
uniformly tame almost complex structures measured through `e : M → F`, with integrable area density
`u^*ω` and curvature `R_K(u)` over `S`, and with `d(e ∘ u ∘ φ'_q)` bounded on some half-cylinder of
each end `q`. Suppose that on each end `q`, every `1`-periodic orbit of `H_q` in `B` along which a
sequence of end loops converges uniformly starts at a nondegenerate fixed point of the time-one map.
Then `u` has finite energy, the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic
orbits `y_q` of `X_{H_q}` in `B`, the Floer energy density of `u` is integrable over `S`, and

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
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
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
  -- Uniform tameness wrt `e`, with `d e` injective on `B`, gives fiberwise tameness on `S`.
  have hJtame (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      (hω.symplecticFormAt (u z)).Tames (J z) := fun v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 fun hdv ↦
      hv ((hde _ (huB z hz)).eq_iff.1 (by rwa [map_zero]))) 2)).trans_le (hJc z hz v)
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    floerEnergyDensity_nonneg hω (hJtame z hz) (hfloer z hz)
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hA hR
  -- Compactness of `B` and the truncated energy identity give finite Floer energy beforehand.
  have hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
    rw [hS]
    exact hω.lintegral_floerEnergyDensity_ne_top_of_isCompact hK hKH hH
      (fun q ↦ (hHs q).continuous) hB hu huB he_nonneg hA hR
  -- Obtain the asymptotic `1`-periodic orbit on each end `q`.
  choose b C hbC using hC
  choose y hy using fun q ↦
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      (hKH q) (hH q) he hB he_inj hde hu huB hfloer hE (hHs q) (hnd q)
      (b := max (b q) 0) (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) hc
      fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hz)) v
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hu.continuousOn hB huB
      tendsto_id fun t _ ↦ (hy q).2.2.2 t
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
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
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
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

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
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
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
      hfloer hA (fun q y hy _ ↦ hnd q y hy) hC
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hint, hid⟩

/-- **The manifold pair-of-pants energy identity with contractible asymptotic orbits.** Under the
hypotheses of `exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`, suppose
that on each end `q` some circle `t ↦ u(φ_q(±s, t))` (`s > 0`) is contractible in `M` and that
every contractible `1`-periodic orbit of `H_q` in `B` starts at a nondegenerate fixed point of the
time-one map; noncontractible periodic orbits may be degenerate. Then `u` has finite energy, the end
loops converge as `s → ∞` to contractible `1`-periodic orbits `y_q` of `X_{H_q}` in `B`, the Floer
energy density is integrable over `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
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
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
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
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
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
  obtain ⟨y, hy, hint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact hK hKH hH hHs he hB
      he_inj hde hu huB hc hJc hfloer hA hR
      (fun q z hz hzB ⟨σ, hσpos, _, hσu, _⟩ ↦
        hnd q z (mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart (l := atTop)
          he.continuous hB he_inj hu.continuousOn huB (hnull q) (Eventually.of_forall hσpos) hz hzB
          hσu) hzB)
      hC
  exact ⟨y, fun q ↦ ⟨mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart he.continuous
    hB he_inj hu.continuousOn huB (hnull q) (eventually_gt_atTop 0) (hy q).1 (hy q).2.1
    (hy q).2.2.1, (hy q).2⟩, hint, hid⟩

/-- **The energy identity of the pair-of-pants perturbation with contractible asymptotic orbits.**
The specialization of
`exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`
to `TauCeti.Floer.pairOfPantsPerturbation`, for which the curvature term is automatically
integrable over `S`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
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
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
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
  exact hω.exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- **The energy identity of the pair-of-pants perturbation with contractible asymptotic orbits in
a closed manifold.** The specialization of
`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`
to a compact Hausdorff boundaryless manifold `M`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
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
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
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
    exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
      hω hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull
      hc hJc hfloer hA (fun q y hy _ ↦ hnd q y hy) hC
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hint, hid⟩

end IsNondegenerate

end EnergyIdentity

end SmoothTwoForm

end TauCeti
