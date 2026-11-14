/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity

/-!
# Periodic orbits at the ends of a finite-energy Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a symplectic
manifold, and let `K` be a `C¹` Hamiltonian perturbation datum on the pair of pants
`S = ℂ ∖ {0, 1}` which equals `H_q(t) dt` beyond some height `T₀` on each end `q`, for `1`-periodic
Hamiltonians `H_q`. For a `C¹` solution `u : S → M` of the Floer equation `(du - X_K)^{0,1} = 0`
with image in a compact set `B ⊆ M` and finite energy over `S`, this file shows that each end of
`u` breaks off a `1`-periodic orbit of `H_q` in `B`, upgrades subsequential accumulation to
convergence of the whole end as `s → ∞` when the `1`-periodic orbits in `B` are isolated or
nondegenerate and the end derivative is bounded, and evaluates the Floer energy of `u` in terms of
its symplectic area, the Hamiltonian integrals at the three asymptotic periodic orbits, and the
curvature term `R_K(u)`.

This is the manifold-target counterpart of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit`
and `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`.

## Reduction to positive half-cylinders

As in the vector-space case, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`) parametrizes every end by a positive half-cylinder `(0, ∞) × ℝ`,
holomorphically and with positive Jacobian determinant. Beyond `T₀`, pulling back `K` along `φ'_q`
produces the cylindrical perturbation `H'_q(t) dt` for the positive end Hamiltonian
`H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`), which equals `H_q` at the two
inputs `q = 0, 1` and `-H_∞(-t, ·)` at the output `q = ∞`:

* `u ∘ φ'_q` solves the half-cylinder Floer equation `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` beyond
  `T₀` (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), with no
  nondegeneracy of `ω` required;
* its Floer energy over `(a, ∞) × [0, 1]`, for `a ≥ max T₀ 0`, is bounded above by the energy of
  `u` over `S` (`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`);
* reparametrizing time by `t ↦ ±t` identifies `1`-periodic orbits of `H'_q` with `1`-periodic
  orbits of `H_q` (`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul_iff`), fixing
  evaluation at `t = 0`.

Applying the manifold half-cylinder convergence theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` through an injective `C¹` immersion
`e : M → F` on `B` into a finite-dimensional normed space then yields:

* subsequential breaking (`s_n → ∞`) to a `1`-periodic orbit `y` of `H_q` in `B`, uniformly after
  `e` and pointwise in `M`, for `C¹` end Hamiltonians
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  and `..._of_floer` on a compact manifold);
* whole-end convergence (`s → ∞`) when the derivative of `e ∘ u ∘ φ'_q` is bounded on a
  half-cylinder and the `1`-periodic orbits of `H_q` in `B` are isolated at `t = 0`
  (`..._endChart_atTop_of_floer_of_eventually_eq`), and in particular when `M` is boundaryless and
  Hausdorff, `H_q` is `C²`, and the `1`-periodic orbits of `H_q` in `B` are nondegenerate fixed
  points of the return map
  (`..._endChart_atTop_of_floer_of_isCompact` in `SmoothTwoForm.IsNondegenerate`, and
  `..._atTop_of_floer` on a closed manifold).

## Energy identity at the asymptotic orbits

Once each end converges as `s → ∞` to a `1`-periodic orbit `y_q` in `B`, compactness of `B` and
time-periodicity make each `H_q` bounded on `ℝ × B`, so dominated convergence gives
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt → ∫₀¹ H_q(t, y_q(t)) dt`. Unlike the vector-space proof via the
action functional, `u` only needs to be `C¹` on `S`: combining whole-end convergence with
`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`
and `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`
shows that when `u^*ω` and `R_K(u)` are integrable and `J` is tamed on `S`, the Floer energy
density is integrable and

`∫_S E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

(`IsNondegenerate.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`). For
the standard datum `pairOfPantsPerturbation H` on a closed manifold, `R_K(u)` is automatically
integrable (`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`),
giving both the exact energy identity
(`IsNondegenerate.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`)
and the lower bound `-∑ q, B_q ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` on the topological energy
at the asymptotic periodic orbits.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy identity for the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Periodic orbits in positive end charts -/

/-- Reading a trajectory of the positive end Hamiltonian `H'_q` with the time `±t` of the end gives
a trajectory of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ x (q.endSign * t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id t).const_smul (q.endSign : ℝ)).hasMFDerivAt
  have h := (hx (q.endSign * t)).comp t hlin
  have hH' : positiveEndHamiltonian H q (q.endSign * t) = (q.endSign : ℝ) • H q t := by
    funext y
    simp only [positiveEndHamiltonian_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      endSign_mul_self, one_mul]
  rw [hH', ω.hamiltonianVectorField_const_smul] at h
  refine h.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
  change (q.endSign • (1 : ℝ)) •
      (q.endSign • ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
    (1 : ℝ) • ω.hamiltonianVectorField (H q t) (x (q.endSign * t))
  rw [smul_eq_mul, mul_one, smul_smul, endSign_mul_self]

/-- Reading a trajectory of `H_q` with the time `±t` of the end gives a trajectory of the positive
end Hamiltonian `H'_q`. -/
theorem hasMFDerivAt_positiveEndHamiltonian_comp_endSign_mul {q : Puncture} {y : ℝ → M}
    (hy : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I y t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (y t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ y (q.endSign * t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (y (q.endSign * t)))) := by
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ q.endSign * s) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id t).const_smul (q.endSign : ℝ)).hasMFDerivAt
  have h := (hy (q.endSign * t)).comp t hlin
  have hH' : positiveEndHamiltonian H q t = (q.endSign : ℝ) • H q (q.endSign * t) := by
    funext p
    simp only [positiveEndHamiltonian_apply, Pi.smul_apply, smul_eq_mul]
  rw [hH', ω.hamiltonianVectorField_const_smul]
  refine h.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
  change (q.endSign • (1 : ℝ)) •
      ω.hamiltonianVectorField (H q (q.endSign * t)) (y (q.endSign * t)) =
    (1 : ℝ) • (q.endSign • ω.hamiltonianVectorField (H q (q.endSign * t)) (y (q.endSign * t)))
  rw [smul_eq_mul, mul_one, one_smul]

/-- Reparametrizing time by `t ↦ ±t` identifies `1`-periodic orbits of the positive end Hamiltonian
`H'_q` with `1`-periodic orbits of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul_iff (ω : SmoothTwoForm I M)
    {q : Puncture} {x : ℝ → M} :
    (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ↔
      x ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 := by
  simp only [mem_periodicSolutions]
  constructor
  · intro hy
    have hinv : x = fun t ↦ (fun s ↦ x (q.endSign * s)) (q.endSign * t) := by
      funext t
      simp only [← mul_assoc, endSign_mul_self, one_mul]
    rw [hinv]
    exact ⟨ω.hasMFDerivAt_positiveEndHamiltonian_comp_endSign_mul hy.1,
      periodic_comp_endSign_mul (x := fun t ↦ x (q.endSign * t)) hy.2⟩
  · exact fun hx ↦ ⟨ω.hasMFDerivAt_comp_endSign_mul hx.1, periodic_comp_endSign_mul hx.2⟩

/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the end coordinates are differentiable in
the target manifold when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x *
        q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v := by
    funext x
    rw [hKH q _ x hre, smul_apply, smul_eq_mul]
  rw [h]
  exact ((hHd q _) y).mul mdifferentiableAt_const

/-- On the positive end beyond `T₀`, the pulled-back perturbation is `H'_q(t) dt`. -/
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
        (u ∘ positiveEndChart q) ζ :=
  ω.perturbedMFDeriv_congr _
    (funext fun x ↦ (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x).symm)
    (funext fun x ↦
      (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x).symm)

/-- **The ends of a Floer pair of pants in a manifold solve the half-cylinder Floer equation.** Let
`K` equal `H_q(t) dt` beyond `T₀` on each end `q`, and let `u` solve the Floer equation
`(du - X_K)^{0,1} = 0` for the almost complex structure `J` on `T_{u (φ'_q ζ)} M` at the image of a
point `ζ` with `s ≥ T₀` of the positive end chart. Then `u ∘ φ'_q` solves the half-cylinder Floer
equation `(dv - X_{H'_q dt})^{0,1} = 0` at `ζ`, for the positive end Hamiltonian `H'_q`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    {q : Puncture} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))}
    (hζ : T₀ ≤ ζ.1) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [ω.perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **The energy of an end of a Floer pair of pants in a manifold.** Under the hypotheses of
`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`, the Floer energy
of `u ∘ φ'_q` for the positive end Hamiltonian `H'_q` over `(a, ∞) × [0, 1]`, for `a ≥ max T₀ 0`,
is at most the Floer energy of `u` over `S`. No nondegeneracy of `ω` is needed. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le (ω : SmoothTwoForm I M)
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
  set edens : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set s : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hs : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  -- The closed band differs from the open one by a null set.
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] s := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  -- On the open band the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * edens (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζ₀ : 0 < ζ.1 := ha₀.trans_lt hζ.1
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
    rw [floerEnergyDensity_def, ω.perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
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

/-! ### Subsequential breaking at each end -/

section Breaking

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

omit [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The positive end chart maps `(a, ∞) × ℝ` into `S` whenever `0 ≤ a`. -/
private theorem mapsTo_positiveEndChart_of_nonneg (q : Puncture) {a : ℝ} (ha : 0 ≤ a) :
    MapsTo (positiveEndChart q) (Ioi a ×ˢ univ) thricePuncturedSphereReal :=
  fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha.trans_lt hz.1)

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Convert the complex-linear Floer equation for `u ∘ φ'_q` with perturbation `H'_q dt` into the
coordinate form `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0`. -/
private theorem coordinate_floer_comp_positiveEndChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    {q : Puncture} {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    (∀ q t, MDifferentiable I 𝓘(ℝ) (H q t)) ∧
      ∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0 := by
  have hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t) := fun q t ↦
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  refine ⟨hHd, fun z hz ↦ ?_⟩
  have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hz.1)
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le)
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    (hfloer _ hS)
  simpa only [ω.hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using
    (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ (fun w ↦ u (positiveEndChart q w)) z
      (J (positiveEndChart q z))).1 hcl

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off a periodic orbit at each end.**
Let `ω` be a nondegenerate two-form on `M`, let `K` equal `H_q(t) dt` beyond `T₀` on each end `q`
for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be `C¹` on `S`, with image in a compact set
`B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` for almost complex structures uniformly tame on the
end `q` with respect to an injective `C¹` immersion `e : M → F` on `B`. If the energy of `u` over
`S` is finite, then at the end `q` there are a `1`-periodic orbit `y` of `X_{H_q}` in `B` and a
sequence `σ_n → ∞` such that the end loops `t ↦ u(φ_q(±σ_n, t))` converge to `y`, uniformly after
`e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hHd, hfloer'⟩ := coordinate_floer_comp_positiveEndChart hKH hH hHs hu hfloer ha₀ haT
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) :=
    hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn
      (mapsTo_positiveEndChart_of_nonneg q ha₀)
  have hE' := ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    hKH hH hHd (hu.mdifferentiableOn one_ne_zero) q ha₀ haT)
  -- In the positive end chart, `u ∘ φ'_q` is a finite-energy Floer half-cylinder for `H'_q`.
  obtain ⟨x, hx, hxB, σ, -, hσ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (mapsTo_positiveEndChart_of_nonneg q ha₀ ⟨hs, mem_univ _⟩))
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE'
  refine ⟨fun t ↦ x (q.endSign * t), ω.mem_periodicSolutions_comp_endSign_mul_iff.2 hx,
    fun t ↦ hxB _, σ, hσ, ?_, fun t ↦ ?_⟩
  · have hloop : (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) =
        fun n ↦ (fun t ↦ e (u (positiveEndChart q (σ n, t)))) ∘ fun t ↦ q.endSign * t := by
      funext n t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [hloop]
    exact hconv.comp _
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Subsequential breaking at each end of a finite-energy Floer pair of pants in a closed
manifold.** Specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` when
`M` is compact. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
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
    (q : Puncture) {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE q hc hJc
  exact ⟨y, hy, h⟩

/-! ### Whole-end convergence at isolated and nondegenerate ends -/

/-- **Whole-end convergence of a finite-energy Floer pair of pants at an isolated end.** Under the
hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
suppose in addition that `e ∘ u ∘ φ'_q` has bounded derivative for `s > b` and that each
`1`-periodic orbit `y` of `X_{H_q}` in `B` is isolated at `t = 0` among `1`-periodic orbits in `B`.
Then as `s → ∞` the end loops `t ↦ u(φ_q(±s, t))` converge to a single `1`-periodic orbit `y` of
`X_{H_q}` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_eventually_eq
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (q : Puncture) {b C c : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  obtain ⟨hHd, hfloer'⟩ := coordinate_floer_comp_positiveEndChart hKH hH hHs hu hfloer ha₀ haT
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) :=
    hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn
      (mapsTo_positiveEndChart_of_nonneg q ha₀)
  have hE' := ne_top_of_le_ne_top hE (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le
    hKH hH hHd (hu.mdifferentiableOn one_ne_zero) q ha₀ haT)
  -- Reparametrizing time by `±t` fixes `t = 0`, so isolation for `H_q` gives isolation for `H'_q`.
  have hiso' (x : ℝ → M)
      (hx : x ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
      (hxB : ∀ t, x t ∈ B) :
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    have h0 : (fun t ↦ x (q.endSign * t)) 0 = x 0 := by simp only [mul_zero]
    rw [← h0]
    refine (hiso (fun t ↦ x (q.endSign * t))
      (ω.mem_periodicSolutions_comp_endSign_mul_iff.2 hx) fun t ↦ hxB _).mono
      fun p hp x' hx' hx'B hx'0 ↦ ?_
    have heq := hp (fun t ↦ x' (q.endSign * t))
      (ω.mem_periodicSolutions_comp_endSign_mul_iff.2 hx') (fun t ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)
    funext t
    have ht := congrFun heq (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using ht
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_eventually_eq
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he hB he_inj hde hu' (fun s _ t ↦ by simp only [positiveEndChart_add_one])
      (fun s hs t ↦ huB _ (mapsTo_positiveEndChart_of_nonneg q ha₀ ⟨hs, mem_univ _⟩))
      (fun z hz ↦ hC z (hab z hz.1)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z (hab z hz.1) v) hfloer' hE' hiso'
  refine ⟨fun t ↦ x (q.endSign * t), ω.mem_periodicSolutions_comp_endSign_mul_iff.2 hx,
    fun t ↦ hxB _, ?_, fun t ↦ ?_⟩
  · have hloop : (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) =
        fun s ↦ (fun t ↦ e (u (positiveEndChart q (s, t)))) ∘ fun t ↦ q.endSign * t := by
      funext s t
      simp only [comp_apply, endChart_eq_positiveEndChart]
    rw [hloop]
    exact hconv.comp _
  · simpa only [comp_apply, endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-- **Whole-end convergence of a finite-energy Floer pair of pants at a nondegenerate end.** Let `M`
be boundaryless and Hausdorff, let `K` equal `H_q(t) dt` beyond `T₀` on each end for `1`-periodic
`C¹` Hamiltonians `H_q` such that `H_q` at the end `q` is `C²`, and let `u` be a `C¹` finite-energy
Floer solution on `S` with image in a compact set `B ⊆ M`. If on the end `q` the derivative of
`e ∘ u ∘ φ'_q` is bounded and `J` is uniformly tame for `s > b`, and every `1`-periodic orbit of
`X_{H_q}` in `B` is a nondegenerate fixed point of the return map `timeDependentFlowOf X_{H_q} 0 1`
at `t = 0`, then as `s → ∞` the end loops `t ↦ u(φ_q(±s, t))` converge to a `1`-periodic orbit `y`
of `X_{H_q}` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
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
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (H q p.1) p.2⟩ : TangentBundle I M)) :=
    hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hHq.of_le (by norm_num))
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_eventually_eq
    hKH hH hHs he hB he_inj hde hu huB hfloer hE q hC hc hJc fun y hy hyB ↦ ?_
  have hnd₀ : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 (0 + 1)) (y 0) := by
    simpa only [zero_add] using hnd y hy hyB
  exact (hnd₀.eventually_eq_of_mem_periodicSolutions hX (mem_periodicSolutions.1 hy).1).mono
    fun p hp y' hy' _ hpy' ↦ hp y' hy' hpy'

/-- **Whole-end convergence of a finite-energy Floer pair of pants in a closed manifold.**
Specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`
when `M` is compact. -/
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
    (q : Puncture) (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
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
      hHq (fun y hy _ ↦ hnd y hy) hC hc hJc
  exact ⟨y, hy, h⟩

/-! ### Energy identity at the asymptotic periodic orbits -/

omit [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- A continuous Hamiltonian on `[0, 1] × B` with compact `B` transfers pointwise convergence of end
loops in `B` to convergence of the Hamiltonian integrals `∫₀¹ H_q(t, u(φ_q(±s, t))) dt`. -/
private theorem tendsto_intervalIntegral_endChart_of_isCompact
    {B : Set M} (hB : IsCompact B) {q : Puncture}
    (hHc : Continuous (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {y : ℝ → M}
    (hy : ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (y t))) := by
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1) |>.prod hB).exists_bound_of_continuousOn hHc.continuousOn
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M₀) ?_ ?_
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, y t)).comp (tendsto_const_nhds.prodMk_nhds (hy t)))
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hmem (t : ℝ) : endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal := by
      rw [endChart_eq_positiveEndChart]
      exact positiveEndChart_mem_thricePuncturedSphereReal hs
    have hloop : Continuous fun t : ℝ ↦ u (endChart q (q.endSign * s, t)) :=
      hu.comp_continuous ((contDiff_endChart q 0).continuous.comp (by fun_prop)) hmem
    exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with s hs
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hmem : endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal := by
      rw [endChart_eq_positiveEndChart]
      exact positiveEndChart_mem_thricePuncturedSphereReal hs
    exact hM₀ (t, u (endChart q (q.endSign * s, t))) ⟨⟨ht.1.le, ht.2⟩, huB _ hmem⟩

/-- **The pair-of-pants energy identity with asymptotic periodic orbits, for a manifold target.**
Let `ω` be a nondegenerate two-form on a boundaryless Hausdorff finite-dimensional manifold `M`, let
`K` be `C¹` on `S × M` and equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C²`
Hamiltonians `H_q` whose `1`-periodic orbits in a compact set `B ⊆ M` are nondegenerate fixed points
of the return map at `t = 0`. Let `u` be `C¹` on `S`, with image in `B`, solving
`(du - X_K)^{0,1} = 0` for tamed almost complex structures `J`, with finite energy over `S`,
integrable symplectic area density `u^*ω`, and integrable curvature `R_K(u)`. Suppose that for an
injective `C¹` immersion `e : M → F` on `B`, on each end `q` the derivative of `e ∘ u ∘ φ'_q` is
bounded and `J` is uniformly tame with respect to `e` on some half-cylinder `s > b_q`. Then:

1. at each end `q`, the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a `1`-periodic orbit
   `y_q` of `X_{H_q}` in `B`, uniformly after `e` and pointwise in `M`;
2. the Floer energy density of `u` is integrable, and
   `∫ E(u) = ∫ u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫ R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hend : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t)))) atTop
          (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      Integrable (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) ∧
      ∫ z, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  have hall (q : Puncture) :
      ∃ yq ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, yq t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ yq) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (yq t)) := by
    obtain ⟨b, C, c, hc, hC, hJc⟩ := hend q
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      hKH hH hHs1 he hB he_inj hde hu huB hfloer hE q (hHs q) (hnd q) hC hc hJc
  choose y hy hyB hconv hpt using hall
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact hB (hHs q).continuous hu.continuousOn huB (hpt q)
  have hnonneg : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have hint : Integrable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) :=
    hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hnonneg hA hR hh
  exact ⟨y, fun q ↦ ⟨hy q, hyB q, hconv q, hpt q, hh q⟩, hint,
    hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hint hA hR hh⟩

/-- **The energy identity and topological energy bound for `pairOfPantsPerturbation` on a closed
manifold.** Let `ω` be a nondegenerate two-form on a compact boundaryless Hausdorff manifold `M`,
and let `K = pairOfPantsPerturbation H` for `1`-periodic `C²` Hamiltonians `H_q` bounded by `B_q`
whose `1`-periodic orbits are all nondegenerate. Let `u` be a `C¹` finite-energy Floer solution on
`S` with integrable symplectic area density `u^*ω`, for tamed almost complex structures `J` that are
uniformly tame on each end with respect to a `C¹` injective immersion `e : M → F`, and with bounded
end derivatives `‖fderiv ℝ (e ∘ u ∘ φ'_q)‖`. Then each end `q` converges as `s → ∞` to a
`1`-periodic orbit `y_q` of `X_{H_q}`, the Floer energy density is integrable over `S`,

`∫_S E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`,

and the topological energy at the asymptotic periodic orbits satisfies
`-∑ q, B_q ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hend : ∀ q, ∃ b C c, 0 < c ∧
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
        c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
          hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
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
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) ∧
      -∑ q, B q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hHs1 : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hR := integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
    rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) := by
    rwa [IntegrableOn, hS] at hR
  obtain ⟨y, hy, hint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
      (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x)
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _)
      hJ hfloer hE hA' hR' (fun q y₀ hy₀ _ ↦ hnd q y₀ hy₀) hend
  have hintOn : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal := by
    rwa [IntegrableOn, hS]
  have hyLift (q : Puncture) (t : ℝ) :
      Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (y q t)) := by
    simpa only [endChart_mk] using (hy q).2.2.2.1 t
  refine ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2.1, (hy q).2.2.2.1⟩, hintOn, ?_,
    hω.neg_sum_le_integral_add_sum_of_isComplexLinearMap hH hHs1 hB hu hyLift hintOn hA hJ hfloer⟩
  simpa only [hS] using hid

end IsNondegenerate

end Breaking

end SmoothTwoForm

end TauCeti
