/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# The ends of a Floer pair of pants in a manifold as Floer half-cylinders

Let `ω` be a two-form on a manifold `M` and let `K` be a Hamiltonian perturbation on the pair of
pants `S = ℂ ∖ {0, 1}` with values in functions on `M`, equal to `H_q(t) dt` beyond some height
`T₀` on each end `q`. On the end `q`, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`) is holomorphic, and beyond `T₀` it pulls `K` back to
`H'_q(t) dt` for the positive end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`). This file transfers the Floer equation and the energy of
a map `u : S → M` to `u ∘ φ'_q`:

* since the perturbed derivative is natural under changes of domain coordinates
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_perturbationPullback`), `u ∘ φ'_q` has perturbed
  derivative `(du - X_K) ∘ dφ'_q`
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_positiveEndChart`) and solves the Floer equation of
  a half-cylinder for `H'_q` when `u` solves `(du - X_K)^{0,1} = 0`
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`);
* its energy density is multiplied by `det dφ'_q > 0`
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_positiveEndChart`), so its energy over a
  half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
  (`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`),
  and more generally, when `u` is only defined near the end, at most its energy over any open set
  containing the part `±s > a` of the end
  (`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen`, and for a
  measurable subset of a band of angular width one
  `SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset_of_isOpen`);
* at the time `±t` of the end, `X_{H'_q(±t)} = ±X_{H_q(t)}`
  (`TauCeti.SmoothTwoForm.hamiltonianVectorField_positiveEndHamiltonian_endSign_mul`), so reading
  an integral curve of `H'_q` with `±t` gives one of `H_q`
  (`TauCeti.SmoothTwoForm.hasMFDerivAt_comp_endSign_mul`);
* combining regularity, the Floer equation, and finite energy on `S` or on an open set containing
  the end gives the coordinate half-cylinder regularity, Floer equation, and finite energy for
  `u ∘ φ'_q` (`TauCeti.SmoothTwoForm.floer_halfCylinder_comp_positiveEndChart_of_isOpen` and
  `TauCeti.SmoothTwoForm.floer_halfCylinder_comp_positiveEndChart`).

These are used in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit`,
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold` to obtain the orbits at the ends of a
pair of pants in a manifold, and, for a constant form, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` for a symplectic vector space.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Hamiltonian vector fields in positive end charts -/

/-- At the time `±t` of the end, the Hamiltonian vector field of the positive end Hamiltonian
`H'_q` is `±` that of `H_q` at the time `t`: `X_{H'_q(±t)} = ±X_{H_q(t)}`. -/
theorem hamiltonianVectorField_positiveEndHamiltonian_endSign_mul (q : Puncture) (t : ℝ)
    (x : M) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) x =
      q.endSign • ω.hamiltonianVectorField (H q t) x := by
  rw [← hamiltonianVectorField_const_smul]
  congr 1
  funext y
  rw [positiveEndHamiltonian_apply, endSign_mul_endSign_mul, Pi.smul_apply, smul_eq_mul]

/-- Reading a solution curve of the positive end Hamiltonian `H'_q` with the time `±t` of the end
gives a solution curve of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ) I (fun s ↦ x (q.endSign * s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  -- The velocity `±X_{H'_q(±t)}` of `x` at `±t`, rescaled by the sign of the end, is `X_{H_q(t)}`.
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
            (x (q.endSign * t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight q.endSign := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight,
      hamiltonianVectorField_positiveEndHamiltonian_endSign_mul, smul_smul]
  rw [h]
  refine (hx (q.endSign * t)).comp t (hasMFDerivAt_iff_hasFDerivAt.2 ?_)
  exact ((hasDerivAt_id' t).const_mul q.endSign).hasFDerivAt.congr_fderiv
    (ContinuousLinearMap.ext_ring (by simp))


/-! ### The ends of a Floer pair of pants as Floer half-cylinders -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- Beyond `T₀` on the end `q`, the components of `K` in the end coordinates are differentiable
in the target point when the end Hamiltonian is. -/
private theorem mdifferentiableAt_perturbation_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
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
    rw [hKH _ x hre, smul_apply, smul_eq_mul]
  rw [h]
  exact ((hHd _) y).mul mdifferentiableAt_const

/-- On the positive end beyond `T₀`, the pulled-back perturbation is `H'_q(t) dt`. -/
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
  have hs := funext fun x ↦
    perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x
  have ht := funext fun x ↦
    perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hs, ht]

/-- **The perturbed derivative in a positive end chart.** Where `K = H_q(t) dt` beyond `T₀` on the
end `q`, the half-cylinder perturbed derivative of `u ∘ φ'_q` for `H'_q` at a point `ζ` with
`ζ.1 ≥ T₀` is `(du - X_K) ∘ dφ'_q`. No nondegeneracy of `ω` is needed. -/
theorem perturbedMFDeriv_comp_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (ω.perturbedMFDeriv
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).comp (fderiv ℝ (positiveEndChart q) ζ) := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The ends of a Floer pair of pants solve the Floer equation of a half-cylinder.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on the end `q`, for differentiable `H_q`, and let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` for the almost complex structure `J` at the image `φ'_q(ζ)`
of a point `ζ` with `s ≥ T₀` of the positive end chart. Then `u ∘ φ'_q` solves the Floer equation
`∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` of a half-cylinder at `ζ`, for the end Hamiltonian `H'_q` of
the positive end. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [ω.perturbedMFDeriv_comp_positiveEndChart hKH hH hHd hζ hu,
    ContinuousLinearMap.toLinearMap_comp]
  exact hfloer.comp (isComplexLinearMap_fderiv_positiveEndChart q ζ)

/-- **The energy density in a positive end chart.** Beyond `T₀` on the end `q`, the half-cylinder
Floer energy density of `u ∘ φ'_q` for `H'_q` at `ζ` is `det dφ'_q(ζ)` times the energy density of
`u` at `φ'_q(ζ)`. No nondegeneracy of `ω` is needed. -/
theorem floerEnergyDensity_comp_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      (fderiv ℝ (positiveEndChart q) ζ).det * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
  rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)

/-- **The energy of a part of an end of a Floer solution on an open set.** Let `K` be equal to
`H_q(t) dt` beyond `T₀` on the end `q`, for differentiable `H_q`, and let `u` be differentiable on
an open set `U` which contains the part `±s > a` of the end `q`, for some `a ≥ T₀`. The energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over a measurable subset `s` of a band
`(a, ∞) × (t₀, t₀ + 1)` of angular width one is at most the energy of `u` over `U`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset_of_isOpen (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u U) {a : ℝ} (haT : T₀ ≤ a)
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) {t₀ : ℝ} (hst : s ⊆ Ioi a ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- On `s` the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζU := haU ζ (hst hζ).1
    rw [abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_comp_positiveEndChart hKH hH hHd (haT.trans (hst hζ).1.le)
      ((hu _ hζU).mdifferentiableAt (hU.mem_nhds hζU))
  rw [← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs
    ((injOn_positiveEndChart q t₀).mono
      (hst.trans (prod_mono (subset_univ _) Ioo_subset_Ico_self)))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact haU ζ (hst hζ).1

/-- **The energy of a part of an end of a Floer pair of pants.** Let `K` be equal to `H_q(t) dt`
beyond `T₀` on the end `q`, for differentiable `H_q`, and let `u` be differentiable on `S`. The
energy of `u ∘ φ'_q` for the end Hamiltonian `H'_q` over a measurable subset `s` of a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ}
    (hst : s ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) :=
  setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset_of_isOpen q hKH hH hHd
    isOpen_thricePuncturedSphereReal hu (le_max_left T₀ 0)
    (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right T₀ 0).trans_lt hζ))
    hs hst

/-- **The energy of an end of a Floer solution on an open set.** Let `K` be equal to `H_q(t) dt`
beyond `T₀` on the end `q`, for differentiable `H_q`, and let `u` be differentiable on an open set
`U` which contains the part `±s > a` of the end `q`, for some `a ≥ T₀`. The energy of `u ∘ φ'_q`
for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]` is at most the energy of
`u` over `U`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u U) {a : ℝ} (haT : T₀ ≤ a)
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- The closed band differs from the open one by a null set.
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Ioi a ×ˢ Ioo 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  rw [setLIntegral_congr hae]
  exact setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset_of_isOpen q hKH hH hHd
    hU hu haT haU (measurableSet_Ioi.prod measurableSet_Ioo) (by rw [zero_add])

/-- **The energy of an end of a Floer pair of pants.** Let `K` be equal to `H_q(t) dt` beyond `T₀`
on the end `q`, for differentiable `H_q`, and let `u` be differentiable on `S`. The energy of
`u ∘ φ'_q` for the end Hamiltonian `H'_q` over the half-cylinder `(a, ∞) × [0, 1]`, for
`a ≥ max T₀ 0`, is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) :=
  setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen q hKH hH hHd
    isOpen_thricePuncturedSphereReal hu haT fun _ hζ ↦
      positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ)

/-- Let `K` be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for differentiable `H_q`, and let
`u` be `Cⁿ` (`n ≠ 0`) on an open set `U` containing the part `±s > a` of the end `q`, for some
`a ≥ T₀`. If `u` solves the Floer equation `(du - X_K)^{0,1} = 0` on `φ'_q((a, ∞) × [0, 1])` with
finite energy over `U`, then on `(a, ∞) × ℝ` the map `u ∘ φ'_q` is `Cⁿ`, solves the coordinate
half-cylinder Floer equation `∂_s v + J' (∂_t v - X_{H'_q}(v)) = 0` on `(a, ∞) × [0, 1]`, and has
finite energy over `(a, ∞) × [0, 1]`. -/
theorem floer_halfCylinder_comp_positiveEndChart_of_isOpen (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : WithTop ℕ∞}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u U) (hn : n ≠ 0) {a : ℝ} (haT : T₀ ≤ a)
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U)
    {J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z))}
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q z)).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
          J' z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineImag -
            ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
              ((u ∘ positiveEndChart q) z)) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ := by
  have hud := hu.mdifferentiableOn hn
  refine ⟨hu.comp (contDiff_positiveEndChart q n).contMDiff.contMDiffOn fun z hz ↦ haU z hz.1,
    fun z hz ↦ ?_, ne_top_of_le_ne_top hE
      (ω.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen q hKH hH hHd hU hud
        haT haU)⟩
  have hS := haU z hz.1
  have hcl := ω.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le) ((hud _ hS).mdifferentiableAt (hU.mem_nhds hS)) (hfloer z hz)
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z (J' z)).1 hcl
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at hiff

/-- Beyond `max T₀ 0`, the positive end chart maps into `S` and transports the regularity,
Floer equation, and finite energy of a pair-of-pants Floer solution to the coordinate
half-cylinder for `H'_q`. -/
theorem floer_halfCylinder_comp_positiveEndChart (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} {n : WithTop ℕ∞}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u thricePuncturedSphereReal) (hn : n ≠ 0)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a)
    {J' : ∀ z, AlmostComplexStructure (TangentSpace I ((u ∘ positiveEndChart q) z))}
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q z)).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n (u ∘ positiveEndChart q) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineReal +
          J' z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ positiveEndChart q) z stdComplexLineImag -
            ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
              ((u ∘ positiveEndChart q) z)) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≠ ⊤ :=
  ω.floer_halfCylinder_comp_positiveEndChart_of_isOpen q hKH hH hHd
    isOpen_thricePuncturedSphereReal hu hn haT
    (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ)) hfloer hE

end SmoothTwoForm

end TauCeti
