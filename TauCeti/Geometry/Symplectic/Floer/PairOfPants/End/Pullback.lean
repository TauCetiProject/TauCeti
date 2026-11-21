/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation
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
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_perturbationPullback`), `u ∘ φ'_q` solves the Floer
  equation of a half-cylinder for `H'_q` when `u` solves `(du - X_K)^{0,1} = 0`
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`);
* its energy over a half-cylinder `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of
  `u` over `S` (`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`),
  and more generally, when `u` is only defined near the end, at most its energy over any open set
  containing the part `±s > a` of the end
  (`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen`, and for a
  measurable subset of a band of angular width one
  `SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset_of_isOpen`);
* at the time `±t` of the end, `X_{H'_q(±t)} = ±X_{H_q(t)}`
  (`TauCeti.SmoothTwoForm.hamiltonianVectorField_positiveEndHamiltonian_endSign_mul`).

The datum `H'_q(t) dt` does not depend on `s`, so the same holds for the translated ends
`v(z) = u(φ'_q(z + (R, 0)))` at every height `R`: they solve one cylindrical Floer equation,
whatever `R`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_add`), and
their energy over a window of angular width one is at most the energy of `u` over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le`). These are
the two inputs of compactness along the ends, where the heights `R` tend to infinity.

These are used in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold` to obtain the
orbits at the ends of a pair of pants in a manifold, and, for a constant form, in
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
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

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
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  -- On `s` the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * e (positiveEndChart q ζ) := by
    intro ζ hζ
    have hζT : T₀ ≤ ζ.1 := haT.trans (hst hζ).1.le
    have hζU := haU ζ (hst hζ).1
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      ((hu _ hζU).mdifferentiableAt (hU.mem_nhds hζU))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
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


/-! ### Translated ends -/

/-- **The translated ends of a Floer pair of pants solve one cylindrical Floer equation.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for differentiable `H_q`, let `R` be a height,
and let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` for the structure `J` at the image
`φ'_q(z + (R, 0))` of a point `z` with `T₀ ≤ z.1 + R`. Then the translated end
`v(w) = u(φ'_q(w + (R, 0)))` solves `∂_s v + J (∂_t v - X_{H'_q(t)}(v)) = 0` at `z`, for the end
Hamiltonian `H'_q` of the positive end, which does not depend on `R`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_add {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (R : ℝ) {z : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q (z + (R, 0)))))}
    (hz : T₀ ≤ z.1 + R)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q (z + (R, 0))))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q (z + (R, 0)))).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun w ↦ u (positiveEndChart q (w + (R, 0)))) z).toLinearMap := by
  have h := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (ζ := z + (R, 0)) (by simpa using hz) hu hfloer
  -- The datum `H'_q(t) dt` is invariant under the translation `(s, t) ↦ (s + R, t)`.
  have heq := ω.perturbedMFDeriv_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) (R, 0) z
  simp only [Prod.snd_add, add_zero, comp_apply] at heq
  rwa [heq]

/-- **The energy of a translated end of a Floer pair of pants.** Let `K` be equal to `H_q(t) dt`
beyond `T₀` on the end `q`, for differentiable `H_q`, and let `u` be differentiable on `S`. Let `R`
be a height and `s` a measurable set whose translate `s + (R, 0)` lies in a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of angular width one. Then the energy of the translated end
`z ↦ u(φ'_q(z + (R, 0)))` for the end Hamiltonian `H'_q` over `s` is at most the energy of `u`
over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℝ × ℝ → M} (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal)
    (R : ℝ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {t₀ : ℝ}
    (hst : ∀ z ∈ s, z + (R, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- The energy of the translated end over `s` is that of `u ∘ φ'_q` over `s + (R, 0)`.
  have h := ω.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) (R, 0)
    ((· + ((R, 0) : ℝ × ℝ)) '' s)
  rw [preimage_image_eq _ (add_left_injective _)] at h
  simp only [Prod.snd_add, add_zero, comp_apply] at h
  rw [h]
  exact setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_subset q hKH hH hHd hu
    ((measurableEmbedding_addRight _).measurableSet_image' hs)
    (by rintro _ ⟨z, hz, rfl⟩; exact hst z hz)

end SmoothTwoForm

end TauCeti
