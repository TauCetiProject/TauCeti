/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Curvature of Hamiltonian perturbations and the Floer energy identity

Inhomogeneous Floer equations on a Riemann surface with coordinates `z = (s, t)` are perturbed by
a Hamiltonian-valued one-form `K = K_s ds + K_t dt`, given here by two families of Hamiltonians
`Ks Kt : ℝ × ℝ → V → ℝ` on a symplectic vector space `(V, ω)`. Writing `X_F` for the Hamiltonian
vector field (`ω(X_F, ·) = dF`) and `{F, G} = ω(X_F, X_G)` for the Poisson bracket, we define:

* the *curvature* `R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}`, a function of `(z, x)`;
* the *perturbed derivative* `du - X_K = du - ds ⊗ X_{K_s}(u) - dt ⊗ X_{K_t}(u)` of a map
  `u : ℝ × ℝ → V`;
* the *Floer energy density* `ω(∂_s u - X_{K_s}(u), ∂_t u - X_{K_t}(u))`.

The Floer equation `(du - X_K)^{0,1} = 0` says that the perturbed derivative is complex linear for
the standard complex structure on `ℝ × ℝ`, or in coordinates
`∂_s u - X_{K_s}(u) + J (∂_t u - X_{K_t}(u)) = 0`. Since the energy density is by definition
the symplectic area density of the perturbed derivative, for solutions it is nonnegative under
tameness and is half the metric energy density `|du - X_K|²`, by
`IsComplexLinearMap.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg` and
`IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`.

The main result is the energy identity: pointwise,
`ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t}) = ω(∂_s u, ∂_t u) + d(K(u)) - R_K(u)`,
where `d(K(u)) = ∂_s (K_t(u)) - ∂_t (K_s(u))` is the exterior derivative of the pulled-back
one-form `K(u) = K_s(u) ds + K_t(u) dt`. Integrated over a rectangle using the divergence theorem,
the energy is the symplectic area plus the boundary integral of `K(u)` minus the integral of the
curvature. Curvature bounds therefore turn into energy bounds. For a cylindrical perturbation
`K = H_t dt`, the curvature vanishes; for a continuation perturbation `K = β(s) H_t dt`, it is
`β'(s) H_t`.

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianCurvature`: the curvature `R_K`.
* `TauCeti.SymplecticForm.perturbedFDeriv`: the perturbed derivative `du - X_K`.
* `TauCeti.SymplecticForm.floerEnergyDensity`: the Floer energy density.

## Main results

* `SymplecticForm.floerEnergyDensity_eq`: the pointwise energy identity.
* `SymplecticForm.integral_floerEnergyDensity`: the energy identity on a rectangle.
* `SymplecticForm.isComplexLinearMap_perturbedFDeriv_iff`: the coordinate form of the Floer
  equation.
* `SymplecticForm.hamiltonianCurvature_zero_left`,
  `SymplecticForm.hamiltonianCurvature_cylindrical`,
  `SymplecticForm.hamiltonianCurvature_continuation`: the curvature of perturbations without `ds`
  component.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations, their curvature and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on inhomogeneous
  pseudoholomorphic maps and their energy.
-/

public section

open Function MeasureTheory Set

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Curvature

/-- The curvature `R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` of the Hamiltonian perturbation one-form
`K = K_s ds + K_t dt`, at the domain point `z = (s, t)` and the target point `x`. -/
noncomputable def hamiltonianCurvature (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (z : ℝ × ℝ) (x : V) : ℝ :=
  fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal - fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag -
    ω.poissonBracket (Ks z) (Kt z) x

theorem hamiltonianCurvature_def (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (z : ℝ × ℝ)
    (x : V) :
    ω.hamiltonianCurvature Ks Kt z x =
      fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag - ω.poissonBracket (Ks z) (Kt z) x :=
  (rfl)

/-- Without a `ds` component, the curvature of `K = K_t dt` is `∂_s K_t`. -/
theorem hamiltonianCurvature_zero_left (ω : SymplecticForm V) (Kt : ℝ × ℝ → V → ℝ)
    (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) Kt z x =
      fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal := by
  simp [hamiltonianCurvature_def]

/-- A cylindrical perturbation `K = H_t dt`, independent of `s`, has zero curvature. -/
theorem hamiltonianCurvature_cylindrical (ω : SymplecticForm V) (H : ℝ → V → ℝ) (z : ℝ × ℝ)
    (x : V) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w ↦ H w.2) z x = 0 := by
  rw [hamiltonianCurvature_zero_left]
  by_cases hH : DifferentiableAt ℝ (fun t ↦ H t x) z.2
  · have h : HasFDerivAt (fun w : ℝ × ℝ ↦ H w.2 x)
        ((fderiv ℝ (fun t ↦ H t x) z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
      hH.hasFDerivAt.comp z hasFDerivAt_snd
    simp [h.fderiv, stdComplexLineReal]
  · have hH' : ¬DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ H w.2 x) z := by
      intro h
      have hz : DifferentiableAt ℝ (fun t : ℝ ↦ ((z.1, t) : ℝ × ℝ)) z.2 :=
        (differentiableAt_const z.1).prodMk differentiableAt_id
      have h' : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ H w.2 x) (z.1, z.2) := h
      exact hH (h'.comp z.2 hz)
    simp [fderiv_zero_of_not_differentiableAt hH']

/-- A continuation perturbation `K = β(s) H_t dt` has curvature `β'(s) H_t`. -/
theorem hamiltonianCurvature_continuation (ω : SymplecticForm V) {β : ℝ → ℝ} {H : ℝ → V → ℝ}
    {z : ℝ × ℝ} {x : V} (hβ : DifferentiableAt ℝ β z.1)
    (hH : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w y ↦ β w.1 * H w.2 y) z x =
      deriv β z.1 * H z.2 x := by
  rw [hamiltonianCurvature_zero_left]
  have hβ' : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1)
      ((fderiv ℝ β z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    hβ.hasFDerivAt.comp z hasFDerivAt_fst
  have hH' : HasFDerivAt (fun w : ℝ × ℝ ↦ H w.2 x)
      ((fderiv ℝ (fun t ↦ H t x) z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    hH.hasFDerivAt.comp z hasFDerivAt_snd
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 * H w.2 x)
      (β z.1 • (fderiv ℝ (fun t ↦ H t x) z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) +
        H z.2 x • (fderiv ℝ β z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    HasFDerivAt.mul hβ' hH'
  rw [h.fderiv]
  simp [stdComplexLineReal]
  ring

end Curvature

section Differential

/-- The perturbed derivative `du - X_K` of a map `u` at `z`, for the perturbation one-form
`K = K_s ds + K_t dt`: it sends a tangent vector `(a, b)` to `du(a, b) - a X_{K_s} - b X_{K_t}`,
with the Hamiltonian vector fields evaluated at `u z`. -/
noncomputable def perturbedFDeriv (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] V :=
  fderiv ℝ u z - (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Ks z) (u z)) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Kt z) (u z))

theorem perturbedFDeriv_apply (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (z v : ℝ × ℝ) :
    ω.perturbedFDeriv Ks Kt u z v =
      fderiv ℝ u z v - v.1 • ω.hamiltonianVectorField (Ks z) (u z) -
        v.2 • ω.hamiltonianVectorField (Kt z) (u z) :=
  (rfl)

/-- The `∂_s` component of the perturbed derivative is `∂_s u - X_{K_s}(u)`. -/
@[simp]
theorem perturbedFDeriv_apply_stdComplexLineReal (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.perturbedFDeriv Ks Kt u z stdComplexLineReal =
      fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) := by
  simp [perturbedFDeriv_apply]

/-- The `∂_t` component of the perturbed derivative is `∂_t u - X_{K_t}(u)`. -/
@[simp]
theorem perturbedFDeriv_apply_stdComplexLineImag (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.perturbedFDeriv Ks Kt u z stdComplexLineImag =
      fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) := by
  simp [perturbedFDeriv_apply]

/-- **The Floer equation in coordinates.** The perturbed derivative is complex linear, that is
`(du - X_K)^{0,1} = 0`, exactly when `∂_s u - X_{K_s}(u) + J (∂_t u - X_{K_t}(u)) = 0`. -/
theorem isComplexLinearMap_perturbedFDeriv_iff (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) ↔
      fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
        J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) = 0 := by
  rw [isComplexLinearMap_stdComplexLine_iff]
  simp only [ContinuousLinearMap.coe_coe, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag]
  constructor
  · intro h
    rw [h, AlmostComplexStructure.apply_apply, add_neg_cancel]
  · intro h
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, map_neg, AlmostComplexStructure.apply_apply, neg_neg]

end Differential

section Density

/-- The Floer energy density `ω(∂_s u - X_{K_s}(u), ∂_t u - X_{K_t}(u))` of a map `u` at `z`:
the symplectic area density of the perturbed derivative. -/
noncomputable def floerEnergyDensity (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  ω (ω.perturbedFDeriv Ks Kt u z stdComplexLineReal)
    (ω.perturbedFDeriv Ks Kt u z stdComplexLineImag)

theorem floerEnergyDensity_def (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    ω.floerEnergyDensity Ks Kt u z =
      ω (ω.perturbedFDeriv Ks Kt u z stdComplexLineReal)
        (ω.perturbedFDeriv Ks Kt u z stdComplexLineImag) :=
  (rfl)

variable {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- **The pointwise energy identity.** The Floer energy density is the symplectic area density
`ω(∂_s u, ∂_t u)`, plus the exterior derivative `∂_s (K_t(u)) - ∂_t (K_s(u))` of the pulled-back
one-form `K(u)`, minus the curvature `R_K(u)`. -/
theorem floerEnergyDensity_eq (ω : SymplecticForm V) (hu : DifferentiableAt ℝ u z)
    (hKs : DifferentiableAt ℝ (uncurry Ks) (z, u z))
    (hKt : DifferentiableAt ℝ (uncurry Kt) (z, u z)) :
    ω.floerEnergyDensity Ks Kt u z =
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
        ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- The chain rule along the graph of `u`, and the domain slices, for `K = Ks` and `K = Kt`.
  have hgraph (K : ℝ × ℝ → V → ℝ) (hK : DifferentiableAt ℝ (uncurry K) (z, u z)) (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K w (u w)) z v =
        fderiv ℝ (uncurry K) (z, u z) (v, 0) + fderiv ℝ (K z) (u z) (fderiv ℝ u z v) :=
    fderiv_comp_graph_apply (f := uncurry K) hu hK v
  have hslice (K : ℝ × ℝ → V → ℝ) (hK : DifferentiableAt ℝ (uncurry K) (z, u z)) (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K w (u z)) z v = fderiv ℝ (uncurry K) (z, u z) (v, 0) :=
    congrArg (· v) (fderiv_slice_left (f := uncurry K) hK)
  rw [floerEnergyDensity_def, hamiltonianCurvature_def, poissonBracket_def,
    perturbedFDeriv_apply_stdComplexLineReal, perturbedFDeriv_apply_stdComplexLineImag,
    hgraph Kt hKt, hgraph Ks hKs, hslice Kt hKt, hslice Ks hKs]
  -- Contracting the Hamiltonian vector fields with `du` gives the target derivatives of `K`.
  have hs : ω.toBilinForm (ω.hamiltonianVectorField (Ks z) (u z))
      (fderiv ℝ u z stdComplexLineImag) = fderiv ℝ (Ks z) (u z) (fderiv ℝ u z stdComplexLineImag) :=
    ω.apply_hamiltonianVectorField _ _ _
  have ht : ω.toBilinForm (fderiv ℝ u z stdComplexLineReal)
      (ω.hamiltonianVectorField (Kt z) (u z)) =
        -fderiv ℝ (Kt z) (u z) (fderiv ℝ u z stdComplexLineReal) := by
    rw [← ω.apply_hamiltonianVectorField, ω.neg_eq]
  simp only [map_sub, LinearMap.sub_apply]
  rw [hs, ht]
  ring

end Density

section Integral

variable {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- For perturbation data that is `C¹` over an open set `U` of the domain, the curvature evaluated
along a map continuous on `U` is continuous on `U`. -/
theorem continuousOn_hamiltonianCurvature_comp (ω : SymplecticForm V) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) :
    ContinuousOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) U := by
  have hmem {z : ℝ × ℝ} (hz : z ∈ U) : (z, u z) ∈ U ×ˢ (univ : Set V) := ⟨hz, mem_univ _⟩
  have hD (K : ℝ × ℝ → V → ℝ) (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) :
      ContinuousOn (fun z ↦ fderiv ℝ (uncurry K) (z, u z)) U :=
    (hK.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp
      (continuousOn_id.prodMk hu) fun _ hz ↦ hmem hz
  have hdiff (K : ℝ × ℝ → V → ℝ) (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ U) : DifferentiableAt ℝ (uncurry K) (z, u z) :=
    (hK.differentiableOn one_ne_zero _ (hmem hz)).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds (hmem hz))
  -- The domain and target derivatives of `K` along `u` are restrictions of its joint derivative.
  have hslice (K : ℝ × ℝ → V → ℝ) (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ U) (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K w (u z)) z v = fderiv ℝ (uncurry K) (z, u z) (v, 0) :=
    congrArg (· v) (fderiv_slice_left (f := uncurry K) (hdiff K hK hz))
  have hX (K : ℝ × ℝ → V → ℝ) (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) :
      ContinuousOn (fun z ↦ ω.hamiltonianVectorField (K z) (u z)) U :=
    ω.continuousOn_hamiltonianVectorField_comp <|
      ((hD K hK).clm_comp (continuousOn_const (c := ContinuousLinearMap.inr ℝ (ℝ × ℝ) V))).congr
        fun _ hz ↦ fderiv_slice_right (f := uncurry K) (hdiff K hK hz)
  have h : ContinuousOn (fun z ↦ fderiv ℝ (uncurry Kt) (z, u z) (stdComplexLineReal, 0) -
      fderiv ℝ (uncurry Ks) (z, u z) (stdComplexLineImag, 0) -
        ω (ω.hamiltonianVectorField (Ks z) (u z)) (ω.hamiltonianVectorField (Kt z) (u z))) U :=
    (((hD Kt hKt).clm_apply continuousOn_const).sub
      ((hD Ks hKs).clm_apply continuousOn_const)).sub
        (ω.continuousOn_apply_comp (hX Ks hKs) (hX Kt hKt))
  refine h.congr fun z hz ↦ ?_
  simp only [hamiltonianCurvature_def, poissonBracket_def, hslice Ks hKs hz, hslice Kt hKt hz]

/-- For `C¹` perturbation data, the curvature evaluated along a continuous map is continuous. -/
theorem continuous_hamiltonianCurvature_comp (ω : SymplecticForm V) (hu : Continuous u)
    (hKs : ContDiff ℝ 1 (uncurry Ks)) (hKt : ContDiff ℝ 1 (uncurry Kt)) :
    Continuous fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z) :=
  continuousOn_univ.mp <| ω.continuousOn_hamiltonianCurvature_comp isOpen_univ hu.continuousOn
    (by simpa using hKs.contDiffOn) (by simpa using hKt.contDiffOn)

/-- **The energy identity on a rectangle.** For a map `u` and perturbation data that are `C¹` over
an open neighbourhood of a rectangle `[a₁, b₁] × [a₂, b₂]`, the integral of the Floer energy
density over the rectangle is the symplectic area, plus the integral of the pulled-back one-form
`K(u) = K_s(u) ds + K_t(u) dt` over the positively oriented boundary, minus the integral of the
curvature `R_K(u)`. -/
theorem integral_floerEnergyDensity (ω : SymplecticForm V) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) {a b : ℝ × ℝ} (hab : a ≤ b)
    (habU : Icc a b ⊆ U) :
    ∫ z in Icc a b, ω.floerEnergyDensity Ks Kt u z =
      (∫ z in Icc a b, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ s in a.1..b.1, Ks (s, a.2) (u (s, a.2))) + (∫ t in a.2..b.2, Kt (b.1, t) (u (b.1, t))) -
          (∫ s in a.1..b.1, Ks (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, Kt (a.1, t) (u (a.1, t))) -
        ∫ z in Icc a b, ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- The pulled-back components `K_t(u)` and `-K_s(u)`, to which the divergence theorem applies.
  set f : ℝ × ℝ → ℝ := fun w ↦ Kt w (u w)
  set g : ℝ × ℝ → ℝ := fun w ↦ -Ks w (u w)
  have hmem {z : ℝ × ℝ} (hz : z ∈ U) : (z, u z) ∈ U ×ˢ (univ : Set V) := ⟨hz, mem_univ _⟩
  have hf : ContDiffOn ℝ 1 f U := hKt.comp (contDiffOn_id.prodMk hu) fun _ hz ↦ hmem hz
  have hg : ContDiffOn ℝ 1 g U := (hKs.comp (contDiffOn_id.prodMk hu) fun _ hz ↦ hmem hz).neg
  have hKdiff {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ U) : DifferentiableAt ℝ (uncurry K) (z, u z) :=
    (hK.differentiableOn one_ne_zero _ (hmem hz)).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds (hmem hz))
  have hdiff {h : ℝ × ℝ → ℝ} (hh : ContDiffOn ℝ 1 h U) {z : ℝ × ℝ} (hz : z ∈ U) :
      HasFDerivAt h (fderiv ℝ h z) z :=
    ((hh.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hint {z : ℝ × ℝ} (hz : z ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2) : z ∈ U :=
    habU (Icc_prod_eq a b ▸ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
  have hcont {L : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} (hL : ContinuousOn L U) (v : ℝ × ℝ) :
      IntegrableOn (fun z ↦ L z v) (Icc a b) :=
    ((hL.mono habU).clm_apply continuousOn_const).integrableOn_compact isCompact_Icc
  have hderiv : IntegrableOn
      (fun z ↦ fderiv ℝ f z stdComplexLineReal + fderiv ℝ g z stdComplexLineImag) (Icc a b) :=
    (hcont (hf.continuousOn_fderiv_of_isOpen hU le_rfl) _).add
      (hcont (hg.continuousOn_fderiv_of_isOpen hU le_rfl) _)
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g (fderiv ℝ f) (fderiv ℝ g)
    a b hab (hf.continuousOn.mono habU) (hg.continuousOn.mono habU)
    (fun _ hz ↦ hdiff hf (hint hz)) (fun _ hz ↦ hdiff hg (hint hz)) hderiv
  have hg' (z : ℝ × ℝ) : fderiv ℝ g z stdComplexLineImag =
      -fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag := by
    simp [g, fderiv_fun_neg]
  -- The remaining terms of the pointwise identity are integrable.
  have hdu' : ContinuousOn (fderiv ℝ u) (Icc a b) :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).mono habU
  have harea : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) (Icc a b) :=
    (ω.continuousOn_apply_comp (hdu'.clm_apply continuousOn_const)
      (hdu'.clm_apply continuousOn_const)).integrableOn_compact isCompact_Icc
  have hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (Icc a b) :=
    ((ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn hKs hKt).mono
      habU).integrableOn_compact isCompact_Icc
  calc
    ∫ z in Icc a b, ω.floerEnergyDensity Ks Kt u z =
        ∫ z in Icc a b, (ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) +
          (fderiv ℝ f z stdComplexLineReal + fderiv ℝ g z stdComplexLineImag) -
          ω.hamiltonianCurvature Ks Kt z (u z)) := by
      refine setIntegral_congr_fun measurableSet_Icc fun z hz ↦ ?_
      have hzU := habU hz
      rw [ω.floerEnergyDensity_eq ((hu.differentiableOn one_ne_zero z hzU).differentiableAt
          (hU.mem_nhds hzU)) (hKdiff hKs hzU) (hKdiff hKt hzU), hg', ← sub_eq_add_neg]
    _ = _ := by
      have hsum : IntegrableOn (fun z ↦
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) +
            (fderiv ℝ f z stdComplexLineReal + fderiv ℝ g z stdComplexLineImag)) (Icc a b) :=
        harea.add hderiv
      rw [integral_sub hsum hcurv, integral_add harea hderiv]
      have h₁ : stdComplexLineReal = ((1 : ℝ), (0 : ℝ)) := rfl
      have h₂ : stdComplexLineImag = ((0 : ℝ), (1 : ℝ)) := rfl
      rw [h₁, h₂, hdiv]
      simp only [g, intervalIntegral.integral_neg, f]
      ring

end Integral

end TauCeti.SymplecticForm
