/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes

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
tameness (`SymplecticForm.floerEnergyDensity_nonneg`) and is half the metric energy density
`|du - X_K|²`, by `IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`.
For a merely tame `J` the form `ω(·, J ·)` is not a metric, so the energy is compared with the norm
instead: if `c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖`, the energy density of a solution bounds
`c (‖∂_s u - X_{K_s}‖² + ‖∂_t u - X_{K_t}‖²)` up to the factor `1 + M²`, pointwise and after
integration. Such constants exist uniformly over a compact set of tamed structures
(`IsCompact.exists_pos_forall_mul_norm_sq_le`), so on a compact window of tamed structures the
energy bounds the `L²` norm of the perturbed derivative.

The main result is the energy identity: pointwise,
`ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t}) = ω(∂_s u, ∂_t u) + d(K(u)) - R_K(u)`,
where `d(K(u)) = ∂_s (K_t(u)) - ∂_t (K_s(u))` is the exterior derivative of the pulled-back
one-form `K(u) = K_s(u) ds + K_t(u) dt`. Integrated over a rectangle using Stokes' formula,
the energy is the symplectic area plus the boundary integral of `K(u)` minus the integral of the
curvature. Curvature bounds therefore turn into energy bounds. For a cylindrical perturbation
`K = H_t dt`, the curvature vanishes; for a continuation perturbation `K = β(s) H_t dt`, it is
`β'(s) H_t`.

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianCurvature`: the curvature `R_K`.
* `TauCeti.SymplecticForm.hamiltonianOneForm`: the vector-valued one-form
  `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}`.
* `TauCeti.SymplecticForm.perturbedFDeriv`: the perturbed derivative `du - X_K`.
* `TauCeti.SymplecticForm.floerEnergyDensity`: the Floer energy density.

## Main results

* `SymplecticForm.floerEnergyDensity_eq`: the pointwise energy identity.
* `SymplecticForm.floerEnergyDensity_nonneg`: the energy density of a solution is nonnegative.
* `SymplecticForm.floerEnergyDensity_eq_zero_iff`: under tameness, the energy density of a
  solution vanishes exactly where the perturbed derivative does.
* `SymplecticForm.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity` and
  `SymplecticForm.setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le`: the energy controls the
  perturbed derivative, pointwise and in `L²`.
* `SymplecticForm.integral_floerEnergyDensity`: the energy identity on a rectangle.
* `SymplecticForm.floerEnergyDensity_add_hamiltonianCurvature_eq`: for a `C²` map, the energy
  density plus the curvature is the exterior derivative of the one-form `K(u) + λ(u)`, where
  `λₓ(v) = ½ ω(x, v)` is the primitive of `ω`; this globalizes the energy identity to domains
  that are not rectangles.
* `SymplecticForm.isComplexLinearMap_perturbedFDeriv_iff`: the coordinate form of the Floer
  equation.
* `SymplecticForm.hamiltonianCurvature_zero_left`,
  `SymplecticForm.hamiltonianCurvature_cylindrical`,
  `SymplecticForm.hamiltonianCurvature_continuation`: the curvature of perturbations without `ds`
  component, and `SymplecticForm.hamiltonianCurvature_eq_zero_of_cylindrical`, its local form
  along a line near which the perturbation is cylindrical.
* `SymplecticForm.hamiltonianCurvature_congr_of_eventuallyEq`,
  `SymplecticForm.hamiltonianCurvature_comp_add_right`: the curvature is local in the domain and
  commutes with domain translations, and likewise for the perturbed derivative
  (`SymplecticForm.perturbedFDeriv_congr_of_eventuallyEq`,
  `SymplecticForm.perturbedFDeriv_comp_add_right`) and the energy density
  (`SymplecticForm.floerEnergyDensity_congr_of_eventuallyEq`,
  `SymplecticForm.floerEnergyDensity_comp_add_right`); hence translations preserve the energy
  (`SymplecticForm.lintegral_floerEnergyDensity_comp_add_right`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations, their curvature and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on inhomogeneous
  pseudoholomorphic maps and their energy.
-/

public section

open Filter Function MeasureTheory Set Topology

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
  rw [hamiltonianCurvature_zero_left, stdComplexLineReal_eq]
  exact fderiv_comp_snd_apply_mk_zero (fun t ↦ H t x) z 1

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

omit [FiniteDimensional ℝ V] in
/-- The cylindrical perturbation `K = H_t dt` of a `Cⁿ` time-dependent Hamiltonian is `Cⁿ`. -/
theorem contDiff_uncurry_cylindrical {n : WithTop ℕ∞} {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ n (uncurry H)) : ContDiff ℝ n (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
  hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)

/-- The curvature only depends on the germs of the perturbation data at the domain point. -/
theorem hamiltonianCurvature_congr_of_eventuallyEq (ω : SymplecticForm V)
    {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ} {z : ℝ × ℝ} (hs : Ks =ᶠ[𝓝 z] Ks') (ht : Kt =ᶠ[𝓝 z] Kt') :
    ω.hamiltonianCurvature Ks Kt z = ω.hamiltonianCurvature Ks' Kt' z := by
  ext x
  have hs' : (fun w ↦ Ks w x) =ᶠ[𝓝 z] fun w ↦ Ks' w x := hs.mono fun _ hw ↦ congrFun hw x
  have ht' : (fun w ↦ Kt w x) =ᶠ[𝓝 z] fun w ↦ Kt' w x := ht.mono fun _ hw ↦ congrFun hw x
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def, hs'.fderiv_eq, ht'.fderiv_eq,
    hs.eq_of_nhds, ht.eq_of_nhds]

/-- Curvature commutes with translations of the domain. -/
theorem hamiltonianCurvature_comp_add_right (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (v z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) z x =
      ω.hamiltonianCurvature Ks Kt (z + v) x := by
  simp only [hamiltonianCurvature_def]
  rw [fderiv_comp_add_right (f := fun w ↦ Kt w x), fderiv_comp_add_right (f := fun w ↦ Ks w x)]

/-- A datum `K = K_s ds + K_t dt` with `K_s = 0` and `K_t` independent of `s` near the line
`s = c` has zero curvature along that line. -/
theorem hamiltonianCurvature_eq_zero_of_cylindrical (ω : SymplecticForm V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {c : ℝ} (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (t : ℝ) (x : V) :
    ω.hamiltonianCurvature Ks Kt (c, t) x = 0 := by
  have hfst : Tendsto Prod.fst (𝓝 ((c, t) : ℝ × ℝ)) (𝓝 c) := continuous_fst.tendsto (c, t)
  have hs : Ks =ᶠ[𝓝 (c, t)] fun _ _ ↦ 0 := by
    filter_upwards [hfst.eventually hKs] with w hw
    funext x
    simpa using congrFun (hw w.2) x
  have ht : Kt =ᶠ[𝓝 (c, t)] fun w ↦ Kt (c, w.2) := by
    filter_upwards [hfst.eventually hKt] with w hw
    simpa using hw w.2
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht]
  exact ω.hamiltonianCurvature_cylindrical (fun t ↦ Kt (c, t)) (c, t) x

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

/-- The Hamiltonian vector field `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` of the perturbation one-form
`K = K_s ds + K_t dt`, at the domain point `z` and the target point `x`: it sends a tangent vector
`(a, b)` of the domain to `a X_{K_s}(x) + b X_{K_t}(x)`. -/
noncomputable def hamiltonianOneForm (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (z : ℝ × ℝ) (x : V) : ℝ × ℝ →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Ks z) x) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Kt z) x)

@[simp]
theorem hamiltonianOneForm_apply (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (z : ℝ × ℝ)
    (x : V) (v : ℝ × ℝ) :
    ω.hamiltonianOneForm Ks Kt z x v =
      v.1 • ω.hamiltonianVectorField (Ks z) x + v.2 • ω.hamiltonianVectorField (Kt z) x :=
  (rfl)

/-- The perturbed derivative is `du - X_K(u)`. -/
theorem perturbedFDeriv_eq_sub (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    ω.perturbedFDeriv Ks Kt u z = fderiv ℝ u z - ω.hamiltonianOneForm Ks Kt z (u z) := by
  ext <;> simp [perturbedFDeriv_apply]

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

/-- The perturbed derivative commutes with translations of the domain: translating the map and
the perturbation data by `v` translates the perturbed derivative by `v`. -/
theorem perturbedFDeriv_comp_add_right (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (v z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.perturbedFDeriv Ks Kt u (z + v) := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedFDeriv_apply, fderiv_comp_add_right]

/-- The perturbed derivative at `z` only depends on the germ of the map at `z`. -/
theorem perturbedFDeriv_congr_of_eventuallyEq (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    {u u' : ℝ × ℝ → V} {z : ℝ × ℝ} (h : u =ᶠ[𝓝 z] u') :
    ω.perturbedFDeriv Ks Kt u z = ω.perturbedFDeriv Ks Kt u' z := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedFDeriv_apply, h.fderiv_eq, h.eq_of_nhds]

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

/-- For the zero perturbation the Floer energy density is the symplectic area density
`ω(∂_s u, ∂_t u)`. -/
@[simp]
theorem floerEnergyDensity_zero (ω : SymplecticForm V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z =
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
  simp [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag]

/-- The Floer energy density commutes with translations of the domain. -/
theorem floerEnergyDensity_comp_add_right (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (v z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.floerEnergyDensity Ks Kt u (z + v) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedFDeriv_comp_add_right]

/-- The Floer energy density at `z` only depends on the germ of the map at `z`. -/
theorem floerEnergyDensity_congr_of_eventuallyEq (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    {u u' : ℝ × ℝ → V} {z : ℝ × ℝ} (h : u =ᶠ[𝓝 z] u') :
    ω.floerEnergyDensity Ks Kt u z = ω.floerEnergyDensity Ks Kt u' z := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def,
    ω.perturbedFDeriv_congr_of_eventuallyEq Ks Kt h]

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

/-- **Nonnegativity of the Floer energy density.** If the perturbed derivative of `u` at `z` is
complex linear for an almost complex structure `J` tamed by `ω`, that is if `u` solves the Floer
equation at `z`, then the Floer energy density at `z` is nonnegative. -/
theorem floerEnergyDensity_nonneg (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z := by
  simpa only [floerEnergyDensity_def, ContinuousLinearMap.coe_coe] using
    h.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg hJ

/-- The Floer energy density of a solution of the Floer equation
`∂_s u + J (∂_t u - X_{K_t}(u)) = 0` at `z`, for the perturbation `K = K_t dt` with a
domain-dependent Hamiltonian `K_t`, is nonnegative when `J` is tamed by `ω`. -/
theorem floerEnergyDensity_zero_left_nonneg (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J)
    (hfloer : fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u z :=
  ω.floerEnergyDensity_nonneg hJ <|
    (ω.isComplexLinearMap_perturbedFDeriv_iff J _ _ u z).2 (by simpa using hfloer)

/-- For a solution of the Floer equation at `z`, the `t`-component of the perturbed derivative is
`J` applied to its `s`-component `a = ∂_s u - X_{K_s}`, so the Floer energy density is
`ω(a, J a)`. -/
theorem floerEnergyDensity_eq_of_isComplexLinearMap (ω : SymplecticForm V)
    {J : AlmostComplexStructure V}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerEnergyDensity Ks Kt u z =
      ω (ω.perturbedFDeriv Ks Kt u z stdComplexLineReal)
        (J (ω.perturbedFDeriv Ks Kt u z stdComplexLineReal)) := by
  rw [floerEnergyDensity_def]
  exact congrArg _ h.apply_stdComplexLineImag

/-- For a solution of the Floer equation with `J` tamed by `ω`, the Floer energy density at `z`
vanishes exactly when the perturbed derivative `du - X_K` vanishes at `z`. -/
theorem floerEnergyDensity_eq_zero_iff (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerEnergyDensity Ks Kt u z = 0 ↔ ω.perturbedFDeriv Ks Kt u z = 0 := by
  -- The metric energy density of a solution is twice its Floer energy density.
  rw [← ω.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff hJ,
    h.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm, floerEnergyDensity_def]
  simp only [ContinuousLinearMap.coe_coe, mul_eq_zero, two_ne_zero, false_or]

/-- **Coercivity of the Floer energy density.** Let `u` solve the Floer equation at `z` for an
almost complex structure `J` with `c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖` for all `v`, where
`0 ≤ c`. Then the energy density controls both components of the perturbed derivative:
`c (‖∂_s u - X_{K_s}‖² + ‖∂_t u - X_{K_t}‖²) ≤ (1 + M²) ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})`.
For `J` ranging over a compact set of tamed structures, uniform constants `c > 0` and `M` exist
by `IsCompact.exists_pos_forall_mul_norm_sq_le` and the boundedness of compact sets. -/
theorem mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity
    (ω : SymplecticForm V) {J : AlmostComplexStructure V} {c M : ℝ} (hc : 0 ≤ c)
    (hJc : ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J v)) (hJM : ∀ v, ‖J v‖ ≤ M * ‖v‖)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    c * (‖ω.perturbedFDeriv Ks Kt u z stdComplexLineReal‖ ^ 2 +
        ‖ω.perturbedFDeriv Ks Kt u z stdComplexLineImag‖ ^ 2) ≤
      (1 + M ^ 2) * ω.floerEnergyDensity Ks Kt u z := by
  rw [ω.floerEnergyDensity_eq_of_isComplexLinearMap h]
  set a := ω.perturbedFDeriv Ks Kt u z stdComplexLineReal
  -- The `t`-component is `J a`, of norm at most `M ‖a‖`, and `ω(a, J a)` dominates `c ‖a‖²`.
  have hM : ‖ω.perturbedFDeriv Ks Kt u z stdComplexLineImag‖ ^ 2 ≤ M ^ 2 * ‖a‖ ^ 2 := by
    rw [show ω.perturbedFDeriv Ks Kt u z stdComplexLineImag = J a from
      h.apply_stdComplexLineImag, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hJM a) 2
  nlinarith [hJc a, mul_le_mul_of_nonneg_left hM hc, sq_nonneg M, sq_nonneg ‖a‖]

/-- **The energy density plus the curvature is exact.** For a `C²` map `u` into a symplectic
vector space and a perturbation `K = K_s ds + K_t dt`, the Floer energy density plus the
curvature `R_K(u)` is the exterior derivative `∂_s α_t - ∂_t α_s` of the one-form
`α = K(u) + λ(u)`, where `λₓ(v) = ½ ω(x, v)` is the primitive of `ω`. -/
theorem floerEnergyDensity_add_hamiltonianCurvature_eq (ω : SymplecticForm V)
    (hu : ContDiffAt ℝ 2 u z) (hKs : DifferentiableAt ℝ (uncurry Ks) (z, u z))
    (hKt : DifferentiableAt ℝ (uncurry Kt) (z, u z)) :
    ω.floerEnergyDensity Ks Kt u z + ω.hamiltonianCurvature Ks Kt z (u z) =
      fderiv ℝ (fun w ↦ Kt w (u w) + 1 / 2 * ω (u w) (fderiv ℝ u w stdComplexLineImag)) z
          stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w (u w) + 1 / 2 * ω (u w) (fderiv ℝ u w stdComplexLineReal)) z
          stdComplexLineImag := by
  have hu₁ : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
  have hgraph {K : ℝ × ℝ → V → ℝ} (hK : DifferentiableAt ℝ (uncurry K) (z, u z)) :
      DifferentiableAt ℝ (fun w ↦ K w (u w)) z :=
    hK.comp (f := fun w ↦ (w, u w)) z (differentiableAt_id.prodMk hu₁)
  -- The derivative of `w ↦ ω(u w, ∂_v u w)` in the direction `e`.
  have hL (v : ℝ × ℝ) : HasFDerivAt (fun w ↦ ω (u w) (fderiv ℝ u w v)) _ z :=
    ω.toBilinForm.toContinuousBilinearMap.hasFDerivAt_bilinear_fderiv_apply hu v
  have hL' (v e : ℝ × ℝ) : fderiv ℝ (fun w ↦ ω (u w) (fderiv ℝ u w v)) z e =
      ω (fderiv ℝ u z e) (fderiv ℝ u z v) + ω (u z) (fderiv ℝ (fderiv ℝ u) z e v) := by
    rw [(hL v).fderiv]
    simp [add_comm]
  have hsymm : fderiv ℝ (fderiv ℝ u) z stdComplexLineReal stdComplexLineImag =
      fderiv ℝ (fderiv ℝ u) z stdComplexLineImag stdComplexLineReal :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  rw [fderiv_fun_add (hgraph hKt) ((hL _).differentiableAt.const_mul _),
    fderiv_fun_add (hgraph hKs) ((hL _).differentiableAt.const_mul _),
    fderiv_const_mul (hL _).differentiableAt, fderiv_const_mul (hL _).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul, hL', hsymm]
  rw [ω.floerEnergyDensity_eq hu₁ hKs hKt]
  linear_combination (-1 / 2 : ℝ) *
    ω.neg_eq (fderiv ℝ u z stdComplexLineImag) (fderiv ℝ u z stdComplexLineReal)

end Density

section Integral

/-- **Translations preserve the energy.** Translating the map and the perturbation data by `v`
preserves the energy: the energy of the translate over `(· + v) ⁻¹' S` is the energy of the
original over `S`. -/
theorem lintegral_floerEnergyDensity_comp_add_right (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + v) ⁻¹' S, ENNReal.ofReal
        (ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [floerEnergyDensity_comp_add_right]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight v)
    (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)) S

variable {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- For a map and perturbation data that are `C¹` over an open set `U` of the domain, the Floer
energy density is continuous on `U`. -/
theorem continuousOn_floerEnergyDensity (ω : SymplecticForm V) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) :
    ContinuousOn (ω.floerEnergyDensity Ks Kt u) U := by
  have hdu := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  refine (ω.continuousOn_apply_comp
    ((hdu.clm_apply (continuousOn_const (c := stdComplexLineReal))).sub
      (ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn hU hu.continuousOn hKs))
    ((hdu.clm_apply (continuousOn_const (c := stdComplexLineImag))).sub
      (ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn hU hu.continuousOn hKt))).congr
    fun z _ ↦ ?_
  simp only [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag, Pi.sub_apply]

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
  -- The domain derivatives of `K` along `u` are restrictions of its joint derivative.
  have hslice (K : ℝ × ℝ → V → ℝ) (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ U) (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K w (u z)) z v = fderiv ℝ (uncurry K) (z, u z) (v, 0) :=
    congrArg (· v) (fderiv_slice_left (f := uncurry K) (hdiff K hK hz))
  have h : ContinuousOn (fun z ↦ fderiv ℝ (uncurry Kt) (z, u z) (stdComplexLineReal, 0) -
      fderiv ℝ (uncurry Ks) (z, u z) (stdComplexLineImag, 0) -
        ω (ω.hamiltonianVectorField (Ks z) (u z)) (ω.hamiltonianVectorField (Kt z) (u z))) U :=
    (((hD Kt hKt).clm_apply continuousOn_const).sub
      ((hD Ks hKs).clm_apply continuousOn_const)).sub
        (ω.continuousOn_apply_comp
          (ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn hU hu hKs)
          (ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn hU hu hKt))
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
  -- The pulled-back components `K_s(u)` and `K_t(u)`, to which Green's theorem applies.
  have hmem {z : ℝ × ℝ} (hz : z ∈ U) : (z, u z) ∈ U ×ˢ (univ : Set V) := ⟨hz, mem_univ _⟩
  have hf : ContDiffOn ℝ 1 (fun w ↦ Kt w (u w)) U :=
    hKt.comp (contDiffOn_id.prodMk hu) fun _ hz ↦ hmem hz
  have hg : ContDiffOn ℝ 1 (fun w ↦ Ks w (u w)) U :=
    hKs.comp (contDiffOn_id.prodMk hu) fun _ hz ↦ hmem hz
  have hKdiff {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ U) : DifferentiableAt ℝ (uncurry K) (z, u z) :=
    (hK.differentiableOn one_ne_zero _ (hmem hz)).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds (hmem hz))
  have hderiv : IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) (Icc a b) :=
    integrableOn_fderiv_sub_fderiv_Icc hU hg hf habU
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
  have hsum : IntegrableOn (fun z ↦
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag)) (Icc a b) :=
    harea.add hderiv
  rw [setIntegral_congr_fun measurableSet_Icc fun z hz ↦ ω.floerEnergyDensity_eq
      ((hu.differentiableOn one_ne_zero z (habU hz)).differentiableAt (hU.mem_nhds (habU hz)))
      (hKdiff hKs (habU hz)) (hKdiff hKt (habU hz)),
    integral_sub hsum hcurv, integral_add harea hderiv, stdComplexLineReal_eq,
    stdComplexLineImag_eq, integral_fderiv_sub_fderiv_Icc hU hg hf hab habU]

/-- **The energy controls the perturbed derivative in `L²`.** Let `u` solve the Floer equation on
a measurable set `U` for domain-dependent almost complex structures `J z` satisfying
`c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` on `U`, with `0 < c`. Then the integral over `U` of
`‖∂_s u - X_{K_s}‖² + ‖∂_t u - X_{K_t}‖²` is at most `(1 + M²) / c` times the energy over `U`.
No measurability of the integrands is assumed. -/
theorem setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le (ω : SymplecticForm V)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}
    (hc : 0 < c) (hJc : ∀ z ∈ U, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ U, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (h : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫⁻ z in U, ENNReal.ofReal (‖ω.perturbedFDeriv Ks Kt u z stdComplexLineReal‖ ^ 2 +
        ‖ω.perturbedFDeriv Ks Kt u z stdComplexLineImag‖ ^ 2) ≤
      ENNReal.ofReal ((1 + M ^ 2) / c) *
        ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hU fun z hz => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
  exact ω.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity hc.le (hJc z hz)
    (hJM z hz) (h z hz)

end Integral

end TauCeti.SymplecticForm
