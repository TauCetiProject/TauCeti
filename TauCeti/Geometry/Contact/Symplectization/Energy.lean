/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Geometry.Contact.StableHamiltonian
public import TauCeti.Geometry.Contact.Symplectization.Cylindrical
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# The ω-energy and the end energy of maps into a cylinder `ℝ × V`

Let `(α, ω)` be a stable Hamiltonian structure on a manifold `V`
(`TauCeti.SmoothForm.IsStableHamiltonian`), with characteristic vector field `R`
(`TauCeti.SmoothForm.characteristicVectorField`). Holomorphic curves in the cylinder `ℝ × V`, for
almost complex structures sending `∂_a` to `R` and compatible with `ω` on `ker α`
(`Module.Dual.IsCylindricalComplexStructure`), have two energies, which Bourgeois, Eliashberg,
Hofer, Wysocki and Zehnder use in their compactness theorem. For a map `u = (a, f)` from a domain
with coordinates `(s, t)`:

* the **ω-energy** `E_ω(u) = ∫ f^*ω` (`TauCeti.SmoothForm.omegaEnergy`);
* the **end energy** (the `λ`-energy) `E_λ(u) = sup_φ ∫ (φ ∘ a) da ∧ f^*α`
  (`TauCeti.SmoothForm.endEnergy`), the supremum over the smooth nonnegative compactly supported
  functions `φ : ℝ → ℝ` of integral `1` (`TauCeti.endEnergyTestFunctions`).

As for `TauCeti.SmoothTwoForm.stdComplexLineEnergy`, a map is given together with a field `du` of
candidate differentials, `du z : ℝ × ℝ → ℝ × T_{f z} V`, and integrands are read through their
positive parts. The two densities, `(f^*ω)(∂_s, ∂_t)` (`TauCeti.SmoothForm.omegaEnergyDensity`) and
`(da ∧ f^*α)(∂_s, ∂_t)` (`TauCeti.SmoothForm.endEnergyDensity`), add up to the symplectization form
`ds ∧ α + ω` of the cylinder evaluated on `du(∂_s)` and `du(∂_t)`
(`TauCeti.SmoothForm.endEnergyDensity_add_omegaEnergyDensity`).

* **Positivity.** If `du(∂_t) = J du(∂_s)` for a cylindrical `J`, both densities are nonnegative
  (`TauCeti.SmoothForm.endEnergyDensity_nonneg`, `TauCeti.SmoothForm.omegaEnergyDensity_nonneg`):
  writing `du(∂_s) = (s, v)`, the end density is `s² + α(v)²` and the ω-density is `ω(u, J u)` for
  the component `u` of `v` in `ker α`. So for holomorphic maps the positive parts lose nothing.
* **Invariance.** Translating the `ℝ`-coordinate `a` by a constant does not change the end energy
  (`TauCeti.SmoothForm.endEnergy_add_const`), since translates of test functions are test functions.
  Both energies are invariant under injective orientation-preserving changes `ψ` of the domain
  coordinates (`TauCeti.SmoothForm.omegaEnergy_restrict_image`,
  `TauCeti.SmoothForm.endEnergy_restrict_image`): the densities are coefficients of two-forms,
  multiplied by `det dψ` (`TauCeti.SmoothForm.omegaEnergyDensity_comp`,
  `TauCeti.SmoothForm.endEnergyDensity_comp`).
* **Additivity.** The ω-energy is additive in the domain measure
  (`TauCeti.SmoothForm.omegaEnergy_add_measure`). The end energy, a supremum, is only subadditive
  (`TauCeti.SmoothForm.endEnergy_add_measure_le`).
* **Trivial cylinders.** Let `γ` be an integral curve of a vector field `R` with `α(R) = 1` along
  `γ`, such as the characteristic vector field
  (`TauCeti.SmoothForm.apply_characteristicVectorField`), and `c > 0`. The cylinder
  `(s, t) ↦ (c s, γ (c t))` has derivative `TauCeti.trivialCylinderDeriv`
  (`TauCeti.hasMFDerivAt_trivialCylinder`). Over `ℝ × [0, 1]` its ω-energy is `0`
  (`TauCeti.SmoothForm.omegaEnergy_trivialCylinder`) and its end energy is
  `c² ∫ φ(c s) ds = c` (`TauCeti.SmoothForm.endEnergy_trivialCylinder`), the action `∫₀ᶜ γ^*α` of
  the trajectory. For a `T`-periodic orbit `γ` and `c = k T` this is the `k`-fold trivial cylinder,
  which is `1`-periodic in `t` (`Function.Periodic.const_mul`) and has end energy `k T`, the action
  of the orbit counted with covering multiplicity, while its ω-energy vanishes. So for varying
  asymptotic orbits a bound on the ω-energy alone does not bound the end energy.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder, *Compactness results in
  symplectic field theory*, Geom. Topol. 7 (2003), 799–888, arXiv:math/0308183, §5.3 (the
  energies `E_ω` and `E_λ` of holomorphic curves in the cylinder over a stable Hamiltonian
  structure).
* H. Hofer, *Pseudoholomorphic curves in symplectizations with applications to the Weinstein
  conjecture in dimension three*, Invent. Math. 114 (1993), 515–563 (the end energy as a supremum
  over test functions).
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped Manifold ENNReal

namespace TauCeti

/-! ### Test functions -/

open scoped ContDiff in
/-- The **test functions of the end energy**: the smooth nonnegative compactly supported functions
`φ : ℝ → ℝ` of integral `1`. -/
def endEnergyTestFunctions : Set (ℝ → ℝ) :=
  {φ | ContDiff ℝ ∞ φ ∧ (∀ r, 0 ≤ φ r) ∧ HasCompactSupport φ ∧ ∫ r, φ r = 1}

open scoped ContDiff in
theorem mem_endEnergyTestFunctions {φ : ℝ → ℝ} :
    φ ∈ endEnergyTestFunctions ↔
      ContDiff ℝ ∞ φ ∧ (∀ r, 0 ≤ φ r) ∧ HasCompactSupport φ ∧ ∫ r, φ r = 1 :=
  Iff.rfl

/-- There are test functions, for instance normalized smooth bump functions. -/
theorem endEnergyTestFunctions_nonempty : endEnergyTestFunctions.Nonempty := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f.normed volume, f.contDiff_normed (n := ⊤), f.nonneg_normed, f.hasCompactSupport_normed,
    f.integral_normed⟩

/-- Translates of test functions are test functions. -/
theorem comp_add_const_mem_endEnergyTestFunctions {φ : ℝ → ℝ}
    (hφ : φ ∈ endEnergyTestFunctions) (c : ℝ) : (fun r ↦ φ (r + c)) ∈ endEnergyTestFunctions := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hφ
  exact ⟨h₁.comp (contDiff_id.add contDiff_const), fun r ↦ h₂ _,
    h₃.comp_homeomorph (Homeomorph.addRight c), by rw [integral_add_right_eq_self φ c, h₄]⟩

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-! ### Energy densities -/

/-- The **ω-energy density** `(f^*ω)(∂_s, ∂_t)` of a map `f` into `V` with differential field
`du`, whose second component is the differential of `f`. -/
def omegaEnergyDensity (ω : SmoothForm I M ℝ 2) (f : ℝ × ℝ → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (f z)) (z : ℝ × ℝ) : ℝ :=
  ω.bilinFormAt (f z) (du z stdComplexLineReal).2 (du z stdComplexLineImag).2

theorem omegaEnergyDensity_def (ω : SmoothForm I M ℝ 2) (f : ℝ × ℝ → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (f z)) (z : ℝ × ℝ) :
    ω.omegaEnergyDensity f du z =
      ω.bilinFormAt (f z) (du z stdComplexLineReal).2 (du z stdComplexLineImag).2 :=
  (rfl)

/-- The **end-energy density** `(da ∧ f^*α)(∂_s, ∂_t)` of a map `u = (a, f)` into `ℝ × V` with
differential field `du`, whose first component is the differential of `a` and whose second
component is the differential of `f`. -/
def endEnergyDensity (α : SmoothForm I M ℝ 1) (f : ℝ × ℝ → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (f z)) (z : ℝ × ℝ) : ℝ :=
  (du z stdComplexLineReal).1 *
      (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (du z stdComplexLineImag).2 -
    (du z stdComplexLineImag).1 *
      (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (du z stdComplexLineReal).2

theorem endEnergyDensity_def (α : SmoothForm I M ℝ 1) (f : ℝ × ℝ → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (f z)) (z : ℝ × ℝ) :
    α.endEnergyDensity f du z =
      (du z stdComplexLineReal).1 *
          (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (du z stdComplexLineImag).2 -
        (du z stdComplexLineImag).1 *
          (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (du z stdComplexLineReal).2 :=
  (rfl)

variable {α : SmoothForm I M ℝ 1} {ω : SmoothForm I M ℝ 2} {f : ℝ × ℝ → M}
  {du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (f z)}

variable (α ω f du) in
/-- The end-energy density and the ω-energy density are the two parts `ds ∧ α` and `ω` of the
symplectization form of the cylinder `ℝ × V`, evaluated on `du(∂_s)` and `du(∂_t)`. -/
theorem endEnergyDensity_add_omegaEnergyDensity (z : ℝ × ℝ) :
    α.endEnergyDensity f du z + ω.omegaEnergyDensity f du z =
      Module.Dual.symplectizationForm (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ)
        (ω.bilinFormAt (f z)) (du z stdComplexLineReal) (du z stdComplexLineImag) := by
  rw [Module.Dual.symplectizationForm_apply, endEnergyDensity_def, omegaEnergyDensity_def]

section Positivity

variable [FiniteDimensional ℝ E] {z : ℝ × ℝ} {J : AlmostComplexStructure (ℝ × TangentSpace I (f z))}

/-- **The end-energy density of a holomorphic map is nonnegative.** If `α` is contact for `ω` at
`f z` and `du(∂_t) = J du(∂_s)` for a cylindrical complex structure `J`, then the end-energy
density at `z` is `s² + α(v)² ≥ 0`, where `du(∂_s) = (s, v)`. -/
theorem endEnergyDensity_nonneg
    (hc : Module.Dual.IsContact (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ)
      (ω.bilinFormAt (f z)))
    (hJ : Module.Dual.IsCylindricalComplexStructure
      (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (ω.bilinFormAt (f z)) J)
    (hdu : du z stdComplexLineImag = J (du z stdComplexLineReal)) :
    0 ≤ α.endEnergyDensity f du z := by
  have h := hJ.mul_apply_snd_sub_fst_mul hc (du z stdComplexLineReal).1
    (du z stdComplexLineReal).2
  rw [Prod.mk.eta] at h
  rw [endEnergyDensity_def, hdu, h]
  positivity

/-- **The ω-energy density of a holomorphic map is nonnegative.** If `α` is contact for `ω` at
`f z` and `du(∂_t) = J du(∂_s)` for a cylindrical complex structure `J`, then the ω-energy density
at `z` is `ω(u, J u) ≥ 0`, where `u` is the component in `ker α` of the second coordinate of
`du(∂_s)`. -/
theorem omegaEnergyDensity_nonneg
    (hc : Module.Dual.IsContact (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ)
      (ω.bilinFormAt (f z)))
    (hJ : Module.Dual.IsCylindricalComplexStructure
      (degreeOneEquiv α (f z) : TangentSpace I (f z) →ₗ[ℝ] ℝ) (ω.bilinFormAt (f z)) J)
    (hdu : du z stdComplexLineImag = J (du z stdComplexLineReal)) :
    0 ≤ ω.omegaEnergyDensity f du z := by
  have h := hJ.apply_apply_snd_nonneg (isAlt_bilinFormAt ω (f z)) hc (du z stdComplexLineReal).1
    (du z stdComplexLineReal).2
  rw [Prod.mk.eta] at h
  rwa [omegaEnergyDensity_def, hdu]

end Positivity

/-- **Change of domain coordinates for the ω-energy density.** Precomposing the differential field
with linear maps `L w` multiplies the density at `w` by `det (L w)`: the density is the coefficient
of the two-form `f^*ω`. -/
theorem omegaEnergyDensity_comp (ψ : ℝ × ℝ → ℝ × ℝ) (L : ℝ × ℝ → (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)
    (w : ℝ × ℝ) :
    ω.omegaEnergyDensity (f ∘ ψ) (fun w ↦ du (ψ w) ∘ₗ L w) w =
      LinearMap.det (L w) * ω.omegaEnergyDensity f du (ψ w) := by
  have h (e : ℝ × ℝ) : (du (ψ w) (L w e)).2 = (L w e).1 • (du (ψ w) stdComplexLineReal).2 +
      (L w e).2 • (du (ψ w) stdComplexLineImag).2 := by
    rw [(du (ψ w)).apply_stdComplexLine (L w e), Prod.snd_add, Prod.smul_snd, Prod.smul_snd]
  rw [omegaEnergyDensity_def, omegaEnergyDensity_def, ← smul_eq_mul,
    ← (isAlt_bilinFormAt ω (f (ψ w))).apply_smul_add_smul_det (L w)]
  simp only [LinearMap.comp_apply, Function.comp_apply, h, stdComplexLineReal_eq,
    stdComplexLineImag_eq]

/-- **Change of domain coordinates for the end-energy density.** Precomposing the differential
field with linear maps `L w` multiplies the density at `w` by `det (L w)`: the density is the
coefficient of the two-form `da ∧ f^*α`. -/
theorem endEnergyDensity_comp (ψ : ℝ × ℝ → ℝ × ℝ) (L : ℝ × ℝ → (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)
    (w : ℝ × ℝ) :
    α.endEnergyDensity (f ∘ ψ) (fun w ↦ du (ψ w) ∘ₗ L w) w =
      LinearMap.det (L w) * α.endEnergyDensity f du (ψ w) := by
  have h := LinearMap.det_mul_wedge_finTwoProd (L w) (LinearMap.fst ℝ ℝ _ ∘ₗ du (ψ w))
    ((degreeOneEquiv α (f (ψ w)) : TangentSpace I (f (ψ w)) →ₗ[ℝ] ℝ) ∘ₗ
      LinearMap.snd ℝ ℝ _ ∘ₗ du (ψ w))
  simp only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply] at h
  simp only [endEnergyDensity_def, LinearMap.comp_apply, Function.comp_apply,
    stdComplexLineReal_eq, stdComplexLineImag_eq]
  exact h.symm

/-! ### The energies -/

variable (ω f du) in
/-- The **ω-energy** `E_ω(u) = ∫ f^*ω` of a map with differential field `du`, over a measure `μ`
on the domain: the lower integral of the positive part of the ω-energy density. For holomorphic
maps the density is nonnegative (`TauCeti.SmoothForm.omegaEnergyDensity_nonneg`), so nothing is
truncated. -/
def omegaEnergy (μ : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (ω.omegaEnergyDensity f du z) ∂μ

variable (α f du) in
/-- The **end energy** `E_λ(u) = sup_φ ∫ (φ ∘ a) da ∧ f^*α` of a map `u = (a, f)` into `ℝ × V`
with differential field `du`, over a measure `μ` on the domain: the supremum, over the test
functions `φ` (`TauCeti.endEnergyTestFunctions`), of the lower integral of the positive part of
`φ (a z)` times the end-energy density. For holomorphic maps the density is nonnegative
(`TauCeti.SmoothForm.endEnergyDensity_nonneg`), so nothing is truncated. -/
def endEnergy (a : ℝ × ℝ → ℝ) (μ : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ⨆ φ ∈ endEnergyTestFunctions, ∫⁻ z, ENNReal.ofReal (φ (a z) * α.endEnergyDensity f du z) ∂μ

variable (ω f du) in
theorem omegaEnergy_def (μ : Measure (ℝ × ℝ)) :
    ω.omegaEnergy f du μ = ∫⁻ z, ENNReal.ofReal (ω.omegaEnergyDensity f du z) ∂μ :=
  (rfl)

variable (α f du) in
theorem endEnergy_def (a : ℝ × ℝ → ℝ) (μ : Measure (ℝ × ℝ)) :
    α.endEnergy f du a μ =
      ⨆ φ ∈ endEnergyTestFunctions,
        ∫⁻ z, ENNReal.ofReal (φ (a z) * α.endEnergyDensity f du z) ∂μ :=
  (rfl)

variable {a : ℝ × ℝ → ℝ}

/-- **The ω-energy is additive** in the domain measure. -/
@[simp]
theorem omegaEnergy_add_measure (μ ν : Measure (ℝ × ℝ)) :
    ω.omegaEnergy f du (μ + ν) = ω.omegaEnergy f du μ + ω.omegaEnergy f du ν := by
  simp only [omegaEnergy_def, lintegral_add_measure]

/-- **The end energy is subadditive** in the domain measure. As a supremum over test functions it
is not additive in general: the two pieces may be bounded through different test functions. -/
theorem endEnergy_add_measure_le (μ ν : Measure (ℝ × ℝ)) :
    α.endEnergy f du a (μ + ν) ≤ α.endEnergy f du a μ + α.endEnergy f du a ν := by
  simp only [endEnergy_def, lintegral_add_measure]
  exact iSup₂_le fun φ hφ ↦ add_le_add (le_iSup₂_of_le φ hφ le_rfl) (le_iSup₂_of_le φ hφ le_rfl)

/-- **Translation invariance of the end energy.** Translating the `ℝ`-coordinate `a` of the map by
a constant `c` does not change its end energy. -/
@[simp]
theorem endEnergy_add_const (c : ℝ) (μ : Measure (ℝ × ℝ)) :
    α.endEnergy f du (fun z ↦ a z + c) μ = α.endEnergy f du a μ := by
  simp only [endEnergy_def]
  refine le_antisymm (iSup₂_le fun φ hφ ↦ ?_) (iSup₂_le fun φ hφ ↦ ?_)
  · exact le_iSup₂_of_le (fun r ↦ φ (r + c)) (comp_add_const_mem_endEnergyTestFunctions hφ c)
      le_rfl
  · refine le_iSup₂_of_le (fun r ↦ φ (r + -c)) (comp_add_const_mem_endEnergyTestFunctions hφ (-c))
      (le_of_eq ?_)
    simp only [add_neg_cancel_right]

/-- **Invariance of the ω-energy under changes of domain coordinates.** For a change of
coordinates `ψ` that is injective, differentiable and orientation preserving on a measurable set
`s`, the ω-energy of `f` over `ψ '' s` is the ω-energy over `s` of `f ∘ ψ`, with the differential
field `du ∘ ψ` precomposed with `dψ`. -/
theorem omegaEnergy_restrict_image {ψ : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hinj : InjOn ψ s) (hψ : ∀ w ∈ s, DifferentiableAt ℝ ψ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ ψ w).det) :
    ω.omegaEnergy f du (volume.restrict (ψ '' s)) =
      ω.omegaEnergy (f ∘ ψ) (fun w ↦ du (ψ w) ∘ₗ (fderiv ℝ ψ w : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
        (volume.restrict s) := by
  rw [omegaEnergy_def, omegaEnergy_def]
  exact lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs hinj hψ fun w hw ↦ by
    rw [omegaEnergyDensity_comp, abs_of_nonneg (hdet w hw)]

/-- **Invariance of the end energy under changes of domain coordinates.** For a change of
coordinates `ψ` that is injective, differentiable and orientation preserving on a measurable set
`s`, the end energy of `(a, f)` over `ψ '' s` is the end energy over `s` of `(a ∘ ψ, f ∘ ψ)`, with
the differential field `du ∘ ψ` precomposed with `dψ`. -/
theorem endEnergy_restrict_image {ψ : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hinj : InjOn ψ s) (hψ : ∀ w ∈ s, DifferentiableAt ℝ ψ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ ψ w).det) :
    α.endEnergy f du a (volume.restrict (ψ '' s)) =
      α.endEnergy (f ∘ ψ) (fun w ↦ du (ψ w) ∘ₗ (fderiv ℝ ψ w : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) (a ∘ ψ)
        (volume.restrict s) := by
  rw [endEnergy_def, endEnergy_def]
  refine biSup_congr fun φ _ ↦
    lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs hinj hψ fun w hw ↦ ?_
  rw [endEnergyDensity_comp, abs_of_nonneg (hdet w hw), Function.comp_apply]
  ring

end SmoothForm

/-! ### Trivial cylinders -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable (R : (x : M) → TangentSpace I x) in
/-- The differential of the cylinder `(s, t) ↦ (c s, γ (c t))` over an integral curve `γ` of a
vector field `R`, at `z = (s, t)`: the linear map `(v₁, v₂) ↦ (c v₁, c v₂ R(γ (c t)))`
(`TauCeti.hasMFDerivAt_trivialCylinder`). -/
def trivialCylinderDeriv (γ : ℝ → M) (c : ℝ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ × TangentSpace I (γ (c * z.2)) :=
  (c • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((c • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (R (γ (c * z.2))))

variable {R : (x : M) → TangentSpace I x} {γ : ℝ → M}

@[simp]
theorem trivialCylinderDeriv_apply (c : ℝ) (z v : ℝ × ℝ) :
    trivialCylinderDeriv R γ c z v = (c * v.1, (c * v.2) • R (γ (c * z.2))) := by
  simp [trivialCylinderDeriv]

/-- **The derivative of a trivial cylinder.** If `γ` is an integral curve of `R`, the cylinder
`(s, t) ↦ (c s, γ (c t))` into `ℝ × M` has derivative `TauCeti.trivialCylinderDeriv R γ c z` at
`z`. -/
theorem hasMFDerivAt_trivialCylinder (hγ : IsMIntegralCurve γ R) (c : ℝ) (z : ℝ × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod I) (fun z : ℝ × ℝ ↦ (c * z.1, γ (c * z.2))) z
      (trivialCylinderDeriv R γ c z) := by
  have hf₁ : HasFDerivAt (fun z : ℝ × ℝ ↦ c * z.1) (c • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hasFDerivAt_fst.const_mul c
  have hf₂ : HasFDerivAt (fun z : ℝ × ℝ ↦ c * z.2) (c • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    hasFDerivAt_snd.const_mul c
  -- The chain rule gives `R(γ (c t))` times the derivative `c • snd` of `(s, t) ↦ c t`, that is
  -- `v ↦ (c v₁, 1 (c v₂) • R(γ (c t)))`. As `1 : ℝ →L[ℝ] ℝ` is the identity, this unfolds to
  -- `trivialCylinderDeriv R γ c z v = (c v₁, (c v₂) • R(γ (c t)))`, so the maps agree by `rfl`.
  -- (`simp` cannot do this step: the chain-rule map is typed between the `TangentSpace` type
  -- synonyms of `ℝ × ℝ` and `ℝ × TangentSpace I _`, where the `ℝ × ℝ` lemmas do not apply.)
  exact (hf₁.hasMFDerivAt.prodMk ((hγ (c * z.2)).comp z hf₂.hasMFDerivAt)).congr_mfderiv
    (ContinuousLinearMap.ext fun _ ↦ rfl)

namespace SmoothForm

variable [IsManifold I 1 M]

/-- **The ω-energy of a trivial cylinder vanishes**: the `V`-component of the differential field
`TauCeti.trivialCylinderDeriv R γ c` vanishes in the `s`-direction, so the pullback of `ω` is zero.
When `γ` is an integral curve of `R`, this field is the differential of the cylinder
`(s, t) ↦ (c s, γ (c t))` (`TauCeti.hasMFDerivAt_trivialCylinder`). -/
theorem omegaEnergy_trivialCylinder (ω : SmoothForm I M ℝ 2) (c : ℝ) (μ : Measure (ℝ × ℝ)) :
    ω.omegaEnergy (fun z ↦ γ (c * z.2))
        (fun z ↦ (trivialCylinderDeriv R γ c z : (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (γ (c * z.2))))
        μ = 0 := by
  simp [omegaEnergy_def, omegaEnergyDensity_def, stdComplexLineReal_eq]

/-- If `α(R) = 1` along `γ`, the end-energy density of the differential field
`TauCeti.trivialCylinderDeriv R γ c` is `c²`. When `γ` is an integral curve of `R`, this field is
the differential of the trivial cylinder `(s, t) ↦ (c s, γ (c t))`
(`TauCeti.hasMFDerivAt_trivialCylinder`), so this is the cylinder's end-energy density. -/
theorem endEnergyDensity_trivialCylinder {α : SmoothForm I M ℝ 1}
    (hR : ∀ t, α.val (γ t) ![R (γ t)] = 1) (c : ℝ) (z : ℝ × ℝ) :
    α.endEnergyDensity (fun z ↦ γ (c * z.2))
        (fun z ↦ (trivialCylinderDeriv R γ c z : (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (γ (c * z.2))))
        z = c ^ 2 := by
  simp only [endEnergyDensity_def, stdComplexLineReal_eq, ContinuousLinearMap.coe_coe,
    trivialCylinderDeriv_apply, mul_one, mul_zero, zero_smul, stdComplexLineImag_eq, map_smul,
    degreeOneEquiv_coe_apply, hR, smul_eq_mul, zero_mul, sub_zero]
  ring

/-- **The end energy of a trivial cylinder is its action.** Let `γ` be a curve along which
`α(R) = 1` and `c > 0`. Over `ℝ × [0, 1]`, the differential field
`TauCeti.trivialCylinderDeriv R γ c` has end energy `c`: for every test function `φ`,
`∫ φ(c s) c² ds dt = c`. When `γ` is an integral curve of `R`, for instance of the characteristic
vector field, this field is the differential of the cylinder `(s, t) ↦ (c s, γ (c t))`
(`TauCeti.hasMFDerivAt_trivialCylinder`) and `c = ∫₀ᶜ γ^*α` is the action of `γ` over `[0, c]`,
so the cylinder's end energy is that action. -/
theorem endEnergy_trivialCylinder {α : SmoothForm I M ℝ 1} (hR : ∀ t, α.val (γ t) ![R (γ t)] = 1)
    {c : ℝ} (hc : 0 < c) :
    α.endEnergy (fun z ↦ γ (c * z.2))
        (fun z ↦ (trivialCylinderDeriv R γ c z : (ℝ × ℝ) →ₗ[ℝ] ℝ × TangentSpace I (γ (c * z.2))))
        (fun z ↦ c * z.1) (volume.restrict (univ ×ˢ Icc 0 1)) = ENNReal.ofReal c := by
  rw [endEnergy_def]
  simp_rw [endEnergyDensity_trivialCylinder hR]
  refine (biSup_congr fun φ hφ ↦ ?_).trans (biSup_const endEnergyTestFunctions_nonempty)
  obtain ⟨hφs, hφ0, hφc, hφ1⟩ := hφ
  have hcont : Continuous fun s : ℝ ↦ φ (c * s) * c ^ 2 :=
    (hφs.continuous.comp (continuous_const.mul continuous_id)).mul continuous_const
  -- The integrand only depends on `s`, and `[0, 1]` has length `1`.
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun z : ℝ × ℝ ↦ ENNReal.ofReal (φ (c * z.1) * c ^ 2))
      (ENNReal.continuous_ofReal.comp (hcont.comp continuous_fst)).measurable.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, mul_one]
  -- `∫ φ(c s) c² ds = c² |c⁻¹| ∫ φ = c`.
  have hint : Integrable (fun s : ℝ ↦ φ (c * s) * c ^ 2) :=
    ((hφs.continuous.integrable_of_hasCompactSupport hφc).comp_mul_left' hc.ne').mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s ↦ mul_nonneg (hφ0 _) (sq_nonneg c)), integral_mul_const,
    Measure.integral_comp_mul_left, hφ1, smul_eq_mul, mul_one, abs_inv, abs_of_pos hc]
  congr 1
  field_simp

end SmoothForm

end TauCeti
