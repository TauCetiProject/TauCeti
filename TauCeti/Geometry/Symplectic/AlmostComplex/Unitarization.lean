/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Unitary normalization of complex-linear frames

Let `(V, ω)` be a real vector space with a symplectic form and an `ω`-compatible complex
structure `J`, so that `g(v, w) = ω(v, J w)` is an inner product and `h = g + i ω` is a Hermitian
inner product on the complex vector space `(V, J)`. Let `G` be a finite-dimensional complex inner
product space, such as `ℂⁿ`. A **unitary frame** of `V` is a real-linear map `φ : G → V` with
`J φ = φ i` that carries the inner product of `G` to `h`:

`ω(φ v, J φ w) = Re ⟪v, w⟫` and `ω(φ v, φ w) = Im ⟪v, w⟫`.

The second identity says that `φ` carries the standard symplectic form `Im ⟪·, ·⟫` of `G` to `ω`,
so a unitary frame is a symplectic frame that is complex linear.

A complex-linear frame `φ` that is not unitary is normalized by the metric change transport
`T = H ^ (-1/2)` of the metric `k(v, w) = ω(φ v, J φ w)` that `φ` pulls back to `G`
(`TauCeti.SymplecticForm.frameMetric`), for the real inner product `Re ⟪·, ·⟫` of `G`; here `H` is
the Riesz operator of `k`. The **unitarization** of `φ` is `φ ∘ T`
(`TauCeti.SymplecticForm.unitarization`). Since `k` is invariant under multiplication by `i`, so is
`T`, by naturality of the metric change transport under the isometry `v ↦ i v`. Hence:

* the unitarization is complex linear (`TauCeti.SymplecticForm.Compatible.unitarization_I_smul`);
* it is unitary (`TauCeti.SymplecticForm.Compatible.apply_unitarization_apply_unitarization`,
  `TauCeti.SymplecticForm.Compatible.apply_unitarization_unitarization`);
* it is injective (`TauCeti.SymplecticForm.Compatible.unitarization_injective`), and a frame that is
  already unitary is its own unitarization (`TauCeti.SymplecticForm.unitarization_eq_self`).

Two unitary frames onto the same space differ by a unitary automorphism of `G`
(`TauCeti.SymplecticForm.inner_symm_apply_symm_apply_of_unitary`).

The construction involves no choices, and `T` depends continuously on `k`
(`ContinuousLinearMap.continuousOn_metricChangeTransport`). So a continuous family of
complex-linear frames, for instance a frame of the tangent bundle of a symplectic manifold along a
map from a contractible space, is normalized to a continuous family of unitary frames. These are
the symplectic trivializations in which the linearized flow along a capped Hamiltonian orbit
becomes a path of symplectic matrices, whose Conley–Zehnder index grades the capped orbit.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (compatible complex structures and unitary frames of symplectic vector bundles).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press (1974), §2 (the
  orthonormalization of frames of a Euclidean vector bundle).
-/

public section

noncomputable section

open InnerProductSpace
open scoped InnerProductSpace

/-- The Riesz operator of a real bilinear form. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

-- The real inner product `Re ⟪·, ·⟫` of a complex inner product space, with respect to which the
-- metric change transport of a pulled-back metric is taken.
attribute [local instance] InnerProductSpace.complexToReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}
  {J : AlmostComplexStructure V}
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
  {φ : G →ₗ[ℝ] V}

variable (ω J) in
/-- The metric `k(v, w) = ω(φ v, J φ w)` of `J` pulled back along a real-linear map `φ : G → V`,
as a continuous bilinear form on `G`. -/
def frameMetric (φ : G →ₗ[ℝ] V) : G →L[ℝ] G →L[ℝ] ℝ :=
  ((ω.associatedBilinForm J).compl₁₂ φ φ).toContinuousBilinearMap

@[simp]
theorem frameMetric_apply (φ : G →ₗ[ℝ] V) (v w : G) :
    ω.frameMetric J φ v w = ω (φ v) (J (φ w)) :=
  (rfl)

variable (ω J) in
/-- The **unitarization** of a real-linear map `φ : G → V`: its composite `φ ∘ T` with the metric
change transport `T` of the metric `ω(φ ·, J φ ·)` it pulls back to `G`, for the real inner product
`Re ⟪·, ·⟫` of `G`. For an `ω`-compatible `J` and an injective complex-linear `φ` it is a unitary
frame (`TauCeti.SymplecticForm.Compatible.apply_unitarization_apply_unitarization`,
`TauCeti.SymplecticForm.Compatible.apply_unitarization_unitarization`). -/
def unitarization (φ : G →ₗ[ℝ] V) : G →ₗ[ℝ] V :=
  φ ∘ₗ ((ω.frameMetric J φ).metricChangeTransport : G →ₗ[ℝ] G)

theorem unitarization_apply (φ : G →ₗ[ℝ] V) (v : G) :
    ω.unitarization J φ v = φ ((ω.frameMetric J φ).metricChangeTransport v) :=
  (rfl)

/-- The metric pulled back along an injective map by the metric of a compatible structure has a
strictly positive Riesz operator. -/
theorem Compatible.isStrictlyPositive_frameMetric (hJ : ω.Compatible J)
    (hφ : Function.Injective φ) : IsStrictlyPositive (ω.frameMetric J φ)♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    ⟨fun u v ↦ by simp only [frameMetric_apply, hJ.associatedBilinForm_apply_swap],
      fun v hv ↦ by
        rw [frameMetric_apply]
        exact hJ.associated_pos fun h0 ↦ hv (hφ (h0.trans φ.map_zero.symm))⟩

/-- The metric change transport of the pulled-back metric of a complex-linear map commutes with
multiplication by `i`. -/
theorem Compatible.metricChangeTransport_frameMetric_I_smul (hJ : ω.Compatible J)
    (hφ : Function.Injective φ) (hφJ : ∀ v, φ (Complex.I • v) = J (φ v)) (v : G) :
    (ω.frameMetric J φ).metricChangeTransport (Complex.I • v) =
      Complex.I • (ω.frameMetric J φ).metricChangeTransport v := by
  -- The metric is invariant under the isometry `e : v ↦ i v`, so its transport is conjugated
  -- by `e`.
  let e : G ≃ₗᵢ[ℝ] G :=
    { toLinearEquiv := (Complex.smulIEquiv G).toLinearEquiv
      norm_map' := fun v ↦ by simp [norm_smul] }
  have he (u : G) : e u = Complex.I • u := Complex.smulIEquiv_apply u
  have hk : (ω.frameMetric J φ).bilinearComp (e : G →L[ℝ] G) (e : G →L[ℝ] G) =
      ω.frameMetric J φ := by
    ext u w
    simp only [ContinuousLinearMap.bilinearComp_apply, frameMetric_apply]
    -- `bilinearComp` evaluates `e` through its coercion to a continuous linear map, which `simp`
    -- does not fold back to the application `e u`.
    change ω (φ (e u)) (J (φ (e w))) = ω (φ u) (J (φ w))
    rw [he, he, hφJ, hφJ, hJ.invariant_apply]
  have h := ContinuousLinearMap.metricChangeTransport_bilinearComp e
    (hJ.isStrictlyPositive_frameMetric hφ) v
  rw [hk] at h
  rw [← he, ← he, h, LinearIsometryEquiv.apply_symm_apply]

/-- **The unitarization is complex linear.** -/
theorem Compatible.unitarization_I_smul (hJ : ω.Compatible J) (hφ : Function.Injective φ)
    (hφJ : ∀ v, φ (Complex.I • v) = J (φ v)) (v : G) :
    ω.unitarization J φ (Complex.I • v) = J (ω.unitarization J φ v) := by
  rw [unitarization_apply, hJ.metricChangeTransport_frameMetric_I_smul hφ hφJ, hφJ,
    unitarization_apply]

/-- **The unitarization is an isometry** from the real inner product `Re ⟪·, ·⟫` of `G` to the
metric `ω(·, J ·)`. -/
theorem Compatible.apply_unitarization_apply_unitarization (hJ : ω.Compatible J)
    (hφ : Function.Injective φ) (v w : G) :
    ω (ω.unitarization J φ v) (J (ω.unitarization J φ w)) = (inner ℂ v w).re := by
  have h := ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport
    (hJ.isStrictlyPositive_frameMetric hφ) v w
  rwa [frameMetric_apply, real_inner_eq_re_inner ℂ, RCLike.re_to_complex] at h

/-- **The unitarization is symplectic**: it carries the standard symplectic form `Im ⟪·, ·⟫` of
`G` to `ω`. -/
theorem Compatible.apply_unitarization_unitarization (hJ : ω.Compatible J)
    (hφ : Function.Injective φ) (hφJ : ∀ v, φ (Complex.I • v) = J (φ v)) (v w : G) :
    ω (ω.unitarization J φ v) (ω.unitarization J φ w) = (inner ℂ v w).im := by
  -- `ω(a, b) = -ω(a, J (J b))` and `J b` is the unitarization of `i w`.
  have h := hJ.apply_unitarization_apply_unitarization hφ v (Complex.I • w)
  rw [hJ.unitarization_I_smul hφ hφJ, AlmostComplexStructure.apply_apply, inner_smul_right,
    Complex.I_mul_re] at h
  -- The `CoeFun` instance of `SymplecticForm` applies `ω` through `ω.toBilinForm`, so the
  -- application `ω a` is definitionally the linear map `ω.toBilinForm a`, whose `map_neg` applies.
  have hneg : ω (ω.unitarization J φ v) (-ω.unitarization J φ w) =
      -ω (ω.unitarization J φ v) (ω.unitarization J φ w) :=
    map_neg (ω.toBilinForm (ω.unitarization J φ v)) _
  linarith

/-- The unitarization of an injective map is injective. -/
theorem Compatible.unitarization_injective (hJ : ω.Compatible J) (hφ : Function.Injective φ) :
    Function.Injective (ω.unitarization J φ) :=
  hφ.comp (ContinuousLinearMap.isUnit_iff_bijective.1
    (ContinuousLinearMap.isStrictlyPositive_metricChangeTransport
      (hJ.isStrictlyPositive_frameMetric hφ)).isUnit).1

/-- **A unitary frame is its own unitarization.** If `φ` already carries `Re ⟪·, ·⟫` to the metric
`ω(·, J ·)`, its pulled-back metric is the real inner product of `G`, whose transport is the
identity. -/
theorem unitarization_eq_self (hu : ∀ v w, ω (φ v) (J (φ w)) = (inner ℂ v w).re) :
    ω.unitarization J φ = φ := by
  have hk : ω.frameMetric J φ = innerSL ℝ := by
    ext v w
    rw [frameMetric_apply, hu, innerSL_apply_apply, real_inner_eq_re_inner ℂ, RCLike.re_to_complex]
  ext v
  rw [unitarization_apply, hk, ContinuousLinearMap.metricChangeTransport_innerSL, one_apply_eq_self]

omit [FiniteDimensional ℂ G] in
/-- **Two unitary frames differ by a unitary automorphism.** If `ψ₁ : G → V` is unitary and
`ψ₂ : G ≃ V` is a unitary isomorphism, then `ψ₂⁻¹ ∘ ψ₁` preserves the inner product of `G`. -/
theorem inner_symm_apply_symm_apply_of_unitary {ψ₁ : G →ₗ[ℝ] V} {ψ₂ : G ≃ₗ[ℝ] V}
    (hψ₁ : ∀ v w, ω (ψ₁ v) (J (ψ₁ w)) = (inner ℂ v w).re)
    (hψ₁' : ∀ v w, ω (ψ₁ v) (ψ₁ w) = (inner ℂ v w).im)
    (hψ₂ : ∀ v w, ω (ψ₂ v) (J (ψ₂ w)) = (inner ℂ v w).re)
    (hψ₂' : ∀ v w, ω (ψ₂ v) (ψ₂ w) = (inner ℂ v w).im) (v w : G) :
    inner ℂ (ψ₂.symm (ψ₁ v)) (ψ₂.symm (ψ₁ w)) = inner ℂ v w := by
  apply Complex.ext
  · rw [← hψ₂, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hψ₁]
  · rw [← hψ₂', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hψ₁']

end TauCeti.SymplecticForm
