/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
import TauCeti.Analysis.Calculus.DifferentialForm.Coordinates

/-!
# Stokes' theorem on a coordinate box

Let `a ≤ b` in `ℝᵖ⁺¹`, so that `Icc a b = ∏ᵢ [aᵢ, bᵢ]` is a coordinate box, and read its points
in Euclidean space `EuclideanSpace ℝ (Fin (p + 1))` through `toLp 2`. For a `p`-form `ω` on
Euclidean space, evaluated on the standard basis `e₀, …, eₚ`, with coefficients
`ωᵢ = ω(e₀, …, êᵢ, …, eₚ)`,

`∫_{[a, b]} dω(e₀, …, eₚ) = ∑ᵢ (-1)ⁱ (∫_{xᵢ = bᵢ} ωᵢ - ∫_{xᵢ = aᵢ} ωᵢ)`

(`TauCeti.integral_extDeriv_toLp_Icc`), where the faces `xᵢ = bᵢ` and `xᵢ = aᵢ` of the box are
parametrized by inserting `bᵢ`, respectively `aᵢ`, as the `i`-th coordinate of the points of the
box `∏_{j ≠ i} [aⱼ, bⱼ]` of one dimension less. The right-hand side is the boundary flux
`TauCeti.boxBoundarySum` of the signed coefficients `(-1)ⁱ ωᵢ`. This is Stokes'
theorem for a box with the boundary orientation of the cubical boundary operator: the face
`xᵢ = bᵢ` carries the sign `(-1)ⁱ` and the face `xᵢ = aᵢ` the sign `-(-1)ⁱ`.

The hypotheses are those of Mathlib's divergence theorem
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`: continuity on the closed box,
differentiability in the open box and integrability of `dω` on the box. The exterior derivative on
the standard basis is the divergence of the signed coefficients
(`DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth`), so Stokes' theorem is the divergence
theorem applied to these coefficients.

## References

* M. Spivak, *Calculus on Manifolds*, Chapter 4 (Stokes' theorem for the standard cube, with the
  boundary orientation `∑ᵢ ∑_α (-1)^{i + α} I_{(i, α)}`, coordinates counted from one there).
-/

public section

open MeasureTheory Set WithLp

namespace TauCeti

variable {p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Stokes' theorem on a coordinate box.** For `a ≤ b` and a `p`-form `ω` on
`EuclideanSpace ℝ (Fin (p + 1))` which is continuous on the box `Icc a b`, differentiable in its
interior and has integrable exterior derivative on it, the integral of `dω` on the standard basis
over the box is the boundary flux of the signed coefficients `(-1)ⁱ ω(e₀, …, êᵢ, …, eₚ)`: the sum
over `i` of their integrals over the face `xᵢ = bᵢ` minus those over the face `xᵢ = aᵢ`. -/
theorem integral_extDeriv_toLp_Icc {a b : Fin (p + 1) → ℝ} (hab : a ≤ b)
    {ω : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F}
    (hc : ContinuousOn (fun x ↦ ω (toLp 2 x)) (Icc a b))
    (hd : ∀ x ∈ pi univ fun i ↦ Ioo (a i) (b i), DifferentiableAt ℝ ω (toLp 2 x))
    (hi : IntegrableOn (fun x ↦ extDeriv ω (toLp 2 x) fun i ↦ EuclideanSpace.single i 1)
      (Icc a b)) :
    ∫ x in Icc a b, extDeriv ω (toLp 2 x) (fun i ↦ EuclideanSpace.single i 1) =
      boxBoundarySum a b fun i x ↦
        (-1 : ℝ) ^ (i : ℕ) • ω (toLp 2 x) (i.removeNth fun j ↦ EuclideanSpace.single j 1) := by
  set e : Fin (p + 1) → EuclideanSpace ℝ (Fin (p + 1)) := fun i ↦ EuclideanSpace.single i 1
  -- The signed coefficients of `ω`, as one vector-valued function on Euclidean space.
  set G := ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := F) e ∘ ω
  set L := (EuclideanSpace.equiv (Fin (p + 1)) ℝ).symm.toContinuousLinearMap
  set f : Fin (p + 1) → (Fin (p + 1) → ℝ) → F := fun i x ↦ G (toLp 2 x) i
  set f' : Fin (p + 1) → (Fin (p + 1) → ℝ) → (Fin (p + 1) → ℝ) →L[ℝ] F :=
    fun i x ↦ (ContinuousLinearMap.proj i).comp ((fderiv ℝ G (toLp 2 x)).comp L)
  have hG {x : Fin (p + 1) → ℝ} (hx : DifferentiableAt ℝ ω (toLp 2 x)) :
      DifferentiableAt ℝ G (toLp 2 x) :=
    (ContinuousAlternatingMap.signedRemoveNth e).differentiableAt.comp _ hx
  have hf' : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∀ i, HasFDerivAt (f i) (f' i x) x :=
    fun x hx i ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (p + 1) ↦ F) i).hasFDerivAt
      |>.comp x ((hG (hd x hx)).hasFDerivAt.comp x L.hasFDerivAt)
  -- In the open box, the divergence of the signed coefficients is the exterior derivative.
  have hdiv : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)),
      ∑ i, f' i x (Pi.single i 1) = extDeriv ω (toLp 2 x) e := fun x hx ↦ by
    have h := (hd x hx).differentiableWithinAt.sum_fderivWithin_signedRemoveNth
      (s := univ) uniqueDiffWithinAt_univ e
    rw [fderivWithin_univ, extDerivWithin_univ] at h
    simpa [f', L, e] using h
  have hae : (fun x ↦ ∑ i, f' i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)]
      fun x ↦ extDeriv ω (toLp 2 x) e := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).measurableSet).mono
      hdiv
  have hcf : ∀ i, ContinuousOn (f i) (Icc a b) := fun i ↦
    (continuous_apply i).comp_continuousOn
      ((ContinuousAlternatingMap.signedRemoveNth e).continuous.comp_continuousOn hc)
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅ countable_empty hcf
    (fun x hx ↦ hf' x hx.1) (hi.congr hae.symm)
  rw [integral_congr_ae hae] at h
  rw [h, boxBoundarySum_def]
  simp [f, G]

end TauCeti
