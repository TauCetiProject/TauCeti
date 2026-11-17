/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Connection
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# First jets of vector fields

Near the chart image of a point `x`, the local representative `TauCeti.FirstJetBundle.localRep` of
a vector field `V : (y : M) → TangentSpace I y` in the preferred tangent-bundle trivialization
agrees with the inverse-chart pullback
`VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)`
(`TauCeti.FirstJetBundle.localRep_eventuallyEq_mpullbackWithin_extChartAt_symm`).

Consequently, on a `C²` manifold, the derivative coordinate of the first jet
`TauCeti.FirstJetBundle.jet I E V x` is the derivative within `range I` of the inverse-chart
pullback (`TauCeti.FirstJetBundle.jet_snd_eq_fderivWithin_mpullbackWithin_extChartAt_symm`), and on
a boundaryless manifold it is the Fréchet derivative
(`TauCeti.FirstJetBundle.jet_snd_eq_fderiv_mpullbackWithin_extChartAt_symm`). At a zero `V x = 0`,
vanishing of the first jet is equivalent to vanishing of this linearization
(`TauCeti.FirstJetBundle.jet_eq_zero_iff_fderivWithin_mpullbackWithin_extChartAt_symm`,
`TauCeti.FirstJetBundle.jet_eq_zero_iff_fderiv_mpullbackWithin_extChartAt_symm`), and over a
complete field with a finite-dimensional model, to vanishing of `∇ V x` for any auxiliary covariant
derivative `∇` on the tangent bundle
(`FirstJetBundle.covariantDerivative_eq_zero_iff_fderivWithin_mpullbackWithin_extChartAt_symm`,
`FirstJetBundle.covariantDerivative_eq_zero_iff_fderiv_mpullbackWithin_extChartAt_symm`).

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17, §17.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 9.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

namespace TauCeti.FirstJetBundle

section OnceDifferentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Near the chart image of `x` within `range I`, the local representative of a vector field `V`
agrees with its inverse-chart pullback. -/
theorem localRep_eventuallyEq_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) :
    localRep I E V x =ᶠ[𝓝[range I] (extChartAt I x x)]
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) := by
  filter_upwards [VectorField.trivializationAt_snd_eventuallyEq_mpullbackWithin_extChartAt_symm V x]
    with z hz
  exact (localRep_apply I E V x z).trans hz

/-- At the chart centre `x`, `localRep` and the inverse-chart pullback of a vector field agree. -/
theorem localRep_extChartAt_self_eq_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) :
    localRep I E V x (extChartAt I x x) =
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
        (extChartAt I x x) :=
  (localRep_eventuallyEq_mpullbackWithin_extChartAt_symm V x).self_of_nhdsWithin
    (mem_range_self (chartAt H x x))

/-- At the chart centre `x`, `localRep` and the inverse-chart pullback of a vector field have the
same `HasFDerivWithinAt` within `range I`. -/
theorem hasFDerivWithinAt_localRep_iff_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) {L : E →L[𝕜] E} :
    HasFDerivWithinAt (localRep I E V x) L (range I) (extChartAt I x x) ↔
      HasFDerivWithinAt (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        L (range I) (extChartAt I x x) :=
  ⟨fun h ↦ h.congr_of_eventuallyEq
      (localRep_eventuallyEq_mpullbackWithin_extChartAt_symm V x).symm
      (localRep_extChartAt_self_eq_mpullbackWithin_extChartAt_symm V x).symm,
    fun h ↦ h.congr_of_eventuallyEq
      (localRep_eventuallyEq_mpullbackWithin_extChartAt_symm V x)
      (localRep_extChartAt_self_eq_mpullbackWithin_extChartAt_symm V x)⟩

/-- On a boundaryless manifold, `localRep` and the inverse-chart pullback of a vector field have
the same Fréchet derivative at the chart centre `x`. -/
theorem hasFDerivAt_localRep_iff_mpullbackWithin_extChartAt_symm [I.Boundaryless]
    (V : (y : M) → TangentSpace I y) (x : M) {L : E →L[𝕜] E} :
    HasFDerivAt (localRep I E V x) L (extChartAt I x x) ↔
      HasFDerivAt (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        L (extChartAt I x x) := by
  let f : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  have h := hasFDerivWithinAt_localRep_iff_mpullbackWithin_extChartAt_symm V x (L := L)
  -- Fix `f : E → E` so rewriting `I.range_eq_univ` leaves the `range I` argument inside `f` intact.
  change HasFDerivWithinAt (localRep I E V x) L (range I) (extChartAt I x x) ↔
    HasFDerivWithinAt f L (range I) (extChartAt I x x) at h
  rw [I.range_eq_univ, hasFDerivWithinAt_univ, hasFDerivWithinAt_univ] at h
  exact h

/-- At the chart centre `x`, `fderivWithin` of `localRep` agrees with `fderivWithin` of the
inverse-chart pullback of `V`. -/
theorem fderivWithin_localRep_eq_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) :
    fderivWithin 𝕜 (localRep I E V x) (range I) (extChartAt I x x) =
      fderivWithin 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (range I) (extChartAt I x x) :=
  (localRep_eventuallyEq_mpullbackWithin_extChartAt_symm V x).fderivWithin_eq
    (localRep_extChartAt_self_eq_mpullbackWithin_extChartAt_symm V x)

end OnceDifferentiable

section TwiceDifferentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The derivative coordinate of the first jet of a vector field `V` at `x` is the `fderivWithin`
of its inverse-chart pullback within `range I`. -/
theorem jet_snd_eq_fderivWithin_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) :
    (jet I E V x).2 =
      fderivWithin 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (range I) (extChartAt I x x) := by
  have : IsManifold I 1 M := .of_le one_le_two
  exact (jet_snd I E V x).trans (fderivWithin_localRep_eq_mpullbackWithin_extChartAt_symm V x)

/-- On a boundaryless `C²` manifold, the derivative coordinate of the first jet of a vector field
`V` at `x` is the Fréchet derivative of its inverse-chart pullback at the chart image of `x`. -/
theorem jet_snd_eq_fderiv_mpullbackWithin_extChartAt_symm [I.Boundaryless]
    (V : (y : M) → TangentSpace I y) (x : M) :
    (jet I E V x).2 =
      fderiv 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (extChartAt I x x) := by
  let f : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  have h := jet_snd_eq_fderivWithin_mpullbackWithin_extChartAt_symm V x
  -- Fix `f : E → E` so rewriting `I.range_eq_univ` leaves the `range I` argument inside `f` intact.
  change (jet I E V x).2 = fderivWithin 𝕜 f (range I) (extChartAt I x x) at h
  rwa [I.range_eq_univ, fderivWithin_univ] at h

/-- The first jet of a vector field `V` at `x` vanishes exactly when `V x = 0` and the derivative
within `range I` of its inverse-chart pullback vanishes at `extChartAt I x x`. -/
theorem jet_eq_zero_iff_fderivWithin_mpullbackWithin_extChartAt_symm
    (V : (y : M) → TangentSpace I y) (x : M) :
    jet I E V x = 0 ↔
      V x = 0 ∧
        fderivWithin 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
          (range I) (extChartAt I x x) = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [jet_eq_zero_iff, fderivWithin_localRep_eq_mpullbackWithin_extChartAt_symm]

/-- On a boundaryless `C²` manifold, the first jet of a vector field `V` at `x` vanishes exactly
when `V x = 0` and the Fréchet derivative of its inverse-chart pullback vanishes at
`extChartAt I x x`. -/
theorem jet_eq_zero_iff_fderiv_mpullbackWithin_extChartAt_symm [I.Boundaryless]
    (V : (y : M) → TangentSpace I y) (x : M) :
    jet I E V x = 0 ↔
      V x = 0 ∧
        fderiv 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
          (extChartAt I x x) = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [jet_eq_zero_iff, ← jet_snd, jet_snd_eq_fderiv_mpullbackWithin_extChartAt_symm]

/-- At a zero of a differentiable vector field on a finite-dimensional `C²` manifold over a complete
field, vanishing of any auxiliary covariant derivative `cov` on `TM` is equivalent to vanishing of
the within-range derivative of the inverse-chart pullback. -/
theorem covariantDerivative_eq_zero_iff_fderivWithin_mpullbackWithin_extChartAt_symm
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {cov : (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y →L[𝕜] TangentSpace I y)}
    {U : Set M} {x : M} (hcov : IsCovariantDerivativeOn E cov U) (hx : x ∈ U)
    {V : (y : M) → TangentSpace I y}
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x)
    (hV0 : V x = 0) :
    cov V x = 0 ↔
      fderivWithin 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (range I) (extChartAt I x x) = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [covariantDerivative_eq_zero_iff_fderivWithin_localRep_eq_zero hcov hx hV hV0,
    fderivWithin_localRep_eq_mpullbackWithin_extChartAt_symm]

/-- Boundaryless version of
`FirstJetBundle.covariantDerivative_eq_zero_iff_fderivWithin_mpullbackWithin_extChartAt_symm`. -/
theorem covariantDerivative_eq_zero_iff_fderiv_mpullbackWithin_extChartAt_symm
    [I.Boundaryless] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {cov : (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y →L[𝕜] TangentSpace I y)}
    {U : Set M} {x : M} (hcov : IsCovariantDerivativeOn E cov U) (hx : x ∈ U)
    {V : (y : M) → TangentSpace I y}
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x)
    (hV0 : V x = 0) :
    cov V x = 0 ↔
      fderiv 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (extChartAt I x x) = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [covariantDerivative_eq_zero_iff_fderivWithin_localRep_eq_zero hcov hx hV hV0, ← jet_snd,
    jet_snd_eq_fderiv_mpullbackWithin_extChartAt_symm]

end TwiceDifferentiable

end TauCeti.FirstJetBundle
