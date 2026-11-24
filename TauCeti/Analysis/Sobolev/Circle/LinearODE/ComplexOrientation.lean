/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap

/-!
# The complex orientation of a loop operator with complex-linear coefficients

Let `E` be a finite-dimensional complex normed space and `S` a continuous loop of real-linear
maps of `E`, with loop operator `L_S ζ = ζ' - S ζ`, `H¹(E) → H⁰(E)`
(`TauCeti.CircleSobolev.loopOperator`), propagator `Ψ` of `w' = S w` and return map `P = Ψ(T)`.
The determinant line of `L_S` is identified with that of `1 - P`
(`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`), and transporting the normalized generator of
the determinant line of `1 - P` (`LinearMap.detLineEndGenerator`) along this identification gives
a continuous orientation of the determinant line bundle over all loops
(`TauCeti.CircleSobolev.isDetLineCoherentOn_detLineLoopOperatorEquiv_symm`).

When every `S t` is complex linear, `L_S` is a complex-linear operator
(`TauCeti.CircleSobolev.complexLoopOperator`), and its determinant line carries a second,
canonical orientation: the complex orientation (`LinearMap.IsComplexPositiveDetLine`), given by
the complex structures of its kernel and cokernel. The two agree
(`TauCeti.CircleSobolev.isComplexPositiveDetLine_detLineLoopOperatorEquiv_symm`, the case of
`complexLoopOperator` in
`TauCeti.CircleSobolev.isComplexPositiveDetLine_detLineCongrOfEq_detLineLoopOperatorEquiv_symm`):
the propagator, hence `1 - P`, is complex linear, the normalized generator of a complex-linear
endomorphism is complex positive (`LinearMap.isComplexPositiveDetLine_detLineEndGenerator`), and
evaluation at `0` on kernels and the endpoint map on cokernels commute with multiplication by `I`
(`LinearMap.IsComplexPositiveDetLine.detLineCongrKerCoker`).

Consequently, the orientation of `L_S` obtained by transporting the complex orientation of a
complex-linear reference `L_{S₀}` along a path of loops from `S₀` to `S` is the transported
normalized generator of `1 - P`
(`TauCeti.CircleSobolev.detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine`).
When `L_S` is bijective, that is `det (1 - P) ≠ 0`, it is the orientation given by bijectivity
exactly when `det (1 - P) > 0`
(`TauCeti.CircleSobolev.sign_detLineEquivOfBijective_eq_sign_det`). This is the comparison behind
the absolute determinant signs `sgn det (1 - P)` of the twisted normal operators of orbit tori in
Taubes's count of pseudoholomorphic tori: on maps periodic along the circle factor, such an
operator reduces to a loop operator, and its complex-linear reference `∂s + J₀ ∂t` to the loop
operator of a loop of complex-linear maps. The
same results apply to the antiperiodic operators: in the periodic gauge they are the loop operators
of `TauCeti.CircleSobolev.antiperiodicGaugeLoop`, a loop of complex-linear maps when `S` is one
(`TauCeti.CircleSobolev.antiperiodicGaugeLoop_apply_I_smul`), with return map `-P`.

## Main results

* `TauCeti.CircleSobolev.isComplexPositiveDetLine_detLineLoopOperatorEquiv_symm`: for a loop of
  complex-linear maps, the transported normalized generator of `1 - P` is complex positive.
* `TauCeti.CircleSobolev.detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine`:
  transport of the complex orientation from a complex-linear loop follows the return maps.
* `TauCeti.CircleSobolev.sign_detLineEquivOfBijective_eq_sign_det`: at a nondegenerate endpoint,
  the transported complex orientation reads as `sgn det (1 - P)` in the trivialization given by
  bijectivity.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (the determinant signs of the twisted normal operators of tori).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (the complex orientation of determinant
  lines of complex-linear Fredholm operators).
-/

public section

noncomputable section

open LinearMap (ker range)
open Complex (I)
open Set (uIcc)

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : ℝ) [hT : Fact (0 < T)] [FiniteDimensional ℂ E] {S : C(AddCircle T, E →L[ℝ] E)}

/-- A finite-dimensional complex space is complete, as needed for continuous representatives and
for the propagator. -/
local instance instCompleteSpaceComplexOrientation : CompleteSpace E :=
  FiniteDimensional.completeSpace ℂ E

/-! ### The complex orientation -/

/-- **The complex orientation of a loop operator with complex-linear coefficients.** If every
`S t` is complex linear, the normalized generator of the determinant line of `1 - Ψ(T)`,
transported to the determinant line of `L_S ζ = ζ' - S ζ` along
`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`, is complex positive for the complex-linear
operator `L_S` (`TauCeti.CircleSobolev.complexLoopOperator`). So on loops of complex-linear maps
the coherent orientation of the loop operators by the return maps is their complex
orientation. -/
theorem isComplexPositiveDetLine_detLineLoopOperatorEquiv_symm
    (hS : ∀ t v, S t (I • v) = I • S t v) :
    (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E).IsComplexPositiveDetLine
      ((detLineLoopOperatorEquiv T S).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator) := by
  -- The general statement for any complex-linear `A` over `L_S`, at `A = complexLoopOperator`.
  have h := isComplexPositiveDetLine_detLineCongrOfEq_detLineLoopOperatorEquiv_symm hS
    (A := (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E)) rfl
  exact (congrArg (fun x ↦ (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ]
    CircleSobolev 0 E).IsComplexPositiveDetLine x) (DFunLike.congr_fun
      (LinearMap.detLineCongrOfEq_rfl
        (f := (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E))) _)).mp h

/-- The complex cokernel of the complex-linear loop operator is finite-dimensional, since the
real cokernel of the Fredholm operator `L_S` is. -/
instance finiteDimensional_coker_complexLoopOperator (hS : ∀ t v, S t (I • v) = I • S t v) :
    FiniteDimensional ℂ (CircleSobolev 0 E ⧸
      range (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E)) :=
  (isFredholm_loopOperator T S).finiteDimensional_quotient_range_of_restrictScalars_eq <| by
    rw [← restrictScalars_complexLoopOperator T hS, ContinuousLinearMap.coe_restrictScalars]

/-! ### Transport from a complex-linear reference -/

/-- **Transport from a complex-linear reference follows the return maps.** Let `M` be a path of
coefficient loops, continuous on `[a, b]`, with `M a` a loop of complex-linear maps, and let `z`
be a complex positive element of the determinant line of `L_{M a}`. Orientation transport
along the loop operators `L_{M t}` carries the orientation of `z`, the complex orientation of
`L_{M a}`, to the orientation of the normalized generator of `1 - Ψ_b(T)` transported to the
determinant line of `L_{M b}`. -/
theorem detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hS : ∀ t v, M a t (I • v) = I • M a t v)
    {z : (loopOperator T (M a) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine}
    (hz : (complexLoopOperator T hS :
      CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E).IsComplexPositiveDetLine z) :
    detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t)) (rayOfNeZero ℝ z hz.ne_zero) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) :
          (detLineLoopOperatorEquiv T (M b)).symm _ ≠ 0) := by
  -- The complex orientation at `a` is the orientation of the transported generator.
  obtain ⟨c, hc, rfl⟩ :=
    (isComplexPositiveDetLine_detLineLoopOperatorEquiv_symm T hS).exists_pos_smul_eq hz
  rw [← detLineOrientationTransport_rayOfNeZero_detLineLoopOperatorEquiv_symm T hM]
  congr 1
  exact ray_pos_smul _ hc _

/-- **The absolute sign at a nondegenerate endpoint.** In the situation of
`TauCeti.CircleSobolev.detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine`, let
`L_{M b}` be bijective, equivalently `det (1 - Ψ_b(T)) ≠ 0`. Every element `x` of the determinant
line of `L_{M b}` in the orientation transported from the complex orientation of `L_{M a}` reads,
in the trivialization given by bijectivity (`LinearMap.detLineEquivOfBijective`), with the sign of
`det (1 - Ψ_b(T))`. So the transported complex orientation is the orientation given by
bijectivity exactly when `det (1 - Ψ_b(T)) > 0`. -/
theorem sign_detLineEquivOfBijective_eq_sign_det
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hS : ∀ t v, M a t (I • v) = I • M a t v)
    {z : (loopOperator T (M a) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine}
    (hz : (complexLoopOperator T hS :
      CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E).IsComplexPositiveDetLine z)
    (hb : Function.Bijective (loopOperator T (M b)))
    {x : (loopOperator T (M b) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t)) (rayOfNeZero ℝ z hz.ne_zero)) :
    SignType.sign
        ((loopOperator T (M b) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective
          hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) := by
  rw [detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine T hM hS hz] at hxz
  exact sign_detLineEquivOfBijective_eq_sign_det_of_sameRay T (M b) hb hx
    ((ray_eq_iff hx _).1 hxz)

end CircleSobolev

end TauCeti
