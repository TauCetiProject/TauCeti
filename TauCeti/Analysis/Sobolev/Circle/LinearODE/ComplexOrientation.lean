/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
import TauCeti.LinearAlgebra.Complex.Module

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
the complex structures of its kernel and cokernel. This file shows that the two agree
(`TauCeti.CircleSobolev.isComplexPositiveDetLine_detLineLoopOperatorEquiv_symm`): the
propagator, hence `1 - P`, is complex linear, the normalized generator of a complex-linear
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

## Main definitions

* `TauCeti.CircleSobolev.complexLoopOperator`: `L_S` as a complex-linear operator, for a loop of
  complex-linear maps.

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

/-! ### Complex linearity -/

/-- Multiplication by a loop of complex-linear maps commutes with multiplication by `I`. -/
theorem mulLoop_I_smul (hs : 1 / 2 < s) (hS : ∀ t v, S t (I • v) = I • S t v)
    (a : CircleSobolev s E) : mulLoop T hs S (I • a) = I • mulLoop T hs S a := by
  rw [mulLoop_apply, mulLoop_apply, map_smul (toContinuousMap T hs), ← map_smul (ofContinuousMap T)]
  refine congrArg (ofContinuousMap T) (ContinuousMap.ext fun t ↦ ?_)
  simp [hS]

/-- The loop operator of a loop of complex-linear maps commutes with multiplication by `I`. -/
theorem loopOperator_I_smul (hS : ∀ t v, S t (I • v) = I • S t v) (a : CircleSobolev 1 E) :
    loopOperator T S (I • a) = I • loopOperator T S a := by
  rw [loopOperator_apply, loopOperator_apply, map_smul, mulLoop_I_smul T _ hS, smul_sub]

/-- **The loop operator of a loop of complex-linear maps is complex linear.** This is
`ζ ↦ ζ' - S ζ` as a complex-linear operator `H¹(E) → H⁰(E)`. It is given by its fields, rather
than by `ContinuousLinearMap.complexOfMapISmul`, so that its underlying real operator is
`TauCeti.CircleSobolev.loopOperator T S` by definition, and complex orientations of its
determinant line are elements of the determinant line of `L_S`. -/
@[expose]
def complexLoopOperator (hS : ∀ t v, S t (I • v) = I • S t v) :
    CircleSobolev 1 E →L[ℂ] CircleSobolev 0 E where
  toFun := loopOperator T S
  map_add' := map_add _
  map_smul' c v := by
    have := ((loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).complexOfMapISmul
      (loopOperator_I_smul T hS)).map_smul c v
    rwa [LinearMap.coe_complexOfMapISmul] at this
  cont := (loopOperator T S).continuous

@[simp]
theorem complexLoopOperator_apply (hS : ∀ t v, S t (I • v) = I • S t v) (a : CircleSobolev 1 E) :
    complexLoopOperator T hS a = loopOperator T S a :=
  (rfl)

/-- The real operator underlying `TauCeti.CircleSobolev.complexLoopOperator` is the loop
operator. -/
@[simp]
theorem restrictScalars_complexLoopOperator (hS : ∀ t v, S t (I • v) = I • S t v) :
    (complexLoopOperator T hS).restrictScalars ℝ = loopOperator T S :=
  (rfl)

omit hT in
/-- The propagator of a loop of complex-linear maps is complex linear. -/
private theorem dysonSeriesLeft_apply_I_smul (hS : ∀ t v, S t (I • v) = I • S t v) (t : ℝ) (v : E) :
    dysonSeriesLeft (fun t : ℝ ↦ S t) t (I • v) = I • dysonSeriesLeft (fun t : ℝ ↦ S t) t v := by
  have h := commute_dysonSeriesLeft (a := I • (1 : E →L[ℝ] E)) (AddCircle.continuous_comp_coe S)
    (fun r ↦ ContinuousLinearMap.ext fun w ↦ by simp [hS]) t
  simpa using (ContinuousLinearMap.ext_iff.1 h.eq v).symm

omit hT in
/-- The inverse `dysonSeries (-S)` of the propagator of a loop of complex-linear maps is complex
linear. -/
private theorem dysonSeries_neg_apply_I_smul (hS : ∀ t v, S t (I • v) = I • S t v) (t : ℝ) (v : E) :
    dysonSeries (-fun t : ℝ ↦ S t) t (I • v) = I • dysonSeries (-fun t : ℝ ↦ S t) t v := by
  have h := commute_dysonSeries_neg (a := I • (1 : E →L[ℝ] E)) (AddCircle.continuous_comp_coe S)
    (fun r ↦ ContinuousLinearMap.ext fun w ↦ by simp [hS]) t
  simpa using (ContinuousLinearMap.ext_iff.1 h.eq v).symm

/-! ### The complex orientation -/

omit hT in
/-- `1 - Ψ(T)` commutes with multiplication by `I`. -/
private theorem one_sub_apply_I_smul (hS : ∀ t v, S t (I • v) = I • S t v) (v : E) :
    (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) (I • v) =
      I • (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) v := by
  simp [dysonSeriesLeft_apply_I_smul T hS, smul_sub]

/-- The inverse of evaluation at `0` on the kernels commutes with multiplication by `I`. -/
private theorem kerLoopOperatorEquiv_symm_I_smul (hS : ∀ t v, S t (I • v) = I • S t v)
    (x y : ker (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)))
    (hxy : (x : E) = I • (y : E)) :
    ((kerLoopOperatorEquiv T S).symm x : CircleSobolev 1 E) =
      I • ((kerLoopOperatorEquiv T S).symm y : CircleSobolev 1 E) := by
  refine toContinuousMap_injective T (show (1 : ℝ) / 2 < 1 by norm_num) ?_
  refine AddCircle.continuousMap_ext_coe fun t ↦ ?_
  rw [map_smul, ContinuousMap.smul_apply, toContinuousMap_kerLoopOperatorEquiv_symm_apply,
    toContinuousMap_kerLoopOperatorEquiv_symm_apply, hxy, dysonSeriesLeft_apply_I_smul T hS]

/-- The inverse of the endpoint map on the cokernels commutes with multiplication by `I`. -/
private theorem quotientRangeLoopOperatorEquiv_symm_I_smul
    (hS : ∀ t v, S t (I • v) = I • S t v) (x : E) (y : CircleSobolev 0 E)
    (hxy : (quotientRangeLoopOperatorEquiv T S).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk y) :
    (quotientRangeLoopOperatorEquiv T S).symm (Submodule.Quotient.mk (I • x)) =
      Submodule.Quotient.mk (I • y) := by
  -- Represent the class of `y` by a continuous loop `f`.
  obtain ⟨f, hf⟩ := exists_mk_ofContinuousMap_eq T S (Submodule.Quotient.mk y)
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).1 hf
  have hIf : (Submodule.Quotient.mk (ofContinuousMap T (I • f)) : CircleSobolev 0 E ⧸
      range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) =
      Submodule.Quotient.mk (I • y) := by
    rw [Submodule.Quotient.eq, map_smul, ← smul_sub, ← hb]
    exact ⟨I • b, loopOperator_I_smul T hS b⟩
  rw [← hIf, LinearEquiv.symm_apply_eq, quotientRangeLoopOperatorEquiv_mk]
  rw [LinearEquiv.symm_apply_eq, ← hf, quotientRangeLoopOperatorEquiv_mk] at hxy
  -- Both sides are `I` times the classes in `hxy`, and `1 - Ψ(T)` commutes with `I`.
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq _).1 hxy
  refine (Submodule.Quotient.eq _).2 ⟨I • c, ?_⟩
  rw [one_sub_apply_I_smul T hS, hc, smul_sub]
  congr 1
  simp only [ContinuousMap.smul_apply, dysonSeries_neg_apply_I_smul T hS,
    intervalIntegral.integral_smul, dysonSeriesLeft_apply_I_smul T hS]

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
  -- `1 - Ψ(T)` as a complex-linear endomorphism, whose real map is `1 - Ψ(T)` by definition.
  let A : E →ₗ[ℂ] E :=
    { toFun v := (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) v
      map_add' x y := map_add _ x y
      map_smul' c v := by
        have := ((1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).complexOfMapISmul
          (one_sub_apply_I_smul T hS)).map_smul c v
        rw [LinearMap.coe_complexOfMapISmul] at this
        exact this }
  rw [detLineLoopOperatorEquiv_def, LinearMap.detLineCongrKerCoker_symm]
  exact (LinearMap.isComplexPositiveDetLine_detLineEndGenerator A).detLineCongrKerCoker _ _
    (kerLoopOperatorEquiv_symm_I_smul T hS) (quotientRangeLoopOperatorEquiv_symm_I_smul T hS)

/-! ### Transport from a complex-linear reference -/

/-- **Transport from a complex-linear reference follows the return maps.** Let `M` be a path of
coefficient loops, continuous on `[a, b]`, with `M a` a loop of complex-linear maps, and let `z`
be a nonzero complex positive element of the determinant line of `L_{M a}`. Orientation transport
along the loop operators `L_{M t}` carries the orientation of `z`, the complex orientation of
`L_{M a}`, to the orientation of the normalized generator of `1 - Ψ_b(T)` transported to the
determinant line of `L_{M b}`. -/
theorem detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hS : ∀ t v, M a t (I • v) = I • M a t v)
    {z : (loopOperator T (M a) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine}
    (hz : (complexLoopOperator T hS :
      CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E).IsComplexPositiveDetLine z)
    (hz0 : z ≠ 0) :
    detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t)) (rayOfNeZero ℝ z hz0) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) :
          (detLineLoopOperatorEquiv T (M b)).symm _ ≠ 0) := by
  have : FiniteDimensional ℝ (CircleSobolev 0 E ⧸ range
      ((complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E).restrictScalars ℝ)) :=
    (isFredholm_loopOperator T (M a)).finite_coker
  have : FiniteDimensional ℝ (CircleSobolev 0 E ⧸
      range (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E)) :=
    Module.Finite.equiv ((complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ]
      CircleSobolev 0 E).cokerRestrictScalarsEquiv ℝ)
  have : FiniteDimensional ℂ (CircleSobolev 0 E ⧸
      range (complexLoopOperator T hS : CircleSobolev 1 E →ₗ[ℂ] CircleSobolev 0 E)) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
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
    (hz0 : z ≠ 0) (hb : Function.Bijective (loopOperator T (M b)))
    {x : (loopOperator T (M b) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t)) (rayOfNeZero ℝ z hz0)) :
    SignType.sign
        ((loopOperator T (M b) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective
          hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) := by
  set A := 1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E)
  rw [detLineOrientationTransport_rayOfNeZero_of_isComplexPositiveDetLine T hM hS hz hz0] at hxz
  -- `x` is a positive multiple of the transported normalized generator of `A`.
  have hy : (detLineLoopOperatorEquiv T (M b)).symm A.detLineEndGenerator ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero A)
  obtain ⟨r, hr, hrx⟩ := SameRay.exists_pos_left (R := ℝ)
    (M := (loopOperator T (M b) : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine)
    ((ray_eq_iff hx hy).1 hxz) hx hy
  -- `A` is injective, so the canonical trivialization takes the value `1` at its generator.
  have hA : Function.Injective A := (injective_loopOperator_iff T (M b)).1 hb.1
  have hdet : LinearMap.det A ≠ 0 := fun h ↦
    LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 hA)
  have hgen : LinearMap.detLineEndEquiv A A.detLineEndGenerator = 1 := by
    rw [LinearMap.detLineEndEquiv_detLineEndGenerator,
      LinearMap.finrank_ker_eq_zero_of_injective hA, zero_mul, pow_zero]
  have hx' : x = r⁻¹ • (detLineLoopOperatorEquiv T (M b)).symm A.detLineEndGenerator := by
    rw [← hrx, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hl : LinearMap.detLineEndEquiv A (detLineLoopOperatorEquiv T (M b) x) = r⁻¹ := by
    rw [hx', map_smul, map_smul, LinearEquiv.apply_symm_apply, hgen, smul_eq_mul, mul_one]
  -- By `detLineEndEquiv_detLineLoopOperatorEquiv`, `r⁻¹ = (det A)⁻¹ * bij x`.
  have hbx : (loopOperator T (M b) :
      CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective hb x =
        LinearMap.det A * r⁻¹ := by
    have key := detLineEndEquiv_detLineLoopOperatorEquiv T (M b) hb x
    rw [hl, eq_comm, inv_mul_eq_iff_eq_mul₀ hdet] at key
    exact key
  rw [hbx, sign_mul, sign_pos (inv_pos.2 hr), mul_one]

end CircleSobolev

end TauCeti
