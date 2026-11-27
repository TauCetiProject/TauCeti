/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConleyZehnder
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.Module.Exp

/-!
# The quadratic Hamiltonian `a ‖z‖²` and the index of the origin

Let `G` be a complex inner product space of complex dimension `n`, a real symplectic vector space
for the form `ω = Im ⟪·, ·⟫_ℂ` (`TauCeti.imInnerSymplecticForm`); for `G = ℂⁿ` this is the
standard symplectic space `(ℝ²ⁿ, Σ dqⱼ ∧ dpⱼ)`. With the convention `ι_{X_H} ω = dH`, the
quadratic Hamiltonian `H(z) = a ‖z‖²` has the linear Hamiltonian vector field `X_H(z) = -2 a i z`
(`TauCeti.hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq`), so its evolution from time
`s` to time `t` multiplies every vector by the unit complex number `e^{-2 i a (t - s)}`
(`TauCeti.timeDependentHamiltonianFlow_mul_norm_sq`). Hence:

* **One-periodic orbits.** A point `z` is fixed by the time-one map exactly when `z = 0` or
  `a ∈ π ℤ` (`TauCeti.isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff`). For `a ∉ π ℤ` the
  only one-periodic orbit is the constant orbit at the origin
  (`TauCeti.fixedPoints_timeDependentHamiltonianFlow_mul_norm_sq_eq_singleton`), while for
  `a ∈ π ℤ` every point lies on a one-periodic orbit
  (`TauCeti.fixedPoints_timeDependentHamiltonianFlow_mul_norm_sq_eq_univ`).
* **Nondegeneracy.** The time-one map is the complex scalar `e^{-2 i a}`, so on a nonzero space the
  origin is a nondegenerate fixed point exactly when `a ∉ π ℤ`
  (`TauCeti.isNondegenerateFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_zero_iff`).
* **The index.** The linearized flow along the constant orbit at `0` is the path
  `t ↦ e^{-2 i a t}`, `t ∈ [0, 1]`. In the symplectic basis `(i e, e)` of an orthonormal basis `e`
  (`OrthonormalBasis.imInnerSymplecticBasis`), in which `ω` has the matrix `J`, its matrices are
  the realified diagonal unitary matrices `diag (e^{2 i a t})`, the conjugate, since multiplication
  by `i` sends `i eⱼ` to `-eⱼ`. Their Conley–Zehnder index is given by
  `TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal`. So the
  Conley–Zehnder index of the orbit (`TauCeti.SymplecticForm.orbitConleyZehnderIndex`) is
  `-n (⌊a / π⌋ + ⌈a / π⌉)` (`TauCeti.orbitConleyZehnderIndex_mul_norm_sq`), that is
  `-n (2 k + 1)` for `k π < a < (k + 1) π`
  (`TauCeti.orbitConleyZehnderIndex_mul_norm_sq_of_mem_Ioo`): it is constant between consecutive
  multiples of `π` and drops by `2 n` across each of them.
* **The index in the coordinates of `ℂⁿ`.** In the real basis `(e, i e)`, the real and imaginary
  parts of the coordinates, `ω` has the matrix `-J`
  (`OrthonormalBasis.toMatrix_reindex_sumComm_imInnerSymplecticForm`) and the matrices of the
  linearized flow are the realified `diag (e^{-2 i a t})` themselves. Their index is
  `n (⌊a / π⌋ + ⌈a / π⌉)`
  (`TauCeti.conleyZehnderIndex_eq_of_toMatrix_fderiv_timeDependentHamiltonianFlow_mul_norm_sq`).
  This is the convention in which a nondegenerate critical point of a small Hamiltonian has index
  `n - ind` (`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`), the
  grading convention `CZ = n - ind` of Hamiltonian Floer homology, and in it the index of the
  origin rises by `2 n` each time the slope crosses a multiple of `π`.

For small `a > 0` the origin is a nondegenerate minimum of `H`, and the two values `-n` and `n`
are the two conventions `ind - n` and `n - ind` of
`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_sigNeg_sub` and
`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`. For `a = 1 / 2`,
the harmonic oscillator `(‖q‖² + ‖p‖²) / 2`, the time-one map is multiplication by `e^{-i}`,
whose only fixed point is the nondegenerate origin.

These are the Hamiltonians that compute the symplectic homology of the ball. The unit ball
`D²ⁿ ⊆ ℂⁿ` is a Liouville domain whose completion is `ℂⁿ`, with radial coordinate `‖z‖²` outside
the ball (`TauCeti.liouvilleRadialCoordinate_closedBall`), so `a ‖z‖²` is linear at infinity with
slope `a` (`TauCeti.isLinearAtInfinity_mul_norm_sq`), and the closed Reeb orbits of the boundary
sphere, the Hopf circles and their multiples, have the periods `k π`. Symplectic homology is the
direct limit over the slope: for a slope outside `π ℤ` the only generator is the origin, and as the
slope grows its degree leaves every bounded window, which is why `SH_*(D²ⁿ) = 0`.

## Main results

* `TauCeti.hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq`: `X_{a ‖z‖²}(z) = -2 a i z`.
* `TauCeti.timeDependentHamiltonianFlow_mul_norm_sq`: its evolution is `z ↦ e^{-2 i a (t - s)} z`,
  with derivative `TauCeti.fderiv_timeDependentHamiltonianFlow_mul_norm_sq`.
* `TauCeti.isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff`: the fixed points of the
  evolution.
* `TauCeti.isNondegenerateFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_zero_iff`: the origin
  is nondegenerate exactly when `a (t - s) ∉ π ℤ`.
* `TauCeti.orbitConleyZehnderIndex_mul_norm_sq`: the Conley–Zehnder index of the origin is
  `-n (⌊a / π⌋ + ⌈a / π⌉)`.
* `TauCeti.conleyZehnderIndex_eq_of_toMatrix_fderiv_timeDependentHamiltonianFlow_mul_norm_sq`:
  in the coordinates of `ℂⁿ` it is `n (⌊a / π⌋ + ⌈a / π⌉)`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (the symplectic homology of the ball).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the Conley–Zehnder index).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3 (the grading of Floer homology).
-/

public section

noncomputable section

open Complex Function Matrix Module
open scoped InnerProductSpace NNReal Manifold

namespace TauCeti

/- The real inner product `Re ⟪·, ·⟫_ℂ` of a complex inner product space is not a global instance
in Mathlib; it is used here to differentiate `‖z‖²`. -/
attribute [local instance] InnerProductSpace.complexToReal

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

/-! ### The vector field and the evolution -/

/-- The Hamiltonian vector field of `a ‖z‖²` is `-2 a` times multiplication by `i`, as a
real-linear map. -/
private theorem hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq_eq_smul (a : ℝ) :
    (imInnerSymplecticForm G).hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) =
      ⇑((-(2 * a)) •
        (AlmostComplexStructure.ofComplexModule G).toLinearMap.toContinuousLinearMap) := by
  have hg := (imInnerSymplecticForm G).apply_ofComplexModule_eq_inner
    fun v w ↦ imInnerSymplecticForm_apply v w
  have h := SymplecticForm.hamiltonianVectorField_div_two_mul_norm_sq hg (2 * a)
  have hH : (fun y : G ↦ 2 * a / 2 * ‖y‖ ^ 2) = fun y ↦ a * ‖y‖ ^ 2 := by
    funext y
    ring
  rwa [hH] at h

/-- **The Hamiltonian vector field of `a ‖z‖²`.** For the symplectic form `Im ⟪·, ·⟫_ℂ` and the
convention `ι_{X_H} ω = dH`, the quadratic Hamiltonian `a ‖z‖²` has the linear vector field
`X(z) = -2 a i z`, which turns every complex line clockwise when `a > 0`. -/
theorem hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq (a : ℝ) :
    (imInnerSymplecticForm G).hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) =
      fun z ↦ ((-2 * a : ℝ) * I : ℂ) • z := by
  rw [hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq_eq_smul]
  funext z
  simp [AlmostComplexStructure.ofComplexModule_apply, mul_smul, ← Complex.coe_smul]

/-- The time suspension of the Hamiltonian vector field of `a ‖z‖²` is Lipschitz with constant
`2 |a|`, so its evolution is defined for all times. -/
theorem lipschitzWith_timeDependentHamiltonianSuspension_mul_norm_sq (a : ℝ) :
    LipschitzWith (2 * ‖a‖₊)
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2) := by
  refine (imInnerSymplecticForm G).lipschitzWith_timeDependentHamiltonianSuspension_const _ ?_
  rw [hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq]
  convert lipschitzWith_smul (β := G) ((-2 * a : ℝ) * I : ℂ) using 1
  ext
  simp

/-- **The evolution of `a ‖z‖²` is a rotation.** For the symplectic form `Im ⟪·, ·⟫_ℂ`, the
Hamiltonian evolution of `a ‖z‖²` from time `s` to time `t` is multiplication by the unit complex
number `e^{-2 i a (t - s)}`. -/
@[simp]
theorem timeDependentHamiltonianFlow_mul_norm_sq (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    (s t : ℝ) (z : G) :
    (imInnerSymplecticForm G).timeDependentHamiltonianFlow (fun _ y ↦ a * ‖y‖ ^ 2) hX s t z =
      exp ((-2 * a * (t - s) : ℝ) * I) • z := by
  have hy (r : ℝ) : HasDerivAt (fun r : ℝ ↦ exp ((-2 * a * (r - s) : ℝ) * I) • z)
      ((imInnerSymplecticForm G).hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2)
        (exp ((-2 * a * (r - s) : ℝ) * I) • z)) r := by
    rw [hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq]
    have hθ : HasDerivAt (fun r : ℝ ↦ ((-2 * a * (r - s) : ℝ) : ℂ) * I)
        (((-2 * a : ℝ) : ℂ) * I) r := by
      have := (((hasDerivAt_id r).sub_const s).const_mul (-2 * a)).ofReal_comp.mul_const I
      simpa using this
    convert hθ.cexp.smul_const z using 1
    dsimp only
    rw [smul_smul, mul_comm]
  have h := (imInnerSymplecticForm G).eq_timeDependentHamiltonianFlow _ hX hy s t
  have hs : exp ((-2 * a * (s - s) : ℝ) * I) • z = z := by simp
  rw [hs] at h
  exact h.symm

/-- The evolution of `a ‖z‖²` from time `s` to time `t` is the real-linear map of multiplication
by `e^{-2 i a (t - s)}`. -/
private theorem timeDependentHamiltonianFlow_mul_norm_sq_eq_lsmul (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    (s t : ℝ) :
    (imInnerSymplecticForm G).timeDependentHamiltonianFlow (fun _ y ↦ a * ‖y‖ ^ 2) hX s t =
      ⇑(ContinuousLinearMap.lsmul ℝ ℂ (exp ((-2 * a * (t - s) : ℝ) * I)) : G →L[ℝ] G) := by
  funext z
  rw [timeDependentHamiltonianFlow_mul_norm_sq, ContinuousLinearMap.lsmul_apply]

/-- **The linearized evolution of `a ‖z‖²`.** At every point, the derivative of the evolution of
`a ‖z‖²` from time `s` to time `t` is multiplication by `e^{-2 i a (t - s)}`. -/
theorem fderiv_timeDependentHamiltonianFlow_mul_norm_sq (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    (s t : ℝ) (z : G) :
    fderiv ℝ ((imInnerSymplecticForm G).timeDependentHamiltonianFlow
        (fun _ y ↦ a * ‖y‖ ^ 2) hX s t) z =
      ContinuousLinearMap.lsmul ℝ ℂ (exp ((-2 * a * (t - s) : ℝ) * I)) := by
  rw [timeDependentHamiltonianFlow_mul_norm_sq_eq_lsmul, ContinuousLinearMap.fderiv]

/-! ### One-periodic orbits and their nondegeneracy -/

/-- **The fixed points of the evolution of `a ‖z‖²`.** A point `z` is fixed by the evolution of
`a ‖z‖²` from time `s` to time `t` exactly when `z = 0` or `a (t - s)` is a multiple of `π`. -/
theorem isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    (s t : ℝ) {z : G} :
    IsFixedPt ((imInnerSymplecticForm G).timeDependentHamiltonianFlow
        (fun _ y ↦ a * ‖y‖ ^ 2) hX s t) z ↔
      z = 0 ∨ ∃ k : ℤ, a * (t - s) = k * Real.pi := by
  set θ : ℝ := -2 * a * (t - s)
  have hsub : exp (θ * I) • z - z = (exp (θ * I) - 1) • z := by rw [sub_smul, one_smul]
  rw [IsFixedPt, timeDependentHamiltonianFlow_mul_norm_sq, ← sub_eq_zero, hsub, smul_eq_zero,
    sub_eq_zero, Complex.exp_eq_one_iff, or_comm]
  -- `e^{θ i} = 1` exactly when `θ = 2 π n`, and `θ = -2 a (t - s)`.
  refine or_congr_right ⟨fun ⟨n, hn⟩ ↦ ⟨-n, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨-k, ?_⟩⟩
  · have hn' : ((θ : ℂ) - 2 * n * Real.pi) * I = 0 := by rw [sub_mul, hn]; ring
    have h := sub_eq_zero.1 ((mul_eq_zero.1 hn').resolve_right I_ne_zero)
    have hθ : θ = 2 * n * Real.pi := by exact_mod_cast h
    push_cast
    linarith
  · have hk' : (a : ℂ) * ((t : ℂ) - s) = k * Real.pi := by exact_mod_cast hk
    simp only [θ]
    push_cast
    linear_combination (-2 * I) * hk'

/-- **The only one-periodic orbit is the origin.** If `a (t - s)` is not a multiple of `π`, the
evolution of `a ‖z‖²` from time `s` to time `t` fixes only the origin. -/
theorem fixedPoints_timeDependentHamiltonianFlow_mul_norm_sq_eq_singleton {a : ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    {s t : ℝ} (h : ∀ k : ℤ, a * (t - s) ≠ k * Real.pi) :
    fixedPoints ((imInnerSymplecticForm G).timeDependentHamiltonianFlow
      (fun _ y ↦ a * ‖y‖ ^ 2) hX s t) = {0} := by
  ext z
  rw [mem_fixedPoints, isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff,
    Set.mem_singleton_iff]
  exact or_iff_left fun ⟨k, hk⟩ ↦ h k hk

/-- **At a slope in `π ℤ` every orbit is periodic.** If `a (t - s)` is a multiple of `π`, the
evolution of `a ‖z‖²` from time `s` to time `t` is the identity, and fixes every point. -/
theorem fixedPoints_timeDependentHamiltonianFlow_mul_norm_sq_eq_univ {a : ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    {s t : ℝ} (h : ∃ k : ℤ, a * (t - s) = k * Real.pi) :
    fixedPoints ((imInnerSymplecticForm G).timeDependentHamiltonianFlow
      (fun _ y ↦ a * ‖y‖ ^ 2) hX s t) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦
    (isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff a hX s t).2 (.inr h)

/-- **Nondegeneracy of the origin.** On a nonzero complex inner product space, the origin is a
nondegenerate fixed point of the evolution of `a ‖z‖²` from time `s` to time `t` exactly when
`a (t - s)` is not a multiple of `π`: the evolution is multiplication by `e^{-2 i a (t - s)}`, which
fixes a nonzero vector exactly when this scalar is `1`. -/
theorem isNondegenerateFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_zero_iff [Nontrivial G]
    (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    (s t : ℝ) :
    IsNondegenerateFixedPt 𝓘(ℝ, G)
        ((imInnerSymplecticForm G).timeDependentHamiltonianFlow (fun _ y ↦ a * ‖y‖ ^ 2) hX s t)
        0 ↔
      ∀ k : ℤ, a * (t - s) ≠ k * Real.pi := by
  have hD := ((imInnerSymplecticForm G).differentiable_timeDependentHamiltonianFlow hX
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)) s t 0).hasFDerivAt
  rw [isNondegenerateFixedPt_iff, hD.hasMFDerivAt.mfderiv,
    fderiv_timeDependentHamiltonianFlow_mul_norm_sq]
  -- A vector is fixed by the derivative exactly when it is fixed by the evolution, which is linear.
  have hfix (v : G) :=
    isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff a hX s t (z := v)
  rw [timeDependentHamiltonianFlow_mul_norm_sq_eq_lsmul] at hfix
  refine ⟨fun h k hk ↦ ?_, fun h ↦ ⟨?_, hD.hasMFDerivAt.mdifferentiableAt, fun v hv ↦ ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : G)
    exact hv (h.2.2 v ((hfix v).2 (.inr ⟨k, hk⟩)))
  · exact (isFixedPt_timeDependentHamiltonianFlow_mul_norm_sq_iff a hX s t).2 (.inl rfl)
  · exact ((hfix v).1 hv).resolve_right fun ⟨k, hk⟩ ↦ h k hk

/-! ### The Conley–Zehnder index of the origin -/

/-- **The Conley–Zehnder index of the origin for `a ‖z‖²`.** On a complex inner product space of
complex dimension `n` with the symplectic form `Im ⟪·, ·⟫_ℂ`, the constant orbit at the origin of
the quadratic Hamiltonian `a ‖z‖²` has Conley–Zehnder index `-n (⌊a / π⌋ + ⌈a / π⌉)`, read in
symplectic bases, in which `ω` has the matrix `J`. Its linearized flow is `t ↦ e^{-2 i a t}`: for
`a > 0` the start `t = 0` contributes `-n`, each multiple of `π` in `(0, a)` contributes `-2 n`,
and a multiple equal to `a` contributes `-n`; for `a < 0` the signs are reversed, and the index
is `0` at `a = 0`. -/
theorem orbitConleyZehnderIndex_mul_norm_sq (a : ℝ)
    (hH : ContDiff ℝ 2 (uncurry fun (_ : ℝ) (y : G) ↦ a * ‖y‖ ^ 2)) :
    (imInnerSymplecticForm G).orbitConleyZehnderIndex hH
        (continuous_const : Continuous fun _ : ℝ ↦ (0 : G)) =
      -(finrank ℂ G : ℝ) * (⌊a / Real.pi⌋ + ⌈a / Real.pi⌉ : ℤ) := by
  set ω := imInnerSymplecticForm G
  set e := stdOrthonormalBasis ℂ G
  have hb := e.toMatrix_imInnerSymplecticForm
  have hx : Continuous fun _ : ℝ ↦ (0 : G) := continuous_const
  -- The linearized flow along the origin is multiplication by `e^{-2 i a t}`.
  have hΨ (t : unitInterval) : ω.linearizedFlowPath hH hx t =
      ContinuousLinearMap.lsmul ℝ ℂ (exp ((-2 * a * t : ℝ) * I)) := by
    rw [SymplecticForm.linearizedFlowPath_apply]
    simp only [ω, hamiltonianVectorField_imInnerSymplecticForm_mul_norm_sq_eq_smul,
      ContinuousLinearMap.fderiv, dysonSeriesLeft_const, smul_smul,
      AlmostComplexStructure.exp_smul_ofComplexModule]
    rw [show (t : ℝ) * -(2 * a) = -2 * a * t by ring]
  -- In the symplectic basis `(i e, e)` its matrices are the realified `diag (e^{2 i a t})`, the
  -- conjugates of the complex matrices.
  have hmat (t : unitInterval) : ω.matrixPath hb (ω.linearizedFlowPath hH hx)
      (ω.apply_linearizedFlowPath_apply hH hx) t =
        (diagonalExpPath (Fin (finrank ℂ G)) (2 * a)).map GLSymplectic.continuous_ofUnitary t := by
    have hconj : starRingEnd ℂ (exp ((-2 * a * t : ℝ) * I)) = exp ((2 * a * t : ℝ) * I) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
    refine Subtype.ext (Units.ext ?_)
    rw [SymplecticForm.matrixPath_apply, SymplecticForm.coe_toGLSymplectic, hΨ t,
      e.toMatrix_imInnerSymplecticBasis_lsmul, hconj, Path.map_coe, Function.comp_apply,
      GLSymplectic.coe_ofUnitary, coe_diagonalExpPath_apply]
  have h2 : 2 * a / (2 * Real.pi) = a / Real.pi := mul_div_mul_left _ _ two_ne_zero
  rw [SymplecticForm.orbitConleyZehnderIndex_def, ω.conleyZehnderIndex_eq hb,
    GLSymplectic.conleyZehnderIndex_congr _ _ hmat,
    GLSymplectic.conleyZehnderIndex_map_ofUnitary_diagonalExpPath, h2, Fintype.card_fin]

/-- **The index jumps by `2 n` at each multiple of `π`.** For `k π < a < (k + 1) π`, the constant
orbit at the origin of `a ‖z‖²` has Conley–Zehnder index `-n (2 k + 1)`, where `n` is the complex
dimension. -/
theorem orbitConleyZehnderIndex_mul_norm_sq_of_mem_Ioo {a : ℝ} {k : ℤ}
    (ha : a ∈ Set.Ioo (k * Real.pi) ((k + 1) * Real.pi))
    (hH : ContDiff ℝ 2 (uncurry fun (_ : ℝ) (y : G) ↦ a * ‖y‖ ^ 2)) :
    (imInnerSymplecticForm G).orbitConleyZehnderIndex hH
        (continuous_const : Continuous fun _ : ℝ ↦ (0 : G)) =
      -(finrank ℂ G : ℝ) * (2 * k + 1) := by
  have h₁ : k < a / Real.pi := by rw [lt_div_iff₀ Real.pi_pos]; exact ha.1
  have h₂ : a / Real.pi < k + 1 := by rw [div_lt_iff₀ Real.pi_pos]; exact ha.2
  have hfloor : ⌊a / Real.pi⌋ = k := Int.floor_eq_iff.2 ⟨h₁.le, h₂⟩
  have hceil : ⌈a / Real.pi⌉ = k + 1 := Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by
    push_cast; exact h₂.le⟩
  rw [orbitConleyZehnderIndex_mul_norm_sq, hfloor, hceil]
  push_cast
  ring

/-- **The index of the origin in the coordinates of `ℂⁿ`.** Let `e` be an orthonormal basis of a
complex inner product space indexed by `ι`, and read the linearized evolutions of `a ‖z‖²` at the
origin as matrices in the real basis `(e, i e)`, in which `Im ⟪·, ·⟫_ℂ` has the matrix `-J`
(`OrthonormalBasis.toMatrix_reindex_sumComm_imInnerSymplecticForm`). Every path of symplectic
matrices made of them has Conley–Zehnder index `n (⌊a / π⌋ + ⌈a / π⌉)`, with `n = card ι`. This is
the convention in which the constant orbit at a nondegenerate critical point of a small Hamiltonian
has index `n - ind` (`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`);
in it the index of the origin rises by `2 n` each time `a` crosses a multiple of `π`. -/
theorem conleyZehnderIndex_eq_of_toMatrix_fderiv_timeDependentHamiltonianFlow_mul_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℂ G) (a : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K
      ((imInnerSymplecticForm G).timeDependentHamiltonianSuspension fun _ y ↦ a * ‖y‖ ^ 2))
    {A B : GLSymplectic ι ℝ} (γ : Path A B)
    (hγ : ∀ t : unitInterval, ((γ t : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      LinearMap.toMatrix (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
        (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
        (fderiv ℝ ((imInnerSymplecticForm G).timeDependentHamiltonianFlow
          (fun _ y ↦ a * ‖y‖ ^ 2) hX 0 t) 0)) :
    GLSymplectic.conleyZehnderIndex γ = Fintype.card ι * (⌊a / Real.pi⌋ + ⌈a / Real.pi⌉ : ℤ) := by
  -- In the basis `(e, i e)` the linearized evolutions are the realified `diag (e^{-2 i a t})`.
  have hmat (t : unitInterval) :
      γ t = (diagonalExpPath ι (-2 * a)).map GLSymplectic.continuous_ofUnitary t := by
    refine Subtype.ext (Units.ext ?_)
    rw [hγ t, fderiv_timeDependentHamiltonianFlow_mul_norm_sq, sub_zero,
      e.toMatrix_reindex_sumComm_imInnerSymplecticBasis_lsmul, Path.map_coe, Function.comp_apply,
      GLSymplectic.coe_ofUnitary, coe_diagonalExpPath_apply]
  have h2 : -2 * a / (2 * Real.pi) = -(a / Real.pi) := by
    rw [neg_mul, neg_div, mul_div_mul_left _ _ two_ne_zero]
  rw [GLSymplectic.conleyZehnderIndex_congr _ _ hmat,
    GLSymplectic.conleyZehnderIndex_map_ofUnitary_diagonalExpPath, h2, Int.floor_neg, Int.ceil_neg]
  push_cast
  ring

end TauCeti
