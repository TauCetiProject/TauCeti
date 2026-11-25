/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Basic
public import TauCeti.Analysis.Complex.LaplaceReflection
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Order-zero reflection for rough Cauchy–Riemann equations with a totally real boundary condition

Let `Ω ⊆ ℂ` be an open set invariant under complex conjugation, write `z = s + i t`, and let `V`
be a real inner product space with an isometric involution `R` (for `V = ℂⁿ`, coordinatewise
conjugation). Let `ξ` be a weak solution up to the real axis of `∂_s ξ + J ∂_t ξ + S ξ = η` on
`Ω ∩ {0 ≤ t}`, in the sense of `TauCeti.IsWeakCRSolutionHalf`, for a boundary subspace `Λ`
containing the fixed vectors of `R`. This file reflects the solution and the data across `ℝ`,
each by the twisted reflection `TauCeti.twistedReflection` (the map above the axis, a linear
image of its values at the conjugate point below it, and `0` on the null axis):

* `ξ(conj z) = R ξ(z)` and `η(conj z) = R η(z)`, `TauCeti.twistedReflection R`,
* `J(conj z) = -R J(z) R⁻¹` (`TauCeti.crReflectionCoeff`), with derivative
  `DJ(conj z) h = -R DJ(z)(conj h) R⁻¹` (`TauCeti.crReflectionDeriv`),
* `S(conj z) = R S(z) R⁻¹` (`TauCeti.crReflectionZeroth`).

The file then proves that the reflected solution is a weak solution of the reflected equation on
all of `Ω` (`TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection`). The coefficient
reflections only need a continuous linear equivalence `R` of a normed space; the isometry and the
involution enter in the reflection theorem. The sign in the reflection of
`J` is forced by `∂_t (ξ(conj z)) = -(∂_t ξ)(conj z)`. For `J = i` and `R = conj` the reflected
coefficient is `i` again off the axis
(`TauCeti.crReflectionCoeff_conjLIE_const_I_smul_id_ae_eq`), and the reflection
of `ξ = z` by `conj` is `z` (`TauCeti.twistedReflection_conjCLE_id`): this is the setting of
McDuff–Salamon, where `J(s) = i` on `ℝ` makes the reflected coefficient continuous across the
axis. The weak identity itself needs no condition on `J` along `ℝ`.

A test function `φ` on `Ω` is paired with its reflection `φ^R(z) = R φ(conj z)`; the sum
`φ + φ^R` takes values in the fixed space of `R` on `ℝ`, so it is admissible for the boundary
condition, and the lower half-plane part of the doubled pairing is the upper half-plane pairing
with `φ^R`, by the measure-preserving substitution `z ↦ conj z`
(`Complex.integral_eq_setIntegral_add_comp_conj`). Pointwise, `R` applied to the reflected formal
adjoint of `φ` at `conj z` is the formal adjoint `TauCeti.crFormalAdjoint` of `φ^R` at `z`.
Integrability on the doubled domain comes from the Hölder condition
`1/p + 1/q ≤ 1` for coefficients `J, DJ, S ∈ Lᵖ_loc` up to the boundary.

Combined with the interior regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`, this
gives `W^{1,r}` regularity up to the boundary (`TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one`),
once the reflected coefficients are Sobolev coefficients on `Ω`. For the constant structure
`J = i` on `V = ℂ` this holds outright (`TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one_of_I`). For
a variable `J ∈ W^{1,p}` up to the boundary, the reflected coefficient is the even reflection of
the part of `J` anticommuting with `R` plus the odd reflection of the part commuting with `R`;
the boundary condition `J(s) = i` says that the second part vanishes on `ℝ`, which is what makes
its odd reflection Sobolev. That gluing step is not part of this file.

## Main results

* `TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection`: the reflected solution is a weak
  solution of the reflected equation on the doubled domain.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one`: if the reflected coefficients are Sobolev
  coefficients with `J² = -1` and `p > 2`, and `η ∈ Lʳ_loc` up to the boundary with
  `1 < r ≤ p`, then `ξ ∈ W^{1,r}_loc(Ω ∩ {0 ≤ t})`.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one_of_I`: the case `V = ℂ`, `J = i`, `S = 0`, real
  boundary values.
* `TauCeti.MemLpLoc.twistedReflection`, `TauCeti.MemLpLoc.of_twistedReflection`: local `Lᵖ`
  bounds pass to and from twisted reflections.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, equation (B.4.3) and Lemma B.4.6.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal ComplexConjugate

namespace TauCeti

/-! ### Reflected coefficients -/

section Coefficients

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {R : W ≃L[ℝ] W}
  {J S : ℂ → W →L[ℝ] W} {DJ : ℂ → ℂ →L[ℝ] W →L[ℝ] W}

/-- The **reflection of the leading coefficient** across the real axis by `R`: the twisted
reflection (`TauCeti.twistedReflection`) of `J` by `M ↦ -R M R⁻¹`, so `J` above the axis and
`-R J(conj z) R⁻¹` below it. Then `∂_s + J' ∂_t`, for this reflected coefficient `J'`, maps
fields reflected by `R` to fields reflected by `R`. -/
def crReflectionCoeff (R : W ≃L[ℝ] W) (J : ℂ → W →L[ℝ] W) : ℂ → W →L[ℝ] W :=
  twistedReflection (-(R.conjContinuousAlgEquiv.toContinuousLinearEquiv :
    (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W)) J

/-- The **reflection of the derivative of the leading coefficient**: the twisted reflection of
`DJ` by `D ↦ (h ↦ -R D(conj h) R⁻¹)`, the derivative of `TauCeti.crReflectionCoeff R J` below the
axis when `DJ` is that of `J`. -/
def crReflectionDeriv (R : W ≃L[ℝ] W) (DJ : ℂ → ℂ →L[ℝ] W →L[ℝ] W) :
    ℂ → ℂ →L[ℝ] W →L[ℝ] W :=
  twistedReflection (-((ContinuousLinearMap.compL ℝ ℂ (W →L[ℝ] W) (W →L[ℝ] W)
    (R.conjContinuousAlgEquiv.toContinuousLinearEquiv : (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W)).comp
      ((ContinuousLinearMap.compL ℝ ℂ ℂ (W →L[ℝ] W)).flip (conjCLE : ℂ →L[ℝ] ℂ)))) DJ

/-- The **reflection of the zeroth-order coefficient**: the twisted reflection of `S` by
`M ↦ R M R⁻¹`. -/
def crReflectionZeroth (R : W ≃L[ℝ] W) (S : ℂ → W →L[ℝ] W) : ℂ → W →L[ℝ] W :=
  twistedReflection (R.conjContinuousAlgEquiv.toContinuousLinearEquiv :
    (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W) S

/-- `TauCeti.crReflectionCoeff` as a twisted reflection. -/
theorem crReflectionCoeff_def (R : W ≃L[ℝ] W) (J : ℂ → W →L[ℝ] W) :
    crReflectionCoeff R J = twistedReflection (-(R.conjContinuousAlgEquiv.toContinuousLinearEquiv :
      (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W)) J :=
  (rfl)

/-- `TauCeti.crReflectionDeriv` as a twisted reflection. -/
theorem crReflectionDeriv_def (R : W ≃L[ℝ] W) (DJ : ℂ → ℂ →L[ℝ] W →L[ℝ] W) :
    crReflectionDeriv R DJ = twistedReflection (-((ContinuousLinearMap.compL ℝ ℂ (W →L[ℝ] W)
      (W →L[ℝ] W) (R.conjContinuousAlgEquiv.toContinuousLinearEquiv :
        (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W)).comp
        ((ContinuousLinearMap.compL ℝ ℂ ℂ (W →L[ℝ] W)).flip (conjCLE : ℂ →L[ℝ] ℂ)))) DJ :=
  (rfl)

/-- `TauCeti.crReflectionZeroth` as a twisted reflection. -/
theorem crReflectionZeroth_def (R : W ≃L[ℝ] W) (S : ℂ → W →L[ℝ] W) :
    crReflectionZeroth R S = twistedReflection (R.conjContinuousAlgEquiv.toContinuousLinearEquiv :
      (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W) S :=
  (rfl)

variable {z : ℂ}

@[simp]
theorem crReflectionCoeff_of_im_eq_zero (hz : z.im = 0) : crReflectionCoeff R J z = 0 := by
  rw [crReflectionCoeff_def, twistedReflection_of_im_eq_zero hz]

@[simp]
theorem crReflectionDeriv_of_im_eq_zero (hz : z.im = 0) : crReflectionDeriv R DJ z = 0 := by
  rw [crReflectionDeriv_def, twistedReflection_of_im_eq_zero hz]

@[simp]
theorem crReflectionZeroth_of_im_eq_zero (hz : z.im = 0) : crReflectionZeroth R S z = 0 := by
  rw [crReflectionZeroth_def, twistedReflection_of_im_eq_zero hz]

@[simp]
theorem crReflectionCoeff_of_im_pos (hz : 0 < z.im) : crReflectionCoeff R J z = J z :=
  twistedReflection_of_im_pos hz

@[simp]
theorem crReflectionCoeff_apply_of_im_neg (hz : z.im < 0) (v : W) :
    crReflectionCoeff R J z v = -R (J (conj z) (R.symm v)) := by
  simp [crReflectionCoeff, twistedReflection_of_im_neg hz]

@[simp]
theorem crReflectionDeriv_of_im_pos (hz : 0 < z.im) : crReflectionDeriv R DJ z = DJ z :=
  twistedReflection_of_im_pos hz

@[simp]
theorem crReflectionDeriv_apply_of_im_neg (hz : z.im < 0) (h : ℂ) (v : W) :
    crReflectionDeriv R DJ z h v = -R (DJ (conj z) (conj h) (R.symm v)) := by
  simp [crReflectionDeriv, twistedReflection_of_im_neg hz]

@[simp]
theorem crReflectionZeroth_of_im_pos (hz : 0 < z.im) : crReflectionZeroth R S z = S z :=
  twistedReflection_of_im_pos hz

@[simp]
theorem crReflectionZeroth_apply_of_im_neg (hz : z.im < 0) (v : W) :
    crReflectionZeroth R S z v = R (S (conj z) (R.symm v)) := by
  simp [crReflectionZeroth, twistedReflection_of_im_neg hz]

/-- Below the axis the reflected coefficient squares to `-1` where `J` does at the conjugate
point: `(R J R⁻¹)² = R J² R⁻¹`. -/
theorem crReflectionCoeff_mul_self_of_im_neg (hz : z.im < 0)
    (hJ : J (conj z) * J (conj z) = -1) :
    crReflectionCoeff R J z * crReflectionCoeff R J z = -1 := by
  ext v
  have h := congrArg (fun M : W →L[ℝ] W => M (R.symm v)) hJ
  simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at h
  simp [crReflectionCoeff_apply_of_im_neg hz, h]

/-- The reflection of the zero derivative field is zero. -/
@[simp]
theorem crReflectionDeriv_zero : crReflectionDeriv R (0 : ℂ → ℂ →L[ℝ] W →L[ℝ] W) = 0 :=
  twistedReflection_zero_right _

/-- The reflection of the zero zeroth-order coefficient is zero. -/
@[simp]
theorem crReflectionZeroth_zero : crReflectionZeroth R (0 : ℂ → W →L[ℝ] W) = 0 :=
  twistedReflection_zero_right _

end Coefficients

/-! ### Local `Lᵖ` bounds on the doubled domain -/

section Integrability

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {f : ℂ → F}

/-- The twisted reflection of a map locally `Lᵖ` up to the real axis is locally `Lᵖ` on the
conjugation-invariant set `U`. -/
theorem MemLpLoc.twistedReflection {U : Set ℂ} (hU : MapsTo (starRingEnd ℂ) U U)
    (L : F →L[ℝ] F) (hf : MemLpLoc p (U ∩ {z | 0 ≤ z.im}) f) :
    MemLpLoc p U (TauCeti.twistedReflection L f) := by
  refine (hf.ite_conj hU L).congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [Complex.ae_im_ne_zero] with z hz
  rcases lt_or_gt_of_ne hz with hz | hz
  · simp [hz, not_le.2 hz]
  · simp [hz, hz.le]

/-- A map whose twisted reflection is locally `Lᵖ` on `U` is locally `Lᵖ` up to the real axis on
`U`: the two agree off the null real axis. -/
theorem MemLpLoc.of_twistedReflection {U : Set ℂ} {L : F →L[ℝ] F}
    (hf : MemLpLoc p U (TauCeti.twistedReflection L f)) :
    MemLpLoc p (U ∩ {z | 0 ≤ z.im}) f :=
  (hf.mono_set inter_subset_left).congr_ae
    (ae_restrict_of_ae_restrict_of_subset inter_subset_right (twistedReflection_ae_eq_restrict L f))

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {R : W ≃L[ℝ] W}
  {J S : ℂ → W →L[ℝ] W} {DJ : ℂ → ℂ →L[ℝ] W →L[ℝ] W} {U : Set ℂ}

/-- Local `Lᵖ` bounds pass between `J` up to the axis and its reflection on the doubled domain. -/
theorem memLpLoc_crReflectionCoeff_iff (hU : MapsTo (starRingEnd ℂ) U U) :
    MemLpLoc p U (crReflectionCoeff R J) ↔ MemLpLoc p (U ∩ {z | 0 ≤ z.im}) J := by
  rw [crReflectionCoeff_def]
  exact ⟨MemLpLoc.of_twistedReflection, fun h => h.twistedReflection hU _⟩

/-- Local `Lᵖ` bounds pass between `DJ` up to the axis and its reflection on the doubled
domain. -/
theorem memLpLoc_crReflectionDeriv_iff (hU : MapsTo (starRingEnd ℂ) U U) :
    MemLpLoc p U (crReflectionDeriv R DJ) ↔ MemLpLoc p (U ∩ {z | 0 ≤ z.im}) DJ := by
  rw [crReflectionDeriv_def]
  exact ⟨MemLpLoc.of_twistedReflection, fun h => h.twistedReflection hU _⟩

/-- Local `Lᵖ` bounds pass between `S` up to the axis and its reflection on the doubled domain. -/
theorem memLpLoc_crReflectionZeroth_iff (hU : MapsTo (starRingEnd ℂ) U U) :
    MemLpLoc p U (crReflectionZeroth R S) ↔ MemLpLoc p (U ∩ {z | 0 ≤ z.im}) S := by
  rw [crReflectionZeroth_def]
  exact ⟨MemLpLoc.of_twistedReflection, fun h => h.twistedReflection hU _⟩

end Integrability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Ω : Opens ℂ} {Λ : Submodule ℝ V} {p q r : ℝ≥0∞} {R : V ≃ₗᵢ[ℝ] V}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

variable [CompleteSpace V]

/-- **The reflected coefficient squares to `-1`.** If `J² = -1` almost everywhere on
`Ω ∩ {0 ≤ t}` for a conjugation-invariant `Ω`, then the reflected coefficient squares to `-1`
almost everywhere on `Ω`: below the axis it squares to `R J² R⁻¹ = -1`. -/
theorem ae_crReflectionCoeff_mul_self {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {R : W ≃L[ℝ] W} {J : ℂ → W →L[ℝ] W} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) :
    ∀ᵐ z ∂volume.restrict Ω, crReflectionCoeff R J z * crReflectionCoeff R J z = -1 := by
  have hJ2' : ∀ᵐ z ∂volume, z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} → J z * J z = -1 :=
    (ae_restrict_iff' (Ω.isOpen.measurableSet.inter
      (measurableSet_le measurable_const measurable_im))).1 hJ2
  have hJ2c := conjLIE.measurePreserving.quasiMeasurePreserving.ae hJ2'
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
  filter_upwards [hJ2', hJ2c, Complex.ae_im_ne_zero]
    with z hz hzc hz0 hzΩ
  rcases lt_or_gt_of_ne hz0 with h0 | h0
  · have hJz := hzc ⟨hΩ hzΩ, by simpa using h0.le⟩
    simp only [conjLIE_apply] at hJz
    exact crReflectionCoeff_mul_self_of_im_neg h0 hJz
  · rw [crReflectionCoeff_of_im_pos h0]
    exact hz ⟨hzΩ, h0.le⟩

/-! ### The reflection theorem -/

section Reflection

variable (hR : Function.Involutive R)
include hR

/-- The test function `z ↦ R φ(conj z)` on a conjugation-invariant open set. -/
private def reflectTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM (R.toContinuousLinearEquiv : V →L[ℝ] V) (TestFunction.compConj hΩ φ)

omit [CompleteSpace V] hR in
private theorem reflectTest_apply (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) (z : ℂ) :
    (reflectTest (R := R) hΩ φ : ℂ → V) z = R ((φ : ℂ → V) (conj z)) := by
  simp [reflectTest]

omit [CompleteSpace V] hR in
private theorem fderiv_reflectTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) (z v : ℂ) :
    fderiv ℝ (reflectTest (R := R) hΩ φ : ℂ → V) z v =
      R (fderiv ℝ (φ : ℂ → V) (conj z) (conj v)) := by
  have hφ := (TestFunction.compConj hΩ φ).contDiff.differentiable (by simp) z
  have h : (reflectTest (R := R) hΩ φ : ℂ → V) =
      (R.toContinuousLinearEquiv : V →L[ℝ] V) ∘ (TestFunction.compConj hΩ φ : ℂ → V) := by
    simp [reflectTest]
  rw [h, fderiv_comp z (ContinuousLinearMap.differentiableAt _) hφ, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply, TestFunction.fderiv_compConj_apply]
  simp

/-- **The pointwise reflection identity.** At a point `z` of the open upper half-plane, the
doubled pairing at `z` and at `conj z` adds up to the pairing of the formal adjoint of
`φ + R φ(conj ·)` with `ξ` at `z`. -/
private theorem inner_crFormalAdjoint_crReflection_add (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (φ : 𝓓(Ω, V)) {z : ℂ} (hz : 0 < z.im) :
    ⟪crFormalAdjoint (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) φ z,
        twistedReflection (R : V →L[ℝ] V) ξ z⟫_ℝ +
      ⟪crFormalAdjoint (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) φ (conj z),
        twistedReflection (R : V →L[ℝ] V) ξ (conj z)⟫_ℝ =
      ⟪crFormalAdjoint J DJ S (φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) z, ξ z⟫_ℝ := by
  have hz' : (conj z).im < 0 := by simpa using hz
  have hd (v : ℂ) : fderiv ℝ ((φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) : ℂ → V) z v =
      fderiv ℝ (φ : ℂ → V) z v + R (fderiv ℝ (φ : ℂ → V) (conj z) (conj v)) := by
    rw [FunLike.coe_add, fderiv_add (φ.contDiff.differentiable (by simp) z)
      ((reflectTest hΩ φ).contDiff.differentiable (by simp) z),
      add_apply, fderiv_reflectTest]
  rw [inner_crFormalAdjoint, inner_crFormalAdjoint, inner_crFormalAdjoint, hd, hd]
  -- Evaluate every reflection: the goal becomes a linear identity between inner products of
  -- `φ`, its derivatives at `z` and `conj z`, their images under `R`, and `ξ z`, `J z (ξ z)`,
  -- `DJ z I (ξ z)`, `S z (ξ z)`, in which `R` sits on either side of `⟪·, ·⟫`.
  simp only [twistedReflection_of_im_pos hz, crReflectionCoeff_of_im_pos hz,
    crReflectionDeriv_of_im_pos hz, crReflectionZeroth_of_im_pos hz,
    twistedReflection_of_im_neg hz', RingHomCompTriple.comp_apply, RingHom.id_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    crReflectionCoeff_apply_of_im_neg hz', LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    R.symm_apply_eq.2 (hR _).symm, inner_neg_right, sub_neg_eq_add,
    crReflectionDeriv_apply_of_im_neg hz', conj_I, map_neg, neg_apply, neg_neg,
    crReflectionZeroth_apply_of_im_neg hz', map_one, inner_add_left, neg_add_rev, inner_neg_left,
    add_apply, reflectTest_apply]
  -- Move every `R` to the left slot (`R` is self-adjoint); then both sides agree term by term.
  simp only [← LinearIsometryEquiv.inner_map_left_eq_of_involutive hR, hR _]
  ring

/-- **Order-zero reflection for rough Cauchy–Riemann equations.** Let `Ω`
be invariant under conjugation, `R` an isometric involution of `V` whose fixed vectors lie in
the boundary subspace `Λ`, and `J`, `DJ`, `S` locally `Lᵖ` up to the real axis with
`1/p + 1/q ≤ 1`. If `ξ` is a weak solution up to the real axis of `∂_s ξ + J ∂_t ξ + S ξ = η`
with boundary subspace `Λ`, then its twisted reflection `TauCeti.twistedReflection R ξ` is a weak
solution on
all of `Ω` of the equation with reflected coefficients and right-hand side. -/
theorem IsWeakCRSolutionHalf.isWeakCRSolution_crReflection
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ) (hJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J)
    (hDJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hS : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S) (hpq : p⁻¹ + q⁻¹ ≤ 1) :
    IsWeakCRSolution q Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S)
      (twistedReflection (R : V →L[ℝ] V) ξ) (twistedReflection (R : V →L[ℝ] V) η) := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hξ := h.memLpLoc.twistedReflection hΩ (R : V →L[ℝ] V)
  have hη := locallyIntegrableOn_twistedReflection (fun _ hz => hΩ hz) (R : V →L[ℝ] V)
    h.locallyIntegrableOn
  have hint (φ : 𝓓(Ω, V)) := integrable_inner_crFormalAdjoint_of_memLpLoc
    ((memLpLoc_crReflectionCoeff_iff (R := R.toContinuousLinearEquiv) hΩ).2 hJ)
    ((memLpLoc_crReflectionDeriv_iff (R := R.toContinuousLinearEquiv) hΩ).2 hDJ)
    ((memLpLoc_crReflectionZeroth_iff (R := R.toContinuousLinearEquiv) hΩ).2 hS) hpq hξ φ
  refine isWeakCRSolution_iff.2 ⟨hξ, hη, fun φ => ⟨hint φ, ?_⟩⟩
  -- `φ + R φ(conj ·)` takes values in the fixed space of `R` on the real axis.
  have hψΛ (s : ℝ) : ((φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) : ℂ → V) s ∈ Λ := by
    refine hΛ _ ?_
    simp only [FunLike.coe_add, Pi.add_apply, reflectTest_apply, conj_ofReal, map_add, hR _]
    exact add_comm _ _
  rw [Complex.integral_eq_setIntegral_add_comp_conj (hint φ),
    Complex.integral_eq_setIntegral_add_comp_conj (φ.integrable_inner hη),
    setIntegral_congr_fun hH fun z hz => inner_crFormalAdjoint_crReflection_add hR hΩ φ hz,
    h.setIntegral_inner_crFormalAdjoint _ hψΛ]
  refine setIntegral_congr_fun hH fun z hz => ?_
  have hz0 : 0 < z.im := hz.out
  have hz' : (conj z).im < 0 := by simpa using hz0
  simp [reflectTest_apply, twistedReflection_of_im_pos hz0, twistedReflection_of_im_neg hz',
    inner_add_left, LinearIsometryEquiv.inner_map_left_eq_of_involutive hR]

/-! ### Regularity up to the boundary -/

/-- **`W^{1,r}` regularity up to the real axis** (McDuff–Salamon, Lemma B.4.6 with a totally real
boundary condition). Let `Ω` be invariant under conjugation, `R` an isometric involution of the
finite-dimensional space `V` whose fixed vectors lie in `Λ`, and suppose that the reflected
coefficients are Sobolev coefficients on `Ω` for some `p > 2`, with `J² = -1` almost everywhere
on `Ω ∩ {0 ≤ t}`. If `ξ ∈ L^q_loc` is a weak solution up to the real axis with `1/p + 1/q < 1`,
and `η ∈ Lʳ_loc` up to the axis with `1 < r ≤ p` finite, then `ξ ∈ W^{1,r}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_one [FiniteDimensional ℝ V]
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S))
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p)
    (hη : MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    MemWkpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  have hsub : (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ Ω := inter_subset_left
  have hw := h.isWeakCRSolution_crReflection hR hΩ hΛ
    ((memLpLoc_crReflectionCoeff_iff hΩ).1 hc.memLpLoc_coeff)
    ((memLpLoc_crReflectionDeriv_iff hΩ).1 hc.memLpLoc_deriv)
    ((memLpLoc_crReflectionZeroth_iff hΩ).1 hc.memLpLoc_zeroth) hpq.le
  have hJJ := ae_crReflectionCoeff_mul_self (R := R.toContinuousLinearEquiv) hΩ hJ2
  exact ((hw.memWkpLoc_one_of_le hc hp hJJ hpq hr hr_top hrp
    (hη.twistedReflection hΩ _)).mono hsub).congr_ae
    (ae_restrict_of_ae_restrict_of_subset inter_subset_right (twistedReflection_ae_eq_restrict _ ξ))

end Reflection

/-! ### The constant structure `J = i` with real boundary values -/

/-- For `J = i` and `R = conj` on `V = ℂ`, the reflected coefficient is `i` again, off the null
real axis. The twisted reflection of `z` by `conj` is `z` off the axis
(`TauCeti.twistedReflection_conjCLE_id`). -/
theorem crReflectionCoeff_conjLIE_const_I_smul_id_ae_eq :
    crReflectionCoeff conjLIE.toContinuousLinearEquiv (fun _ => I • ContinuousLinearMap.id ℝ ℂ)
      =ᵐ[volume] fun _ => I • ContinuousLinearMap.id ℝ ℂ := by
  filter_upwards [Complex.ae_im_ne_zero] with z hz
  rcases lt_or_gt_of_ne hz with hz | hz
  · ext v
    simp [crReflectionCoeff_apply_of_im_neg hz,
      conjCLE.symm_apply_eq.2 (by simp : v = conjCLE (conj v))]
  · exact crReflectionCoeff_of_im_pos hz

/-- **`W^{1,r}` regularity up to the real axis for `J = i`.** On a conjugation-invariant open set,
a locally `L^q` weak solution up to the real axis of `∂_s ξ + i ∂_t ξ = η` with real boundary
values, for `1 < q` and `η ∈ Lʳ_loc` up to the axis with `1 < r < ∞`, lies in
`W^{1,r}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_one_of_I {ξ η : ℂ → ℂ}
    (h : IsWeakCRSolutionHalf q Ω (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 ξ η)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hq : 1 < q) (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hη : MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    MemWkpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  -- The coefficients are bounded, so the exponent `p = ∞` applies.
  have hc : IsSobolevCRCoefficients ⊤ Ω
      (crReflectionCoeff conjLIE.toContinuousLinearEquiv fun _ => I • ContinuousLinearMap.id ℝ ℂ)
      (crReflectionDeriv conjLIE.toContinuousLinearEquiv 0)
      (crReflectionZeroth conjLIE.toContinuousLinearEquiv 0) := by
    rw [crReflectionDeriv_zero, crReflectionZeroth_zero]
    have h0 : IsSobolevCRCoefficients ⊤ Ω (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 := by
      simpa [fderiv_const] using IsSobolevCRCoefficients.of_contDiffOn
        (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0) contDiffOn_const
        continuousOn_const ⊤
    have hae : crReflectionCoeff conjLIE.toContinuousLinearEquiv
        (fun _ => I • ContinuousLinearMap.id ℝ ℂ) =ᵐ[volume.restrict Ω]
          fun _ => I • ContinuousLinearMap.id ℝ ℂ :=
      ae_restrict_of_ae crReflectionCoeff_conjLIE_const_I_smul_id_ae_eq
    exact ⟨h0.hasWeakFDerivOn.congr_ae hae.symm, h0.memLpLoc_coeff.congr_ae hae.symm,
      h0.memLpLoc_deriv, h0.memLpLoc_zeroth⟩
  have hR : Function.Involutive conjLIE := fun v => by simp
  have hΛ (v : ℂ) (hv : conjLIE v = v) : v ∈ Submodule.span ℝ {(1 : ℂ)} :=
    Submodule.mem_span_singleton.2 ⟨v.re, by
      simpa [Complex.real_smul] using Complex.conj_eq_iff_re.1 (by simpa using hv)⟩
  have hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) z * (fun _ => I • ContinuousLinearMap.id ℝ ℂ) z =
        (-1 : ℂ →L[ℝ] ℂ) := .of_forall fun _ => by
    ext v
    simp [← mul_assoc]
  have hpq : (⊤ : ℝ≥0∞)⁻¹ + q⁻¹ < 1 := by simpa [ENNReal.inv_lt_one] using hq
  exact h.memWkpLoc_one hR hΩ hΛ hc (by simp) hJ2 hpq hr hr_top le_top hη

end TauCeti
