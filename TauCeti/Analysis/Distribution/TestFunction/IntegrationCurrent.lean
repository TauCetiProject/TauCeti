/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import TauCeti.MeasureTheory.Integral.Bochner.Alternating
import TauCeti.Analysis.Calculus.DifferentialForm.Integral

/-!
# The oriented integration current of a Euclidean open set

Let `E` be a real vector space of finite dimension `m` with an orientation `o`, and let `Ω` be an
open subset of `E`. The *integration current* `[[Ω]]` of `Ω` is the top-degree current
`ω ↦ ∫_Ω ω`, a continuous linear functional on the test `m`-forms
`𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)`. In coordinates, for any basis `b` of `E` with orientation `o`,
`[[Ω]] ω = ∫ x, ω x b ∂b.addHaar`, the integral of the coefficient of `ω` in the basis `b` against
the Haar measure normalized by `b`. This does not depend on the choice of `b`: the factor
`b.det b'` by which the coefficient changes and the factor `|b.det b'|⁻¹` by which the measure
changes cancel for bases of the same orientation (`Module.Basis.integral_signed_apply_eq`). No
inner product or choice of measure on `E` is needed to define `[[Ω]]`; only the Borel structure
enters. Continuity comes from Mathlib's `TestFunction.integralAgainstBilinCLM`.

This is the comparison current of the constancy theorem: on a connected open set, a top-degree
current with zero boundary is a constant multiple of `[[Ω]]`. Here we prove that `[[Ω]]` itself
has zero boundary, `[[Ω]] (d ω) = 0`, which is Stokes' theorem for compactly supported forms on
an open set; that reversing the orientation negates it; that it is compatible with extending test
forms by zero from a smaller open set; and its normalizations in degree zero and on inner
product spaces.

## Main declarations

* `Orientation.integrationCurrent o Ω`: the oriented integration current `[[Ω]]`.
* `Orientation.integrationCurrent_apply`: `[[Ω]] ω = ∫ x, ω x b ∂b.addHaar` for every basis `b` of
  orientation `o`; `Orientation.integrationCurrent_apply_eq_signBasis_mul` computes it in an
  arbitrary basis.
* `Orientation.integrationCurrent_apply_eq_integral_volume`: on an inner product space,
  `[[Ω]] ω = ∫ x, ω x b` against the volume for every positively oriented orthonormal basis `b`.
* `Orientation.integrationCurrent_neg`: `[[Ω]]` changes sign with the orientation.
* `Orientation.integrationCurrent_comp_extDerivCLM`: `[[Ω]]` has zero boundary, `[[Ω]] ∘ d = 0`.
* `Orientation.integrationCurrent_monoCLM`: restriction to a smaller open set.
* `Orientation.integrationCurrent_positiveOrientation_apply`: in dimension zero, the positively
  oriented point is the Dirac current at the origin.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16.
-/

public section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω Ω' : Opens E} {m : ℕ} {n : ℕ∞}

/-- The **oriented integration current** `[[Ω]]` of an open set `Ω` of an oriented real vector
space `E` of dimension `m`: the continuous linear functional `ω ↦ ∫_Ω ω` on test `m`-forms on `Ω`.
For any basis `b` of orientation `o` it is `ω ↦ ∫ x, ω x b ∂b.addHaar`
(`Orientation.integrationCurrent_apply`). If `m` is not the dimension of `E`, it is zero. -/
noncomputable def integrationCurrent (o : Orientation ℝ E (Fin m)) (Ω : Opens E) :
    𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  if h : finrank ℝ E = m then
    letI b := finBasisOfFinrankEq ℝ E h
    (o.signBasis b : ℝ) •
      integralAgainstBilinCLM
        (ContinuousLinearMap.mul ℝ ℝ ∘L ContinuousAlternatingMap.apply ℝ E ℝ ⇑b)
        b.addHaar (fun _ ↦ (1 : ℝ))
  else 0

/-- The integration current `[[Ω]]` evaluated on a test top form `ω`, computed in an arbitrary
basis `b`: it is the integral of the coefficient `ω x b` against the Haar measure normalized by
`b`, multiplied by the sign `o.signBasis b` of `b` relative to the orientation `o`. -/
theorem integrationCurrent_apply_eq_signBasis_mul (o : Orientation ℝ E (Fin m)) (Ω : Opens E)
    (b : Basis (Fin m) ℝ E) (ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) :
    o.integrationCurrent Ω ω = (o.signBasis b : ℝ) * ∫ x, ω x b ∂b.addHaar := by
  have h : finrank ℝ E = m := by simpa using finrank_eq_card_basis b
  rw [← (finBasisOfFinrankEq ℝ E h).integral_signed_apply_eq o b]
  simp only [integrationCurrent, h, ↓reduceDIte, FunLike.coe_smul, Pi.smul_apply,
    integralAgainstBilinCLM_eq_integral ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _)]
  simp

/-- The integration current `[[Ω]]` evaluated on a test top form `ω` is the integral of the
coefficient `ω x b` against the Haar measure normalized by `b`, for every basis `b` of the given
orientation. -/
theorem integrationCurrent_apply (o : Orientation ℝ E (Fin m)) (Ω : Opens E)
    (b : Basis (Fin m) ℝ E) (hb : b.orientation = o) (ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) :
    o.integrationCurrent Ω ω = ∫ x, ω x b ∂b.addHaar := by
  subst hb
  simp [integrationCurrent_apply_eq_signBasis_mul _ Ω b]

/-- On a finite-dimensional inner product space, the integration current `[[Ω]]` evaluated on a
test top form `ω` is the integral of `ω x b` against the volume, for every orthonormal basis `b` of
the given orientation. -/
theorem integrationCurrent_apply_eq_integral_volume {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {Ω : Opens F} (o : Orientation ℝ F (Fin m)) (b : OrthonormalBasis (Fin m) ℝ F)
    (hb : b.toBasis.orientation = o) (ω : 𝓓^{n}(Ω, F [⋀^Fin m]→L[ℝ] ℝ)) :
    o.integrationCurrent Ω ω = ∫ x, ω x b ∂volume := by
  rw [integrationCurrent_apply o Ω b.toBasis hb, b.addHaar_eq_volume, b.coe_toBasis]

/-- The integration current vanishes when the degree is not the dimension of the space. -/
theorem integrationCurrent_eq_zero_of_finrank_ne (o : Orientation ℝ E (Fin m)) (Ω : Opens E)
    (h : finrank ℝ E ≠ m) :
    (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  simp [integrationCurrent, h]

/-- **Orientation reversal**: the integration current of the opposite orientation is the negative
of the integration current. -/
@[simp]
theorem integrationCurrent_neg (o : Orientation ℝ E (Fin m)) (Ω : Opens E) :
    ((-o).integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      -o.integrationCurrent Ω := by
  by_cases h : finrank ℝ E = m
  · ext ω
    let b := finBasisOfFinrankEq ℝ E h
    simp [integrationCurrent_apply_eq_signBasis_mul _ Ω b]
  · simp [integrationCurrent_eq_zero_of_finrank_ne _ Ω h]

/-- **Stokes' theorem for test forms**: the integration current annihilates every exact test
form. -/
@[simp]
theorem integrationCurrent_extDerivCLM {k : ℕ} (o : Orientation ℝ E (Fin (k + 1)))
    (Ω : Opens E) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    o.integrationCurrent Ω (extDerivCLM ω) = 0 := by
  by_cases h : finrank ℝ E = k + 1
  · let b := finBasisOfFinrankEq ℝ E h
    rw [integrationCurrent_apply_eq_signBasis_mul o Ω b]
    simp_rw [extDerivCLM_apply]
    rw [(b.integral_extDeriv_eq_zero (ω.contDiff.of_le (by simp)) ω.hasCompactSupport).2,
      mul_zero]
  · simp [integrationCurrent_eq_zero_of_finrank_ne o Ω h]

/-- The integration current has **zero boundary**: `[[Ω]] ∘ d = 0`. -/
theorem integrationCurrent_comp_extDerivCLM {k : ℕ} (o : Orientation ℝ E (Fin (k + 1)))
    (Ω : Opens E) :
    o.integrationCurrent Ω ∘L (extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) = 0 := by
  ext ω
  simp

/-- The integration current is compatible with restriction: on a test form extended by zero from
a smaller open set `Ω'`, the integration current of `Ω` is that of `Ω'`. -/
@[simp]
theorem integrationCurrent_monoCLM (o : Orientation ℝ E (Fin m)) (h : Ω' ≤ Ω)
    (ω : 𝓓^{n}(Ω', E [⋀^Fin m]→L[ℝ] ℝ)) :
    o.integrationCurrent Ω (monoCLM ℝ ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) =
      o.integrationCurrent Ω' ω := by
  by_cases hm : finrank ℝ E = m
  · let b := finBasisOfFinrankEq ℝ E hm
    rw [integrationCurrent_apply_eq_signBasis_mul o Ω b,
      integrationCurrent_apply_eq_signBasis_mul o Ω' b]
    simp [monoCLM_apply, h]
  · simp [integrationCurrent_eq_zero_of_finrank_ne o _ hm]

/-- **Degree zero**: on a zero-dimensional space, the integration current of the positive
orientation is the Dirac current at the origin. -/
theorem integrationCurrent_positiveOrientation_apply [Subsingleton E] (Ω : Opens E)
    (ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ)) :
    (positiveOrientation : Orientation ℝ E (Fin 0)).integrationCurrent Ω ω = ω 0 ![] := by
  let b : Basis (Fin 0) ℝ E := Basis.empty E
  have hfun : (fun x ↦ ω x b) = fun _ ↦ ω 0 ![] := by
    ext x
    rw [Subsingleton.elim x 0, Subsingleton.elim (⇑b) ![]]
  rw [integrationCurrent_apply _ Ω b (Basis.orientation_isEmpty b)]
  simp [hfun, measureReal_def, b.addHaar_univ_of_isEmpty]

end Orientation
